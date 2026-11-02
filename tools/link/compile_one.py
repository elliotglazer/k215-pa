"""Compile ONE pa-mm0 module against the interfaces of its dependencies (separate compilation).

  python3 compile_one.py MODULE... --build DIR [--tools TOOLDIR] [--full] [--force] [--keep-input]

Input file DIR/MODULE/input.mm1 =
    import "../_peano/peano_iface.mm1";   (peano.mm1 with every theorem stubbed, annotations and do blocks
                                            kept: 0.16 s to elaborate instead of 0.47 s; --real-peano imports
                                            lean-mm0/vendor/peano.mm1 itself)
    the interface items (mkiface.py) of every project module in MODULE's import closure, in check.py's flat order
    (with --full all items; by default only the items MODULE can reach, see below);
    MODULE's own source with its imports removed (exactly the chunk check.py's flattening would contain).
Output DIR/MODULE/MODULE.mmb (peano + interface copies + MODULE's own proofs) and DIR/MODULE/link.json.
input.mm1 is deleted after a passing compile (it is regenerated on every run anyway; --keep-input keeps it).

Pruning (default): every `do` block and notation of the closure is kept; a def or stub is kept iff its name is
reachable from an identifier of MODULE's source or of a kept item (identifiers of kept items are followed
transitively; an identifier X that names no declaration but has the form <def>eq.. / <def>eqd.. keeps <def>,
whose derive-eq annotation generates it). Pruning is untrusted like everything else here: if it dropped
something the module needs, its compile fails; rerun with --full.

A Plan holds a root's whole closure (import order, every module's interface items, a name index), computed once,
so that build_all.py does O(closure) work per job instead of per module. Plan.select gives exactly the items the
original per-module selection (select_flat below) gives; selftest.py compares the two.

The cache key is sha256(input.mm1 text) : sha256(peano interface) : sha256(mm0-rs) (= the module's source and its
dependency interfaces). A module whose link.json has the same key, status PASSED and a .mmb with the recorded
sha256 is not rebuilt (its link.json mtime is touched: build_all.py --cache-max-gb evicts least recently used).
A compile counts as passed iff mm0-rs exits 0 and its output has no "contains sorry" (as check.py).

Proof readers (README 4.8): when MODULE's input contains a `do` block that reads proofs (get-decl / get-proof, or a
Lisp name defined in such a block) and names a theorem, MODULE imports the real peano.mm1 and the dependency theorems
reachable from those names are kept verbatim (with proofs) instead of as stubs (Plan.verbatim); a remaining
`match failed: (axiom X ..)` adds X and recompiles. Other modules are unaffected.

Elaboration time limits are off: every `(set-timeout N)` of the input becomes `(set-timeout 0)` (no limit). The
limit is wall-clock, so under load it fails proofs that are fine; it has no bearing on what mm0-c accepts.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mm1lib as L  # noqa: E402
import mkiface  # noqa: E402
from runstat import run  # noqa: E402

SET_TIMEOUT = re.compile(r"\(set-timeout\s+\d+\s*\)")
# Proof readers (README 4.8): Lisp primitives that return a theorem's proof. A `do` block whose text uses one, or
# calls a Lisp name defined in such a block, is a READER block; the theorem names it mentions are its seeds.
READ_PRIMS = re.compile(r"\(\s*(?:get-decl|get-proof)[\s)]")
LISP_DEF = re.compile(r"\(\s*def\s+\(?\s*([^\s()\[\]{}'`,@;\"]+)")
LISP_TOK = re.compile(r"[^\s()\[\]{}'`,@;\"$]+")
MATCH_AXIOM = re.compile(r"match failed: \(axiom ([A-Za-z_][A-Za-z0-9_]*) ")
DERIVED = re.compile(r"^(.+?)(eqd|eq|eq\d+d?)$")
DS = ("def", "stub")
# Windows: keep every path the compile touches under MAX_PATH (mm0-rs runs with cwd = the module dir).
MAX_WIN_PATH = 240


def select_flat(dep_items, own_text, full):
    """Reference selection over a flat item list. dep_items: [(module, [(kind, name, text)])] in order. Returns
    (kept texts in order, total item count). Plan.select computes the same with a closure-wide index."""
    flat = [(m, k, n, t) for m, its in dep_items for k, n, t in its]
    if full:
        return [t for _, _, _, t in flat], len(flat)
    provide = {}
    for i, (m, k, n, t) in enumerate(flat):
        if k in DS and n is not None:
            provide.setdefault(n, i)
    keep = [False] * len(flat)
    work = [L.idents(own_text)]
    for i, (m, k, n, t) in enumerate(flat):
        if k not in DS:
            keep[i] = True
            work.append(L.idents(t))
    seen = set()
    while work:
        for x in work.pop():
            if x in seen:
                continue
            seen.add(x)
            i = provide.get(x)
            if i is None:
                d = DERIVED.match(x)
                i = provide.get(d.group(1)) if d else None
                if i is None or flat[i][1] != "def":
                    continue
            if not keep[i]:
                keep[i] = True
                work.append(L.idents(flat[i][3]))
    kept = [t for (m, k, n, t), y in zip(flat, keep) if y]
    return kept, len(flat)


class NameClash(Exception):
    pass


class Plan:
    """A root's closure, computed once: order / imports (check.py flat order), interface items of every module
    (cached on disk in DIR/_iface by source sha256), the providers of every def / stub name, and the identifiers of
    each module's always-kept items (do blocks, notations)."""

    def __init__(self, root, bdir, real_peano=False):
        self.root, self.bdir = root, bdir
        self.order, self.imports = L.closure_order(root)
        cache = os.path.join(bdir, "_iface")
        self.items = {m: mkiface.cached_items(m, cache) for m in self.order}
        self.provide = {}                 # name -> [(module, item index)] of def / stub items
        self.always = {}                  # module -> [item index] of non-def/stub items (always kept)
        self.always_ids = {}              # module -> identifiers of those items
        for m in self.order:
            ids, alw = set(), []
            for i, (k, n, t) in enumerate(self.items[m]):
                if k in DS:
                    if n is not None:
                        self.provide.setdefault(n, []).append((m, i))
                else:
                    alw.append(i)
                    ids |= L.idents(t)
            self.always[m], self.always_ids[m] = alw, frozenset(ids)
        self._ids = {}
        self._full = {}
        self._tac = {}
        self.real_peano = real_peano
        self.pfile = os.path.join(L.VENDOR, "peano.mm1") if real_peano else peano_iface(bdir)
        # reader blocks (README 4.8): readers = Lisp names defined in do blocks that use get-decl / get-proof
        readers = set()
        for m in self.order:
            for k, n, t in self.items[m]:
                if k == "do" and READ_PRIMS.search(t):
                    readers |= set(LISP_DEF.findall(t))
        self.reader_seeds = {}           # module -> Lisp tokens of its reader blocks (candidate seed names)
        for m in self.order:
            toks = set()
            for k, n, t in self.items[m]:
                if k == "do" and (READ_PRIMS.search(t) or readers & set(LISP_TOK.findall(t))):
                    toks |= set(LISP_TOK.findall(t))
            if toks:
                self.reader_seeds[m] = frozenset(toks)
        self._peano_thms = None

    def idents(self, m, i):
        v = self._ids.get((m, i))
        if v is None:
            v = self._ids[(m, i)] = L.idents(self.items[m][i][2])
        return v

    def full_text(self, m, i):
        """Verbatim text (proof included, comments removed) of item i of module m."""
        st = self._full.get(m)
        if st is None:
            st = self._full[m] = [t for kw, _n, t in L.statements(L.read_text(os.path.join(L.PA, m + ".mm1")))
                                  if kw != "import"]
        return st[i]

    def peano_thms(self):
        if self._peano_thms is None:
            self._peano_thms = frozenset(n for kw, n, _ in L.statements(L.read_text(
                os.path.join(L.VENDOR, "peano.mm1"))) if kw == "theorem")
        return self._peano_thms

    def verbatim(self, m, deps, extra=()):
        """Proof readers (README 4.8). Returns (V, peano): V = the dependency theorems of m to keep verbatim, with
        their proofs, instead of as stubs; peano = True iff m must import the real peano.mm1 (a reader can reach a
        peano proof). Seeds: the theorem names mentioned by the reader blocks of m's closure and of m itself (plus
        `extra`); V is their closure under the identifiers of the theorems' texts (own theorems of m are followed
        but stay as they are). Empty unless a reader block is in m's input: then the result is as before."""
        seeds = set(extra)
        for d in deps + [m]:
            seeds |= self.reader_seeds.get(d, frozenset())
        mpos = {d: k for k, d in enumerate(deps + [m])}
        pth = self.peano_thms()
        seeds = {x for x in seeds if x in pth or self._is_thm(self._find(x, mpos))}
        if not seeds:
            return set(), False
        # Theorems that tactics of the closure can put into an elaborated proof without the source naming them:
        # those named in do blocks (e.g. `(register-eqd 'f) '(lemma)`) and annotated theorems (@(register-eqd ..)).
        for d in deps + [m]:
            seeds |= self.tactic_names(d)
        V, peano, seen, work = set(), False, set(), list(seeds)
        while work:
            x = work.pop()
            if x in seen:
                continue
            seen.add(x)
            b = self._find(x, mpos)
            if b is None:
                if x in pth:
                    peano = True
                continue
            _p, d, i = b
            if self.items[d][i][0] != "stub":
                continue
            if d != m:
                V.add((d, i))
            work.extend(L.idents(self.full_text(d, i)))
        return V, peano or bool(V)

    def _is_thm(self, b):
        return b is not None and self.items[b[1]][b[2]][0] == "stub"

    def tactic_names(self, d):
        v = self._tac.get(d)
        if v is None:
            v = set()
            for k, n, t in self.items[d]:
                if k == "do":
                    v |= L.idents(t)
                elif k == "stub" and t.startswith("@"):
                    v.add(n)
            v = self._tac[d] = frozenset(v)
        return v

    def _find(self, x, mpos):
        best = None
        for d, i in self.provide.get(x, ()):
            p = mpos.get(d)
            if p is not None and (best is None or (p, i) < best[0]):
                best = ((p, i), d, i)
        return best

    def clashes(self, m, deps):
        """Def / stub names of m that a module of its closure (pruned or not) also declares."""
        mpos = {d: k for k, d in enumerate(deps)}
        return [n for k, n, _t in self.items[m] if k in DS and n and self._find(n, mpos)]

    def select(self, m, deps, own_text, full, verbatim=()):
        """(kept texts in m's flat order, total item count); same result as select_flat when `verbatim` is empty.
        Items (module, index) in `verbatim` are kept with their full text (proof included) instead of the stub."""
        total = sum(len(self.items[d]) for d in deps)
        txt = lambda d, i: self.full_text(d, i) if (d, i) in verbatim else self.items[d][i][2]
        if full:
            return [txt(d, i) for d in deps for i in range(len(self.items[d]))], total
        mpos = {d: k for k, d in enumerate(deps)}
        keep = set(verbatim)
        seen = set()
        work = [L.idents(own_text)] + [self.always_ids[d] for d in deps]
        work += [L.idents(self.full_text(d, i)) for d, i in verbatim]
        while work:
            for x in work.pop():
                if x in seen:
                    continue
                seen.add(x)
                b = self._find(x, mpos)
                if b is None:
                    dm = DERIVED.match(x)
                    b = self._find(dm.group(1), mpos) if dm else None
                    if b is None or self.items[b[1]][b[2]][0] != "def":
                        continue
                key = (b[1], b[2])
                if key not in keep:
                    keep.add(key)
                    work.append(self.idents(b[1], b[2]))
        pos = [(mpos[d], i) for d, i in keep] + [(mpos[d], i) for d in deps for i in self.always[d]]
        pos.sort()
        return [txt(deps[p], i) for p, i in pos], total


def peano_iface(bdir):
    """DIR/_peano/peano_iface.mm1 (regenerated when missing or when the vendor file changed)."""
    src = os.path.join(L.VENDOR, "peano.mm1")
    path = os.path.join(bdir, "_peano", "peano_iface.mm1")
    tag = "-- peano interface of sha256 %s\n" % L.sha256(src)
    try:
        with open(path, encoding="utf-8") as f:
            if f.readline() == tag:
                return path
    except OSError:
        pass
    os.makedirs(os.path.dirname(path), exist_ok=True)
    out = [L.stub_text(s) if kw == "theorem" else s for kw, n, s in L.statements(L.read_text(src))]
    tmp = "%s.%d.%d.tmp" % (path, os.getpid(), id(out))
    with open(tmp, "wb") as f:
        f.write((tag + "\n".join(out) + "\n").encode("utf-8"))
    os.replace(tmp, path)
    return path


def build_input(module, plan, full, extra=()):
    """(input text, closure order, kept items, total items, own source sha256, imports, peano file, verbatim
    count); NameClash on a hidden clash. extra = additional reader seeds (README 4.8)."""
    order = L.sub_order(plan.imports, module)
    deps = order[:-1]
    raw = L.read_text(os.path.join(L.PA, module + ".mm1"))
    own = L.IMPORT.sub("", raw)
    # Name clashes the monolithic compile would report ("redeclared") but a pruned interface would hide:
    # a def or theorem of MODULE named like a def or theorem of its closure. Reject them here, so separate
    # compilation accepts no closure that the flattened compile rejects for this reason.
    mine = plan.clashes(module, deps)
    if mine:
        raise NameClash("%s redeclares %d name(s) of its closure, e.g. %s" % (module, len(mine), mine[:5]))
    V, real = plan.verbatim(module, deps, extra)
    kept, total = plan.select(module, deps, L.strip_comments(own), full, V)
    pfile = os.path.join(L.VENDOR, "peano.mm1") if real else plan.pfile
    mdir = os.path.join(plan.bdir, module)
    peano = os.path.relpath(pfile, mdir).replace("\\", "/")
    text = ('import "%s";\n' % peano + "\n".join(kept) +
            "\n\n-- Original proof module: %s.mm1\n" % module + own + "\n")
    text = SET_TIMEOUT.sub("(set-timeout 0)", text)
    return (text, order, len(kept), total, hashlib.sha256(raw.encode("utf-8")).hexdigest(), L.IMPORT.findall(raw),
            pfile, len(V))


def _failed(module, err, **kw):
    man = {"module": module, "status": "FAILED", "errors": [err], "compile_seconds": 0, "compile_peak_rss_bytes": 0,
           "iface_items_kept": 0, "iface_items_total": 0, "input_bytes": 0, "mmb_bytes": None}
    man.update(kw)
    return man


def compile_one(module, bdir, tools=None, full=False, force=False, real_peano=False, plan=None, keep_input=False):
    tools = tools or L.default_tools()
    mm0rs = L.tool(tools, "mm0-rs")
    if plan is None:
        plan = Plan(module, bdir, real_peano)
    t0 = time.perf_counter()
    mdir = os.path.join(bdir, module)
    inp, mmb, man_path = (os.path.join(mdir, n) for n in ("input.mm1", module + ".mmb", "link.json"))
    if os.name == "nt" and max(len(os.path.abspath(p)) for p in (inp, mmb, man_path)) > MAX_WIN_PATH:
        return _failed(module, "path too long for Windows (> %d chars): %s; use a shorter --build dir"
                       % (MAX_WIN_PATH, os.path.abspath(mmb)))
    # reader seeds learned by an earlier compile of this module (README 4.8), so that its cache key is reproduced
    extra = []
    try:
        with open(man_path, encoding="utf-8") as f:
            extra = list(json.load(f).get("reader_extra", []))
    except (OSError, ValueError, AttributeError):
        pass
    for _attempt in range(READER_RETRIES + 1):
        man, out = _compile_attempt(module, plan, full, force, keep_input, mm0rs, t0, mdir, inp, mmb, man_path, extra)
        if man["status"] == "PASSED" or out is None:
            return man
        # A reader block met a stub where it needed a proof: keep that theorem verbatim too, and retry.
        V, _real = plan.verbatim(module, L.sub_order(plan.imports, module)[:-1], extra)
        have = {plan.items[d][i][1] for d, i in V}
        new = sorted(set(MATCH_AXIOM.findall(out)) - have - set(extra))
        if not new:
            return man
        extra += new
    return man


READER_RETRIES = 20


def _compile_attempt(module, plan, full, force, keep_input, mm0rs, t0, mdir, inp, mmb, man_path, extra):
    """One compile of module (or its cache hit). Returns (manifest, None if cached or passed, else the log text)."""
    try:
        text, order, nkept, ntotal, src_sha, imps, pfile, nverb = build_input(module, plan, full, extra)
    except NameClash as e:
        return _failed(module, str(e)), None
    data = text.encode("utf-8")
    t_iface = time.perf_counter() - t0
    compiler_sha = L.sha256_memo(mm0rs)
    key = hashlib.sha256(data).hexdigest() + ":" + L.sha256_memo(pfile) + ":" + compiler_sha
    if not force and os.path.exists(man_path) and os.path.exists(mmb):
        try:
            with open(man_path, encoding="utf-8") as f:
                old = json.load(f)
            if old.get("key") == key and old.get("status") == "PASSED" and old.get("mmb_sha256") == L.sha256(mmb):
                try:
                    os.utime(man_path)          # last use, for build_all.py --cache-max-gb
                except OSError:
                    pass
                old["cached"] = True
                return old, None
        except ValueError:
            pass
    os.makedirs(mdir, exist_ok=True)
    for p in (mmb, man_path):                  # never leave an old .mmb next to a new (failed) manifest
        if os.path.exists(p):
            os.remove(p)
    with open(inp, "wb") as f:
        f.write(data)
    log = os.path.join(mdir, "compile.log")
    with open(log, "wb") as lf:
        r, wall, peak = run([mm0rs, "compile", "--cache=false", os.path.basename(inp), os.path.basename(mmb)],
                            cwd=mdir, stdout=lf, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
    with open(log, "rb") as lf:
        out = lf.read()
    ok = r.returncode == 0 and b"contains sorry" not in out and os.path.exists(mmb)
    man = {
        "module": module, "status": "PASSED" if ok else "FAILED", "key": key, "closure": order,
        "imports": imps, "source_sha256": src_sha,
        "input_bytes": len(data), "iface_items_kept": nkept, "iface_items_total": ntotal,
        "pruned": not full, "iface_seconds": round(t_iface, 2), "compile_seconds": round(wall, 2),
        "compile_peak_rss_bytes": peak, "compile_rc": r.returncode,
        "mmb_sha256": L.sha256(mmb) if ok else None, "mmb_bytes": os.path.getsize(mmb) if ok else None,
        "compiler_sha256": compiler_sha,
        "reader_verbatim": nverb, "reader_extra": list(extra),
        "peano": "real" if pfile == os.path.join(L.VENDOR, "peano.mm1") else "interface",
    }
    tail = None
    if not ok:
        tail = re.sub(r"\x1b\[[0-9;]*m", "", out.decode("utf-8", "replace"))
        errs = [ln for ln in tail.splitlines() if ln.startswith("error") or "contains sorry" in ln]
        man["errors"] = errs[:20] or tail.strip().splitlines()[-5:]
    else:
        if os.path.getsize(log) > 1 << 20:     # keep small logs only
            os.remove(log)
        if not keep_input:
            os.remove(inp)
    tmp = man_path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(man, f, indent=1)
    os.replace(tmp, man_path)
    return man, tail


def main():
    a = sys.argv[1:]

    def opt(flag, default=None):
        if flag in a:
            i = a.index(flag); v = a[i + 1]; del a[i:i + 2]; return v
        return default
    bdir = opt("--build", "build-link")
    tools = opt("--tools")
    flags = ("--full", "--force", "--real-peano", "--keep-input")
    full, force, real_peano, keep = (f in a for f in flags)
    a = [x for x in a if x not in flags]
    rc = 0
    for m in a:
        man = compile_one(m, bdir, tools, full, force, real_peano, keep_input=keep)
        print("%-60s %s %6.1fs %6.0fMB peak  items %d/%d%s" % (
            m, man["status"], man["compile_seconds"], man["compile_peak_rss_bytes"] / 1e6,
            man["iface_items_kept"], man["iface_items_total"], " (cached)" if man.get("cached") else ""))
        if man["status"] != "PASSED":
            print("\n".join("   " + e for e in man.get("errors", [])))
            rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
