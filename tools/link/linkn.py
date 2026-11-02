"""N-way MMB linker: separately compiled pa-mm0 modules (compile_one.py) -> one .mmb for mm0-c.

  python3 linkn.py ROOT --build DIR --spec JOINED.mm0 OUT.mmb OUT.mm0 [--peano PEANO.mmb] [--reorder]

Inputs. DIR/<m>/<m>.mmb for every module m of ROOT's .mm1 import closure (compile_one.py output: peano +
interface copies of m's dependencies + m's own statements), DIR/_peano/peano.mmb (peano.mm1 compiled alone;
made here if missing), and JOINED.mm0 = `mm0-rs join ROOT.mm0`, the spec the monolithic check uses.

Link order. peano, then the modules in check.py's flat order (post-order DFS of the .mm1 imports), each
contributing its OWN statements in its own order: exactly the declaration sequence of the monolithic
flattened compile, so the public statements come out in the order of the joined spec.

Resolution, per module m with closure C(m) (m's transitive imports, plus peano):
  * a term/def or theorem/axiom of m.mmb whose name is declared by a module of C(m) is a COPY: it is
    identified with that declaration (closure-scoped, so a local name reused in an unrelated subtree is
    harmless; two candidates in C(m) is an error). Its statement must equal the original's after
    renumbering (args, return/conclusion, hypotheses, def body), else LINK ERROR. A copied axiom is a
    stub; a copied theorem is one an annotation or `do` block re-derived (its proof is dropped).
  * every other declaration is m's OWN: appended with renumbered term/theorem ids, keeping its visibility.
    An own axiom (a stub with no theorem of that name in C(m)) or an own primitive term is a LINK ERROR.
Afterwards only peano's axioms remain (counted; tools/gen7/axioms.py re-checks against peano.mm0's text).

Spec. The public statements (sorts, terms, public defs, axioms, public theorems) of OUT.mmb are compared,
by kind and name, with the statements of JOINED.mm0. If they agree in order, OUT.mm0 is a byte copy of
JOINED.mm0. Otherwise LINK ERROR, unless --reorder: then OUT.mm0 is JOINED.mm0's statements reordered to the
output order (notations follow their term), as tools/gen7/link.py does.

Trust: none of this is trusted. mm0-c checks OUT.mmb against OUT.mm0; a stub whose text differs from the
real theorem, a def body that differs, a missing or misordered statement each make it reject.
"""
import hashlib
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mm1lib as L  # noqa: E402
from rawmmb import (RawMMB, RawWriter, Entry, remap, PROOF_T, PROOF_H,  # noqa: E402
                    STMT_DEF, STMT_AXIOM, STMT_THM, STMT_SORT)

NOTA = ("prefix", "infixl", "infixr", "notation", "coercion")


# TEST ONLY (selftest.py): skip the linker's own statement comparison, to show that mm0-c alone rejects a
# mismatched stub or def. Never set it in production; the result is still only trusted via mm0-c.
NO_VERIFY = os.environ.get("LINKN_TEST_NO_VERIFY") == "1"


class LinkError(Exception):
    pass


def closures(order, imports):
    idx = {m: i + 1 for i, m in enumerate(order)}        # 0 = peano
    clos = {}
    for m in order:                                       # post-order: imports first
        c = {0}
        for d in imports[m]:
            c.add(idx[d])
            c |= clos[d]
        clos[m] = c
    return idx, clos


def ensure_peano(path, tools):
    """peano.mm1 compiled alone, rebuilt when peano.mm1 or mm0-rs changed (tag file next to it)."""
    src = os.path.join(L.VENDOR, "peano.mm1")
    mm0rs = L.tool(tools, "mm0-rs")
    tag = "%s:%s" % (L.sha256(src), L.sha256(mm0rs))
    tagf = path + ".key"
    try:
        with open(tagf, encoding="utf-8") as f:
            if os.path.exists(path) and f.read() == tag:
                return
    except OSError:
        pass
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp.mmb"
    r = subprocess.run([mm0rs, "compile", "--cache=false", src, tmp], capture_output=True, stdin=subprocess.DEVNULL)
    if r.returncode:
        raise LinkError("peano.mm1 compile failed: " + (r.stdout + r.stderr).decode("utf-8", "replace")[-2000:])
    os.replace(tmp, path)
    with open(tagf, "w", encoding="utf-8") as f:
        f.write(tag)


class Linker:
    """Byte-level linker (rawmmb). Global tables hold rawmmb.Entry objects (raw binder words + unify bytes in
    output numbering); a copy is checked by comparing its renumbered raw bytes with the original's."""

    def __init__(self, out_mmb):
        self.w = RawWriter(out_mmb, os.path.dirname(os.path.abspath(out_mmb)))
        self.terms, self.thms = [], []
        self.tname, self.hname = {}, {}       # name -> [(module index, global id)]
        self.order = []                       # (kind letter, name, public) in output order
        self.sorts = None
        self.peano = None                     # (term names, thm names, term slices, thm slices) of peano
        self.stats = {"stubs_resolved": 0, "rederived_dropped": 0, "peano_copies": 0, "copies_terms": 0,
                      "own_terms": 0, "own_thms": 0, "axioms": 0, "modules": 0, "own_proof_bytes": 0}

    def _lookup(self, table, name, clos, what):
        c = [g for j, g in table.get(name, ()) if j in clos]
        if len(c) > 1:
            raise LinkError("%s %s: %d declarations in the closure" % (what, name, len(c)))
        return c[0] if c else None

    @staticmethod
    def _slices(M, ents, n):
        """Raw slices [p_i, p_{i+1}) of the first n-1 entries (the last one's end is not delimited)."""
        d = M.d
        return [d[ents[i][3]:ents[i + 1][3]] for i in range(n - 1)]

    def _peano_prefix(self, M):
        """Number of leading terms / theorems of M that are byte-identical to peano's (fast path for the
        peano part every module contains). 0, 0 if M does not start with peano."""
        pt, ph, st, sh = self.peano
        if M.term_names[:len(pt)] != pt or M.thm_names[:len(ph)] != ph:
            return 0, 0
        if self._slices(M, M.term_ent, len(pt)) != st or self._slices(M, M.thm_ent, len(ph)) != sh:
            return 0, 0
        return len(pt) - 1, len(ph) - 1          # the last peano entry goes through the general path

    def add_module(self, mi, mname, path, clos, peano_axioms):
        M = RawMMB(path)
        sorts = list(zip(M.sort_names, M.sort_mods))
        if self.sorts is None:
            self.sorts = sorts
            for n, m in sorts:
                self.w.add_sort(m, n)
        elif sorts != self.sorts:
            raise LinkError("%s: sorts differ from peano's" % mname)
        if mi == 0:
            self.peano = (M.term_names, M.thm_names, self._slices(M, M.term_ent, M.nterms),
                          self._slices(M, M.thm_ent, M.nthms))
            kt = kh = 0
        else:
            kt, kh = self._peano_prefix(M)
        tm = list(range(kt)) + [0] * (M.nterms - kt)
        own_t = set()
        self.stats["peano_copies"] += kt + kh
        for i in range(kt, M.nterms):
            name = M.term_names[i]
            g = self._lookup(self.tname, name, clos, "term")
            sort, nargs, words, u = M.term(i, tm)
            if g is None:
                g = len(self.terms)
                tm[i] = g
                e = Entry(name, M.var_names("t", i), None, nargs, sort, bytes(words), u)
                self.terms.append(e)
                self.w.add_term(e)
                own_t.add(i)
                self.tname.setdefault(name, []).append((mi, g))
                self.stats["own_terms"] += 1
            else:
                tm[i] = g
                r = self.terms[g]
                if (r.sort, r.words) != (sort, words):
                    raise LinkError("%s: term %s: signature differs from the original" % (mname, name))
                if r.unify != u and not NO_VERIFY:
                    raise LinkError("%s: def %s: body differs from the original" % (mname, name))
                self.stats["copies_terms"] += 1
        kinds = {}
        stl = list(M.stmts())
        for op, k, ref, s, e in stl:
            if k == "h":
                kinds[ref] = op
        sm = list(range(kh)) + [0] * (M.nthms - kh)
        own_h = set()
        for i in range(kh, M.nthms):
            name = M.thm_names[i]
            g = self._lookup(self.hname, name, clos, "theorem")
            nargs, words, u = M.thm(i, tm)
            if g is None:
                if kinds[i] == STMT_AXIOM and mi != 0:
                    raise LinkError("%s: axiom %s has no theorem of that name in its closure" % (mname, name))
                g = len(self.thms)
                sm[i] = g
                e = Entry(name, M.var_names("h", i), M.hyp_names(i), nargs, 0, bytes(words), u)
                self.thms.append(e)
                self.w.add_thm(e)
                own_h.add(i)
                self.hname.setdefault(name, []).append((mi, g))
                self.stats["own_thms"] += 1
            else:
                sm[i] = g
                r = self.thms[g]
                if (r.words != words or r.unify != u) and not NO_VERIFY:
                    raise LinkError("%s: %s %s: statement differs from the original" % (
                        mname, "stub" if kinds[i] == STMT_AXIOM else "theorem", name))
                self.stats["stubs_resolved" if kinds[i] == STMT_AXIOM else "rederived_dropped"] += 1
        d = M.d
        for op, k, ref, s, e in stl:
            if k == "s":
                if mi == 0:
                    self.w.add_stmt(STMT_SORT, body=bytes(d[s:e]))
                    self.order.append(("s", M.sort_names[ref], True))
                continue
            if k == "t":
                if ref not in own_t:
                    continue
                if not M.term_ent[ref][1] & 0x80 and mi != 0:
                    raise LinkError("%s: primitive term %s outside peano" % (mname, M.term_names[ref]))
                name = M.term_names[ref]
            else:
                if ref not in own_h:
                    continue
                name = M.thm_names[ref]
                if op == STMT_AXIOM:
                    if name not in peano_axioms:
                        raise LinkError("%s: non-peano axiom %s" % (mname, name))
                    self.stats["axioms"] += 1
            if mi == 0:
                body = bytes(d[s:e])
            else:
                body, end = remap(d, s, PROOF_T, tm, PROOF_H, sm)
                if end != e:
                    raise LinkError("%s: %s: proof stream ends before its statement" % (mname, name))
                self.stats["own_proof_bytes"] += e - s
            self.w.add_stmt(op, body=body)
            self.order.append((k, name, op in (STMT_DEF, STMT_AXIOM, STMT_THM)))
        self.stats["modules"] += 1
        M.d.close()

    def finish(self):
        self.w.finish()


def spec_items(spec_text):
    return [(kw, n, s) for kw, n, s in L.statements(spec_text)]


def write_spec(spec_path, out_mm0, order, reorder):
    text = L.read_text(spec_path)
    items = spec_items(text)
    kmap = {"sort": "s", "term": "t", "def": "t", "axiom": "h", "theorem": "h"}
    want = [(kmap[kw], n) for kw, n, _ in items if kw in kmap]
    have = [(k, n) for k, n, pub in order if pub]
    if want == have:
        with open(out_mm0, "wb") as f:
            f.write(open(spec_path, "rb").read())
        return "identical"
    sw, sh = set(want), set(have)
    if sw != sh or len(want) != len(have):
        raise LinkError("public statements differ from the spec: %d only in the spec (e.g. %s), %d only in the "
                        "output (e.g. %s)" % (len(sw - sh), sorted(sw - sh)[:3], len(sh - sw), sorted(sh - sw)[:3]))
    first = next(i for i, (a, b) in enumerate(zip(want, have)) if a != b)
    if not reorder:
        raise LinkError("public statement order differs from the spec at #%d: spec %s, output %s (use --reorder)"
                        % (first, want[first], have[first]))
    pos = {x: i for i, x in enumerate(have)}
    head, body, last, byname = [], [], None, {}
    for kw, n, s in items:
        if kw in kmap:
            body.append([pos[(kmap[kw], n)], s, []])
            last = body[-1]
            if kw in ("term", "def"):
                byname[n] = last
        elif kw in NOTA and n in byname:
            byname[n][2].append(s)
        else:
            (last[2] if last else head).append(s)
    body.sort(key=lambda b: b[0])
    with open(out_mm0, "w", newline="\n", encoding="utf-8") as f:
        f.write("\n".join(head) + "\n")
        for _, s, extra in body:
            f.write(s + "\n")
            for e in extra:
                f.write(e + "\n")
    return "reordered"


def peano_axiom_names():
    return {n for kw, n, _ in L.statements(L.read_text(os.path.join(L.VENDOR, "peano.mm0"))) if kw == "axiom"}


def link(root, bdir, spec, out_mmb, out_mm0, peano_mmb=None, tools=None, reorder=False):
    t0 = time.perf_counter()
    tools = tools or L.default_tools()
    order, imports = L.closure_order(root)
    idx, clos = closures(order, imports)
    peano_mmb = peano_mmb or os.path.join(bdir, "_peano", "peano.mmb")
    ensure_peano(peano_mmb, tools)
    pax = peano_axiom_names()
    lk = Linker(out_mmb)
    lk.add_module(0, "peano", peano_mmb, {0}, pax)
    for m in order:
        try:
            with open(os.path.join(bdir, m, "link.json"), encoding="utf-8") as f:
                man = json.load(f)
        except (OSError, ValueError):
            raise LinkError("module %s was not compiled (no link.json)" % m)
        path = os.path.join(bdir, m, m + ".mmb")
        if man.get("status") != "PASSED":
            raise LinkError("module %s was not compiled successfully" % m)
        if man.get("closure") != L.sub_order(imports, m):
            raise LinkError("module %s: stale build (closure changed)" % m)
        lk.add_module(idx[m], m, path, clos[m], pax)
    lk.finish()
    if lk.stats["axioms"] != len(pax):
        raise LinkError("%d axioms in the output, peano.mm0 has %d" % (lk.stats["axioms"], len(pax)))
    how = write_spec(spec, out_mm0, lk.order, reorder)
    info = dict(lk.stats, root=root, terms=len(lk.terms), thms=len(lk.thms), spec=how,
                link_seconds=round(time.perf_counter() - t0, 2), out_bytes=os.path.getsize(out_mmb))
    return info


def main():
    a = sys.argv[1:]

    def opt(flag, default=None):
        if flag in a:
            i = a.index(flag); v = a[i + 1]; del a[i:i + 2]; return v
        return default
    bdir = opt("--build", "build-link")
    spec = opt("--spec")
    peano = opt("--peano")
    tools = opt("--tools")
    reorder = "--reorder" in a
    a = [x for x in a if x != "--reorder"]
    if len(a) != 3 or not spec:
        raise SystemExit(__doc__)
    try:
        info = link(a[0], bdir, spec, a[1], a[2], peano, tools, reorder)
    except LinkError as e:
        print("LINK ERROR:", e)
        return 1
    print("linked", json.dumps(info))
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    sys.exit(main())
