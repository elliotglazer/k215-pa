"""B6 driver: translate a compiled MM0 PA proof (.mmb over foundation/peano.mm0)
that contains K215_sigma1 / K215_sigma2 into an MM0 HA proof over
foundation/hpeano.mm0, recover the Pi2 statements, and check the result.

  python -B -I b6/b6.py --src <input.mmb> --out <outdir> --tools <dir with mm0-c(.exe)>
                        [--set thm1|b4b] [--repo <mm0-pa-ha root>] [--rehearsal] [--rebuild-lib]

Target sets (--set, default thm1; the description below is for thm1):
  thm1  B6: K215_sigma1, K215_sigma2 (b4/b4_statements.mm0) over the bd defs of
        b4/bd_certs.mm0, library b6/b6-lib.mmb; input b4_final.mmb.
  b4b   B6b: K215 Theorems 1, 2, 3 and G2: K215_sigma1, K215_sigma2 (b4/b4_statements.mm0;
        with thm3_pi2a/b they are the four-sentence Theorem 3), K215_thm2_pi2a,
        K215_thm2_pi2b, K215_thm3_pi2a, K215_thm3_pi2b, K215_G2_pi2 (b4/b4b_statements.mm0),
        over the bd defs of b4/bd_certs.mm0 + b4/bd_certs_b4b.mm0, library
        b6/b6-lib-b4b.mmb (b6/gen_lib.py --set b4b); input b4b_final.mmb. In rehearsal
        mode the sources are the `_of` forms; their extra bound binder (b, which only hT
        mentions) is kept as a binder of the output theorem.

Steps
 1. Pins: foundation/hpeano.mm0, b4/bd_certs.mm0, b4/b4_statements.mm0 (the
    approved texts) and the HA library b6/b6-lib.mmb (made by b6/gen_lib.py
    from sources; --rebuild-lib regenerates it with mm0-rs from --tools and
    reports whether it reproduces the pin).
 2. Translate every def/theorem of the input once (translator.negtrans,
    combined negative + Friedman translation, nat terms as graphs), streaming
    to <outdir>/b6-out.mmb.
 3. Recovery (B5): append
      final mode     K215_sigma1 := rec_K215_sigma1 (K215_sigma1_N at
                     A := E. w bdZfcBot w), K215_sigma2 likewise; the input must
                     contain the theorems K215_sigma1 / K215_sigma2 (b4_final.mm1);
      --rehearsal    K215_sigma1 / K215_sigma2 from K215_sigma1_of /
                     K215_sigma2_of, keeping the translated hypothesis hT
                     (k215LiteralHalts <-> zfcInconsistent at the Friedman
                     parameter) as a hypothesis: the spec line is the approved
                     line with `(hT: $ .. $)` inserted before the colon.
 4. Spec <outdir>/b6-out.mm0 = hpeano.mm0 + the bd defs of b4/bd_certs.mm0
    (verbatim) + (final mode) the K215_sigma1 / K215_sigma2 lines of
    b4/b4_statements.mm0 verbatim. In final mode every translated declaration
    is local; in rehearsal mode the translated defs are public (the kept
    hypothesis mentions them).
 5. mm0-c b6-out.mmb < b6-out.mm0 (must exit 0), and a control: the same .mmb
    against the spec whose last theorem has conclusion F. (must be rejected).
 6. <outdir>/report.json. Exit 0 iff mm0-c accepts and the control is rejected
    (and, in final mode, both final statements are the approved text).
Pure stdlib Python 3; runs on Windows and Linux.
"""
import argparse
import collections
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))

PINS = {
    "foundation/hpeano.mm0": "625beda4d6b1fd9721cce0c555e1bb83cca6e0235f4265aa81456512e9cbdda3",
    "foundation/peano.mm0": "463a7d6e4f4791313dedcfd737053dcf2cc07b466371e263c38a994c6fb72052",
    "b4/bd_certs.mm0": "4c7ef156e0476891acf43802f7dd7932745ecfd2b2664a23c1f8eb4ad1169485",
    "b4/b4_statements.mm0": "e42aa4c38725c0176006c92f6b9ca1a43c6167280d844f23279ea772b50a79a9",
    "b6/b6-lib.mmb": "7d70fd3e8a23cf545f618aa020e011ee11d107f9614c0fba61b2ffbde27bca83",
}
PINS_B4B = {
    "b4/bd_certs_b4b.mm0": "e27ae9594e8030427fe17040fcdfb2a6ab6eab127a6b2e1be91e6a22504a6451",
    "b4/b4b_statements.mm0": "5e2136dab503e4df35029b7ea06375f3afd789d6eefc74e434afd20fa9f68fb0",
    "b6/b6-lib-b4b.mmb": "23d7e5a929887bb5cb826ab08a505d5acb8ba47348dfdb148975682f94e4b798",
}
# (output name, rec lemma, src theorem final, src theorem rehearsal, D, E)
TARGETS = [
    ("K215_sigma1", "rec_K215_sigma1", "K215_sigma1", "K215_sigma1_of", "bdK215Halt", "bdZfcBot"),
    ("K215_sigma2", "rec_K215_sigma2", "K215_sigma2", "K215_sigma2_of", "bdZfcBot", "bdK215Halt"),
]
TARGETS_B4B = TARGETS + [
    (n, "rec_" + n, n, n + "_of", d, e) for n, d, e in (
        ("K215_thm2_pi2a", "bdBB215Prf", "bdZfcBot"),
        ("K215_thm2_pi2b", "bdZfcBot", "bdBB215Prf"),
        ("K215_thm3_pi2a", "bdK215Halt", "bdBB215Prf"),
        ("K215_thm3_pi2b", "bdBB215Prf", "bdK215Halt"),
        ("K215_G2_pi2", "bdZfcConPrf", "bdZfcBot"))]
# per target set: pins, targets, approved statement files, bd-def files (with the import
# line each starts with, dropped from the spec), library
SETS = {
    "thm1": dict(pins=PINS, targets=TARGETS, stmts=["b4/b4_statements.mm0"],
                 bd=[("b4/bd_certs.mm0", 'import "../foundation/peano.mm0";')],
                 lib="b6/b6-lib.mmb", libset="thm1"),
    "b4b": dict(pins=dict(PINS, **PINS_B4B), targets=TARGETS_B4B,
                stmts=["b4/b4_statements.mm0", "b4/b4b_statements.mm0"],
                bd=[("b4/bd_certs.mm0", 'import "../foundation/peano.mm0";'),
                    ("b4/bd_certs_b4b.mm0", 'import "bd_certs.mm0";')],
                lib="b6/b6-lib-b4b.mmb", libset="b4b"),
}
# K215 checker/PINNED.md: mm0-c with the capacity patch (64-bit file size on Windows)
CAPACITY2_MM0C = "bba77622e7540e3f68eb1cc0c202c1cfcdaa2c5bed01754eb0b86d143e4f6371"
# --limits: the mm0-c stack sizes the translator plans for (translator/negtrans.py LIMITS). Only a pre-filter:
# mm0-c itself is the check, so a wrong choice can only make b6 refuse a theorem or mm0-c reject the output.
# capacity3 = K215 checker/mm0-c-capacity3.patch on top of capacity2: HYP_STACK_SIZE and UNIFY_STACK_SIZE 4096.
CHECKER_LIMITS = {"stock": dict(hyps=256, ustack=256), "capacity3": dict(hyps=4096, ustack=4096)}
NAT = 1
T0 = time.time()


def log(*a):
    print("[b6 %8.1fs]" % (time.time() - T0), *a, flush=True)


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 22)
            if not b:
                return h.hexdigest()
            h.update(b)


def exe(tools, name, required=True):
    for n in (name + ".exe", name):
        p = os.path.join(tools, n)
        if os.path.isfile(p):
            return p
    if required:
        raise SystemExit("b6: no %s(.exe) in %s" % (name, tools))
    return None


def read_text(path):
    with open(path, "r", encoding="utf-8", newline="") as f:
        return f.read()


def self_peak_rss():
    """Peak resident set size of this process in bytes (None if unknown)."""
    try:
        if os.name == "nt":
            return _win_peak(None)
        import resource
        r = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        return r if sys.platform == "darwin" else r * 1024
    except Exception:
        return None


def _win_peak(handle):
    import ctypes
    from ctypes import wintypes

    class PMC(ctypes.Structure):
        _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD),
                    ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                    ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                    ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t)]
    k32 = ctypes.WinDLL("kernel32")
    psapi = ctypes.WinDLL("psapi")
    k32.GetCurrentProcess.restype = wintypes.HANDLE
    psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(PMC), wintypes.DWORD]
    h = k32.GetCurrentProcess() if handle is None else wintypes.HANDLE(int(handle))
    c = PMC()
    c.cb = ctypes.sizeof(PMC)
    if not psapi.GetProcessMemoryInfo(h, ctypes.byref(c), c.cb):
        return None
    return int(c.PeakWorkingSetSize)


_WRAP = ("import os,sys,subprocess,resource\n"
         "fd=int(os.environ['B6_FD']); del os.environ['B6_FD']\n"
         "rc=subprocess.call(sys.argv[1:], env=os.environ)\n"
         "m=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss\n"
         "os.write(fd, ('%d %d' % (rc, m*(1 if sys.platform=='darwin' else 1024))).encode())\n"
         "sys.exit(0)\n")


def run_tool(cmd, stdin_path, log_path):
    """Run a tool with stdin from a file; returns (exit code, seconds, peak RSS bytes, log tail)."""
    t = time.time()
    peak = None
    with open(stdin_path, "rb") as fin, open(log_path, "wb") as fout:
        if os.name == "posix":
            # Linux carries the forking parent's peak RSS over fork+exec into the
            # child's ru_maxrss, so the tool runs under a small fresh wrapper
            # process that reports its own child's peak on fd 3.
            r, wfd = os.pipe()
            p = subprocess.Popen([sys.executable, "-I", "-S", "-c", _WRAP] + cmd, stdin=fin, stdout=fout,
                                 stderr=subprocess.STDOUT, pass_fds=(wfd,), env=dict(os.environ, B6_FD=str(wfd)))
            os.close(wfd)
            with os.fdopen(r) as rf:
                info = rf.read().split()
            p.wait()
            rc = int(info[0]) if info else p.returncode
            peak = int(info[1]) if len(info) > 1 else None
        else:
            p = subprocess.Popen(cmd, stdin=fin, stdout=fout, stderr=subprocess.STDOUT)
            rc = p.wait()
            try:
                peak = _win_peak(p._handle)
            except Exception:
                peak = None
    with open(log_path, "rb") as f:
        f.seek(0, 2)
        n = f.tell()
        f.seek(max(0, n - 3000))
        tail = f.read().decode("utf-8", "replace")
    return rc, round(time.time() - t, 2), peak, tail


def approved_lines(stmts_text, targets=TARGETS):
    """The approved declarations of the targets (doc line + theorem line), verbatim.
    stmts_text: the approved statement file(s), concatenated. Each target must be
    stated on one line, exactly once."""
    lines = stmts_text.replace("\r\n", "\n").split("\n")
    out = {}
    for i, l in enumerate(lines):
        for name, *_ in targets:
            if l.startswith("theorem %s " % name):
                if name in out:
                    raise SystemExit("b6: %s stated twice in the approved statements" % name)
                if not l.endswith("$;"):
                    raise SystemExit("b6: approved %s is not a one-line statement" % name)
                doc = lines[i - 1] if i and lines[i - 1].startswith("--|") else None
                out[name] = (doc, l)
    for name, *_ in targets:
        if name not in out:
            raise SystemExit("b6: %s not found in the approved statements" % name)
    return out


def binder_names(line):
    """Variable names of the leading binder groups of a one-line statement."""
    import re
    m = re.match(r"theorem \S+((?:\s*[{(][^:]*:[^})]*[})])*)\s*:", line)
    return re.findall(r"[A-Za-z_][A-Za-z0-9_]*(?=[^:{}()]*:)", m.group(1)) if m else []


def control_spec(spec_text):
    """The spec with the conclusion of its last theorem replaced by F."""
    lines = spec_text.split("\n")
    for i in range(len(lines) - 1, -1, -1):
        l = lines[i]
        if l.startswith("theorem ") or l.startswith("pub theorem "):
            j = l.rindex(": $")
            lines[i] = l[:j] + ": $ F. $;"
            return "\n".join(lines), lines[i]
    raise SystemExit("b6: no theorem in the spec")


def recover(tr, src_ids, name, rec, srcthm, D, E, rehearsal):
    """Append the recovered HA theorem: rec_X applied to the translated theorem."""
    from translator.negtrans import Ctx
    from translator.mmb_format import type_word
    from translator.proof_dag import decode_unify

    class M:
        terms = tr.terms

    def inst(cx, thm, args):
        nodes, root, hyps = decode_unify(M, thm)
        memo = {}

        def go(n0):
            st = [(n0, False)]
            while st:
                n, ex = st.pop()
                if n in memo:
                    continue
                nd = nodes[n]
                if nd[0] == "var":
                    memo[n] = args[nd[1]]
                elif nd[0] == "app":
                    if not ex:
                        st.append((n, True))
                        st.extend((a, False) for a in reversed(nd[2]) if a not in memo)
                        continue
                    memo[n] = cx.mk("app", nd[1], tuple(memo[a] for a in nd[2]))
                else:
                    raise ValueError("dummy in statement")
            return memo[n0]
        return go(root), [go(h) for h in hyps]

    def T(cx, nm, *args):
        return cx.mk("app", tr.tname[nm], tuple(args))

    def thm(cx, tid, args, hyps):
        concl, _ = inst(cx, tr.thms[tid], args)
        return cx.mk("thm", tid, tuple(args), tuple(hyps), concl), concl

    sid = src_ids.get(srcthm)
    if sid is None:
        raise SystemExit("b6: the input has no theorem %s" % srcthm)
    if sid not in tr.hmap:
        raise SystemExit("b6: %s was not translated: %s" % (srcthm, tr.why.get(("thm", sid), "?")))
    oid, needed = tr.hmap[sid]
    if needed:
        raise SystemExit("b6: translated %s has side hypotheses %r" % (srcthm, needed))
    # which binder is universal: the statement is A. u (D u -> E. e D' e)
    sth = tr.src.thms[sid]
    snodes, sroot, _ = decode_unify(tr.src, sth)
    top = snodes[sroot]
    nsrc = len(sth.args)
    from translator.mmb_format import type_bound, type_sort
    if (top[0] != "app" or tr.src.terms[top[1]].name != "al" or nsrc < 2 or (nsrc > 2 and not rehearsal)
            or not all(type_bound(w) and type_sort(w) == NAT for w in sth.args)):
        raise SystemExit("b6: %s is not of the form A. u (D u -> E. e D' e) over 2 bound nat binders%s"
                         % (srcthm, " (+ binders of hT)" if rehearsal else ""))
    # u = the universal binder, e = the existential one; every other binder (rehearsal:
    # the `b` of the _of forms) is mentioned only by hT and stays a binder of the output
    u = snodes[top[2][0]][1]
    im = snodes[top[2][1]]
    ex = snodes[im[2][1]] if im[0] == "app" and tr.src.terms[im[1]].name == "im" else None
    if ex is None or ex[0] != "app" or tr.src.terms[ex[1]].name != "ex" or snodes[ex[2][0]][0] != "var":
        raise SystemExit("b6: %s is not of the form A. u (D u -> E. e D' e)" % srcthm)
    e = snodes[ex[2][0]][1]
    cx = Ctx()
    vu, ve = cx.mk("var", u), cx.mk("var", e)
    w1, nargs = cx.mk("dummy", NAT, 0), nsrc     # hT does not mention u, e (rehearsal)
    Ew = T(cx, "ex", ve, T(cx, E, ve))
    srcargs = [cx.mk("var", i) for i in range(nsrc)] + [Ew]
    srcargs[u], srcargs[e] = vu, w1
    srcargs = tuple(srcargs)
    hyps, sub = [], []
    if rehearsal:
        _, hs = inst(cx, tr.thms[oid], srcargs)
        if len(hs) != 1:
            raise SystemExit("b6: %s has %d hypotheses, expected 1 (hT)" % (srcthm, len(hs)))
        hyps, sub = hs, [cx.mk("hyp", 0)]
    pT, _ = thm(cx, oid, srcargs, sub)
    root, concl = thm(cx, tr.hname[rec], (vu, ve, w1), [pT])
    args = [type_word(True, NAT, 1 << i) for i in range(nargs)]
    return cx, args, concl, hyps, root, nargs


def rehearsal_defs(src, lib, sids):
    """Output names of the defs the translated hypotheses of the source theorems `sids` can
    mention: D_N for every source def D reachable from their hypotheses (through def bodies),
    every lib local def that is not a lib-supplied translation (name not ending in _N), and
    the lib defs reachable from those (through lib def bodies)."""
    from translator.proof_dag import decode_unify

    def reach(m, seeds):
        seen, todo = set(), list(seeds)
        while todo:
            t = todo.pop()
            if t in seen:
                continue
            seen.add(t)
            if m.terms[t].unify:
                nodes, _, _ = decode_unify(m, m.terms[t])
                todo += [nd[1] for nd in nodes if nd[0] == "app"]
        return seen

    seeds = set()
    for sid in sids:
        nodes, _, hyps = decode_unify(src, src.thms[sid])
        seeds |= {nd[1] for nd in nodes if nd[0] == "app"}
    names = {src.terms[t].name + "_N" for t in reach(src, seeds) if src.terms[t].unify}
    lname = {t.name: t.id for t in lib.terms}
    lseeds = [t.id for t in lib.terms if not t.name.endswith("_N")] + [lname[n] for n in names if n in lname]
    return names | {lib.terms[t].name for t in reach(lib, lseeds)}


def _pi2_vars(tr, sid):
    """Source binder indices (universal, existential) of A. u (D u -> E. e D' e)."""
    from translator.proof_dag import decode_unify
    sn, sr, _ = decode_unify(tr.src, tr.src.thms[sid])
    top = sn[sr]
    im = sn[top[2][1]]
    ex = sn[im[2][1]]
    return sn[top[2][0]][1], sn[ex[2][0]][1]


def expr_text(tr, cx, e, names):
    """MM0 prefix rendering of an output expression (vars named by `names`)."""
    out, st = [], [e]
    while st:
        x = st.pop()
        if isinstance(x, str):
            out.append(x)
            continue
        nd = cx.nodes[x]
        if nd[0] == "var":
            out.append(names[nd[1]])
        elif nd[0] == "app":
            nm = tr.terms[nd[1]].name
            if not nd[2]:
                out.append(nm)
                continue
            seq = ["(", nm]
            for a in nd[2]:
                seq += [" ", a]
            seq.append(")")
            st.extend(reversed(seq))
        else:
            raise SystemExit("b6: unexpected node in a hypothesis: %r" % (nd,))
    s = "".join(out)
    return s[1:-1] if s.startswith("(") else s


def main(argv=None):
    ap = argparse.ArgumentParser(prog="b6.py")
    ap.add_argument("--src", required=True, help="input .mmb (peano-based, contains K215_sigma1/2)")
    ap.add_argument("--out", required=True, help="output directory")
    ap.add_argument("--tools", required=True, help="directory with mm0-c(.exe) (and mm0-rs for --rebuild-lib)")
    ap.add_argument("--repo", default=os.path.dirname(HERE), help="mm0-pa-ha root")
    ap.add_argument("--set", default=None, choices=sorted(SETS),
                    help="target set: thm1 (K215_sigma1/2, B6) or b4b (+ Theorems 2/3 and G2, B6b); default: b4b "
                         "when the --src file is named b4b_*.mmb (the K215 runner passes no --set), else thm1")
    ap.add_argument("--limits", default="stock", choices=sorted(CHECKER_LIMITS),
                    help="mm0-c stack sizes to plan for: stock (256 hypotheses, 256 unify stack) or capacity3 "
                         "(4096 each; the K215 runner passes this when it uses the capacity3 mm0-c)")
    ap.add_argument("--rehearsal", action="store_true",
                    help="recover from the _of forms, keeping hT as a hypothesis")
    ap.add_argument("--rebuild-lib", action="store_true",
                    help="regenerate b6-lib.mmb from sources with mm0-rs (from --tools)")
    ns = ap.parse_args(argv)
    if ns.set is None:
        ns.set = "b4b" if os.path.basename(ns.src).startswith("b4b_") else "thm1"
    repo = os.path.abspath(ns.repo)
    sys.path.insert(0, repo)
    out = os.path.abspath(ns.out)
    os.makedirs(out, exist_ok=True)
    tools = os.path.abspath(ns.tools)
    mm0c = exe(tools, "mm0-c")
    cfg = SETS[ns.set]
    report = dict(driver="b6/b6.py", mode="rehearsal" if ns.rehearsal else "final", target_set=ns.set,
                  argv=sys.argv[1:] if argv is None else argv,
                  python=sys.version.split()[0], platform=platform.platform(),
                  tools={"mm0-c": [mm0c, sha256(mm0c)]})
    rpath = os.path.join(out, "report.json")

    def save():
        report["total_seconds"] = round(time.time() - T0, 1)
        with open(rpath, "w", newline="\n") as f:
            json.dump(report, f, indent=1)

    # 1. pins
    pins = {}
    for rel, want in cfg["pins"].items():
        p = os.path.join(repo, *rel.split("/"))
        got = sha256(p) if os.path.isfile(p) else None
        pins[rel] = dict(sha256=got, pinned=want, ok=got == want)
    report["pins"] = pins
    lib_path = os.path.join(repo, *cfg["lib"].split("/"))
    if ns.rebuild_lib:
        sys.path.insert(0, os.path.join(repo, "b6"))
        import gen_lib
        log("rebuilding %s from sources" % cfg["lib"])
        lib_path, h = gen_lib.build(tools, os.path.join(out, "lib"), cfg["libset"])
        report["lib_rebuilt"] = dict(path=lib_path, sha256=h, reproduces_pin=h == cfg["pins"][cfg["lib"]])
        tools_rs = exe(tools, "mm0-rs")
        report["tools"]["mm0-rs"] = [tools_rs, sha256(tools_rs)]
    bad = [k for k, v in pins.items() if not v["ok"] and not (ns.rebuild_lib and k == cfg["lib"])]
    if bad:
        report["error"] = "pin mismatch: %s" % bad
        save()
        log("PIN MISMATCH", bad)
        return 2
    hpeano = read_text(os.path.join(repo, "foundation", "hpeano.mm0"))
    bd_body = ""
    for rel, imp in cfg["bd"]:
        bd = read_text(os.path.join(repo, *rel.split("/"))).replace("\r\n", "\n")
        bd_body += bd.split(imp, 1)[1]
    approved = approved_lines("\n".join(read_text(os.path.join(repo, *rel.split("/")))
                                        for rel in cfg["stmts"]), cfg["targets"])
    lib_spec = hpeano + bd_body
    return drive(report, save, ns.src, out, mm0c, lib_path, lib_spec, approved, cfg["targets"], ns.rehearsal,
                 ns.limits)


def drive(report, save, src_path, out, mm0c, lib_path, lib_spec, approved, targets, rehearsal, limits="stock"):
    """Steps 2-6 (translate, recover, spec, mm0-c, control, report); `targets`
    as TARGETS, `approved` maps each target name to (doc line, theorem line).
    Separate from main() so a test can run the final-mode path on B5's
    synthetic Pi2 theorem with the B5 library."""
    class NS:
        pass
    ns = NS()
    ns.rehearsal = rehearsal
    # 2. input
    src_path = os.path.abspath(src_path)
    log("input", src_path)
    report["input"] = dict(path=src_path, bytes=os.path.getsize(src_path))
    t = time.time()
    report["input"]["sha256"] = sha256(src_path)
    report["timings"] = {"sha256_input": round(time.time() - t, 1)}
    from translator.mmb_reader import read_mmb
    from translator.negtrans import NegTrans, LIMITS
    LIMITS.update(CHECKER_LIMITS[limits])
    report["limits"] = limits
    t = time.time()
    src = read_mmb(src_path)
    lib = read_mmb(lib_path)
    report["timings"]["read_tables"] = round(time.time() - t, 1)
    report["input"].update(sorts=len(src.sorts), terms=len(src.terms), thms=len(src.thms))
    log("tables read: %d terms, %d theorems" % (len(src.terms), len(src.thms)))
    src_ids = {}
    for th in src.thms:
        if th.name is not None:
            src_ids.setdefault(th.name, th.id)
    want = [x[3] if ns.rehearsal else x[2] for x in targets]
    missing = [n for n in want if n not in src_ids]
    if missing:
        report["error"] = "input has no theorem(s) %s%s" % (
            missing, "" if ns.rehearsal else " (use --rehearsal for K215_sigma{1,2}_of inputs)")
        save()
        log(report["error"])
        return 2

    # 3. translate
    out_mmb = os.path.join(out, "b6-out.mmb")
    out_mm0 = os.path.join(out, "b6-out.mm0")
    tr = NegTrans(src, lib)
    head = ("-- B6 (b6/b6.py): the recovered Pi2 statements over hpeano, stated with the approved text "
            "of b4/b4_statements.mm0" + ("; REHEARSAL: translated defs (public, for hT) and hT as hypothesis"
                                         if ns.rehearsal else "") + ".")
    # rehearsal: public = the defs the kept hypotheses hT need (stock mm0-c's spec parser has a
    # fixed-size token trie: making every translated def of a real closure public overflows it)
    pubdefs = rehearsal_defs(src, lib, [src_ids[x[3]] for x in targets]) if ns.rehearsal else False
    if ns.rehearsal:
        report["rehearsal_public_defs"] = len(pubdefs)
    tr.stream_to(out_mmb, lib_spec, def_pub=pubdefs, thm_pub=None, spool_dir=out, header=head)
    size = report["input"]["bytes"]
    t = time.time()
    tr.run(progress=lambda i, off: log("statement %d, input offset %d of %d" % (i, off, size)))
    report["timings"]["translate"] = round(time.time() - t, 1)
    fails = [(k, v) for k, v in tr.why.items() if k[0] == "thm" and src.thms[k[1]].kind != "axiom"]
    roots = [(src.thms[k[1]].name, v) for k, v in fails if not v.startswith("uses")]
    report["translation"] = dict(
        stats=tr.stats, theorems_failed=len(fails), root_failures=roots[:50],
        root_failure_kinds=sorted(collections.Counter(re.sub(r"\d+", "N", v) for _, v in roots).items(),
                                  key=lambda kv: -kv[1]),
        defs_failed=[(src.terms[k[1]].name, v) for k, v in tr.why.items() if k[0] == "term"][:50],
        axioms_unmapped=[(src.thms[k[1]].name, v) for k, v in tr.why.items()
                         if k[0] == "thm" and src.thms[k[1]].kind == "axiom"],
        renamed=tr.renamed[:50], renamed_count=len(tr.renamed),
        mm0c_limits=dict(LIMITS), max_use={k: list(v) for k, v in tr.usage.items()},
        src_max_use={k: list(v) for k, v in tr.src_usage.items()},
        max_ratio_out_over_src={k: list(v) for k, v in tr.ratio.items()},
        limit_failures=tr.limit_fail[:50])
    log("translated %d theorems, %d defs; %d failed (%d root)" % (
        tr.stats["thms"], tr.stats["defs"], len(fails), len(roots)))

    # 4. recovery + spec
    final = []
    for name, rec, sthm, rthm, D, E in targets:
        oname = name
        try:
            cx, args, concl, hyps, root, nargs = recover(tr, src_ids, name, rec,
                                                         rthm if ns.rehearsal else sthm, D, E,
                                                         ns.rehearsal)
        except SystemExit as e:
            report["error"] = str(e)
            save()
            log(str(e))
            return 1
        doc, line = approved[name]
        if ns.rehearsal:      # the approved line with the translated hT as hypothesis
            # output var i = source binder i. The approved plain line names the two Pi2
            # binders in source order; the extra binders of an _of form (only hT mentions
            # them) must come after them and are named b, b1, ..
            vn = binder_names(line)
            pu, pe = _pi2_vars(tr, src_ids[rthm])
            if len(vn) != 2 or sorted((pu, pe)) != [0, 1]:
                raise SystemExit("b6: %s: expected the two Pi2 binders first, approved binders %r" % (rthm, vn))
            extra = ["b" if i == 0 else "b%d" % i for i in range(nargs - 2)]
            src_names = vn + extra
            if extra:
                g = line.index(": nat}")
                line = line[:g] + " " + " ".join(extra) + line[g:]
            j = line.index(": $")
            line = line[:j] + " (hT: $ %s $)" % expr_text(tr, cx, hyps[0], src_names) + line[j:]
            doc = "--| REHEARSAL: %s with the K215 statement (translated) as hypothesis hT." % name
        tr.spec.append("")
        tr.spec.append(doc)
        tid, _ = tr.add_thm(oname, args, cx, concl, hyps, root, nargs, pub=True, spec_line=line)
        final.append(tid)
    t = time.time()
    tr.finish_stream(out_mm0)
    report["timings"]["write"] = round(time.time() - t, 1)
    report["translator_peak_rss_bytes"] = self_peak_rss()
    spec_text = read_text(out_mm0)
    report["output"] = dict(mmb=out_mmb, mmb_bytes=os.path.getsize(out_mmb), mm0=out_mm0,
                            mm0_bytes=os.path.getsize(out_mm0))
    t = time.time()
    report["output"]["mmb_sha256"] = sha256(out_mmb)
    report["output"]["mm0_sha256"] = sha256(out_mm0)
    report["timings"]["sha256_output"] = round(time.time() - t, 1)
    pubs = []
    for tid in final:
        th = tr.thms[tid]
        line = next(l for l in spec_text.split("\n") if l.startswith("theorem %s " % th.name))
        ent = dict(name=th.name, spec_text=line, rendered=tr.print_decl(th, False))
        ent["approved_text"] = approved[th.name][1]
        ent["is_approved_text"] = line == approved[th.name][1]
        if ns.rehearsal:
            j = line.find(" (hT: $")
            k = line.find(" $)", j)
            plain = line[:j] + line[k + 3:]
            for x in ("b", "b1", "b2"):   # extra binders of the _of forms
                plain = plain.replace(" %s: nat}" % x, ": nat}")
            ent["is_approved_text_plus_hT"] = j > 0 and plain == approved[th.name][1]
        pubs.append(ent)
    report["final_public_theorems"] = pubs
    report["spec_layout"] = ("hpeano.mm0 verbatim + the bd defs of the target set's bd_certs*.mm0 verbatim "
                             "(import lines dropped)"
                             + (" + the translated defs hT needs (public, rehearsal)" if ns.rehearsal else "")
                             + " + the final theorems")
    del src, lib

    # 5. mm0-c and control
    if os.name == "nt" and report["output"]["mmb_bytes"] >= 1 << 31 and \
            report["tools"]["mm0-c"][1] != CAPACITY2_MM0C and limits != "capacity3":
        report["warning"] = ("output is over 2 GiB: stock Windows mm0-c reads the size with a 32-bit "
                             "fstat; use the K215 capacity2 build (sha256 %s)" % CAPACITY2_MM0C)
        log("WARNING", report["warning"])
    log("mm0-c", out_mmb)
    rc, secs, peak, tail = run_tool([mm0c, out_mmb], out_mm0, os.path.join(out, "mm0c.log"))
    report["mm0c"] = dict(exit=rc, seconds=secs, peak_rss_bytes=peak, log_tail=tail[-1500:])
    ctext, cline = control_spec(spec_text)
    cpath = os.path.join(out, "b6-control.mm0")
    with open(cpath, "w", newline="\n") as f:
        f.write(ctext)
    rc2, secs2, peak2, tail2 = run_tool([mm0c, out_mmb], cpath, os.path.join(out, "control.log"))
    report["control"] = dict(spec=cpath, changed_line=cline, exit=rc2, rejected=rc2 != 0,
                             seconds=secs2, peak_rss_bytes=peak2, log_tail=tail2[-1500:])
    ok = rc == 0 and rc2 != 0
    key = "is_approved_text_plus_hT" if ns.rehearsal else "is_approved_text"
    ok = ok and len(pubs) == len(targets) and all(p[key] for p in pubs)
    report["result"] = "PASS" if ok else "FAIL"
    save()
    log("mm0-c exit %d; control exit %d; %s" % (rc, rc2, report["result"]))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
