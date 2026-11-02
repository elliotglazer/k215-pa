"""Link-check a root: link the separately compiled modules, then the trusted checks of pa-mm0/check.py.

  python3 link_check.py ROOT --build DIR [--tools TOOLDIR] [--out OUTDIR] [--reorder] [--progress FILE]

Steps (each timed, report in OUTDIR/report.json; OUTDIR defaults to DIR/_link/ROOT; logs OUTDIR/<stage>.log):
  0. sources: check.py's source_graph: the .mm0 and .mm1 import closure of ROOT, pinned peano vendor files
              (same sha256 values as check.py), LF line endings, no `axiom` in any project source
  1. join:    mm0-rs join pa-mm0/ROOT.mm0 -> ROOT-joined.mm0 (check.py's spec, same command)
  2. link:    linkn.py -> ROOT.mmb (+ ROOT.mm0, which must be byte-identical to the joined spec unless --reorder)
  3. check:   mm0-c ROOT.mmb < ROOT-joined.mm0, must exit 0 (check.py's "check-original")
  4. axioms:  (as tools/gen7/axioms.py) the .mmb has as many axioms as the spec, and the spec's axioms are exactly
              peano.mm0's 26, by statement text
  5. false:   the last theorem of pa-mm0/ROOT.mm0 gets the conclusion F. in the joined spec (check.py's control,
              same code); mm0-c must reject (check.py's "reject-false")
  6. sources unchanged since step 0 (check.py: "A source changed during verification")
Exit 0 iff all pass. report.json has check.py's report fields (status PASSED / FAILED, spec_sha256, sources, ...)
plus the link-specific ones. Requires every module of the closure built by build_all.py.

Trust: steps 0, 1, 3, 4, 5 and 6 are check.py's own checks on the same inputs; mm0-c checks every proof of the
linked .mmb against the joined spec. Interfaces, pruning, the separate compiles and the linker are untrusted.
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
from runstat import run  # noqa: E402

# pa-mm0/check.py's pinned vendor hashes and source rules, verbatim.
EXPECTED_VENDOR = {
    "peano.mm0": "463a7d6e4f4791313dedcfd737053dcf2cc07b466371e263c38a994c6fb72052",
    "peano.mm1": "13fd383aa02e434cba1350e9a8f12c440b5114d22f26506fece4aecdf1370079",
    "peano.mmu": "3405aa9f99417850acb766845cc0031651bcaacb7dc9b87e25e6598bdf872cfd",
}
MODULE_NAME = re.compile(r"[a-z][a-z0-9_]*\Z")
NON_CODE = re.compile(r'--[^\n]*|"(?:\\.|[^"\\])*"|\$[^$]*\$', re.DOTALL)
SCOPE_DEFAULT = "PA theorems in %s; exact claims are in the separately checked source specification"


class CheckError(Exception):
    pass


def source_graph(module, pa, vendor):
    """check.py's source_graph: {path: sha256} of the .mm0 + .mm1 import closure, vendor files allowed only as
    the pinned peano.{mm0,mm1,mmu}; rejects CR line endings and any `axiom` in project sources."""
    if not MODULE_NAME.fullmatch(module):
        raise CheckError("Invalid module name")
    root = os.path.realpath(pa)
    allowed = {os.path.realpath(os.path.join(vendor, "peano." + s)) for s in ("mm0", "mm1", "mmu")}
    pending = [os.path.join(pa, module + ".mm0"), os.path.join(pa, module + ".mm1")]
    found = {}
    while pending:
        path = os.path.realpath(pending.pop())
        if path in found:
            continue
        if path in allowed:
            found[path] = L.sha256(path)
            continue
        if os.path.commonpath([root, path]) != root:
            raise CheckError("Unpinned external import: " + path)
        with open(path, "rb") as f:
            raw = f.read()
        if b"\r" in raw:
            raise CheckError("MM0 sources require LF line endings: " + path)
        content = raw.decode("utf-8")
        if re.search(r"\baxiom\b", NON_CODE.sub(" ", content)):
            raise CheckError("Project source adds an axiom: " + path)
        found[path] = hashlib.sha256(raw).hexdigest()
        pending.extend(os.path.join(os.path.dirname(path), c) for c in L.IMPORT.findall(content))
    return found


def axiom_check(mmb, spec, peano0):
    """As tools/gen7/axioms.py: mm0-c matches the k-th axiom of the .mmb with the k-th axiom of the spec, so it
    suffices that the .mmb has as many axioms as the spec and that the spec's axiom statements are exactly
    peano.mm0's (whitespace-normalized text, comments removed)."""
    from rawmmb import RawMMB, STMT_AXIOM
    m = RawMMB(mmb)
    n_mmb = sum(1 for op, k, *_ in m.stmts() if op == STMT_AXIOM)
    m.d.close()
    norm = lambda path: [" ".join(s.split()) for kw, n, s in L.statements(L.read_text(path)) if kw == "axiom"]
    sp, pa = norm(spec), norm(peano0)
    ok = n_mmb == len(sp) and sorted(sp) == sorted(pa) and len(set(pa)) == len(pa)
    return ok, "axioms: mmb %d, spec %d, peano.mm0 %d; spec axioms not in peano.mm0: %d" % (
        n_mmb, len(sp), len(pa), len(set(sp) - set(pa)))


def theorem_names(root_mm0):
    with open(root_mm0, encoding="utf-8") as f:
        return re.findall(r"(?m)^theorem\s+(\w+)", f.read())


def false_spec(spec_bytes, root_mm0):
    """check.py's control, same code: the last theorem of ROOT.mm0 gets the conclusion F. in the joined spec."""
    names = theorem_names(root_mm0)
    marker = b"theorem " + names[-1].encode("ascii")
    prefix, tail = spec_bytes.rsplit(marker, 1)
    binders, body = tail.split(b"$", 1)
    _, suffix = body.split(b"$;", 1)
    return prefix + marker + binders + b"$ F. $;" + suffix, names[-1]


def write_json(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        json.dump(obj, f, indent=2)
        f.write("\n")
    os.replace(tmp, path)


def link_check(root, bdir, tools, out, reorder=False, progress=None):
    os.makedirs(out, exist_ok=True)
    mm0rs, mm0c = L.tool(tools, "mm0-rs"), L.tool(tools, "mm0-c")
    pa, vendor = L.PA, L.VENDOR
    src = os.path.join(pa, root + ".mm0")
    joined = os.path.join(out, root + "-joined.mm0")
    omb, om0 = os.path.join(out, root + ".mmb"), os.path.join(out, root + ".mm0")
    fpath = os.path.join(out, root + ".false.mm0")
    for p in (joined, omb, om0, fpath):
        if os.path.exists(p):
            os.remove(p)
    timings, stages = {}, {}
    rep = {"status": "FAILED", "module": root, "proof_input_mode": "separate-link", "timings_seconds": timings,
           "stages": stages}

    def note(stage):
        if progress:
            try:
                with open(progress + ".tmp", "w", encoding="utf-8", newline="\n") as f:
                    f.write("stage=%s\n" % stage)
                os.replace(progress + ".tmp", progress)
            except OSError:
                pass

    def stage(label, cmd, data=None, reject=False):
        """One command, stdout+stderr to OUTDIR/<label>.log; returns (rc, last 8 KB of the log)."""
        note(label)
        logp = os.path.join(out, label + ".log")
        with open(logp, "wb") as lf:
            fin = open(data, "rb") if data else subprocess.DEVNULL
            try:
                r, wall, peak = run(cmd, stdin=fin, stdout=lf, stderr=subprocess.STDOUT, cwd=pa)
            finally:
                if data:
                    fin.close()
        timings[label] = round(wall, 2)
        stages[label] = {"seconds": round(wall, 2), "peak_bytes": peak, "rc": r.returncode}
        with open(logp, "rb") as lf:
            lf.seek(max(0, os.path.getsize(logp) - 8000))
            tail = lf.read().decode("utf-8", "replace")
        return r.returncode, tail

    try:
        t = time.perf_counter()
        note("sources")
        for name, digest in EXPECTED_VENDOR.items():
            if L.sha256(os.path.join(vendor, name)) != digest:
                raise CheckError("The pinned PA library changed")
        graph = source_graph(root, pa, vendor)
        rp = os.path.realpath(pa)
        rep["sources"] = {os.path.relpath(p, rp).replace("\\", "/"): d for p, d in sorted(graph.items())
                          if os.path.commonpath([rp, p]) == rp}
        rep["dependency_graph_closed"] = True
        rep["project_source_files"] = len(rep["sources"])
        timings["sources"] = round(time.perf_counter() - t, 2)
        order, _imports = L.closure_order(root)
        rep["proof_module_order"] = [m + ".mm1" for m in order]
        rc, msg = stage("join", [mm0rs, "join", src, joined])
        if rc or not os.path.exists(joined):
            raise CheckError("join failed: " + msg)
        linkpy = os.path.join(HERE, "linkn.py")
        rc, msg = stage("link", [sys.executable, "-B", "-I", "-X", "utf8", linkpy, root, "--build", bdir, "--spec", joined,
                                 "--tools", tools, omb, om0] + (["--reorder"] if reorder else []))
        if rc or "linked " not in msg:
            raise CheckError("link failed: " + msg.strip()[-3000:])
        rep["link"] = json.loads(msg.split("linked ", 1)[1].strip().splitlines()[0])
        rep["spec_identical_to_joined"] = L.sha256(om0) == L.sha256(joined)
        spec = joined if rep["spec_identical_to_joined"] else om0     # check.py checks the joined spec itself
        rc, msg = stage("check-original", [mm0c, omb], data=spec)
        if rc:
            raise CheckError("mm0-c rejected the linked output: " + msg[-3000:])
        t = time.perf_counter()
        note("axioms")
        ok, msg = axiom_check(omb, spec, os.path.join(vendor, "peano.mm0"))
        timings["axioms"] = round(time.perf_counter() - t, 2)
        rep["axioms"] = msg
        if not ok:
            raise CheckError("axiom check failed: " + msg)
        with open(spec, "rb") as f:
            wrong, thm = false_spec(f.read(), src)
        with open(fpath, "wb") as f:
            f.write(wrong)
        rc, msg = stage("reject-false", [mm0c, omb], data=fpath)
        if rc == 0:
            raise CheckError("Checker accepted the deliberately false specification")
        if graph != {p: L.sha256(p) for p in graph}:
            raise CheckError("A source changed during verification")
        names = theorem_names(src)
        rep.update({
            "status": "PASSED",
            "scope": SCOPE_DEFAULT % root,
            "checked_theorems": names,
            "new_project_axioms": False,
            "spec_sha256": L.sha256(spec),
            "joined_sha256": L.sha256(joined),
            "binary_sha256": L.sha256(omb),
            "binary_bytes": os.path.getsize(omb),
            "wrong_conclusion_rejected": True,
            "wrong_conclusion_control": "Only %s is replaced by false; all other declarations are preserved" % thm,
            "false_control_rc": rc,
            "vendor": EXPECTED_VENDOR,
            "checker_sha256": L.sha256(mm0c),
            "compiler_sha256": L.sha256(mm0rs),
        })
        rep["timings_seconds"] = timings
    except (CheckError, OSError, ValueError) as e:
        rep["error"] = "%s" % e
    note("done")
    write_json(os.path.join(out, "report.json"), rep)
    return rep


def main():
    a = sys.argv[1:]

    def opt(flag, default=None):
        if flag in a:
            i = a.index(flag); v = a[i + 1]; del a[i:i + 2]; return v
        return default
    bdir = opt("--build", "build-link")
    tools = opt("--tools") or L.default_tools()
    outopt = opt("--out")
    progress = opt("--progress")
    reorder = "--reorder" in a
    a = [x for x in a if x != "--reorder"]
    if len(a) != 1:
        raise SystemExit(__doc__)
    root = a[0]
    rep = link_check(root, bdir, tools, outopt or os.path.join(bdir, "_link", root), reorder, progress)
    print(json.dumps({k: v for k, v in rep.items() if k not in ("sources", "proof_module_order", "checked_theorems")},
                     indent=1))
    return 0 if rep["status"] == "PASSED" else 1


if __name__ == "__main__":
    sys.exit(main())
