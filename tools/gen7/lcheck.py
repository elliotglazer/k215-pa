#!/usr/bin/env python3
"""Local check (GEN7, adapted from GEN4's): python3 tools/gen7/lcheck.py gen7/gen7_trpa  (module relative to pa-mm0/).
Flattens the mm1 import closure like pa-mm0/check.py, compiles with the Linux mm0-rs, joins the original mm0 closure,
checks with mm0-c, and runs the false-final control (last theorem's conclusion replaced by F.)."""
import os, re, sys, subprocess, time, shutil
S = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(S)); WT = os.path.join(ROOT, "pa-mm0"); CO = WT
EXTRA = os.environ.get("GEN7_SRC")  # extra dir checked first (generated scratch modules)
TOOLS = os.environ.get("MM0TOOLS", "/home/user/mm0-pa-ha/tools")
EXE = ".exe" if os.name == "nt" else ""   # Windows host runner (host/gen7): mm0-rs.exe / mm0-c.exe
PEANO1 = os.path.join(ROOT, "lean-mm0/vendor/peano.mm1")
PEANO0 = os.path.join(ROOT, "lean-mm0/vendor/peano.mm0")
IMPORT = re.compile(r'^\s*import\s+"([^"]+)"\s*;', re.M)
def find(rel):
    for d in ([EXTRA] if EXTRA else []) + [WT, CO]:
        p = os.path.normpath(os.path.join(d, rel))
        if os.path.exists(p): return p
    raise SystemExit("missing " + rel)
def closure(rel, out, seen):
    if rel in seen: return
    seen.add(rel)
    ur = rel.replace(os.sep, "/")   # normpath gives "\\" on Windows
    if ur.endswith("lean-mm0/vendor/peano.mm1") or ur.endswith("lean-mm0/vendor/peano.mm0"): return
    p = find(rel); txt = open(p, encoding="utf-8").read()
    for c in IMPORT.findall(txt):
        closure(os.path.normpath(os.path.join(os.path.dirname(rel), c)), out, seen)
    out.append((rel, p, txt))
def main():
    mod = sys.argv[1]; od = os.path.join(os.environ.get("LCHECK_OUT", "/tmp/gen7-lcheck"), mod); os.makedirs(od, exist_ok=True)
    m1 = []; closure(mod + ".mm1", m1, set())
    base = os.path.basename(mod); flat = os.path.join(od, base + "-proof-input.mm1")
    # LF only (mm0-rs and mm0-c reject CR). On Windows the import is relative with "/": mm0-rs reads "\r", "\t"
    # in a string literal as escapes, and host paths (C:\K215Proof\runner\...) contain them.
    pin = PEANO1 if os.name != "nt" else os.path.relpath(PEANO1, od).replace("\\", "/")
    with open(flat, "w", encoding="utf-8", newline="\n") as f:
        f.write('import "%s";\n' % pin)
        f.write('do { (set-timeout 0) };\n')   # no elaboration timeouts (a loaded host can time out generated proofs)
        for rel, p, txt in m1: f.write("\n-- Original proof module: " + rel + "\n" + IMPORT.sub("", txt))
    m0 = []; closure(mod + ".mm0", m0, set())
    joined = os.path.join(od, base + "-joined.mm0")
    with open(joined, "w", encoding="utf-8", newline="\n") as f:
        f.write(open(PEANO0, encoding="utf-8").read())
        for rel, p, txt in m0: f.write("\n" + IMPORT.sub("", txt))
    mmb = os.path.join(od, base + ".mmb")
    t = time.time()
    try:
        import resource                     # not on Windows: peak RSS is then reported as 0
    except ImportError:
        resource = None
    r = subprocess.run([TOOLS + "/mm0-rs" + EXE, "compile", "--cache=false", flat, mmb], capture_output=True)
    pk = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss if resource else 0
    log = (r.stdout + r.stderr).decode("utf-8", "replace")
    open(os.path.join(od, "compile.log"), "w").write(log)
    print("compile rc", r.returncode, "%.1fs" % (time.time() - t), "peakMB", pk // 1024,
          "sorry" if "contains sorry" in log else "")
    if r.returncode or "contains sorry" in log:
        errs = [l for l in log.splitlines() if "error" in l.lower() or "sorry" in l][:30]
        print("\n".join(errs)); print("log:", os.path.join(od, "compile.log")); sys.exit(1)
    spec = open(joined, "rb").read()
    r = subprocess.run([TOOLS + "/mm0-c" + EXE, mmb], input=spec, capture_output=True)
    print("check rc", r.returncode, (r.stdout + r.stderr).decode()[-2000:])
    if r.returncode: sys.exit(1)
    src0 = open(find(mod + ".mm0"), encoding="utf-8").read()
    names = re.findall(r"(?m)^theorem\s+(\w+)", src0)
    marker = b"theorem " + names[-1].encode()
    pre, tail = spec.rsplit(marker, 1); binders, body = tail.split(b"$", 1); _, suf = body.split(b"$;", 1)
    wrong = pre + marker + binders + b"$ F. $;" + suf
    r = subprocess.run([TOOLS + "/mm0-c" + EXE, mmb], input=wrong, capture_output=True)
    print("false-final rejected" if r.returncode else "ERROR: false-final ACCEPTED")
    print("LOCAL PASS", mod, len(names), "theorems")
main()
