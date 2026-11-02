"""Host driver of the runner's "gen7" action (route T, lanes/D3CHECK.md section 8, HOST NEEDED 2 and 3).

The runner (host/runner.ps1) calls it after it has extracted host/gen7 from the fetched host-release commit,
checked host/gen7/src against host/gen7/MANIFEST.sha256, and checked the kept input .mmb against its PASSED
report:

    python -B -I -X utf8 gen7_job.py --job queue/<id>.json --snap <runner\\gen7\\host\\gen7\\src>
        --tools <capacity2 tools dir> --src <routeb\\mmb\\<module>.mmb> --work <gen7\\<module>>
        --repo <repo checkout> --results <results\\<id>>

Job fields (anything else is rejected):
  "action": "gen7"
  "module": "<name>"           the kept .mmb (a coordinator "check" with "keep_mmb": true); names the work dir
  "reflect": true | false      default true. false: reuse <work>/R from an earlier PASSED reflection of the same
                               module (its out.mmb must still have the recorded sha256); then "hand" is required
  "roots": "<repo path>"       required when reflecting: roots file (one theorem name per line), read from the
                               repo checkout (main), e.g. "tools/gen7/d3/roots_adq.txt"
  "nfr": "a,b,..."             optional: refl_lib --nfr
  "cone": true | false         default true: refl_lib --cone
  "need": "nf:D1,pf:D2,..."     optional: extra per-def lemmas for hand glue, passed to refl_lib as GEN7_NEED; kinds
                               nf / pf / ev / pal (g7nfc_D / g7pfc_D / g7evr_D / g7pal_D). The reflection fails if
                               one of them is not in <work>/R/gen7/perdef.mm1 (refl_lib skips unknown names silently)
  "hand": "<module>"           optional: hand module relative to pa-mm0 (e.g. "gen7/d3_final") to link
  "statements": "T1,T2,..."    required with "hand": the theorems of the checked spec (minspec.py)
  "bodies": "ALL" | "D1,..."   minspec.py --bodies; default "ALL" (every kept def keeps its body, D3CHECK section 8)
  "timeout_minutes": N         read by the runner only

Step 1 (reflect): [GEN7_NEED=NEED] tools/gen7/refl_lib.py SRC <work>/R --roots ROOTS [--cone] [--nfr NFR]. refl_lib compiles
<work>/R/gen7/perdef.mm1 (lcheck.py, mm0-rs), writes out.mmb / out.mm0 / manifest.json, runs mm0-c on them,
axioms.py and the false control itself; its exit status is 0 only if all of them pass and no theorem failed.
Step 2 (link, with "hand"), D3CHECK section 8's route-t-link recipe: lcheck.py compiles the hand module flattened
with GEN7_SRC = a staging dir that holds <work>/R/gen7/perdef.*, the pinned host shims tools/gen7/d3/host/gen7/*
(as gen7/*: they replace the TEST ONLY stand-ins d3_s6defs / d3_s6ql) and the hand closure's modules from the repo
checkout that the snapshot does not pin (pinned gen7-library modules win; differences are listed in gen7.json).
Only lcheck's "compile rc 0" counts: its own mm0-c run on the full joined spec overflows the name trie. Then
d3/minspec.py (--bodies ALL by default), link.py without --keep-axiom (every stub must resolve),
mm0-c (capacity2) on linked.mmb < linked.mm0, axioms.py linked.mmb linked.mm0 (only peano.mm0's axioms) and the false control
(the last theorem's conclusion replaced by F. must be rejected).

Everything large stays in <work>. <results> gets gen7.json (verdicts, return codes, sha256 and sizes),
out.mm0 / manifest.json / linked.mm0 (each only if 25 MB or smaller), the roots file, and the logs.
Exit status 0 iff every requested step passed.
"""
import argparse
import hashlib
import json
import os
import posixpath
import re
import shutil
import subprocess
import sys
import time

MAX_COPY = 25 * 1024 * 1024
NAME = r"[A-Za-z_][A-Za-z0-9_.]{0,200}"
NAMES = re.compile(r"^%s(,%s){0,999}$" % (NAME, NAME))
MODULE = re.compile(r"^[a-z0-9_]{1,120}$")
HAND = re.compile(r"^[a-z0-9_]{1,120}(/[a-z0-9_]{1,120}){0,3}$")
REPO_PATH = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.-]*(/[A-Za-z0-9_][A-Za-z0-9_.-]*){0,8}$")
NEED_KINDS = {"nf": "g7nfc_", "pf": "g7pfc_", "ev": "g7evr_", "pal": "g7pal_"}   # perdef.Perdef.need kinds
NEED = re.compile(r"^(?:nf|pf|ev|pal):%s(,(?:nf|pf|ev|pal):%s){0,999}$" % (NAME, NAME))
FIELDS = {"action", "module", "reflect", "roots", "nfr", "cone", "need", "hand", "statements", "bodies",
          "timeout_minutes"}
IMPORT = re.compile(r'^\s*import\s+"([^"]+)"\s*;', re.M)
EXE = ".exe" if os.name == "nt" else ""
LOGS = ("reflect.log", "perdef-compile.log", "link.log", "hand-compile.log", "false-control.log")


class JobError(Exception):
    pass


def validate(spec):
    """The checked job fields as a dict; JobError on anything not allowed."""
    if not isinstance(spec, dict):
        raise JobError("job is not a JSON object")
    extra = sorted(set(spec) - FIELDS)
    if extra:
        raise JobError("unknown job fields: %s (allowed: %s)" % (", ".join(extra), ", ".join(sorted(FIELDS))))
    if spec.get("action") != "gen7":
        raise JobError("action is not gen7")
    j = {}
    m = spec.get("module")
    if not isinstance(m, str) or not MODULE.match(m):
        raise JobError("rejected module: %r" % (m,))
    j["module"] = m
    for k, default in (("reflect", True), ("cone", True)):
        v = spec.get(k, default)
        if not isinstance(v, bool):
            raise JobError("rejected %s: %r (allowed: true, false)" % (k, v))
        j[k] = v
    for k in ("nfr", "statements", "bodies"):
        v = spec.get(k)
        if v is None:
            j[k] = None
            continue
        if not isinstance(v, str) or not NAMES.match(v):
            raise JobError("rejected %s: %r (comma-separated names)" % (k, v))
        j[k] = v
    nd = spec.get("need")
    if nd is not None and (not isinstance(nd, str) or not NEED.match(nd)):
        raise JobError("rejected need: %r (comma-separated kind:name, kind nf, pf, ev or pal)" % (nd,))
    j["need"] = nd
    r = spec.get("roots")
    if r is not None and (not isinstance(r, str) or not REPO_PATH.match(r) or ".." in r.split("/")):
        raise JobError("rejected roots path: %r" % (r,))
    j["roots"] = r
    h = spec.get("hand")
    if h is not None and (not isinstance(h, str) or not HAND.match(h)):
        raise JobError("rejected hand module: %r" % (h,))
    j["hand"] = h
    if j["reflect"] and not r:
        raise JobError("reflect needs \"roots\"")
    if not j["reflect"] and (r or j["nfr"] or nd or "cone" in spec):
        raise JobError("\"roots\" / \"nfr\" / \"need\" / \"cone\" are reflection options; this job has \"reflect\": false")
    if h and not j["statements"]:
        raise JobError("\"hand\" needs \"statements\"")
    if h and not j["bodies"]:
        j["bodies"] = "ALL"            # D3CHECK section 8: minspec --bodies ALL (every kept def with its body)
    if not h and (j["statements"] or j["bodies"]):
        raise JobError("\"statements\" / \"bodies\" need \"hand\"")
    if not j["reflect"] and not h:
        raise JobError("nothing to do: \"reflect\": false and no \"hand\"")
    return j


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def fileinfo(path):
    if not os.path.isfile(path):
        return None
    return {"sha256": sha256(path), "bytes": os.path.getsize(path)}


def child_env(snap, tools, extra=None):
    """Environment of the pinned tools: tools dir, translator from the snapshot, UTF-8, no bytecode files."""
    env = {k: v for k, v in os.environ.items()
           if k not in ("GEN7_SRC", "GEN7_NEED", "LCHECK_OUT", "PYTHONHOME", "PYTHONSTARTUP")}
    tr = os.path.join(snap, "mm0-pa-ha")
    env.update(MM0TOOLS=tools, ROUTEB=tr, MM0PAHA=tr, PYTHONPATH=tr, PYTHONUTF8="1", PYTHONDONTWRITEBYTECODE="1",
               PYTHONIOENCODING="utf-8")
    env.update(extra or {})
    return env


class Steps:
    """Runs the commands; every command, rc and duration goes to the summary."""

    def __init__(self, work, results, summary, runner=None):
        self.work, self.results, self.summary = work, results, summary
        self.runner = runner or self._run
        summary.setdefault("commands", [])

    @staticmethod
    def _run(argv, cwd, env, log, stdin=None, stdout=None):
        with open(log, "ab") as lf:
            lf.write(("$ " + " ".join(argv) + "\n").encode("utf-8"))
            lf.flush()
            fi = open(stdin, "rb") if stdin else subprocess.DEVNULL
            try:
                if stdout:
                    with open(stdout, "wb") as fo:
                        p = subprocess.run(argv, cwd=cwd, env=env, stdin=fi, stdout=fo, stderr=lf)
                else:
                    p = subprocess.run(argv, cwd=cwd, env=env, stdin=fi, stdout=lf, stderr=subprocess.STDOUT)
            finally:
                if stdin:
                    fi.close()
            lf.write(("\n[rc %d]\n" % p.returncode).encode("utf-8"))
        return p.returncode

    def run(self, tag, argv, cwd, env, log, stdin=None, stdout=None):
        t = time.time()
        rc = self.runner(argv, cwd, env, log, stdin=stdin, stdout=stdout)
        self.summary["commands"].append({"step": tag, "argv": argv, "cwd": cwd, "rc": rc,
                                         "seconds": round(time.time() - t, 1), "log": os.path.basename(log)})
        return rc


def copy_small(src, dst_dir, name=None):
    """Copy src into results if it is at most 25 MB; returns True if copied."""
    if os.path.isfile(src) and os.path.getsize(src) <= MAX_COPY:
        shutil.copyfile(src, os.path.join(dst_dir, name or os.path.basename(src)))
        return True
    return False


def grep(log, rx):
    try:
        with open(log, encoding="utf-8", errors="replace") as f:
            return re.findall(rx, f.read(), re.M)
    except OSError:
        return []


def host_shims(snap):
    """{rel: path} of the pinned host shims tools/gen7/d3/host/gen7/* (D3CHECK section 8: copied into GEN7_SRC/gen7, so
    they replace the TEST ONLY stand-ins gen7/d3_s6defs, gen7/d3_s6ql of the repo by imports of the real modules)."""
    d = os.path.join(snap, "tools", "gen7", "d3", "host", "gen7")
    if not os.path.isdir(d):
        return {}
    return {"gen7/" + f: os.path.join(d, f) for f in sorted(os.listdir(d)) if os.path.isfile(os.path.join(d, f))}


def hand_closure(hand, snap_pa, main_pa, perdef_dir, shims=None):
    """lcheck's .mm1 and .mm0 closure of the hand module. Returns ({rel: source path} of the files to stage,
    [rels resolved in the snapshot], [rels where the repo copy differs from the pinned one]). Order of lookup:
    gen7/perdef.* from the reflection, the pinned host shims, the snapshot (pinned gen7 library), the repo checkout."""
    stage, pinned, differ, seen = {}, [], [], set()
    shims = shims or {}

    def visit(rel):
        if rel in seen:
            return
        seen.add(rel)
        if rel.endswith("lean-mm0/vendor/peano.mm1") or rel.endswith("lean-mm0/vendor/peano.mm0"):
            return
        if rel.startswith("../") or rel.startswith("/") or ":" in rel or "\\" in rel:
            raise JobError("hand closure leaves pa-mm0: " + rel)
        parts = rel.split("/")
        if rel in ("gen7/perdef.mm1", "gen7/perdef.mm0"):
            p = os.path.join(perdef_dir, parts[-1])
            stage[rel] = p
        elif rel in shims:
            p = shims[rel]
            stage[rel] = p
        else:
            ps, pm = os.path.join(snap_pa, *parts), os.path.join(main_pa, *parts)
            if os.path.isfile(ps):
                p = ps
                pinned.append(rel)
                if os.path.isfile(pm) and sha256(pm) != sha256(ps):
                    differ.append(rel)
            elif os.path.isfile(pm):
                p = pm
                stage[rel] = p
            else:
                raise JobError("hand closure: no file pa-mm0/" + rel)
        if not os.path.isfile(p):
            raise JobError("hand closure: missing " + p)
        with open(p, encoding="utf-8") as f:
            txt = f.read()
        for imp in IMPORT.findall(txt):
            visit(posixpath.normpath(posixpath.join(posixpath.dirname(rel), imp)))

    for ext in (".mm1", ".mm0"):
        visit(hand + ext)
    return stage, sorted(pinned), sorted(differ)


def false_spec(text):
    """link_check.sh's control: the last theorem's conclusion replaced by F."""
    t = text.rstrip("\n").split("\n")
    k = max(i for i, l in enumerate(t) if l.startswith("theorem "))
    j = k
    while not t[j].rstrip().endswith("$;"):
        j += 1
    st = "\n".join(t[k:j + 1])
    st2 = re.sub(r"\$[^$]*\$;\s*$", "$ F. $;", st)
    if st2 == st:
        raise JobError("false control: no conclusion replaced")
    t[k:j + 1] = [st2]
    return "\n".join(t) + "\n"


def need_missing(need, perdef):
    """The "need" lemmas (g7nfc_D, ...) that are not theorems of perdef.mm1."""
    if not need:
        return []
    try:
        with open(perdef, encoding="utf-8") as f:
            have = set(re.findall(r"^\s*(?:pub\s+)?theorem\s+([A-Za-z0-9_.]+)", f.read(), re.M))
    except OSError:
        have = set()
    want = [NEED_KINDS[k] + n for k, n in (t.split(":") for t in need.split(","))]
    return [w for w in want if w not in have]


def reflect(j, a, steps, summary):
    py, g7 = sys.executable, os.path.join(a.snap, "tools", "gen7")
    R = os.path.join(a.work, "R")
    shutil.rmtree(R, ignore_errors=True)
    os.makedirs(R)
    roots_src = os.path.join(a.repo, *j["roots"].split("/"))
    if not os.path.isfile(roots_src):
        raise JobError("no roots file %s in the repo checkout" % j["roots"])
    roots = os.path.join(a.work, "roots.txt")
    shutil.copyfile(roots_src, roots)
    shutil.copyfile(roots, os.path.join(a.results, "roots.txt"))
    argv = [py, os.path.join(g7, "refl_lib.py"), a.src, R, "--roots", roots]
    if j["cone"]:
        argv.append("--cone")
    if j["nfr"]:
        argv += ["--nfr", j["nfr"]]
    log = os.path.join(a.work, "reflect.log")
    rc = steps.run("reflect", argv, a.snap, child_env(a.snap, a.tools, {"GEN7_NEED": j["need"]} if j["need"] else None), log)
    lc = os.path.join(R, "lc", "gen7", "perdef", "compile.log")
    if os.path.isfile(lc):
        shutil.copyfile(lc, os.path.join(a.work, "perdef-compile.log"))
    rs = {"rc": rc, "roots": j["roots"], "roots_sha256": sha256(roots), "cone": j["cone"], "nfr": j["nfr"], "need": j["need"],
          "source_mmb": fileinfo(a.src), "out_mmb": fileinfo(os.path.join(R, "out.mmb")),
          "out_mm0": fileinfo(os.path.join(R, "out.mm0")), "manifest_json": fileinfo(os.path.join(R, "manifest.json")),
          "snapshot": summary.get("snapshot"),
          "log_mm0c": grep(log, r"^mm0-c rc .*$"), "log_axioms": grep(log, r"^axioms: .*$"),
          "log_false_control": grep(log, r"^false control rc .*$"), "log_pass2": grep(log, r"^pass 2: .*$")}
    rs["need_missing"] = need_missing(j["need"], os.path.join(R, "gen7", "perdef.mm1"))
    rs["passed"] = rc == 0 and bool(rs["out_mmb"]) and bool(rs["out_mm0"]) and not rs["need_missing"]
    try:
        with open(os.path.join(R, "manifest.json"), encoding="utf-8") as f:
            man = json.load(f)
        rs["failed_theorems"] = len(man.get("failed", [])) if isinstance(man, dict) else None
    except (OSError, ValueError):
        rs["failed_theorems"] = None
    with open(os.path.join(a.work, "reflect.json"), "w", encoding="utf-8", newline="\n") as f:
        json.dump(rs, f, indent=1)
    rs["out_mm0_in_results"] = copy_small(os.path.join(R, "out.mm0"), a.results)
    rs["manifest_json_in_results"] = copy_small(os.path.join(R, "manifest.json"), a.results)
    return rs


def reuse(j, a):
    """An earlier PASSED reflection of the same module, unchanged since."""
    R = os.path.join(a.work, "R")
    try:
        with open(os.path.join(a.work, "reflect.json"), encoding="utf-8") as f:
            rs = json.load(f)
    except (OSError, ValueError):
        raise JobError("\"reflect\": false but there is no earlier reflection of %s" % j["module"])
    if not rs.get("passed"):
        raise JobError("the earlier reflection of %s did not pass" % j["module"])
    out = fileinfo(os.path.join(R, "out.mmb"))
    if not out or out["sha256"] != (rs.get("out_mmb") or {}).get("sha256"):
        raise JobError("the earlier reflection's out.mmb is missing or changed")
    src = fileinfo(a.src)
    if not src or src["sha256"] != (rs.get("source_mmb") or {}).get("sha256"):
        raise JobError("the kept .mmb of %s changed since the earlier reflection (reflect again)" % j["module"])
    rs = dict(rs, reused=True)
    rs["out_mm0_in_results"] = copy_small(os.path.join(R, "out.mm0"), a.results)
    return rs


def link(j, a, steps, summary):
    py, g7 = sys.executable, os.path.join(a.snap, "tools", "gen7")
    R = os.path.join(a.work, "R")
    H = os.path.join(a.work, "H")                       # one hand module at a time; short paths (Windows)
    shutil.rmtree(H, ignore_errors=True)
    stage_dir = os.path.join(H, "stage")
    os.makedirs(stage_dir)
    shims = host_shims(a.snap)
    stage, pinned, differ = hand_closure(j["hand"], os.path.join(a.snap, "pa-mm0"), os.path.join(a.repo, "pa-mm0"),
                                         os.path.join(R, "gen7"), shims)
    for rel, p in stage.items():
        d = os.path.join(stage_dir, *rel.split("/"))
        os.makedirs(os.path.dirname(d), exist_ok=True)
        shutil.copyfile(p, d)
    ls = {"hand": j["hand"], "statements": j["statements"].split(","), "bodies": j["bodies"],
          "shims_used": sorted(r for r in stage if r in shims),
          "staged_from_repo": len([r for r in stage if not r.startswith("gen7/perdef.") and r not in shims]),
          "pinned_modules": len(pinned), "pinned_differs_from_repo": differ}
    log = os.path.join(a.work, "link.log")
    base = j["hand"].split("/")[-1]
    lc = os.path.join(H, "lc")
    hd = os.path.join(lc, *j["hand"].split("/"))
    env = child_env(a.snap, a.tools, {"GEN7_SRC": stage_dir, "LCHECK_OUT": lc})
    ls["lcheck_rc"] = steps.run("hand-compile", [py, os.path.join(g7, "lcheck.py"), j["hand"]],
                                os.path.join(a.snap, "pa-mm0"), env, log)
    if os.path.isfile(os.path.join(hd, "compile.log")):
        shutil.copyfile(os.path.join(hd, "compile.log"), os.path.join(a.work, "hand-compile.log"))
    comp = grep(log, r"^compile rc (\d+).*$")
    ls["log_compile"] = grep(log, r"^compile rc .*$")
    ls["log_check"] = grep(log, r"^check rc \d+")
    hmmb, joined = os.path.join(hd, base + ".mmb"), os.path.join(hd, base + "-joined.mm0")
    ls["hand_mmb"] = fileinfo(hmmb)
    compiled = comp == ["0"] and not any("sorry" in l for l in ls["log_compile"]) and ls["hand_mmb"] and os.path.isfile(joined)
    ls["hand_compiled"] = bool(compiled)
    ls["passed"] = False
    if not compiled:
        return ls
    spec = os.path.join(H, "spec.mm0")
    argv = [py, os.path.join(g7, "d3", "minspec.py"), joined, j["statements"], "--bodies", j["bodies"]]
    ls["minspec_rc"] = steps.run("minspec", argv, a.snap, child_env(a.snap, a.tools), log, stdout=spec)
    if ls["minspec_rc"] or not os.path.isfile(spec):
        return ls
    with open(spec, "rb") as f:                      # print() on Windows writes CRLF; mm0-c needs LF
        b = f.read()
    with open(spec, "wb") as f:
        f.write(b.replace(b"\r\n", b"\n"))
    lmmb, lmm0 = os.path.join(H, "linked.mmb"), os.path.join(H, "linked.mm0")
    ls["link_rc"] = steps.run("link", [py, os.path.join(g7, "link.py"), os.path.join(R, "out.mmb"), hmmb, spec, lmmb, lmm0],
                              a.snap, child_env(a.snap, a.tools), log)
    ls["log_link"] = grep(log, r"^(?:linked|LINK ERROR).*$")
    if ls["link_rc"] or not os.path.isfile(lmmb) or not os.path.isfile(lmm0):
        return ls
    ls["linked_mmb"], ls["linked_mm0"] = fileinfo(lmmb), fileinfo(lmm0)
    mm0c = os.path.join(a.tools, "mm0-c" + EXE)
    ls["mm0c_rc"] = steps.run("mm0-c", [mm0c, lmmb], H, child_env(a.snap, a.tools), log, stdin=lmm0)
    ls["axioms_rc"] = steps.run("axioms", [py, os.path.join(g7, "axioms.py"), lmmb, lmm0], a.snap, child_env(a.snap, a.tools), log)
    ls["log_axioms"] = grep(log, r"^axioms: .*$")
    with open(lmm0, encoding="utf-8") as f:
        bad = false_spec(f.read())
    lbad = os.path.join(H, "linked.false.mm0")
    with open(lbad, "w", encoding="utf-8", newline="\n") as f:
        f.write(bad)
    ls["false_control_rc"] = steps.run("false-control", [mm0c, lmmb], H, child_env(a.snap, a.tools),
                                       os.path.join(a.work, "false-control.log"), stdin=lbad)
    ls["linked_mm0_in_results"] = copy_small(lmm0, a.results)
    ls["passed"] = ls["mm0c_rc"] == 0 and ls["axioms_rc"] == 0 and ls["false_control_rc"] != 0
    return ls


def main(argv=None):
    ap = argparse.ArgumentParser()
    for k in ("job", "snap", "tools", "src", "work", "repo", "results"):
        ap.add_argument("--" + k, required=True)
    a = ap.parse_args(argv)
    for k in ("snap", "tools", "src", "work", "repo", "results"):
        setattr(a, k, os.path.abspath(getattr(a, k)))
    summary = {"driver_sha256": sha256(os.path.abspath(__file__)), "python": sys.version.split()[0], "passed": False}
    os.makedirs(a.results, exist_ok=True)
    out = os.path.join(a.results, "gen7.json")
    try:
        with open(a.job, encoding="utf-8") as f:
            j = validate(json.load(f))
        summary["job"] = j
        if os.path.basename(a.src) != j["module"] + ".mmb":
            raise JobError("job module %s does not match the input %s" % (j["module"], os.path.basename(a.src)))
        man = os.path.join(os.path.dirname(a.snap), "MANIFEST.sha256")
        summary["snapshot"] = dict(re.findall(r"^# (k215-pa-mm0|mm0-pa-ha) ([0-9a-f]{40})$",
                                              open(man, encoding="utf-8").read(), re.M)) if os.path.isfile(man) else None
        summary["tools"] = {n: fileinfo(os.path.join(a.tools, n + EXE)) for n in ("mm0-rs", "mm0-c")}
        os.makedirs(a.work, exist_ok=True)
        stale = list(LOGS) + (["reflect.json"] if j["reflect"] else [])   # a killed run must not leave an old "passed"
        for name in stale:
            if os.path.isfile(os.path.join(a.work, name)):
                os.remove(os.path.join(a.work, name))
        steps = Steps(a.work, a.results, summary)
        ok = True
        if j["reflect"]:
            summary["reflect"] = reflect(j, a, steps, summary)
            ok = summary["reflect"]["passed"]
        else:
            summary["reflect"] = reuse(j, a)
        if ok and j["hand"]:
            summary["link"] = link(j, a, steps, summary)
            ok = summary["link"]["passed"]
        summary["passed"] = bool(ok)
    except JobError as e:
        summary["error"] = str(e)
    finally:
        for name in LOGS:
            p = os.path.join(a.work, name)
            if os.path.isfile(p):
                shutil.copyfile(p, os.path.join(a.results, name))      # the runner trims *.log to head + tail
        with open(out, "w", encoding="utf-8", newline="\n") as f:
            json.dump(summary, f, indent=1)
    print(json.dumps({k: summary.get(k) for k in ("passed", "error")}))
    return 0 if summary["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
