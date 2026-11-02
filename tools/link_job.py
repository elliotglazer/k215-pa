"""Host driver of the runner's "link-check" action: separate compilation + link + the trusted checks of check.py.

The runner (host/runner.ps1) calls it after it has extracted host/link from the fetched host-release commit and
checked host/link/src against host/link/MANIFEST.sha256:

    python -B -I -X utf8 link_job.py --job <work>\\job.json --snap <runner\\link\\host\\link\\src>
        --tools <capacity2 tools dir> --repo <repo checkout> --cache <C:\\K215Proof\\linkcache>
        --work <C:\\K215Proof\\link\\<module>> --results <results\\<id>> [--keep <C:\\K215Proof\\routeb\\mmb>]

Job fields (anything else is rejected):
  "action": "link-check"
  "module": "<name>"          root module (pa-mm0/<name>.mm1 and .mm0 in the repo checkout, host-staged files included)
  "jobs": N                   parallel compiles, 1..64
  "timeout_minutes": N        read by the runner only
  "mem_budget_gb": G          optional, 8..4000: memory budget of the parallel compiles (default: the free commit at
                              start minus 64 GB, see build_all.py --mem-gb)
  "cache_max_gb": C           optional, 1..4000, default 300: build_all.py --cache-max-gb (LRU bound of the cache)
  "keep_mmb": true|false      optional, default false: keep the PASSED linked .mmb (step 3); the runner passes
                              --keep <C:\\K215Proof\\routeb\\mmb> only for true

Steps, all with the snapshot's tools/link (pinned) and the given mm0-rs / mm0-c:
  1. build:      tools/link/build_all.py <module> --build <cache> -j N --mem-gb G --cache-max-gb C
                 (every module of the .mm1 closure compiled against stub interfaces; untrusted; cached by content hash)
  2. link-check: tools/link/link_check.py <module> --build <cache> --out <work>/out: check.py's source rules and pinned
                 vendor hashes, mm0-rs join <module>.mm0 (check.py's spec), linkn.py, mm0-c on the linked .mmb against
                 the joined spec, axiom check (only peano.mm0's axioms), false control (must be rejected), sources
                 unchanged
  3. keep (only "keep_mmb": true and --keep <dir>, only after PASSED): <work>/out/<module>.mmb is moved (renamed on the
                 same volume, else copied after a free-space check, hash-verified, and the source removed) to
                 <dir>/<module>.mmb, replacing an older one, and <dir>/<module>-report.json gets this report plus
                 "kept_from": "link-check" (the input pair of the runner's "translate" / "gen7": status PASSED and
                 binary_sha256 of the file). The old report is removed first and the new one written last, so an
                 interrupted keep leaves no pair. report.json then has "kept_mmb": {"status": "kept" | "skipped" |
                 "error", ...}; a failed keep does not change the link-check status.
<results> gets report.json (status PASSED / FAILED in check.py's format, spec_sha256, stage timings, a compile summary,
link stats, snapshot / driver / tool hashes), build.json (per-module stats), the stage logs (join, link, check-original,
reject-false) and the compile logs of up to 20 failing modules. Large outputs (linked .mmb unless kept, joined spec) stay in <work>.
<work>/progress.txt holds one status line that the runner appends to results/<id>/progress.log.
Exit status 0 iff the report is PASSED.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

MAX_COPY = 25 * 1024 * 1024
MODULE = re.compile(r"^[a-z0-9_]{1,120}$")
FIELDS = {"action", "module", "jobs", "timeout_minutes", "mem_budget_gb", "cache_max_gb", "keep_mmb"}
EXE = ".exe" if os.name == "nt" else ""
SNAP_FILES = ("build_all.py", "compile_one.py", "link_check.py", "linkn.py", "mkiface.py", "mm1lib.py", "rawmmb.py",
              "runstat.py")
STAGE_LOGS = ("join.log", "link.log", "check-original.log", "reject-false.log")
DEFAULT_CACHE_MAX_GB = 300
KEEP_MARGIN = 2 * 10 ** 9                            # free bytes left on the keep volume after a cross-volume copy
SHA256 = re.compile(r"^[0-9a-f]{64}$")


class JobError(Exception):
    pass


def _int(spec, k, lo, hi, default=None):
    if k not in spec:
        return default
    v = spec[k]
    if isinstance(v, bool) or not isinstance(v, int) or not lo <= v <= hi:
        raise JobError("rejected %s: %r (allowed: integer %d..%d)" % (k, v, lo, hi))
    return v


def validate(spec):
    """The checked job fields as a dict; JobError on anything not allowed."""
    if not isinstance(spec, dict):
        raise JobError("job is not a JSON object")
    extra = sorted(set(spec) - FIELDS)
    if extra:
        raise JobError("unknown job fields: %s (allowed: %s)" % (", ".join(extra), ", ".join(sorted(FIELDS))))
    if spec.get("action") != "link-check":
        raise JobError("action is not link-check")
    m = spec.get("module")
    if not isinstance(m, str) or not MODULE.match(m):
        raise JobError("rejected module: %r" % (m,))
    if "jobs" not in spec:
        raise JobError("link-check needs \"jobs\"")
    j = {"module": m, "jobs": _int(spec, "jobs", 1, 64), "timeout_minutes": _int(spec, "timeout_minutes", 1, 4320),
         "mem_budget_gb": _int(spec, "mem_budget_gb", 8, 4000),
         "cache_max_gb": _int(spec, "cache_max_gb", 1, 4000, DEFAULT_CACHE_MAX_GB)}
    if "keep_mmb" in spec:                           # only when given, so other jobs' reports are unchanged
        if not isinstance(spec["keep_mmb"], bool):
            raise JobError("rejected keep_mmb: %r (allowed: true, false)" % (spec["keep_mmb"],))
        j["keep_mmb"] = spec["keep_mmb"]
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


def free_commit_bytes():
    """Free commit (Windows: ullAvailPageFile of GlobalMemoryStatusEx), else MemAvailable; None if unknown."""
    try:
        if os.name == "nt":
            import ctypes

            class MS(ctypes.Structure):
                _fields_ = [("dwLength", ctypes.c_ulong), ("dwMemoryLoad", ctypes.c_ulong),
                            ("ullTotalPhys", ctypes.c_ulonglong), ("ullAvailPhys", ctypes.c_ulonglong),
                            ("ullTotalPageFile", ctypes.c_ulonglong), ("ullAvailPageFile", ctypes.c_ulonglong),
                            ("ullTotalVirtual", ctypes.c_ulonglong), ("ullAvailVirtual", ctypes.c_ulonglong),
                            ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]
            s = MS()
            s.dwLength = ctypes.sizeof(MS)
            if ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(s)):
                return int(s.ullAvailPageFile)
            return None
        with open("/proc/meminfo", encoding="ascii") as f:
            for line in f:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) * 1024
    except Exception:
        pass
    return None


def mem_budget_gb(j, free):
    """The job's mem_budget_gb, else free commit minus 64 GB (at least 8 GB), else None (no budget)."""
    if j["mem_budget_gb"]:
        return j["mem_budget_gb"]
    if free is None:
        return None
    return max(8, int(free / 1e9) - 64)


def child_env(snap, repo, tools):
    """Environment of the pinned tools: module and vendor dirs of the repo checkout, tools dir, UTF-8, no .pyc."""
    env = {k: v for k, v in os.environ.items()
           if k not in ("LINK_PA", "LINK_VENDOR", "MM0TOOLS", "LINKN_TEST_NO_VERIFY", "PYTHONHOME", "PYTHONSTARTUP")}
    env.update(LINK_PA=os.path.join(repo, "pa-mm0"), LINK_VENDOR=os.path.join(repo, "lean-mm0", "vendor"),
               MM0TOOLS=tools, PYTHONUTF8="1", PYTHONDONTWRITEBYTECODE="1", PYTHONIOENCODING="utf-8")
    return env


def _run(argv, cwd, env, log):
    with open(log, "ab") as lf:
        lf.write(("$ " + " ".join(argv) + "\n").encode("utf-8"))
        lf.flush()
        p = subprocess.run(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=lf, stderr=subprocess.STDOUT)
        lf.write(("\n[rc %d]\n" % p.returncode).encode("utf-8"))
    return p.returncode


def write_progress(path, text):
    try:
        with open(path + ".tmp", "w", encoding="utf-8", newline="\n") as f:
            f.write(text + "\n")
        os.replace(path + ".tmp", path)
    except OSError:
        pass


def write_json(path, obj):
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(obj, f, indent=2)
        f.write("\n")


def run_job(a, j, runner=_run):
    """Steps 1 and 2; returns the report dict (also written to <results>/report.json)."""
    py = sys.executable
    tl = os.path.join(a.snap, "tools", "link")
    missing = [f for f in SNAP_FILES if not os.path.isfile(os.path.join(tl, f))]
    if missing:
        raise JobError("snapshot lacks tools/link/%s" % ", ".join(missing))
    module = j["module"]
    pa = os.path.join(a.repo, "pa-mm0")
    for ext in (".mm1", ".mm0"):
        if not os.path.isfile(os.path.join(pa, module + ext)):
            raise JobError("no such module: pa-mm0/%s%s" % (module, ext))
    for n in ("mm0-rs", "mm0-c"):
        if not os.path.isfile(os.path.join(a.tools, n + EXE)):
            raise JobError("no %s%s in %s" % (n, EXE, a.tools))
    env = child_env(a.snap, a.repo, a.tools)
    prog = os.path.join(a.work, "progress.txt")
    out = os.path.join(a.work, "out")
    shutil.rmtree(out, ignore_errors=True)          # never pass on an old linked output or report
    os.makedirs(a.cache, exist_ok=True)
    free = free_commit_bytes()
    budget = mem_budget_gb(j, free)
    stage_s = {}
    rep = {"status": "FAILED", "module": module}
    t = time.time()
    write_progress(prog, "stage=build starting")
    argv = [py, "-B", "-I", "-X", "utf8", os.path.join(tl, "build_all.py"), module, "--build", a.cache,
            "-j", str(j["jobs"]), "--tools", a.tools, "--progress", prog, "--cache-max-gb", str(j["cache_max_gb"])]
    if budget:
        argv += ["--mem-gb", str(budget)]
    blog = os.path.join(a.results, "build.log")
    rc_build = runner(argv, a.snap, env, blog)
    stage_s["build"] = round(time.time() - t, 1)
    bj = os.path.join(a.cache, "_build-%s.json" % module)
    summary = None
    try:
        with open(bj, encoding="utf-8") as f:
            summary = json.load(f)
        if os.path.getmtime(bj) < t:
            summary = None                           # an old summary: this run did not get that far
    except (OSError, ValueError):
        pass
    if summary:
        shutil.copyfile(bj, os.path.join(a.results, "build.json"))
        for m in summary.get("failed", [])[:20]:     # the failing modules' compile logs (the runner trims and greps them)
            lg = os.path.join(a.cache, m, "compile.log")
            if os.path.isfile(lg):
                shutil.copyfile(lg, os.path.join(a.results, "compile-%s.log" % m[:80]))
    if rc_build == 0 and summary and not summary.get("failed"):
        t = time.time()
        llog = os.path.join(a.results, "link-check.log")
        rc_link = runner([py, "-B", "-I", "-X", "utf8", os.path.join(tl, "link_check.py"), module, "--build", a.cache,
                          "--tools", a.tools, "--out", out, "--progress", prog], a.snap, env, llog)
        stage_s["link_check"] = round(time.time() - t, 1)
        try:
            with open(os.path.join(out, "report.json"), encoding="utf-8") as f:
                rep = json.load(f)
        except (OSError, ValueError):
            rep = {"status": "FAILED", "module": module, "error": "link_check.py wrote no report (rc %d)" % rc_link}
        if rc_link != 0 and rep.get("status") == "PASSED":
            rep["status"] = "FAILED"
            rep["error"] = "link_check.py rc %d" % rc_link
        for n in STAGE_LOGS:
            if os.path.isfile(os.path.join(out, n)):
                shutil.copyfile(os.path.join(out, n), os.path.join(a.results, n))
        joined = os.path.join(out, module + "-joined.mm0")
        if os.path.isfile(joined) and os.path.getsize(joined) <= MAX_COPY:
            shutil.copyfile(joined, os.path.join(a.results, module + "-joined.mm0"))
    else:
        if not summary:
            rep["error"] = "build_all.py rc %d and no build summary (see build.log)" % rc_build
        else:
            f = summary.get("failed", [])
            rep["error"] = "%d of %d modules failed to compile, e.g. %s" % (len(f), summary.get("modules", 0), f[:5])
    if summary:
        rep["compile"] = {k: v for k, v in summary.items() if k != "per_module"}
    rep["job"] = j
    rep["mem_budget_gb"] = budget
    rep["free_commit_bytes_at_start"] = free
    rep["stage_seconds"] = stage_s
    write_progress(prog, "stage=done status=%s" % rep["status"])
    return rep


def _remove(path):
    if os.path.lexists(path):
        os.remove(path)


def keep_mmb(rep, module, out, keep_dir, free_bytes=None):
    """Step 3: move the PASSED linked <out>/<module>.mmb to <keep_dir>/<module>.mmb and write its report next to it.
    Returns the "kept_mmb" entry of report.json; raises on I/O errors (the caller records them)."""
    if rep.get("status") != "PASSED":
        return {"status": "skipped", "reason": "link-check did not pass"}
    want, size = rep.get("binary_sha256"), rep.get("binary_bytes")
    if not isinstance(want, str) or not SHA256.match(want) or isinstance(size, bool) or not isinstance(size, int):
        return {"status": "error", "reason": "the report lacks binary_sha256 / binary_bytes"}
    src = os.path.join(out, module + ".mmb")
    if not os.path.isfile(src):
        return {"status": "error", "reason": "no linked %s.mmb in the work dir" % module}
    if os.path.getsize(src) != size:
        return {"status": "error", "reason": "linked .mmb has %d bytes, the report says %d" % (os.path.getsize(src), size)}
    os.makedirs(keep_dir, exist_ok=True)
    dst = os.path.join(keep_dir, module + ".mmb")
    dst_rep = os.path.join(keep_dir, module + "-report.json")
    part = dst + ".part"
    _remove(dst_rep)                                 # never pair a new .mmb with an old report
    _remove(part)
    try:
        os.replace(src, dst)                         # same volume: instant; replaces an older kept .mmb
        how = "rename"
    except OSError:                                  # another volume (or the rename failed): copy, verify, remove
        _remove(dst)                                 # one kept .mmb per module; frees its space for the copy
        free = shutil.disk_usage(keep_dir).free if free_bytes is None else free_bytes
        if free < size + KEEP_MARGIN:
            return {"status": "error", "reason": "%s has %d bytes free, the copy needs %d (+%d margin); the linked "
                    ".mmb stays in the work dir" % (keep_dir, free, size, KEEP_MARGIN)}
        shutil.copyfile(src, part)
        got = sha256(part)
        if got != want:
            _remove(part)
            return {"status": "error", "reason": "copied .mmb hash %s does not match the report" % got}
        os.replace(part, dst)
        os.remove(src)
        how = "copy"
    kept = dict(rep, kept_from="link-check")         # proof_input_mode stays "separate-link"
    write_json(dst_rep + ".tmp", kept)
    os.replace(dst_rep + ".tmp", dst_rep)
    return {"status": "kept", "path": dst, "report": dst_rep, "sha256": want, "bytes": size, "how": how}


def main(argv=None):
    ap = argparse.ArgumentParser()
    for k in ("job", "snap", "tools", "repo", "cache", "work", "results"):
        ap.add_argument("--" + k, required=True)
    ap.add_argument("--keep", default=None)
    a = ap.parse_args(argv)
    for k in ("snap", "tools", "repo", "cache", "work", "results"):
        setattr(a, k, os.path.abspath(getattr(a, k)))
    os.makedirs(a.results, exist_ok=True)
    os.makedirs(a.work, exist_ok=True)
    head = {"driver_sha256": sha256(os.path.abspath(__file__)), "python": sys.version.split()[0]}
    man = os.path.join(os.path.dirname(a.snap), "MANIFEST.sha256")
    try:
        with open(man, encoding="utf-8") as f:
            head["snapshot"] = dict(re.findall(r"^# (k215-pa-mm0) ([0-9a-f]{40})$", f.read(), re.M))
        head["snapshot_manifest_sha256"] = sha256(man)
    except OSError:
        head["snapshot"] = None
    head["tools"] = {n: fileinfo(os.path.join(a.tools, n + EXE)) for n in ("mm0-rs", "mm0-c")}
    rep = {"status": "FAILED"}
    j = None
    try:
        with open(a.job, encoding="utf-8") as f:
            j = validate(json.load(f))
        rep = run_job(a, j)
    except (JobError, OSError, ValueError) as e:
        rep = {"status": "FAILED", "error": str(e)}
    finally:
        rep.update(head)
        if j and j.get("keep_mmb"):
            if not a.keep:
                rep["kept_mmb"] = {"status": "skipped", "reason": "no --keep directory given"}
            else:
                try:
                    rep["kept_mmb"] = keep_mmb(rep, j["module"], os.path.join(a.work, "out"), os.path.abspath(a.keep))
                except Exception as e:               # never lose the report over a failed keep
                    rep["kept_mmb"] = {"status": "error", "reason": "%s: %s" % (type(e).__name__, e)}
        write_json(os.path.join(a.results, "report.json"), rep)
    print(json.dumps({k: rep.get(k) for k in ("status", "error", "spec_sha256") + (("kept_mmb",) if "kept_mmb" in rep else ())}))
    return 0 if rep.get("status") == "PASSED" else 1


if __name__ == "__main__":
    sys.exit(main())
