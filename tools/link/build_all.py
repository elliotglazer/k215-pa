"""Compile every module of a root's closure separately (compile_one.py), in parallel.

  python3 build_all.py ROOT --build DIR [-j N] [--tools TOOLDIR] [--full] [--real-peano] [--keep-input]
                        [--mem-gb G] [--progress FILE] [--cache-max-gb C]

Modules are independent: each is compiled against interfaces generated from its dependencies' sources, not
from their compiled outputs, so any order and any parallelism is fine. The closure, interfaces and name index are
computed once (compile_one.Plan). Biggest modules start first.

  -j N             at most N compiles at a time (threads; each runs one mm0-rs process)
  --mem-gb G       memory budget: a compile starts only while the estimates of the running compiles plus its own
                   fit in G GB (the biggest waiting module that fits goes first; when nothing runs, the next module
                   starts whatever its estimate). Estimate = 1 GB + 160 B per source byte (230 for proof-slimmed
                   _slim<N>_ files), from the measured 140-170 B of peak memory per input byte. Scheduling only.
  --progress FILE  rewritten (atomically, at most every 5 s and at the end) with one line
                   "stage=build total=.. done=.. compiled=.. cached=.. failed=.. running=.. compile_cpu_s=.. elapsed_s=..
                   biggest_running=<module>"; the host runner appends it to results/<id>/progress.log
  --cache-max-gb C after the build, evict least recently used module dirs of DIR that are NOT in this closure
                   until DIR's module dirs total at most C GB (the closure's own modules are never evicted)

Prints a summary and writes DIR/_build-ROOT.json (per-module seconds / peak memory / status). Exit 0 iff every
module PASSED.
"""
import json
import os
import re
import shutil
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mm1lib as L  # noqa: E402
from compile_one import compile_one, Plan  # noqa: E402

SLIM = re.compile(r"_slim\d+_")
SPECIAL = ("_peano", "_iface", "_link")


def estimate(module, size):
    return int(1e9 + (230 if SLIM.search(module) else 160) * size)


def dir_bytes(d):
    s = 0
    for dp, _dn, fn in os.walk(d):
        for f in fn:
            try:
                s += os.path.getsize(os.path.join(dp, f))
            except OSError:
                pass
    return s


def evict(bdir, keep, max_bytes):
    """Delete least recently used module dirs (link.json mtime) not in keep until the module dirs fit max_bytes."""
    dirs = []
    for n in os.listdir(bdir):
        p = os.path.join(bdir, n)
        if n in SPECIAL or n.startswith("_") or not os.path.isdir(p):
            continue
        try:
            used = os.path.getmtime(os.path.join(p, "link.json"))
        except OSError:
            used = 0
        dirs.append((used, n, dir_bytes(p)))
    total = sum(b for _u, _n, b in dirs)
    gone = []
    for used, n, b in sorted(dirs):
        if total <= max_bytes:
            break
        if n in keep:
            continue
        shutil.rmtree(os.path.join(bdir, n), ignore_errors=True)
        total -= b
        gone.append(n)
    return {"evicted": len(gone), "module_dirs_bytes": total}


class Sched:
    """Hands out modules biggest first, within -j and the memory budget."""

    def __init__(self, todo, sizes, jobs, budget):
        self.todo = list(todo)            # biggest first
        self.sizes, self.jobs, self.budget = sizes, jobs, budget
        self.cv = threading.Condition()
        self.running = {}                 # module -> estimate
        self.res = {}
        self.t0 = time.perf_counter()

    def take(self):
        with self.cv:
            while True:
                if not self.todo:
                    return None
                if len(self.running) < self.jobs:
                    used = sum(self.running.values())
                    for k, m in enumerate(self.todo):
                        e = estimate(m, self.sizes[m])
                        if not self.running or self.budget is None or used + e <= self.budget:
                            del self.todo[k]
                            self.running[m] = e
                            return m
                self.cv.wait(5)

    def done(self, m, man):
        with self.cv:
            self.running.pop(m, None)
            self.res[m] = man
            self.cv.notify_all()

    def line(self, total):
        with self.cv:
            r = dict(self.res)
            run = sorted(self.running, key=lambda m: -self.sizes[m])
        cached = sum(1 for x in r.values() if x.get("cached"))
        failed = sum(1 for x in r.values() if x["status"] != "PASSED")
        cpu = sum(x.get("compile_seconds") or 0 for x in r.values() if not x.get("cached"))
        return ("stage=build total=%d done=%d compiled=%d cached=%d failed=%d running=%d compile_cpu_s=%d elapsed_s=%d"
                " biggest_running=%s" % (total, len(r), len(r) - cached, cached, failed, len(run), cpu,
                                         time.perf_counter() - self.t0, run[0] if run else "-"))


def write_progress(path, text):
    if not path:
        return
    tmp = path + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8", newline="\n") as f:
            f.write(text + "\n")
        os.replace(tmp, path)
    except OSError:
        pass


def main():
    a = sys.argv[1:]

    def opt(flag, default=None):
        if flag in a:
            i = a.index(flag); v = a[i + 1]; del a[i:i + 2]; return v
        return default
    bdir = opt("--build", "build-link")
    jobs = int(opt("-j", "2"))
    tools = opt("--tools")
    mem = opt("--mem-gb")
    budget = float(mem) * 1e9 if mem else None
    progress = opt("--progress")
    cmax = opt("--cache-max-gb")
    flags = ("--full", "--real-peano", "--keep-input")
    full, real_peano, keep_input = (f in a for f in flags)
    a = [x for x in a if x not in flags]
    if len(a) != 1 or jobs < 1:
        raise SystemExit(__doc__)
    root = a[0]
    os.makedirs(bdir, exist_ok=True)
    t0 = time.perf_counter()
    write_progress(progress, "stage=plan root=%s" % root)
    plan = Plan(root, bdir, real_peano)
    order = plan.order
    t_plan = time.perf_counter() - t0
    sizes = {m: os.path.getsize(os.path.join(L.PA, m + ".mm1")) for m in order}
    todo = sorted(order, key=lambda m: -sizes[m])
    sch = Sched(todo, sizes, jobs, budget)
    last = [0.0]
    lock = threading.Lock()

    def tick(force=False):
        with lock:
            if force or time.perf_counter() - last[0] >= 5:
                last[0] = time.perf_counter()
                write_progress(progress, sch.line(len(order)))

    def worker():
        while True:
            m = sch.take()
            if m is None:
                return
            try:
                man = compile_one(m, bdir, tools, full, False, real_peano, plan=plan, keep_input=keep_input)
            except Exception as e:     # one module's failure must not kill the pool
                man = {"module": m, "status": "FAILED", "errors": ["%s: %s" % (type(e).__name__, e)],
                       "compile_seconds": 0, "compile_peak_rss_bytes": 0, "mmb_bytes": None, "input_bytes": 0}
            sch.done(m, man)
            if man["status"] != "PASSED":
                print("FAILED", m, *man.get("errors", [])[:3], sep="\n  ", flush=True)
            tick()

    ts = [threading.Thread(target=worker, daemon=True) for _ in range(min(jobs, len(order)))]
    for t in ts:
        t.start()
    for t in ts:
        t.join()
    tick(True)
    res = sch.res
    wall = time.perf_counter() - t0
    fails = [m for m in order if res[m]["status"] != "PASSED"]
    built = [res[m] for m in order if not res[m].get("cached")]
    summary = {
        "root": root, "modules": len(order), "failed": fails, "wall_seconds": round(wall, 1), "jobs": jobs,
        "plan_seconds": round(t_plan, 1), "mem_budget_bytes": budget,
        "compiled": len(built), "cached": len(order) - len(built),
        "sum_compile_seconds": round(sum(m["compile_seconds"] for m in built), 1),
        "max_compile_seconds": max([m["compile_seconds"] for m in built] or [0]),
        "max_peak_rss_bytes": max([m["compile_peak_rss_bytes"] for m in built] or [0]),
        "sum_mmb_bytes": sum(res[m].get("mmb_bytes") or 0 for m in order),
        "sum_input_bytes": sum(res[m].get("input_bytes") or 0 for m in order),
        "sum_source_bytes": sum(sizes.values()), "max_source_bytes": max(sizes.values()),
        "errors": {m: res[m].get("errors", [])[:5] for m in fails},
    }
    slow = sorted(built, key=lambda m: -m["compile_seconds"])[:10]
    summary["slowest"] = [[m["module"], m["compile_seconds"], m["compile_peak_rss_bytes"]] for m in slow]
    if cmax:
        summary["cache"] = evict(bdir, set(order), float(cmax) * 1e9)
    summary["per_module"] = {m: [res[m]["compile_seconds"], res[m]["compile_peak_rss_bytes"], res[m].get("mmb_bytes"),
                                 res[m].get("input_bytes"), bool(res[m].get("cached")), res[m]["status"]] for m in order}
    with open(os.path.join(bdir, "_build-%s.json" % root), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps({k: v for k, v in summary.items() if k != "per_module"}, indent=1))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
