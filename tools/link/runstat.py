"""Run a command; print wall seconds and the peak memory of the child.

  python3 runstat.py LABEL [--json FILE] -- CMD ARGS...

Peak memory: on Linux the peak RSS of the child and its waited descendants (wait4 ru_maxrss); on Windows the
child's own peak commit (PeakPagefileUsage of its process handle, the counter the host runner records as
PeakPagedMemorySize64). 0 when it cannot be read. Exit status is the command's. With --json FILE, appends
{"label", "wall_s", "peak_rss_bytes", "rc"} as one line.
"""
import json, os, subprocess, sys, time


def _win_peak_commit(handle):
    """PeakPagefileUsage (peak commit, bytes) of a process handle that is still open; 0 on any failure."""
    try:
        import ctypes
        from ctypes import wintypes

        class PMC(ctypes.Structure):
            _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD),
                        ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                        ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                        ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                        ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t)]
        c = PMC()
        c.cb = ctypes.sizeof(PMC)
        k = ctypes.WinDLL("kernel32", use_last_error=True)
        k.K32GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(PMC), wintypes.DWORD]
        k.K32GetProcessMemoryInfo.restype = wintypes.BOOL
        if k.K32GetProcessMemoryInfo(wintypes.HANDLE(int(handle)), ctypes.byref(c), c.cb):
            return int(c.PeakPagefileUsage)
    except Exception:
        pass
    return 0


def run(cmd, **kw):
    """subprocess.run-like; returns (Popen with returncode set, wall seconds, peak memory bytes, see above)."""
    t = time.perf_counter()
    p = subprocess.Popen(cmd, **kw)
    if hasattr(os, "wait4"):
        _, status, ru = os.wait4(p.pid, 0)
        p.returncode = os.waitstatus_to_exitcode(status)
        peak = ru.ru_maxrss * 1024
    else:                       # Windows: the process handle stays open until p is collected, so its counters survive exit
        p.wait()
        peak = _win_peak_commit(getattr(p, "_handle", 0)) if os.name == "nt" else 0
    return p, time.perf_counter() - t, peak


def main():
    a = sys.argv[1:]
    label = a.pop(0)
    out = None
    if a[0] == "--json":
        out = a[1]; a = a[2:]
    assert a[0] == "--"
    r, wall, peak = run(a[1:])
    rec = {"label": label, "wall_s": round(wall, 2), "peak_rss_bytes": peak, "rc": r.returncode}
    print("RUNSTAT", json.dumps(rec), file=sys.stderr)
    if out:
        with open(out, "a", encoding="utf-8") as f:
            f.write(json.dumps(rec) + "\n")
    return r.returncode


if __name__ == "__main__":
    sys.exit(main())
