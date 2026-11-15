#!/usr/bin/env python3
"""RSS / footprint over time for one command (macOS proc_pid_rusage), with the
command's stderr lines timestamped on the same clock.

Usage: rss_trace.py <out.tsv> -- cmd args...
Prints the peak and a coarse timeline; writes every sample to out.tsv.
"""
import ctypes
import struct
import subprocess
import sys
import threading
import time

libproc = ctypes.CDLL("/usr/lib/libproc.dylib")
RUSAGE_INFO_V4 = 4
buf = ctypes.create_string_buffer(1024)


def sample(pid):
    if libproc.proc_pid_rusage(pid, RUSAGE_INFO_V4, buf) != 0:
        return None
    raw = buf.raw
    resident, footprint = struct.unpack_from("<QQ", raw, 16 + 8 * 6)
    return resident, footprint


out = sys.argv[1]
cmd = sys.argv[3:]
t0 = time.monotonic()
proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
lines = []


def reader():
    for line in proc.stderr:
        lines.append((time.monotonic() - t0, line.rstrip()))


th = threading.Thread(target=reader, daemon=True)
th.start()
samples = []
import os
maxrss = None
while True:
    pid, status, ru = os.wait4(proc.pid, os.WNOHANG)
    if pid:
        proc.returncode = os.waitstatus_to_exitcode(status)
        maxrss = ru.ru_maxrss
        break
    s = sample(proc.pid)
    if s:
        samples.append((time.monotonic() - t0, *s))
    time.sleep(0.0003)
th.join(timeout=5)
with open(out, "w") as f:
    for t, r, fp in samples:
        f.write(f"{t:.4f}\t{r}\t{fp}\n")
peak = max(samples, key=lambda s: s[1])
print(f"ru_maxrss={maxrss/2**20:.1f}MB")
print(f"rc={proc.returncode} samples={len(samples)} peak_rss={peak[1]/2**20:.1f}MB at t={peak[0]:.3f}s "
      f"(footprint then {peak[2]/2**20:.1f}MB); max footprint {max(s[2] for s in samples)/2**20:.1f}MB")
# coarse timeline: every ~25 ms
last = -1
for t, r, fp in samples:
    if t - last >= 0.025:
        print(f"  t={t:6.3f}s rss={r/2**20:7.1f}MB footprint={fp/2**20:7.1f}MB")
        last = t
for t, line in lines:
    if "TCG_TIME" in line or "error" in line:
        print(f"  [{t:6.3f}s] {line[:160]}")
