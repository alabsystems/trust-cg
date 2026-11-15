#!/usr/bin/env python3
"""Peak resident size of every process in a command's tree (macOS libproc),
sampled every ~2 ms. Usage: tree_trace.py -- cmd args..."""
import ctypes
import struct
import subprocess
import sys
import time

libproc = ctypes.CDLL("/usr/lib/libproc.dylib")
buf = ctypes.create_string_buffer(1024)
kids = (ctypes.c_int * 1024)()
name = ctypes.create_string_buffer(256)


def resident(pid):
    if libproc.proc_pid_rusage(pid, 4, buf) != 0:
        return None
    return struct.unpack_from("<Q", buf.raw, 16 + 8 * 6)[0]


def children(pid):
    n = libproc.proc_listchildpids(pid, kids, ctypes.sizeof(kids))
    return list(kids[:max(n, 0)])


def pname(pid):
    libproc.proc_name(pid, name, 256)
    return name.value.decode(errors="replace")


cmd = sys.argv[2:] if sys.argv[1] == "--" else sys.argv[1:]
proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
peaks, names, first = {}, {}, {}
t0 = time.monotonic()
while proc.poll() is None:
    frontier, seen = [proc.pid], []
    while frontier:
        p = frontier.pop()
        seen.append(p)
        frontier.extend(children(p))
    for p in seen:
        r = resident(p)
        if r is None:
            continue
        if p not in names:
            names[p] = pname(p)
            first[p] = time.monotonic() - t0
        peaks[p] = max(peaks.get(p, 0), r)
    time.sleep(0.002)
for p, r in sorted(peaks.items(), key=lambda kv: first[kv[0]]):
    print(f"pid {p:>7} {names[p]:<24} first seen t={first[p]:.3f}s peak resident {r/2**20:8.1f} MB")
