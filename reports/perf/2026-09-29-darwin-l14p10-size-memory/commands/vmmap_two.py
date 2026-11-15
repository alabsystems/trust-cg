#!/usr/bin/env python3
"""vmmap at two breakpoints: the Nth hit of regex A (ignore count N-1) and the
first hit of regex B after it. Usage:
vmmap_two.py <prefix> <regexA> <N> <regexB> -- cmd args..."""
import os
import subprocess
import sys
import tempfile

prefix, bpa, n, bpb = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
assert sys.argv[5] == "--"
cmd = sys.argv[6:]
script = f"""
import lldb, subprocess
def snap(frame, name):
    pid = frame.GetThread().GetProcess().GetProcessID()
    with open({prefix!r} + name, "w") as f:
        subprocess.run(["vmmap", "-wide", str(pid)], stdout=f, stderr=subprocess.STDOUT)
def hit_a(frame, bp_loc, internal_dict):
    snap(frame, ".a.txt")
    frame.GetThread().GetProcess().GetTarget().FindBreakpointByID(2).SetEnabled(True)
    return False
def hit_b(frame, bp_loc, internal_dict):
    snap(frame, ".b.txt")
    return True
"""
with tempfile.TemporaryDirectory() as tmp:
    mod = os.path.join(tmp, "twohook.py")
    with open(mod, "w") as f:
        f.write(script)
    args = ["lldb", "-b", "-o", f"command script import {mod}",
            "-o", "process handle SIGUSR1 SIGUSR2 SIGPIPE -s false -p true -n false",
            "-o", f"breakpoint set -r {bpa}",
            "-o", f"breakpoint modify -i {n - 1} 1",
            "-o", "breakpoint command add -F twohook.hit_a 1",
            "-o", f"breakpoint set -r {bpb}",
            "-o", "breakpoint disable 2",
            "-o", "breakpoint command add -F twohook.hit_b 2",
            "-o", "run", "-o", "process kill", "--", *cmd]
    r = subprocess.run(args, capture_output=True, text=True, env=os.environ)
    print("\n".join(l for l in r.stdout.splitlines() if "stop reason" in l or "Breakpoint" in l))
