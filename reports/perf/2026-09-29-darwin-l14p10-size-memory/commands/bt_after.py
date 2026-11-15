#!/usr/bin/env python3
"""After the Nth hit of regex A, print a backtrace at the first K hits of regex B.
Usage: bt_after.py <regexA> <N> <regexB> <K> -- cmd args..."""
import os
import sys

sys.path.insert(0, "/Applications/Xcode.app/Contents/SharedFrameworks/LLDB.framework/Resources/Python")
import lldb  # noqa: E402

rxa, n, rxb, k = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
assert sys.argv[5] == "--"
cmd = sys.argv[6:]
dbg = lldb.SBDebugger.Create()
dbg.SetAsync(False)
target = dbg.CreateTarget(cmd[0])
bpa = target.BreakpointCreateByRegex(rxa)
bpa.SetIgnoreCount(n - 1)
bpb = target.BreakpointCreateByRegex(rxb)
bpb.SetEnabled(False)
li = lldb.SBLaunchInfo(cmd[1:])
li.SetWorkingDirectory(os.getcwd())
li.SetEnvironmentEntries([f"{a}={b}" for a, b in os.environ.items()], False)
err = lldb.SBError()
process = target.Launch(li, err)
signals = process.GetUnixSignals()
for sig in ("SIGUSR1", "SIGUSR2", "SIGPIPE"):
    num = signals.GetSignalNumberFromName(sig)
    signals.SetShouldStop(num, False)
    signals.SetShouldNotify(num, False)
shown = 0
seen = {}
while process.GetState() == lldb.eStateStopped and shown < k:
    for thread in process:
        if thread.GetStopReason() != lldb.eStopReasonBreakpoint:
            continue
        bp_id = thread.GetStopReasonDataAtIndex(0)
        if bp_id == bpa.GetID():
            print("== A hit; enabling B")
            bpb.SetEnabled(True)
            bpa.SetEnabled(False)
        elif bp_id == bpb.GetID():
            frames = [thread.GetFrameAtIndex(i).GetFunctionName() or "?" for i in range(min(thread.GetNumFrames(), 40))]
            key = frames[0]
            seen[key] = seen.get(key, 0) + 1
            if seen[key] <= 2:
                shown += 1
                print(f"== B hit #{shown}: {key}")
                for f in frames[1:40]:
                    print("     ", f[:160])
    process.Continue()
print("counts:", seen)
process.Kill()
