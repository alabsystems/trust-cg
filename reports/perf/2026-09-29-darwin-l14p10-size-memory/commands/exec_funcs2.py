#!/usr/bin/env python3
"""Record every function of one module that executes during a run, with
one-shot breakpoints driven through the lldb SB API (run with Xcode's python:
`xcrun python3`). Usage: exec_funcs2.py <out.tsv> <module-basename> -- cmd args...
Writes offset-from-module-header, size and name of every executed function."""
import os
import sys

sys.path.insert(0, "/Applications/Xcode.app/Contents/SharedFrameworks/LLDB.framework/Resources/Python")
import lldb  # noqa: E402

out, module = sys.argv[1], sys.argv[2]
assert sys.argv[3] == "--"
cmd = sys.argv[4:]
dbg = lldb.SBDebugger.Create()
dbg.SetAsync(False)
target = dbg.CreateTarget(cmd[0])
bp = target.BreakpointCreateByRegex(".", module)
li = lldb.SBLaunchInfo(cmd[1:])
li.SetWorkingDirectory(os.getcwd())
env = [f"{k}={v}" for k, v in os.environ.items()]
li.SetEnvironmentEntries(env, False)
err = lldb.SBError()
process = target.Launch(li, err)
if not err.Success():
    sys.exit(f"launch failed: {err}")
for sig in ("SIGUSR1", "SIGUSR2", "SIGPIPE"):
    process.GetUnixSignals().SetShouldStop(process.GetUnixSignals().GetSignalNumberFromName(sig), False)
    process.GetUnixSignals().SetShouldNotify(process.GetUnixSignals().GetSignalNumberFromName(sig), False)
hits = {}
stops = 0
base = None
while process.GetState() == lldb.eStateStopped:
    stops += 1
    for thread in process:
        if thread.GetStopReason() != lldb.eStopReasonBreakpoint:
            continue
        frame = thread.GetFrameAtIndex(0)
        if base is None:
            m = frame.GetModule()
            base = m.GetObjectFileHeaderAddress().GetLoadAddress(target)
        sym = frame.GetSymbol()
        start = sym.GetStartAddress().GetLoadAddress(target)
        end = sym.GetEndAddress().GetLoadAddress(target)
        pc = frame.GetPC()
        if pc not in hits:
            hits[pc] = (max(end - start, 0), sym.GetName())
        # Disable the location at this pc (one-shot).
        for i in range(0, thread.GetStopReasonDataCount(), 2):
            loc = bp.FindLocationByID(thread.GetStopReasonDataAtIndex(i + 1))
            if loc.IsValid():
                loc.SetEnabled(False)
        loc = bp.FindLocationByAddress(pc)
        if loc.IsValid():
            loc.SetEnabled(False)
    process.Continue()
with open(out, "w") as f:
    for pc, (size, name) in sorted(hits.items()):
        f.write(f"{pc - base}\t{size}\t{name}\n")
print(f"state={process.GetState()} exit={process.GetExitStatus()} stops={stops} functions={len(hits)} "
      f"bytes={sum(s for s, _ in hits.values())}")
