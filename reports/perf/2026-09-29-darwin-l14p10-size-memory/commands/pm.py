#!/usr/bin/env python3
"""Median-of-N peak RSS through the harness's own sampler (peak_rss.measure).
Usage: pm.py <N> <label> -- cmd args..."""
import statistics
import sys

sys.path.insert(0, "$HOME/trust-cg/.claude/worktrees/agent-workflow/benchmarks/beat-llvm")
import peak_rss  # noqa: E402

n, label = int(sys.argv[1]), sys.argv[2]
assert sys.argv[3] == "--"
cmd = sys.argv[4:]
vals = []
for _ in range(n):
    s = peak_rss.measure(cmd, timeout=600)
    vals.append(s.peak_rss_bytes if s.returncode == 0 else None)
ok = [v for v in vals if v]
med = statistics.median(ok) if ok else None
print(f"{label:40} median={med / 2**20 if med else float('nan'):8.2f} MiB  samples={[round(v / 2**20, 2) if v else None for v in vals]}")
