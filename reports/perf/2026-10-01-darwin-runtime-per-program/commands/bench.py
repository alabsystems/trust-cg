#!/usr/bin/env python3
"""Interleaved per-program runtime A/B under /usr/bin/time -l (Darwin).

For each program, every round runs each lane's binary once, in a rotated lane
order, and records wall time (parent monotonic clock), cycles elapsed and
instructions retired. Reports min and median per lane, and ratios vs the first
lane. Load average is stamped per round. Instructions retired do not move with
load; cycles move less than wall time; min is the least load-contaminated.
"""
import argparse, json, math, re, statistics, subprocess, sys, time
from pathlib import Path

def load1():
    out = subprocess.run(["sysctl", "-n", "vm.loadavg"], capture_output=True, text=True).stdout
    return float(out.strip("{} \n").split()[0])

def timed(binary):
    t0 = time.perf_counter()
    r = subprocess.run(["/usr/bin/time", "-l", binary], capture_output=True, text=True)
    wall = time.perf_counter() - t0
    rec = {"exit": r.returncode, "wall_s": wall}
    for key, pat in (("instructions", r"(\d+)\s+instructions retired"), ("cycles", r"(\d+)\s+cycles elapsed")):
        m = re.search(pat, r.stderr)
        rec[key] = int(m.group(1)) if m else None
    return rec

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", required=True)
    ap.add_argument("--lanes", nargs="+", required=True)
    ap.add_argument("--progs", nargs="*")
    ap.add_argument("-n", type=int, default=11)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    work = Path(a.work)
    progs = a.progs or sorted(p.name for p in work.iterdir() if p.is_dir())
    res = {}
    for p in progs:
        bins = {l: str(work / p / l / p) for l in a.lanes}
        samples = {l: [] for l in a.lanes}
        loads = []
        for r in range(a.n + 1):
            loads.append(load1())
            order = a.lanes[r % len(a.lanes):] + a.lanes[:r % len(a.lanes)]
            for l in order:
                s = timed(bins[l])
                if r > 0:
                    samples[l].append(s)
        loads.append(load1())
        res[p] = {"load1": loads, "lanes": {}}
        for l, ss in samples.items():
            res[p]["lanes"][l] = {
                "samples": ss,
                "exit": sorted({s["exit"] for s in ss}),
                **{f"{k}_{f}": fn([s[k] for s in ss]) for k in ("wall_s", "cycles", "instructions")
                   for f, fn in (("min", min), ("med", statistics.median))},
            }
        L = res[p]["lanes"]; b = L[a.lanes[0]]
        print(f"{p:18} " + " ".join(f"{l}: cyc_min {L[l]['cycles_min']/b['cycles_min']:.3f} cyc_med {L[l]['cycles_med']/b['cycles_med']:.3f} wall_min {L[l]['wall_s_min']/b['wall_s_min']:.3f} ins {L[l]['instructions_med']/b['instructions_med']:.3f} exit {L[l]['exit']}" for l in a.lanes[1:]) + f"  load {min(loads):.1f}-{max(loads):.1f}", flush=True)
    Path(a.out).write_text(json.dumps(res, indent=1))
    for k in ("cycles_min", "cycles_med", "wall_s_min", "wall_s_med", "instructions_med"):
        gm = {l: math.exp(statistics.mean(math.log(res[p]["lanes"][l][k] / res[p]["lanes"][a.lanes[0]][k]) for p in progs)) for l in a.lanes[1:]}
        print(f"geomean {k}: " + " ".join(f"{l} {v:.4f}" for l, v in gm.items()))

if __name__ == "__main__":
    sys.exit(main())
