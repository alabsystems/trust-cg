#!/usr/bin/env python3
"""Load-robust A/B measurements for the emitted-size work on Darwin arm64.

Two modes, both under `/usr/bin/time -l` (macOS reports instructions retired,
cycles elapsed and peak RSS per process):

  run      run each lane's linked binary (from a `size_attrib.py --keep-work`
           tree) N times, lanes INTERLEAVED per round, and record wall time,
           instructions retired, cycles elapsed and the exit code; the
           1-minute load average is stamped before and after every round
  compile  compile each corpus program with each lane N times (the same
           command line as size_attrib.py / run.py) and record the compiler's
           instructions retired, cycles and peak RSS

Medians are exact (odd N). Instructions retired do not move with machine load;
wall time and cycles do, so they are reported with the load average and are
not claimed as results on a loaded host. Output: JSON plus a Markdown table.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
PROGS = REPO / "benchmarks" / "beat-llvm" / "progs"


def load1() -> float:
    out = subprocess.run(["sysctl", "-n", "vm.loadavg"], capture_output=True, text=True).stdout
    return float(out.strip("{} \n").split()[0])


def timed(cmd: list[str], cwd: str | None = None, env: dict | None = None) -> dict:
    # Wall time from the parent's monotonic clock (time(1) prints 10 ms
    # resolution, too coarse for the 3-35 ms corpus programs); it includes
    # time(1)'s own fork/exec, the same constant for every lane.
    t0 = time.perf_counter()
    r = subprocess.run(["/usr/bin/time", "-l", *cmd], capture_output=True, text=True, cwd=cwd, env=env)
    wall = time.perf_counter() - t0
    err = r.stderr
    rec = {"exit": r.returncode, "wall_s": wall}
    for key, pat in (("instructions", r"(\d+)\s+instructions retired"),
                     ("cycles", r"(\d+)\s+cycles elapsed"),
                     ("peak_rss", r"(\d+)\s+maximum resident set size")):
        m = re.search(pat, err)
        rec[key] = int(m.group(1)) if m else None
    return rec


def med(values):
    values = [v for v in values if v is not None]
    return statistics.median(values) if values else None


def mode_run(args) -> dict:
    work = Path(args.work)
    results = {}
    for stem in args.progs:
        lanes = {lane: work / stem / lane / stem for lane in args.lanes}
        samples = {lane: [] for lane in args.lanes}
        loads = []
        for _ in range(args.n + 1):  # round 0 is the warmup, discarded
            loads.append(load1())
            for lane, binary in lanes.items():
                samples[lane].append(timed([str(binary)]))
        loads.append(load1())
        results[stem] = {"load1": loads, "lanes": {}}
        for lane, recs in samples.items():
            recs = recs[1:]
            results[stem]["lanes"][lane] = {
                "samples": recs,
                "exit": sorted({r["exit"] for r in recs}),
                "wall_s": med([r["wall_s"] for r in recs]),
                "instructions": med([r["instructions"] for r in recs]),
                "cycles": med([r["cycles"] for r in recs]),
            }
        print(stem, {l: (v["wall_s"], v["instructions"]) for l, v in results[stem]["lanes"].items()},
              f"load {min(loads):.1f}-{max(loads):.1f}", flush=True)
    return results


def mode_compile(args) -> dict:
    trustc = shutil.which("trustc")
    env = {k: v for k, v in os.environ.items() if not (k.startswith("TCG_") or k.startswith("TRUST_CG_"))}
    env["MACOSX_DEPLOYMENT_TARGET"] = env.get("MACOSX_DEPLOYMENT_TARGET", "13.0")
    lanes = {}
    for spec in args.lane:
        name, _, rest = spec.partition("=")
        dylib, _, knobs = rest.partition(":")
        lanes[name] = (dylib or None, [k for k in knobs.split(",") if k])
    results = {}
    for stem in args.progs:
        src = PROGS / f"{stem}.rs"
        samples = {name: [] for name in lanes}
        loads = []
        for _ in range(args.n + 1):
            loads.append(load1())
            for name, (dylib, knobs) in lanes.items():
                with tempfile.TemporaryDirectory(prefix="abm-", dir=args.tmp) as tmp:
                    cmd = [trustc, "-Ztrust-verify=off", "--edition=2021", "--crate-type", "bin",
                           "--target", "aarch64-apple-darwin", "-Cpanic=abort", "-Copt-level=3",
                           "-o", str(Path(tmp) / stem), str(src)]
                    if dylib:
                        cmd[1:1] = [f"-Zcodegen-backend={dylib}", *[f"-Ztrust-ir-cg-args={k}" for k in knobs]]
                    samples[name].append(timed(cmd, cwd=tmp, env=env))
        loads.append(load1())
        results[stem] = {"load1": loads, "lanes": {}}
        for name, recs in samples.items():
            recs = recs[1:]
            results[stem]["lanes"][name] = {
                "samples": recs,
                "exit": sorted({r["exit"] for r in recs}),
                "wall_s": med([r["wall_s"] for r in recs]),
                "instructions": med([r["instructions"] for r in recs]),
                "cycles": med([r["cycles"] for r in recs]),
                "peak_rss": med([r["peak_rss"] for r in recs]),
            }
        print(stem, {l: v["instructions"] for l, v in results[stem]["lanes"].items()},
              f"load {min(loads):.1f}-{max(loads):.1f}", flush=True)
    return results


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=("run", "compile"))
    ap.add_argument("--work", help="run: a size_attrib.py work tree")
    ap.add_argument("--lanes", nargs="*", default=[], help="run: lane names under the work tree")
    ap.add_argument("--lane", action="append", default=[], metavar="NAME=[DYLIB[:knobs]]",
                    help="compile: a lane (empty DYLIB = the LLVM backend)")
    ap.add_argument("--progs", nargs="*", default=None)
    ap.add_argument("-n", type=int, default=5)
    ap.add_argument("--tmp", default=None, help="compile: parent of the per-compile temp dirs")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    if args.n % 2 == 0:
        ap.error("-n must be odd so the median is a sample")
    if args.progs is None:
        args.progs = sorted(json.loads((PROGS / "manifest.json").read_text())["programs"])
    results = mode_run(args) if args.mode == "run" else mode_compile(args)
    Path(args.out).write_text(json.dumps(results, indent=1, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
