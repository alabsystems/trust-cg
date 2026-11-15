#!/usr/bin/env python3
"""Load-robust companion to the beat-llvm diagnostic lane (Darwin, 2026-10-14).

The beat-llvm harness reports wall-clock medians, which move with the shared
host's load. This script re-measures the same 18 programs with counters that
do not (or barely) move with load, under `/usr/bin/time -l`:

  compile: instructions retired by the compiler process (trustc; the bridge runs
           inside it, its AY/Clean children and the linker do not count), user+sys
           CPU of the whole tree, peak RSS of the largest process, wall time;
           lanes LLVM -O2, LLVM -O3 and the bridge's no-proof-certs diagnostic lane
           at -O3, after one unmeasured warmup compile each, N interleaved rounds
           in a rotated lane order.
  runtime: cycles elapsed and instructions retired of the program process, wall
           time; LLVM -O3 against the bridge's diagnostic binary, one warmup run
           each, then M interleaved rounds in a rotated order. Every exit status
           must equal the corpus manifest's expected_exit.

The flags are run.py's (`--edition=2021 --crate-type bin -Cpanic=abort
-Copt-level=N` plus the driver's `-Ztrust-verify=off`). The no-proof-certs
lane is diagnostic, never evidence. Usage:

  loadrobust.py --repo <checkout> --driver <pkg>/bin/trustc --work <scratch>
                --out <json> [-n 5] [-m 11] [--progs ...]
"""
import argparse
import json
import math
import os
import re
import shutil
import statistics
import subprocess
import sys
import time
from pathlib import Path

TIME = ["/usr/bin/time", "-l"]
PATTERNS = {
    "instructions": re.compile(r"^\s*(\d+)\s+instructions retired\s*$", re.M),
    "cycles": re.compile(r"^\s*(\d+)\s+cycles elapsed\s*$", re.M),
    "maxrss_bytes": re.compile(r"^\s*(\d+)\s+maximum resident set size\s*$", re.M),
}
TIMES = re.compile(r"^\s*([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys\s*$", re.M)


def load1():
    return round(os.getloadavg()[0], 2)


def timed(cmd, env=None, cwd=None):
    t0 = time.perf_counter()
    r = subprocess.run([*TIME, *cmd], capture_output=True, text=True, env=env, cwd=cwd)
    rec = {"exit": r.returncode, "wall_s": round(time.perf_counter() - t0, 6)}
    for key, pattern in PATTERNS.items():
        found = pattern.findall(r.stderr)
        rec[key] = int(found[-1]) if found else None
    t = TIMES.findall(r.stderr)
    rec["cpu_s"] = round(float(t[-1][1]) + float(t[-1][2]), 4) if t else None
    if r.returncode != 0 and not cmd[0].endswith("/prog"):
        rec["stderr_tail"] = r.stderr[-600:]
    return rec


def gmean(values):
    values = [v for v in values if v]
    return math.exp(statistics.mean(math.log(v) for v in values)) if values else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--driver", required=True)
    ap.add_argument("--dylib", default=None)
    ap.add_argument("--work", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("-n", type=int, default=5, help="compile rounds")
    ap.add_argument("-m", type=int, default=11, help="runtime rounds")
    ap.add_argument("--progs", nargs="*")
    a = ap.parse_args()
    repo = Path(a.repo)
    dylib = a.dylib or str(repo / "crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.dylib")
    manifest = json.loads((repo / "benchmarks/beat-llvm/progs/manifest.json").read_text())
    entries = {p["stem"] if "stem" in p else p["name"]: p for p in manifest["programs"]} \
        if isinstance(manifest.get("programs"), list) else manifest["programs"]
    progs = a.progs or sorted(entries)
    env = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
    host = subprocess.run([a.driver, "-vV"], capture_output=True, text=True).stdout
    target = re.search(r"^host: (\S+)", host, re.M).group(1)
    lanes = {
        "llvm_o2": ["-Copt-level=2"],
        "llvm_o3": ["-Copt-level=3"],
        "bridge_diag_o3": [f"-Zcodegen-backend={dylib}", "-Ztrust-ir-cg-args=no-proof-certs", "-Copt-level=3"],
    }
    work = Path(a.work)
    work.mkdir(parents=True, exist_ok=True)
    res = {"driver": a.driver, "dylib": dylib, "target": target, "n_compile": a.n, "n_run": a.m,
           "programs": {}}
    for prog in progs:
        src = repo / "benchmarks/beat-llvm/progs" / f"{prog}.rs"
        expected = (entries.get(prog) or {}).get("expected_exit")
        d = work / prog
        d.mkdir(exist_ok=True)

        def cmd(lane):
            return [a.driver, "-Ztrust-verify=off", *lanes[lane][:-1], "--edition=2021", "--crate-type", "bin",
                    "--target", target, "-Cpanic=abort", lanes[lane][-1], "-o", str(d / lane / "prog"), str(src)]

        for lane in lanes:
            (d / lane).mkdir(exist_ok=True)
            timed(cmd(lane), env, d / lane)  # warmup (populates the bridge's warm caches)
        comp = {lane: [] for lane in lanes}
        loads = [load1()]
        names = list(lanes)
        for r in range(a.n):
            for lane in names[r % 3:] + names[:r % 3]:
                comp[lane].append(timed(cmd(lane), env, d / lane))
            loads.append(load1())
        run = {"llvm_o3": [], "bridge_diag_o3": []}
        for lane in run:
            timed([str(d / lane / "prog")])  # warmup
        rnames = list(run)
        for r in range(a.m):
            for lane in rnames[r % 2:] + rnames[:r % 2]:
                run[lane].append(timed([str(d / lane / "prog")]))
            loads.append(load1())
        row = {"load1": loads, "expected_exit": expected, "compile": {}, "run": {}}
        for lane, samples in comp.items():
            ok = all(s["exit"] == 0 for s in samples)
            row["compile"][lane] = {"samples": samples, "ok": ok, **{
                f"{k}_med": statistics.median([s[k] for s in samples]) if ok else None
                for k in ("instructions", "cpu_s", "maxrss_bytes", "wall_s")}}
        for lane, samples in run.items():
            row["run"][lane] = {"samples": samples, "exit": sorted({s["exit"] for s in samples}),
                                **{f"{k}_{f}": fn([s[k] for s in samples])
                                   for k in ("cycles", "instructions", "wall_s")
                                   for f, fn in (("min", min), ("med", statistics.median))}}
        row["exit_ok"] = all(row["run"][lane]["exit"] == [expected] for lane in run)
        res["programs"][prog] = row
        c, rr = row["compile"], row["run"]
        print(f"{prog:18} compile ins x O2 {c['bridge_diag_o3']['instructions_med'] / c['llvm_o2']['instructions_med']:.3f} "
              f"cpu x O2 {c['bridge_diag_o3']['cpu_s_med'] / c['llvm_o2']['cpu_s_med']:.3f} "
              f"rss x O2 {c['bridge_diag_o3']['maxrss_bytes_med'] / c['llvm_o2']['maxrss_bytes_med']:.3f} | "
              f"run cyc_min x O3 {rr['bridge_diag_o3']['cycles_min'] / rr['llvm_o3']['cycles_min']:.3f} "
              f"ins {rr['bridge_diag_o3']['instructions_med'] / rr['llvm_o3']['instructions_med']:.3f} "
              f"exit_ok {row['exit_ok']} load {min(loads)}-{max(loads)}", flush=True)
    P = res["programs"]
    summary = {}
    for base in ("llvm_o2", "llvm_o3"):
        for key in ("instructions_med", "cpu_s_med", "maxrss_bytes_med", "wall_s_med"):
            summary[f"compile_{key}_vs_{base}"] = gmean(
                [P[p]["compile"]["bridge_diag_o3"][key] / P[p]["compile"][base][key] for p in P])
    for key in ("cycles_min", "cycles_med", "instructions_med", "wall_s_min", "wall_s_med"):
        summary[f"runtime_{key}_vs_llvm_o3"] = gmean(
            [P[p]["run"]["bridge_diag_o3"][key] / P[p]["run"]["llvm_o3"][key] for p in P])
    summary["exit_ok_programs"] = sum(1 for p in P if P[p]["exit_ok"])
    summary["programs"] = len(P)
    res["summary"] = summary
    Path(a.out).write_text(json.dumps(res, indent=1) + "\n")
    for k, v in summary.items():
        print(f"{k}: {v:.4f}" if isinstance(v, float) else f"{k}: {v}")
    shutil.rmtree(work, ignore_errors=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
