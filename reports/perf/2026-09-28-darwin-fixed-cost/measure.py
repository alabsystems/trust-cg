#!/usr/bin/env python3
# Interleaved before/after measurement of a bridge compile's fixed cost.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates
# License: Apache-2.0
"""Measure warm and cold bridge compiles of the same programs with two or more
backend dylibs, interleaved, plus the driver's own LLVM lane.

Every compile runs under `/usr/bin/time -l` and records instructions retired,
wall time, peak memory footprint, maximum RSS and the 1-minute load average
read just before it. Cold means a fresh private (0700) `XDG_CACHE_HOME` per
compile, as `benchmarks/beat-llvm/run.py --cold` uses; warm reuses one private
root per backend that two unrecorded compiles populated first. Each iteration
alternates the backend order. Every `TCG_*` and `TRUST_CG_*` variable is
removed from the child environment.

Instructions retired and peak footprint are the decision metrics: wall time on
a shared host is recorded with its load, and a cold compile's wall time also
depends on the macOS XProtect scan queue that every process's new executables
share (see README.md).

Output: one JSON document with every raw sample and the per-lane medians.
Testing evidence only: it measures one host, it proves nothing.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import statistics
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path

TIME_FIELDS = (
    ("instructions", r"(\d+)\s+instructions retired"),
    ("peak_footprint_bytes", r"(\d+)\s+peak memory footprint"),
    ("max_rss_bytes", r"(\d+)\s+maximum resident set size"),
)


def load_1min() -> float | None:
    text = subprocess.run(["sysctl", "-n", "vm.loadavg"], capture_output=True, text=True).stdout
    numbers = re.findall(r"[\d.]+", text)
    return float(numbers[0]) if numbers else None


def parse_time(stderr: str) -> dict:
    sample: dict = {}
    match = re.search(r"^\s*([\d.]+) real", stderr, re.M)
    sample["wall_s"] = float(match.group(1)) if match else None
    for key, pattern in TIME_FIELDS:
        match = re.search(pattern, stderr)
        sample[key] = int(match.group(1)) if match else None
    return sample


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def private_dir(parent: Path, prefix: str) -> Path:
    path = Path(tempfile.mkdtemp(prefix=prefix, dir=parent))
    os.chmod(path, 0o700)
    return path


def compile_once(args, program: dict, backend: Path | None, cache: Path, out: Path) -> dict:
    command = ["/usr/bin/time", "-l", str(args.driver), "-Ztrust-verify=off", "--edition=2021",
               "--crate-type", program["crate_type"], "--target", args.target, "-Cpanic=abort",
               "-Copt-level=3", "-o", str(out), str(program["path"])]
    if backend is not None:
        command[3:3] = [f"-Zcodegen-backend={backend}",
                        *[f"-Ztrust-ir-cg-args={knob}" for knob in program["knobs"]]]
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("TCG_", "TRUST_CG_"))}
    env["XDG_CACHE_HOME"] = str(cache)
    load = load_1min()
    process = subprocess.run(command, capture_output=True, text=True, env=env)
    sample = parse_time(process.stderr)
    sample["load_1min_before"] = load
    sample["exit"] = process.returncode
    if process.returncode != 0:
        sample["stderr_tail"] = process.stderr[-2000:]
    return sample


def parse_program(text: str) -> dict:
    # PATH:CRATE_TYPE:KNOB,KNOB (knobs may be empty: certificates on).
    parts = text.split(":")
    if len(parts) != 3:
        raise SystemExit(f"--program {text!r}: expected PATH:CRATE_TYPE:KNOBS")
    path = Path(parts[0]).resolve()
    if not path.is_file():
        raise SystemExit(f"--program {text!r}: no such file")
    return {"name": path.stem, "path": path, "crate_type": parts[1],
            "knobs": [knob for knob in parts[2].split(",") if knob]}


def median_row(rows: list[dict]) -> dict:
    ok = [row for row in rows if row["exit"] == 0]
    if not ok:
        return {"n": 0, "failures": len(rows)}

    def med(key):
        values = [row[key] for row in ok if row[key] is not None]
        return statistics.median(values) if values else None

    return {"n": len(ok), "failures": len(rows) - len(ok),
            "instructions_M": round(med("instructions") / 1e6),
            "wall_s": round(med("wall_s"), 3),
            "peak_footprint_MB": round(med("peak_footprint_bytes") / 1e6, 1),
            "max_rss_MB": round(med("max_rss_bytes") / 1e6, 1),
            "load_1min_min": min(row["load_1min_before"] for row in ok),
            "load_1min_max": max(row["load_1min_before"] for row in ok)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--driver", type=Path, required=True, help="the Trust package's bin/trustc")
    parser.add_argument("--backend", action="append", required=True, metavar="NAME=DYLIB")
    parser.add_argument("--program", action="append", required=True, metavar="PATH:CRATE_TYPE:KNOBS")
    parser.add_argument("--n", type=int, default=5)
    parser.add_argument("--target", default="aarch64-apple-darwin")
    parser.add_argument("--work", type=Path, required=True, help="a new private scratch directory")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    backends = {}
    for item in args.backend:
        name, _, path = item.partition("=")
        backends[name] = Path(path).resolve()
    programs = [parse_program(item) for item in args.program]
    args.work.mkdir(mode=0o700, parents=True, exist_ok=False)
    outputs = args.work / "out"
    outputs.mkdir()

    report = {
        "schema": "trust-cg-darwin-fixed-cost-v1",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "host": {"machine": platform.machine(), "macos": platform.mac_ver()[0],
                 "cpus": os.cpu_count()},
        "driver": str(args.driver),
        "driver_sha256": sha256(args.driver),
        "backends": {name: {"path": str(path), "sha256": sha256(path)}
                     for name, path in backends.items()},
        "n": args.n,
        "programs": {},
    }
    for program in programs:
        samples = {f"{name}-{lane}": [] for name in backends for lane in ("warm", "cold")}
        samples["llvm"] = []
        warm_roots = {}
        for name, dylib in backends.items():
            warm_roots[name] = private_dir(args.work, f"warm-{name}-")
            for _ in range(2):
                compile_once(args, program, dylib, warm_roots[name], outputs / f"{program['name']}-prewarm")
        order = list(backends.items())
        for iteration in range(args.n):
            for name, dylib in (order if iteration % 2 == 0 else list(reversed(order))):
                samples[f"{name}-warm"].append(compile_once(
                    args, program, dylib, warm_roots[name], outputs / f"{program['name']}-{name}-warm"))
                cold_root = private_dir(args.work, f"cold-{name}-")
                try:
                    samples[f"{name}-cold"].append(compile_once(
                        args, program, dylib, cold_root, outputs / f"{program['name']}-{name}-cold"))
                finally:
                    shutil.rmtree(cold_root, ignore_errors=True)
            samples["llvm"].append(compile_once(
                args, program, None, warm_roots[next(iter(backends))], outputs / f"{program['name']}-llvm"))
        report["programs"][program["name"]] = {
            "source": str(program["path"]),
            "crate_type": program["crate_type"],
            "knobs": program["knobs"],
            "medians": {lane: median_row(rows) for lane, rows in samples.items()},
            "samples": samples,
        }
        print(program["name"], json.dumps(report["programs"][program["name"]]["medians"]), flush=True)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    args.out.write_text(json.dumps(report, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
