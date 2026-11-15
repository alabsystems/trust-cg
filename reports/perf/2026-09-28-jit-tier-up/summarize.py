#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Summarize a measure.py matrix: medians per (workload, calls, arm).

    summarize.py results.json [--table out.md]

Columns (median over repetitions):
  first ms   wall time from session start to the first kernel result
  tier0 Mi   instructions of the tier-0 compile bracket
  run ms     wall time from session start to the last result
  proc Gi    whole-process instructions retired (/usr/bin/time -l)
  proc Gc    whole-process cycles elapsed, all threads (/usr/bin/time -l)
  up@        call index at which the top tier took over (tier arms)
"""

from __future__ import annotations

import argparse
import gzip
import json
import statistics
from pathlib import Path

ARMS = ["base", "top", "tier", "tierc"]


def load(path: str) -> dict:
    raw = Path(path).read_bytes()
    if raw[:2] == b"\x1f\x8b":
        raw = gzip.decompress(raw)
    return json.loads(raw)


def med(values):
    values = [v for v in values if v is not None]
    return statistics.median(values) if values else None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("results")
    ap.add_argument("--table")
    args = ap.parse_args()
    doc = load(args.results)
    lines = [
        f"# tier_up_bench matrix — {doc['started']} .. {doc['finished']}",
        "",
        f"binary `{Path(doc['binary']).name}`, {doc['reps']} repetitions per arm, rotating order; "
        f"load average {doc['loadavg_start'][0]:.1f} at start, {doc['loadavg_end'][0]:.1f} at end.",
        "",
        "| workload | calls | exact | arm | first ms | tier0 Mi | run ms | proc Gi | proc Gc | up@ |",
        "|---|--:|---|---|--:|--:|--:|--:|--:|--:|",
    ]
    for cell in doc["cells"]:
        name = Path(cell["workload"]).name if cell["workload"].startswith("bcp:") else cell["workload"]
        if cell["workload"].startswith("bcp:"):
            name = "bcp:" + Path(cell["workload"][4:]).stem
        for arm in ARMS:
            runs = [r for r in cell["runs"] if r["arm"] == arm]
            first = med([r["first_result_wall_ns"] for r in runs])
            tier0 = med([r["tier0_compile"]["instructions"] for r in runs])
            run = med([r["run"]["wall_ns"] for r in runs])
            pi = med([r["process"]["instructions"] for r in runs])
            pc = med([r["process"]["cycles"] for r in runs])
            ups = [r["upgraded_at_call"] for r in runs]
            up = "—" if arm in ("base", "top") else ",".join("—" if u is None else str(u) for u in ups)
            lines.append(
                f"| {name} | {cell['calls']} | {'yes' if cell['exact'] else 'NO'} | {arm} | "
                f"{first / 1e6:.1f} | {tier0 / 1e6:.1f} | {run / 1e6:.1f} | {pi / 1e9:.3f} | {pc / 1e9:.3f} | {up} |"
            )
    text = "\n".join(lines) + "\n"
    if args.table:
        Path(args.table).write_text(text)
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
