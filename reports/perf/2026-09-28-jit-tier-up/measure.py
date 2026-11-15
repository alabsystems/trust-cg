#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Run tier_up_bench over a workload matrix, interleaved, under /usr/bin/time -l.

    measure.py --bin target/release/tier_up_bench --out results.json [--reps 3]

Every (workload, calls) cell runs every arm (base, top, tier, tierc) `--reps`
times in a rotating order, one fresh process per run. A cell is EXACT only if
every run of every arm printed the same checksum. Recorded per run: the
bench's own JSON (tier-0 compile bracket, first-result wall time, whole run
bracket, the call at which the top tier took over, the session's tier report)
and the whole process's instructions retired / cycles elapsed / peak RSS from
/usr/bin/time -l.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
CNF = REPO / "crates/trust-cg-sat-host/tests/fixtures/sat_corpus"
TIME_RE = {
    "instructions": re.compile(r"^\s*(\d+)\s+instructions retired\s*$", re.M),
    "cycles": re.compile(r"^\s*(\d+)\s+cycles elapsed\s*$", re.M),
    "max_rss": re.compile(r"^\s*(\d+)\s+maximum resident set size\s*$", re.M),
}
ARMS = ["base", "top", "tier", "tierc"]

# (workload, size, [calls...]): a short run (compile-dominated) and a long
# run (execution-dominated) for each.
MATRIX = [
    (f"bcp:{CNF / 'rand3sat-225-970-s1.cnf'}", 64, [500, 20000]),
    (f"bcp:{CNF / 'blocks-3-t4.cnf'}", 64, [500, 20000]),
    ("fib", 4096, [2000, 200000]),
    ("trib", 4096, [2000, 200000]),
    ("pc", 4096, [2000, 100000]),
    ("abs", 4096, [2000, 100000]),
    ("prodi64", 4096, [2000, 100000]),
    ("st", 4096, [2000, 100000]),
    ("crcx", 4096, [2000, 100000]),
    ("mm_ijk", 48, [20, 2000]),
    ("mm_ikj", 48, [20, 2000]),
]


def run_one(binary: str, workload: str, size: int, calls: int, arm: str) -> dict:
    cmd = ["/usr/bin/time", "-l", binary, "--workload", workload, "--arm", arm,
           "--calls", str(calls), "--size", str(size)]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
    if p.returncode != 0:
        raise SystemExit(f"{' '.join(cmd)}: exit {p.returncode}\n{p.stderr[-3000:]}")
    doc = json.loads(p.stdout)
    doc["process"] = {k: (int(m.group(1)) if (m := rx.search(p.stderr)) else None)
                      for k, rx in TIME_RE.items()}
    return doc


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bin", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--filter", action="append", default=[])
    args = ap.parse_args()
    binary = str(Path(args.bin).resolve())
    out = {
        "schema": "trust-cg.tier-up-bench.matrix.v1",
        "binary": binary,
        "reps": args.reps,
        "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "loadavg_start": os.getloadavg(),
        "cells": [],
    }
    for workload, size, calls_list in MATRIX:
        if args.filter and not any(f in workload for f in args.filter):
            continue
        for calls in calls_list:
            runs = []
            for rep in range(args.reps):
                order = ARMS[rep % len(ARMS):] + ARMS[: rep % len(ARMS)]
                for arm in order:
                    runs.append(run_one(binary, workload, size, calls, arm))
            checksums = {r["checksum"] for r in runs}
            cell = {"workload": workload, "size": size, "calls": calls,
                    "exact": len(checksums) == 1, "checksums": sorted(checksums), "runs": runs}
            out["cells"].append(cell)
            print(f"{Path(workload).name} calls={calls}: exact={cell['exact']}", file=sys.stderr, flush=True)
    out["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    out["loadavg_end"] = os.getloadavg()
    Path(args.out).write_text(json.dumps(out, indent=1) + "\n")
    return 0 if all(c["exact"] for c in out["cells"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
