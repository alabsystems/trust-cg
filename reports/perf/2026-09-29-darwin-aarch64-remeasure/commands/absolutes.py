#!/usr/bin/env python3
"""Absolute medians behind the ratios of one or more beat-llvm results files.

Usage: absolutes.py <results.json> [...]

For each file: the geometric mean over MATCH programs of the LLVM -O2 compile
median, the bridge warm and cold compile medians and their difference, and the
geometric mean of the LLVM -O3 run median over the harness's resolvable rows
(LLVM median >= 50 ms and bridge rel_spread <= 0.25), so two campaigns'
absolute levels can be set side by side. It reads only the files given.
"""
import json
import math
import sys


def gmean(xs):
    xs = [x for x in xs if x]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else None


for path in sys.argv[1:]:
    d = json.load(open(path))
    rows = [p for p in d["programs"].values() if p.get("verdict") == "MATCH"]
    o2 = gmean([p["compile"]["llvm_o2"]["median_s"] for p in rows])
    warm = gmean([p["compile"]["bridge_warm"]["median_s"] for p in rows])
    cold = gmean([p["compile"]["bridge_cold"]["median_s"] for p in rows])
    crit = d["aggregates"].get("runtime_reliable_criteria") or {"min_llvm_median_s": 0.05, "max_rel_spread": 0.25}
    res = [p for p in rows
           if p["run"]["llvm_o3"]["median_s"] >= crit["min_llvm_median_s"]
           and p["run"]["bridge"]["rel_spread"] <= crit["max_rel_spread"]]
    run = gmean([p["run"]["llvm_o3"]["median_s"] for p in res])
    prov = d["provenance"]
    print(f"{path.split('/')[-1]}: load {prov['loadavg_before']}->{prov['loadavg_after']} "
          f"({prov.get('load_status')}); MATCH {len(rows)}")
    if rows:
        print(f"  compile geomean s: LLVM -O2 {o2:.3f}, bridge warm {warm:.3f}, bridge cold {cold:.3f}, "
              f"cold - warm {cold - warm:.3f}")
        print(f"  LLVM -O3 run geomean over {len(res)} resolvable rows: {run:.4f} s "
              f"({', '.join(sorted(n for n, p in d['programs'].items() if p in res))})")
