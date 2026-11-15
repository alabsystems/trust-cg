#!/usr/bin/env python3
"""OD-224 lane: the AY and Clean seconds the census route (measure_mulo.py's unit_route) spends
per function on a stage, from the replay cache (every replay measured once by its bytes).
usage: route_cost.py <stage dir>..."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import measure_mulo as M
cache = M.load_cache()
spent = []
real = M.replay
def counting(path, label, cache):
    rec = real(path, label, cache)
    spent.append((rec.get("ay_s") or 0.0, rec.get("clean_s") or 0.0))
    return rec
M.replay = counting
for stage in sys.argv[1:]:
    q = os.path.join(stage, "q")
    print(f"## {stage}")
    for line in open(os.path.join(q, "index.tsv")):
        parts = line.rstrip("\n").split("\t")
        h, name = parts[0], parts[1]
        n = int(parts[2]) if len(parts) > 2 else 0
        stems = [f"{h}.part{k}" for k in range(1, n + 1)] if n else [h]
        spent.clear()
        M.theorem_route(q, stems, "cost", cache)
        ay = sum(a for a, _ in spent); cl = sum(c for _, c in spent)
        print(f"{name.split('4core')[-1]}\treplays={len(spent)}\tay_s={ay:.2f}\tclean_s={cl:.2f}")
