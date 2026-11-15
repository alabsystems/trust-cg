#!/usr/bin/env python3
"""OD-224 lane: per function, the production route's credit on main's bytes (old, the division
form) and on the lane's (new), from route_{old,new}_p4 rows, with the AY and Clean seconds the
route spent (the cache's measurements). usage: table_mulo.py"""
import json, os, hashlib, glob
M = "$HOME/tcg-scratch/mulo-run"
recs = {}
for l in open(f"{M}/replay/data/replays.jsonl"):
    r = json.loads(l); recs.setdefault(r["sha"], r)
def rows(label):
    out = {}
    for l in open(f"{M}/replay/data/roots_{label}.tsv"):
        name, closed, how = l.rstrip("\n").split("\t", 2)
        out[name] = (closed, how)
    return out
old, new = rows("old_p4"), rows("new_p4")
print("| function | main (division form) | OD-224 | bytes main -> OD-224 |")
print("| --- | --- | --- | ---: |")
cmp = {}
for l in open(f"{M}/all/cmp_old_new_p4.changed.tsv"):
    p = l.split("\t"); cmp[p[0].split("4core")[-1]] = (p[2], p[3])
for name in new:
    b = cmp.get(name, ("?", "?"))
    print(f"| `{name}` | {old[name][0]}: {old[name][1]} | {new[name][0]}: {new[name][1]} | {b[0]} -> {b[1]} |")
