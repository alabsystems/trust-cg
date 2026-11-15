#!/usr/bin/env python3
"""Compare two whole-core probe runs (run_probe_all.sh outputs) function by function: the functions
whose theorem query bytes differ (index.tsv name -> query files), the functions whose cf.tsv row
differs, and the functions present in one run only. Writes <out>/changed.tsv (name, base parts,
new parts, base bytes, new bytes, base cf row, new cf row) and prints a summary.
usage: cmp_probe.py <base dir> <new dir> <out prefix>"""
import os, sys
def idx(d):
    out = {}
    for l in open(f"{d}/smt2/index.tsv"):
        r = l.rstrip("\n").split("\t")
        out[r[1]] = (r[0], int(r[2]) if len(r) == 3 else 0)
    return out
def files(d, h, n):
    return [f"{d}/smt2/{h}.part{k}.smt2" for k in range(1, n + 1)] if n else [f"{d}/smt2/{h}.smt2"]
def cf(d):
    return {l.split("\t", 1)[0]: l.rstrip("\n") for l in open(f"{d}/cf.tsv")}
base, new, out = sys.argv[1:4]
b, n = idx(base), idx(new)
cb, cn = cf(base), cf(new)
changed = []
for fn in sorted(set(b) | set(n)):
    if fn not in b or fn not in n:
        changed.append((fn, "only-in-" + ("new" if fn in n else "base"), b.get(fn), n.get(fn)))
        continue
    tb = [open(p).read() for p in files(base, *b[fn])]
    tn = [open(p).read() for p in files(new, *n[fn])]
    if tb != tn:
        changed.append((fn, "bytes", (b[fn][1], sum(map(len, tb))), (n[fn][1], sum(map(len, tn)))))
cf_changed = sorted(k for k in set(cb) | set(cn) if cb.get(k) != cn.get(k))
with open(out + ".changed.tsv", "w") as f:
    for fn, kind, x, y in changed:
        f.write(f"{fn}\t{kind}\t{x}\t{y}\t{cb.get(fn, '-')}\t{cn.get(fn, '-')}\n")
with open(out + ".cf_changed.tsv", "w") as f:
    for k in cf_changed:
        f.write(f"{k}\n  base {cb.get(k, '-')}\n  new  {cn.get(k, '-')}\n")
print(f"functions: base {len(b)} indexed / {len(cb)} rows, new {len(n)} indexed / {len(cn)} rows")
print(f"theorem bytes differ: {sum(1 for c in changed if c[1] == 'bytes')}; only in one run: "
      f"{sum(1 for c in changed if c[1] != 'bytes')}; cf.tsv rows differ: {len(cf_changed)}")
for fn, kind, x, y in changed:
    print(f"  {kind:14s} parts/bytes {x} -> {y}  {fn}")
