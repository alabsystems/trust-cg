#!/usr/bin/env python3
"""Offline certification of newly bound bodies by bound-row size.

usage: size_rates.py QDIR REPLAY.tsv CF.tsv BASE_CF.tsv
"""
import collections
import re
import sys

qdir, replay, cf, base_cf = sys.argv[1:5]
index = dict(line.rstrip("\n").split("\t", 1) for line in open(f"{qdir}/index.tsv"))
rows = {}
for line in open(cf):
    parts = line.rstrip("\n").split("\t")
    m = re.match(r"OWNER (\d+)", parts[1])
    if m:
        rows[parts[0]] = int(m.group(1))
base = {l.split("\t")[0]: l.split("\t")[1] for l in open(base_cf)}
buckets = [(0, 100), (100, 200), (200, 300), (300, 400), (400, 513)]
table = collections.defaultdict(collections.Counter)
for line in open(replay):
    f, outcome = line.split("\t")[:2]
    name = index[f.removesuffix(".smt2")]
    cls = "loop" if "a loop" in base.get(name, "") else "escape join"
    r = rows[name]
    b = next(f"{lo}-{hi - 1}" for lo, hi in buckets if lo <= r < hi)
    table[(cls, b)][outcome] += 1
for (cls, b), outcomes in sorted(table.items()):
    total = sum(outcomes.values())
    print(f"{cls:12s} {b:8s} {total:3d} verified {outcomes.get('VERIFIED', 0):3d}  {dict(outcomes)}")
