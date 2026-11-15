#!/usr/bin/env python3
"""Every newly bound body an offline replay did not certify, with its class,
bound-row count and AY's reason.

usage: size_outcomes.py QDIR REPLAY.tsv CF.tsv BASE_CF.tsv
"""
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
for line in open(replay):
    f, outcome, _secs, notes = (line.rstrip("\n").split("\t") + [""])[:4]
    if outcome == "VERIFIED":
        continue
    name = index[f.removesuffix(".smt2")]
    cls = "loop" if "a loop" in base.get(name, "") else "escape join"
    reason = re.search(r"reason-unknown \(?([^)]*)", notes)
    print(f"{cls:12s} {rows[name]:4d} {outcome:10s} {reason.group(1) if reason else notes[:50]}")
