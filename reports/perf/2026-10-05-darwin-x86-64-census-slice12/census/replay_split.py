#!/usr/bin/env python3
"""Split a replay TSV (replay_dir.py) of probe queries (index.tsv maps file -> name)
by the baseline verdict class of each function.

usage: replay_split.py QDIR REPLAY.tsv BASE_CF.tsv
"""
import collections
import sys

qdir, replay, base_cf = sys.argv[1:4]
index = dict(line.rstrip("\n").split("\t", 1) for line in open(f"{qdir}/index.tsv"))
base = {l.split("\t")[0]: l.split("\t")[1] for l in open(base_cf)}
counts = collections.Counter()
for line in open(replay):
    f, outcome = line.split("\t")[:2]
    name = index[f.removesuffix(".smt2")]
    v = base.get(name, "")
    cls = "loop" if "a loop" in v else ("escape join" if "escaped" in v else "other: " + v[:80])
    counts[(cls, outcome)] += 1
for (cls, outcome), n in sorted(counts.items()):
    print(f"{cls:14s} {outcome:10s} {n}")
