#!/usr/bin/env python3
"""The one-shot strict replay (replay_one.py, 30 s wall cap) of every query in a directory.

usage: oneshot_dir.py AY DIR OUT.tsv
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
os.environ.setdefault("REPLAY_WALL_CAP", "30")
replay_one = {}
exec(compile(open(os.path.join(HERE, "replay_one.py")).read().replace("\nmain()\n", "\n"),
             "replay_one.py", "exec"), replay_one)
ay, d, out = sys.argv[1:4]
counts = {}
with open(out, "w") as o:
    for name in sorted(os.listdir(d)):
        if not name.endswith(".smt2"):
            continue
        kind, wall, cpu, notes = replay_one["replay"](ay, open(os.path.join(d, name)).read())
        counts[kind] = counts.get(kind, 0) + 1
        o.write(f"{name}\t{kind}\t{wall:.1f}\t{cpu:.1f}\t{notes[:200]}\n")
        o.flush()
print(counts)
