#!/usr/bin/env python3
"""Verdict transitions between two probe --sig TSVs (before, after)."""
import collections
import sys


def load(path):
    return {line.split("\t")[0]: line.split("\t")[1] for line in open(path)}


a, b = load(sys.argv[1]), load(sys.argv[2])
trans = collections.Counter()
for name in a:
    if name not in b:
        continue
    before, after = a[name], b[name]
    if before.startswith("OWNER") and not after.startswith("OWNER"):
        trans[("LOST", after[:160])] += 1
    elif not before.startswith("OWNER") and after.startswith("OWNER"):
        trans[("NEW", before[:110])] += 1
    elif not before.startswith("OWNER") and before != after:
        trans[("MOVED", before[:90] + " ==> " + after[:150])] += 1
for key, count in trans.most_common(int(sys.argv[3]) if len(sys.argv) > 3 else 60):
    print(count, key)
print("owner before", sum(v.startswith("OWNER") for v in a.values()),
      "after", sum(v.startswith("OWNER") for v in b.values()))
