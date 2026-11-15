#!/usr/bin/env python3
"""Compare two probe `--cf` TSVs (baseline, candidate) function by function:
verdict transitions (bound/refused classes), theorem changes for functions bound
on both (defs count / rows), and any sampled refutation.

usage: cf_compare.py BASE.tsv NEW.tsv
"""
import collections
import re
import sys


def load(path):
    rows = {}
    for line in open(path):
        parts = line.rstrip("\n").split("\t")
        rows[parts[0]] = parts[1]
    return rows


def cls(verdict):
    if verdict.startswith("OWNER"):
        return "REFUTED-SAMPLE" if "REFUTED" in verdict else "OWNER"
    v = re.sub(r"Block\(\d+\)", "B", verdict)
    v = re.sub(r"Value\(\d+\)", "V", v)
    v = re.sub(r"\d+", "N", v)
    return v[:150]


base, new = load(sys.argv[1]), load(sys.argv[2])
trans = collections.Counter()
same_bound_changed = []
for name in sorted(set(base) | set(new)):
    a, b = base.get(name, "(absent)"), new.get(name, "(absent)")
    ca, cb = cls(a), cls(b)
    if ca != cb:
        trans[(ca, cb)] += 1
    elif ca == "OWNER" and a != b:
        same_bound_changed.append((name, a, b))
for (a, b), n in trans.most_common():
    print(f"{n:5d}  {a}\n       -> {b}")
print("bound on both with a changed theorem size:", len(same_bound_changed))
for name, a, b in same_bound_changed[:20]:
    print("  ", a, "|", b, "|", name[:120])
print("sampled refutations in NEW:", sum(1 for v in new.values() if "REFUTED" in v))
