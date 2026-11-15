#!/usr/bin/env python3
"""For each slice-11 class file (cls_*.txt: base name, roots, census trace), the
offline verdict of the slice-11 owner on that function (sig census TSV: name,
verdict, params, returns, sret, call results), grouped by verdict text with
numbers masked.
usage: class_verdicts.py <sig.tsv> <cls file>..."""
import collections
import re
import sys


def key(verdict):
    v = re.sub(r"\d+", "N", verdict)
    v = v.replace("unsupported source-bound x86-64 body: ", "")
    return v[:150]


sig = {}
for line in open(sys.argv[1]):
    parts = line.rstrip("\n").split("\t")
    if len(parts) >= 2:
        sig[parts[0]] = parts[1]
for path in sys.argv[2:]:
    names = [line.split("\t")[0] for line in open(path)]
    counts = collections.Counter()
    owner = 0
    for name in names:
        verdict = sig.get(name)
        if verdict is None:
            counts["(not in the dump)"] += 1
        elif verdict.startswith("OWNER"):
            owner += 1
            counts["OWNER"] += 1
        else:
            counts[key(verdict)] += 1
    print(f"== {path.split('/')[-1]}: {len(names)} functions, {owner} bound")
    for k, n in counts.most_common():
        print(f"  {n:4d} {k}")
