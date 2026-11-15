#!/usr/bin/env python3
"""What the slice-12 owner does with each loop function of the class, offline:
bound (OWNER) or the first refusal, normalized (numbers, slots, registers and
names masked) and counted.

usage: loop_refusals.py CF_S12.tsv NAMES.txt
  CF_S12.tsv: the probe's per-function outcome over the census dump (name,
  outcome, ...); NAMES.txt: the class's function names, one per line
  (`loop_roots.py`).
"""
import collections
import re
import sys

cf, names = sys.argv[1:3]
wanted = {line.strip() for line in open(names) if line.strip()}
counts = collections.Counter()
for line in open(cf):
    parts = line.rstrip("\n").split("\t")
    if parts[0] not in wanted:
        continue
    outcome = parts[1]
    if outcome.startswith("OWNER"):
        counts["bound"] += 1
        continue
    text = re.sub(r"unsupported source-bound x86-64 body: ", "", outcome)
    text = re.sub(r"Block\(\d+\)|block \d+|v\d+|%\w+|\b\d+\b", "#", text)
    text = re.sub(r"`[^`]*`", "`…`", text)
    counts[text[:150]] += 1
for text, n in counts.most_common():
    print(f"{n:4d}  {text}")
