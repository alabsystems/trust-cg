#!/usr/bin/env python3
"""Copy every query of IN listed in a replay TSV with a given outcome to OUT.
usage: copy_outcome.py <in dir> <replay.tsv> <outcome> <out dir>"""
import os
import shutil
import sys

src, tsv, outcome, out = sys.argv[1:5]
os.makedirs(out, exist_ok=True)
n = 0
for line in open(tsv):
    name, kind = line.split("\t")[:2]
    if kind == outcome:
        shutil.copy(os.path.join(src, name), os.path.join(out, name))
        n += 1
print(n)
