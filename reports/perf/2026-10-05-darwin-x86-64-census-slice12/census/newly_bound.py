#!/usr/bin/env python3
"""Names a candidate probe TSV binds and a baseline TSV does not.

usage: newly_bound.py BASE.tsv NEW.tsv OUT.txt
"""
import sys

base = {l.split("\t")[0]: l.split("\t")[1] for l in open(sys.argv[1])}
new = {l.split("\t")[0]: l.split("\t")[1] for l in open(sys.argv[2])}
names = [n for n in new if new[n].startswith("OWNER") and not base.get(n, "").startswith("OWNER")]
open(sys.argv[3], "w").write("\n".join(names) + "\n")
print(len(names))
