#!/usr/bin/env python3
"""Attribute each failed root of a census to the named function's last body
trace, and write one TSV (fn, roots, trace) of every failed root's function,
sorted by roots. With a class needle, print only rows whose trace contains it.
usage: roots_by_class.py <census dir> <out.tsv>"""
import collections
import json
import re
import sys

run, out = sys.argv[1], sys.argv[2]
last = {}
for line in open(f"{run}/stderr.log", errors="replace"):
    m = re.match(r"\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)", line.rstrip())
    if m:
        last[m.group(1)] = m.group(2)
roots = collections.Counter()
for line in open(f"{run}/failed_roots.jsonl"):
    r = json.loads(line)
    m = re.search(r"non_verified proof entry \S+ in (\S+?): ", r.get("message", ""))
    roots[m.group(1) if m else "(none)"] += 1
with open(out, "w") as f:
    for fn, n in roots.most_common():
        f.write(f"{fn}\t{n}\t{last.get(fn, '(untraced)')}\n")
print(len(roots), "functions,", sum(roots.values()), "roots")
