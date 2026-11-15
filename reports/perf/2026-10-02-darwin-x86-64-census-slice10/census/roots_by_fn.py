#!/usr/bin/env python3
"""For each failed root of a census, the function its proof failure names and that
function's last body trace. Prints TSV: fn, roots, trace. Usage: roots_by_fn.py <census-dir>"""
import collections
import json
import re
import sys

run = sys.argv[1]
last = {}
for line in open(f"{run}/stderr.log", errors="replace"):
    m = re.match(r"\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)", line.rstrip())
    if m:
        last[m.group(1)] = m.group(2)
roots = collections.Counter()
for line in open(f"{run}/failed_roots.jsonl"):
    record = json.loads(line)
    msg = record.get("message", "")
    m = re.search(r"non_verified proof entry \S+ in (\S+?): ", msg)
    roots[m.group(1) if m else None] += 1
for fn, n in roots.most_common():
    print(f"{fn}\t{n}\t{last.get(fn, '(untraced)')}")
