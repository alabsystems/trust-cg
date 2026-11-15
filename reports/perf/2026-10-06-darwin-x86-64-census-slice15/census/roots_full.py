#!/usr/bin/env python3
"""Print each failed root's named function and that function's last body trace
(one TSV line per root): the input of the scope measurement.
usage: roots_full.py <census dir>"""
import re, json, sys
run = sys.argv[1]
last = {}
for line in open(f"{run}/stderr.log", errors="replace"):
    m = re.match(r"\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)", line.rstrip())
    if m:
        last[m.group(1)] = m.group(2)
for l in open(f"{run}/failed_roots.jsonl"):
    r = json.loads(l)
    msg = r.get("message", "")
    m = re.search(r"non_verified proof entry \S+ in (\S+?): ", msg)
    fn = m.group(1) if m else None
    t = last.get(fn, "(untraced)")
    print(f"{fn}\t{t}")
