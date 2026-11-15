#!/usr/bin/env python3
"""List the functions a census run's body trace refuses for a loop: every traced
one (<out>/all.txt) and those a failed root names (<out>/roots.txt).

usage: loop_roots.py <census-out-dir> <out-dir>
"""
import json
import re
import sys

run, out = sys.argv[1], sys.argv[2]
last = {}
for line in open(f"{run}/stderr.log", errors="replace"):
    m = re.match(r"\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)", line.rstrip())
    if m:
        last[m.group(1)] = m.group(2)
loops = {fn for fn, t in last.items() if "a loop (block" in t}
roots = set()
for line in open(f"{run}/failed_roots.jsonl"):
    if not line.strip():
        continue
    r = json.loads(line)
    m = re.search(r"non_verified proof entry \S+ in (\S+?): ", r.get("message", ""))
    if m and m.group(1) in loops:
        roots.add(m.group(1))
open(f"{out}/all.txt", "w").write("\n".join(sorted(loops)) + "\n")
open(f"{out}/roots.txt", "w").write("\n".join(sorted(roots)) + "\n")
print(len(loops), len(roots))
