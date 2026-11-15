#!/usr/bin/env python3
"""S/R first-hit counts of a Darwin core census: each failed root by the last
[TCG-X86-BODY-TRACE] line of the function it names. S is the stack-slot
scan's refusal; R:<Op> a row outside the body domain, by its opcode.
Copied from the slice-25 design's work/angleA/firsthit.py.

usage: firsthit.py <census dir>
"""
import re, sys, json, collections
run = sys.argv[1]
last = {}
for line in open(f"{run}/stderr.log", errors="replace"):
    m = re.match(r"\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)", line.rstrip())
    if m: last[m.group(1)] = m.group(2)
roots = collections.Counter()
for l in open(f"{run}/failed_roots.jsonl"):
    r = json.loads(l); msg = r.get("message", "")
    m = re.search(r"non_verified proof entry \S+ in (\S+?): ", msg)
    fn = m.group(1) if m else None
    t = last.get(fn, "")
    if "references a stack slot outside" in t: k = "S"
    elif "outside the body domain (BODY_OPCODES" in t or "is outside the body domain (" in t:
        d = t.split("Nop): ")[-1]
        k = "R:" + d.split(" with ")[0].split(" reads ")[0]
    else: k = "other"
    roots[k] += 1
for k, v in sorted(roots.items(), key=lambda x: -x[1]): print(v, k)
