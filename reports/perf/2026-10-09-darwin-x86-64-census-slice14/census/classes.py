#!/usr/bin/env python3
"""The four slice-14 refusal classes of a census: the functions the body trace
first refuses at a division (`Udiv`/`Urem`/`Sdiv`), a `GuardDivZero`, a
`Switch` with two edges to one block, or the machine-function tables, and
whether a failed root names each.

usage: classes.py <census dir> <names out.tsv>
"""
import collections, json, re, sys

census, out = sys.argv[1], sys.argv[2]
roots = [json.loads(line) for line in open(f"{census}/failed_roots.jsonl")]
texts = [root["symbol"] + " " + root["message"] for root in roots]
classes = {}
for line in open(f"{census}/stderr.log", errors="replace"):
    m = re.match(r"\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)", line.rstrip())
    if not m:
        continue
    name, rest = m.groups()
    kind = None
    if "is outside Iconst" in rest:
        op = re.search(r"instruction \d+ \((\w+)", rest).group(1)
        if op in ("Udiv", "Urem", "Sdiv", "Srem", "GuardDivZero"):
            kind = "div:" + op
    elif "two edges to one block" in rest:
        kind = "switch"
    elif "constant pool, jump tables" in rest:
        kind = "mtables"
    if kind:
        classes[name] = kind
with open(out, "w") as f:
    for name, kind in sorted(classes.items(), key=lambda item: (item[1], item[0])):
        f.write(f"{name}\t{kind}\n")
named = {name: any(name in text for text in texts) for name in classes}
print(collections.Counter(classes.values()), len(classes), "named by a root:", sum(named.values()))
