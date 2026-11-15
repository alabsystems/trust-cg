#!/usr/bin/env python3
"""Classify, in probe dumps (dump_class.sh), every LIR store of a private
stack address: into a private slot or through another (incoming) address,
and whether the body has a back edge or a call. Address tracking follows
StackAddr results through Copy, Bitcast, StructGep and Iadd of a constant
(as the owner does).
usage: escape_shapes.py <dump.txt>"""
import collections
import re
import sys

LINE = re.compile(r"^\s+\[(.*?)\] = (\w+)(.*?) \[(.*)\]$")
VAL = re.compile(r"Value\((\d+)\)")

functions = collections.OrderedDict()
current = None
for line in open(sys.argv[1]):
    if line.startswith("==== "):
        current = line[5:].strip()
        functions[current] = []
    elif current is not None:
        functions[current].append(line.rstrip("\n"))

summary = collections.Counter()
for fn, lines in functions.items():
    frame = set()
    stores = []
    calls = 0
    blocks = 0
    for line in lines:
        if re.match(r"^  Block\(\d+\)", line):
            blocks += 1
        m = LINE.match(line)
        if not m:
            continue
        results = [int(v) for v in VAL.findall(m.group(1))]
        opcode = m.group(2)
        args = [int(v) for v in VAL.findall(m.group(4))]
        if opcode == "StackAddr":
            frame.update(results)
        elif opcode in ("Copy", "Bitcast", "StructGep") and args and args[0] in frame:
            frame.update(results)
        elif opcode == "Iadd" and any(a in frame for a in args):
            frame.update(results)
        elif opcode == "Store" and args and args[0] in frame:
            stores.append("private" if args[1] in frame else "incoming")
        elif opcode in ("Call", "CallIndirect"):
            calls += 1
    verdict = next((l for l in lines if l.startswith("  BODY")), "")
    kinds = "+".join(sorted(set(stores)))
    summary[kinds] += 1
    print(f"{kinds:18} stores={len(stores):2} calls={calls:2} blocks={blocks:3} {fn[:110]}")
print(summary)
