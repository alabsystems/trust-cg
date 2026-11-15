#!/usr/bin/env python3
"""Per-class outcome of the probe's `--dump` over the slice-14 functions.

usage: dump_classes.py <class_names.tsv> <dump summary.tsv>

`class_names.tsv` is `classes.py`'s list (function name, class); the
summary is the probe's (`name`, hash, verdict, machine-table causes). Each
function's verdict is grouped as `theorem` (the owner built one and no
sample refutes it), `REFUTED-AT-SAMPLE` (a sample refutes it: a wrong
lowering or a false mismatch, to read), or the refusal with its varying
parts (numbers, value and block names) normalized.
"""
import collections
import re
import sys

classes = {}
for line in open(sys.argv[1]):
    name, cls = line.rstrip("\n").split("\t")[:2]
    classes[name] = cls

by_class = collections.defaultdict(collections.Counter)
for line in open(sys.argv[2]):
    fields = line.rstrip("\n").split("\t")
    name, verdict = fields[0], fields[2]
    if name not in classes:
        continue
    if verdict.startswith("OWNER") and "REFUTED-AT-SAMPLE" in verdict:
        kind = "REFUTED-AT-SAMPLE"
    elif verdict.startswith("OWNER"):
        kind = "theorem"
    else:
        kind = re.sub(r"(?<![\w-])\d+", "N", verdict)
        kind = re.sub(r"\b(Value|Block|VReg|PReg)\([^)]*\)", r"\1(..)", kind)
        kind = kind[:220]
    by_class[classes[name]][kind] += 1

for cls in sorted(by_class):
    total = sum(by_class[cls].values())
    print(f"== {cls}: {total}")
    for kind, count in by_class[cls].most_common():
        print(f"  {count:3}  {kind}")
