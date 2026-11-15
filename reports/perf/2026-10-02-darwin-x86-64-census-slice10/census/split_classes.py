#!/usr/bin/env python3
"""Split the one-pass probe dump (all_s8probe.txt) into one file per slice-10 class
(classes.py's rules over the slice-8 census roots), and print each class's function
count, roots and machine-opcode histogram."""
import collections
import re
import sys

sys.path.insert(0, "$HOME/tcg-scratch/s10")
from classes import classify, base  # noqa: E402

S10 = "$HOME/tcg-scratch/s10"
dump = sys.argv[1] if len(sys.argv) > 1 else f"{S10}/all_s8probe.txt"
roots_tsv = sys.argv[2] if len(sys.argv) > 2 else f"{S10}/s8_roots.tsv"
outdir = sys.argv[3] if len(sys.argv) > 3 else S10

text = {}
current = None
for line in open(dump, errors="replace"):
    if line.startswith("==== "):
        current = line[5:].strip()
        text.setdefault(current, [])
    if current is not None:
        text[current].append(line)

by_class = collections.defaultdict(list)
for line in open(roots_tsv):
    fn, n, trace = line.rstrip("\n").split("\t", 2)
    cls = classify(trace)
    if cls:
        by_class[cls].append((base(fn), int(n)))

for cls, fns in sorted(by_class.items()):
    ops = collections.Counter()
    found = 0
    name = re.sub(r"[^A-Za-z0-9]", "_", cls)
    with open(f"{outdir}/cls_{name}.txt", "w") as out:
        for fn, _ in fns:
            if fn in text:
                found += 1
                out.writelines(text[fn])
                for l in text[fn]:
                    m = re.match(r"^ +\d+ ([A-Za-z0-9]+) ", l)
                    if m:
                        ops[m.group(1)] += 1
    roots = sum(n for _, n in fns)
    print(f"{cls}: {len(fns)} fns ({found} in dump), {roots} roots")
    print("   ", ", ".join(f"{k}:{v}" for k, v in ops.most_common(40)))
