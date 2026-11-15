#!/usr/bin/env python3
"""For every failing COI theorem, write encoding variants (each COI-reduced):
  <name>__ite.smt2, <name>__split_<i>.smt2, <name>__flatcase.smt2 (tag+merged items when shapes agree)
usage: variants_batch.py SRC_DIR REPLAY.tsv OUT_DIR
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sexp import *


def atoms(e, acc):
    if isinstance(e, list):
        for x in e:
            atoms(x, acc)
    else:
        acc.add(e)
    return acc


def coi(header, defs, goal):
    by_name = {d[1]: d for d in defs}
    need, work = set(), list(atoms(goal, set()))
    while work:
        n = work.pop()
        if n in need:
            continue
        need.add(n)
        if n in by_name:
            work.extend(atoms(by_name[n][2], set()))
    kept = [d for d in defs if d[1] in need]
    decls = [c for c in header if not (c[0] == "declare-const" and c[1] not in need)]
    return render(decls, kept, goal)


src, tsv, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)
failing = [l.split("\t")[0] for l in open(tsv) if l.split("\t")[1] != "VERIFIED"]
n = 0
for name in failing:
    header, defs, goal = split(open(os.path.join(src, name)).read())
    try:
        ps = paths(goal)
    except AssertionError:
        continue
    stem = name[:-5]
    acc = ps[-1][1]
    for c, x in reversed(ps[:-1]):
        acc = ["ite", c, x, acc]
    open(os.path.join(out, f"{stem}__ite.smt2"), "w").write(coi(header, defs, acc))
    for i, (c, x) in enumerate(ps):
        open(os.path.join(out, f"{stem}__split_{i}.smt2"), "w").write(coi(header, defs, ["or", ["not", c], x]))
    n += 1
print(n, "theorems")
