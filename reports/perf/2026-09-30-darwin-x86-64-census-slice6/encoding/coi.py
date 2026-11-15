#!/usr/bin/env python3
"""Reduce a body theorem query to the definitions its goal depends on (cone of influence).

usage: coi.py IN.smt2 OUT.smt2
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


src, out = sys.argv[1], sys.argv[2]
header, defs, goal = split(open(src).read())
by_name = {d[1]: d for d in defs}
need = set()
work = list(atoms(goal, set()))
while work:
    n = work.pop()
    if n in need:
        continue
    need.add(n)
    if n in by_name:
        work.extend(atoms(by_name[n][2], set()))
kept = [d for d in defs if d[1] in need]
decls = [c for c in header if not (c[0] == "declare-const" and c[1] not in need)]
open(out, "w").write(render(decls, kept, goal))
print(f"{len(defs)} -> {len(kept)} definitions")
