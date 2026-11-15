#!/usr/bin/env python3
"""Spelling experiment for an arithmetic shift by a constant: every `bvashr` by a
constant respelled as the sign extension of the kept bits.
usage: variants2.py <qdump dir> <out dir> <shape>..."""
import os
import re
import sys

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
TERM = r"(\(concat e_rsi e_rdi\)|[a-z]+\d+)"


def respell(m):
    x, k, w = m.group(1), int(m.group(2)), int(m.group(3))
    if k == 0:
        return x
    return f"((_ sign_extend {k}) ((_ extract {w - 1} {k}) {x}))"


for shape in sys.argv[3:]:
    q = open(os.path.join(src, shape + ".smt2")).read()
    a = re.sub(r"\(bvashr " + TERM + r" \(_ bv(\d+) (\d+)\)\)", respell, q)
    open(os.path.join(out, shape + "__ashr_as_sign_extend.smt2"), "w").write(a)
    # Only the machine's shifts respelled (the source keeps bvashr).
    b = re.sub(r"\(bvashr ([a-z]+\d+) \(_ bv(\d+) (\d+)\)\)", respell, q)
    open(os.path.join(out, shape + "__machine_only.smt2"), "w").write(b)
