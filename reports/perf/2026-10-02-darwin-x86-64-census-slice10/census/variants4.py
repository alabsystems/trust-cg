#!/usr/bin/env python3
"""Respell the source overflow of unsigned checked add/sub in census queries as the
machine's flag (add: carry out of the top bit; sub: the borrow `bvult`), the same
predicate trust-ir states (`unsigned_overflow`), to see whether AY certifies them.
usage: variants4.py <queries dir> <out dir>"""
import os
import re
import sys

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
ADD = re.compile(r"\(not \(= \(\(_ zero_extend 1\) \(\(_ extract 63 0\) \(bvadd \(\(_ zero_extend 1\) (\w+)\) \(\(_ zero_extend 1\) (\w+)\)\)\)\) \(bvadd \(\(_ zero_extend 1\) \1\) \(\(_ zero_extend 1\) \2\)\)\)\)")
SUB = re.compile(r"\(not \(= \(\(_ zero_extend 1\) \(\(_ extract 63 0\) \(bvsub \(\(_ zero_extend 1\) (\w+)\) \(\(_ zero_extend 1\) (\w+)\)\)\)\) \(bvsub \(\(_ zero_extend 1\) \1\) \(\(_ zero_extend 1\) \2\)\)\)\)")
for name in sorted(os.listdir(src)):
    if not name.endswith(".smt2"):
        continue
    text = open(os.path.join(src, name)).read()
    new = ADD.sub(lambda m: f"(= ((_ extract 64 64) (bvadd ((_ zero_extend 1) {m.group(1)}) ((_ zero_extend 1) {m.group(2)}))) (_ bv1 1))", text)
    new = SUB.sub(lambda m: f"(bvult {m.group(1)} {m.group(2)})", new)
    if new != text:
        open(os.path.join(out, name), "w").write(new)
print(len(os.listdir(out)))
