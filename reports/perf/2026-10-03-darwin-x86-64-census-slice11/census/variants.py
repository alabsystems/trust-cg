#!/usr/bin/env python3
"""Spelling experiments for the slice-11 theorems the qualification AY/Clean pair
does not certify: write variant queries of the dumped canonical ones (QDUMP) into
OUT, each a satisfiability-preserving respelling of the same theorem, for
replay_dir.py.
usage: variants.py <qdump dir> <out dir>"""
import os
import re
import sys

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)


def read(name):
    return open(os.path.join(src, name + ".smt2")).read()


def write(name, text):
    open(os.path.join(out, name + ".smt2"), "w").write(text)


def const_shift(op, x, k, w=128):
    """A shift of `x` (w bits) by the constant `k` as an extract and a concat."""
    if k == 0:
        return x
    if op == "bvshl":
        return f"(concat ((_ extract {w - 1 - k} 0) {x}) (_ bv0 {k}))"
    if op == "bvlshr":
        return f"(concat (_ bv0 {k}) ((_ extract {w - 1} {k}) {x}))"
    return f"((_ sign_extend {k}) ((_ extract {w - 1} {k}) {x}))"


# (1) The source's constant 128-bit shift spelled as extract/concat.
for shape in ["ShrU128By64", "ShlU128By3", "SarI128By100"]:
    q = read(shape)
    a = re.sub(r"\((bvshl|bvlshr|bvashr) (\(concat e_rsi e_rdi\)) \(_ bv(\d+) 128\)\)",
               lambda m: const_shift(m.group(1), m.group(2), int(m.group(3))), q)
    write(f"{shape}__source_extract", a)

# (2) The sign extension spelled through its sign bit: the high half all ones
# exactly when bit 63 is set.
q = read("SextI64")
a = q.replace("((_ extract 127 64) ((_ sign_extend 64) p0))",
              "(ite (= ((_ extract 63 63) p0) #b1) (_ bv18446744073709551615 64) (_ bv0 64))")
write("SextI64__ite_sign", a)
b = q.replace("((_ extract 127 64) ((_ sign_extend 64) p0))",
              "((_ sign_extend 63) ((_ extract 63 63) p0))")
write("SextI64__extend_sign_bit", b)
c = q.replace("((_ extract 63 0) ((_ sign_extend 64) p0))", "p0")
write("SextI64__low_simplified", c)
d = c.replace("((_ extract 127 64) ((_ sign_extend 64) p0))",
              "((_ sign_extend 63) ((_ extract 63 63) p0))")
write("SextI64__both", d)
