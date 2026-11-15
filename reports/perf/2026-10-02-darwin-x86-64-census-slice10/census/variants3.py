#!/usr/bin/env python3
"""The 64-bit multiply spellings tried (all rejected by AY's strict self-check on the
qualification host): `bvumulo` on both sides, the overflow equation alone, and the
value equation alone, of the dumped canonical `MulU64` query.
usage: variants3.py <qdump dir> <out dir>"""
import os
import sys

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
q = open(os.path.join(src, "MulU64.smt2")).read()
SOURCE = ("(not (= ((_ zero_extend 64) ((_ extract 63 0) (bvmul ((_ zero_extend 64) p0) "
          "((_ zero_extend 64) p1)))) (bvmul ((_ zero_extend 64) p0) ((_ zero_extend 64) p1))))")
MACHINE = "(not (= ((_ extract 127 64) (bvmul ((_ zero_extend 64) m2) ((_ zero_extend 64) m1))) (_ bv0 64)))"
GOAL = "(not (= true (and (= s0 m8) (= ((_ zero_extend 31) s1) ((_ extract 31 0) m9)))))"
assert SOURCE in q and MACHINE in q and GOAL in q
variants = {
    "MulU64__umulo": q.replace(SOURCE, "(bvumulo p0 p1)").replace(MACHINE, "(bvumulo m2 m1)"),
    "MulU64__flag_only": q.replace(GOAL, "(not (= ((_ zero_extend 31) s1) ((_ extract 31 0) m9)))"),
    "MulU64__value_only": q.replace(GOAL, "(not (= s0 m8))"),
}
for name, text in variants.items():
    open(os.path.join(out, name + ".smt2"), "w").write(text)
print(sorted(variants))
