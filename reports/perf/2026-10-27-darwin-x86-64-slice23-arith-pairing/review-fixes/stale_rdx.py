# The hostile review's z3 script (2026-10-28), verbatim below this header: a `div` with RDX the
# divisor minus one never faults and divides (d - 1) * 2^64 + a; its exact theorem is satisfiable
# (refuted) and, paired on its stamp alone, unsat (credited). Report section 9, item 2.
import z3
a, d = z3.BitVecs('a d', 64)
rdx = d - 1                     # wrong lowering: RDX := divisor-1 instead of 0
wide = z3.Concat(rdx, a)
q_machine = z3.Extract(63, 0, z3.UDiv(wide, z3.ZeroExt(64, d)))
fault = z3.Or(d == 0, z3.UGE(rdx, d))          # x86 #DE: zero divisor or quotient overflow
s = z3.Solver()
# source: a / d (stops iff d == 0). Correct lowering requires: machine faults iff source stops, and equal quotient when running
s.add(z3.Not(z3.And(fault == (d == 0), z3.Implies(d != 0, q_machine == z3.UDiv(a, d)))))
print('exact (unpaired) theorem of RDX:=d-1:', s.check(), s.model() if s.check()==z3.sat else '')
# mutant pair-stamp-only: quotient name redefined as udiv(a, d); claims a=a, d=d
s2 = z3.Solver()
s2.add(z3.Not(z3.And(fault == (d == 0), z3.Implies(d != 0, z3.UDiv(a, d) == z3.UDiv(a, d)))))
print('paired theorem under pair-stamp-only:', s2.check(), '(unsat = credited)')
