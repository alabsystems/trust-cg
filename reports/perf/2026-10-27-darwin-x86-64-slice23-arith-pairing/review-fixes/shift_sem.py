# The hostile review's z3 script (2026-10-28), verbatim below this header: the barrel the walk
# states equals x86's `shl`/`shr`/`sar r, cl` (CL masked to 5 bits, 6 under REX.W) at 32 and 64
# bits and differs at 8 and 16. Report section 9, item 3.
import z3
def barrel(op, v, amt):
    w = v.size(); stages = w.bit_length()-1
    t = v
    for i in range(stages):
        by = 1 << i
        if op == 'shl':
            sh = z3.Concat(z3.Extract(w-1-by, 0, t), z3.BitVecVal(0, by))
        elif op == 'lshr':
            sh = z3.Concat(z3.BitVecVal(0, by), z3.Extract(w-1, by, t))
        else:
            sh = z3.SignExt(by, z3.Extract(w-1, by, t))
        t = z3.If(z3.Extract(i, i, amt) == 1, sh, t)
    return t
def x86(op, v, cl):
    w = v.size(); m = 63 if w == 64 else 31   # Intel: 5-bit mask unless REX.W
    c = z3.ZeroExt(w-8, cl & m) if w > 8 else (cl & m)
    return {'shl': v << c, 'lshr': z3.LShR(v, c), 'ashr': v >> c}[op]
for w in (8, 16, 32, 64):
    for op in ('shl', 'lshr', 'ashr'):
        v = z3.BitVec('v', w); cl = z3.BitVec('cl', 8)
        s = z3.Solver(); s.add(barrel(op, v, cl) != x86(op, v, cl))
        r = s.check()
        print(w, op, 'barrel==x86(cl&%d)' % (63 if w == 64 else 31), 'EQUAL' if r == z3.unsat else 'DIFFER e.g. %s' % s.model())
