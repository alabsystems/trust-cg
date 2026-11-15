"""synth.py <part.smt2> <out.smt2> <cut> <slot> [wrong]: OD-233's rule applied to one dumped
part, spelled as ~/tcg-scratch/od233-design/work/synth/p2-defined.smt2 spells wtf8's: the
cut's slot bytes x{cut}b{slot}o0..7 are DEFINED as the bytes of p1 (the source's `s.len()`
parameter, bound p1 := e_rsi as the caller view binds it), both as conjuncts ahead of the
part's own assertion. Nothing else changes. With `wrong`, the MACHINE side's uses of the
`len` register (e_rsi, Closed at the cut) in the failing comparisons are replaced by
e_rsi + 1, as p2-defined-wrong.smt2 does (a machine that compares len+1)."""
import sys
src, out, cut, slot = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
wrong = len(sys.argv) > 5 and sys.argv[5] == 'wrong'
s = open(src).read()
names = [f'x{cut}b{slot}o{k}' for k in range(8)]
for n in names:
    assert f'(declare-const {n} (_ BitVec 8))' in s, n
assert '(declare-const p1 ' not in s
anchor = f'(declare-const {names[0]} (_ BitVec 8))'
s = s.replace(anchor, '(declare-const p1 (_ BitVec 64))\n' + anchor, 1)
lines = s.split('\n')
ai = [i for i, l in enumerate(lines) if l.startswith('(assert ')]
assert len(ai) == 1
body = lines[ai[0]][len('(assert '):-1]
defs = ' '.join(f'(= {n} ((_ extract {8*k+7} {8*k}) p1))' for k, n in enumerate(names))
body = f'(and (and (= p1 e_rsi) (and {defs})) {body})'
if wrong:
    reps = {
        '2': [('(bvult e_rsi e_rcx)', '(bvult (bvadd e_rsi #x0000000000000001) e_rcx)')],
        '6': [('(bvult e_rdx e_rsi)', '(bvult e_rdx (bvadd e_rsi #x0000000000000001))'),
              ('(ite (= e_rdx e_rsi) (_ bv1 8) (_ bv0 8))', '(ite (= e_rdx (bvadd e_rsi #x0000000000000001)) (_ bv1 8) (_ bv0 8))')],
        '9': [],
    }[cut]
    for a, b in reps:
        c = body.count(a); assert c >= 1, a
        body = body.replace(a, b)
        print(f'replaced {c} x {a}', file=sys.stderr)
lines[ai[0]] = f'(assert {body})'
open(out, 'w').write('\n'.join(lines))
