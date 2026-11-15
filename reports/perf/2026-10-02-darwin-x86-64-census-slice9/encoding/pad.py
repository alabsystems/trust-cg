"""Pad a certified query with K extra definitional premises (fresh names,
unused by the goal) and K extra 64-bit inputs; usage: pad.py in.smt2 K out.smt2 [nest]"""
import sys
src, k, dst = sys.argv[1], int(sys.argv[2]), sys.argv[3]
nest = len(sys.argv) > 4
text = open(src).read()
lines = text.split('\n')
out = []
for line in lines:
    if line.startswith('(assert '):
        body = line[len('(assert '):-1]
        prem = ''
        close = ''
        for i in range(k):
            prev = 'x_pad' if i == 0 or not nest else f'd_pad{i-1}'
            prem += f'(and (= d_pad{i} (bvadd {prev} (_ bv{i+1} 64))) '
            close += ')'
        out.append(f'(assert {prem}{body}{close})')
    elif line.startswith('(set-logic'):
        out.append(line)
        out.append('(declare-const x_pad (_ BitVec 64))')
        for i in range(k):
            out.append(f'(declare-const d_pad{i} (_ BitVec 64))')
    else:
        out.append(line)
open(dst, 'w').write('\n'.join(out))
