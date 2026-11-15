#!/usr/bin/env python3
"""Check every constant fold OD-188's fold sweep exercises against z3, an implementation of
SMT-LIB independent of this lane's evaluator: each `FOLD <node>\t<folded>` line of the dump
(the local `dump_constant_folds_for_z3` test) becomes `(assert (not (= <node> <folded>)))`
under push/pop, which must be unsat. usage: z3_folds.py <dump> <out dir>"""
import os, subprocess, sys
dump, out = sys.argv[1:3]
os.makedirs(out, exist_ok=True)
lines = [l.rstrip('\n') for l in open(dump) if l.startswith('FOLD ')]
chunk = 2000
bad = 0
total = 0
for start in range(0, len(lines), chunk):
    part = lines[start:start + chunk]
    q = ['(set-logic QF_BV)']
    for l in part:
        node, folded = l[5:].split('\t')
        q += ['(push 1)', f'(assert (not (= {node} {folded})))', '(check-sat)', '(pop 1)']
    path = os.path.join(out, f'folds_{start // chunk:03d}.smt2')
    open(path, 'w').write('\n'.join(q) + '\n')
    r = subprocess.run(['z3', path], capture_output=True, text=True, timeout=3600)
    answers = r.stdout.split()
    total += len(part)
    for l, a in zip(part, answers):
        if a != 'unsat':
            bad += 1
            print('MISMATCH', a, l[:200])
    if len(answers) != len(part):
        print('ANSWER COUNT', len(answers), len(part), r.stderr[:300])
        bad += 1
print(f'folds checked: {total}; not unsat: {bad}')
