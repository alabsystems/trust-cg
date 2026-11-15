#!/usr/bin/env python3
"""Review a golden migration: per golden file, the theorems that changed, and for each changed
theorem two independent checks of the rewrite against the old theorem (the design's):
  * an evaluation sweep (smtq.py's evaluator, 256 seeded inputs): equal claim values, and every
    kept definition equal to the old definition of that name;
  * z3, both directions (z3_equiv.py's A and B queries), each UNSAT within 60 s.
usage: review_goldens.py <old dir> <new dir> <out dir> [--z3 all|N]
Writes <out dir>/review.jsonl (one line per changed theorem) and prints a per-file table."""
import json, os, random, re, subprocess, sys, zlib
sys.path.insert(0, os.path.expanduser('~/tcg-scratch/s18-design/scripts'))
import smtq as S
from respell import sweep

old_dir, new_dir, out = sys.argv[1:4]
z3_mode = sys.argv[sys.argv.index('--z3') + 1] if '--z3' in sys.argv else 'all'
os.makedirs(out, exist_ok=True)
Z3 = 'z3'

def sections(text):
    chunks = re.split(r"^;;;; (.*)$", text, flags=re.M)
    return [(chunks[k].strip(), chunks[k + 1].strip('\n')) for k in range(1, len(chunks), 2)]

def z3(path):
    try:
        p = subprocess.run([Z3, '-T:60', path], capture_output=True, text=True, timeout=90)
        return p.stdout.strip().splitlines()[0] if p.stdout.strip() else 'none'
    except subprocess.TimeoutExpired:
        return 'timeout'

rep = open(os.path.join(out, 'review.jsonl'), 'w')
table = []
n_z3 = 0
for fn in sorted(os.listdir(new_dir)):
    if not fn.endswith('.smt2'):
        continue
    old = sections(open(os.path.join(old_dir, fn)).read())
    new = sections(open(os.path.join(new_dir, fn)).read())
    assert [a for a, _ in old] == [b for b, _ in new], fn
    changed = 0
    bad = 0
    for (shape, a), (_, b) in zip(old, new):
        if a == b:
            continue
        changed += 1
        rec = {'file': fn, 'shape': shape, 'bytes_old': len(a), 'bytes_new': len(b)}
        t1 = S.Theorem(S.Query(a)); t2 = S.Theorem(S.Query(b))
        rec['defs'] = [len(t1.defs), len(t2.defs)]
        rec['claims'] = [len(S.conjuncts_right(t1.machine)) if t1.source == S.TRUE else 1,
                         len(S.conjuncts_right(t2.machine)) if t2.source == S.TRUE else 1]
        mm, fc, first = sweep(t1, (t2.defs, t2.source, t2.machine), 256, zlib.crc32((fn + shape).encode()))
        rec['sweep_mismatches'] = mm
        rec['false_claims'] = fc
        if z3_mode == 'all' or n_z3 < int(z3_mode):
            n_z3 += 1
            base = re.sub(r'[^A-Za-z0-9_]', '_', f'{fn[:-5]}__{shape}')
            po, pn = os.path.join(out, 'q', base + '.old.smt2'), os.path.join(out, 'q', base + '.new.smt2')
            os.makedirs(os.path.join(out, 'q'), exist_ok=True)
            open(po, 'w').write(a + '\n'); open(pn, 'w').write(b + '\n')
            zd = os.path.join(out, 'z3')
            subprocess.run([sys.executable, os.path.expanduser('~/tcg-scratch/s18-design/scripts/z3_equiv.py'), po, pn, zd],
                           check=True, capture_output=True)
            rec['z3_A'] = z3(os.path.join(zd, base + '.old.A.smt2'))
            rec['z3_B'] = z3(os.path.join(zd, base + '.old.B.smt2'))
        if mm or rec.get('z3_A', 'unsat') != 'unsat' or rec.get('z3_B', 'unsat') != 'unsat':
            bad += 1
        rep.write(json.dumps(rec) + '\n'); rep.flush()
    table.append((fn, len(new), changed, bad))
print('| file | theorems | changed | sweep or z3 failures |')
print('| --- | ---: | ---: | ---: |')
for fn, n, c, b in table:
    print(f'| `{fn}` | {n} | {c} | {b} |')
print(f'| total | {sum(t[1] for t in table)} | {sum(t[2] for t in table)} | {sum(t[3] for t in table)} |')
