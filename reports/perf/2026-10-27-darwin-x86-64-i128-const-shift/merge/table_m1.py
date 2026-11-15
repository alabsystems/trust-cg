#!/usr/bin/env python3
"""Per function: every query of a stage replayed (the cache of measure_m1.py), summarised per route:
the units exact (whole or each part), the units' OD-206 generalizations, the OD-197 claims exact and
the claims' generalizations, and a paired theorem's arbiter. One row per function; a second stage's
units (the fold off, = main) beside it for the units' exact replays.
usage: table_m1.py <stage dir> [<base stage dir>]"""
import glob, hashlib, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
cache = {}
for l in open(os.path.join(HERE, 'data', 'replays.jsonl')):
    r = json.loads(l); cache[r['sha']] = r
def rec(p):
    return cache.get(hashlib.sha256(open(p, 'rb').read()).hexdigest())
def short(r):
    if r is None: return 'not replayed'
    o = {'certified': 'cert', 'not-certified': 'unknown' if r.get('verdict') != 'sat' else 'sat', 'timeout': 'timeout'}.get(r['outcome'], r['outcome'])
    if r['outcome'] == 'not-certified' and r.get('verdict') == 'unknown':
        n = ' '.join(x[1] for x in r.get('notes', []))
        o = 'memout' if 'memout' in n else ('self-check-rejected' if 'self-check' in n else 'unknown')
    return f"{o} {r.get('ay_s')}" + (f"/{r['clean_s']}" if r.get('clean_s') is not None else '')
def stage(d):
    rows = {}
    for line in open(os.path.join(d, 'q', 'index.tsv')):
        h, name, *p = line.rstrip('\n').split('\t')
        n = int(p[0]) if p else 0
        units = [f'{h}.part{k}' for k in range(1, n + 1)] if n else [h]
        rows[name] = (h, units)
    return rows
new = stage(sys.argv[1]); base = stage(sys.argv[2]) if len(sys.argv) > 2 else {}
q = os.path.join(sys.argv[1], 'q')
print('| function | units | units exact (merged) | units exact (main) | unit generalizations | claims exact | claim generalizations | arbiter |')
print('| --- | ---: | --- | --- | --- | --- | --- | --- |')
for name, (h, units) in new.items():
    ex = '; '.join(short(rec(os.path.join(q, u + '.smt2'))) for u in units)
    b = base.get(name)
    bex = '; '.join(short(rec(os.path.join(sys.argv[2], 'q', u + '.smt2'))) for u in b[1]) if b else '-'
    gens = [g for u in units for g in [os.path.join(q, u + '.gen.smt2')] if os.path.exists(g)]
    gx = '; '.join(short(rec(g)) for g in gens) or '-'
    claims = sorted(p for p in glob.glob(os.path.join(q, h + '*.claim*.smt2')) if not p.endswith('.gen.smt2') and '.unpaired' not in p)
    cg = sorted(p for p in glob.glob(os.path.join(q, h + '*.claim*.gen.smt2')) if '.unpaired' not in p)
    def summ(ps):
        if not ps: return '-'
        rs = [rec(p) for p in ps]
        c = [r for r in rs if r and r['outcome'] == 'certified']
        other = sorted({short(r).split(' ')[0] for r in rs if not (r and r['outcome'] == 'certified')})
        return f"{len(c)}/{len(ps)} cert (max {max((r['ay_s'] for r in c), default=0)} s)" + (f"; {len(ps)-len(c)} {'/'.join(other)}" if other else '')
    arb = [p for p in glob.glob(os.path.join(q, h + '.unpaired*.smt2')) if '.claim' not in p and not p.endswith('.gen.smt2')]
    ax = '; '.join(short(rec(p)) for p in sorted(arb)) or '-'
    print(f"| `{name.split('4core')[-1]}` | {len(units)} | {ex} | {bex} | {gx} | {summ(claims)} | {summ(cg)} | {ax} |")
