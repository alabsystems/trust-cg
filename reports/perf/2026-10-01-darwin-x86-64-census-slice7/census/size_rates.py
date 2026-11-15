#!/usr/bin/env python3
"""Certification rate by bound-row count: the baseline's bound bodies against the
bodies slice 7 newly binds (from the two census traces)."""
import collections, os, re
R = os.path.expanduser('~/tcg-scratch/runs')
pat = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) bound rows=(\d+) replay=(\S+)')


def load(p):
    d = {}
    for l in open(p, errors='replace'):
        m = pat.match(l)
        if m:
            d[m.group(1)] = (int(m.group(2)), m.group(3).startswith('Valid'))
    return d


b = load(f'{R}/census-main-336a/stderr.log')
n = load(f'{R}/census-s7/stderr.log')
new = {f: v for f, v in n.items() if f not in b}


def bucket(r):
    return '<50' if r < 50 else '50-99' if r < 100 else '100-149' if r < 150 else '>=150'


for name, d in (('baseline', b), ('newly bound', new)):
    c = collections.defaultdict(lambda: [0, 0])
    for r, v in d.values():
        c[bucket(r)][0] += 1
        c[bucket(r)][1] += v
    print(name, {k: f'{c[k][1]}/{c[k][0]}' for k in ['<50', '50-99', '100-149', '>=150']})
