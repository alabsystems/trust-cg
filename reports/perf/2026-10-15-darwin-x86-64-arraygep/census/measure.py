#!/usr/bin/env python3
"""Classify the probe's verdicts (`--cf` TSV) on the functions `newly_failing.py`
lists (census-s14 credited, census-main-2854ce did not), by main's refusal.

usage: measure.py <probe cf.tsv> <newly.tsv>
"""
import collections, re, sys
cf = sys.argv[1]
names = [l.split('\t')[0] for l in open(sys.argv[2])]
before = {l.split('\t')[0]: l.rstrip('\n').split('\t')[1] for l in open(sys.argv[2])}
rows = {}
for line in open(cf):
    f = line.rstrip('\n').split('\t')
    rows.setdefault(f[0], f[1])
def norm(s):
    s = re.sub(r'OWNER \d+ defs=\d+', 'OWNER (theorem built, holds on samples)', s)
    s = re.sub(r'OWNER \d+ REFUTED-AT-SAMPLE \d+', 'OWNER REFUTED-AT-SAMPLE', s)
    s = re.sub(r'instruction \d+', 'instruction N', s)
    s = re.sub(r'Value\(\d+\)', 'Value(N)', s)
    s = re.sub(r'row \d+', 'row N', s)
    s = re.sub(r'access \d+', 'access N', s)
    return s[:170]
c = collections.Counter(); bykind = collections.defaultdict(collections.Counter)
for n in names:
    v = rows.get(n, 'NOT IN DUMP')
    k = 'ArrayGep' if 'ArrayGep' in before[n] else ('type hint' if 'type hint' in before[n] else 'other')
    c[norm(v)] += 1
    bykind[k][norm(v)] += 1
print('all 476:')
for k, v in c.most_common(): print(f'{v:5} {k}')
for kind, cc in bykind.items():
    print(f'\n{kind} ({sum(cc.values())}) on main-2854ce:')
    for k, v in cc.most_common(): print(f'{v:5} {k}')
