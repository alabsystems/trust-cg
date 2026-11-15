#!/usr/bin/env python3
"""Per root of the design's 33 in-scope domain refusals: the class, the branch probe's
verdict (built or the refusal), and whether every query of a built theorem replayed VERIFIED
within the 30 s deadline (replay_one.py rows; a query whose AY wall is past 30 s counts as the
lane's Timeout).
usage: roots33.py <probe tsv> <smt2 dir with index.tsv> <replay tsv>"""
import collections
import re
import sys

probe, qdir, replay = sys.argv[1:4]
D = '$HOME/tcg-scratch/s20-design/data'
cls = {}
for line in open(f'{D}/inscope.tsv'):
    c, n = line.rstrip('\n').split('\t')[:2]
    cls[n] = c
verdict = {l.split('\t')[0]: l.rstrip('\n').split('\t')[1] for l in open(probe)}
queries = collections.defaultdict(list)
for l in open(f'{qdir}/index.tsv'):
    f = l.rstrip('\n').split('\t')
    if len(f) == 3:
        queries[f[1]] += [f'{f[0]}.part{k}.smt2' for k in range(1, int(f[2]) + 1)]
    else:
        queries[f[1]].append(f'{f[0]}.smt2')
outcome = {}
for l in open(replay):
    f = l.rstrip('\n').split('\t')
    wall = float(re.search(r'wall=([0-9.]+)', l).group(1))
    kind = f[3]
    if kind == 'VERIFIED' and wall > 30.0:
        kind = 'LATE'
    outcome[f[0]] = (kind, wall)
table = collections.Counter()
for n in sorted(cls, key=lambda n: (cls[n], n)):
    v = verdict[n]
    if not v.startswith('OWNER'):
        why = re.sub(r'.*outside the body domain: ', '', v)[:90]
        print(f'{cls[n]}\t{n[-55:]}\tREFUSED\t{why}')
        table[(cls[n], 'refused')] += 1
        continue
    qs = queries[n]
    got = [outcome.get(q, ('MISSING', 0.0)) for q in qs]
    kinds = collections.Counter(k for k, _ in got)
    closes = all(k == 'VERIFIED' for k, _ in got)
    worst = max(w for _, w in got) if got else 0.0
    state = 'CLOSES' if closes else 'built, not certified'
    print(f'{cls[n]}\t{n[-55:]}\t{state}\t{len(qs)} queries {dict(kinds)} max {worst:.1f} s')
    table[(cls[n], state)] += 1
print()
for (c, s), k in sorted(table.items()):
    print(f'{c:16} {s:22} {k}')
print('closes:', sum(k for (c, s), k in table.items() if s == 'CLOSES'), 'of', len(cls))
