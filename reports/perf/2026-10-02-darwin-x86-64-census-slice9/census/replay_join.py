#!/usr/bin/env python3
"""Join `replay_dir.py` outcome tables of probe-dumped queries (files named
by a hash, `index.tsv` mapping hash -> function) with the probe's `--cf`
TSV: every query's outcome per AY, with its bound rows, blocks, paths and
machine rows, and the counts per outcome and per bound-row bucket.

usage: replay_join.py <smt dir with index.tsv> <probe --cf tsv> <label=replay.tsv>...
"""
import collections
import sys

smt_dir, probe = sys.argv[1], sys.argv[2]
runs = [arg.split('=', 1) for arg in sys.argv[3:]]
index = {}
for line in open(f'{smt_dir}/index.tsv'):
    h, name = line.rstrip('\n').split('\t', 1)
    index[h] = name
shape = {}
for line in open(probe, errors='replace'):
    f = line.rstrip('\n').split('\t')
    if len(f) >= 9 and f[1].startswith('OWNER'):
        shape[f[0]] = (int(f[1].split()[1]), int(f[2]), f[4], int(f[8]))
outcome = collections.defaultdict(dict)
for label, path in runs:
    for line in open(path):
        f = line.rstrip('\n').split('\t')
        outcome[f[0][:-len('.smt2')]][label] = (f[1], float(f[2]))
EDGES = [0, 100, 200, 256, 384, 512, 768, 1024, 10**9]
for label, _ in runs:
    by = collections.defaultdict(collections.Counter)
    for h, results in outcome.items():
        rows = shape.get(index.get(h, ''), (0,))[0]
        for lo, hi in zip(EDGES, EDGES[1:]):
            if lo <= rows < hi:
                by[(lo, hi)][results[label][0]] += 1
    print(f'== {label}')
    for lo, hi in zip(EDGES, EDGES[1:]):
        c = by[(lo, hi)]
        if c:
            print(f'  rows {lo:4}-{hi - 1:<5} VERIFIED {c["VERIFIED"]:3} / {sum(c.values()):3}  {dict(c)}')
print('== certified by some AY')
for h, results in sorted(outcome.items()):
    if any(kind == 'VERIFIED' for kind, _ in results.values()):
        name = index.get(h, h)
        print(' ', shape.get(name), {k: v for k, v in results.items()}, name[:100])
