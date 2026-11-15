#!/usr/bin/env python3
"""Offline certification rate by size: join a `replay_dir.py` outcome table
(one row per dumped query, `<name>.smt2`) with the probe's `--cf` TSV (bound
rows and shape per function) and print the outcome counts per bound-row and
machine-row bucket, and per baseline class when a class table is given.

usage: replay_rates.py <replay.tsv> <probe --cf tsv> [<class_functions.tsv>]
"""
import collections
import sys

replay, probe = sys.argv[1], sys.argv[2]
classes = {}
if len(sys.argv) > 3:
    for line in open(sys.argv[3]):
        f = line.rstrip('\n').split('\t')
        if f[0] != 'name':
            classes[f[0][:200]] = f[1]
shape = {}
for line in open(probe, errors='replace'):
    f = line.rstrip('\n').split('\t')
    if len(f) >= 9 and f[1].startswith('OWNER'):
        shape[f[0][:200]] = (int(f[1].split()[1]), int(f[8]), int(f[4]))
EDGES = [0, 50, 100, 150, 200, 256, 384, 512, 768, 1024, 2048, 10**9]
by_rows = collections.defaultdict(collections.Counter)
by_class = collections.defaultdict(collections.Counter)
times = collections.defaultdict(list)
for line in open(replay):
    f = line.rstrip('\n').split('\t')
    name, kind, secs = f[0][:-len('.smt2')], f[1], float(f[2])
    if name not in shape:
        continue
    rows = shape[name][0]
    for lo, hi in zip(EDGES, EDGES[1:]):
        if lo <= rows < hi:
            by_rows[(lo, hi)][kind] += 1
            times[(lo, hi)].append(secs)
    by_class[classes.get(name, '-')][kind] += 1
print('bound rows | VERIFIED / total | outcomes | median seconds')
for lo, hi in zip(EDGES, EDGES[1:]):
    c = by_rows[(lo, hi)]
    if not c:
        continue
    total = sum(c.values())
    t = sorted(times[(lo, hi)])
    print(f'{lo:5}-{hi - 1:<6} {c["VERIFIED"]:4} / {total:<4} {dict(c)}  {t[len(t) // 2]:.1f}')
if classes:
    print('by baseline class:')
    for k, c in sorted(by_class.items()):
        print(f'  {k:10} {c["VERIFIED"]:4} / {sum(c.values()):<4} {dict(c)}')
