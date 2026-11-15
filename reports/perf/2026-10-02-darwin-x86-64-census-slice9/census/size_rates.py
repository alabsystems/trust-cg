#!/usr/bin/env python3
"""Certification rate by bound-row count from census body traces: every
bound body of each run, and the bodies the new run binds that the baseline
did not.

usage: size_rates.py <baseline census dir> [<new census dir>]
"""
import collections
import re
import sys

PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) bound rows=(\d+) replay=(\S+)')
EDGES = [0, 25, 50, 75, 100, 150, 200, 256, 384, 512, 768, 1024, 2048, 10**9]


def load(d):
    out = {}
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = PAT.match(line)
        if m:
            out[m.group(1)] = (int(m.group(2)), m.group(3).startswith('Valid'))
    return out


def table(name, bodies):
    counts = collections.defaultdict(lambda: [0, 0])
    for rows, valid in bodies.values():
        for lo, hi in zip(EDGES, EDGES[1:]):
            if lo <= rows < hi:
                counts[(lo, hi)][0] += 1
                counts[(lo, hi)][1] += valid
    print(name)
    for lo, hi in zip(EDGES, EDGES[1:]):
        n, v = counts[(lo, hi)]
        if n:
            print(f'  {lo:5}-{hi - 1:<6} {v:5}/{n:<5} {100 * v / n:5.1f}%')
    total = sum(v for _, v in bodies.values())
    print(f'  total {total}/{len(bodies)}')


base = load(sys.argv[1])
table('baseline', base)
if len(sys.argv) > 2:
    new = load(sys.argv[2])
    table('new run', new)
    table('newly bound', {f: v for f, v in new.items() if f not in base})
