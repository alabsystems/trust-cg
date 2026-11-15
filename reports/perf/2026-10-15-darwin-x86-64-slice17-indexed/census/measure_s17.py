#!/usr/bin/env python3
"""Slice 17: classify the probe's verdicts over the design's 51 functions of
the indexed-access class (A: the 35 census roots stopping at the slot offset;
B: 12 behind a size bound; C: 4 behind an i128 loop-carried value), against a
control run (slice 16's probe, the same dump), and, when a replay table of
the run's queries is given (`replay_dir.py`), the offline certification of
each built theorem (every part of a theorem in parts).

usage: measure_s17.py <functions.tsv> <control cf.tsv> <slice-17 cf.tsv>
                      [<smt2 index.tsv> <replay.tsv>]
"""
import collections
import re
import sys

functions, control_tsv, new_tsv = sys.argv[1:4]
index_tsv = sys.argv[4] if len(sys.argv) > 4 else None
replay_tsv = sys.argv[5] if len(sys.argv) > 5 else None


def group(cls):
    if cls == 'SLOT-OFFSET':
        return 'A'
    if cls.startswith('size'):
        return 'B'
    return 'C'


groups = {}
for line in open(functions):
    cols = line.rstrip('\n').split('\t')
    if cols[0] == 'fn':
        continue
    groups[cols[0]] = group(cols[1])


def verdicts(path):
    out = {}
    for line in open(path):
        cols = line.rstrip('\n').split('\t')
        if len(cols) >= 2:
            out[cols[0]] = cols[1:]
    return out


control = verdicts(control_tsv)
new = verdicts(new_tsv)


def kind(verdict):
    if verdict.startswith('OWNER'):
        if 'REFUTED' in verdict:
            return 'REFUTED-ON-SAMPLES'
        return 'BUILT-PARTS' if ' PARTS ' in verdict else 'BUILT'
    return 'REFUSED'


def reason(verdict):
    text = re.sub(r'Value\(\d+\)', 'Value(N)', verdict)
    text = re.sub(r'Block\(\d+\)', 'Block(N)', text)
    text = re.sub(r'\b\d+\b', 'N', text)
    return text[:150]


# Offline certification: each function's queries (one, or one per part).
certified = {}
if index_tsv and replay_tsv:
    outcome = {}
    for line in open(replay_tsv):
        cols = line.rstrip('\n').split('\t')
        outcome[cols[0]] = cols[1]
    for line in open(index_tsv):
        cols = line.rstrip('\n').split('\t')
        stem, name = cols[0], cols[1]
        parts = int(cols[2]) if len(cols) > 2 else 0
        files = [f'{stem}.part{k}.smt2' for k in range(1, parts + 1)] if parts else [f'{stem}.smt2']
        results = [outcome.get(f, 'MISSING') for f in files]
        certified[name] = (all(r == 'VERIFIED' for r in results), results)

table = collections.Counter()
refusals = collections.Counter()
rows = []
for name, g in sorted(groups.items(), key=lambda kv: (kv[1], kv[0])):
    c = control.get(name, ['ABSENT'])[0]
    n = new.get(name, ['ABSENT'])[0]
    k = kind(n) if n != 'ABSENT' else 'ABSENT'
    cert = certified.get(name)
    table[(g, k)] += 1
    if k in ('BUILT', 'BUILT-PARTS') and cert:
        table[(g, 'CERTIFIED' if cert[0] else 'NOT-CERTIFIED')] += 1
    if k == 'REFUSED':
        refusals[(g, reason(n))] += 1
    rows.append((g, name, kind(c) if c != 'ABSENT' else 'ABSENT', reason(c), k, n[:120],
                 '' if cert is None else ('VERIFIED' if cert[0] else ','.join(cert[1]))))

for g in 'ABC':
    total = sum(1 for v in groups.values() if v == g)
    parts = ', '.join(f'{k} {table[(g, k)]}' for k in
                      ('BUILT', 'BUILT-PARTS', 'REFUTED-ON-SAMPLES', 'REFUSED', 'ABSENT',
                       'CERTIFIED', 'NOT-CERTIFIED') if table[(g, k)])
    print(f'{g} ({total}): {parts}')
print()
print('First refusals:')
for (g, text), count in sorted(refusals.items()):
    print(f'  {g} {count:3}  {text}')
print()
print('group\tfunction\tcontrol\tcontrol reason\tslice 17\tverdict\tcertification')
for row in rows:
    print('\t'.join(row))
