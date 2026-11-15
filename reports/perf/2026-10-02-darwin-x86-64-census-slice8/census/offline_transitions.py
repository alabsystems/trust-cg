#!/usr/bin/env python3
"""Offline verdict transitions of the slice-8 classes between two probe
--sig TSVs (baseline owner, slice-8 owner) over the same dumped module.

usage: offline_transitions.py <before.tsv> <after.tsv>
"""
import collections
import sys


def load(path):
    return {line.split('\t')[0]: line.rstrip('\n').split('\t') for line in open(path)}


a, b = load(sys.argv[1]), load(sys.argv[2])


def cls(v):
    if v.startswith('OWNER'):
        return 'bound'
    if 'at most six register parameters' in v:
        return 'more than six parameters'
    if 'register parameters' in v:
        return 'non-scalar parameter'
    if 'I32 or I64 results' in v:
        return 'non-scalar result'
    if 'no scalar result type' in v:
        return 'call result with no scalar type'
    if 'inconsistent type hint' in v:
        return 'inconsistent type hint'
    return 'other'


newly = collections.Counter()
for n in a:
    if n in b and not a[n][1].startswith('OWNER') and b[n][1].startswith('OWNER'):
        newly[cls(a[n][1])] += 1
print('newly bound by baseline class', dict(newly), sum(newly.values()))
lost = [n for n in a if n in b and a[n][1].startswith('OWNER') and not b[n][1].startswith('OWNER')]
print('bound before and not now', len(lost))
refuted = [n for n in b if 'REFUTED' in b[n][1]]
print('bound now and refuted at a sample', len(refuted))
totals, became = collections.Counter(), collections.Counter()
for n in a:
    if n not in b:
        continue
    k = cls(a[n][1])
    if k not in ('non-scalar parameter', 'non-scalar result', 'call result with no scalar type',
                 'inconsistent type hint'):
        continue
    totals[k] += 1
    v = b[n][1]
    if v.startswith('OWNER'):
        d = 'bound'
    elif 'i128' in v:
        d = 'i128'
    elif 'floating' in v:
        d = 'floating-point'
    elif 'six' in v:
        d = 'stack parameters or arguments'
    elif 'INTEGER register class' in v:
        d = 'MEMORY class or an i128 field'
    elif 'control flow' in v:
        d = 'control flow (loop, > 16 blocks, long path)'
    else:
        d = 'a later instruction outside the lane'
    became[(k, d)] += 1
print(dict(totals))
for (k, d), v in sorted(became.items()):
    print(f'{k:35} -> {d:45} {v}')
