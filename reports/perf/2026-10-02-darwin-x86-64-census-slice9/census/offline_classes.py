#!/usr/bin/env python3
"""Offline slice-9 measurement: the control-flow shape of every function the
baseline census refused for the slice-6 bounds (more than sixteen blocks, a
path of more than 256 instructions, more than sixteen paths), and what the
slice-9 owner (the probe's `--cf` TSV over a dumped `core`) does with each.

usage: offline_classes.py <baseline census dir> <probe --cf tsv> <out dir>

Writes <out>/class_functions.tsv (one row per class function: baseline
refusal, new verdict, shape) and <out>/newly_bound.txt (names for the SMT
dump), and prints the distributions.
"""
import collections
import os
import re
import sys

base, tsv, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)
PRIVATE = re.compile(r'^__trust_cg_private\.core\.[^.]*\.\d+\.\d+\.')
TRACE = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')

last = {}
for line in open(f'{base}/stderr.log', errors='replace'):
    m = TRACE.match(line.rstrip('\n'))
    if m and 'negative-memo hit' not in m.group(2):
        last[PRIVATE.sub('', m.group(1))] = m.group(2)


def base_class(text):
    if 'blocks (the lane admits 1 to 16)' in text:
        return 'blocks'
    if 'instructions (the lane admits at most 256)' in text:
        return 'path'
    if 'entry-to-end paths' in text:
        return 'paths'
    return None


def new_class(verdict):
    if verdict.startswith('OWNER'):
        return 'bound (sample-REFUTED)' if 'REFUTED' in verdict else 'bound'
    for key, name in (
        ('a loop', 'loop'),
        ('blocks (the lane admits', 'over the block bound'),
        ('instructions (the lane admits', 'over the instruction bound'),
        ('more than', 'over the machine bounds'),
        ('(Checked', 'checked arithmetic'),
        ('CallIndirect', 'CallIndirect'),
        ('correspond one to one', 'no block correspondence'),
        ('different private stack slots escaped', 'join of different escapes'),
        ('different kinds of value', 'root of different kinds at a join'),
        ('which a path into it already defined', 'redefinition after a join'),
        ('escapes', 'slot address escapes'),
        ('(Guard', 'guards'),
        ('Bnot', 'Bnot'),
        ('CtPop', 'CtPop'),
        ('shifts by a non-constant', 'variable shift'),
        ('(Udiv', 'division'), ('(Urem', 'division'), ('(Sdiv', 'division'), ('(Srem', 'division'),
        ('i128', 'i128'),
        ('floating-point', 'floating point'),
        ('mismatch', 'MISMATCH'),
    ):
        if key in verdict:
            return name
    return 'other: ' + re.sub(r'\d+', 'N', verdict)[:90]


rows = []
for line in open(tsv, errors='replace'):
    f = line.rstrip('\n').split('\t')
    if len(f) < 9:
        continue
    name, verdict = f[0], f[1]
    klass = base_class(last.get(name, ''))
    if klass is None:
        continue
    blocks, looped, paths, longest, instrs, mblocks, mrows = f[2:9]
    rows.append((name, klass, new_class(verdict), verdict, int(blocks), looped == 'true',
                 int(paths), int(longest), int(instrs), int(mblocks), int(mrows)))
with open(f'{out}/class_functions.tsv', 'w') as o:
    o.write('name\tbaseline\tslice9\tverdict\tblocks\tloop\tpaths\tlongest\tinstructions\tmachine_blocks\tmachine_rows\n')
    for r in rows:
        o.write('\t'.join(str(x) for x in r) + '\n')
with open(f'{out}/newly_bound.txt', 'w') as o:
    for r in rows:
        if r[2].startswith('bound'):
            o.write(r[0] + '\n')
traced = collections.Counter(base_class(t) for t in last.values() if base_class(t))
print('baseline class functions traced:', dict(traced), ' in the dump:', len(rows))


def hist(values, edges):
    counts = collections.Counter()
    for v in values:
        for lo, hi in zip(edges, edges[1:]):
            if lo <= v < hi:
                counts[(lo, hi)] += 1
    return ', '.join(f'{lo}-{hi - 1}: {counts[(lo, hi)]}' for lo, hi in zip(edges, edges[1:]) if counts[(lo, hi)])


for klass in ('blocks', 'path', 'paths'):
    sub = [r for r in rows if r[1] == klass]
    if not sub:
        continue
    acyclic = [r for r in sub if not r[5]]
    print(f'\n== baseline class {klass}: {len(sub)} functions, {len(sub) - len(acyclic)} with a loop')
    print('  LIR blocks:', hist([r[4] for r in sub], [1, 17, 25, 33, 49, 65, 129, 10**9]))
    print('  paths (acyclic):', hist([r[6] for r in acyclic], [1, 17, 65, 257, 1025, 4097, 10**30]))
    print('  longest path (acyclic):', hist([r[7] for r in acyclic], [1, 257, 385, 513, 769, 1025, 2049, 10**9]))
    print('  instructions:', hist([r[8] for r in sub], [1, 257, 513, 769, 1025, 2049, 10**9]))
    print('  machine rows:', hist([r[10] for r in sub], [1, 257, 513, 1025, 2049, 4097, 10**9]))
    print('  slice-9 verdict:')
    for k, v in collections.Counter(r[2] for r in sub).most_common():
        print(f'    {v:4} {k}')
