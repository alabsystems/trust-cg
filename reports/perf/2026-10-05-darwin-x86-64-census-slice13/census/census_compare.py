#!/usr/bin/env python3
"""Compare two Darwin core census runs (baseline `main`, slice 13): failed
roots, promoted and newly failing lists, every named mismatch and refuted
body, the verdict changes of functions bound on both sides, and where the
functions the baseline refused in the slice-13 classes went (each function's
last body trace on each side).

usage: census_compare.py <baseline dir> <new dir> <out dir>
"""
import collections
import json
import os
import re
import sys

base, new, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)


def roots(d):
    found = {}
    for line in open(f'{d}/failed_roots.jsonl'):
        line = line.strip()
        if not line:
            continue
        record = json.loads(line)
        m = re.search(r'non_verified proof entry \S+ in (\S+?): ', record.get('message', ''))
        found[record['symbol']] = m.group(1) if m else None
    return found


PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')


def traces(d):
    by_fn = collections.defaultdict(list)
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = PAT.match(line.rstrip('\n'))
        if m and 'negative-memo hit' not in m.group(2):
            by_fn[m.group(1)].append(m.group(2))
    return by_fn


# The slice-13 classes, by the refusal text of the baseline (`main`): a
# private slot's address stored as data, parameters and call arguments past
# the argument registers, the bulk-memory intrinsics, atomics, and the
# neighbouring escaped-address accesses.
SLICE13 = [
    ("uses a private stack address as a value", "slot address stored"),
    ("register parameters", "parameters on the stack"),
    ("more than six argument registers", "parameters on the stack"),
    ("passes more than six register arguments", "arguments on the stack"),
    ("(Memcpy)", "memcpy/memmove/memset"),
    ("(Memmove)", "memcpy/memmove/memset"),
    ("(Memset)", "memcpy/memmove/memset"),
    ("(AtomicLoad", "atomics"),
    ("(AtomicStore", "atomics"),
    ("on which different private stack slots escaped", "a join of different escapes"),
    ("loads a bool from a private byte", "a bool read of another store's byte"),
]


def slice13_class(text):
    for key, name in SLICE13:
        if key in text:
            return name
    return None


def verdict(lines):
    bound = [l for l in lines if l.startswith('bound rows=')]
    if bound:
        last = bound[-1]
        if 'replay=Valid' in last:
            return 'bound, replays Valid'
        if 'Invalid' in last:
            return 'bound, REFUTED'
        return 'bound, no independently checked proof'
    if any('mismatch' in l for l in lines):
        return 'MISMATCH'
    last = re.sub(r'instruction \d+', 'instruction N', lines[-1])
    last = re.sub(r'row \d+', 'row N', last)
    last = re.sub(r'Block\(\d+\)', 'Block(N)', last)
    last = re.sub(r'\{[^{}]*\}', '{..}', last)
    return 'refused: ' + last.replace('unsupported source-bound x86-64 body: ', '')[:170]


base_roots, new_roots = roots(base), roots(new)
base_traces, new_traces = traces(base), traces(new)
promoted = sorted(set(base_roots) - set(new_roots))
newly = sorted(set(new_roots) - set(base_roots))
lines = [
    f'baseline failed roots: {len(base_roots)}',
    f'slice-13 failed roots: {len(new_roots)}',
    f'promoted: {len(promoted)}',
    f'newly failing: {len(newly)}',
]
mismatches = [(fn, l) for fn, ls in new_traces.items() for l in ls if 'mismatch' in l]
refuted = [(fn, l) for fn, ls in new_traces.items() for l in ls if 'Invalid' in l]
lines.append(f'named mismatches: {len(mismatches)}')
lines.append(f'refuted bodies: {len(refuted)}')
for fn, l in mismatches + refuted:
    lines.append(f'  {fn} {l[:300]}')

# Promoted roots: what the named function was on each side.
attribution = collections.Counter()
for symbol in promoted:
    fn = base_roots[symbol]
    b = verdict(base_traces[fn]) if fn in base_traces else '(untraced)'
    cls = slice13_class(base_traces[fn][-1]) if fn in base_traces else None
    n = verdict(new_traces[fn]) if fn in new_traces else '(untraced)'
    key = f'{cls or b} -> {n}'
    attribution[key] += 1
lines.append('promoted roots by the named function (baseline class -> slice 13):')
for key, n in attribution.most_common():
    lines.append(f'  {n:5d}  {key}')
for symbol in newly:
    fn = new_roots[symbol]
    lines.append(f'NEWLY FAILING {symbol} named {fn}: {new_traces.get(fn, ["(untraced)"])[-1][:300]}')

# Bound on both sides: verdict changes.
changes = collections.Counter()
for fn in set(base_traces) & set(new_traces):
    b, n = verdict(base_traces[fn]), verdict(new_traces[fn])
    if b.startswith('bound') and n.startswith('bound') and b != n:
        changes[f'{b} -> {n}'] += 1
lines.append('verdict changes of functions bound on both sides:')
for key, n in changes.most_common():
    lines.append(f'  {n:5d}  {key}')

# Where the baseline's slice-13 classes went.
transitions = collections.defaultdict(collections.Counter)
with open(f'{out}/slice13_transitions.tsv', 'w') as tsv:
    for fn, ls in sorted(base_traces.items()):
        cls = slice13_class(ls[-1])
        if cls is None:
            continue
        n = verdict(new_traces[fn]) if fn in new_traces else '(untraced)'
        transitions[cls][n] += 1
        tsv.write(f'{fn}\t{cls}\t{n}\n')
lines.append('functions the baseline refused in a slice-13 class, by their slice-13 outcome:')
for cls, outcomes in sorted(transitions.items()):
    lines.append(f'  {cls}: {sum(outcomes.values())}')
    for key, n in outcomes.most_common():
        lines.append(f'      {n:5d}  {key}')

open(f'{out}/promoted.txt', 'w').write('\n'.join(promoted) + '\n')
open(f'{out}/newly_failing.txt', 'w').write('\n'.join(newly) + '\n')
open(f'{out}/compare.txt', 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
