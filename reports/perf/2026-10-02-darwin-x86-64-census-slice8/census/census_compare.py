#!/usr/bin/env python3
"""Compare two Darwin core census runs (baseline, slice 8): failed roots,
promoted and newly failing lists, the body-trace class of every traced
function on each side (its bound verdict if it has one, else its last
refusal), where the baseline's slice-8 classes went, and every named
mismatch.

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
    found = set()
    for line in open(f'{d}/failed_roots.jsonl'):
        line = line.strip()
        if line:
            found.add(json.loads(line)['symbol'])
    return found


PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')


def traces(d):
    by_fn = collections.defaultdict(list)
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = PAT.match(line.rstrip('\n'))
        if m and 'negative-memo hit' not in m.group(2):
            by_fn[m.group(1)].append(m.group(2))
    return by_fn


def norm(text):
    text = re.sub(r'row \d+', 'row N', text)
    text = re.sub(r'instruction \d+', 'instruction N', text)
    text = re.sub(r'Block\(\d+\)', 'Block(N)', text)
    text = re.sub(r'\bv\d+\b', 'vN', text)
    text = re.sub(r'Value\(\d+\)', 'Value(N)', text)
    text = re.sub(r'name: "[^"]*"', 'name: ..', text)
    text = re.sub(r'\d+', 'N', text)
    return text


SLICE8 = (
    'register parameters',
    'I32 or I64 results',
    'no scalar result type',
)


def klass(lines):
    bound = [l for l in lines if l.startswith('bound rows=')]
    if bound:
        last = bound[-1]
        if 'replay=Valid' in last:
            return 'bound, replays Valid'
        if 'Invalid' in last:
            return 'bound, REFUTED'
        return 'bound, no independently checked proof'
    last = lines[-1]
    if 'requires at most six register parameters' in last:
        return 'refused: more than six register parameters'
    if 'register parameters' in last:
        return 'refused: a non-scalar parameter (pre-slice-8 text)'
    if 'I32 or I64 results' in last:
        return 'refused: a non-scalar result (pre-slice-8 text)'
    if 'has no scalar result type' in last:
        return 'refused: a call result with no scalar type'
    if 'inconsistent type hint' in last:
        return 'refused: an inconsistent sidecar type hint'
    if 'has an i128' in last:
        return 'refused (slice 8): an i128 ' + ('parameter' if 'parameter' in last else 'result')
    if 'floating-point or vector' in last:
        return 'refused (slice 8): a floating-point ' + ('parameter' if 'parameter' in last else 'result')
    if 'outside the System V INTEGER register class' in last:
        return 'refused (slice 8): an aggregate outside the INTEGER class: ' + norm(last.split('class: ')[-1])[:60]
    if 'more than six argument registers' in last:
        return 'refused (slice 8): parameters in more than six registers'
    if 'mismatch' in last:
        return 'MISMATCH: ' + norm(last)[:120]
    return norm(last)[:150]


rb, rn = roots(base), roots(new)
tb, tn = traces(base), traces(new)
promoted = sorted(rb - rn)
newly = sorted(rn - rb)
open(f'{out}/promoted.txt', 'w').write(''.join(s + '\n' for s in promoted))
open(f'{out}/newly_failing.txt', 'w').write(''.join(s + '\n' for s in newly))
print(f'baseline failed roots {len(rb)}, new {len(rn)}; promoted {len(promoted)}, '
      f'newly failing {len(newly)}')
print('promoted by baseline class:')
for k, v in collections.Counter(klass(tb[s]) if tb.get(s) else '(no trace)' for s in promoted).most_common():
    print(f'  {v:5d} {k}')
print('newly failing by new class:')
for k, v in collections.Counter(klass(tn[s]) if tn.get(s) else '(no trace)' for s in newly).most_common():
    print(f'  {v:5d} {k}')
fns = sorted(set(tb) | set(tn))
cb = collections.Counter(klass(tb[f]) for f in fns if tb.get(f))
cn = collections.Counter(klass(tn[f]) for f in fns if tn.get(f))
print(f'traced functions: baseline {sum(cb.values())}, new {sum(cn.values())}')
rows = sorted(set(cb) | set(cn), key=lambda k: -(cb.get(k, 0) + cn.get(k, 0)))
with open(f'{out}/body_trace_classes.tsv', 'w') as f:
    f.write('class\tbaseline\tslice8\n')
    for k in rows:
        f.write(f'{k}\t{cb.get(k, 0)}\t{cn.get(k, 0)}\n')
for k in rows[:50]:
    print(f'  {cb.get(k, 0):5d} {cn.get(k, 0):5d}  {k}')
# Where the baseline's slice-8 classes went.
moved = collections.Counter()
for f in fns:
    if not tb.get(f) or not tn.get(f):
        continue
    before = klass(tb[f])
    if any(t in before for t in ('non-scalar parameter', 'non-scalar result', 'no scalar type',
                                 'inconsistent sidecar type hint')):
        moved[(before, klass(tn[f]))] += 1
print('baseline slice-8 classes, by new class:')
for (b, a), v in moved.most_common(60):
    print(f'  {v:5d} {b[:50]} -> {a}')
with open(f'{out}/slice8_transitions.tsv', 'w') as f:
    f.write('baseline\tslice8\tcount\n')
    for (b, a), v in moved.most_common():
        f.write(f'{b}\t{a}\t{v}\n')
# Every function that replayed Valid on the baseline must still (no regression).
lost = [f for f in fns if tb.get(f) and tn.get(f) and klass(tb[f]) == 'bound, replays Valid'
        and klass(tn[f]) != 'bound, replays Valid']
print(f'functions Valid on the baseline and not now: {len(lost)}')
for f in lost[:20]:
    print('   ', f, '->', klass(tn[f]))
mismatches = [(f, l) for f in fns for l in tn.get(f, []) if 'mismatch' in l]
print(f'named mismatches in the new run: {len(mismatches)}')
for f, l in mismatches[:20]:
    print('   ', f, l[:200])
refuted = [f for f in fns if tn.get(f) and klass(tn[f]) == 'bound, REFUTED']
print(f'bound bodies refuted in the new run: {len(refuted)}')
for f in refuted[:20]:
    print('   ', f)
