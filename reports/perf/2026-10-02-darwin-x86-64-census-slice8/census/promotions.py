#!/usr/bin/env python3
"""Where a census row's promoted roots came from, and what its newly bound
bodies are.

1. Every promoted root, attributed to the function its baseline failure
   names (`non_verified proof entry ... in <fn>:`; a private copy's trace is
   under its `__trust_cg_private.<cgu>.<n>.` name): that function's class
   on the baseline -> on the new run.
2. Every function bound on both runs whose replay verdict changed, with the
   AY outcome line the baseline printed before it.
3. Newly bound bodies (bound now, traced but not bound on the baseline): by
   verdict, with bound-row medians, and the AY outcome before each one that
   does not certify.

usage: promotions.py <baseline census dir> <new census dir>
"""
import collections
import json
import re
import statistics
import sys

base, new = sys.argv[1:3]
TRACE = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
BOUND = re.compile(r'^bound rows=(\d+) replay=(\S+)')
NAMED = re.compile(r'proof entry \S+ in (\S+?):')


def scan(d):
    """Per function: its trace lines, and its last bound verdict with the AY
    outcome line printed just before it."""
    lines = collections.defaultdict(list)
    bound = {}
    prev = ''
    for line in open(f'{d}/stderr.log', errors='replace'):
        line = line.rstrip('\n')
        if line.startswith('[TCG-X86-BODY-TRACE] replay outcome='):
            prev = re.sub(r'path=\S+', 'path=P', line)[:120]
            continue
        m = TRACE.match(line)
        if not m:
            continue
        lines[m.group(1)].append(m.group(2))
        b = BOUND.match(m.group(2))
        if b:
            bound[m.group(1)] = (int(b.group(1)), b.group(2), prev)
        prev = ''
    return lines, bound


def records(d):
    return {json.loads(l)['symbol']: json.loads(l) for l in open(f'{d}/failed_roots.jsonl') if l.strip()}


def klass(lines):
    if not lines:
        return '(no trace)'
    bound = [l for l in lines if l.startswith('bound rows=')]
    if bound:
        return 'bound, Valid' if 'replay=Valid' in bound[-1] else 'bound, ' + bound[-1].split('replay=')[-1][:40]
    last = lines[-1]
    for key, name in (
        ('at most six register parameters', 'more than six parameters'),
        ('register parameters', 'non-scalar parameter'),
        ('I32 or I64 results', 'non-scalar result'),
        ('has no scalar result type', 'call result with no scalar type'),
        ('inconsistent type hint', 'inconsistent type hint'),
    ):
        if key in last:
            return 'refused: ' + name
    return 'other: ' + re.sub(r'\d+', 'N', last)[:90]


tb, bb = scan(base)
tn, bn = scan(new)
rb, rn = records(base), records(new)

print('1. promoted roots by the function their baseline failure names: baseline class -> new class')
attribution = collections.Counter()
for root in sorted(set(rb) - set(rn)):
    m = NAMED.search(rb[root]['message'])
    named = m.group(1) if m else root
    attribution[(klass(tb.get(named)), klass(tn.get(named)))] += 1
for (b, n), v in attribution.most_common():
    print(f'  {v:4d}  {b} -> {n}')
print(f'  total {sum(attribution.values())}')

print('2. functions bound on both runs whose replay verdict changed')
both = set(bb) & set(bn)
flips = collections.Counter()
for f in sorted(both):
    if bb[f][1] != bn[f][1]:
        same = 'same rows' if bb[f][0] == bn[f][0] else 'different rows'
        flips[(bb[f][1], bn[f][1], same, re.sub(r'\d+', 'N', bb[f][2]))] += 1
        print(f'    {f[:110]}')
print(f'  bound on both: {len(both)}')
for (vb, vn, same, outcome), v in flips.most_common():
    print(f'  {v:4d}  {vb} -> {vn} ({same}); baseline outcome: {outcome}')

print('3. newly bound bodies (traced on both runs, bound only on the new one)')
fresh = {f: v for f, v in bn.items() if f not in bb and f in tb}
by = collections.defaultdict(list)
outcome = collections.Counter()
for rows, verdict, prev in fresh.values():
    by[verdict].append(rows)
    if verdict != 'Valid':
        outcome[prev or '(no outcome line)'] += 1
print(f'  newly bound: {len(fresh)}')
for verdict, rows in sorted(by.items()):
    print(f'  {verdict}: {len(rows)} bodies, bound rows median {statistics.median(rows)}, max {max(rows)}')
for k, v in outcome.most_common():
    print(f'  {v:4d}  {k}')
