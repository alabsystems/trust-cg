#!/usr/bin/env python3
"""Compare two Darwin core census runs (baseline, slice 7): failed roots,
promoted and newly failing lists, and the body-trace class of every traced
function on each side (its bound verdict if it has one, else its last refusal).

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
    if 'sret-arg callee' in last:
        return 'refused: an sret-arg callee (frame metadata)'
    if 'uses a private stack address as a value' in last:
        op = re.search(r'instruction \d+ \((\w+)', last)
        return f'refused: a private stack address escaping ({op.group(1) if op else "?"})'
    if 'may derive from an escaped private stack slot' in last:
        return 'refused: an access through an escape-derived address (slice 7)'
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
    f.write('class\tbaseline\tslice7\n')
    for k in rows:
        f.write(f'{k}\t{cb.get(k, 0)}\t{cn.get(k, 0)}\n')
for k in rows[:45]:
    print(f'  {cb.get(k, 0):5d} {cn.get(k, 0):5d}  {k}')
# Where the baseline's sret / escape functions went.
moved = collections.Counter()
for f in fns:
    if not tb.get(f) or not tn.get(f):
        continue
    before = klass(tb[f])
    if before.startswith('refused: an sret-arg') or before.startswith('refused: a private stack address escaping (Call'):
        moved[(before[:45], klass(tn[f]))] += 1
print('baseline sret / call-escape functions, by new class:')
for (b, a), v in moved.most_common(40):
    print(f'  {v:5d} {b} -> {a}')
# Every function that replayed Valid on the baseline must still (no regression).
lost = [f for f in fns if tb.get(f) and tn.get(f) and klass(tb[f]) == 'bound, replays Valid'
        and klass(tn[f]) != 'bound, replays Valid']
print(f'functions Valid on the baseline and not now: {len(lost)}')
for f in lost[:20]:
    print('   ', f, '->', klass(tn[f]))
