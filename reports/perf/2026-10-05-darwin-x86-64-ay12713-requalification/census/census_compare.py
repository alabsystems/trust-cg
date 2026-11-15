#!/usr/bin/env python3
"""Compare two Darwin core census runs of the SAME trust-cg tree that differ only in the
replayer AY (baseline: AY build 10530; new: AY build 12713 from the overlay): failed roots,
promoted and newly failing lists with each named function's last body trace on both sides,
every named mismatch and refuted body, the verdict changes of functions bound on both
sides, and the replay outcomes of the bound bodies that do not replay Valid.

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


TRACE = re.compile(r'^\[TCG-X86-BODY-TRACE\] (.*)$')
FN = re.compile(r'^fn=(\S+) (.*)$')


def traces(d):
    """Each function's body-trace lines, with the `replay outcome=` line that precedes a
    non-Valid `bound` line attached to that function."""
    by_fn = collections.defaultdict(list)
    outcomes = collections.defaultdict(list)
    pending = None
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = TRACE.match(line.rstrip('\n'))
        if not m:
            continue
        text = m.group(1)
        if text.startswith('replay outcome='):
            pending = text[len('replay outcome='):]
            continue
        if text.startswith('replay negative-memo hit'):
            continue
        f = FN.match(text)
        if not f:
            continue
        fn, rest = f.groups()
        by_fn[fn].append(rest)
        if rest.startswith('bound rows=') and 'replay=Valid' not in rest and pending:
            outcomes[fn].append(pending)
        pending = None
    return by_fn, outcomes


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


def outcome_class(text):
    if text.startswith('Timeout'):
        return 'Timeout'
    m = re.search(r'reason-unknown \(?([a-z-]+(?: [a-z-]+)?)', text)
    if m:
        return 'Unknown ' + m.group(1)
    if 'unproved_steps' in text:
        return 'incomplete certificate'
    return text.split(' ')[0][:40]


base_roots, new_roots = roots(base), roots(new)
(base_traces, base_outcomes), (new_traces, new_outcomes) = traces(base), traces(new)
promoted = sorted(set(base_roots) - set(new_roots))
newly = sorted(set(new_roots) - set(base_roots))
lines = [
    f'baseline failed roots: {len(base_roots)}',
    f'new failed roots: {len(new_roots)}',
    f'promoted: {len(promoted)}',
    f'newly failing: {len(newly)}',
]
mismatches = [(fn, l) for fn, ls in new_traces.items() for l in ls if 'mismatch' in l]
refuted = [(fn, l) for fn, ls in new_traces.items() for l in ls if 'Invalid' in l]
lines.append(f'named mismatches (new): {len(mismatches)}')
lines.append(f'refuted bodies (new): {len(refuted)}')
for fn, l in mismatches + refuted:
    lines.append(f'  {fn} {l[:300]}')

attribution = collections.Counter()
for symbol in promoted:
    fn = base_roots[symbol]
    b = verdict(base_traces[fn]) if fn in base_traces else '(untraced)'
    n = verdict(new_traces[fn]) if fn in new_traces else '(untraced)'
    attribution[f'{b} -> {n}'] += 1
lines.append('promoted roots by the named function (baseline -> new):')
for key, n in attribution.most_common():
    lines.append(f'  {n:5d}  {key}')
newly_attr = collections.Counter()
for symbol in newly:
    fn = new_roots[symbol]
    b = verdict(base_traces[fn]) if fn in base_traces else '(untraced)'
    n = verdict(new_traces[fn]) if fn in new_traces else '(untraced)'
    outcome = outcome_class(new_outcomes[fn][-1]) if new_outcomes.get(fn) else '-'
    newly_attr[f'{b} -> {n} [{outcome}]'] += 1
    lines.append(f'NEWLY FAILING {symbol} named {fn}: base [{b}] new [{n}] outcome [{outcome}]')
lines.append('newly failing roots by the named function (baseline -> new [new replay outcome]):')
for key, n in newly_attr.most_common():
    lines.append(f'  {n:5d}  {key}')

changes = collections.Counter()
with open(f'{out}/bound_both_changes.tsv', 'w') as tsv:
    for fn in sorted(set(base_traces) & set(new_traces)):
        b, n = verdict(base_traces[fn]), verdict(new_traces[fn])
        if b.startswith('bound') and n.startswith('bound') and b != n:
            bo = outcome_class(base_outcomes[fn][-1]) if base_outcomes.get(fn) else '-'
            no = outcome_class(new_outcomes[fn][-1]) if new_outcomes.get(fn) else '-'
            changes[f'{b} [{bo}] -> {n} [{no}]'] += 1
            tsv.write(f'{fn}\t{b}\t{bo}\t{n}\t{no}\n')
lines.append('verdict changes of functions bound on both sides (with replay outcome classes):')
for key, n in changes.most_common():
    lines.append(f'  {n:5d}  {key}')
for name, outcomes in (('baseline', base_outcomes), ('new', new_outcomes)):
    counter = collections.Counter(outcome_class(v[-1]) for v in outcomes.values() if v)
    lines.append(f'{name}: last replay outcome of each bound, not-Valid function: {dict(counter.most_common())}')
for name, tr in (('baseline', base_traces), ('new', new_traces)):
    counter = collections.Counter(verdict(v) for v in tr.values())
    bound = {k: v for k, v in counter.items() if k.startswith('bound')}
    lines.append(f'{name}: traced functions {len(tr)}, bound {sum(bound.values())}: {bound}')

open(f'{out}/promoted.txt', 'w').write('\n'.join(promoted) + '\n')
open(f'{out}/newly_failing.txt', 'w').write('\n'.join(newly) + '\n')
open(f'{out}/compare.txt', 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
