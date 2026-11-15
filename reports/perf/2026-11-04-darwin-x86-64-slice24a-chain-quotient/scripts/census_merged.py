#!/usr/bin/env python3
"""Attribute a slice-24a census to the merged-chain quotient: every function
whose body trace prints `merged chains=K absorbed=N`, its last trace line
(the verdict), against its last trace line in the baseline census, and how
many of the census's failed roots name such a function.

usage: census_merged.py <baseline dir> <slice-24a dir>  (prints the summary)
"""
import collections
import json
import re
import sys

base, new = sys.argv[1:3]
PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')


def traces(d):
    by_fn = collections.defaultdict(list)
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = PAT.match(line.rstrip('\n'))
        if m and 'negative-memo hit' not in m.group(2):
            by_fn[m.group(1)].append(m.group(2))
    return by_fn


def verdict(lines):
    last = lines[-1]
    if last.startswith('bound rows='):
        return 'bound, replays Valid' if 'replay=Valid' in last else (
            'bound, REFUTED' if 'Invalid' in last else 'bound, no independently checked proof')
    if 'mismatch' in last:
        return 'MISMATCH'
    if 'not contracted: ' in last:
        why = last.split('not contracted: ', 1)[1]
        why = re.sub(r' \(over the merged-chain quotient: .*\)$', '', why)
        why = re.sub(r'Block\(\d+\)', 'Block(N)', why)
        why = re.sub(r'(instruction|row) \d+', r'\1 N', why)
        why = re.sub(r'\d+ parameter', 'K parameter', why)
        why = re.sub(r'\[[^\]]*\]', '[..]', why)
        return 'not contracted: ' + why[:140]
    if 'over the merged-chain quotient' in last:
        text = last.replace('unsupported source-bound x86-64 body: ', '')
        text = re.sub(r' \(over the merged-chain quotient: .*\)$', '', text)
        text = re.sub(r'Block\(\d+\)', 'Block(N)', text)
        text = re.sub(r'(instruction|row) \d+', r'\1 N', text)
        text = re.sub(r'\[[^\]]*\]', '[..]', text)
        return 'refused over the quotient: ' + text[:140]
    if 'not contracted: ' in last:
        why = last.split('not contracted: ', 1)[1]
        why = re.sub(r'Block\(\d+\)', 'Block(N)', why)
        why = re.sub(r'(instruction|row) \d+', r'\1 N', why)
        why = re.sub(r'\d+ parameter', 'K parameter', why)
        return 'not contracted: ' + why[:140]
    return 'refused: ' + re.sub(r'Block\(\d+\)', 'Block(N)', last)[:140]


def roots(d):
    found = collections.Counter()
    for line in open(f'{d}/failed_roots.jsonl'):
        line = line.strip()
        if not line:
            continue
        m = re.search(r'non_verified proof entry \S+ in (\S+?): ', json.loads(line).get('message', ''))
        if m:
            found[m.group(1)] += 1
    return found


bt, nt = traces(base), traces(new)
merged = {fn: ls for fn, ls in nt.items() if any(' merged chains=' in f' {l}' or l.startswith('merged chains=') for l in ls)}
print(f'functions stated over a quotient (a merged chains= line): {len(merged)}')
outcome = collections.Counter(verdict(ls) for ls in merged.values())
for key, n in outcome.most_common():
    print(f'  {n:5d}  {key}')
moved = collections.Counter()
for fn, ls in merged.items():
    b = verdict(bt[fn]) if fn in bt else '(untraced)'
    moved[(b[:100], verdict(ls)[:60])] += 1
print('baseline verdict -> verdict over the quotient:')
for (b, n), k in moved.most_common(25):
    print(f'  {k:5d}  {b} -> {n}')
declined = collections.Counter(verdict(ls) for fn, ls in nt.items()
                               if fn not in merged and 'not contracted: ' in ls[-1])
print(f'functions whose merged block was not contracted (named decline): {sum(declined.values())}')
for key, n in declined.most_common(15):
    print(f'  {n:5d}  {key}')
r = roots(new)
print(f'failed roots naming a function stated over a quotient: {sum(n for fn, n in r.items() if fn in merged)}')
print(f'failed roots naming a function with a named decline: {sum(n for fn, n in r.items() if fn in nt and fn not in merged and "not contracted: " in nt[fn][-1])}')
