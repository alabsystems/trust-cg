#!/usr/bin/env python3
"""The O3 counts of the slice-24c design §7 (M2's trigger): how often a
census stops at one of the three refusals a routeless-edge claim (OD-228
part (c), not built) would be for:

- `continues to LIR blocks` (the machine block's successors are not its LIR
  block's, or not the segment's exits: N7);
- `has no route` (the walk finds no machine route for a LIR edge);
- `has no row attributed` (a machine block no stamp names).

Each count is given three ways: failed roots whose named function's LAST
[TCG-X86-BODY-TRACE] line holds the text (its first refusal, as the design
§2.8 measured O2), functions whose last line holds it, and trace lines that
hold it (every attempt). No O3 baseline exists, so nothing else of the O3
census is attributed here; the named mismatches and refuted bodies are
printed for the stop rule only.

usage: o3_counts.py <census dir>
"""
import collections
import json
import re
import sys

run = sys.argv[1]
PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
FN_IN_MSG = re.compile(r'non_verified proof entry \S+ in (\S+?): ')
KEYS = ['continues to LIR blocks', 'has no route', 'has no row attributed']

by_fn = collections.defaultdict(list)
for line in open(f'{run}/stderr.log', errors='replace'):
    m = PAT.match(line.rstrip('\n'))
    if m:
        by_fn[m.group(1)].append(m.group(2))
root_fns = []
for line in open(f'{run}/failed_roots.jsonl'):
    if line.strip():
        m = FN_IN_MSG.search(json.loads(line).get('message', ''))
        root_fns.append(m.group(1) if m else None)

for key in KEYS:
    roots = sum(1 for fn in root_fns if fn in by_fn and key in by_fn[fn][-1])
    fns = sum(1 for ls in by_fn.values() if key in ls[-1])
    lines = sum(1 for ls in by_fn.values() for l in ls if key in l)
    print(f'`{key}`: failed roots at first refusal {roots}; functions (last line) {fns}; trace lines {lines}')
mism = sorted({fn for fn, ls in by_fn.items() for l in ls if 'mismatch' in l})
refuted = [(fn, l) for fn, ls in by_fn.items() for l in ls if 'Invalid' in l]
print(f'stop rule: named mismatches (functions) {len(mism)}; refuted bodies (trace lines) {len(refuted)}')
for fn in mism:
    print(f'  MISMATCH {fn}: {[l for l in by_fn[fn] if "mismatch" in l][0][:400]}')
for fn, l in refuted:
    print(f'  REFUTED {fn} {l[:200]}')
