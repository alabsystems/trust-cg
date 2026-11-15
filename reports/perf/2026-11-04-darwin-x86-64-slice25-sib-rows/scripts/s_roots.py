#!/usr/bin/env python3
"""The S roots of a Darwin core census as the roots JSONL o0_sib_sites.py reads:
one {"symbol", "fn", "cls": "S"} per failed root whose named function's last
[TCG-X86-BODY-TRACE] line is the stack-slot scan's refusal.

usage: s_roots.py <census dir> > s_roots.jsonl
"""
import json
import re
import sys

run = sys.argv[1]
PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
FN_IN_MSG = re.compile(r'non_verified proof entry \S+ in (\S+?): ')
S_PREFIX = 'a row that references a stack slot outside a modelled `[slot + disp]` operand'
last = {}
for line in open(f'{run}/stderr.log', errors='replace'):
    m = PAT.match(line.rstrip('\n'))
    if m:
        last[m.group(1)] = m.group(2)
for line in open(f'{run}/failed_roots.jsonl'):
    if not line.strip():
        continue
    r = json.loads(line)
    m = FN_IN_MSG.search(r.get('message', ''))
    fn = m.group(1) if m else None
    if fn is not None and S_PREFIX in last.get(fn, ''):
        print(json.dumps({'symbol': r['symbol'], 'fn': fn, 'cls': 'S'}))
