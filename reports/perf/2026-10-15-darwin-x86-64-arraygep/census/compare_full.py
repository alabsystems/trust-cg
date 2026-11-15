#!/usr/bin/env python3
"""Compare the probe's verdict on every function of the dump with census-s16's
body-trace verdict (slice 16 on main 2854ce3e3).

usage: compare_full.py <probe cf.tsv> <census stderr.log>
"""
import collections, re, sys
cf = sys.argv[1]
trace = {}
for l in open(sys.argv[2], errors='replace'):
    m = re.match(r'.*\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)', l.rstrip('\n'))
    if m: trace[m.group(1)] = m.group(2)
rows = {}
for l in open(cf):
    f = l.rstrip('\n').split('\t'); rows.setdefault(f[0], f[1])
def cls(s):
    if s.startswith('OWNER') and 'REFUTED' in s: return 'probe: REFUTED on samples'
    if s.startswith('OWNER'): return 'probe: theorem'
    s = re.sub(r'instruction \d+', 'instruction N', s); s = re.sub(r'Value\(\d+\)', 'Value(N)', s)
    s = re.sub(r'row \d+', 'row N', s); s = re.sub(r'\[def=.*', '', s)
    return 'probe: ' + s[:140]
def ccls(s):
    if s is None: return 'census: no trace'
    if 'replay=Valid' in s: return 'census: Valid'
    if s.startswith('bound rows'): return 'census: bound, not Valid'
    if 'ArrayGep' in s: return 'census: ArrayGep refusal'
    if 'type hint' in s: return 'census: type hint refusal'
    if 'mismatch' in s.lower(): return 'census: MISMATCH'
    return 'census: other refusal'
pairs = collections.Counter()
for name, v in rows.items():
    pairs[(ccls(trace.get(name)), cls(v))] += 1
for (c, p), n in sorted(pairs.items(), key=lambda kv: (kv[0][0], -kv[1])):
    print(f'{n:5}  {c:30} -> {p}')
print('functions in probe:', len(rows), ' in census-s16 traces:', len(trace))
