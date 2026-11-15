#!/usr/bin/env python3
"""Write slice24_o0_owners.txt from a fails-before log's S24_O0 lines.
Usage: o0_record.py <fails-before log> <out file>"""
import sys
log, out = sys.argv[1:3]
lines = [l.rstrip('\n').split('\t', 1)[1] for l in open(log) if l.startswith('S24_O0\t')]
assert lines, 'no S24_O0 lines'
header = [
    '# Slice 24a (OD-226): the outcome of every slice 1-23 fixture with a shape list',
    '# (`o0_outcomes`) on the code before slice 24a (7ee0def54), recorded by the',
    '# fails-before run of reports/perf/2026-11-04-darwin-x86-64-slice24a-chain-quotient.',
    '# label <TAB> stated <TAB> SHA-256 of its replayed units, or',
    '# label <TAB> refused <TAB> SHA-256 of its refusal text before any "; not contracted: ".',
]
open(out, 'w').write('\n'.join(header + lines) + '\n')
print(len(lines), 'outcomes;', sum(1 for l in lines if '\tstated\t' in l), 'stated')
