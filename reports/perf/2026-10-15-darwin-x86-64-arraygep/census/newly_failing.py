#!/usr/bin/env python3
"""The functions a baseline census's body trace credits (`replay=Valid`) and a
later census's does not, with the later verdict: the 476 of census-s14 (342
failed roots) against census-main-2854ce (813).

usage: newly_failing.py <baseline census dir> <later census dir> <out.tsv>
"""
import re, sys

def traces(path):
    found = {}
    for line in open(path, errors='replace'):
        m = re.match(r'.*\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)', line.rstrip('\n'))
        if m:
            found[m.group(1)] = m.group(2)
    return found

before = traces(f'{sys.argv[1]}/stderr.log')
after = traces(f'{sys.argv[2]}/stderr.log')
newly = sorted(f for f, v in after.items()
               if 'replay=Valid' not in v and 'replay=Valid' in before.get(f, ''))
with open(sys.argv[3], 'w') as out:
    for f in newly:
        out.write(f'{f}\t{after[f][:300]}\n')
print(len(newly))
