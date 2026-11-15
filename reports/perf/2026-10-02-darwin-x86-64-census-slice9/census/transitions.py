#!/usr/bin/env python3
"""Where the functions whose last body trace on the baseline matches a
pattern went in the new census: the new trace class of each (the bound
verdict, or the refusal with its numbers kept).

usage: transitions.py <baseline census dir> <new census dir> <regex>
"""
import collections
import re
import sys

PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')


def traces(d):
    out = {}
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = PAT.match(line.rstrip('\n'))
        if m:
            out[m.group(1)] = m.group(2)
    return out


def short(rest):
    rest = re.sub(r'^bound rows=\d+ ', 'bound ', rest)
    return rest[:150]


base, new, pattern = sys.argv[1], sys.argv[2], re.compile(sys.argv[3])
b, n = traces(base), traces(new)
moved = collections.Counter()
for name, rest in b.items():
    if pattern.search(rest):
        moved[short(n.get(name, '(no trace)'))] += 1
for rest, count in moved.most_common():
    print(f'{count:5}  {rest}')
