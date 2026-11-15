#!/usr/bin/env python3
"""Group the slice-12 outcomes of the functions the baseline refused at a loop
(`census_compare.py`'s slice12_transitions.tsv) into the levers' classes.

usage: levers.py <compare dir>/slice12_transitions.tsv"""
import collections
import re
import sys

CLASSES = [
    ('bound, replays Valid', r'^bound, replays Valid'),
    ('bound, no independently checked proof', r'^bound, no independently'),
    ('a load or store through an address that may derive from an escaped slot (retention rule)',
     r'(loads|stores) through an address that may derive from an escaped'),
    ('a private slot offset by a non-constant amount', r'offsets a private stack address by a non-constant'),
    ('division (`GuardDivZero`, `Udiv`)', r'\((GuardDivZero|Udiv|Urem)'),
    ('more than 512 machine rows', r'more than \d+ rows'),
    ('more than 1024 LIR instructions', r'instructions \(the lane admits at most'),
    ('an `I128` loop-carried value', r'of type I128'),
    ('a header entered from two edges outside its loop', r'entered from \d+ edges outside'),
    ('a stored private address in a byte the loop changes', r'one of them a private stack'),
]
counts = collections.Counter()
other = collections.Counter()
for line in open(sys.argv[1]):
    name, cls, outcome = line.rstrip('\n').split('\t')[:3]
    if cls != 'loop':
        continue
    for label, pattern in CLASSES:
        if re.search(pattern, outcome):
            counts[label] += 1
            break
    else:
        other[outcome[:120]] += 1
total = sum(counts.values()) + sum(other.values())
print(f'| Slice-12 outcome | Functions |\n| --- | ---: |')
for label, _ in CLASSES:
    if counts[label]:
        print(f'| {label} | {counts[label]} |')
for outcome, n in other.most_common():
    print(f'| {outcome} | {n} |')
print(f'| **all** | **{total}** |')
