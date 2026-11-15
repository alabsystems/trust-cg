#!/usr/bin/env python3
"""Slice 17: the select and update chains of a directory of queries.

A chain is a maximal `(ite (= o (_ bvK 64)) A (ite (= o (_ bvK' 64)) B ...))`
nest over one offset term `o` (the spelling of `indexed::select` and
`indexed::update`); its arm count is its conditions plus the final else. Prints
one row per query (`file  chains  max_arms  arms...`) and a summary.

usage: select_arms.py <smt2 dir>
"""
import os
import sys


def parse(text):
    stack, cur, tok = [], [], ''
    for ch in text:
        if ch == '(':
            if tok:
                cur.append(tok)
                tok = ''
            stack.append(cur)
            cur = []
        elif ch == ')':
            if tok:
                cur.append(tok)
                tok = ''
            done = cur
            cur = stack.pop()
            cur.append(done)
        elif ch.isspace():
            if tok:
                cur.append(tok)
                tok = ''
        else:
            tok += ch
    return cur


def offset_condition(term):
    """`(= o (_ bvK 64))` -> o (as a string key), else None."""
    if (isinstance(term, list) and len(term) == 3 and term[0] == '='
            and isinstance(term[2], list) and len(term[2]) == 3 and term[2][0] == '_'
            and term[2][2] == '64' and str(term[2][1]).startswith('bv')):
        return repr(term[1])
    return None


def chains(term, out, inner=False):
    if not isinstance(term, list):
        return
    if term and term[0] == 'ite' and len(term) == 4:
        key = offset_condition(term[1])
        if key is not None and not inner:
            arms, node = 1, term
            while (isinstance(node, list) and node and node[0] == 'ite' and len(node) == 4
                   and offset_condition(node[1]) == key):
                arms += 1
                chains(node[2], out)
                node = node[3]
            out.append(arms)
            chains(node, out)
            return
    for child in term:
        chains(child, out)


rows = []
for name in sorted(os.listdir(sys.argv[1])):
    if not name.endswith('.smt2'):
        continue
    text = open(os.path.join(sys.argv[1], name)).read()
    found = []
    for form in parse(text):
        chains(form, found)
    rows.append((name, found))
    if found:
        print(f'{name}\t{len(found)}\t{max(found)}\t{",".join(map(str, sorted(found)))}')
every = [arms for _, found in rows for arms in found]
with_select = sum(1 for _, found in rows if found)
print(f'# queries {len(rows)}, with a chain {with_select}, chains {len(every)}, '
      f'max arms {max(every) if every else 0}')
if every:
    every.sort()
    print(f'# arms: median {every[len(every) // 2]}, p90 {every[int(len(every) * 0.9)]}')
