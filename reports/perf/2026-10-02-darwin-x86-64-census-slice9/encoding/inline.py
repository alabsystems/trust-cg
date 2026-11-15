#!/usr/bin/env python3
"""Respell dumped x86 body queries by substituting every definition used at
most once (and dropping one used never) into its one use, a
satisfiability-preserving presentation of the same theorem (evidence for the
encoding choice, never credit).

usage: inline.py <in dir> <out dir> [max uses]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from respell import conjuncts, parse_all, show  # noqa: E402

sys.setrecursionlimit(1_000_000)


def count_uses(e, counts):
    stack = [e]
    while stack:
        x = stack.pop()
        if isinstance(x, list):
            stack.extend(x)
        else:
            counts[x] = counts.get(x, 0) + 1


def substitute(e, env):
    if isinstance(e, str):
        return env.get(e, e)
    return [substitute(x, env) for x in e]


def inline(script, max_uses):
    commands = parse_all(script)
    asserts = [c for c in commands if isinstance(c, list) and c and c[0] == 'assert']
    assert len(asserts) == 1
    parts = conjuncts(asserts[0][1])
    premises, goal = parts[:-1], parts[-1]
    defs = []
    for p in premises:
        if isinstance(p, list) and len(p) == 3 and p[0] == '=' and isinstance(p[1], str):
            defs.append((p[1], p[2]))
        else:
            defs.append((None, p))
    counts = {}
    for name, expr in defs:
        count_uses(expr, counts)
    count_uses(goal, counts)
    inlined = {name for name, _ in defs if name and counts.get(name, 0) <= max_uses}
    env = {}
    kept = []
    for name, expr in defs:
        expr = substitute(expr, env)
        if name in inlined:
            env[name] = expr
        else:
            kept.append(['=', name, expr] if name else expr)
    goal = substitute(goal, env)
    body = goal
    for p in reversed(kept):
        body = ['and', p, body]
    out = []
    for c in commands:
        if isinstance(c, list) and c and c[0] == 'declare-const' and c[1] in inlined:
            continue
        if isinstance(c, list) and c and c[0] == 'assert':
            out.append(['assert', body])
        else:
            out.append(c)
    return '\n'.join(show(c) for c in out) + '\n', len(defs), len(kept)


src, dst = sys.argv[1], sys.argv[2]
max_uses = int(sys.argv[3]) if len(sys.argv) > 3 else 1
os.makedirs(dst, exist_ok=True)
for name in sorted(os.listdir(src)):
    if name.endswith('.smt2'):
        text, before, after = inline(open(os.path.join(src, name)).read(), max_uses)
        open(os.path.join(dst, name), 'w').write(text)
        print(f'{name}\t{before}\t{after}')
