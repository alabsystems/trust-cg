#!/usr/bin/env python3
"""Respell dumped x86 body queries as the owner states an inlined DAG
theorem: substitute every definition used at most once into its use, drop
every claim equation that is then an identity `(= X X)` (true by definition;
a guarded claim `(or (not G) X)` keeps its guard over what is left of X and
goes when nothing is), and repeat to a fixpoint; declare only the names the
query still reads. Satisfiability-preserving, evidence for the encoding
choice, never credit.

usage: drop_identities.py <in dir> <out dir>
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


def rebuild(terms):
    if not terms:
        return None
    body = terms[-1]
    for t in reversed(terms[:-1]):
        body = ['and', t, body]
    return body


def identity(t):
    return isinstance(t, list) and len(t) == 3 and t[0] == '=' and t[1] == t[2]


def drop(conj):
    kept = []
    for claim in conjuncts(conj):
        if identity(claim):
            continue
        if (isinstance(claim, list) and len(claim) == 3 and claim[0] == 'or'
                and isinstance(claim[1], list) and claim[1][0] == 'not'):
            rest = rebuild([t for t in conjuncts(claim[2]) if not identity(t)])
            if rest is None:
                continue
            kept.append(['or', claim[1], rest])
        else:
            kept.append(claim)
    return rebuild(kept)


def respell(script):
    commands = parse_all(script)
    asserts = [c for c in commands if isinstance(c, list) and c and c[0] == 'assert']
    assert len(asserts) == 1
    parts = conjuncts(asserts[0][1])
    premises, goal = parts[:-1], parts[-1]
    defs = [(p[1], p[2]) for p in premises]
    # goal: (not (= true CONJ)); a one-item theorem `(not (= S M))` is left
    # as it is.
    if not (goal[0] == 'not' and goal[1][0] == '=' and goal[1][1] == 'true'):
        return script
    conj = goal[1][2]
    while True:
        counts = {}
        for _, expr in defs:
            count_uses(expr, counts)
        count_uses(conj, counts)
        env, kept = {}, []
        for name, expr in defs:
            expr = substitute(expr, env)
            if counts.get(name, 0) <= 1:
                env[name] = expr
            else:
                kept.append((name, expr))
        conj = substitute(conj, env)
        dropped = drop(conj)
        if dropped is None:
            return None
        changed = dropped != conj or len(kept) != len(defs)
        defs, conj = kept, dropped
        if not changed:
            break
    body = ['not', ['=', 'true', conj]]
    for name, expr in reversed(defs):
        body = ['and', ['=', name, expr], body]
    used = {}
    count_uses(body, used)
    out = []
    for c in commands:
        if isinstance(c, list) and c and c[0] == 'declare-const' and c[1] not in used:
            continue
        out.append(['assert', body] if isinstance(c, list) and c and c[0] == 'assert' else c)
    return '\n'.join(show(c) for c in out) + '\n'


src, dst = sys.argv[1], sys.argv[2]
os.makedirs(dst, exist_ok=True)
for name in sorted(os.listdir(src)):
    if name.endswith('.smt2'):
        text = respell(open(os.path.join(src, name)).read())
        if text is None:
            print(f'{name}\tno claim left')
            continue
        open(os.path.join(dst, name), 'w').write(text)
