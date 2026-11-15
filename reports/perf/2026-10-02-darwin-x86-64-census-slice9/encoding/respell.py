#!/usr/bin/env python3
"""Respell dumped x86 body queries (evidence for the encoding choice, never
credit): every variant states the same theorem.

usage: respell.py <variant> <in dir> <out dir>

variants:
  split      the definitions and the negated goal as separate top-level
             asserts (the replay's `and_pos` retry spelling)
  goals      the negated goal's conjunction as a disjunction of negated
             claims, each its own top-level `(or ...)` under one assert
  flat       the premises' right-nested `and` as one n-ary `and`
"""
import os
import sys

sys.setrecursionlimit(1_000_000)
TOKEN_CHARS = '()'


def tokens(text):
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c in TOKEN_CHARS:
            out.append(c)
            i += 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in TOKEN_CHARS:
                j += 1
            out.append(text[i:j])
            i = j
    return out


def parse_all(text):
    toks = tokens(text)
    stack = [[]]
    for tok in toks:
        if tok == '(':
            stack.append([])
        elif tok == ')':
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(tok)
    return stack[0]


def show(e):
    out = []
    stack = [e]
    while stack:
        x = stack.pop()
        if isinstance(x, str):
            out.append(x)
        elif isinstance(x, list):
            out.append('(')
            stack.append(')')
            for item in reversed(x):
                stack.append(item)
                stack.append(' ')
            if x:
                stack.pop()
        else:
            out.append(x)
    text = ''.join(out)
    return text.replace('( ', '(').replace(' )', ')')


def conjuncts(e):
    out = []
    while isinstance(e, list) and len(e) == 3 and e[0] == 'and':
        out.append(e[1])
        e = e[2]
    out.append(e)
    return out


def respell(variant, script):
    commands = parse_all(script)
    out = []
    for cmd in commands:
        if isinstance(cmd, list) and cmd and cmd[0] == 'assert':
            body = cmd[1]
            parts = conjuncts(body)
            premises, goal = parts[:-1], parts[-1]
            if variant == 'split':
                out.extend(['assert', p] for p in premises)
                out.append(['assert', goal])
            elif variant == 'flat':
                out.append(['assert', ['and'] + premises + [goal]])
            elif variant == 'goals':
                # goal is (not (= true CONJ)); state it as (or (not k1) ...).
                inner = goal[1] if goal[0] == 'not' else goal
                conj = inner[2] if isinstance(inner, list) and inner[0] == '=' else inner
                claims = conjuncts(conj)
                negated = ['or'] + [['not', c] for c in claims] if len(claims) > 1 else ['not', claims[0]]
                out.extend(['assert', p] for p in premises)
                out.append(['assert', negated])
            else:
                raise SystemExit(f'unknown variant {variant}')
        else:
            out.append(cmd)
    return '\n'.join(show(c) for c in out) + '\n'


if __name__ == '__main__':
    variant, src, dst = sys.argv[1:4]
    os.makedirs(dst, exist_ok=True)
    for name in sorted(os.listdir(src)):
        if name.endswith('.smt2'):
            text = open(os.path.join(src, name)).read()
            open(os.path.join(dst, name), 'w').write(respell(variant, text))
    print('respelled', variant)
