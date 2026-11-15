#!/usr/bin/env python3
"""Encoding experiment (evidence only): respell every aligned 8-byte run of
call-defined bytes `(concat dCsXo(8k+7) (... dCsXo(8k)))` as one 64-bit free
input `dCsXw{k}`, in queries where every use of those bytes is such a run
(else the query is skipped: its bytes and words would be unrelated inputs).

usage: word_respell.py <in dir> <out dir>
"""
import os, re, sys

src, dst = sys.argv[1], sys.argv[2]
os.makedirs(dst, exist_ok=True)
DECL = re.compile(r'^\(declare-const (d\d+s\d+o\d+) \(_ BitVec 8\)\)$', re.M)
done = skipped = 0
for name in sorted(os.listdir(src)):
    if not name.endswith('.smt2'):
        continue
    text = open(os.path.join(src, name)).read()
    groups = {}
    def run(m):
        site, slot, k = m.group(1), m.group(2), int(m.group(3)) // 8
        return f'd{site}s{slot}w{k}'
    # A run: (concat dXsYo(b+7) (concat ... (concat dXsYo(b+1) dXsYo(b)))...)
    pattern = re.compile(
        r'\(concat d(\d+)s(\d+)o(\d+) ' + r'\(concat d\1s\2o\d+ ' * 6 + r'd\1s\2o\d+\){7}')
    words = set()
    def replace(m):
        site, slot, top = m.group(1), m.group(2), int(m.group(3))
        expected = ' '.join(f'd{site}s{slot}o{top - i}' for i in range(8))
        found = ' '.join(re.findall(r'd\d+s\d+o\d+', m.group(0)))
        if top % 8 != 7 or found != expected or m.group(0).count(')') != 7:
            return m.group(0)
        w = f'd{site}s{slot}w{top // 8}'
        words.add(w)
        return w
    out = pattern.sub(replace, text)
    leftover = set(re.findall(r'd\d+s\d+o\d+', re.sub(DECL, '', out)))
    if not words or leftover:
        skipped += 1
        continue
    out = re.sub(DECL, '', out)
    decls = ''.join(f'(declare-const {w} (_ BitVec 64))\n' for w in sorted(words))
    out = out.replace('(set-logic QF_BV)\n', '(set-logic QF_BV)\n' + decls, 1)
    out = re.sub(r'\n\n+', '\n', out)
    open(os.path.join(dst, name), 'w').write(out)
    done += 1
print(f'respelled {done}, skipped {skipped}')
