#!/usr/bin/env python3
"""Spelling experiment: a half of a concatenation of two 64-bit names is that
name (`((_ extract 63 0) (concat X Y))` -> `Y`, `((_ extract 127 64) (concat X Y))`
-> `X`), for every query of IN listed in a replay TSV with a given outcome.
usage: variants3.py <in dir> <replay.tsv> <outcome> <out dir>"""
import os
import re
import sys

src, tsv, outcome, out = sys.argv[1:5]
os.makedirs(out, exist_ok=True)
NAME = r"([a-z_]+\d*|e_[a-z0-9]+)"
for line in open(tsv):
    name, kind = line.split("\t")[:2]
    if kind != outcome:
        continue
    q = open(os.path.join(src, name)).read()
    q = re.sub(r"\(\(_ extract 63 0\) \(concat " + NAME + " " + NAME + r"\)\)", r"\2", q)
    q = re.sub(r"\(\(_ extract 127 64\) \(concat " + NAME + " " + NAME + r"\)\)", r"\1", q)
    open(os.path.join(out, name), "w").write(q)
