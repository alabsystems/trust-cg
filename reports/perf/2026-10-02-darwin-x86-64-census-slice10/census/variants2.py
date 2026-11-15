#!/usr/bin/env python3
"""Barrel-shifter spelling of the variable shifts: `x op (n mod w)` as log2(w)
stages, stage i shifting by 2^i (an extract/concat) when bit i of n is set.
usage: variants2.py <qdump dir> <out dir>"""
import os
import re
import sys

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)


def barrel(op, x, n, w):
    k = (w - 1).bit_length()
    term = x
    for i in range(k):
        s = 1 << i
        if op == "bvshl":
            shifted = f"(concat ((_ extract {w - 1 - s} 0) {term}) (_ bv0 {s}))"
        elif op == "bvlshr":
            shifted = f"(concat (_ bv0 {s}) ((_ extract {w - 1} {s}) {term}))"
        else:
            shifted = f"((_ sign_extend {s}) ((_ extract {w - 1} {s}) {term}))"
        term = f"(ite (= ((_ extract {i} {i}) {n}) #b1) {shifted} {term})"
    return term


def parse(text, i):
    """The balanced s-expression or atom starting at text[i]: (expr, end)."""
    if text[i] != "(":
        j = i
        while j < len(text) and text[j] not in " ()":
            j += 1
        return text[i:j], j
    depth = 0
    j = i
    while True:
        if text[j] == "(":
            depth += 1
        elif text[j] == ")":
            depth -= 1
            if depth == 0:
                return text[i:j + 1], j + 1
        j += 1


def rewrite(text, w):
    for op in ["bvshl", "bvlshr", "bvashr"]:
        start = 0
        while True:
            i = text.find(f"({op} ", start)
            if i == -1:
                break
            x, j = parse(text, i + len(op) + 2)
            amount, k = parse(text, j + 1)
            end = k + 1
            m = re.fullmatch(r"\(bvand (.*) \(_ bv%d (\d+)\)\)" % (w - 1), amount)
            if not m:
                start = end
                continue
            inner = m.group(1)
            cl = re.fullmatch(r"\(\(_ zero_extend \d+\) \(\(_ extract 7 0\) (.*)\)\)", inner)
            n = cl.group(1) if cl else inner
            replaced = barrel(op, x, n, w)
            text = text[:i] + replaced + text[end:]
            start = i + len(replaced)
    return text


for shape, w in [("ShrU64", 64), ("SarI32", 32), ("ShlChecked", 32), ("SarI16", 16), ("ShlU8", 8)]:
    q = open(os.path.join(src, shape + ".smt2")).read()
    text = rewrite(q, w)
    if w < 32:
        text = rewrite(text, 32)
    open(os.path.join(out, shape + "__barrel.smt2"), "w").write(text)
print(sorted(os.listdir(out)))
