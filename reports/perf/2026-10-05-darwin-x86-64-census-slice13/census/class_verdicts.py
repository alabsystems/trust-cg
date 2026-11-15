#!/usr/bin/env python3
"""Offline verdicts of the slice-13 classes: for each failed root of a census
(roots table: fn, roots, trace) whose trace names a slice-13 class, the
verdict the probe's `--sig` census of the same functions gives under the
owner it was built with (OWNER n = bound with n rows; REFUTED-AT-SAMPLE =
the theorem fails a sample; anything else is the refusal).

usage: class_verdicts.py <roots.tsv> <sig.tsv> [<sig-baseline.tsv>]"""
import collections
import re
import sys

CLASSES = [
    ("uses a private stack address as a value", "slot address stored"),
    ("register parameters", "parameters on the stack"),
    ("passes more than six register arguments", "arguments on the stack"),
    ("(Memcpy)", "memcpy/memset"),
    ("(Memset)", "memcpy/memset"),
    ("(Memmove)", "memcpy/memset"),
    ("(AtomicLoad", "atomics"),
    ("(AtomicStore", "atomics"),
    ("offsets a private stack address by a non-constant", "variable slot offset"),
    ("loads a bool from a private byte", "bool from another byte"),
    ("may derive from an escaped", "tainted access"),
    ("a call or an incoming-memory access", "no observable"),
    ("B1 argument from a function that takes a B1", "bool forwarded"),
]


def norm(text):
    text = re.sub(r"instruction \d+", "instruction N", text)
    text = re.sub(r"row \d+", "row N", text)
    text = re.sub(r"Block\(\d+\)", "Block(N)", text)
    text = re.sub(r"Value\(\d+\)", "Value(N)", text)
    text = re.sub(r"slot \d+ \+ \d+", "slot N + N", text)
    text = re.sub(r'name: "[^"]*"', 'name: _', text)
    text = re.sub(r"\{[^{}]*\}", "{..}", text)
    return text.replace("unsupported source-bound x86-64 body: ", "")[:150]


def load_sig(path):
    sig = {}
    for line in open(path):
        cols = line.rstrip("\n").split("\t")
        sig[cols[0]] = cols[1]
    return sig


roots = [line.rstrip("\n").split("\t", 2) for line in open(sys.argv[1])]
sig = load_sig(sys.argv[2])
base = load_sig(sys.argv[3]) if len(sys.argv) > 3 else {}
by_class = collections.defaultdict(collections.Counter)
for fn, n, trace in roots:
    cls = next((name for key, name in CLASSES if key in trace), None)
    if cls is None:
        continue
    verdict = sig.get(fn, "(absent from the module)")
    if verdict.startswith("OWNER"):
        verdict = "OWNER" + (" REFUTED-AT-SAMPLE" if "REFUTED" in verdict else "")
    else:
        verdict = norm(verdict)
    by_class[cls][verdict] += int(n)
    if base and fn in base and not base[fn].startswith("OWNER") and verdict == "OWNER":
        pass
for cls, verdicts in sorted(by_class.items()):
    print(f"{cls}: {sum(verdicts.values())} roots")
    for verdict, n in verdicts.most_common():
        print(f"    {n:4d}  {verdict}")
