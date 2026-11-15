#!/usr/bin/env python3
"""Count a census's failed roots by the slice-13 class of the named function's
last body trace (the roots table `roots_by_class.py` writes: fn, roots,
trace), and write one class file per class (the same rows).

usage: split13.py <roots.tsv> <out dir>"""
import collections
import os
import sys

CLASSES = [
    ("uses a private stack address as a value", "a private address stored"),
    ("requires at most six register parameters", "more than six register parameters"),
    ("passes its parameters in more than six", "more than six register parameters"),
    ("passes more than six register arguments", "more than six register arguments"),
    ("(Memcpy)", "Memcpy/Memmove/Memset"),
    ("(Memset)", "Memcpy/Memmove/Memset"),
    ("(Memmove)", "Memcpy/Memmove/Memset"),
    ("(AtomicLoad", "an atomic access"),
    ("(AtomicStore", "an atomic access"),
    ("loads a bool from a private byte", "a bool read of another store's byte"),
    ("offsets a private stack address by a non-constant", "neighbour: a variable slot offset"),
    ("may derive from an escaped", "neighbour: an access through a maybe-escaped address"),
    ("B1 argument from a function that takes a B1", "neighbour: a forwarded bool argument"),
    ("a call or an incoming-memory access", "neighbour: no observable"),
    ("on which different private stack slots escaped", "a join of different escapes"),
]

rows, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
roots = collections.Counter()
functions = collections.Counter()
files = collections.defaultdict(list)
for line in open(rows):
    fn, n, trace = line.rstrip("\n").split("\t", 2)
    for needle, name in CLASSES:
        if needle in trace:
            roots[name] += int(n)
            functions[name] += 1
            files[name].append(line)
            break
for name, lines in files.items():
    slug = "".join(c if c.isalnum() else "_" for c in name)[:48]
    with open(os.path.join(out, f"cls_{slug}.tsv"), "w") as f:
        f.writelines(lines)
for name in dict.fromkeys(name for _, name in CLASSES):
    print(f"{name}\t{functions[name]}\t{roots[name]}")
