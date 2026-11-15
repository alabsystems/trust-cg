#!/usr/bin/env python3
"""Split a census roots table (fn, roots, trace) into the slice-11 classes:
the i128 and floating-point parameter/result refusals, plus the neighbouring
non-scalar load/extend and call-result classes. Writes cls_<class>.txt in the
output directory (base name, roots, trace) and prints the counts.
usage: split_classes.py <roots.tsv> <out dir>"""
import collections
import os
import re
import sys

KEYS = [
    ("i128_param", "has an i128 parameter"),
    ("i128_result", "has an i128 result"),
    ("float_param", "has a floating-point or vector parameter"),
    ("float_result", "has a floating-point or vector result"),
    ("nonscalar_load", "non-scalar type"),
    ("call_result", "call result"),
]


def base(fn):
    m = re.match(r"__trust_cg_private\.[^.]+\.[^.]+\.\d+\.\d+\.(.*)", fn)
    return m.group(1) if m else fn


def main():
    rows = [line.rstrip("\n").split("\t", 2) for line in open(sys.argv[1])]
    out = sys.argv[2]
    classes = collections.defaultdict(list)
    for fn, n, trace in rows:
        for key, needle in KEYS:
            if needle in trace:
                classes[key].append((base(fn), int(n), trace))
                break
    for key, _ in KEYS:
        rows = classes[key]
        print(f"{key}\t{len(rows)} functions\t{sum(n for _, n, _ in rows)} roots")
        with open(os.path.join(out, f"cls_{key}.txt"), "w") as f:
            for fn, n, trace in rows:
                f.write(f"{fn}\t{n}\t{trace}\n")


if __name__ == "__main__":
    main()
