#!/usr/bin/env python3
"""Group the failed roots of a census by the slice-10 instruction classes of the
function each names (its last body trace). Usage: classes.py <roots.tsv> [class]
Prints the class table, or with a class name the functions of that class (base
names, the `__trust_cg_private.<cgu>.<n>.` prefix stripped)."""
import collections
import re
import sys

RULES = [
    ("(CheckedUadd)", "checked:Uadd"), ("(CheckedUsub)", "checked:Usub"),
    ("(CheckedUmul)", "checked:Umul"), ("(CheckedSadd)", "checked:Sadd"),
    ("(CheckedSsub)", "checked:Ssub"), ("(CheckedSmul)", "checked:Smul"),
    ("escapes", "slot escape"), ("non-scalar type", "non-scalar load/extend"),
    ("(CallIndirect", "CallIndirect"), ("(Bnot", "Bnot"), ("(CtPop", "CtPop"),
    ("(Atomic", "atomics"), ("(GuardBoundsCheck", "guard:bounds"),
    ("(GuardDivZero", "guard:divzero"), ("(Guard", "guard:other"),
    ("shifts by a non-constant", "variable shift"),
    ("(Udiv", "div:Udiv"), ("(Urem", "div:Urem"), ("(Sdiv", "div:Sdiv"), ("(Srem", "div:Srem"),
    ("no value observable", "no observable"),
]


def classify(trace):
    for key, name in RULES:
        if key in trace:
            return name
    return None


def base(fn):
    m = re.match(r"__trust_cg_private\.[^.]+\.[^.]+\.\d+\.\d+\.(.*)", fn)
    return m.group(1) if m else fn


def main():
    rows = [line.rstrip("\n").split("\t", 2) for line in open(sys.argv[1])]
    if len(sys.argv) > 2:
        want = sys.argv[2]
        for fn, n, trace in rows:
            cls = classify(trace) or ""
            if cls == want or (want.endswith(":") and cls.startswith(want)):
                print(base(fn))
        return
    count = collections.Counter()
    for fn, n, trace in rows:
        count[classify(trace) or "(other)"] += int(n)
    for name, n in sorted(count.items(), key=lambda kv: -kv[1]):
        print(f"{n:5d}  {name}")


if __name__ == "__main__":
    main()
