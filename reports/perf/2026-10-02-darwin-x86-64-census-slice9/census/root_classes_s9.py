#!/usr/bin/env python3
"""Attribute each failed root of a Darwin x86-64 core census to the body-lane
class of the function its proof failure names: main's
`reports/perf/2026-09-27-darwin-x86-64-census/root_classes.py` rules, with
the slice-8 refusals (an i128 or floating-point value, an aggregate outside
the System V INTEGER class, parameters in more than six argument registers),
the more-than-six-parameters refusal and the slice-9 refusals (the slice-9
block and instruction bounds, a join of different escapes or root kinds, a
redefinition after a join) matched first, so the older rules do not misfile
them.

usage: root_classes_s9.py <census-out-dir> [<census-out-dir> ...]
"""
import collections
import json
import re
import sys

SLICE8 = [
    ("blocks (the lane admits 1 to 16)", ">16 blocks"),
    ("instructions (the lane admits at most 256)", "long path"),
    ("blocks (the lane admits 1 to", "more blocks than the slice-9 bound"),
    ("instructions (the lane admits at most", "more instructions than the slice-9 bound"),
    ("different private stack slots escaped", "join of different escapes (slice 9)"),
    ("different kinds of value", "root of different kinds at a join (slice 9)"),
    ("which a path into it already defined", "redefinition after a join (slice 9)"),
    ("correspond one to one", "no block correspondence"),
    ("has an i128", "i128 value (slice 8 refuses by name)"),
    ("floating-point or vector", "float value (slice 8 refuses by name)"),
    ("outside the System V INTEGER register class", "aggregate outside INTEGER (slice 8 refuses by name)"),
    ("more than six argument registers", ">6 argument registers (slice 8)"),
    # "requires at most six register parameters" (more than six LIR
    # parameters) would otherwise land under "non-scalar params".
    ("at most six", ">6 params"),
]
RULES = [
    ("register parameters", "non-scalar params"), ("I64 results", "non-scalar results"),
    ("blocks (the lane", ">16 blocks"), ("a path of", "long path"), ("a loop", "loop"),
    ("a call or an incoming-memory access", "no observable"), ("(Checked", "checked arith"),
    ("escapes", "slot address escapes"), ("at most six", ">6 params"), ("type hint", "inconsistent type hint"),
    ("CallIndirect", "CallIndirect"), ("non-scalar type", "non-scalar load/extend"),
    ("(Guard", "guards"), ("CtPop", "CtPop"), ("Bnot", "Bnot"), ("Atomic", "atomics"),
    ("shifts by a non-constant", "variable shift"), ("(Udiv", "div/rem"), ("(Urem", "div/rem"),
    ("(Sdiv", "div/rem"), ("(Srem", "div/rem"),
    ("(Call {", "call shapes"), ("Memcpy", "memcpy/memset"), ("Memset", "memcpy/memset"),
    ("more than", "machine >N rows"), ("mismatch", "MISMATCH"),
]


def cls(t):
    if "replay=Valid" in t:
        return "VALID(?)"
    if "replay=" in t or "bound rows" in t:
        return "bound, not certified (AY)"
    for k, v in SLICE8 + RULES:
        if k in t:
            return v
    return "other: " + re.sub(r"\d+", "N", t)[:110]


def classes(run):
    last = {}
    for line in open(f"{run}/stderr.log", errors="replace"):
        m = re.match(r"\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)", line.rstrip())
        if m:
            last[m.group(1)] = m.group(2)
    c = collections.Counter()
    for line in open(f"{run}/failed_roots.jsonl"):
        if not line.strip():
            continue
        r = json.loads(line)
        m = re.search(r"non_verified proof entry \S+ in (\S+?): ", r.get("message", ""))
        fn = m.group(1) if m else None
        c[cls(last[fn]) if fn in last else ("(named fn untraced)" if fn else "(no fn in message)")] += 1
    return c


runs = sys.argv[1:]
counts = [classes(run) for run in runs]
keys = sorted(set().union(*counts), key=lambda k: -sum(c.get(k, 0) for c in counts))
print("| Class of the named function | " + " | ".join(run.rstrip("/").split("/")[-1] for run in runs) + " |")
print("| --- |" + " ---: |" * len(runs))
for k in keys:
    print(f"| {k} | " + " | ".join(str(c.get(k, 0)) for c in counts) + " |")
print("| total | " + " | ".join(str(sum(c.values())) for c in counts) + " |")
