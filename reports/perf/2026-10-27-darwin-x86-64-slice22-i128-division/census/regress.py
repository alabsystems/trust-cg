#!/usr/bin/env python3
"""Whole-core regression set: every function whose probe theorem bytes change between two
run_probe_all.sh outputs, with its census-s21 outcome (the last [TCG-X86-BODY-TRACE] line);
the new queries of each census-certified one copied to <out>/q with an index.tsv, for
measure.py. usage: regress.py <base dir> <new dir> <out dir>"""
import os, re, shutil, sys
CENSUS = os.path.expanduser("~/tcg-scratch/runs/census-s21/stderr.log")
def idx(d):
    out = {}
    for l in open(f"{d}/smt2/index.tsv"):
        r = l.rstrip("\n").split("\t")
        out[r[1]] = (r[0], int(r[2]) if len(r) == 3 else 0)
    return out
def files(d, h, n):
    return [f"{h}.part{k}.smt2" for k in range(1, n + 1)] if n else [f"{h}.smt2"]
last = {}
pat = re.compile(r"\[TCG-X86-BODY-TRACE\] fn=(\S+) bound rows=\d+ replay=(.*)")
for line in open(CENSUS, errors="replace"):
    m = pat.match(line.rstrip())
    if m:
        last[m.group(1)] = m.group(2)
base, new, out = sys.argv[1:4]
b, n = idx(base), idx(new)
os.makedirs(f"{out}/q", exist_ok=True)
index = open(f"{out}/q/index.tsv", "w")
valid = other = 0
for fn in sorted(set(b) & set(n)):
    tb = [open(f"{base}/smt2/{q}").read() for q in files(base, *b[fn])]
    tn = [open(f"{new}/smt2/{q}").read() for q in files(new, *n[fn])]
    if tb == tn:
        continue
    outcome = last.get(fn, "not traced")
    print(f"{'Valid' if outcome.startswith('Valid') else outcome[:60]:60s} {fn.split('4core')[-1][:90]}")
    if outcome.startswith("Valid"):
        valid += 1
        h, k = n[fn]
        for q in files(new, h, k):
            shutil.copyfile(f"{new}/smt2/{q}", f"{out}/q/{q}")
        index.write(f"{h}\t{fn}" + (f"\t{k}" if k else "") + "\n")
    else:
        other += 1
print(f"changed: {valid} census-certified (queries written), {other} other")
