#!/usr/bin/env python3
"""Aggregate a TRUST_CG_TIME_PASSES=1 log of one CLI compile: total wall per
pipeline phase, adapter stage, opt pass (with run counts) and regalloc stage.
Usage: passagg.py LOG [TOP] [FUNC_REGEX]. Measurement only."""
import collections, re, sys
txt = open(sys.argv[1]).read().splitlines()
top = int(sys.argv[2]) if len(sys.argv) > 2 else 40
func_re = sys.argv[3] if len(sys.argv) > 3 else None
P = collections.Counter(); N = collections.Counter(); R = collections.Counter(); PH = collections.Counter(); A = collections.Counter()
for l in txt:
    if func_re and not re.search(func_re, l):
        continue
    m = re.search(r"elapsed_us=(\d+)", l)
    if not m: continue
    us = int(m.group(1))
    if l.startswith("[trust-cg-time-pass] end"):
        p = re.search(r" pass=(\S+)", l).group(1); P[p] += us; N[p] += 1
    elif l.startswith("[trust-cg-time-regalloc]"):
        p = re.search(r" pass=(\S+) stage=(\S+)", l); R[p.group(1)+":"+p.group(2)] += us
    elif l.startswith("[trust-cg-time-pipeline] end"):
        p = re.search(r" phase=(\S+)", l).group(1); PH[p] += us
    elif l.startswith("[trust-cg-time-adapter]"):
        p = re.search(r" stage=(\S+)", l).group(1); A[p] += us
print("== pipeline phases (ms)")
for k, v in PH.most_common(): print(f"{v/1000:9.1f}  {k}")
print("== adapter (ms)")
for k, v in A.most_common(): print(f"{v/1000:9.1f}  {k}")
print(f"== opt passes (ms) total={sum(P.values())/1000:.1f}")
for k, v in P.most_common(top): print(f"{v/1000:9.1f}  {N[k]:5d}  {k}")
print(f"== regalloc stages (ms)")
for k, v in R.most_common(top): print(f"{v/1000:9.1f}  {k}")
