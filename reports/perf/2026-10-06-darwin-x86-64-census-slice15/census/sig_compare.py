#!/usr/bin/env python3
"""Compare two probe --sig runs: functions bound before and after, newly bound,
lost, refuted at a sample, and the new verdicts of a class list.
usage: sig_compare.py <base.tsv> <new.tsv> [names file]"""
import collections, re, sys


def load(path):
    rows = {}
    for line in open(path, errors="replace"):
        parts = line.rstrip("\n").split("\t")
        if len(parts) >= 2:
            rows[parts[0]] = parts[1]
    return rows


base, new = load(sys.argv[1]), load(sys.argv[2])
bound = lambda v: v.startswith("OWNER")
print(f"functions: base {len(base)} new {len(new)}")
print(f"bound: base {sum(map(bound, base.values()))} new {sum(map(bound, new.values()))}")
gained = [n for n in new if bound(new[n]) and not bound(base.get(n, ""))]
lost = [n for n in base if bound(base[n]) and not bound(new.get(n, ""))]
refuted = [n for n in new if "REFUTED" in new[n]]
print(f"newly bound: {len(gained)}; lost: {len(lost)}; refuted at a sample: {len(refuted)}")
for n in lost:
    print("  LOST", n, "|", new.get(n, "?")[:200])
for n in refuted:
    print("  REFUTED", n, "|", new[n][:120], "| base:", base.get(n, "?")[:120])
why = collections.Counter(re.sub(r"\d+", "N", base.get(n, "?"))[:150] for n in gained)
print("newly bound, by the base refusal:")
for k, v in why.most_common():
    print(f"  {v:4d} {k}")
if len(sys.argv) > 3:
    names = {re.sub(r'^__trust_cg_private\.[^.]+\.[^.]+\.[0-9]+\.[0-9]+\.', '', l.strip())
             for l in open(sys.argv[3]) if l.strip()}
    print("class functions:")
    for n in sorted(names):
        print(f"  {n[:80]}\t{base.get(n, 'absent')[:70]}\t->\t{new.get(n, 'absent')[:110]}")
