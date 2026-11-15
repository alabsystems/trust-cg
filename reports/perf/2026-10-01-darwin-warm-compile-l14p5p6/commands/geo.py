#!/usr/bin/env python3
"""Geomean ratios against the LLVM -O2 lane of a warm_corpus.py result: wall,
CPU (user+sys of the compile and its waited children), instructions retired
and peak RSS, per backend lane, with the load range. Usage: geo.py RESULT.json"""
import json, math, sys
d = json.load(open(sys.argv[1]))
lanes = [l for l in next(iter(d["programs"].values()))["summary"] if l != "llvm_o2"]
for lane in lanes:
    rw, ri, rr, ru, loads = [], [], [], [], []
    for p, v in d["programs"].items():
        s = v["summary"]; L = s["llvm_o2"]; B = s[lane]
        rw.append(B["wall"] / L["wall"]); ri.append(B["instr"] / L["instr"]); rr.append(B["rss"] / L["rss"])
        ru.append((B["user"] + B["sys"]) / (L["user"] + L["sys"])); loads += B["load"]
    g = lambda xs: math.exp(sum(map(math.log, xs)) / len(xs))
    print(f"{lane}: wall {g(rw):.3f}x (max {max(rw):.3f}) cpu {g(ru):.3f}x instr {g(ri):.3f}x rss {g(rr):.3f}x load {min(loads)}-{max(loads)}")
