#!/usr/bin/env python3
"""Whole-core probe comparison: functions whose verdict or theorem bytes differ between two
run_probe_all.sh outputs. usage: allcmp.py <base dir> <new dir> [--list]"""
import os, sys
def load(d):
    verdict = {}
    for line in open(f"{d}/cf.tsv"):
        r = line.rstrip("\n").split("\t")
        verdict[r[0]] = r[1] if len(r) > 1 else ""
    files = {}
    p = f"{d}/smt2/index.tsv"
    if os.path.exists(p):
        for line in open(p):
            r = line.rstrip("\n").split("\t")
            qs = [f"{r[0]}.part{k}.smt2" for k in range(1, int(r[2]) + 1)] if len(r) == 3 else [f"{r[0]}.smt2"]
            files[r[1]] = [open(f"{d}/smt2/{q}").read() for q in qs]
    return verdict, files
bv, bf = load(sys.argv[1]); nv, nf = load(sys.argv[2])
vchg = [f for f in bv if f in nv and bv[f].split(" ")[0] != nv[f].split(" ")[0]]
built_b = {f for f in bv if bv[f].startswith("OWNER")}; built_n = {f for f in nv if nv[f].startswith("OWNER")}
qchg = [f for f in bf if f in nf and bf[f] != nf[f]]
print(f"functions {len(bv)}/{len(nv)}; built {len(built_b)} -> {len(built_n)}; newly built {len(built_n - built_b)}; "
      f"no longer built {len(built_b - built_n)}; theorem bytes changed {len(qchg)}")
if "--list" in sys.argv:
    for f in sorted(built_n - built_b): print("NEW", f.split("4core")[-1][:90], nv[f][:60])
    for f in sorted(built_b - built_n): print("LOST", f.split("4core")[-1][:90], nv.get(f, "")[:100])
    for f in sorted(qchg): print("BYTES", f.split("4core")[-1][:90])
