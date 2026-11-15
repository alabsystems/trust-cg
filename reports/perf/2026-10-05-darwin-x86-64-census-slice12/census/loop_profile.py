#!/usr/bin/env python3
"""Summarize the probe's `--loops` TSV (slice 12): the loop class's shapes.

usage: loop_profile.py <loops.tsv>
"""
import collections
import re
import sys

LANE = {
    "Iconst", "Iconst128", "Copy", "Bitcast", "Iadd", "Isub", "Imul", "Band", "Bor",
    "Bxor", "Bnot", "Ineg", "CtPop", "Ishl", "Ushr", "Sshr", "Uextend", "Sextend",
    "Trunc", "Icmp", "Select", "CheckedUadd", "CheckedUsub", "CheckedUmul",
    "CheckedSadd", "CheckedSsub", "CheckedSmul", "StackAddr", "StructGep", "GlobalRef",
    "ExternRef", "Load", "Store", "Call", "CallIndirect", "Return", "Trap", "Jump",
    "Brif", "Switch",
}

rows = [line.rstrip("\n").split("\t") for line in open(sys.argv[1])]
c = collections.Counter()
per_loop = collections.Counter()
outside = collections.Counter()
fn_outside = collections.Counter()
calls_in = collections.Counter()
params_c = collections.Counter()
blocks_c = collections.Counter()
mem_c = collections.Counter()
latch_c = collections.Counter()
exit_c = collections.Counter()
stepped_c = collections.Counter()
for r in rows:
    name, verdict, blocks, instrs, reducible, nloops, depth = r[:7]
    loops = re.findall(r"h(\d+)\[(.*?)\](?= h|$)", r[10]) if len(r) > 10 else []
    fn_ops = set()
    for header, body in loops:
        fields = dict(kv.split("=", 1) for kv in re.findall(r"(\w+=\([^)]*\)|\w+=[^ ]+)", body))
        per_loop["loops"] += 1
        blocks_c[int(fields["blocks"])] += 1
        latch_c[int(fields["latches"])] += 1
        exit_c[int(fields["exits"])] += 1
        params = fields["params"].strip("()")
        params_c[params] += 1
        stepped_c[(int(fields["stepped"]), len(params.split(",")) if params else 0)] += 1
        calls_in["calls>0" if int(fields["calls"]) else "no calls"] += 1
        mem_c[(int(fields["incoming"]) > 0, int(fields["private"]) > 0)] += 1
        for op in fields["ops"].split(","):
            if not op:
                continue
            o = op.split(":")[0]
            if o not in LANE:
                outside[o] += 1
                fn_ops.add(o)
    for o in fn_ops:
        fn_outside[o] += 1
    if not fn_ops:
        fn_outside["(none outside the lane)"] += 1

print("loops:", per_loop["loops"])
print("loop blocks:", sorted(blocks_c.items()))
print("latches:", sorted(latch_c.items()))
print("exit edges:", sorted(exit_c.items()))
print("calls in loop:", dict(calls_in))
print("(incoming, private) memory in loop:", dict(mem_c))
print("(stepped params, params):", sorted(stepped_c.items()))
print("header param types (top 25):")
for k, v in params_c.most_common(25):
    print(f"  {v:4d}  ({k})")
print("functions by opcode outside the lane in a loop:")
for k, v in fn_outside.most_common():
    print(f"  {v:4d}  {k}")
