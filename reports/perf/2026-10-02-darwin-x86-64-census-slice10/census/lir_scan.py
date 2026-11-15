#!/usr/bin/env python3
"""For each function of a class file (split_classes.py), the LIR opcodes outside the
slice-8 admitted set, the block count, and the machine rows outside BODY_OPCODES.
Usage: lir_scan.py <cls_file>"""
import collections
import re
import sys

ADMITTED = {"Iconst", "Copy", "Bitcast", "Iadd", "Isub", "Imul", "Band", "Bor", "Bxor", "Ishl",
            "Ushr", "Sshr", "Uextend", "Sextend", "Trunc", "Icmp", "Select", "StackAddr",
            "StructGep", "GlobalRef", "ExternRef", "Load", "Store", "Call", "Return", "Trap",
            "Jump", "Brif", "Switch"}
MACHINE = {"MovRR", "MovRR32", "MovRI", "Movzx", "MovzxW", "MovsxB", "MovsxW", "Movsx", "AddRR",
           "SubRR", "ImulRR", "AndRR", "OrRR", "XorRR", "AddRI", "SubRI", "AndRI", "OrRI", "XorRI",
           "ShlRI", "ShrRI", "SarRI", "Lea", "LeaSib", "MovRM8", "MovRM16", "MovzxRM8",
           "MovzxRM16", "MovRM32", "MovRM", "MovMR8", "MovMR16", "MovMR32", "MovMR", "LeaRip",
           "MovRipRel", "CmpRR", "CmpRI", "TestRR", "TestRI", "Setcc", "Cmovcc", "Cmovcc32", "Call",
           "Jcc", "Jmp", "Ret", "Ud2", "Nop"}

fns = {}
cur = None
for line in open(sys.argv[1], errors="replace"):
    if line.startswith("==== "):
        cur = line[5:].strip()
        fns[cur] = {"lir": collections.Counter(), "mach": collections.Counter(), "blocks": 0,
                    "verdict": "", "lirlines": 0}
        continue
    if cur is None:
        continue
    f = fns[cur]
    m = re.match(r"^    \[.*?\] = ([A-Za-z0-9]+)", line)
    if m:
        f["lir"][m.group(1)] += 1
        f["lirlines"] += 1
        continue
    if re.match(r"^  Block\(\d+\) params", line):
        f["blocks"] += 1
        continue
    m = re.match(r"^ +\d+ ([A-Za-z0-9]+) ", line)
    if m:
        f["mach"][m.group(1)] += 1
        continue
    if line.startswith("  BODY"):
        f["verdict"] = line.strip()[:160]

total_lir = collections.Counter()
total_mach = collections.Counter()
for name, f in fns.items():
    extra = sorted(k for k in f["lir"] if k not in ADMITTED)
    mextra = sorted(k for k in f["mach"] if k not in MACHINE)
    for k in extra:
        total_lir[k] += 1
    for k in mextra:
        total_mach[k] += 1
    print(f"{f['blocks']:3d} blk {f['lirlines']:4d} lir  lir+{extra}  mach+{mextra}  {name[:90]}")
print("functions with each LIR opcode outside slice 8:", dict(total_lir.most_common()))
print("functions with each machine row outside slice 8:", dict(total_mach.most_common()))
