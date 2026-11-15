#!/usr/bin/env python3
"""Profile a probe dump (dump_class.sh output): per function, the LIR opcodes
(with I128/F32/F64 operand types where the LIR names them), the machine opcodes,
the machine rows outside the slice-10 lane, the block count and row count.
usage: profile.py <dump.txt> [--per-fn]"""
import collections
import re
import sys

LANE = set("""MovRR MovRR32 MovRI Movzx MovzxW MovsxB MovsxW Movsx AddRR SubRR ImulRR AndRR
OrRR XorRR AddRI SubRI AndRI OrRI XorRI ShlRI ShrRI SarRI ShlRR ShrRR SarRR Not Neg Popcnt
Mul Lea LeaSib MovRM8 MovRM16 MovzxRM8 MovzxRM16 MovRM32 MovRM MovMR8 MovMR16 MovMR32 MovMR
LeaRip MovRipRel CmpRR CmpRI TestRR TestRI Setcc Cmovcc Cmovcc32 Call CallR Jcc Jmp Ret Ud2
Nop""".split())


def functions(path):
    fn = None
    for line in open(path, errors="replace"):
        if line.startswith("==== "):
            if fn:
                yield fn
            fn = {"name": line[5:].strip(), "lir": [], "mach": [], "verdict": "", "sig": "",
                  "blocks": 0}
            continue
        if fn is None:
            continue
        s = line.strip()
        if s.startswith("sig "):
            fn["sig"] = s
        elif s.startswith("MBlock"):
            fn["blocks"] += 1
        elif re.match(r"\d+ \w+", s):
            fn["mach"].append(s.split()[1])
        elif s.startswith("[") and "] = " in s:
            op = s.split("] = ", 1)[1]
            fn["lir"].append(op)
        elif s.startswith("BODY") or s.startswith("SELECT"):
            fn["verdict"] = s
    if fn:
        yield fn


def lir_key(op):
    name = re.split(r"[ {(\[]", op, 1)[0]
    tys = sorted(set(re.findall(r"\b(I128|F32|F64|F16|V128|V64)\b", op)))
    return name + ("<" + ",".join(tys) + ">" if tys else "")


def main():
    fns = list(functions(sys.argv[1]))
    per_fn = "--per-fn" in sys.argv
    machine_out = collections.Counter()
    lir_ops = collections.Counter()
    for fn in fns:
        outside = sorted(set(op for op in fn["mach"] if op not in LANE))
        for op in set(fn["mach"]):
            if op not in LANE:
                machine_out[op] += 1
        for op in set(lir_key(o) for o in fn["lir"]):
            lir_ops[op] += 1
        if per_fn:
            print(f"{fn['name'][:90]}\tblocks={fn['blocks']}\trows={len(fn['mach'])}\t"
                  f"out={','.join(outside)}\t{fn['sig'][:80]}")
    print(f"# {len(fns)} functions")
    print("# machine opcodes outside the lane (functions using each):")
    for op, n in machine_out.most_common():
        print(f"  {n:4d} {op}")
    print("# LIR opcodes (functions using each):")
    for op, n in lir_ops.most_common():
        print(f"  {n:4d} {op}")


if __name__ == "__main__":
    main()
