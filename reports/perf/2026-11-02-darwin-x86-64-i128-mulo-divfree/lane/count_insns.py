#!/usr/bin/env python3
"""OD-224 lane: static instruction counts per function of x86-64 objects, decoded by the system's
llvm-objdump (`objdump -d --no-show-raw-insn`, Xcode's disassembler, independent of trust-cg's
encoder). For each object and each function symbol: instructions, `mul`s (MUL/IMUL in every
form), `call`s. usage: count_insns.py <object>... -> TSV on stdout"""
import re, subprocess, sys

def functions(path):
    out = subprocess.run(["objdump", "-d", "--no-show-raw-insn", path], capture_output=True,
                         text=True, check=True).stdout
    funcs, cur = {}, None
    for line in out.splitlines():
        m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
        if m:
            cur = m.group(1)
            funcs[cur] = []
            continue
        m = re.match(r"^\s+[0-9a-f]+:\s+(\S+)\s*(.*)$", line)
        if m and cur is not None:
            funcs[cur].append((m.group(1), m.group(2)))
    return funcs

print("object\tfunction\tinsns\tmuls\tcalls")
for path in sys.argv[1:]:
    for name, insns in functions(path).items():
        muls = sum(1 for op, _ in insns if op.startswith(("mul", "imul")))
        calls = sum(1 for op, _ in insns if op.startswith("call"))
        print(f"{path.rsplit('/', 1)[-1]}\t{name}\t{len(insns)}\t{muls}\t{calls}")
