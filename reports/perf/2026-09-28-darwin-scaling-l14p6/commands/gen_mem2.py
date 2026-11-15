#!/usr/bin/env python3
"""One straight-line block of m (store; load) pairs into a stack tuple with a
running accumulator: memory-order heavy, register-pressure light.
Usage: gen_mem2.py M OUT"""
import sys

m = int(sys.argv[1])
L = ["; TrustIr text format v1", 'module "mem_chain"', "", "functy.0 = (u64) -> (u64)", "",
     "fn @memchain(functy.0) {", "bb0(%0: u64):",
     "    %1 = alloca (" + ", ".join(["u64"] * m) + "), align 8"]
acc = 0
v = 2
for i in range(m):
    L += [f"    %{v} = const i64 {8 * i}",
          f"    %{v + 1} = gep i8, ptr %1, %{v}",
          f"    %{v + 2} = const u64 {i + 1}",
          f"    %{v + 3} = xor u64 %{acc}, %{v + 2}",
          f"    store u64 %{v + 3}, ptr %{v + 1}",
          f"    %{v + 4} = load u64, ptr %{v + 1}",
          f"    %{v + 5} = add u64 %{acc}, %{v + 4}"]
    acc = v + 5
    v += 6
L += [f"    ret %{acc}", "}"]
open(sys.argv[2], "w").write("\n".join(L) + "\n")
