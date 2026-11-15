#!/usr/bin/env python3
"""The scaling test's store/load block through a pointer argument.
Usage: gen_ptr.py M OUT"""
import sys

m = int(sys.argv[1])
L = ["; TrustIr text format v1", 'module "ptr_block"', "", "functy.2 = (ptr, u64) -> (u64)", "",
     "fn @entry(functy.0) {", "bb0(%0: ptr, %1: u64):"]
acc = 1
n = 2
for i in range(m):
    o, a, c, v, l, s = n, n + 1, n + 2, n + 3, n + 4, n + 5
    n += 6
    L += [f"    %{o} = const i64 {8 * i}",
          f"    %{a} = gep i8, ptr %0, %{o}",
          f"    %{c} = const u64 {i + 1}",
          f"    %{v} = xor u64 %{acc}, %{c}",
          f"    store u64 %{v}, ptr %{a}",
          f"    %{l} = load u64, ptr %{a}",
          f"    %{s} = add u64 %{acc}, %{l}"]
    acc = s
L += [f"    ret %{acc}", "}"]
text = "\n".join(L) + "\n"
text = text.replace("functy.2 =", "functy.0 =")
open(sys.argv[2], "w").write(text)
