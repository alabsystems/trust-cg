#!/usr/bin/env python3
"""N sequential byte-fill loops through one pointer argument: loop k fills
bytes [64k, 64k+64) with a constant, then reads one byte back into an
accumulator. Only the pointer and the accumulator live across loops (the
trust-ir form of `aarch64_compile_scaling`'s fill-loop chain).
Usage: gen_fill_chain.py N OUT"""
import sys

n = int(sys.argv[1])
L = ["; TrustIr text format v1", 'module "fills"', "", "functy.0 = (ptr, u64) -> (u64)", "",
     "fn @fills(functy.0) {", "bb0(%0: ptr, %1: u64):"]
v = 2
acc = 1
block = 1
for k in range(n):
    header, body, exit_ = block, block + 1, block + 2
    block += 3
    off, base, zero = v, v + 1, v + 2
    v += 3
    L += [f"    %{off} = const i64 {64 * k}", f"    %{base} = gep i8, ptr %0, %{off}",
          f"    %{zero} = const u64 0", f"    br bb{header}(%{zero})"]
    i, lim, c = v, v + 1, v + 2
    v += 3
    L += [f"bb{header}(%{i}: u64):", f"    %{lim} = const u64 64", f"    %{c} = icmp ult u64 %{i}, %{lim}",
          f"    condbr %{c}, bb{body}, bb{exit_}"]
    p, val, one, nxt = v, v + 1, v + 2, v + 3
    v += 4
    L += [f"bb{body}:", f"    %{p} = gep i8, ptr %{base}, %{i}", f"    %{val} = const u8 {(k * 37) % 251 + 1}",
          f"    store u8 %{val}, ptr %{p}", f"    %{one} = const u64 1", f"    %{nxt} = add u64 %{i}, %{one}",
          f"    br bb{header}(%{nxt})"]
    q, x, w, na = v, v + 1, v + 2, v + 3
    v += 4
    L += [f"bb{exit_}:", f"    %{q} = gep i8, ptr %{base}, %{zero}",
          f"    %{x} = load u8, ptr %{q}", f"    %{w} = zext u8 %{x} to u64", f"    %{na} = xor u64 %{acc}, %{w}"]
    acc = na
L += [f"    ret %{acc}", "}"]
open(sys.argv[2], "w").write("\n".join(L) + "\n")
