#!/usr/bin/env python3
"""Generate a trust-ir text module shaped like scale_gate.py's crate:
N functions, each a 64-iteration loop over mul/xor/shift/rotate with a
branch, and one entry function whose single block calls every one of them
and xors the results. Usage: gen_tir.py N OUT"""
import sys

MUL = 6364136223846793005


def function(i: int) -> str:
    seed = (i * 2654435761) % (1 << 32)
    k = (i + 1) % 63
    return f"""fn @f{i}(functy.0) {{
bb0(%0: u64, %1: u64):
    %2 = const u64 {seed}
    %3 = xor u64 %0, %2
    %4 = const u64 0
    br bb1(%0, %3, %4)
bb1(%5: u64, %6: u64, %7: u64):
    %8 = const u64 64
    %9 = icmp ult u64 %7, %8
    condbr %9, bb2, bb6(%6)
bb2:
    %10 = const u64 {MUL}
    %11 = mul u64 %6, %10
    %12 = xor u64 %7, %1
    %13 = add u64 %11, %12
    %14 = const u64 29
    %15 = lshr u64 %13, %14
    %16 = xor u64 %13, %15
    %17 = const u64 7
    %18 = urem u64 %16, %17
    %19 = const u64 0
    %20 = icmp eq u64 %18, %19
    condbr %20, bb3, bb4
bb3:
    %21 = add u64 %16, %5
    br bb5(%21)
bb4:
    %22 = xor u64 %16, %7
    br bb5(%22)
bb5(%23: u64):
    %24 = const u64 {k}
    %25 = shl u64 %5, %24
    %26 = const u64 {64 - k}
    %27 = lshr u64 %5, %26
    %28 = or u64 %25, %27
    %29 = const u64 1
    %30 = add u64 %7, %29
    br bb1(%28, %23, %30)
bb6(%31: u64):
    ret %31
}}
"""


def entry(n: int) -> str:
    lines = ["fn @entry(functy.1) {", "bb0(%0: u64):"]
    v = 1
    acc = None
    for i in range(n):
        lines.append(f"    %{v} = const u64 {i}")
        lines.append(f"    %{v + 1} = call @func.{i}(%0, %{v})")
        r = v + 1
        v += 2
        if acc is None:
            acc = r
        else:
            lines.append(f"    %{v} = xor u64 %{acc}, %{r}")
            acc = v
            v += 1
    lines.append(f"    ret %{acc}")
    lines.append("}")
    return "\n".join(lines) + "\n"


def module(n: int) -> str:
    head = f"""; TrustIr text format v1
module "scale_{n}"

functy.0 = (u64, u64) -> (u64)

functy.1 = (u64) -> (u64)

"""
    return head + "\n".join(function(i) for i in range(n)) + "\n" + entry(n)


if __name__ == "__main__":
    n = int(sys.argv[1])
    with open(sys.argv[2], "w") as f:
        f.write(module(n))
