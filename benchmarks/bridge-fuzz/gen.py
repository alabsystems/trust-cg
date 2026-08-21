#!/usr/bin/env python3
"""Seeded generator of DETERMINISTIC, UB-FREE safe-Rust programs for
differential testing of the rustc bridge against LLVM.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0

WHY THIS EXISTS: `scripts/fuzz_campaign.sh` drives trust-ir-gen / csmith /
yarpgen, but all of those feed the trust_ir and LLVM-import frontends. The rustc
BRIDGE -- the primary user-facing path -- had no generative differential
coverage at all: 18 beat-llvm programs plus 23 shape-coverage programs, all
hand-written. Every one of the 14+ wrong-code bugs found on 2026-08-19/20 was
caught by differential testing on a shape those 40 programs did not contain.

UB-FREEDOM IS THE WHOLE GAME. A generated program that is itself undefined
lets the two backends differ legitimately, so every finding would be a false
positive. Constraints, enforced by construction rather than by hope:
  * every arithmetic op is `wrapping_*` (no overflow, and the corpus compiles
    with -Coverflow-checks=off where overflow would otherwise be silent);
  * shift amounts are masked to the operand width (`>> (k & 63)`);
  * division and remainder go through `checked_div`/`checked_rem` (no /0, and
    no INT_MIN/-1);
  * indexing is `arr[i % LEN]` with a non-empty array (never out of bounds);
  * no floats (formatting/NaN differences are not what this is testing), no
    `unsafe`, no uninitialised reads, no interior mutability, no I/O, no time,
    no address-dependent behaviour;
  * all inputs come through `black_box` so nothing is const-folded to a
    constant, and the result is folded into an exit code.
"""
import random, sys

U64 = "u64"
I64 = "i64"
U32 = "u32"
I32 = "i32"
U16 = "u16"
I16 = "i16"
U8 = "u8"
I8 = "i8"
# Narrow widths included deliberately: truncation/sign-extension lowering was
# entirely untested by the original u64/i64/u32/i32 set, and the sub-word
# argument is a required ingredient of the stack-argument P0 above.
TYPES = [U64, I64, U32, I32, U16, I16, U8, I8]


class Gen:
    def __init__(self, seed):
        self.r = random.Random(seed)
        self.seed = seed

    # ---------- expressions ----------
    def expr(self, ty, vars_, depth):
        r = self.r
        if depth <= 0 or (vars_ and r.random() < 0.25):
            return r.choice(vars_) if vars_ else self.lit(ty)
        k = r.randrange(10)
        if k < 4:  # binary wrapping arithmetic
            op = r.choice(["wrapping_add", "wrapping_sub", "wrapping_mul"])
            a = self.expr(ty, vars_, depth - 1)
            b = self.expr(ty, vars_, depth - 1)
            return f"({a}).{op}({b})"
        if k < 6:  # bitwise
            op = r.choice(["&", "|", "^"])
            a = self.expr(ty, vars_, depth - 1)
            b = self.expr(ty, vars_, depth - 1)
            return f"(({a}) {op} ({b}))"
        if k == 6:  # masked shift
            w = {U64: 63, I64: 63, U32: 31, I32: 31, U16: 15, I16: 15, U8: 7, I8: 7}[ty]
            a = self.expr(ty, vars_, depth - 1)
            b = self.expr(ty, vars_, depth - 1)
            op = r.choice([">>", "<<"])
            if op == "<<":
                return f"(({a}).wrapping_shl((({b}) as u32) & {w}))"
            return f"(({a}).wrapping_shr((({b}) as u32) & {w}))"
        if k == 7:  # guarded div/rem
            op = r.choice(["checked_div", "checked_rem"])
            a = self.expr(ty, vars_, depth - 1)
            b = self.expr(ty, vars_, depth - 1)
            return f"({a}).{op}({b}).unwrap_or(1)"
        if k == 8:  # select
            c = self.cond(ty, vars_, depth - 1)
            a = self.expr(ty, vars_, depth - 1)
            b = self.expr(ty, vars_, depth - 1)
            return f"(if {c} {{ {a} }} else {{ {b} }})"
        # cast round-trip through another width
        other = r.choice([t for t in TYPES if t != ty])
        a = self.expr(ty, vars_, depth - 1)
        return f"((({a}) as {other}) as {ty})"

    def cond(self, ty, vars_, depth):
        a = self.expr(ty, vars_, max(0, depth - 1))
        b = self.expr(ty, vars_, max(0, depth - 1))
        return f"({a}) {self.r.choice(['<', '<=', '>', '>=', '==', '!='])} ({b})"

    def lit(self, ty):
        r = self.r
        bits = {U64: 64, I64: 64, U32: 32, I32: 32, U16: 16, I16: 16, U8: 8, I8: 8}[ty]
        if ty in (U64, U32, U16, U8):
            return f"{r.randrange(0, 1 << min(bits, 40))}{ty}"
        lim = 1 << min(bits - 2, 20)
        return f"{r.randrange(-lim, lim)}{ty}"

    # ---------- statements ----------
    def body(self, ty, vars_, depth, indent, budget):
        r = self.r
        out, live = [], list(vars_)
        for i in range(budget):
            k = r.randrange(10)
            name = f"t{i}"
            if k < 5:
                out.append(f"{indent}let {name} = {self.expr(ty, live, depth)};")
                live.append(name)
            elif k < 7:  # counted loop with a carried accumulator
                acc = f"a{i}"
                n = r.choice([3, 4, 7, 8, 16])
                idx = f"i{i}"
                out.append(f"{indent}let mut {acc} = {self.expr(ty, live, 1)};")
                out.append(f"{indent}let mut {idx} = 0{ty};")
                out.append(f"{indent}while {idx} < {n}{ty} {{")
                inner = live + [acc, idx]
                out.append(f"{indent}    {acc} = {self.expr(ty, inner, depth)};")
                out.append(f"{indent}    {idx} = {idx}.wrapping_add(1);")
                out.append(f"{indent}}}")
                live.append(acc)
            elif k < 9:  # array fill + reduce, always in bounds
                arr = f"v{i}"
                n = r.choice([4, 8, 16, 24])
                idx = f"j{i}"
                out.append(f"{indent}let mut {arr} = [0{ty}; {n}];")
                out.append(f"{indent}let mut {idx} = 0usize;")
                out.append(f"{indent}while {idx} < {n} {{")
                out.append(f"{indent}    {arr}[{idx} % {n}] = {self.expr(ty, live, max(1, depth - 1))};")
                out.append(f"{indent}    {idx} += 1;")
                out.append(f"{indent}}}")
                acc = f"s{i}"
                out.append(f"{indent}let mut {acc} = 0{ty};")
                out.append(f"{indent}let mut {idx}b = 0usize;")
                out.append(f"{indent}while {idx}b < {n} {{")
                out.append(f"{indent}    {acc} = {acc}.wrapping_add({arr}[{idx}b % {n}]);")
                out.append(f"{indent}    {idx}b += 1;")
                out.append(f"{indent}}}")
                live.append(acc)
            else:  # branch
                c = self.cond(ty, live, depth)
                out.append(f"{indent}let {name} = if {c} {{ {self.expr(ty, live, depth)} }} "
                           f"else {{ {self.expr(ty, live, depth)} }};")
                live.append(name)
        out.append(f"{indent}{self.expr(ty, live, depth)}")
        return "\n".join(out)

    # ---------- program ----------
    def program(self, nfuncs=None):
        r = self.r
        nfuncs = nfuncs or r.randrange(2, 6)
        parts = ["// GENERATED by benchmarks/bridge-fuzz/gen.py — do not edit.",
                 f"// seed={self.seed}",
                 "use std::hint::black_box as bb;", ""]
        sigs = []
        for f in range(nfuncs):
            ty = r.choice(TYPES)
            # Up to 12 parameters so the AArch64 8-integer-register boundary is
            # crossed and STACK-PASSED arguments are exercised. The stock range
            # of 1..3 could never reach it, and that blind spot hid a P0: a dead
            # load of an unused stack parameter scheduled past the ABI return
            # value, clobbering x0 (see
            # benchmarks/shape-coverage/progs/s23_abi_stack_arg_return_clobber.rs).
            nargs = r.randrange(1, 13)
            args = [f"p{i}" for i in range(nargs)]
            sig = ", ".join(f"{a}: {ty}" for a in args)
            parts.append("#[inline(never)]")
            parts.append(f"fn f{f}({sig}) -> {ty} {{")
            parts.append(self.body(ty, args, r.randrange(2, 4), "    ", r.randrange(2, 5)))
            parts.append("}")
            parts.append("")
            sigs.append((f, ty, nargs))
        parts.append("fn main() {")
        parts.append("    let mut acc: u64 = 0;")
        for f, ty, nargs in sigs:
            # Argument literals must fit the parameter's width — a `9998u8`
            # does not compile, and an oracle-side compile failure silently
            # erases a seed from the campaign.
            hi = {U64: 9999, I64: 9999, U32: 9999, I32: 9999,
                  U16: 9999, I16: 9999, U8: 200, I8: 100}[ty]
            a = ", ".join(f"bb({r.randrange(1, hi)}{ty})" for _ in range(nargs))
            parts.append(f"    acc = acc.wrapping_mul(31).wrapping_add(f{f}({a}) as u64);")
        parts.append("    std::process::exit((acc % 251) as i32);")
        parts.append("}")
        return "\n".join(parts)


if __name__ == "__main__":
    print(Gen(int(sys.argv[1])).program())
