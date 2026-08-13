#!/usr/bin/env python3
# trust-cg - AFFINE IOTA reduction-term differential fuzzer (gap 1)
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Soundness fuzzer for the AFFINE IOTA reduction-term extension (gap 1):
reductions `r OP= TERM(i) BIT a[i]` whose per-lane term MIXES the loop index
(`i`, `i+K`, `c*i+d`) with an array load. These are the shapes the `neon-minmax`
(XOR/AND/OR reductions) and `neon-array` (ADD reduction) vectorizers newly admit
by materialising the iv as a per-lane iota position vector.

For each kernel it compiles the trust_ir with trust-cg -O0/-O2/-O3, links a printf
driver, runs the native aarch64 binary, and asserts ALL outputs are string-
IDENTICAL to a clang -O2 C twin over a sweep of trip counts (`n` EDGES around the
16-lane block width) and INT_MAX-adjacent iv windows (the iota wrap must match the
scalar two's-complement wrap). Also runs a must-BAIL control (`i*i` quadratic
term) that must still be left CORRECT.

usage: iotaredfuzz.py <trust-cg-binary> [--quick]
"""
import subprocess, sys, tempfile, os

TCG = sys.argv[1] if len(sys.argv) > 1 else "trust-cg"
QUICK = "--quick" in sys.argv

# reduction root op: (trust_ir mnemonic, C operator, identity)
REDS = {
    "add": ("add", "+", 0),
    "xor": ("xor", "^", 0),
    "or":  ("or",  "|", 0),
    "and": ("and", "&", -1),
}
# affine iv sub-term: (trust_ir producing %24 from %20 (i2) and consts %3..%7,
#  C expr over i). Uses %25 as a temp where a two-op affine is needed.
AFFINE = {
    "i":      ("%24 = add i32 %20, %3",        "i"),          # %3=0
    "ip1":    ("%24 = add i32 %20, %4",        "(i+1)"),      # %4=1
    "i3p7":   ("%25 = mul i32 %20, %6\n    %24 = add i32 %25, %7", "(i*3+7)"),  # %6=3,%7=7
    "i7":     ("%24 = mul i32 %20, %7",        "(i*7)"),      # %7=7
    "ishl2":  ("%24 = shl i32 %20, %5",        "(i<<2)"),     # %5=2
}
# bitwise mix combining the affine term with the load a[i].
MIX = {"xorm": ("xor", "^"), "andm": ("and", "&"), "orm": ("or", "|"), "addm": ("add", "+")}


def gen_tir(red, aff, mix):
    rmn, _, init = REDS[red]
    aff_ir, _ = AFFINE[aff]
    mmn, _ = MIX[mix]
    return f"""; TrustIr text format v1
module "ir"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32, i32) -> (i32)
fn @kernel(functy.0) {{
bb0(%0: ptr, %1: i32, %2: i32):
    %3 = const i32 0
    %4 = const i32 1
    %5 = const i32 2
    %6 = const i32 3
    %7 = const i32 7
    %8 = const i32 {init}
    br bb1(%2, %8)
bb1(%10: i32, %11: i32):
    %12 = icmp sge i32 %10, %1
    condbr %12, bb2(%11), bb3(%10, %11)
bb3(%20: i32, %21: i32):
    %22 = gep i32, ptr %0, %20
    %23 = load i32, ptr %22
    {aff_ir}
    %26 = {mmn} i32 %24, %23
    %27 = {rmn} i32 %21, %26
    %28 = add i32 %20, %4
    br bb1(%28, %27)
bb2(%40: i32): ret %40
}}
"""


def gen_c(red, aff, mix):
    _, cop, init = REDS[red]
    _, aexpr = AFFINE[aff]
    _, mop = MIX[mix]
    return f"""#include <stdint.h>
int32_t kernel(const int32_t *a, int32_t n, int32_t start){{
    uint32_t acc = {init & 0xffffffff}u;
    for (int32_t i = start; i < n; i++) {{
        uint32_t t = (uint32_t)({aexpr});
        acc = acc {cop} (t {mop} (uint32_t)a[i]);
    }}
    return (int32_t)acc;
}}
"""


def gen_tir_square():
    return """; TrustIr text format v1
module "sq"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32, i32) -> (i32)
fn @kernel(functy.0) {
bb0(%0: ptr, %1: i32, %2: i32):
    %3 = const i32 0
    %4 = const i32 1
    br bb1(%2, %3)
bb1(%10: i32, %11: i32):
    %12 = icmp sge i32 %10, %1
    condbr %12, bb2(%11), bb3(%10, %11)
bb3(%20: i32, %21: i32):
    %22 = gep i32, ptr %0, %20
    %23 = load i32, ptr %22
    %24 = mul i32 %20, %20
    %26 = xor i32 %24, %23
    %27 = xor i32 %21, %26
    %28 = add i32 %20, %4
    br bb1(%28, %27)
bb2(%40: i32): ret %40
}
"""


def gen_c_square():
    return """#include <stdint.h>
int32_t kernel(const int32_t *a, int32_t n, int32_t start){
    uint32_t acc = 0;
    for (int32_t i = start; i < n; i++) {
        uint32_t t = (uint32_t)i * (uint32_t)i;
        acc = acc ^ (t ^ (uint32_t)a[i]);
    }
    return (int32_t)acc;
}
"""


NS = [0, 1, 2, 15, 16, 17, 31, 32, 33, 47, 48, 63, 64, 100]
def gen_driver():
    body = ",".join(str(((i * 2654435761) & 0xffffffff) - 0x80000000) for i in range(128))
    ns = ",".join(str(x) for x in NS)
    return f"""#include <stdio.h>
#include <stdint.h>
extern int32_t kernel(const int32_t *, int32_t, int32_t);
int main(void) {{
    static const int32_t a[128] = {{{body}}};
    static const int32_t ns[] = {{{ns}}};
    for (unsigned k = 0; k < sizeof(ns)/sizeof(ns[0]); k++)
        printf("%d ", kernel(a, ns[k], 0));
    /* INT_MAX-adjacent iv windows: high start, small span (iota wrap). */
    printf("%d ", kernel(a, 2147483647, 2147483647 - 40));
    printf("%d ", kernel(a, -2147483648 + 40, -2147483648));
    printf("\\n");
    return 0;
}}
"""


def run(tir, tag):
    with tempfile.TemporaryDirectory() as d:
        tf = os.path.join(d, "k.trust_ir")
        open(tf, "w").write(tir)
        drv = os.path.join(d, "drv.c")
        open(drv, "w").write(gen_driver())
        outs = {}
        for o in ("O0", "O2", "O3"):
            obj = os.path.join(d, f"{o}.o")
            r = subprocess.run([TCG, "--format=text", "--target", "aarch64", f"-{o}",
                                "-c", tf, "-o", obj], capture_output=True, text=True)
            if r.returncode != 0:
                return ("COMPILE_ERR", tag, r.stderr[:200])
            b = os.path.join(d, o)
            if subprocess.run(["cc", drv, obj, "-o", b], capture_output=True).returncode != 0:
                return ("LINK_ERR", tag, "")
            outs[o] = subprocess.run([b], capture_output=True, text=True).stdout.strip()
    return ("OK", tag, outs)


def run_ref(cf):
    with tempfile.TemporaryDirectory() as d:
        drv = os.path.join(d, "drv.c")
        open(drv, "w").write(gen_driver())
        cfp = os.path.join(d, "twin.c")
        open(cfp, "w").write(cf)
        b = os.path.join(d, "ref")
        if subprocess.run(["cc", "-O2", cfp, drv, "-o", b], capture_output=True).returncode != 0:
            return None
        return subprocess.run([b], capture_output=True, text=True).stdout.strip()


def main():
    reds = ["xor", "add"] if QUICK else list(REDS)
    affs = ["ip1", "i3p7"] if QUICK else list(AFFINE)
    mixes = ["xorm"] if QUICK else list(MIX)
    ok = mism = err = 0
    for red in reds:
        for aff in affs:
            for mix in mixes:
                tag = f"{red}/{aff}/{mix}"
                st, _, outs = run(gen_tir(red, aff, mix), tag)
                if st != "OK":
                    print(f"[{st}] {tag}: {outs}"); err += 1; continue
                ref = run_ref(gen_c(red, aff, mix))
                if ref is None:
                    print(f"[REF_ERR] {tag}"); err += 1; continue
                if len(set(outs.values()) | {ref}) != 1:
                    print(f"[MISMATCH] {tag}: tcg={outs} clang={ref}"); mism += 1
                else:
                    ok += 1
    st, _, outs = run(gen_tir_square(), "square(bail)")
    ref = run_ref(gen_c_square())
    if st == "OK" and ref is not None and len(set(outs.values()) | {ref}) == 1:
        ok += 1
    else:
        print(f"[MISMATCH] square control: {outs} clang={ref}"); mism += 1
    print(f"iotaredfuzz: {ok} OK, {mism} mismatch, {err} err")
    sys.exit(1 if (mism or err) else 0)


if __name__ == "__main__":
    main()
