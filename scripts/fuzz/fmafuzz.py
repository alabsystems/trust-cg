#!/usr/bin/env python3
# fmafuzz.py — scalar FUSED multiply-add (FMADD) differential fuzzer for trust-cg.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# The whole point of FMADD is a SINGLE rounding of the exact `a*b + c` — NOT
# `round(round(a*b) + c)` (two roundings), which differs in the last ULP on a
# dense set of inputs. This fuzzer proves trust-cg's `llvm.fmuladd` lowering is
# BIT-IDENTICAL to clang's hardware FMADD across a battery of triples
# (NaN / Inf / denormal / round-once-vs-twice divergent / random), AND that the
# UNFUSED reference (`a*b+c` with `-ffp-contract=off`) genuinely DIFFERS from the
# fused result on the sensitive triples — i.e. that trust-cg actually FUSES.
#
# Pipeline (per width f32/f64):
#   1. A kernel `.ll` defines `f(a,b,c) = @llvm.fmuladd.fN(a,b,c)`.
#   2. clang -O1 kernel.ll  -> the ORACLE binary (hardware FMADD).      [fused]
#   3. trust-cg-ws2-import kernel.ll -> object -> the TEST binary.      [fused]
#   4. clang -O0 -ffp-contract=off unfused.c -> the UNFUSED reference.  [2 rounds]
#   A driver reads triples (hex bits) on argv and prints the result bits; we
#   compare TEST vs ORACLE bit-for-bit, and assert UNFUSED differs on ≥1 triple.
#
# Usage: python3 fmafuzz.py /path/to/trust-cg-ws2-import
import os, random, struct, subprocess, sys, tempfile

IMP = sys.argv[1] if len(sys.argv) > 1 else "target/release/trust-cg-ws2-import"
random.seed(20260713)


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=180, **kw)


def bits_f64(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def f64_of(b):
    return struct.unpack("<d", struct.pack("<Q", b & 0xFFFFFFFFFFFFFFFF))[0]


def bits_f32(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def f32_of(b):
    return struct.unpack("<f", struct.pack("<I", b & 0xFFFFFFFF))[0]


# ---------------------------------------------------------------------------
# Triple battery: NaN / Inf / denormal / round-divergent / random. Values are
# given as raw bit patterns so denormals/NaNs/signed-zeros are exact.
# ---------------------------------------------------------------------------
F64_SPECIAL = [
    0x0000000000000000,  # +0
    0x8000000000000000,  # -0
    0x3FF0000000000000,  # 1.0
    0xBFF0000000000000,  # -1.0
    0x4000000000000000,  # 2.0
    0x7FF0000000000000,  # +Inf
    0xFFF0000000000000,  # -Inf
    0x7FF8000000000000,  # qNaN
    0x7FF0000000000001,  # sNaN
    0x0000000000000001,  # min denormal
    0x000FFFFFFFFFFFFF,  # max denormal
    0x0010000000000000,  # min normal
    0x7FEFFFFFFFFFFFFF,  # max normal
    0xFFEFFFFFFFFFFFFF,  # -max normal
    0x3FF000000006DF38,  # 1.0000000001 (round-divergent multiplicand)
    0x4340000000000000,  # 2^53
]
# The round-once-vs-twice DIVERGENT triple (fused != unfused in the last ULP).
F64_DIVERGENT = (0x3FF000000006DF38, 0x3FF000000006DF38, 0xBFF0000000000000)
F32_SPECIAL = [
    0x00000000, 0x80000000, 0x3F800000, 0xBF800000, 0x40000000,
    0x7F800000, 0xFF800000, 0x7FC00000, 0x7F800001, 0x00000001,
    0x007FFFFF, 0x00800000, 0x7F7FFFFF, 0xFF7FFFFF, 0x3F800002, 0x4B000000,
]
F32_DIVERGENT = (0x3F800002, 0x3F800002, 0xBF800000)  # 1.00000024f, sq, -1


def gen_triples(special, divergent, mk_bits, n_random):
    triples = [divergent]
    # full special x special x {a few special c}
    for a in special:
        for b in special:
            for c in special[:6]:
                triples.append((a, b, c))
    # random (incl. random exponents to hit denormals/overflow paths)
    for _ in range(n_random):
        triples.append((mk_bits(), mk_bits(), mk_bits()))
    return triples


def rnd64():
    return random.getrandbits(64)


def rnd32():
    return random.getrandbits(32)


KERNEL_LL = """; fmafuzz kernel — single-rounding fused multiply-add via llvm.fmuladd.
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx11.0.0"

define double @fma64(double %a, double %b, double %c) {
  %r = call double @llvm.fmuladd.f64(double %a, double %b, double %c)
  ret double %r
}
define float @fma32(float %a, float %b, float %c) {
  %r = call float @llvm.fmuladd.f32(float %a, float %b, float %c)
  ret float %r
}
declare double @llvm.fmuladd.f64(double, double, double)
declare float @llvm.fmuladd.f32(float, float, float)
"""

# Driver: argv = width, a_bits, b_bits, c_bits (hex); prints result bits (hex).
DRIVER_C = """
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
extern double fma64(double,double,double);
extern float  fma32(float,float,float);
static double d_of(unsigned long long b){ double x; memcpy(&x,&b,8); return x; }
static unsigned long long b_of_d(double x){ unsigned long long b; memcpy(&b,&x,8); return b; }
static float  f_of(unsigned u){ float x; memcpy(&x,&u,4); return x; }
static unsigned b_of_f(float x){ unsigned b; memcpy(&b,&x,4); return b; }
int main(int argc, char** argv){
  int w = atoi(argv[1]);
  if (w == 64){
    unsigned long long a=strtoull(argv[2],0,16),b=strtoull(argv[3],0,16),c=strtoull(argv[4],0,16);
    printf("%016llx\\n", b_of_d(fma64(d_of(a),d_of(b),d_of(c))));
  } else {
    unsigned a=strtoul(argv[2],0,16),b=strtoul(argv[3],0,16),c=strtoul(argv[4],0,16);
    printf("%08x\\n", b_of_f(fma32(f_of(a),f_of(b),f_of(c))));
  }
  return 0;
}
"""

# UNFUSED reference (strict two-rounding a*b+c, no contraction): the anti-oracle
# that MUST differ from fused on the sensitive triple (proves we actually fuse).
UNFUSED_C = """
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static double d_of(unsigned long long b){ double x; memcpy(&x,&b,8); return x; }
static unsigned long long b_of_d(double x){ unsigned long long b; memcpy(&b,&x,8); return b; }
static float  f_of(unsigned u){ float x; memcpy(&x,&u,4); return x; }
static unsigned b_of_f(float x){ unsigned b; memcpy(&b,&x,4); return b; }
double fma64(double a,double b,double c){ return a*b + c; }
float  fma32(float a,float b,float c){ return a*b + c; }
int main(int argc, char** argv){
  int w = atoi(argv[1]);
  if (w == 64){
    unsigned long long a=strtoull(argv[2],0,16),b=strtoull(argv[3],0,16),c=strtoull(argv[4],0,16);
    printf("%016llx\\n", b_of_d(fma64(d_of(a),d_of(b),d_of(c))));
  } else {
    unsigned a=strtoul(argv[2],0,16),b=strtoul(argv[3],0,16),c=strtoul(argv[4],0,16);
    printf("%08x\\n", b_of_f(fma32(f_of(a),f_of(b),f_of(c))));
  }
  return 0;
}
"""


def build(wd):
    ll = os.path.join(wd, "kernel.ll")
    open(ll, "w").write(KERNEL_LL)
    open(os.path.join(wd, "driver.c"), "w").write(DRIVER_C)
    open(os.path.join(wd, "unfused.c"), "w").write(UNFUSED_C)

    # ORACLE: clang lowers llvm.fmuladd -> hardware FMADD (fused).
    r = run(["clang", "-O1", ll, os.path.join(wd, "driver.c"), "-o", os.path.join(wd, "oracle")])
    if r.returncode != 0:
        print("clang oracle build FAILED:\n" + r.stderr[:2000]); sys.exit(2)

    # TEST: trust-cg importer lowers llvm.fmuladd -> FMADD (fused).
    obj = os.path.join(wd, "kernel.o")
    r = run([IMP, "--opt-level", "O2", ll, obj])
    if r.returncode != 0:
        print("trust-cg import FAILED:\n" + (r.stderr or r.stdout)[:2000]); sys.exit(2)
    r = run(["cc", obj, os.path.join(wd, "driver.c"), "-o", os.path.join(wd, "test")])
    if r.returncode != 0:
        print("trust-cg link FAILED:\n" + r.stderr[:2000]); sys.exit(2)

    # UNFUSED anti-oracle (two roundings, no contraction).
    r = run(["clang", "-O0", "-ffp-contract=off",
             os.path.join(wd, "unfused.c"), "-o", os.path.join(wd, "unfused")])
    if r.returncode != 0:
        print("unfused build FAILED:\n" + r.stderr[:2000]); sys.exit(2)
    return wd


def result(binpath, w, a, b, c):
    r = run([binpath, str(w), f"{a:x}", f"{b:x}", f"{c:x}"])
    if r.returncode != 0:
        return None
    return r.stdout.strip()


def main():
    with tempfile.TemporaryDirectory() as wd:
        build(wd)
        oracle, test, unfused = (os.path.join(wd, n) for n in ("oracle", "test", "unfused"))

        total = passed = 0
        fails = []
        fused_differs_from_unfused = 0

        batteries = [
            (64, gen_triples(F64_SPECIAL, F64_DIVERGENT, rnd64, 4000)),
            (32, gen_triples(F32_SPECIAL, F32_DIVERGENT, rnd32, 4000)),
        ]
        for w, triples in batteries:
            for (a, b, c) in triples:
                total += 1
                want = result(oracle, w, a, b, c)   # hardware FMADD (fused)
                got = result(test, w, a, b, c)      # trust-cg FMADD
                unf = result(unfused, w, a, b, c)   # two-rounding reference
                if want is None or got is None:
                    fails.append((w, a, b, c, "run-error")); continue
                # NaN payload note: both sides are the same hardware FMADD, so a
                # bit-exact match is required (NaN payloads included).
                if got == want:
                    passed += 1
                else:
                    fails.append((w, a, b, c, f"got={got} want={want}"))
                if unf is not None and unf != want:
                    fused_differs_from_unfused += 1

        print(f"=== fmafuzz: {passed}/{total} bit-identical vs clang hardware FMADD ===")
        print(f"fused != unfused on {fused_differs_from_unfused} triples "
              f"(proves trust-cg actually FUSES; must be > 0)")

        # The sensitive divergent triple MUST be present and MUST show fusion.
        for w, div in ((64, F64_DIVERGENT), (32, F32_DIVERGENT)):
            a, b, c = div
            f = result(test, w, a, b, c)
            u = result(unfused, w, a, b, c)
            o = result(oracle, w, a, b, c)
            tag = "OK" if (f == o and f != u) else "BAD"
            print(f"  f{w} divergent triple: trust-cg={f} clang-fused={o} unfused={u} [{tag}]")
            if f != o or f == u:
                fails.append((w, a, b, c, "divergent-triple-not-fused"))

        if fails:
            print(f"--- {len(fails)} FAILURES (first 20) ---")
            for (w, a, b, c, why) in fails[:20]:
                print(f"  f{w} a={a:x} b={b:x} c={c:x} {why}")
            sys.exit(1)
        if fused_differs_from_unfused == 0:
            print("ERROR: fused never differed from unfused — fusion not proven")
            sys.exit(1)
        print("fmafuzz: PASS")


if __name__ == "__main__":
    main()
