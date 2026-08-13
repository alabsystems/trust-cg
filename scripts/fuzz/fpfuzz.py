#!/usr/bin/env python3
# fpfuzz.py — FP loop-carried differential fuzzer for trust-cg.
#
# Fills the gap the every-program census exposed (2026-07-08): all prior
# fuzzers were integer-only, so the FPR-copy P0 (ISel class-blind MovR for
# block-arg copies -> SEGV on every scalar FP reduction) was invisible to the
# whole gate set. This sweeps FP loop-carried reduction shapes at every opt
# level, bit-exact vs clang -O0 -ffp-contract=off (STRICT order + no fmadd
# fusion on the reference side; trust-cg emits unfused fmul+fadd at all levels,
# so bit-equality is the correct oracle).
#
# Usage: python3 fpfuzz.py /path/to/trust-cg
import os, random, struct, subprocess, sys, tempfile

MB = sys.argv[1] if len(sys.argv) > 1 else "target/release/trust-cg"
random.seed(20260708)
NL = chr(10)

# (name, trust_ir body-op recipe, C body expr) per reduction shape.
# %21=acc (fT), %23=loaded a[i], %26=loaded b[i] (dot only).
SHAPES = [
    ("sum",  lambda t: f"%24=fadd {t} %21,%23",                          "s += a[i]"),
    ("dot",  lambda t: f"%27=fmul {t} %23,%26{NL} %24=fadd {t} %21,%27", "s += a[i]*b[i]"),
    ("max",  lambda t: f"%27=fcmp ogt {t} %23,%21{NL} %24=select {t} %27,%23,%21", "s = a[i]>s ? a[i] : s"),
    ("min",  lambda t: f"%27=fcmp olt {t} %23,%21{NL} %24=select {t} %27,%23,%21", "s = a[i]<s ? a[i] : s"),
    ("sub",  lambda t: f"%24=fsub {t} %21,%23",                          "s -= a[i]"),
    ("mac3", lambda t: f"%27=fmul {t} %23,%23{NL} %24=fadd {t} %21,%27", "s += a[i]*a[i]"),
]

def kernel(shape_body, fty, two_arrays):
    b_param = ", ptr" if two_arrays else ""
    b_arg = ",%9: ptr" if two_arrays else ""
    b_load = f" %25=gep {fty},ptr %9,%20{NL} %26=load {fty},ptr %25{NL}" if two_arrays else ""
    return f"""; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr{b_param}, i32) -> ({fty})
fn @k(functy.0){{
bb0(%0: ptr{b_arg},%1: i32):
 %2=const i32 0
 %3=const i32 1
 %4=const {fty} 0.0
 br bb1(%2,%4)
bb1(%10: i32,%11: {fty}):
 %12=icmp slt i32 %10,%1
 condbr %12,bb3(%10,%11),bb2(%11)
bb3(%20: i32,%21: {fty}):
 %22=gep {fty},ptr %0,%20
 %23=load {fty},ptr %22
{b_load} {shape_body}
 %28=add i32 %20,%3
 br bb1(%28,%24)
bb2(%40: {fty}):
 ret %40
}}
"""

def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=120, **kw)

ok = mm = err = 0
fails = []
with tempfile.TemporaryDirectory() as wd:
    for fty, cty, fmt in [("f32", "float", "a"), ("f64", "double", "la")]:
        for name, mk, cexpr in SHAPES:
            two = name == "dot"
            src = kernel(mk(fty), fty, two)
            ir = os.path.join(wd, "k.trust_ir")
            open(ir, "w").write(src)
            # C reference (strict order, no contraction) + driver with random
            # + sign-edge data across many n including 0/1/tails.
            bsig = f", const {cty}* b" if two else ""
            buse = cexpr.replace("a[i]", "a[i]").replace("b[i]", "b[i]")
            drv = f"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
extern {cty} k({cty}*{', ' + cty + '*' if two else ''}, int);
static {cty} ref(const {cty}* a{bsig}, int n) {{ {cty} s = 0; for (int i = 0; i < n; i++) {{ {buse}; }} return s; }}
int main() {{
  int ns[] = {{0,1,2,3,4,7,8,15,16,17,31,33,100,1000,4097}};
  srand(7); int bad = 0;
  for (int j = 0; j < 15; j++) {{
    int n = ns[j]; int sz = n ? n : 1;
    {cty}* a = malloc(sz * sizeof({cty})); {cty}* b = malloc(sz * sizeof({cty}));
    for (int i = 0; i < n; i++) {{
      a[i] = ({cty})((rand() % 2001) - 1000) / 3;
      b[i] = ({cty})((rand() % 2001) - 1000) / 7;
      if (i % 17 == 3) a[i] = -a[i];
    }}
    {cty} got = k(a{', b' if two else ''}, n);
    {cty} exp = ref(a{', b' if two else ''}, n);
    if (memcmp(&got, &exp, sizeof({cty}))) {{ bad++; fprintf(stderr, "n=%d got=%{fmt} exp=%{fmt}\\n", n, got, exp); }}
    free(a); free(b);
  }}
  printf(bad ? "BAD %d\\n" : "OK\\n", bad);
  return bad != 0;
}}
"""
            cdrv = os.path.join(wd, "d.c")
            open(cdrv, "w").write(drv)
            for O in ["O0", "O1", "O2"]:
                obj = os.path.join(wd, "k.o")
                r = run([MB, "--format=text", "--target", "aarch64", f"-{O}", "-c", ir, "-o", obj])
                if r.returncode != 0:
                    err += 1; fails.append(f"{fty}:{name}:-{O} compile: {r.stderr.strip()[:80]}"); continue
                exe = os.path.join(wd, "t")
                r = run(["cc", "-O0", "-ffp-contract=off", cdrv, obj, "-o", exe])
                if r.returncode != 0:
                    err += 1; fails.append(f"{fty}:{name}:-{O} link"); continue
                r = run([exe])
                if r.returncode == 0 and "OK" in r.stdout:
                    ok += 1
                else:
                    mm += 1; fails.append(f"{fty}:{name}:-{O} MISMATCH/crash rc={r.returncode} {r.stderr.strip()[:80]}")

print(f"=== fpfuzz: FP loop-carried differential ===")
print(f"OK={ok}  MISMATCH={mm}  other(compile/link)={err}   [2 widths x {len(SHAPES)} shapes x 3 opt levels, 15 n-values each]")
for f in fails[:12]:
    print("  FAIL:", f)
sys.exit(1 if (mm or err) else 0)
