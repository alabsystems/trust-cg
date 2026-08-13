#!/usr/bin/env python3
"""
Benchmarks for the width-parameterized NEON vectorizers (2e7 elements,
interleaved best-of-11): each kernel compiled trust-cg -O2 pass-ON (after),
trust-cg -O2 pass-OFF (before/scalar), clang -O3 (reference). The three
binaries are run interleaved (A,B,C x 3 process reps; each process reports its
in-process best of 11 timed calls after warmup); the min per binary is
reported. Also verifies the three binaries agree on the checksum.
usage: widebench.py <trust-cg-binary> [kernel...]
"""
import sys, os, subprocess, tempfile

N = 20000000

HDR = """; TrustIr text format v1
module "k"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
"""

# ---- TRACK B (i32 accumulator over i8/i16 elements) ----
def widen_tir(ety, ext, pop):
    popline = "    %17 = ctpop i32 %13\n" if pop else ""
    term = "17" if pop else "13"
    return HDR + f"""functy.0 = (ptr, i32) -> (i32)
fn @kernel(functy.0) {{
bb0(%1: ptr, %2: i32):
    %3 = const i32 0
    %4 = const i32 1
    %5 = const i32 0
    br bb1(%3, %5)
bb1(%6: i32, %7: i32):
    %8 = icmp slt i32 %6, %2
    condbr %8, bb3(%6, %7), bb2(%7)
bb3(%9: i32, %10: i32):
    %11 = gep {ety}, ptr %1, %9
    %12 = load {ety}, ptr %11
    %13 = {ext} {ety} %12 to i32
{popline}    %14 = add i32 %10, %{term}
    %15 = add i32 %9, %4
    br bb1(%15, %14)
bb2(%16: i32):
    ret %16
}}
"""

# ---- TRACK A (i64) ----
def red64_tir(body, init_line="", init="3", next_="14"):
    return HDR + f"""functy.0 = (ptr, i64, i64) -> (i64)
fn @kernel(functy.0) {{
bb0(%1: ptr, %2: i64, %20: i64):
    %3 = const i64 0
    %4 = const i64 1
{init_line}    br bb1(%3, %{init})
bb1(%6: i64, %7: i64):
    %8 = icmp slt i64 %6, %2
    condbr %8, bb3(%6, %7), bb2(%7)
bb3(%9: i64, %10: i64):
    %11 = gep i64, ptr %1, %9
    %12 = load i64, ptr %11
{body}    %15 = add i64 %9, %4
    br bb1(%15, %{next_})
bb2(%16: i64):
    ret %16
}}
"""

MAP64_TIR = HDR + """functy.0 = (ptr, ptr, i64) -> (i64)
fn @kernel(functy.0) {
; #param_attrs 0: noalias
; #param_attrs 1: noalias
bb0(%1: ptr, %30: ptr, %2: i64):
    %3 = const i64 0
    %4 = const i64 1
    %21 = const i64 7
    br bb1(%3)
bb1(%6: i64):
    %8 = icmp slt i64 %6, %2
    condbr %8, bb3(%6), bb2
bb3(%9: i64):
    %11 = gep i64, ptr %30, %9
    %12 = load i64, ptr %11
    %13 = add i64 %12, %21
    %18 = gep i64, ptr %1, %9
    store i64 %13, ptr %18
    %15 = add i64 %9, %4
    br bb1(%15)
bb2:
    ret %3
}
"""

KERNELS = {
    # name: (tir, C kernel text, kind)  kind: b8/b16 = TRACK B; r64; m64
    "sum_i8z": (widen_tir("i8", "zext", False),
        "uint32_t kernel(uint8_t* a, int n){uint32_t s=0;for(int i=0;i<n;i++)s+=(uint32_t)a[i];return s;}", "b8"),
    "sum_i8s": (widen_tir("i8", "sext", False),
        "uint32_t kernel(int8_t* a, int n){uint32_t s=0;for(int i=0;i<n;i++)s+=(uint32_t)(int32_t)a[i];return s;}", "b8"),
    "sum_i16z": (widen_tir("i16", "zext", False),
        "uint32_t kernel(uint16_t* a, int n){uint32_t s=0;for(int i=0;i<n;i++)s+=(uint32_t)a[i];return s;}", "b16"),
    "sum_i16s": (widen_tir("i16", "sext", False),
        "uint32_t kernel(int16_t* a, int n){uint32_t s=0;for(int i=0;i<n;i++)s+=(uint32_t)(int32_t)a[i];return s;}", "b16"),
    "pop_i8": (widen_tir("i8", "zext", True),
        "uint32_t kernel(uint8_t* a, int n){uint32_t s=0;for(int i=0;i<n;i++)s+=(uint32_t)__builtin_popcount((uint32_t)a[i]);return s;}", "b8"),
    "ceq_i64": (red64_tir("    %13 = icmp eq i64 %12, %20\n    %17 = select i64 %13, %4, %3\n    %14 = add i64 %10, %17\n"),
        "uint64_t kernel(uint64_t* a, int64_t n, uint64_t k){uint64_t s=0;for(int64_t i=0;i<n;i++)s+=(a[i]==k)?1:0;return s;}", "r64"),
    "smax_i64": (red64_tir("    %13 = icmp sgt i64 %12, %10\n    %14 = select i64 %13, %12, %10\n",
                           init_line="    %6x = const i64 -9223372036854775808\n".replace("%6x", "%60"), init="60"),
        "uint64_t kernel(uint64_t* a, int64_t n, uint64_t k){(void)k;int64_t m=INT64_MIN;for(int64_t i=0;i<n;i++)m=((int64_t)a[i]>m)?(int64_t)a[i]:m;return (uint64_t)m;}", "r64"),
    "umin_i64": (red64_tir("    %13 = icmp ult i64 %12, %10\n    %14 = select i64 %13, %12, %10\n",
                           init_line="    %60 = const i64 -1\n", init="60"),
        "uint64_t kernel(uint64_t* a, int64_t n, uint64_t k){(void)k;uint64_t m=UINT64_MAX;for(int64_t i=0;i<n;i++)m=(a[i]<m)?a[i]:m;return m;}", "r64"),
    "xor_i64": (red64_tir("    %14 = xor i64 %10, %12\n"),
        "uint64_t kernel(uint64_t* a, int64_t n, uint64_t k){(void)k;uint64_t s=0;for(int64_t i=0;i<n;i++)s^=a[i];return s;}", "r64"),
    "prod_i64": (red64_tir("    %14 = mul i64 %10, %12\n", init_line="    %60 = const i64 1\n", init="60"),
        "uint64_t kernel(uint64_t* a, int64_t n, uint64_t k){(void)k;uint64_t s=1;for(int64_t i=0;i<n;i++)s*=a[i];return s;}", "r64"),
    "map_i64": (MAP64_TIR,
        "uint64_t kernel(uint64_t* restrict a, uint64_t* restrict b, int64_t n){for(int64_t i=0;i<n;i++)a[i]=b[i]+7;return 0;}", "m64"),
}

DRIVER = """#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#define N %dLL
%s
static double now_ms(void){struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);return ts.tv_sec*1e3+ts.tv_nsec/1e6;}
int main(void){
  %s
  volatile uint64_t sink = 0;
  sink += CALL; /* warm-up */
  double best = 1e18;
  for (int it = 0; it < 11; it++){
    double t0 = now_ms();
    uint64_t s = CALL;
    double t1 = now_ms();
    sink += s;
    if (t1 - t0 < best) best = t1 - t0;
  }
  printf("%%llu %%.3f\\n", (unsigned long long)(uint64_t)CALL, best);
  return 0;
}
"""

SETUP = {
    "b8": ("extern uint32_t kernel(void*, int);",
           """uint8_t* a = malloc(N);
  uint32_t r = 0x9e3779b9u;
  for (long i = 0; i < N; i++){ r = r*1664525u + 1013904223u; a[i] = (uint8_t)(r >> 13); }
#define CALL (uint64_t)kernel(a, (int)N)"""),
    "b16": ("extern uint32_t kernel(void*, int);",
            """uint16_t* a = malloc(N*2);
  uint32_t r = 0x9e3779b9u;
  for (long i = 0; i < N; i++){ r = r*1664525u + 1013904223u; a[i] = (uint16_t)(r >> 9); }
#define CALL (uint64_t)kernel(a, (int)N)"""),
    "r64": ("extern uint64_t kernel(void*, int64_t, uint64_t);",
            """uint64_t* a = malloc(N*8);
  uint64_t r = 88172645463325252ull;
  for (long i = 0; i < N; i++){ r ^= r<<13; r ^= r>>7; r ^= r<<17; a[i] = r; }
  a[N/2] = 42; /* one hit for count-eq */
#define CALL kernel(a, N, 42)"""),
    "m64": ("extern uint64_t kernel(void*, void*, int64_t);",
            """uint64_t* a = malloc(N*8); uint64_t* b = malloc(N*8);
  uint64_t r = 88172645463325252ull;
  for (long i = 0; i < N; i++){ r ^= r<<13; r ^= r>>7; r ^= r<<17; b[i] = r; a[i] = 0; }
#define CALL (kernel(a, b, N), (uint64_t)a[N-1])"""),
}

def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

def main():
    tcg = sys.argv[1]
    wanted = sys.argv[2:] or list(KERNELS)
    wd = tempfile.mkdtemp(prefix="widebench_")
    print(f"workdir {wd}")
    rows = []
    for name in wanted:
        tir_text, ck, kind = KERNELS[name]
        t = os.path.join(wd, name + ".trust_ir"); open(t, "w").write(tir_text)
        c = os.path.join(wd, name + ".c")
        open(c, "w").write("#include <stdint.h>\n" + ck + "\n")
        ext_decl, setup = SETUP[kind]
        d = os.path.join(wd, name + "_drv.c")
        open(d, "w").write(DRIVER % (N, ext_decl, setup))
        on_o, off_o, cl_o = [os.path.join(wd, name + x) for x in ("_on.o", "_off.o", "_cl.o")]
        env = dict(os.environ)
        r = run([tcg, "--format=text", "--target", "aarch64", "-O2", "-c", t, "-o", on_o], env=env)
        assert r.returncode == 0, r.stderr
        envoff = dict(os.environ)
        envoff["TRUST_CG_DISABLE_PASSES"] = "neon_predsum,neon_minmax,neon_map,neon_array"
        assert run([tcg, "--format=text", "--target", "aarch64", "-O2", "-c", t, "-o", off_o], env=envoff).returncode == 0
        assert run(["cc", "-O3", "-c", c, "-o", cl_o]).returncode == 0
        bins = {}
        for tag, obj in (("after", on_o), ("before", off_o), ("clang", cl_o)):
            bp = os.path.join(wd, name + "_" + tag)
            assert run(["cc", "-O2", d, obj, "-o", bp]).returncode == 0
            bins[tag] = bp
        best = {tag: 1e18 for tag in bins}
        csum = {}
        for rep in range(3):  # interleaved process reps; each = in-process best-of-11
            for tag, bp in bins.items():
                out = run([bp]).stdout.split()
                csum[tag] = out[0]
                best[tag] = min(best[tag], float(out[1]))
        agree = csum["after"] == csum["before"] == csum["clang"]
        ratio_before = best["before"] / best["clang"]
        ratio_after = best["after"] / best["clang"]
        verdict = ("WIN" if ratio_after < 0.97 else "TIE" if ratio_after <= 1.05 else
                   f"behind {ratio_after:.2f}x")
        rows.append((name, best["before"], best["after"], best["clang"],
                     ratio_before, ratio_after, verdict, agree))
        print(f"{name:9s} before={best['before']:8.3f}ms after={best['after']:8.3f}ms "
              f"clang={best['clang']:8.3f}ms  before/clang={ratio_before:5.1f}x "
              f"after/clang={ratio_after:4.2f}x  {verdict}  bit-identical={agree}")
    print("\n| kernel | before (scalar) | after (vectorized) | clang -O3 | before/clang | after/clang | verdict |")
    print("|---|---|---|---|---|---|---|")
    for (name, b, a, c, rb, ra, v, agree) in rows:
        print(f"| {name} | {b:.2f} ms | {a:.2f} ms | {c:.2f} ms | {rb:.1f}x | {ra:.2f}x | {v}{'' if agree else ' (CHECKSUM MISMATCH!)'} |")

if __name__ == "__main__":
    main()
