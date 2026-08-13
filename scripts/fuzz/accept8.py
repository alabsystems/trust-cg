#!/usr/bin/env python3
"""Acceptance benchmark: 8 kernels, trust-cg -O3 vs clang -O3.
INTERLEAVED best-of-15 in ONE process per kernel; asserts bit-identical results.
usage: accept8.py <trust-cg-cli-binary>
"""
import sys, os, subprocess, tempfile

TCG = sys.argv[1]

HDR = '; TrustIr text format v1\nmodule "m"\ntarget "aarch64-apple-darwin" 8 little abi="aapcs64"\n'

KERNELS = {}

# ---------------- 1. callloop: s = ext2(i, s) ----------------
KERNELS['callloop'] = dict(
    tir=HDR + """functy.0 = (i32, i32) -> (i32)
functy.1 = (i32) -> (i32)
external fn @ext2(functy.0) {}
fn @kernel(functy.1) {
bb0(%0: i32):
    %1 = const i32 0
    %2 = const i32 1
    br bb1(%1, %1)
bb1(%5: i32, %6: i32):
    %7 = icmp slt i32 %5, %0
    condbr %7, bb3(%5, %6), bb2(%6)
bb3(%8: i32, %9: i32):
    %10 = call @func.0(%8, %9)
    %11 = add i32 %8, %2
    br bb1(%11, %10)
bb2(%14: i32):
    ret %14
}
""",
    ref_c="""#include <stdint.h>
extern int32_t ext2(int32_t,int32_t);
int32_t ref_kernel(int32_t n){int32_t s=0;for(int32_t i=0;i<n;i++)s=ext2(i,s);return s;}
""",
    extra_c="""#include <stdint.h>
int32_t ext2(int32_t i, int32_t s){uint32_t ui=(uint32_t)i,us=(uint32_t)s;return (int32_t)(us+ui*ui-(ui^us));}
""",
    driver_kind='scalar_n', N=30000000)

# ---------------- 2. ptrchase: idx = a[idx] ----------------
KERNELS['ptrchase'] = dict(
    tir=HDR + """functy.0 = (ptr, i32, i32) -> (i32)
fn @kernel(functy.0) {
bb0(%0: ptr, %1: i32, %2: i32):
    %3 = const i32 0
    %4 = const i32 1
    br bb1(%3, %1)
bb1(%5: i32, %6: i32):
    %7 = icmp slt i32 %5, %2
    condbr %7, bb3(%5, %6), bb2(%6)
bb3(%8: i32, %9: i32):
    %10 = gep i32, ptr %0, %9
    %11 = load i32, ptr %10
    %12 = add i32 %8, %4
    br bb1(%12, %11)
bb2(%14: i32):
    ret %14
}
""",
    ref_c="""#include <stdint.h>
int32_t ref_kernel(int32_t* a, int32_t idx, int32_t n){for(int32_t k=0;k<n;k++)idx=a[idx];return idx;}
""",
    driver_kind='chase', N=30000000, M=1 << 14)

# ---------------- 3. bsearch: sum of lower_bound over q queries ----------------
KERNELS['bsearch'] = dict(
    tir=HDR + """functy.0 = (ptr, i32, i32) -> (i32)
fn @kernel(functy.0) {
bb0(%0: ptr, %1: i32, %2: i32):
    %3 = const i32 0
    %4 = const i32 1
    %5 = const i32 1664525
    %6 = const i32 1013904223
    %7 = const i32 131071
    br bb1(%3, %3, %6)
bb1(%10: i32, %11: i32, %12: i32):
    %13 = icmp slt i32 %10, %2
    condbr %13, bb3(%10, %11, %12), bb2(%11)
bb3(%20: i32, %21: i32, %22: i32):
    %23 = mul i32 %22, %5
    %24 = add i32 %23, %6
    %25 = and i32 %24, %7
    br bb4(%3, %1, %20, %21, %24, %25)
bb4(%30: i32, %31: i32, %32: i32, %33: i32, %34: i32, %35: i32):
    %36 = icmp slt i32 %30, %31
    condbr %36, bb5(%30, %31, %32, %33, %34, %35), bb6(%30, %32, %33, %34)
bb5(%40: i32, %41: i32, %42: i32, %43: i32, %44: i32, %45: i32):
    %46 = add i32 %40, %41
    %47 = lshr i32 %46, %4
    %48 = gep i32, ptr %0, %47
    %49 = load i32, ptr %48
    %50 = icmp slt i32 %49, %45
    %51 = add i32 %47, %4
    %52 = select i32 %50, %51, %40
    %53 = select i32 %50, %41, %47
    br bb4(%52, %53, %42, %43, %44, %45)
bb6(%60: i32, %61: i32, %62: i32, %63: i32):
    %64 = add i32 %62, %60
    %65 = add i32 %61, %4
    br bb1(%65, %64, %63)
bb2(%70: i32):
    ret %70
}
""",
    ref_c="""#include <stdint.h>
int32_t ref_kernel(int32_t* a, int32_t n, int32_t q){
  int32_t s=0; uint32_t seed=1013904223u;
  for(int32_t j=0;j<q;j++){
    seed = seed*1664525u+1013904223u;
    int32_t key=(int32_t)(seed & 131071u);
    int32_t lo=0, hi=n;
    while(lo<hi){ int32_t mid=(int32_t)(((uint32_t)(lo+hi))>>1);
      if(a[mid]<key) lo=mid+1; else hi=mid; }
    s += lo;
  }
  return s;
}
""",
    driver_kind='bsearch', N=2000000, M=1 << 16)

# ---------------- 4. prefix-sum: run += a[i]; o[i]=run ----------------
KERNELS['prefix-sum'] = dict(
    tir=HDR + """functy.0 = (ptr, ptr, i32) -> (i32)
fn @kernel(functy.0) {
bb0(%0: ptr, %1: ptr, %2: i32):
    %3 = const i32 0
    %4 = const i32 1
    br bb1(%3, %3)
bb1(%5: i32, %6: i32):
    %7 = icmp slt i32 %5, %2
    condbr %7, bb3(%5, %6), bb2(%6)
bb3(%8: i32, %9: i32):
    %10 = gep i32, ptr %1, %8
    %11 = load i32, ptr %10
    %12 = add i32 %9, %11
    %13 = gep i32, ptr %0, %8
    store i32 %12, ptr %13
    %14 = add i32 %8, %4
    br bb1(%14, %12)
bb2(%20: i32):
    ret %20
}
""",
    ref_c="""#include <stdint.h>
int32_t ref_kernel(int32_t* o, int32_t* a, int32_t n){
  int32_t run=0; for(int32_t i=0;i<n;i++){ run+=a[i]; o[i]=run; } return run; }
""",
    driver_kind='arr_out', N=20000000)

# ---------------- 5. fib: (a,b) = (b, a+b) ----------------
KERNELS['fib'] = dict(
    tir=HDR + """functy.0 = (i32) -> (i32)
fn @kernel(functy.0) {
bb0(%0: i32):
    %1 = const i32 0
    %2 = const i32 1
    br bb1(%1, %1, %2)
bb1(%5: i32, %6: i32, %7: i32):
    %8 = icmp slt i32 %5, %0
    condbr %8, bb3(%5, %6, %7), bb2(%6)
bb3(%10: i32, %11: i32, %12: i32):
    %13 = add i32 %11, %12
    %14 = add i32 %10, %2
    br bb1(%14, %12, %13)
bb2(%20: i32):
    ret %20
}
""",
    ref_c="""#include <stdint.h>
int32_t ref_kernel(int32_t n){
  uint32_t a=0,b=1; for(int32_t i=0;i<n;i++){ uint32_t t=a+b; a=b; b=t; } return (int32_t)a; }
""",
    driver_kind='scalar_n', N=300000000)

# ---------------- 6. i32 sum: s += a[i] ----------------
KERNELS['i32sum'] = dict(
    tir=HDR + """functy.0 = (ptr, i32) -> (i32)
fn @kernel(functy.0) {
bb0(%0: ptr, %1: i32):
    %2 = const i32 0
    %3 = const i32 1
    br bb1(%2, %2)
bb1(%5: i32, %6: i32):
    %7 = icmp slt i32 %5, %1
    condbr %7, bb3(%5, %6), bb2(%6)
bb3(%8: i32, %9: i32):
    %10 = gep i32, ptr %0, %8
    %11 = load i32, ptr %10
    %12 = add i32 %9, %11
    %13 = add i32 %8, %3
    br bb1(%13, %12)
bb2(%14: i32):
    ret %14
}
""",
    ref_c="""#include <stdint.h>
int32_t ref_kernel(int32_t* a, int32_t n){int32_t s=0;for(int32_t i=0;i<n;i++)s+=a[i];return s;}
""",
    driver_kind='arr_in', N=20000000)

# ---------------- 7. NEON kernel: s += (i*i)^(i*3) ----------------
KERNELS['neon-mix'] = dict(
    tir=HDR + """functy.0 = (i32) -> (i32)
fn @kernel(functy.0) {
bb0(%0: i32):
    %1 = const i32 0
    %2 = const i32 1
    %3 = const i32 3
    br bb1(%1, %1)
bb1(%5: i32, %6: i32):
    %7 = icmp slt i32 %5, %0
    condbr %7, bb3(%5, %6), bb2(%6)
bb3(%8: i32, %9: i32):
    %10 = mul i32 %8, %8
    %11 = mul i32 %8, %3
    %12 = xor i32 %10, %11
    %13 = add i32 %9, %12
    %14 = add i32 %8, %2
    br bb1(%14, %13)
bb2(%20: i32):
    ret %20
}
""",
    ref_c="""#include <stdint.h>
int32_t ref_kernel(int32_t n){
  uint32_t s=0; for(uint32_t i=0;i<(uint32_t)n;i++) s += (i*i)^(i*3u); return (int32_t)s; }
""",
    driver_kind='scalar_n', N=1000000000)

# ---------------- 8. fsum: f32 sequential sum ----------------
KERNELS['fsum'] = dict(
    tir=HDR + """functy.0 = (ptr, i32) -> (f32)
fn @kernel(functy.0) {
bb0(%0: ptr, %1: i32):
    %2 = const i32 0
    %3 = const i32 1
    %4 = const f32 0.0
    br bb1(%2, %4)
bb1(%5: i32, %6: f32):
    %7 = icmp slt i32 %5, %1
    condbr %7, bb3(%5, %6), bb2(%6)
bb3(%8: i32, %9: f32):
    %10 = gep f32, ptr %0, %8
    %11 = load f32, ptr %10
    %12 = fadd f32 %9, %11
    %13 = add i32 %8, %3
    br bb1(%13, %12)
bb2(%14: f32):
    ret %14
}
""",
    ref_c="""#include <stdint.h>
float ref_kernel(float* a, int32_t n){float s=0.0f;for(int32_t i=0;i<n;i++)s+=a[i];return s;}
""",
    driver_kind='fsum', N=20000000)

COMMON = r"""
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
static double now_ms(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
    return t.tv_sec*1000.0 + t.tv_nsec/1e6; }
#define REPS 15
"""

DRIVERS = {
    'scalar_n': COMMON + r"""
extern int32_t kernel(int32_t);
extern int32_t ref_kernel(int32_t);
int main(void){
    int32_t N = %(N)d;
    int32_t a = kernel(N), b = ref_kernel(N);
    if(a!=b){ printf("MISMATCH tcg=%%d clang=%%d\n", a, b); return 1; }
    double bt=1e18, bc=1e18;
    for(int r=0;r<REPS;r++){
        double t0=now_ms(); volatile int32_t x=kernel(N);     double t1=now_ms();
        double c0=now_ms(); volatile int32_t y=ref_kernel(N); double c1=now_ms();
        if((int32_t)x!=a||(int32_t)y!=b){ printf("MISMATCH-REP\n"); return 1; }
        if(t1-t0<bt) bt=t1-t0; if(c1-c0<bc) bc=c1-c0;
    }
    printf("RESULT tcg=%%.2f clang=%%.2f ratio=%%.3f val=%%d\n", bt, bc, bt/bc, a);
    return 0;
}
""",
    'chase': COMMON + r"""
extern int32_t kernel(int32_t*, int32_t, int32_t);
extern int32_t ref_kernel(int32_t*, int32_t, int32_t);
int main(void){
    int32_t N = %(N)d, M = %(M)d;
    int32_t* a = malloc(sizeof(int32_t)*(size_t)M);
    /* random permutation cycle: Sattolo */
    for(int32_t i=0;i<M;i++) a[i]=i;
    uint32_t s=88172645u;
    for(int32_t i=M-1;i>0;i--){ s^=s<<13;s^=s>>17;s^=s<<5; int32_t j=(int32_t)(s%%(uint32_t)i);
        int32_t t=a[i];a[i]=a[j];a[j]=t; }
    int32_t va = kernel(a, 0, N), vb = ref_kernel(a, 0, N);
    if(va!=vb){ printf("MISMATCH tcg=%%d clang=%%d\n", va, vb); return 1; }
    double bt=1e18, bc=1e18;
    for(int r=0;r<REPS;r++){
        double t0=now_ms(); volatile int32_t x=kernel(a,0,N);     double t1=now_ms();
        double c0=now_ms(); volatile int32_t y=ref_kernel(a,0,N); double c1=now_ms();
        if((int32_t)x!=va||(int32_t)y!=vb){ printf("MISMATCH-REP\n"); return 1; }
        if(t1-t0<bt) bt=t1-t0; if(c1-c0<bc) bc=c1-c0;
    }
    printf("RESULT tcg=%%.2f clang=%%.2f ratio=%%.3f val=%%d\n", bt, bc, bt/bc, va);
    return 0;
}
""",
    'bsearch': COMMON + r"""
extern int32_t kernel(int32_t*, int32_t, int32_t);
extern int32_t ref_kernel(int32_t*, int32_t, int32_t);
int main(void){
    int32_t Q = %(N)d, M = %(M)d;
    int32_t* a = malloc(sizeof(int32_t)*(size_t)M);
    for(int32_t i=0;i<M;i++) a[i]=2*i;
    int32_t va = kernel(a, M, Q), vb = ref_kernel(a, M, Q);
    if(va!=vb){ printf("MISMATCH tcg=%%d clang=%%d\n", va, vb); return 1; }
    double bt=1e18, bc=1e18;
    for(int r=0;r<REPS;r++){
        double t0=now_ms(); volatile int32_t x=kernel(a,M,Q);     double t1=now_ms();
        double c0=now_ms(); volatile int32_t y=ref_kernel(a,M,Q); double c1=now_ms();
        if((int32_t)x!=va||(int32_t)y!=vb){ printf("MISMATCH-REP\n"); return 1; }
        if(t1-t0<bt) bt=t1-t0; if(c1-c0<bc) bc=c1-c0;
    }
    printf("RESULT tcg=%%.2f clang=%%.2f ratio=%%.3f val=%%d\n", bt, bc, bt/bc, va);
    return 0;
}
""",
    'arr_in': COMMON + r"""
extern int32_t kernel(int32_t*, int32_t);
extern int32_t ref_kernel(int32_t*, int32_t);
int main(void){
    int32_t N = %(N)d;
    int32_t* a = malloc(sizeof(int32_t)*(size_t)N);
    uint32_t s=2463534242u;
    for(int32_t i=0;i<N;i++){ s^=s<<13;s^=s>>17;s^=s<<5; a[i]=(int32_t)s; }
    int32_t va = kernel(a, N), vb = ref_kernel(a, N);
    if(va!=vb){ printf("MISMATCH tcg=%%d clang=%%d\n", va, vb); return 1; }
    double bt=1e18, bc=1e18;
    for(int r=0;r<REPS;r++){
        double t0=now_ms(); volatile int32_t x=kernel(a,N);     double t1=now_ms();
        double c0=now_ms(); volatile int32_t y=ref_kernel(a,N); double c1=now_ms();
        if((int32_t)x!=va||(int32_t)y!=vb){ printf("MISMATCH-REP\n"); return 1; }
        if(t1-t0<bt) bt=t1-t0; if(c1-c0<bc) bc=c1-c0;
    }
    printf("RESULT tcg=%%.2f clang=%%.2f ratio=%%.3f val=%%d\n", bt, bc, bt/bc, va);
    return 0;
}
""",
    'arr_out': COMMON + r"""
extern int32_t kernel(int32_t*, int32_t*, int32_t);
extern int32_t ref_kernel(int32_t*, int32_t*, int32_t);
static uint64_t hash_arr(int32_t* o, int32_t n){
    uint64_t h=1469598103934665603ull;
    for(int32_t i=0;i<n;i++){ h^=(uint32_t)o[i]; h*=1099511628211ull; } return h; }
int main(void){
    int32_t N = %(N)d;
    int32_t* a = malloc(sizeof(int32_t)*(size_t)N);
    int32_t* o1 = malloc(sizeof(int32_t)*(size_t)N);
    int32_t* o2 = malloc(sizeof(int32_t)*(size_t)N);
    uint32_t s=2463534242u;
    for(int32_t i=0;i<N;i++){ s^=s<<13;s^=s>>17;s^=s<<5; a[i]=(int32_t)s; }
    int32_t va = kernel(o1, a, N), vb = ref_kernel(o2, a, N);
    uint64_t h1=hash_arr(o1,N), h2=hash_arr(o2,N);
    if(va!=vb||h1!=h2){ printf("MISMATCH\n"); return 1; }
    double bt=1e18, bc=1e18;
    for(int r=0;r<REPS;r++){
        double t0=now_ms(); volatile int32_t x=kernel(o1,a,N);     double t1=now_ms();
        double c0=now_ms(); volatile int32_t y=ref_kernel(o2,a,N); double c1=now_ms();
        if((int32_t)x!=va||(int32_t)y!=vb){ printf("MISMATCH-REP\n"); return 1; }
        if(t1-t0<bt) bt=t1-t0; if(c1-c0<bc) bc=c1-c0;
    }
    if(hash_arr(o1,N)!=hash_arr(o2,N)){ printf("MISMATCH-ARR\n"); return 1; }
    printf("RESULT tcg=%%.2f clang=%%.2f ratio=%%.3f val=%%d\n", bt, bc, bt/bc, va);
    return 0;
}
""",
    'fsum': COMMON + r"""
extern float kernel(float*, int32_t);
extern float ref_kernel(float*, int32_t);
int main(void){
    int32_t N = %(N)d;
    float* a = malloc(sizeof(float)*(size_t)N);
    uint32_t s=2463534242u;
    for(int32_t i=0;i<N;i++){ s^=s<<13;s^=s>>17;s^=s<<5;
        a[i]=(float)((int32_t)(s %% 2000001u) - 1000000) * 0.001f; }
    float va = kernel(a, N), vb = ref_kernel(a, N);
    uint32_t ba, bb; memcpy(&ba,&va,4); memcpy(&bb,&vb,4);
    if(ba!=bb){ printf("MISMATCH tcg=%%08x clang=%%08x\n", ba, bb); return 1; }
    double bt=1e18, bc=1e18;
    for(int r=0;r<REPS;r++){
        double t0=now_ms(); volatile float x=kernel(a,N);     double t1=now_ms();
        double c0=now_ms(); volatile float y=ref_kernel(a,N); double c1=now_ms();
        (void)x;(void)y;
        if(t1-t0<bt) bt=t1-t0; if(c1-c0<bc) bc=c1-c0;
    }
    printf("RESULT tcg=%%.2f clang=%%.2f ratio=%%.3f val=%%08x\n", bt, bc, bt/bc, ba);
    return 0;
}
""",
}


def run_kernel(name, spec, wd):
    tir = os.path.join(wd, f"{name}.trust_ir")
    open(tir, "w").write(spec['tir'])
    obj = os.path.join(wd, f"{name}.o")
    r = subprocess.run([TCG, "--format=text", "--target", "aarch64", "-O3",
                        "-c", tir, "-o", obj], capture_output=True, text=True)
    if r.returncode != 0:
        print(f"{name}: COMPILE FAIL\n{r.stderr[-2000:]}")
        return False
    ref_c = os.path.join(wd, f"{name}_ref.c")
    open(ref_c, "w").write(spec['ref_c'])
    drv_c = os.path.join(wd, f"{name}_drv.c")
    open(drv_c, "w").write(DRIVERS[spec['driver_kind']] % spec)
    binp = os.path.join(wd, f"{name}_bin")
    cc = ["cc", "-O3", drv_c, ref_c, obj, "-o", binp]
    if 'extra_c' in spec:
        ex = os.path.join(wd, f"{name}_extra.c")
        open(ex, "w").write(spec['extra_c'])
        cc.insert(4, ex)
    r = subprocess.run(cc, capture_output=True, text=True)
    if r.returncode != 0:
        print(f"{name}: LINK FAIL\n{r.stderr[-2000:]}")
        return False
    r = subprocess.run([binp], capture_output=True, text=True)
    out = r.stdout.strip()
    print(f"{name:12s} {out}" + ("" if r.returncode == 0 else f"  EXIT={r.returncode}"))
    return r.returncode == 0 and out.startswith("RESULT")


def main():
    wd = tempfile.mkdtemp(prefix="accept8_")
    ok = True
    for name, spec in KERNELS.items():
        ok &= run_kernel(name, spec, wd)
    print("ACCEPT8: " + ("ALL OK" if ok else "FAILURES"))
    sys.exit(0 if ok else 1)


main()
