#!/usr/bin/env python3
# Interleaved best-of-15 argmin/argmax (index-tracking) benchmark:
#   * tcg-on  : trust-cg -O3 (neon-minmax argmin path FIRES)
#   * tcg-off : trust-cg -O3 with neon-minmax DISABLED (the honest scalar before)
#   * clang   : clang -O3 (stays SCALAR — its cost model refuses the NEON argmin)
# All three binaries must agree on the result index before timing counts.
# usage: bench_argmin.py <trust-cg> [N] [variant]
#        variant in argmin_s/argmax_s/argmin_u/argmax_u (i32, .4S)
#                or argmin_s64/argmax_s64/argmin_u64/argmax_u64 (i64, .2D)
import sys, os, subprocess, tempfile

TCG = sys.argv[1]
VARIANT = sys.argv[3] if len(sys.argv) > 3 else "argmin_s"
REPS = 15

SPEC = {
    'argmin_s': ('slt', '2147483647', 'int', '2147483647', '<'),
    'argmax_s': ('sgt', '-2147483648', 'int', '(-2147483647-1)', '>'),
    'argmin_u': ('ult', '4294967295', 'unsigned', '4294967295u', '<'),
    'argmax_u': ('ugt', '0', 'unsigned', '0u', '>'),
    'argmin_s64': ('slt', '9223372036854775807', 'int64_t',
                   '9223372036854775807LL', '<'),
    'argmax_s64': ('sgt', '-9223372036854775808', 'int64_t',
                   '(-9223372036854775807LL-1)', '>'),
    'argmin_u64': ('ult', '-1', 'uint64_t', '0xFFFFFFFFFFFFFFFFULL', '<'),
    'argmax_u64': ('ugt', '0', 'uint64_t', '0ULL', '>'),
}
icmp, seed, cty, cseed, cop = SPEC[VARIANT]
IS64 = VARIANT.endswith('64')
ETY = 'i64' if IS64 else 'i32'
ELEM_C = 'int64_t' if IS64 else 'int'
N = int(sys.argv[2]) if len(sys.argv) > 2 else (10_000_000 if IS64 else 20_000_000)

wd = tempfile.mkdtemp(prefix="benchargmin_")
tir = os.path.join(wd, "k.trust_ir")
open(tir, "w").write(f"""; TrustIr text format v1
module "am"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, {ETY}) -> ({ETY})
fn @argmin_kernel(functy.0){{
bb0(%0: ptr,%1: {ETY}):
 %2=const {ETY} {seed}
 %3=const {ETY} 0
 %4=const {ETY} 1
 br bb1(%3,%2,%3)
bb1(%10: {ETY},%11: {ETY},%12: {ETY}):
 %13=icmp slt {ETY} %10,%1
 condbr %13,bb3(%10,%11,%12),bb2(%12)
bb3(%20: {ETY},%21: {ETY},%22: {ETY}):
 %23=gep {ETY},ptr %0,%20
 %24=load {ETY},ptr %23
 %25=icmp {icmp} {ETY} %24,%21
 %26=select {ETY} %25,%24,%21
 %27=select {ETY} %25,%20,%22
 %28=add {ETY} %20,%4
 br bb1(%28,%26,%27)
bb2(%40: {ETY}): ret %40
}}
""")
objs = {}
for tag, disable in (("on", None), ("off", "neon_minmax")):
    o = os.path.join(wd, f"t_{tag}.o")
    env = dict(os.environ)
    if disable:
        env["TRUST_CG_DISABLE_PASSES"] = disable
    r = subprocess.run([TCG, "--format=text", "--target", "aarch64", "-O3",
                        "-c", tir, "-o", o], capture_output=True, text=True, env=env)
    assert r.returncode == 0, "trust-cg compile failed:\n" + r.stderr[-2000:]
    objs[tag] = o

cref = os.path.join(wd, "c.c")
open(cref, "w").write(f"""
#include <stdint.h>
{ELEM_C} argmin_kernel(const {ELEM_C}* a, {ELEM_C} n){{
    {cty} bv = {cseed}; {ELEM_C} bi = 0;
    for ({ELEM_C} i = 0; i < n; i++) {{ {cty} v = ({cty})a[i]; if (v {cop} bv) {{ bv = v; bi = i; }} }}
    return bi;
}}
""")
cobj = os.path.join(wd, "c.o")
subprocess.run(["clang", "-O3", "-c", cref, "-o", cobj], check=True)
objs["clang"] = cobj

drv = os.path.join(wd, "drv.c")
open(drv, "w").write(f"""
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
extern {ELEM_C} argmin_kernel(const {ELEM_C}* a, {ELEM_C} n);
static double now_ms(void){{ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts);
  return ts.tv_sec*1000.0 + ts.tv_nsec/1e6; }}
int main(int argc, char**argv){{
  long N=atol(argv[1]); int REPS=atoi(argv[2]);
  {ELEM_C}* a=malloc(sizeof({ELEM_C})*(size_t)N);
  uint64_t s=88172645463325252ull;
  for(long i=0;i<N;i++){{ s^=s<<13; s^=s>>7; s^=s<<17; a[i]=({ELEM_C})s; }}
  volatile long res = (long)argmin_kernel(a,({ELEM_C})N);
  double best=1e30;
  for(int r=0;r<REPS;r++){{ double t0=now_ms(); res=(long)argmin_kernel(a,({ELEM_C})N);
    double dt=now_ms()-t0; if(dt<best)best=dt; }}
  printf("%.3f %ld\\n", best, (long)res);
  return 0;
}}
""")
bins = {}
for tag, o in objs.items():
    b = os.path.join(wd, tag)
    subprocess.run(["clang", "-O2", drv, o, "-o", b], check=True)
    bins[tag] = b
best = {t: 1e30 for t in bins}
res = {}
for _ in range(REPS):
    for tag in bins:
        out = subprocess.run([bins[tag], str(N), str(REPS)],
                             capture_output=True, text=True).stdout.split()
        best[tag] = min(best[tag], float(out[0]))
        res.setdefault(tag, out[1])
assert len(set(res.values())) == 1, f"RESULT MISMATCH {res}"
sp_off = best["off"] / best["on"]
sp_clang = best["clang"] / best["on"]
verdict = "WIN" if min(sp_off, sp_clang) >= 1.7 else \
          ("tie/small-win" if min(sp_off, sp_clang) >= 1.05 else
           ("TIE" if min(sp_off, sp_clang) >= 0.95 else "BEHIND"))
print(f"{VARIANT} N={N} on={best['on']:.2f}ms off(scalar)={best['off']:.2f}ms "
      f"clang={best['clang']:.2f}ms speedup(off/on)={sp_off:.3f}x "
      f"speedup(clang/on)={sp_clang:.3f}x resultid={res['on']} => {verdict}")
