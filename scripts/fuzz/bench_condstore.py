#!/usr/bin/env python3
# DORMANT conditional-store benchmark asset.
#
# The blind-store transform now requires validator-issued authority bound to
# the exact function, output base, and byte range. No CLI carrier exists yet;
# `TRUST_CG_CONDSTORE=blind` is deliberately non-authoritative and production
# keeps the pass inert. This script must not report an on/off speedup until it
# is rewired to supply that typed capability.
#
# Historical comparison shape:
#   * tcg-on  : trust-cg -O2 with typed ownership authority (not yet wired)
#   * tcg-off : same input, pass disabled
#   * clang   : clang -O3 (scalarises this class — C11 forbids inventing the
#               store, NEON has no masked store)
# The kernel is `for i<n: if (a[i] > 0) b[i] = a[i] OP k` at the given
# predicate DENSITY. All three binaries must produce a bit-identical output
# array (FNV over poisoned b) before timing counts.
# usage: bench_condstore.py <trust-cg> [N] [variant] [density]
#        variant in cs_i32/cs_i64, density in 0..100 (default 50)
import sys, os, subprocess, tempfile

raise SystemExit(
    "bench_condstore.py is dormant: typed function/base/range ownership "
    "authority is not wired; TRUST_CG_CONDSTORE is not an authorization seam"
)

TCG = sys.argv[1]
VARIANT = sys.argv[3] if len(sys.argv) > 3 else "cs_i32"
DENS = int(sys.argv[4]) if len(sys.argv) > 4 else 50
REPS = 15

SPEC = {
    # (trust_ir ety, C ety, value op line, C value, default N)
    'cs_i32': ('i32', 'int32_t', "    %14 = mul i32 %12, %5\n", "a[i]*2", 20_000_000),
    'cs_i64': ('i64', 'int64_t', "    %14 = add i64 %12, %5\n", "a[i]+2", 10_000_000),
}
ety, cty, vline, cval, defn = SPEC[VARIANT]
N = int(sys.argv[2]) if len(sys.argv) > 2 else defn

wd = tempfile.mkdtemp(prefix="benchcs_")
tir = os.path.join(wd, "k.trust_ir")
open(tir, "w").write(f"""; TrustIr text format v1
module "k"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, ptr, {ety}) -> ({ety})
fn @kernel(functy.0) {{
; #param_attrs 0: noalias
; #param_attrs 1: noalias
bb0(%1: ptr, %30: ptr, %2: {ety}):
    %3 = const {ety} 0
    %4 = const {ety} 1
    %5 = const {ety} 2
    br bb1(%3)
bb1(%6: {ety}):
    %8 = icmp slt {ety} %6, %2
    condbr %8, bb3(%6), bb2
bb3(%9: {ety}):
    %11 = gep {ety}, ptr %30, %9
    %12 = load {ety}, ptr %11
    %13 = icmp sgt {ety} %12, %3
    condbr %13, bb4(%9), bb5(%9)
bb4(%40: {ety}):
{vline}    %18 = gep {ety}, ptr %1, %40
    store {ety} %14, ptr %18
    br bb5(%40)
bb5(%41: {ety}):
    %15 = add {ety} %41, %4
    br bb1(%15)
bb2:
    ret %3
}}
""")

objs = {}
for tag, disable in (("on", None), ("off", "neon_condstore")):
    o = os.path.join(wd, f"t_{tag}.o")
    env = dict(os.environ)
    if disable:
        env["TRUST_CG_DISABLE_PASSES"] = disable
    r = subprocess.run([TCG, "--format=text", "--target", "aarch64", "-O2",
                        "-c", tir, "-o", o], capture_output=True, text=True, env=env)
    assert r.returncode == 0, "trust-cg compile failed:\n" + r.stderr[-2000:]
    objs[tag] = o

cref = os.path.join(wd, "c.c")
open(cref, "w").write(f"""
#include <stdint.h>
void kernel({cty}* restrict b, const {cty}* restrict a, {cty} n){{
    for ({cty} i = 0; i < n; i++) if (a[i] > 0) b[i] = {cval};
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
extern void kernel({cty}* b, const {cty}* a, {cty} n);
static double now_ms(void){{ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts);
  return ts.tv_sec*1000.0 + ts.tv_nsec/1e6; }}
int main(int argc, char**argv){{
  long N=atol(argv[1]); int REPS=atoi(argv[2]); int d=atoi(argv[3]);
  {cty}* a=malloc(sizeof({cty})*(size_t)N);
  {cty}* b=malloc(sizeof({cty})*(size_t)N);
  uint64_t s=0x9e3779b97f4a7c15ull;
  for(long i=0;i<N;i++){{
    s=s*6364136223846793005ull+1442695040888963407ull;
    int positive=(int)((s>>33)%100)<d;
    {cty} mag=({cty})(1+((s>>20)%1000));
    a[i]=positive?mag:-mag;
    b[i]=({cty})(0xCCu)+({cty})i;
  }}
  kernel(b,a,({cty})N); /* warm */
  double best=1e30;
  for(int r=0;r<REPS;r++){{ double t0=now_ms(); kernel(b,a,({cty})N);
    double dt=now_ms()-t0; if(dt<best)best=dt; }}
  uint64_t h=1469598103934665603ull;
  for(long i=0;i<N;i++){{ h^=(uint64_t)b[i]; h*=1099511628211ull; }}
  printf("%.3f %llu\\n", best, (unsigned long long)h);
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
        out = subprocess.run([bins[tag], str(N), str(REPS), str(DENS)],
                             capture_output=True, text=True).stdout.split()
        best[tag] = min(best[tag], float(out[0]))
        res.setdefault(tag, out[1])
assert len(set(res.values())) == 1, f"OUTPUT-ARRAY HASH MISMATCH {res}"
sp_off = best["off"] / best["on"]
sp_clang = best["clang"] / best["on"]
verdict = "WIN" if min(sp_off, sp_clang) >= 1.7 else \
          ("tie/small-win" if min(sp_off, sp_clang) >= 1.05 else
           ("TIE" if min(sp_off, sp_clang) >= 0.95 else "BEHIND"))
print(f"{VARIANT} N={N} d={DENS}% on={best['on']:.2f}ms off(scalar)={best['off']:.2f}ms "
      f"clang={best['clang']:.2f}ms speedup(off/on)={sp_off:.3f}x "
      f"speedup(clang/on)={sp_clang:.3f}x hash={res['on']} => {verdict}")
