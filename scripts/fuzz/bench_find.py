#!/usr/bin/env python3
# Interleaved best-of-15 first-match search (find/memchr) benchmark:
#   * tcg-on  : trust-cg -O3 (neon-find FIRES — the vector block filter)
#   * tcg-off : trust-cg -O3 with neon-find DISABLED (the honest scalar before)
#   * clang   : clang -O3 (REFUSES this class — LLVM's loop vectorizer bails on
#               the data-dependent early exit; scalar since 2013)
# Data is NO-MATCH (the honest worst case: every execution scans [0, n)).
# All three binaries must agree bit-identically (-1) before timing counts.
# usage: bench_find.py <trust-cg> [N] [variant]   variant in find_i32/find_u8
import sys, os, subprocess, tempfile

TCG = sys.argv[1]
VARIANT = sys.argv[3] if len(sys.argv) > 3 else "find_i32"
REPS = 15

SPEC = {
    # (elem trust_ir ty, needs zext, C elem ty, default N, key)
    'find_i32': ('i32', False, 'int', 20_000_000, 999),
    'find_u8':  ('i8',  True,  'unsigned char', 80_000_000, 0x5A),
}
ety, zext, cty, defn, key = SPEC[VARIANT]
N = int(sys.argv[2]) if len(sys.argv) > 2 else defn

wd = tempfile.mkdtemp(prefix="benchfind_")
tir = os.path.join(wd, "k.trust_ir")
load = (" %22=load i8,ptr %21\n %25=zext i8 %22 to i32\n"
        if zext else " %25=load i32,ptr %21\n")
open(tir, "w").write(f"""; TrustIr text format v1
module "find"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32, i32) -> (i32)
fn @findkey(functy.0){{
bb0(%0: ptr,%1: i32,%2: i32):
 %3=const i32 0
 %4=const i32 1
 %5=const i32 -1
 br bb1(%3)
bb1(%10: i32):
 %11=icmp slt i32 %10,%1
 condbr %11,bb2(%10),bb4()
bb2(%20: i32):
 %21=gep {ety},ptr %0,%20
{load} %23=icmp eq i32 %25,%2
 condbr %23,bb3(%20),bb5(%20)
bb3(%30: i32): ret %30
bb5(%40: i32):
 %41=add i32 %40,%4
 br bb1(%41)
bb4(): ret %5
}}
""")

objs = {}
for tag, disable in (("on", None), ("off", "neon_find")):
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
int findkey(const {cty}* a, int n, int key){{
    for (int i = 0; i < n; i++) if ((int)a[i] == key) return i;
    return -1;
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
extern int findkey(const {cty}* a, int n, int key);
static double now_ms(void){{ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts);
  return ts.tv_sec*1000.0 + ts.tv_nsec/1e6; }}
int main(int argc, char**argv){{
  int N=atoi(argv[1]); int REPS=atoi(argv[2]);
  {cty}* a=malloc(sizeof({cty})*(size_t)N);
  uint32_t s=2463534242u;
  for(int i=0;i<N;i++){{ s^=s<<13; s^=s>>17; s^=s<<5;
    {cty} v=({cty})s; if ((int)v == {key}) v=({cty})(v^1); a[i]=v; }}
  volatile int res = findkey(a,N,{key});
  double best=1e30;
  for(int r=0;r<REPS;r++){{ double t0=now_ms(); res=findkey(a,N,{key});
    double dt=now_ms()-t0; if(dt<best)best=dt; }}
  printf("%.3f %d\\n", best, res);
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
