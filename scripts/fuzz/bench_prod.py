#!/usr/bin/env python3
# Interleaved best-of-11 prod_i64 (i32 product reduction) trust-cg -O3 vs clang -O3.
import sys, os, subprocess, tempfile
TCG = sys.argv[1]
N = int(sys.argv[2]) if len(sys.argv) > 2 else 200_000_000
REPS = 11
wd = tempfile.mkdtemp(prefix="benchprod_")
tir = os.path.join(SCR:=os.path.dirname(os.path.abspath(__file__)), "prod.trust_ir")
# trust-cg object (symbol prod_kernel)
tobj = os.path.join(wd, "t.o")
r = subprocess.run([TCG,"--format=text","--target","aarch64","-O3","-c",tir,"-o",tobj],
                   capture_output=True, text=True)
assert r.returncode == 0, "trust-cg compile failed:\n"+r.stderr[-2000:]
# clang reference (well-defined 2's-complement wrapping to match i32 mul bits)
cref = os.path.join(wd,"c.c")
open(cref,"w").write(r"""
int prod_kernel(int* a, int n){ unsigned p=1u; for(int i=0;i<n;i++) p*=(unsigned)a[i]; return (int)p; }
""")
cobj = os.path.join(wd,"c.o")
subprocess.run(["clang","-O3","-c",cref,"-o",cobj],check=True)
drv = os.path.join(wd,"drv.c")
open(drv,"w").write(r"""
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
extern int prod_kernel(int* a, int n);
static double now_ms(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts);
  return ts.tv_sec*1000.0 + ts.tv_nsec/1e6; }
int main(int argc, char**argv){
  int N=atoi(argv[1]); int REPS=atoi(argv[2]);
  int* a=malloc(sizeof(int)*(size_t)N);
  uint32_t s=2463534242u;
  for(int i=0;i<N;i++){ s^=s<<13; s^=s>>17; s^=s<<5; a[i]=(int)(s|1u); }
  volatile int res = prod_kernel(a,N);
  double best=1e30;
  for(int r=0;r<REPS;r++){ double t0=now_ms(); res=prod_kernel(a,N); double dt=now_ms()-t0; if(dt<best)best=dt; }
  printf("%.3f %08x\n", best, (unsigned)res);
  return 0;
}
""")
bins={}
for tag,o in [("tcg",tobj),("clang",cobj)]:
    b=os.path.join(wd,tag); subprocess.run(["clang","-O2",drv,o,"-o",b],check=True); bins[tag]=b
best={"tcg":1e30,"clang":1e30}; hsh={}
for _ in range(REPS):
    for tag in ("tcg","clang"):
        out=subprocess.run([bins[tag],str(N),str(REPS)],capture_output=True,text=True).stdout.split()
        ms=float(out[0]); h=out[1]
        best[tag]=min(best[tag],ms); hsh.setdefault(tag,h)
        assert hsh[tag]==h, "nondeterministic "+tag
assert hsh["tcg"]==hsh["clang"], f"BIT MISMATCH tcg={hsh['tcg']} clang={hsh['clang']}"
ratio=best["tcg"]/best["clang"]
verdict="TIE" if 0.9<=ratio<=1.11 else ("WIN" if ratio<0.9 else "BEHIND")
print(f"prod_i64 N={N} tcg={best['tcg']:.2f}ms clang={best['clang']:.2f}ms ratio={ratio:.3f} bitid=OK => {verdict}")
