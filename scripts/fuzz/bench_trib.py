#!/usr/bin/env python3
# Interleaved best-of-15 iterative-trib (serial 3-carried-var recurrence)
# trust-cg -O3 vs clang -O3. Bit-identical required.
import sys, os, subprocess, tempfile
TCG = sys.argv[1]
N = int(sys.argv[2]) if len(sys.argv) > 2 else 200_000_000
REPS = 15
SCR = os.path.dirname(os.path.abspath(__file__))
wd = tempfile.mkdtemp(prefix="benchtrib_")
tir = os.path.join(SCR, "trib.trust_ir")
tobj = os.path.join(wd, "t.o")
r = subprocess.run([TCG, "--format=text", "--target", "aarch64", "-O3", "-c", tir, "-o", tobj],
                   capture_output=True, text=True)
assert r.returncode == 0, "trust-cg compile failed:\n" + r.stderr[-2000:]
# clang reference — well-defined 2's-complement wrapping (unsigned) to match i32 add bits.
cref = os.path.join(wd, "c.c")
open(cref, "w").write(r"""
int trib_kernel(int n){ unsigned a=0u,b=0u,c=1u; for(int i=0;i<n;i++){ unsigned t=a+b+c; a=b; b=c; c=t; } return (int)c; }
""")
cobj = os.path.join(wd, "c.o")
subprocess.run(["clang", "-O3", "-c", cref, "-o", cobj], check=True)
drv = os.path.join(wd, "drv.c")
open(drv, "w").write(r"""
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
extern int trib_kernel(int n);
static double now_ms(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts);
  return ts.tv_sec*1000.0 + ts.tv_nsec/1e6; }
int main(int argc,char**argv){
  int N=atoi(argv[1]); int REPS=atoi(argv[2]);
  volatile int res=trib_kernel(N);
  double best=1e30;
  for(int r=0;r<REPS;r++){ double t0=now_ms(); res=trib_kernel(N); double dt=now_ms()-t0; if(dt<best)best=dt; }
  printf("%.3f %08x\n", best, (unsigned)res);
  return 0;
}
""")
bins = {}
for tag, o in [("tcg", tobj), ("clang", cobj)]:
    b = os.path.join(wd, tag); subprocess.run(["clang", "-O2", drv, o, "-o", b], check=True); bins[tag] = b
best = {"tcg": 1e30, "clang": 1e30}; hsh = {}
for _ in range(REPS):
    for tag in ("tcg", "clang"):
        out = subprocess.run([bins[tag], str(N), str(REPS)], capture_output=True, text=True).stdout.split()
        ms = float(out[0]); h = out[1]
        best[tag] = min(best[tag], ms); hsh.setdefault(tag, h)
        assert hsh[tag] == h, "nondeterministic " + tag
assert hsh["tcg"] == hsh["clang"], f"BIT MISMATCH tcg={hsh['tcg']} clang={hsh['clang']}"
ratio = best["tcg"] / best["clang"]
verdict = "TIE" if 0.9 <= ratio <= 1.15 else ("WIN" if ratio < 0.9 else "BEHIND")
print(f"trib N={N} tcg={best['tcg']:.2f}ms clang={best['clang']:.2f}ms ratio={ratio:.3f} bitid=OK => {verdict}")
