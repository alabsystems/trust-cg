#!/usr/bin/env python3
"""3-pt i32 stencil o[i]=a[i-1]+a[i]+a[i+1], 2e7 i32.
trust-cg -O2 vs clang -O3. Best-of-11 per binary, runs INTERLEAVED.
Asserts whole-array bit-identity. usage: bench_ext.py <tcg> [reps]"""
import sys, os, subprocess, tempfile
import stencilfuzz as S

DRIVER = r"""
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
extern void kernel(uint32_t* restrict o, uint32_t* restrict a, int n);
static double now_ms(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts);
  return ts.tv_sec*1000.0 + ts.tv_nsec/1e6; }
int main(int argc, char**argv){
  (void)argc;
  int N = atoi(argv[1]); int REPS = atoi(argv[2]);
  uint32_t* a = malloc(sizeof(uint32_t)*(size_t)N);
  uint32_t* o = malloc(sizeof(uint32_t)*(size_t)N);
  uint32_t s = 2463534242u;
  for (int i=0;i<N;i++){ s^=s<<13; s^=s>>17; s^=s<<5; a[i]=s; o[i]=0xCCCCCCCCu; }
  kernel(o,a,N); /* warm */
  double best = 1e30;
  for (int r = 0; r < REPS; r++){
    double t0 = now_ms(); kernel(o,a,N); double dt0 = now_ms()-t0;
    if (dt0 < best) best = dt0;
  }
  double dt = best;
  uint64_t h=1469598103934665603ull;
  for (int i=0;i<N;i++){ h^=o[i]; h*=1099511628211ull; }
  printf("%.3f %016llx\n", dt, (unsigned long long)h);
  return 0;
}
"""

def main():
    tcg = sys.argv[1]; reps = int(sys.argv[2]) if len(sys.argv)>2 else 11
    global N, IREPS
    N = int(sys.argv[3]) if len(sys.argv)>3 else 20000000
    IREPS = int(sys.argv[4]) if len(sys.argv)>4 else 11
    wd = tempfile.mkdtemp(prefix="benchext_")
    tir = os.path.join(wd,"k.trust_ir"); open(tir,"w").write(S._gen_tir_impl("sum3", True))
    obj = os.path.join(wd,"t.o")
    r = S.compile_tcg(tcg, tir, obj, disable=None, dump=True)
    assert S.has_st1(obj), "trust-cg build did not vectorize (no ST1)"
    cref = os.path.join(wd,"k.c"); open(cref,"w").write(S.gen_c("sum3"))
    c_o = os.path.join(wd,"c.o")
    subprocess.run(["clang","-O3","-c",cref,"-o",c_o],check=True)
    drv = os.path.join(wd,"drv.c"); open(drv,"w").write(DRIVER)
    bins={}
    for tag,o in [("tcg",obj),("clang",c_o)]:
        b=os.path.join(wd,tag); subprocess.run(["clang","-O2",drv,o,"-o",b],check=True); bins[tag]=b
    best={"tcg":1e30,"clang":1e30}; hashes={}
    for r_ in range(reps):
        for tag in ("tcg","clang"):
            out=subprocess.run([bins[tag],str(N),str(IREPS)],capture_output=True,text=True).stdout.split()
            ms=float(out[0]); h=out[1]
            if ms<best[tag]: best[tag]=ms
            hashes.setdefault(tag,h)
            assert hashes[tag]==h, f"nondeterministic {tag}"
    assert hashes["tcg"]==hashes["clang"], f"BIT MISMATCH tcg={hashes['tcg']} clang={hashes['clang']}"
    ratio=best["tcg"]/best["clang"]
    verdict = "TIE" if 0.9<=ratio<=1.11 else ("WIN" if ratio<0.9 else "BEHIND")
    print(f"N={N} tcg={best['tcg']:.3f}ms clang={best['clang']:.3f}ms ratio={ratio:.3f} bitid=OK => {verdict}")

if __name__=="__main__": main()
