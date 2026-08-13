#!/usr/bin/env python3
"""
Popcount-reduction benchmark: `s += popcount(a[i])` over 2e7 i32.
trust-cg -O2 (CNT + accumulating UDOT) vs clang -O3 (__builtin_popcount).
Best-of-11 per binary, the two binaries INTERLEAVED so machine load hits both
equally. Asserts bit-identical results.
usage: bench_udot.py <trust-cg-binary>
"""
import sys, os, subprocess, tempfile

TIR = """; TrustIr text format v1
module "k"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32) -> (i32)
fn @kernel(functy.0) {
bb0(%1: ptr, %2: i32):
    %3 = const i32 0
    %4 = const i32 1
    %5 = const i32 0
    br bb1(%3, %5)
bb1(%6: i32, %7: i32):
    %8 = icmp slt i32 %6, %2
    condbr %8, bb3(%6, %7), bb2(%7)
bb3(%9: i32, %10: i32):
    %11 = gep i32, ptr %1, %9
    %12 = load i32, ptr %11
    %13 = ctpop i32 %12
    %14 = add i32 %10, %13
    %15 = add i32 %9, %4
    br bb1(%15, %14)
bb2(%16: i32):
    ret %16
}
"""

CREF = """#include <stdint.h>
uint32_t kernel(uint32_t* a, int n){
  uint32_t s = 0u;
  for (int i = 0; i < n; i++) s += (uint32_t)__builtin_popcount(a[i]);
  return s;
}
"""

DRIVER = r"""
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
extern uint32_t kernel(uint32_t*, int);
static double now_ms(void){
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec*1000.0 + ts.tv_nsec/1e6;
}
int main(void){
  const int N = 20000000;
  uint32_t* a = malloc(sizeof(uint32_t)*(size_t)N);
  uint32_t s = 2463534242u;
  for (int i = 0; i < N; i++){ s ^= s<<13; s ^= s>>17; s ^= s<<5; a[i]=s; }
  volatile uint32_t sink = kernel(a, N);   /* warm */
  double best = 1e30;
  for (int r = 0; r < 11; r++){
    double t0 = now_ms();
    sink = kernel(a, N);
    double dt = now_ms() - t0;
    if (dt < best) best = dt;
  }
  printf("%.3f %u\n", best, (unsigned)sink);
  return 0;
}
"""

def main():
    tcg = sys.argv[1]
    wd = tempfile.mkdtemp(prefix="benchudot_")
    tir = os.path.join(wd,"k.trust_ir"); open(tir,"w").write(TIR)
    cref = os.path.join(wd,"k.c"); open(cref,"w").write(CREF)
    drv = os.path.join(wd,"drv.c"); open(drv,"w").write(DRIVER)
    t_o = os.path.join(wd,"t.o"); c_o = os.path.join(wd,"c.o")
    r = subprocess.run([tcg,"--format=text","--target","aarch64","-O2","-c",tir,"-o",t_o],
                       capture_output=True,text=True)
    if r.returncode: print("tcg compile failed:", r.stderr); sys.exit(2)
    subprocess.run(["clang","-O3","-c",cref,"-o",c_o],check=True)
    t_b = os.path.join(wd,"t_bin"); c_b = os.path.join(wd,"c_bin")
    subprocess.run(["cc",drv,t_o,"-o",t_b],check=True)
    subprocess.run(["cc",drv,c_o,"-o",c_b],check=True)
    # shape confirmation
    dis = subprocess.run(["otool","-tvV",t_o],capture_output=True,text=True).stdout
    print("shape: udot=%s uaddlp=%s cnt=%s ldp_q=%s" %
          ("udot" in dis, "uaddlp" in dis, ("\tcnt" in dis or "cnt.16b" in dis), "ldp\tq" in dis or "ldp q" in dis))
    # interleave: 7 rounds, each binary reports its own best-of-11
    t_best = 1e30; c_best = 1e30; t_val=c_val=None
    for _ in range(7):
        for which in ("t","c"):
            b = t_b if which=="t" else c_b
            out = subprocess.run([b],capture_output=True,text=True).stdout.split()
            ms, val = float(out[0]), out[1]
            if which=="t":
                t_best=min(t_best,ms); t_val=val
            else:
                c_best=min(c_best,ms); c_val=val
    match = "YES" if t_val==c_val else "NO"
    ratio = t_best/c_best
    verdict = "WIN" if ratio < 0.98 else ("TIE" if ratio <= 1.05 else "BEHIND")
    print(f"trust-cg {t_best:.3f} ms   clang -O3 {c_best:.3f} ms   ratio {ratio:.3f}x   bit-identical={match} ({t_val})   verdict {verdict}")

if __name__=="__main__":
    main()
