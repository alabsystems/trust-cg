#!/usr/bin/env python3
"""
Popcount-reduction differential: `s += popcount(a[i])` (`ctpop i32`).
Compiles the SAME trust_ir kernel three ways and asserts BIT-IDENTICAL results:
  - trust-cg -O2                                   (pass ON  = CNT.16B + UADDLP fold)
  - trust-cg -O2 TRUST_CG_DISABLE_PASSES=neon_array (pass OFF = scalar SWAR)
  - clang   -O2  __builtin_popcount                 (reference)
across edge patterns (all-0, all-FF=popcount32, INT_MIN, alternating, random)
x many n (0,1,3,4,7,8,15,16,17,tail...). Also asserts the ON binary actually
contains a `cnt` instruction (the fold fired), else the test is meaningless.
usage: popfuzz.py <trust-cg-binary>
"""
import sys, os, subprocess, tempfile, shutil

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

DRIVER = """#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
extern uint32_t kernel(uint32_t*, int);
int main(int argc, char** argv){
  int n = atoi(argv[1]);
  int pat = atoi(argv[2]);
  int m = n > 0 ? n : 1;
  uint32_t* a = malloc(sizeof(uint32_t) * m);
  uint32_t s = 2463534242u;
  for (int i = 0; i < n; i++){
    uint32_t v;
    switch (pat){
      case 0: v = 0u; break;                       // all zero
      case 1: v = 0xFFFFFFFFu; break;              // all ones (popcount 32)
      case 2: v = 0x80000000u; break;              // INT_MIN (popcount 1)
      case 3: v = (i & 1) ? 0x55555555u : 0xAAAAAAAAu; break; // alternating (16 each)
      default: {                                    // xorshift random + specials
        s ^= s << 13; s ^= s >> 17; s ^= s << 5;
        v = s;
        int r = i % 13;
        if (r==0) v=0u; else if (r==1) v=0xFFFFFFFFu; else if (r==2) v=0x80000000u;
        else if (r==3) v=0x7FFFFFFFu; else if (r==4) v=1u; else if (r==5) v=255u;
        else if (r==6) v=0xDEADBEEFu; else if (r==7) v=0xCAFEBABEu;
      }
    }
    a[i] = v;
  }
  printf("%u\\n", kernel(a, n));
  return 0;
}
"""

NS = [0,1,2,3,4,5,7,8,15,16,17,18,31,32,33,47,48,63,64,65,100,127,128,129,255,256,1000,1001,4096,4097]
PATS = [0,1,2,3,4]

def main():
    tcg = sys.argv[1]
    wd = tempfile.mkdtemp(prefix="popfuzz_")
    tir = os.path.join(wd, "pop.trust_ir"); open(tir,"w").write(TIR)
    cref = os.path.join(wd, "pop.c"); open(cref,"w").write(CREF)
    drv = os.path.join(wd, "drv.c"); open(drv,"w").write(DRIVER)

    on_o = os.path.join(wd,"on.o"); off_o = os.path.join(wd,"off.o"); cl_o = os.path.join(wd,"cl.o")
    env = dict(os.environ); env["TRUST_CG_DUMP_NEONARRAY"]="1"
    r = subprocess.run([tcg,"--format=text","--target","aarch64","-O2","-c",tir,"-o",on_o],
                       capture_output=True,text=True,env=env)
    if r.returncode != 0:
        print("COMPILE_ON failed:\n", r.stderr); sys.exit(2)
    fired = "neon-array" in r.stderr
    # confirm the fold actually emitted a CNT instruction
    dis = subprocess.run(["otool","-tvV",on_o],capture_output=True,text=True).stdout
    has_cnt = "\tcnt" in dis or "cnt.16b" in dis
    has_uaddlp = "uaddlp" in dis
    has_udot = "udot" in dis

    envoff = dict(os.environ); envoff["TRUST_CG_DISABLE_PASSES"]="neon_array"
    if subprocess.run([tcg,"--format=text","--target","aarch64","-O2","-c",tir,"-o",off_o],
                      capture_output=True,text=True,env=envoff).returncode != 0:
        print("COMPILE_OFF failed"); sys.exit(2)
    if subprocess.run(["cc","-O2","-c",cref,"-o",cl_o],capture_output=True).returncode != 0:
        print("CLANG_C failed"); sys.exit(2)

    on_b=os.path.join(wd,"on"); off_b=os.path.join(wd,"off"); cl_b=os.path.join(wd,"cl")
    subprocess.run(["cc",drv,on_o,"-o",on_b],capture_output=True)
    subprocess.run(["cc",drv,off_o,"-o",off_b],capture_output=True)
    subprocess.run(["cc",drv,cl_o,"-o",cl_b],capture_output=True)

    total=ok=mism=0; fails=[]
    for pat in PATS:
        for n in NS:
            total+=1
            von=subprocess.run([on_b,str(n),str(pat)],capture_output=True,text=True).stdout.strip()
            voff=subprocess.run([off_b,str(n),str(pat)],capture_output=True,text=True).stdout.strip()
            vcl=subprocess.run([cl_b,str(n),str(pat)],capture_output=True,text=True).stdout.strip()
            if von==voff==vcl and von!="":
                ok+=1
            else:
                mism+=1; fails.append((f"pat={pat} n={n}", f"on={von} off={voff} clang={vcl}"))
    print(f"\n=== popcount differential: {total} runs ===")
    print(f"neon-array fired: {fired}   CNT emitted: {has_cnt}   UDOT emitted: {has_udot}   UADDLP emitted: {has_uaddlp}")
    print(f"OK(on==off==clang)={ok}  MISMATCH={mism}")
    if fails:
        print("\n!!! MISMATCHES:")
        for d,info in fails[:40]: print("   ",d,info)
    shutil.rmtree(wd,ignore_errors=True)
    # Term-root ctpop now accumulates via UDOT.4S (CNT + UDOT, clang's shape);
    # the UADDLP chain remains only for NESTED ctpop uses and must be GONE here.
    bad = mism>0 or not (fired and has_cnt and has_udot) or has_uaddlp
    if not fired: print("ERROR: neon-array did not fire on the popcount kernel")
    if not has_cnt: print("ERROR: no CNT instruction in the ON binary (fold did not fire)")
    if not has_udot: print("ERROR: no UDOT instruction in the ON binary (fast path did not fire)")
    if has_uaddlp: print("ERROR: UADDLP still present — term-root ctpop should use the UDOT fast path")
    sys.exit(1 if bad else 0)

if __name__=="__main__":
    main()
