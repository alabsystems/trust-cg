#!/usr/bin/env python3
"""
Soundness fuzzer for the neon-map store-form matmul row-update vectorization
(loop-invariant scalar leaf + derived-row-base noalias resolution).

Generates the classic i32 square matmul `C[i][j] += A[i][k]*B[k][j]` in BOTH
loop orders — ikj (store-form saxpy inner, the vectorized order) and ijk
(dot-product inner) — as size-generic trust_ir `@matmul(C,A,B,N)` with noalias
on all three pointer params and row-base geps hoisted. For each order and a
sweep of matrix sizes INCLUDING edges (0,1,tails, non-multiples of 16) and
random sizes, it fills A,B with a seeded PRNG (incl INT_MIN/INT_MAX/-1/0
patterns), zeroes C, and compiles three ways:
  - trust-cg -O2                                  (pass ON  = vectorized ikj)
  - trust-cg -O2 TRUST_CG_DISABLE_PASSES=neon_map (pass OFF = scalar)
  - clang   -O3                                   (reference)
then requires the ENTIRE C matrix byte-for-byte identical across on==off==clang
(integer matmul is order-independent, so ikj and ijk must also agree).

GUARD-PAGE OOB variant: places C (store), A and B (loads) each flush against a
trailing PROT_NONE page so ANY over-read/over-write past element [N*N-1] faults
(SIGSEGV). Runs the vectorized (pass-ON) kernel across a size sweep; 0 faults
required (proves the vector loop touches EXACTLY the in-bounds elements).

Also an ALIASING NEGATIVE test: matmul compiled WITHOUT noalias must BAIL (no
st1.4s) and stay correct.

usage: matmulfuzz.py <trust-cg-binary>
"""
import sys, os, subprocess, tempfile, shutil, random

HDR = '''; TrustIr text format v1
module "mm"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, ptr, ptr, i32) -> ()
fn @matmul(functy.0) {
'''

ATTRS = '''; #param_attrs 0: noalias
; #param_attrs 1: noalias
; #param_attrs 2: noalias
'''

def gen_ikj(noalias=True):
    C,A,B,N=0,1,2,3; z,one=4,5
    i,rowC,crow,rowA,arow=10,11,12,13,14
    k,ag,s,rowB,brow=20,21,22,23,24
    j,cg,cv,bg,bv,prod,new,jn=30,31,32,33,34,35,36,37
    kn,inx=40,41; ci,ck,cj=50,51,52
    a = ATTRS if noalias else ""
    return HDR + a + f"""bb0(%{C}: ptr, %{A}: ptr, %{B}: ptr, %{N}: i32):
    %{z} = const i32 0
    %{one} = const i32 1
    br bb1(%{z})
bb1(%{i}: i32):
    %{ci} = icmp slt i32 %{i}, %{N}
    condbr %{ci}, bb2, bb9
bb2:
    %{rowC} = mul i32 %{i}, %{N}
    %{crow} = gep i32, ptr %{C}, %{rowC}
    %{rowA} = mul i32 %{i}, %{N}
    %{arow} = gep i32, ptr %{A}, %{rowA}
    br bb3(%{z})
bb3(%{k}: i32):
    %{ck} = icmp slt i32 %{k}, %{N}
    condbr %{ck}, bb4, bb8
bb4:
    %{ag} = gep i32, ptr %{arow}, %{k}
    %{s} = load i32, ptr %{ag}
    %{rowB} = mul i32 %{k}, %{N}
    %{brow} = gep i32, ptr %{B}, %{rowB}
    br bb5(%{z})
bb5(%{j}: i32):
    %{cj} = icmp slt i32 %{j}, %{N}
    condbr %{cj}, bb6, bb7
bb6:
    %{cg} = gep i32, ptr %{crow}, %{j}
    %{cv} = load i32, ptr %{cg}
    %{bg} = gep i32, ptr %{brow}, %{j}
    %{bv} = load i32, ptr %{bg}
    %{prod} = mul i32 %{s}, %{bv}
    %{new} = add i32 %{cv}, %{prod}
    store i32 %{new}, ptr %{cg}
    %{jn} = add i32 %{j}, %{one}
    br bb5(%{jn})
bb7:
    %{kn} = add i32 %{k}, %{one}
    br bb3(%{kn})
bb8:
    %{inx} = add i32 %{i}, %{one}
    br bb1(%{inx})
bb9:
    ret
}}
"""

def gen_ijk(noalias=True):
    C,A,B,N=0,1,2,3; z,one=4,5
    i,rowC,crow,rowA,arow=10,11,12,13,14
    j,cg,acc0=20,21,22
    k,ag,s,bg,bv,prod,acc1,kn=30,31,32,33,34,35,36,37
    rowB,browbase=38,39; jn,inx=40,41; ci,cj,ck=50,51,52; accp=60
    a = ATTRS if noalias else ""
    return HDR + a + f"""bb0(%{C}: ptr, %{A}: ptr, %{B}: ptr, %{N}: i32):
    %{z} = const i32 0
    %{one} = const i32 1
    br bb1(%{z})
bb1(%{i}: i32):
    %{ci} = icmp slt i32 %{i}, %{N}
    condbr %{ci}, bb2, bb9
bb2:
    %{rowC} = mul i32 %{i}, %{N}
    %{crow} = gep i32, ptr %{C}, %{rowC}
    %{rowA} = mul i32 %{i}, %{N}
    %{arow} = gep i32, ptr %{A}, %{rowA}
    br bb3(%{z})
bb3(%{j}: i32):
    %{cj} = icmp slt i32 %{j}, %{N}
    condbr %{cj}, bb4, bb8
bb4:
    %{cg} = gep i32, ptr %{crow}, %{j}
    %{acc0} = load i32, ptr %{cg}
    br bb5(%{z}, %{acc0})
bb5(%{k}: i32, %{accp}: i32):
    %{ck} = icmp slt i32 %{k}, %{N}
    condbr %{ck}, bb6, bb7
bb6:
    %{ag} = gep i32, ptr %{arow}, %{k}
    %{s} = load i32, ptr %{ag}
    %{rowB} = mul i32 %{k}, %{N}
    %{browbase} = gep i32, ptr %{B}, %{rowB}
    %{bg} = gep i32, ptr %{browbase}, %{j}
    %{bv} = load i32, ptr %{bg}
    %{prod} = mul i32 %{s}, %{bv}
    %{acc1} = add i32 %{accp}, %{prod}
    %{kn} = add i32 %{k}, %{one}
    br bb5(%{kn}, %{acc1})
bb7:
    store i32 %{accp}, ptr %{cg}
    %{jn} = add i32 %{j}, %{one}
    br bb3(%{jn})
bb8:
    %{inx} = add i32 %{i}, %{one}
    br bb1(%{inx})
bb9:
    ret
}}
"""

GEN = {'ikj': gen_ikj, 'ijk': gen_ijk}

C_REF = r"""#include <stdint.h>
void matmul(int32_t* restrict C, const int32_t* restrict A, const int32_t* restrict B, int N){
  for(int i=0;i<N;i++) for(int k=0;k<N;k++){ int32_t s=A[i*N+k];
    for(int j=0;j<N;j++) C[i*N+j] += s*B[k*N+j]; }
}
"""

# Normal driver: fill A,B seeded (adversarial patterns), zero C, run, dump C.
DRV = r"""#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void matmul(int32_t* C, const int32_t* A, const int32_t* B, int N);
static void fill(int32_t* p,long n,uint32_t seed){
  uint32_t s=seed?seed:1;
  for(long i=0;i<n;i++){ s^=s<<13;s^=s>>17;s^=s<<5; uint32_t v=s;
    int r=(int)((i*7+seed)%17);
    if(r==0)v=0; else if(r==1)v=0xFFFFFFFFu; else if(r==2)v=0x80000000u;
    else if(r==3)v=0x7FFFFFFFu; else if(r==4)v=1; else if(r==5)v=2;
    p[i]=(int32_t)v; }
}
int main(int argc,char**argv){
  int N=atoi(argv[1]); long nn=(long)N*N; long m=nn>0?nn:1;
  int32_t* C=calloc(m,4); int32_t* A=malloc(4*m); int32_t* B=malloc(4*m);
  fill(A,nn,0x9e3779b9u); fill(B,nn,0x85ebca6bu);
  matmul(C,A,B,N);
  FILE* f=fopen(argv[2],"wb"); fwrite(C,4,nn,f); fclose(f); return 0;
}
"""

# Guard-page driver: C (store), A, B each flush against a trailing PROT_NONE
# page so any over-read/over-write past element [N*N-1] faults.
GUARD_DRV = r"""#include <sys/mman.h>
#include <unistd.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
extern void matmul(int32_t* C, const int32_t* A, const int32_t* B, int N);
static int32_t* guarded(long n, int zero){
  long pg=sysconf(_SC_PAGESIZE);
  size_t need=(size_t)(n>0?n:1)*4;
  size_t rw=(need+pg-1)/pg*pg; if(rw==0)rw=pg;
  char* p=(char*)mmap(NULL,rw+pg,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANON,-1,0);
  if(p==MAP_FAILED){perror("mmap");exit(2);}
  if(mprotect(p+rw,pg,PROT_NONE)!=0){perror("mprotect");exit(2);}
  int32_t* a=(int32_t*)(p+rw-need);   // a[n] == guard page start
  if(!zero) for(long i=0;i<n;i++) a[i]=(int32_t)(i*2654435761u+1u);
  return a;                            // MAP_ANON is zero-filled for C
}
int main(int argc,char**argv){
  int N=atoi(argv[1]); long nn=(long)N*N;
  int32_t* C=guarded(nn,1); int32_t* A=guarded(nn,0); int32_t* B=guarded(nn,0);
  matmul(C,A,B,N);
  uint64_t sum=0; for(long i=0;i<nn;i++) sum+=(uint32_t)C[i];
  printf("%llu\n",(unsigned long long)sum); return 0;
}
"""

def compile_tcg(tcg, tir, obj, disable=None):
    env=dict(os.environ)
    if disable: env["TRUST_CG_DISABLE_PASSES"]=disable
    return subprocess.run([tcg,"--format=text","--target","aarch64","-O2","-c",tir,"-o",obj],
                          capture_output=True,text=True,env=env)

def has_st1(obj):
    r=subprocess.run(["objdump","-d",obj],capture_output=True,text=True)
    return "st1." in r.stdout

def run_dump(binpath,N,outpath):
    r=subprocess.run([binpath,str(N),outpath],capture_output=True)
    if r.returncode!=0: return None
    try: return open(outpath,"rb").read()
    except FileNotFoundError: return None

def main():
    tcg=sys.argv[1]
    wd=tempfile.mkdtemp(prefix="matmulfuzz_")
    random.seed(1234)
    sizes=sorted(set([0,1,2,3,4,5,7,8,9,15,16,17,18,23,31,32,33,47,48,63,64,65,
                      100,127,128,129,200,255,256] + [random.randint(1,300) for _ in range(30)]))
    total=ok=mism=err=0; fails=[]; fired=set()

    # compile C reference once
    cref=os.path.join(wd,"ref.c"); open(cref,"w").write(C_REF)
    cl_o=os.path.join(wd,"ref.o")
    if subprocess.run(["cc","-O3","-c",cref,"-o",cl_o],capture_output=True).returncode!=0:
        print("clang ref compile FAILED"); sys.exit(1)
    drvc=os.path.join(wd,"drv.c"); open(drvc,"w").write(DRV)
    cl_b=os.path.join(wd,"cl_b"); subprocess.run(["cc","-O2",drvc,cl_o,"-o",cl_b],capture_output=True)

    order_bins={}
    for order in ('ikj','ijk'):
        tir=os.path.join(wd,f"{order}.trust_ir"); open(tir,"w").write(GEN[order]())
        on_o=os.path.join(wd,f"{order}_on.o"); off_o=os.path.join(wd,f"{order}_off.o")
        r=compile_tcg(tcg,tir,on_o)
        if r.returncode!=0:
            err+=1; fails.append((order,"COMPILE_ON",r.stderr.strip().splitlines()[-2:])); continue
        if has_st1(on_o): fired.add(order)
        if compile_tcg(tcg,tir,off_o,disable="neon_map").returncode!=0:
            err+=1; fails.append((order,"COMPILE_OFF","")); continue
        if has_st1(off_o):
            err+=1; fails.append((order,"ST1_WHEN_OFF","kill switch failed")); continue
        on_b=os.path.join(wd,f"{order}_on_b"); off_b=os.path.join(wd,f"{order}_off_b")
        subprocess.run(["cc","-O2",drvc,on_o,"-o",on_b],capture_output=True)
        subprocess.run(["cc","-O2",drvc,off_o,"-o",off_b],capture_output=True)
        order_bins[order]=(on_b,off_b)

    # correctness: on==off==clang, whole C, both orders
    for order in order_bins:
        on_b,off_b=order_bins[order]
        for N in sizes:
            total+=1
            von=run_dump(on_b,N,os.path.join(wd,"on.bin"))
            voff=run_dump(off_b,N,os.path.join(wd,"off.bin"))
            vcl=run_dump(cl_b,N,os.path.join(wd,"cl.bin"))
            if von is not None and von==voff==vcl: ok+=1
            else:
                mism+=1; fails.append((f"{order} N={N}","MISMATCH",f"eq={von==voff==vcl}"))

    # guard-page OOB: pass-ON ikj across a size sweep, expect 0 faults.
    print("\n--- guard-page OOB (ikj pass-ON, C/A/B flush against PROT_NONE) ---")
    gtir=os.path.join(wd,"ikj.trust_ir")
    gon_o=os.path.join(wd,"g_on.o"); compile_tcg(tcg,gtir,gon_o)
    gdrv=os.path.join(wd,"gdrv.c"); open(gdrv,"w").write(GUARD_DRV)
    gbin=os.path.join(wd,"g_on_b")
    subprocess.run(["cc","-O2",gdrv,gon_o,"-o",gbin],capture_output=True)
    faults=0; gruns=0
    gsizes=list(range(0,70))+[95,96,97,127,128,129,200,255,256,257]
    for N in gsizes:
        gruns+=1
        r=subprocess.run([gbin,str(N)],capture_output=True)
        if r.returncode!=0:
            faults+=1; fails.append((f"guard N={N}","FAULT/OOB",f"rc={r.returncode}"))
    print(f"guard-page: {gruns} sizes run, faults={faults} (must be 0); ikj vectorized={'ikj' in fired}")

    # aliasing negative: matmul WITHOUT noalias must BAIL (no st1).
    print("\n--- aliasing negative (no noalias -> must BAIL) ---")
    natir=os.path.join(wd,"na.trust_ir"); open(natir,"w").write(gen_ikj(noalias=False))
    na_o=os.path.join(wd,"na.o"); rna=compile_tcg(tcg,natir,na_o)
    alias_ok = (rna.returncode==0 and not has_st1(na_o))
    if not alias_ok:
        fails.append(("alias","VECTORIZED_OR_FAILED","unsound: fired without noalias, or compile err"))
    print(f"no-noalias bailed (no st1.4s)={alias_ok}")

    print(f"\n=== matmul soundness: {total} correctness runs over both orders ===")
    print(f"orders vectorized (st1 present): {sorted(fired)} (expect ['ikj'])")
    print(f"OK(on==off==clang, whole matrix)={ok}  MISMATCH={mism}  compile/other-err={err}")
    print(f"guard-page faults={faults}  alias-bail-ok={alias_ok}")
    if fails:
        print(f"\n!!! FAILURES ({len(fails)}):")
        for f in fails[:40]: print("   ",f)
    shutil.rmtree(wd,ignore_errors=True)
    bad = mism or err or faults or (not alias_ok) or ('ikj' not in fired)
    sys.exit(1 if bad else 0)

if __name__=="__main__":
    main()
