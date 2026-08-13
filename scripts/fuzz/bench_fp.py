#!/usr/bin/env python3
"""
Acceptance benchmarks for the neon-fmap elementwise-FP vectorizer.
Interleaved best-of-15 vs clang -O3 AND clang -O3 -ffp-contract=off.
Kernels: fmap32, saxpy32, fstencil32, fcount32, fmap64.
Also bit-identity cross-check: tcg-vec == tcg-scalar == clang-contract-off.

usage: bench_fp.py <trust-cg-binary>
"""
import sys, os, subprocess, tempfile, shutil
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fpmapfuzz as F

TCG = sys.argv[1]
ROUNDS = 15
WD = tempfile.mkdtemp(prefix="benchfp_")

# (bench-name, fmap-kind, fty)
KERNELS = [
    ("fmap32",     "map_mul_add", "f32"),
    ("saxpy32",    "saxpy",       "f32"),
    ("fstencil32", "stencil3",    "f32"),
    ("fcount32",   "count",       "f32"),
    ("fmap64",     "map_mul_add", "f64"),
]

def bench_driver(kind, fty):
    ct = 'float' if fty == 'f32' else 'double'
    is_count = kind == 'count'
    stencil = kind.startswith('stencil')
    ptrs = ['a'] if (kind == 'inplace' or is_count) else (
        ['a', 'b', 'c'] if kind in ('map_sub', 'map_mul2', 'map_div') else ['a', 'b'])
    allocs = []
    for p in ptrs:
        allocs.append(f"  {ct}* {p} = ({ct}*)malloc(sizeof({ct})*(size_t)n);")
    # finite normal random fill (representative throughput; denormal penalty avoided)
    fills = []
    for p in ptrs:
        fills.append(f"""  {{ uint64_t s = 0x9e3779b97f4a7c15ull ^ (uint64_t){ord(p)};
    for (int i=0;i<n;i++){{ s=s*6364136223846793005ull+1442695040888963407ull;
      {p}[i] = ({ct})(( (double)((s>>11)&0xfffff) / 1048576.0 ) * 4.0 - 2.0); }} }}""")
    if is_count:
        proto = f"extern int kernel(const {ct}*, {ct}, int);"
        lo = "0"
        call = f"vol += kernel(a, ({ct})0.0, n);"
        touch = ""
    else:
        sig = [f"{ct}*"]
        if kind != 'inplace':
            sig.append(f"const {ct}*")
        if kind in ('map_sub','map_mul2','map_div'):
            sig.append(f"const {ct}*")
        if kind == 'saxpy':
            sig.append(ct)
        sig.append("int")
        proto = f"extern int kernel({', '.join(sig)});"
        extra = f", ({ct})0.5" if kind == 'saxpy' else ""
        call = f"kernel({', '.join(ptrs)}{extra}, n); vol += (uint64_t)a[n/2];"
        touch = ""
    return f"""#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
{proto}
static double now(){{ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
  return t.tv_sec*1e3 + t.tv_nsec/1e6; }}
int main(int argc,char**argv){{
  int n=atoi(argv[1]); int reps=atoi(argv[2]);
{chr(10).join(allocs)}
{chr(10).join(fills)}
  volatile uint64_t vol=0;
  /* warmup */
  for(int r=0;r<3;r++){{ {call} }}
  double best=1e30;
  for(int r=0;r<reps;r++){{
    double t0=now();
    {call}
    double t1=now();
    if(t1-t0<best) best=t1-t0;
  }}
  /* whole-array / result hash for bit-identity */
  uint64_t h=1469598103934665603ull;
  {"for(int i=0;i<n;i++){ uint8_t*bp=(uint8_t*)&a[i]; for(int k=0;k<(int)sizeof("+ct+");k++){h^=bp[k];h*=1099511628211ull;} }" if not is_count else "h ^= vol;"}
  fprintf(stderr,"arrhash=%016llx\\n",(unsigned long long)h);
  printf("%.4f %llu\\n", best, (unsigned long long)vol);
  return 0;
}}
"""

def compile_tcg(tir, obj, disable=None):
    env = dict(os.environ)
    if disable:
        env["TRUST_CG_DISABLE_PASSES"] = disable
    r = subprocess.run([TCG,"--format=text","--target","aarch64","-O2","-c",tir,"-o",obj],
                       env=env, capture_output=True, text=True)
    if r.returncode: raise SystemExit(f"tcg fail {tir}: {r.stderr}")

def has_vec(obj):
    r = subprocess.run(["objdump","-d",obj], capture_output=True, text=True)
    return ("st1." in r.stdout) or ("fcmgt." in r.stdout)

def build(name, kind, fty):
    tir = os.path.join(WD, name+".trust_ir")
    if kind == 'count':
        open(tir,"w").write(F.count_ir(fty)); open(os.path.join(WD,name+".c"),"w").write(F.count_c(fty))
    else:
        open(tir,"w").write(F.kernel_ir(kind, fty, noalias=True))
        open(os.path.join(WD,name+".c"),"w").write(F.kernel_c(kind, fty))
    vec_o = os.path.join(WD,name+"_vec.o"); compile_tcg(tir, vec_o)
    sca_o = os.path.join(WD,name+"_sca.o"); compile_tcg(tir, sca_o, disable="neon_fmap")
    vec = has_vec(vec_o)
    cref = os.path.join(WD,name+".c")
    drv = os.path.join(WD,name+"_drv.c"); open(drv,"w").write(bench_driver(kind, fty))
    bins = {}
    # tcg vec / scalar link with clang -O3 driver
    for tag,obj in [("vec",vec_o),("scalar",sca_o)]:
        b=os.path.join(WD,name+"_"+tag)
        subprocess.run(["clang","-O3",drv,obj,"-o",b],check=True); bins[tag]=b
    # clang -O3 (default contract) full build
    b=os.path.join(WD,name+"_clangO3")
    subprocess.run(["clang","-O3",drv,cref,"-o",b],check=True); bins["clangO3"]=b
    # clang -O3 -ffp-contract=off
    b=os.path.join(WD,name+"_clangOff")
    subprocess.run(["clang","-O3","-ffp-contract=off",drv,cref,"-o",b],check=True); bins["clangOff"]=b
    return bins, vec

def run_once(binpath, N, reps):
    r=subprocess.run([binpath,str(N),str(reps)],capture_output=True,text=True)
    ms=float(r.stdout.split()[0]); ah=r.stderr.strip().split("=")[1]
    return ms, ah

def main():
    print(f"=== FP acceptance bench: interleaved best-of-{ROUNDS}, vs clang -O3 AND -ffp-contract=off ===")
    print(f"{'kernel':11s} {'N':>8s} {'vec':>9s} {'scalar':>9s} {'clangO3':>9s} {'clangOff':>9s} "
          f"{'vs-O3':>7s} {'vs-Off':>7s} {'sca/vec':>7s}  bitid vecfired")
    for (name, kind, fty) in KERNELS:
        bins, vec = build(name, kind, fty)
        elem = 4 if fty=='f32' else 8
        N = (1<<20)              # 1M elements
        reps = 200
        best = {k:1e30 for k in bins}
        hashes = {}
        for rnd in range(ROUNDS):
            for k in bins:
                ms, ah = run_once(bins[k], N, reps)
                if ms < best[k]: best[k] = ms
                hashes[k] = ah
        bitid = (hashes["vec"]==hashes["scalar"]==hashes["clangOff"])
        vs_o3  = best["vec"]/best["clangO3"]
        vs_off = best["vec"]/best["clangOff"]
        sca_vec = best["scalar"]/best["vec"]
        print(f"{name:11s} {N:8d} {best['vec']:9.4f} {best['scalar']:9.4f} "
              f"{best['clangO3']:9.4f} {best['clangOff']:9.4f} "
              f"{vs_o3:6.2f}x {vs_off:6.2f}x {sca_vec:6.2f}x  {str(bitid):5s} {vec}")
    shutil.rmtree(WD, ignore_errors=True)

if __name__ == "__main__":
    main()
