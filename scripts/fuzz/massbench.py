#!/usr/bin/env python3
"""
MASS RANDOM KERNEL battery: trust-cg -O2 vs clang -O3, Apple M4 Max.
Seeded sample (~60) over the redfuzz/arrfuzz operator/shape space:
  - array reductions  s = s RED term(a[i][,b[i]],i,consts), n=1e7 i32 (streaming)
  - pure-IV reductions (redfuzz space) s = s RED term(i), 1e7 iters
One C driver per kernel, tcg and clang INTERLEAVED in the same process,
best-of-7 min, TWO process runs (min across both, >5% ratio disagreement flagged),
bit-identity checked on every call.
"""
import os, sys, random, subprocess, math, json
from concurrent.futures import ThreadPoolExecutor

TCG = os.environ.get("TCG_BIN") or os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
    "target", "release", "trust-cg",
)
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "massbench")
SEED = 20260708
NELEM = 10_000_000

REDS = {'add': ('+', 0), 'mul': ('*', 1), 'or': ('|', 0), 'xor': ('^', 0)}

# ---------------- term shapes ----------------
CTERM1 = {
  'id':     'x',
  'sq':     'x*x',
  'mulc3':  'x*3u',
  'mulc7':  'x*7u',
  'mulcK':  'x*40503u',
  'mix':    '(x*x)^(x*3u)',
  'or1':    'x|1u',
  'and255': 'x&255u',
  'shl3':   'x<<3',
  'ashr2':  '(uint32_t)((int32_t)x>>2)',
  'clamp':  '(((int32_t)x>0)?x:0u)',
  'cnt100': '(((int32_t)x>100)?1u:0u)',
  'absx':   '(((int32_t)x<0)?(0u-x):x)',
  'ctpop':  '(uint32_t)__builtin_popcount(x)',
  'ixor':   'x^(uint32_t)i',
}
CTERM2 = {
  'xy_mul': 'x*y',
  'xy_xor': 'x^y',
  'xy_or':  'x|y',
  'xy_and': 'x&y',
  'xy_add': 'x+y',
  'xy_sub': 'x-y',
  'max2':   '(((int32_t)x>(int32_t)y)?x:y)',
  'mix2':   '(x*y)^(x&255u)',
}
IVTERM_C = {'i': 'i', 'ii': 'i*i', 'mix': '(i*i)^(i*3u)', 'i7': 'i*7u', 'ior1': '(i|1u)'}

def tir_term(shape, alloc, x, y, i2, C):
    L = []
    def op(fmt):
        t = alloc(); L.append("    %%%d = %s" % (t, fmt)); return t
    if shape == 'id':     return L, x
    if shape == 'sq':     return L, op("mul i32 %%%d, %%%d" % (x, x))
    if shape == 'mulc3':  return L, op("mul i32 %%%d, %%%d" % (x, C[3]))
    if shape == 'mulc7':  return L, op("mul i32 %%%d, %%%d" % (x, C[7]))
    if shape == 'mulcK':  return L, op("mul i32 %%%d, %%%d" % (x, C[40503]))
    if shape == 'mix':
        a = op("mul i32 %%%d, %%%d" % (x, x)); b = op("mul i32 %%%d, %%%d" % (x, C[3]))
        return L, op("xor i32 %%%d, %%%d" % (a, b))
    if shape == 'or1':    return L, op("or i32 %%%d, %%%d" % (x, C[1]))
    if shape == 'and255': return L, op("and i32 %%%d, %%%d" % (x, C[255]))
    if shape == 'shl3':   return L, op("shl i32 %%%d, %%%d" % (x, C[3]))
    if shape == 'ashr2':  return L, op("ashr i32 %%%d, %%%d" % (x, C[2]))
    if shape == 'clamp':
        c = op("icmp sgt i32 %%%d, %%%d" % (x, C[0]))
        return L, op("select i32 %%%d, %%%d, %%%d" % (c, x, C[0]))
    if shape == 'cnt100':
        c = op("icmp sgt i32 %%%d, %%%d" % (x, C[100]))
        return L, op("select i32 %%%d, %%%d, %%%d" % (c, C[1], C[0]))
    if shape == 'absx':
        n = op("sub i32 %%%d, %%%d" % (C[0], x)); c = op("icmp slt i32 %%%d, %%%d" % (x, C[0]))
        return L, op("select i32 %%%d, %%%d, %%%d" % (c, n, x))
    if shape == 'ctpop':  return L, op("ctpop i32 %%%d" % x)
    if shape == 'ixor':   return L, op("xor i32 %%%d, %%%d" % (x, i2))
    if shape == 'xy_mul': return L, op("mul i32 %%%d, %%%d" % (x, y))
    if shape == 'xy_xor': return L, op("xor i32 %%%d, %%%d" % (x, y))
    if shape == 'xy_or':  return L, op("or i32 %%%d, %%%d" % (x, y))
    if shape == 'xy_and': return L, op("and i32 %%%d, %%%d" % (x, y))
    if shape == 'xy_add': return L, op("add i32 %%%d, %%%d" % (x, y))
    if shape == 'xy_sub': return L, op("sub i32 %%%d, %%%d" % (x, y))
    if shape == 'max2':
        c = op("icmp sgt i32 %%%d, %%%d" % (x, y))
        return L, op("select i32 %%%d, %%%d, %%%d" % (c, x, y))
    if shape == 'mix2':
        m = op("mul i32 %%%d, %%%d" % (x, y)); a = op("and i32 %%%d, %%%d" % (x, C[255]))
        return L, op("xor i32 %%%d, %%%d" % (m, a))
    raise KeyError(shape)

CONSTS = [0, 1, 2, 3, 7, 100, 255, 40503]

def gen_tir_array(red, shape, narr):
    init = REDS[red][1]
    n = [0]
    def alloc():
        n[0] += 1; return n[0]
    params = [alloc() for _ in range(narr)]
    N = alloc()
    C = {}
    cl = []
    for cv in CONSTS:
        cid = alloc(); C[cv] = cid
        cl.append("    %%%d = const i32 %d" % (cid, cv))
    initc = alloc(); cl.append("    %%%d = const i32 %d" % (initc, init))
    i_p, acc_p, cmp_id, i2, acc2 = (alloc() for _ in range(5))
    loads = []; body = []
    for p in params:
        g = alloc(); l = alloc()
        body.append("    %%%d = gep i32, ptr %%%d, %%%d" % (g, p, i2))
        body.append("    %%%d = load i32, ptr %%%d" % (l, g))
        loads.append(l)
    x = loads[0]; y = loads[1] if narr > 1 else None
    tl, t = tir_term(shape, alloc, x, y, i2, C)
    body += tl
    accN, iN, rp = alloc(), alloc(), alloc()
    body.append("    %%%d = %s i32 %%%d, %%%d" % (accN, red, acc2, t))
    body.append("    %%%d = add i32 %%%d, %%%d" % (iN, i2, C[1]))
    fparams = ", ".join(["ptr"] * narr + ["i32"])
    bb0p = ", ".join(["%%%d: ptr" % p for p in params] + ["%%%d: i32" % N])
    nl = chr(10)
    return f"""; TrustIr text format v1
module "k"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = ({fparams}) -> (i32)
fn @kernel(functy.0) {{
bb0({bb0p}):
{nl.join(cl)}
    br bb1(%{C[0]}, %{initc})
bb1(%{i_p}: i32, %{acc_p}: i32):
    %{cmp_id} = icmp slt i32 %{i_p}, %{N}
    condbr %{cmp_id}, bb3(%{i_p}, %{acc_p}), bb2(%{acc_p})
bb3(%{i2}: i32, %{acc2}: i32):
{nl.join(body)}
    br bb1(%{iN}, %{accN})
bb2(%{rp}: i32):
    ret %{rp}
}}
"""

def gen_c_array(red, shape, narr):
    cop, init = REDS[red]
    term = (CTERM1 if narr == 1 else CTERM2)[shape]
    args = ", ".join(["uint32_t* %s" % c for c in "ab"[:narr]] + ["int n"])
    ydecl = "uint32_t y=b[i];" if narr > 1 else ""
    return f"""#include <stdint.h>
uint32_t kernel_ref({args}){{
  uint32_t s={init}u;
  for(int i=0;i<n;i++){{ uint32_t x=a[i]; {ydecl} s = s {cop} ({term}); }}
  return s;
}}
"""

def gen_tir_iv(red, term):
    # redfuzz shape, i32, [0, NELEM)
    init = REDS[red][1]
    n = [0]
    def alloc():
        n[0] += 1; return n[0]
    limit_id, start_id, one_id, init_id, c3, c7 = (alloc() for _ in range(6))
    consts = [
        "    %%%d = const i32 %d" % (limit_id, NELEM),
        "    %%%d = const i32 0" % start_id,
        "    %%%d = const i32 1" % one_id,
        "    %%%d = const i32 %d" % (init_id, init),
        "    %%%d = const i32 3" % c3,
        "    %%%d = const i32 7" % c7,
    ]
    i_p, acc_p, cmp_id, i2, acc2 = (alloc() for _ in range(5))
    tinsts = []
    if term == 'i':
        t = i2
    elif term == 'ii':
        r = alloc(); tinsts.append("    %%%d = mul i32 %%%d, %%%d" % (r, i2, i2)); t = r
    elif term == 'mix':
        a, b, c = alloc(), alloc(), alloc()
        tinsts += ["    %%%d = mul i32 %%%d, %%%d" % (a, i2, i2),
                   "    %%%d = mul i32 %%%d, %%%d" % (b, i2, c3),
                   "    %%%d = xor i32 %%%d, %%%d" % (c, a, b)]
        t = c
    elif term == 'i7':
        r = alloc(); tinsts.append("    %%%d = mul i32 %%%d, %%%d" % (r, i2, c7)); t = r
    elif term == 'ior1':
        r = alloc(); tinsts.append("    %%%d = or i32 %%%d, %%%d" % (r, i2, one_id)); t = r
    accN, iN, rp = alloc(), alloc(), alloc()
    tinsts.append("    %%%d = %s i32 %%%d, %%%d" % (accN, red, acc2, t))
    tinsts.append("    %%%d = add i32 %%%d, %%%d" % (iN, i2, one_id))
    nl = chr(10)
    return f"""; TrustIr text format v1
module "r"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = () -> (i32)
fn @kernel(functy.0) {{
bb0():
{nl.join(consts)}
    br bb1(%{start_id}, %{init_id})
bb1(%{i_p}: i32, %{acc_p}: i32):
    %{cmp_id} = icmp sge i32 %{i_p}, %{limit_id}
    condbr %{cmp_id}, bb2(%{acc_p}), bb3(%{i_p}, %{acc_p})
bb3(%{i2}: i32, %{acc2}: i32):
{nl.join(tinsts)}
    br bb1(%{iN}, %{accN})
bb2(%{rp}: i32):
    ret %{rp}
}}
"""

def gen_c_iv(red, term):
    cop, init = REDS[red]
    return f"""#include <stdint.h>
uint32_t kernel_ref(void){{
  uint32_t s={init}u;
  for(uint32_t i=0;i<{NELEM}u;i++) s = s {cop} ({IVTERM_C[term]});
  return s;
}}
"""

DRIVER_ARRAY = r"""#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
extern uint32_t kernel(ARGDECL);
extern uint32_t kernel_ref(ARGDECL);
static double now_ms(void){ return (double)clock_gettime_nsec_np(CLOCK_UPTIME_RAW)/1e6; }
int main(void){
  int n = NELEM_N;
  uint32_t* arr[2] = {0,0};
  for(int k=0;k<NARR;k++) arr[k]=malloc(sizeof(uint32_t)*(size_t)n);
  uint32_t s = 2463534242u;
  for(int i=0;i<n;i++){
    for(int k=0;k<NARR;k++){
      s^=s<<13; s^=s>>17; s^=s<<5;
      uint32_t v=s;
      int r=(i*3+k)%13;
      if(r==0)v=0; else if(r==1)v=0xFFFFFFFFu; else if(r==2)v=0x80000000u;
      else if(r==3)v=0x7FFFFFFFu; else if(r==4)v=1; else if(r==5)v=255;
      arr[k][i]=v;
    }
  }
  uint32_t r1 = kernel(CALLARGS);      /* warmup + reference value */
  uint32_t r2 = kernel_ref(CALLARGS);
  int match = (r1==r2);
  double bt=1e18, bc=1e18;
  for(int rep=0;rep<7;rep++){
    double t0=now_ms(); uint32_t v1=kernel(CALLARGS);     double t1=now_ms();
                        uint32_t v2=kernel_ref(CALLARGS); double t2=now_ms();
    if(v1!=r1||v2!=r2||v1!=v2) match=0;
    if(t1-t0<bt)bt=t1-t0;
    if(t2-t1<bc)bc=t2-t1;
  }
  printf("%.5f %.5f %d %u %u\n", bt, bc, match, r1, r2);
  return 0;
}
"""

DRIVER_IV = r"""#include <stdio.h>
#include <stdint.h>
#include <time.h>
extern uint32_t kernel(void);
extern uint32_t kernel_ref(void);
static double now_ms(void){ return (double)clock_gettime_nsec_np(CLOCK_UPTIME_RAW)/1e6; }
int main(void){
  uint32_t r1 = kernel();
  uint32_t r2 = kernel_ref();
  int match = (r1==r2);
  double bt=1e18, bc=1e18;
  for(int rep=0;rep<7;rep++){
    double t0=now_ms(); uint32_t v1=kernel();     double t1=now_ms();
                        uint32_t v2=kernel_ref(); double t2=now_ms();
    if(v1!=r1||v2!=r2||v1!=v2) match=0;
    if(t1-t0<bt)bt=t1-t0;
    if(t2-t1<bc)bc=t2-t1;
  }
  printf("%.5f %.5f %d %u %u\n", bt, bc, match, r1, r2);
  return 0;
}
"""

def build_one(k):
    """k = dict(name, kind, red, shape, narr). Returns (k, ok, err)."""
    d = os.path.join(ROOT, k['name'].replace('/', '_').replace(':', '_'))
    os.makedirs(d, exist_ok=True)
    tir = os.path.join(d, "k.trust_ir"); refc = os.path.join(d, "ref.c"); drvc = os.path.join(d, "drv.c")
    if k['kind'] == 'array':
        open(tir, "w").write(gen_tir_array(k['red'], k['shape'], k['narr']))
        open(refc, "w").write(gen_c_array(k['red'], k['shape'], k['narr']))
        argdecl = ", ".join(["uint32_t*"] * k['narr'] + ["int"])
        callargs = ", ".join(["arr[%d]" % i for i in range(k['narr'])] + ["n"])
        drv = (DRIVER_ARRAY.replace("ARGDECL", argdecl).replace("CALLARGS", callargs)
               .replace("NELEM_N", str(NELEM)).replace("NARR", str(k['narr'])))
    else:
        open(tir, "w").write(gen_tir_iv(k['red'], k['shape']))
        open(refc, "w").write(gen_c_iv(k['red'], k['shape']))
        drv = DRIVER_IV
    open(drvc, "w").write(drv)
    to = os.path.join(d, "tcg.o"); ro = os.path.join(d, "ref.o"); b = os.path.join(d, "bench")
    r = subprocess.run([TCG, "--format=text", "--target", "aarch64", "-O2", "-c", tir, "-o", to],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return k, False, "TCG_COMPILE: " + (r.stderr or r.stdout).strip().splitlines()[-1][:120]
    r = subprocess.run(["cc", "-O3", "-c", refc, "-o", ro], capture_output=True, text=True)
    if r.returncode != 0:
        return k, False, "CLANG_COMPILE: " + r.stderr.strip()[:120]
    r = subprocess.run(["cc", "-O2", drvc, to, ro, "-o", b], capture_output=True, text=True)
    if r.returncode != 0:
        return k, False, "LINK: " + r.stderr.strip()[:120]
    k['bin'] = b
    return k, True, ""

def time_one(k):
    """Two independent process runs; min per side; flag >5% ratio disagreement."""
    runs = []
    for _ in range(2):
        r = subprocess.run([k['bin']], capture_output=True, text=True, timeout=300)
        parts = r.stdout.split()
        bt, bc, match = float(parts[0]), float(parts[1]), int(parts[2])
        runs.append((bt, bc, match))
    unstable = False
    if runs[0][1] > 1e-4 and runs[1][1] > 1e-4:
        rat0 = runs[0][0] / runs[0][1]; rat1 = runs[1][0] / runs[1][1]
        if abs(rat0 - rat1) / min(rat0, rat1) > 0.05:
            r = subprocess.run([k['bin']], capture_output=True, text=True, timeout=300)
            parts = r.stdout.split()
            runs.append((float(parts[0]), float(parts[1]), int(parts[2])))
            unstable = True
    bt = min(x[0] for x in runs); bc = min(x[1] for x in runs)
    match = all(x[2] == 1 for x in runs)
    return bt, bc, match, unstable

def main():
    rng = random.Random(SEED)
    space_arr = [(red, sh, 1) for red in REDS for sh in CTERM1] + \
                [(red, sh, 2) for red in REDS for sh in CTERM2]
    space_iv = [(red, t) for red in REDS for t in IVTERM_C]
    pick_arr = rng.sample(space_arr, 50)
    pick_iv = rng.sample(space_iv, 10)
    kernels = []
    for red, sh, narr in pick_arr:
        kernels.append({'name': f"{red}:{sh}", 'kind': 'array', 'red': red, 'shape': sh, 'narr': narr,
                        'cls': f"stream-{narr}arr"})
    for red, t in pick_iv:
        kernels.append({'name': f"{red}:iv:{t}", 'kind': 'iv', 'red': red, 'shape': t, 'narr': 0,
                        'cls': "iv-arith"})
    os.makedirs(ROOT, exist_ok=True)
    print(f"battery: {len(kernels)} kernels, seed={SEED}, n={NELEM}", flush=True)
    with ThreadPoolExecutor(max_workers=8) as ex:
        built = list(ex.map(build_one, kernels))
    fails = [(k['name'], err) for k, ok, err in built if not ok]
    results = []
    for k, ok, err in built:
        if not ok:
            print(f"BUILD-FAIL {k['name']}: {err}", flush=True)
            continue
        bt, bc, match, unstable = time_one(k)
        ratio = bt / bc if bc > 0 else float('inf')
        results.append({'name': k['name'], 'cls': k['cls'], 'tcg_ms': round(bt, 4),
                        'clang_ms': round(bc, 4), 'ratio': round(ratio, 4), 'match': match,
                        'unstable': unstable})
        flag = "" if match else "  *** MISMATCH P0 ***"
        us = " [unstable]" if unstable else ""
        print(f"{k['name']:18s} {k['cls']:12s} tcg={bt:9.4f} clang={bc:9.4f} ratio={ratio:8.3f} match={match}{us}{flag}", flush=True)
    out = os.path.join(ROOT, "results.json")
    json.dump({'results': results, 'build_fails': fails}, open(out, "w"), indent=1)
    # distribution
    ratios = [r['ratio'] for r in results]
    buckets = {'<0.95': 0, '0.95-1.05': 0, '1.05-1.2': 0, '1.2-1.5': 0, '>1.5': 0}
    for x in ratios:
        if x < 0.95: buckets['<0.95'] += 1
        elif x <= 1.05: buckets['0.95-1.05'] += 1
        elif x <= 1.2: buckets['1.05-1.2'] += 1
        elif x <= 1.5: buckets['1.2-1.5'] += 1
        else: buckets['>1.5'] += 1
    gm = math.exp(sum(math.log(x) for x in ratios) / len(ratios)) if ratios else 0
    print("\nbuckets:", buckets)
    print(f"geomean: {gm:.4f}")
    print(f"mismatches: {sum(1 for r in results if not r['match'])}")
    print(f"build fails: {fails}")
    ws = sorted(results, key=lambda r: -r['ratio'])[:10]
    print("\nworst 10:")
    for r in ws: print(" ", r)
    bs = sorted(results, key=lambda r: r['ratio'])[:5]
    print("best 5:")
    for r in bs: print(" ", r)

if __name__ == "__main__":
    main()
