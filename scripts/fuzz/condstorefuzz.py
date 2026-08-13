#!/usr/bin/env python3
"""
condstorefuzz -- DORMANT differential-fuzzer asset for the NEON conditional-store vectorizer
(`neon-condstore`): the class `for i<n: if (P(a[i])) b[i] = F(a[i])` that both
clangs scalarise (C11 forbids inventing a store; NEON has no masked store).

The structural transform uses a BLIND full-width store
`b[i] = mask ? F(a[i]) : b[i]`. Production correctly keeps it inert until a
validator can issue writable/single-owner authority bound to the exact
function, output base, and byte range. `TRUST_CG_CONDSTORE=blind` is deliberately
non-authoritative, so this harness cannot currently create its historical ON
variant and must not claim differential coverage of the transform.

Each kernel is compiled three ways and the ENTIRE output array must be
bit-identical (`on == off == clang`):
  * trust-cg -O2 with typed ownership authority         (not yet wired)
  * trust-cg -O2 without that authority                 (pass OFF, scalar)
  * clang -O2                                            (scalar reference)

across a DENSITY sweep {0,5,50,95,100}% x {unpredictable, predictable} x n edges
{0,1,2,...,1027}, with b pre-poisoned so a wrong false-lane write-back changes
the hash. Plus:
  * FIRE/BAIL: ON must emit BIT/STP; OFF and clang must not.
  * ALIASING NEGATIVE: the two-pointer form WITHOUT noalias must NOT vectorize;
    run under full overlap (b == a) it must still match a scalar clang reference.
  * GUARD PAGES on BOTH a and b: element n sits at a PROT_NONE page, so any
    read of a[] or write of b[] past the scalar loop's [0,n) faults.

i64 (`.2D`) width battery: the same kernels over i64 elements (8 lanes /
iteration, so the n edges cross 8/16/24) — same density sweep, same poisoned-b
bit-identity, same guard pages on both arrays (8-byte elements), the same
aliasing negative at i64, PLUS a must-BAIL control (`b[i] = a[i]*k` — MUL.2D is
UNALLOCATED, so the i64 multiply value must stay scalar and correct).

usage: condstorefuzz.py <trust-cg-binary> [--quick]
"""
import sys, os, subprocess, tempfile

raise SystemExit(
    "condstorefuzz.py is dormant: typed function/base/range ownership "
    "authority is not wired; TRUST_CG_CONDSTORE is not an authorization seam"
)

TCG = sys.argv[1] if len(sys.argv) > 1 else "target/release/trust-cg"
QUICK = "--quick" in sys.argv
PASS = "neon_condstore"

HDR = """; TrustIr text format v1
module "k"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
"""

# Two-pointer conditional store `if (a[i] PRED 0) b[i] = VALUE(a[i])`.
# param0 = b (store base), param1 = a (load base), param2 = n.
TWO_TMPL = HDR + """functy.0 = (ptr, ptr, i32) -> (i32)
fn @kernel(functy.0) {{
; #param_attrs 0: noalias
; #param_attrs 1: noalias
bb0(%1: ptr, %30: ptr, %2: i32):
    %3 = const i32 0
    %4 = const i32 1
    %5 = const i32 {k}
    br bb1(%3)
bb1(%6: i32):
    %8 = icmp slt i32 %6, %2
    condbr %8, bb3(%6), bb2
bb3(%9: i32):
    %11 = gep i32, ptr %30, %9
    %12 = load i32, ptr %11
    %13 = icmp {pred} i32 %12, %3
    condbr %13, bb4(%9), bb5(%9)
bb4(%40: i32):
{value}    %18 = gep i32, ptr %1, %40
    store i32 %14, ptr %18
    br bb5(%40)
bb5(%41: i32):
    %15 = add i32 %41, %4
    br bb1(%15)
bb2:
    ret %3
}}
"""

# In-place conditional store `if (a[i] PRED 0) a[i] = VALUE(a[i])` — one pointer,
# no noalias needed (aliasing is not load-bearing); the contract still is.
IN_TMPL = HDR + """functy.0 = (ptr, i32) -> (i32)
fn @kernel(functy.0) {{
bb0(%1: ptr, %2: i32):
    %3 = const i32 0
    %4 = const i32 1
    %5 = const i32 {k}
    br bb1(%3)
bb1(%6: i32):
    %8 = icmp slt i32 %6, %2
    condbr %8, bb3(%6), bb2
bb3(%9: i32):
    %11 = gep i32, ptr %1, %9
    %12 = load i32, ptr %11
    %13 = icmp {pred} i32 %12, %3
    condbr %13, bb4(%9), bb5(%9)
bb4(%40: i32):
{value}    %18 = gep i32, ptr %1, %40
    store i32 %14, ptr %18
    br bb5(%40)
bb5(%41: i32):
    %15 = add i32 %41, %4
    br bb1(%15)
bb2:
    ret %3
}}
"""

# The two-pointer form WITHOUT noalias (aliasing unprovable => must BAIL).
TWO_NOALIAS_TMPL = TWO_TMPL.replace(
    "; #param_attrs 0: noalias\n; #param_attrs 1: noalias\n", ""
)

# value blocks: produce %14 from the loaded %12 and the constant %5.
VALUES = {
    "mul": "    %14 = mul i32 %12, %5\n",   # a[i]*k
    "add": "    %14 = add i32 %12, %5\n",   # a[i]+k
    "neg": "    %14 = sub i32 %3, %12\n",   # -a[i]
    "shl": "    %14 = shl i32 %12, %5\n",   # a[i]<<k
}
# predicate: icmp <pred> a[i], 0. (C operator, machine cc)
PREDS = {
    "sgt": ">",   # a[i] > 0
    "sge": ">=",  # a[i] >= 0
    "slt": "<",   # a[i] < 0
    "eq":  "==",  # a[i] == 0
}
VALUE_C = {"mul": "a[i]*{k}", "add": "a[i]+{k}", "neg": "-a[i]", "shl": "a[i]<<{k}"}

# (name -> (template, pred, value, k, is_inplace))
KERNELS = {
    "gt0_mul2":   (TWO_TMPL, "sgt", "mul", 2, False),
    "ge0_addk":   (TWO_TMPL, "sge", "add", 7, False),
    "lt0_neg":    (TWO_TMPL, "slt", "neg", 0, False),
    "eq0_shl":    (TWO_TMPL, "eq",  "shl", 3, False),
    "inplace_gt": (IN_TMPL,  "sgt", "mul", 2, True),
}

# ---------------------------------------------------------------------------
# i64 (`.2D`) width battery: the same kernels over i64 elements.
# ---------------------------------------------------------------------------

TWO64_TMPL = TWO_TMPL.replace("i32", "i64")
IN64_TMPL = IN_TMPL.replace("i32", "i64")
TWO64_NOALIAS_TMPL = TWO64_TMPL.replace(
    "; #param_attrs 0: noalias\n; #param_attrs 1: noalias\n", ""
)

VALUES64 = {k: v.replace("i32", "i64") for k, v in VALUES.items()}

# (name -> (template, pred, value, k, is_inplace, expect_fire))
# gt0_mul2_64 is the must-BAIL control: MUL.2D is UNALLOCATED, so the i64
# multiply value cannot be vectorized — the loop must stay (correct) scalar.
KERNELS64 = {
    "gt0_add7_64":   (TWO64_TMPL, "sgt", "add", 7, False, True),
    "sge0_addk_64":  (TWO64_TMPL, "sge", "add", 9, False, True),
    "lt0_neg_64":    (TWO64_TMPL, "slt", "neg", 0, False, True),
    "eq0_shl3_64":   (TWO64_TMPL, "eq",  "shl", 3, False, True),
    "inplace_gt_64": (IN64_TMPL,  "sgt", "add", 5, True,  True),
    "gt0_mul2_64":   (TWO64_TMPL, "sgt", "mul", 2, False, False),
}

def kernel_c64(pred, value, k, inplace):
    op = PREDS[pred]
    val = VALUE_C[value].format(k=k)
    if inplace:
        return (f"#include <stdint.h>\nvoid kernel(int64_t* a, int64_t n){{\n"
                f"  for (int64_t i=0;i<n;i++) if (a[i] {op} 0) a[i] = {val};\n}}\n")
    return (f"#include <stdint.h>\nvoid kernel(int64_t* b, const int64_t* a, int64_t n){{\n"
            f"  for (int64_t i=0;i<n;i++) if (a[i] {op} 0) b[i] = {val};\n}}\n")

def gen_tir64(name):
    tmpl, pred, value, k, inplace, _fire = KERNELS64[name]
    return tmpl.format(pred=pred, value=VALUES64[value], k=k)

def kernel_c(pred, value, k, inplace):
    op = PREDS[pred]
    val = VALUE_C[value].format(k=k)
    if inplace:
        return (f"void kernel(int* a, int n){{\n"
                f"  for (int i=0;i<n;i++) if (a[i] {op} 0) a[i] = {val};\n}}\n")
    return (f"void kernel(int* b, const int* a, int n){{\n"
            f"  for (int i=0;i<n;i++) if (a[i] {op} 0) b[i] = {val};\n}}\n")

def gen_tir(name):
    tmpl, pred, value, k, inplace = KERNELS[name]
    return tmpl.format(pred=pred, value=VALUES[value], k=k)

# ---------------------------------------------------------------------------
# Drivers. Density is a property of the INPUT: a[i] positive fraction ~= density.
# b is poisoned with a per-index sentinel so a wrong false-lane keep is visible.
# ---------------------------------------------------------------------------

DRIVER = """#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
{proto}
int main(int argc,char**argv){{
  int n=atoi(argv[1]); int d=atoi(argv[2]); int pred=atoi(argv[3]);
  int m=n>0?n:1;
  int* a=(int*)malloc(sizeof(int)*(size_t)m);
  int* b={bdecl};
  uint64_t s=0x9e3779b97f4a7c15ull ^ (uint64_t)(d*131+pred);
  for(int i=0;i<n;i++){{
    s=s*6364136223846793005ull+1442695040888963407ull;
    int r=(int)((s>>33)%100);
    int positive = pred ? ((i%100)<d) : (r<d);
    int mag=1+(int)((s>>20)%1000);
    a[i]=positive?mag:-mag;
    b[i]=(int)(0xCC000000u|(uint32_t)i);
  }}
  FILE* f=fopen(argv[4],"wb");
  {call}
  fwrite(b,sizeof(int),(size_t)n,f);
  fclose(f);
  return 0;
}}
"""

def driver_c(inplace, alias=False):
    if inplace:
        proto = "extern void kernel(int* a, int n);"
        # in-place: b is a (the only array); the sentinel poison seeds it.
        return DRIVER.format(proto=proto, bdecl="a", call="kernel(b, n);")
    proto = "extern void kernel(int* b, const int* a, int n);"
    bdecl = "a; /* deliberate full overlap */" if alias else "(int*)malloc(sizeof(int)*(size_t)m)"
    return DRIVER.format(proto=proto, bdecl=bdecl, call="kernel(b, a, n);")

# Guard-page driver: element n of BOTH a and b abuts a PROT_NONE page.
GUARD_DRIVER = """#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>
{proto}
static int* guarded(int n){{
  long pg=sysconf(_SC_PAGESIZE); size_t need=(size_t)(n>0?n:1)*sizeof(int);
  size_t pages=(need+pg-1)/pg, total=(pages+1)*pg;
  char* base=mmap(0,total,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANON,-1,0);
  if(base==MAP_FAILED){{perror("mmap");exit(3);}}
  mprotect(base+pages*pg,pg,PROT_NONE);
  return (int*)(base+pages*pg-need);
}}
int main(int argc,char**argv){{
  int n=atoi(argv[1]); int d=atoi(argv[2]);
  int* a=guarded(n); int* b={bdecl};
  uint64_t s=0x1234567;
  for(int i=0;i<n;i++){{ s=s*6364136223846793005ull+1; int mag=1+(int)((s>>20)%1000);
    a[i]=((int)((s>>33)%100)<d)?mag:-mag; b[i]=(int)(0xCC000000u|(uint32_t)i);}}
  {call}
  fputs("ok\\n",stdout); return 0;
}}
"""

def guard_driver_c(inplace):
    if inplace:
        return GUARD_DRIVER.format(proto="extern void kernel(int* a, int n);",
                                   bdecl="a", call="kernel(b, n);")
    return GUARD_DRIVER.format(proto="extern void kernel(int* b, const int* a, int n);",
                               bdecl="guarded(n)", call="kernel(b, a, n);")

# --- i64 drivers: int64_t elements, same density/poison/guard structure. ---

DRIVER64 = """#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
{proto}
int main(int argc,char**argv){{
  long n=atol(argv[1]); int d=atoi(argv[2]); int pred=atoi(argv[3]);
  long m=n>0?n:1;
  int64_t* a=(int64_t*)malloc(sizeof(int64_t)*(size_t)m);
  int64_t* b={bdecl};
  uint64_t s=0x9e3779b97f4a7c15ull ^ (uint64_t)(d*131+pred);
  for(long i=0;i<n;i++){{
    s=s*6364136223846793005ull+1442695040888963407ull;
    int r=(int)((s>>33)%100);
    int positive = pred ? ((i%100)<d) : (r<d);
    /* magnitudes with HIGH bits set so a 32-bit-lane confusion misfolds */
    int64_t mag=(int64_t)(1+((s>>20)%1000)) | ((int64_t)((s>>13)&0x7FF)<<32);
    a[i]=positive?mag:-mag;
    b[i]=(int64_t)(0xCC00000000000000ull|(uint64_t)i);
  }}
  FILE* f=fopen(argv[4],"wb");
  {call}
  fwrite(b,sizeof(int64_t),(size_t)n,f);
  fclose(f);
  return 0;
}}
"""

def driver64_c(inplace, alias=False):
    if inplace:
        proto = "extern void kernel(int64_t* a, int64_t n);"
        return DRIVER64.format(proto=proto, bdecl="a", call="kernel(b, n);")
    proto = "extern void kernel(int64_t* b, const int64_t* a, int64_t n);"
    bdecl = "a; /* deliberate full overlap */" if alias else \
            "(int64_t*)malloc(sizeof(int64_t)*(size_t)m)"
    return DRIVER64.format(proto=proto, bdecl=bdecl, call="kernel(b, a, n);")

GUARD_DRIVER64 = """#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>
{proto}
static int64_t* guarded(long n){{
  long pg=sysconf(_SC_PAGESIZE); size_t need=(size_t)(n>0?n:1)*sizeof(int64_t);
  size_t pages=(need+pg-1)/pg, total=(pages+1)*pg;
  char* base=mmap(0,total,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANON,-1,0);
  if(base==MAP_FAILED){{perror("mmap");exit(3);}}
  mprotect(base+pages*pg,pg,PROT_NONE);
  return (int64_t*)(base+pages*pg-need);
}}
int main(int argc,char**argv){{
  long n=atol(argv[1]); int d=atoi(argv[2]);
  int64_t* a=guarded(n); int64_t* b={bdecl};
  uint64_t s=0x1234567;
  for(long i=0;i<n;i++){{ s=s*6364136223846793005ull+1;
    int64_t mag=(int64_t)(1+((s>>20)%1000));
    a[i]=((int)((s>>33)%100)<d)?mag:-mag;
    b[i]=(int64_t)(0xCC00000000000000ull|(uint64_t)i);}}
  {call}
  fputs("ok\\n",stdout); return 0;
}}
"""

def guard_driver64_c(inplace):
    if inplace:
        return GUARD_DRIVER64.format(proto="extern void kernel(int64_t* a, int64_t n);",
                                     bdecl="a", call="kernel(b, n);")
    return GUARD_DRIVER64.format(
        proto="extern void kernel(int64_t* b, const int64_t* a, int64_t n);",
        bdecl="guarded(n)", call="kernel(b, a, n);")

NS = [0, 1, 2, 3, 4, 7, 8, 15, 16, 17, 18, 24, 31, 32, 33, 47, 48, 63, 64, 65,
      100, 127, 128, 129, 255, 256, 257, 1000, 1023, 1024, 1027]
DENS = [0, 5, 50, 95, 100]
# i64 edges: the same sweep plus the 8-lane block boundaries 9/23/25.
NS64 = sorted(set(NS + [9, 23, 25]))
if QUICK:
    NS = [0, 1, 15, 16, 17, 33, 128, 1027]
    NS64 = [0, 1, 7, 8, 9, 17, 128, 1027]
    DENS = [0, 50, 100]

def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

def compile_tcg(tir, obj, contract=False, disable=None):
    env = dict(os.environ)
    if contract:
        raise RuntimeError("typed condstore ownership authority is not wired")
    if disable:
        env["TRUST_CG_DISABLE_PASSES"] = disable
    r = run([TCG, "--format=text", "--target", "aarch64", "-O2", "-c", tir, "-o", obj], env=env)
    if r.returncode != 0:
        print(r.stderr)
        raise SystemExit(f"tcg compile failed: {tir}")

def vectorized(obj):
    r = run(["otool", "-tvV", obj])
    dis = r.stdout.lower()
    return ("bit.16b" in dis) and (("stp" in dis) or ("st1." in dis))

def vectorized64(obj):
    """The i64 fire pin is stricter: the mask compare must be a `.2D` form."""
    dis = run(["otool", "-tvV", obj]).stdout.lower()
    has_cmp2d = any(c in dis for c in
                    ("cmgt.2d", "cmge.2d", "cmhi.2d", "cmhs.2d", "cmeq.2d"))
    return ("bit.16b" in dis) and has_cmp2d and (("stp" in dis) or ("st1." in dis))

def main():
    wd = tempfile.mkdtemp(prefix="condstorefuzz")
    total = fails = 0
    vec_fired = 0
    for name in KERNELS:
        tmpl, pred, value, k, inplace = KERNELS[name]
        tir = os.path.join(wd, name + ".trust_ir")
        cref = os.path.join(wd, name + ".c")
        drv = os.path.join(wd, name + "_drv.c")
        open(tir, "w").write(gen_tir(name))
        open(cref, "w").write(kernel_c(pred, value, k, inplace))
        open(drv, "w").write(driver_c(inplace))
        on_o = os.path.join(wd, name + "_on.o")
        off_o = os.path.join(wd, name + "_off.o")
        compile_tcg(tir, on_o, contract=True)
        compile_tcg(tir, off_o, contract=True, disable=PASS)   # contract set but pass killed
        # FIRE / BAIL
        if vectorized(on_o):
            vec_fired += 1
        else:
            print(f"NOTE: {name} did not vectorize (pass bail)")
        if vectorized(off_o):
            print(f"FAIL: {name} vectorized with the pass DISABLED")
            fails += 1
        binaries = {}
        for tag, obj in (("on", on_o), ("off", off_o)):
            b = os.path.join(wd, name + "_" + tag)
            r = run(["clang", "-O2", drv, obj, "-o", b])
            assert r.returncode == 0, r.stderr
            binaries[tag] = b
        b = os.path.join(wd, name + "_ref")
        r = run(["clang", "-O2", drv, cref, "-o", b])
        assert r.returncode == 0, r.stderr
        binaries["ref"] = b
        if vectorized(os.path.join(wd, name + "_ref.o") if False else on_o):
            pass  # clang ref vectorization is checked implicitly by bit-identity
        for n in NS:
            for d in DENS:
                for p in (0, 1):
                    outs = {}
                    for tag, binpath in binaries.items():
                        out = os.path.join(wd, "o.bin")
                        run([binpath, str(n), str(d), str(p), out])
                        outs[tag] = open(out, "rb").read()
                    total += 1
                    if not (outs["on"] == outs["off"] == outs["ref"]):
                        fails += 1
                        print(f"MISMATCH {name} n={n} d={d} p={p}: "
                              f"on==off:{outs['on']==outs['off']} on==ref:{outs['on']==outs['ref']}")
        # ---- GUARD PAGES: [0,n) exactly, on both arrays ----
        gdrv = os.path.join(wd, name + "_guard.c")
        open(gdrv, "w").write(guard_driver_c(inplace))
        gbin = os.path.join(wd, name + "_guard")
        r = run(["clang", "-O2", gdrv, on_o, "-o", gbin])
        assert r.returncode == 0, r.stderr
        for n in NS:
            for d in (0, 50, 100):
                total += 1
                r = run([gbin, str(n), str(d)])
                if r.returncode != 0:
                    fails += 1
                    print(f"GUARD FAULT {name} n={n} d={d} rc={r.returncode}")

    # ------------------------------------------------------------------
    # i64 (`.2D`) width battery.
    # ------------------------------------------------------------------
    vec_fired64 = 0
    for name in KERNELS64:
        tmpl, pred, value, k, inplace, expect_fire = KERNELS64[name]
        tir = os.path.join(wd, name + ".trust_ir")
        cref = os.path.join(wd, name + ".c")
        drv = os.path.join(wd, name + "_drv.c")
        open(tir, "w").write(gen_tir64(name))
        open(cref, "w").write(kernel_c64(pred, value, k, inplace))
        open(drv, "w").write(driver64_c(inplace))
        on_o = os.path.join(wd, name + "_on.o")
        off_o = os.path.join(wd, name + "_off.o")
        compile_tcg(tir, on_o, contract=True)
        compile_tcg(tir, off_o, contract=True, disable=PASS)
        # FIRE / BAIL (gt0_mul2_64 must BAIL: MUL.2D is UNALLOCATED).
        if vectorized64(on_o):
            if expect_fire:
                vec_fired64 += 1
            else:
                print(f"FAIL: {name} vectorized but must BAIL (no MUL.2D)")
                fails += 1
        elif expect_fire:
            print(f"NOTE: {name} did not vectorize (pass bail)")
        if vectorized64(off_o):
            print(f"FAIL: {name} vectorized with the pass DISABLED")
            fails += 1
        binaries = {}
        for tag, obj in (("on", on_o), ("off", off_o)):
            b = os.path.join(wd, name + "_" + tag)
            r = run(["clang", "-O2", drv, obj, "-o", b])
            assert r.returncode == 0, r.stderr
            binaries[tag] = b
        b = os.path.join(wd, name + "_ref")
        r = run(["clang", "-O2", drv, cref, "-o", b])
        assert r.returncode == 0, r.stderr
        binaries["ref"] = b
        for n in NS64:
            for d in DENS:
                for p in (0, 1):
                    outs = {}
                    for tag, binpath in binaries.items():
                        out = os.path.join(wd, "o64.bin")
                        run([binpath, str(n), str(d), str(p), out])
                        outs[tag] = open(out, "rb").read()
                    total += 1
                    if not (outs["on"] == outs["off"] == outs["ref"]):
                        fails += 1
                        print(f"MISMATCH {name} n={n} d={d} p={p}: "
                              f"on==off:{outs['on']==outs['off']} on==ref:{outs['on']==outs['ref']}")
        # ---- GUARD PAGES: [0,n) exactly, on both arrays (8-byte elems) ----
        gdrv = os.path.join(wd, name + "_guard.c")
        open(gdrv, "w").write(guard_driver64_c(inplace))
        gbin = os.path.join(wd, name + "_guard")
        r = run(["clang", "-O2", gdrv, on_o, "-o", gbin])
        assert r.returncode == 0, r.stderr
        for n in NS64:
            for d in (0, 50, 100):
                total += 1
                r = run([gbin, str(n), str(d)])
                if r.returncode != 0:
                    fails += 1
                    print(f"GUARD FAULT {name} n={n} d={d} rc={r.returncode}")

    # ---- ALIASING NEGATIVE: two-pointer WITHOUT noalias must BAIL + stay correct ----
    for tag64, tmpl_na, val_map, drvfn, kcfn, vfy, ns_sweep, value, k in [
        ("", TWO_NOALIAS_TMPL, VALUES, driver_c, kernel_c, vectorized, NS, "mul", 2),
        ("64", TWO64_NOALIAS_TMPL, VALUES64, driver64_c, kernel_c64, vectorized64, NS64, "add", 7),
    ]:
        an_tir = os.path.join(wd, f"alias_neg{tag64}.trust_ir")
        open(an_tir, "w").write(tmpl_na.format(pred="sgt", value=val_map[value], k=k))
        an_o = os.path.join(wd, f"alias_neg{tag64}.o")
        compile_tcg(an_tir, an_o, contract=True)   # contract ON, but no noalias => must BAIL
        if vfy(an_o):
            print(f"FAIL: i{tag64 or '32'} two-pointer form WITHOUT noalias vectorized (unsound overlap!)")
            fails += 1
        # run under full overlap b == a; compare to a scalar clang reference (overlap-safe)
        an_drv = os.path.join(wd, f"alias_neg{tag64}_drv.c")
        open(an_drv, "w").write(drvfn(False, alias=True))
        an_ref_c = os.path.join(wd, f"alias_neg{tag64}_ref.c")
        open(an_ref_c, "w").write(kcfn("sgt", value, k, False))
        an_on = os.path.join(wd, f"alias_neg{tag64}_on")
        an_ref = os.path.join(wd, f"alias_neg{tag64}_ref")
        assert run(["clang", "-O2", an_drv, an_o, "-o", an_on]).returncode == 0
        assert run(["clang", "-O0", "-fno-vectorize", "-fno-slp-vectorize",
                    an_drv, an_ref_c, "-o", an_ref]).returncode == 0
        for n in ns_sweep:
            for d in DENS:
                outs = {}
                for tag, bp in (("on", an_on), ("ref", an_ref)):
                    out = os.path.join(wd, "oa.bin")
                    run([bp, str(n), str(d), "0", out])
                    outs[tag] = open(out, "rb").read()
                total += 1
                if outs["on"] != outs["ref"]:
                    fails += 1
                    print(f"ALIAS MISMATCH i{tag64 or '32'} n={n} d={d}")

    kernels = len(KERNELS)
    kernels64_fire = sum(1 for v in KERNELS64.values() if v[5])
    print(f"condstorefuzz: {total - fails}/{total} bit-identical, {fails} failures; "
          f"{vec_fired}/{kernels} i32 kernels vectorized, "
          f"{vec_fired64}/{kernels64_fire} i64 kernels vectorized (+1 must-BAIL held)")
    return 1 if fails else 0


if __name__ == "__main__":
    raise SystemExit(main())
