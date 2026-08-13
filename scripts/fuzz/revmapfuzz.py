#!/usr/bin/env python3
# trust-cg - REVERSE (descending) memory-map differential + guard-page fuzzer (gap 2)
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Soundness fuzzer for the DESCENDING map vectorizer (gap 2): reverse in-place
maps `for i=n-1; i>=0; i--: a[i] = f(a[i])`. Single-array in-place (regime A)
needs no noalias, so it fires end-to-end in the CLI. Because a map's lanes are
independent, the descending vector loop must store BYTE-IDENTICAL memory to the
scalar reverse loop (and to the forward loop).

Per kernel it:
  * compiles trust-cg -O0 (scalar) and -O3 (descending vector),
  * links a harness that (a) checks the whole output array against a reference
    over trip counts 0..N, and (b) runs the exact-size kernel with the array
    flush against PROT_NONE GUARD PAGES on BOTH sides — a descending store/load
    that steps below a[0] or above a[n-1] faults, proving no OOB either way
    (backward OOB is the new risk for descending stores).

usage: revmapfuzz.py <trust-cg-binary> [--quick]
"""
import subprocess, sys, tempfile, os

TCG = sys.argv[1] if len(sys.argv) > 1 else "trust-cg"
QUICK = "--quick" in sys.argv

# f(a[i]): (trust_ir producing %25 from load %23 and consts %4(=1)/%5(=3)/%6(=0xff),
#           C expression over x). All in-place, single array.
FUNCS = {
    "mul3":  ("%25 = mul i32 %23, %5",         "x*3"),
    "add1":  ("%25 = add i32 %23, %4",         "x+1"),
    "xorself": ("%25 = xor i32 %23, %23",      "x^x"),
    "and_ff": ("%25 = and i32 %23, %6",        "x&0xff"),
    "shl1":  ("%25 = shl i32 %23, %4",         "x<<1"),
    "cube":  ("%24 = mul i32 %23, %23\n    %25 = mul i32 %24, %23", "x*x*x"),
}


def gen_tir(fn):
    body, _ = FUNCS[fn]
    return f"""; TrustIr text format v1
module "rm"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32) -> ()
fn @kernel(functy.0) {{
bb0(%0: ptr, %1: i32):
    %3 = const i32 0
    %4 = const i32 1
    %5 = const i32 3
    %6 = const i32 255
    %7 = sub i32 %1, %4
    br bb1(%7)
bb1(%10: i32):
    %11 = icmp sge i32 %10, %3
    condbr %11, bb3(%10), bb2()
bb3(%20: i32):
    %22 = gep i32, ptr %0, %20
    %23 = load i32, ptr %22
    {body}
    store i32 %25, ptr %22
    %28 = sub i32 %20, %4
    br bb1(%28)
bb2(): ret
}}
"""


def gen_ref_c(fn):
    _, expr = FUNCS[fn]
    return f"""#include <stdint.h>
/* Order-independent reference (map lanes are independent). */
void ref_kernel(int32_t *a, int32_t n){{
    for (int32_t i=0;i<n;i++){{ uint32_t x=(uint32_t)a[i]; a[i]=(int32_t)((uint32_t)({expr})); }}
}}
"""


HARNESS = r"""
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
extern void kernel(int32_t *a, int32_t n);
extern void ref_kernel(int32_t *a, int32_t n);
static int fails = 0;
static void test_correctness(int N){
    for (int n = 0; n <= N; n++){
        int32_t a[512], b[512];
        for (int i=0;i<N;i++){ a[i]=b[i]=(int32_t)((i*2654435761u) ^ (i-7)); }
        kernel(a, n); ref_kernel(b, n);
        if (memcmp(a, b, sizeof(int32_t)*N) != 0){ printf("MISMATCH n=%d\n", n); fails++; return; }
    }
}
static void test_guard(int NMAX){
    long pg = sysconf(_SC_PAGESIZE);
    for (int n = 1; n <= NMAX; n++){
        size_t bytes = (size_t)n*4, dp = (bytes+pg-1)/pg, total = (dp+2)*pg;
        char *base = mmap(NULL,total,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANON,-1,0);
        if (base==MAP_FAILED){ printf("mmap fail\n"); fails++; return; }
        mprotect(base, pg, PROT_NONE); mprotect(base+total-pg, pg, PROT_NONE);
        for (int side=0; side<2; side++){
            int32_t *a = side==0 ? (int32_t*)(base+total-pg-bytes) : (int32_t*)(base+pg);
            for (int i=0;i<n;i++) a[i]=i-3;
            kernel(a, n);
        }
        munmap(base, total);
    }
}
int main(void){ test_correctness(200); test_guard(300);
    printf(fails ? "FAIL\n" : "OK\n"); return fails?1:0; }
"""


def run(fn):
    with tempfile.TemporaryDirectory() as d:
        tf = os.path.join(d, "k.trust_ir"); open(tf, "w").write(gen_tir(fn))
        harn = os.path.join(d, "h.c"); open(harn, "w").write(HARNESS)
        refc = os.path.join(d, "ref.c"); open(refc, "w").write(gen_ref_c(fn))
        results = {}
        for o in ("O0", "O3"):
            obj = os.path.join(d, f"{o}.o")
            r = subprocess.run([TCG, "--format=text", "--target", "aarch64", f"-{o}",
                                "-c", tf, "-o", obj], capture_output=True, text=True)
            if r.returncode != 0:
                return ("COMPILE_ERR", r.stderr[:200])
            b = os.path.join(d, o)
            if subprocess.run(["cc", harn, refc, obj, "-o", b], capture_output=True).returncode != 0:
                return ("LINK_ERR", "")
            out = subprocess.run([b], capture_output=True, text=True)
            results[o] = out.stdout.strip()
            if out.returncode != 0:
                return ("RUNTIME_FAULT", f"{o}: {out.stdout.strip()}")
        if results["O0"] != "OK" or results["O3"] != "OK":
            return ("BADOUT", str(results))
    return ("OK", "")


def main():
    fns = ["mul3", "cube"] if QUICK else list(FUNCS)
    ok = bad = 0
    for fn in fns:
        st, msg = run(fn)
        if st == "OK":
            ok += 1
        else:
            print(f"[{st}] {fn}: {msg}"); bad += 1
    print(f"revmapfuzz: {ok} OK, {bad} fail")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
