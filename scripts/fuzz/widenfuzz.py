#!/usr/bin/env python3
"""
Widening byte/half reduction differential (TRACK B):
  sum_i8z : s(u32) += (u32)a_u8[i]        (UADDLP chain)
  sum_i8s : s(i32) += (i32)a_i8[i]        (SADDLP chain — SIGN edges!)
  sum_i16z: s(u32) += (u32)a_u16[i]       (UADDLP .8H->.4S)
  sum_i16s: s(i32) += (i32)a_i16[i]       (SADDLP .8H->.4S)
  pop_i8  : s(u32) += popcount(a_u8[i])   (CNT.16B + UDOT)
Compiles the SAME trust_ir kernel with the pass ON and OFF plus a clang -O2 C
reference; asserts BIT-IDENTICAL results across sign-edge patterns
(0x80/0x8000, 0xFF/0xFFFF, alternating +/-, random-signed) x n edge sizes.
usage: widenfuzz.py <trust-cg-binary>
"""
import sys, os, subprocess, tempfile

TIR_TMPL = """; TrustIr text format v1
module "k"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32) -> (i32)
fn @kernel(functy.0) {{
bb0(%1: ptr, %2: i32):
    %3 = const i32 0
    %4 = const i32 1
    %5 = const i32 0
    br bb1(%3, %5)
bb1(%6: i32, %7: i32):
    %8 = icmp slt i32 %6, %2
    condbr %8, bb3(%6, %7), bb2(%7)
bb3(%9: i32, %10: i32):
    %11 = gep {ety}, ptr %1, %9
    %12 = load {ety}, ptr %11
    %13 = {ext} {ety} %12 to i32
{popline}    %14 = add i32 %10, %{term}
    %15 = add i32 %9, %4
    br bb1(%15, %14)
bb2(%16: i32):
    ret %16
}}
"""

def tir(ety, ext, pop):
    popline = "    %17 = ctpop i32 %13\n" if pop else ""
    return TIR_TMPL.format(ety=ety, ext=ext, popline=popline, term="17" if pop else "13")

CREF_TMPL = """#include <stdint.h>
uint32_t kernel({cty}* a, int n){{
  uint32_t s = 0u;
  for (int i = 0; i < n; i++) s += {expr};
  return s;
}}
"""

KERNELS = {
    # name: (elem ty, ext, pop, C elem ty, C expr, expected-op substring)
    "sum_i8z":  ("i8",  "zext", False, "uint8_t",  "(uint32_t)a[i]", "uaddlp"),
    "sum_i8s":  ("i8",  "sext", False, "int8_t",   "(uint32_t)(int32_t)a[i]", "saddlp"),
    "sum_i16z": ("i16", "zext", False, "uint16_t", "(uint32_t)a[i]", "uaddlp"),
    "sum_i16s": ("i16", "sext", False, "int16_t",  "(uint32_t)(int32_t)a[i]", "saddlp"),
    "pop_i8":   ("i8",  "zext", True,  "uint8_t",  "(uint32_t)__builtin_popcount((uint32_t)a[i])", "udot"),
}

DRIVER = """#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern uint32_t kernel(void*, int);
int main(int argc, char** argv){
  int n = atoi(argv[1]);
  int pat = atoi(argv[2]);
  int esz = atoi(argv[3]);
  int m = n > 0 ? n : 1;
  unsigned char* a = malloc((size_t)m * esz);
  uint32_t s = 2463534242u;
  for (int i = 0; i < n; i++){
    uint32_t v;
    switch (pat){
      case 0: v = 0u; break;
      case 1: v = 0xFFFFFFFFu; break;               /* -1 / 0xFF / 0xFFFF */
      case 2: v = (esz==1) ? 0x80u : 0x8000u; break; /* most-negative */
      case 3: v = (i & 1) ? 1u : 0xFFFFFFFFu; break; /* alternating +1/-1 */
      case 4: v = (i & 1) ? 0x7Fu : 0x80u; break;    /* max-pos / min-neg */
      default: {
        s ^= s << 13; s ^= s >> 17; s ^= s << 5;
        v = s;
        int r = i % 11;
        if (r==0) v=0; else if (r==1) v=0xFFFFFFFFu; else if (r==2) v=(esz==1)?0x80u:0x8000u;
        else if (r==3) v=(esz==1)?0x7Fu:0x7FFFu; else if (r==4) v=1u;
      }
    }
    if (esz==1) ((uint8_t*)a)[i] = (uint8_t)v; else ((uint16_t*)a)[i] = (uint16_t)v;
  }
  printf("%u\\n", kernel(a, n));
  return 0;
}
"""

NS = [0,1,2,3,7,8,15,16,17,31,32,33,63,64,65,66,100,127,128,129,255,256,257,511,512,1000,4095,4096,4097]
PATS = [0,1,2,3,4,5]

def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

def main():
    tcg = sys.argv[1]
    wd = tempfile.mkdtemp(prefix="widenfuzz_")
    total = ok = mism = 0
    fails = []
    for name, (ety, ext, pop, cty, cexpr, opsub) in KERNELS.items():
        t = os.path.join(wd, name + ".trust_ir"); open(t, "w").write(tir(ety, ext, pop))
        c = os.path.join(wd, name + ".c"); open(c, "w").write(CREF_TMPL.format(cty=cty, expr=cexpr))
        d = os.path.join(wd, "drv.c"); open(d, "w").write(DRIVER)
        on_o, off_o, cl_o = [os.path.join(wd, name + x) for x in ("_on.o", "_off.o", "_cl.o")]
        env = dict(os.environ); env["TRUST_CG_DUMP_NEONARRAY"] = "1"
        r = run([tcg, "--format=text", "--target", "aarch64", "-O2", "-c", t, "-o", on_o], env=env)
        if r.returncode != 0:
            print(f"{name}: COMPILE_ON failed\n{r.stderr}"); sys.exit(2)
        fired = "neon-array" in r.stderr
        dis = run(["otool", "-tvV", on_o]).stdout
        has_op = opsub in dis
        envoff = dict(os.environ); envoff["TRUST_CG_DISABLE_PASSES"] = "neon_array"
        assert run([tcg, "--format=text", "--target", "aarch64", "-O2", "-c", t, "-o", off_o], env=envoff).returncode == 0
        assert run(["cc", "-O2", "-c", c, "-o", cl_o]).returncode == 0
        on_b, off_b, cl_b = [os.path.join(wd, name + x) for x in ("_on", "_off", "_cl")]
        for (obj, binp) in ((on_o, on_b), (off_o, off_b), (cl_o, cl_b)):
            assert run(["cc", d, obj, "-o", binp]).returncode == 0
        esz = "1" if ety == "i8" else "2"
        k_ok = k_mism = 0
        for pat in PATS:
            for n in NS:
                total += 1
                von = run([on_b, str(n), str(pat), esz]).stdout.strip()
                voff = run([off_b, str(n), str(pat), esz]).stdout.strip()
                vcl = run([cl_b, str(n), str(pat), esz]).stdout.strip()
                if von == voff == vcl and von != "":
                    ok += 1; k_ok += 1
                else:
                    mism += 1; k_mism += 1
                    fails.append((name, f"pat={pat} n={n}", f"on={von} off={voff} clang={vcl}"))
        print(f"{name}: fired={fired} {opsub}-emitted={has_op} ok={k_ok} mismatch={k_mism}")
        if not (fired and has_op):
            print(f"{name}: PASS DID NOT FIRE OR WRONG OPS — test not meaningful"); sys.exit(2)
    print(f"\n=== widening differential: {total} runs, OK={ok} MISMATCH={mism} ===")
    if fails:
        for f in fails[:20]:
            print("FAIL:", f)
        sys.exit(1)
    print("ALL BIT-IDENTICAL (on == off == clang)")

if __name__ == "__main__":
    main()
