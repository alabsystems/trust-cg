#!/usr/bin/env python3
"""
i64 (`.2D`) width-parameterization differential (TRACK A):
  ceq   : s += (a[i] == k) ? 1 : 0      (predsum: CMEQ.2D + SUB.2D fusion)
  clamp : s += (a[i] > 0) ? a[i] : 0    (predsum: CMGT.2D + AND)
  smin  : m = min_signed(m, a[i])       (minmax: CMGT.2D + EOR/AND bitselect)
  smax  : m = max_signed(m, a[i])
  umin  : m = min_unsigned(m, a[i])
  umax  : m = max_unsigned(m, a[i])
  xorred: x ^= a[i]                     (minmax bitwise)
  prod  : p *= a[i]                     (minmax: must BAIL — no MUL.2D)
  mapadd: a[i] = b[i] + 7               (map: ADD.2D + ST1.2D)
  mapmul: a[i] = b[i] * 7               (map: must BAIL — no MUL.2D)
Each kernel is compiled pass-ON and pass-OFF plus a clang -O2 C reference;
asserts BIT-IDENTICAL results across sign-edge patterns (INT64_MIN, -1,
alternating +/-, high-bit random) x n edges.  BAIL kernels additionally assert
NO vector op was emitted.
usage: i64widefuzz.py <trust-cg-binary>
"""
import sys, os, subprocess, tempfile

HDR = """; TrustIr text format v1
module "k"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
"""

RED_TMPL = HDR + """functy.0 = (ptr, i64, i64) -> (i64)
fn @kernel(functy.0) {{
bb0(%1: ptr, %2: i64, %20: i64):
    %3 = const i64 0
    %4 = const i64 1
    br bb1(%3, %{init})
bb1(%6: i64, %7: i64):
    %8 = icmp slt i64 %6, %2
    condbr %8, bb3(%6, %7), bb2(%7)
bb3(%9: i64, %10: i64):
    %11 = gep i64, ptr %1, %9
    %12 = load i64, ptr %11
{body}    %15 = add i64 %9, %4
    br bb1(%15, %{next})
bb2(%16: i64):
    ret %16
}}
"""

MAP_TMPL = HDR + """functy.0 = (ptr, ptr, i64) -> (i64)
fn @kernel(functy.0) {{
; #param_attrs 0: noalias
; #param_attrs 1: noalias
bb0(%1: ptr, %30: ptr, %2: i64):
    %3 = const i64 0
    %4 = const i64 1
    %21 = const i64 7
    br bb1(%3)
bb1(%6: i64):
    %8 = icmp slt i64 %6, %2
    condbr %8, bb3(%6), bb2
bb3(%9: i64):
    %11 = gep i64, ptr %30, %9
    %12 = load i64, ptr %11
    %13 = {op} i64 %12, %21
    %18 = gep i64, ptr %1, %9
    store i64 %13, ptr %18
    %15 = add i64 %9, %4
    br bb1(%15)
bb2:
    ret %3
}}
"""

def red(body, init="3", next_="14"):
    return RED_TMPL.format(body=body, init=init, next=next_)

KERNELS = {
    # name: (tir, C body, expected fire?, op substring, is_map)
    "ceq": (red("""    %13 = icmp eq i64 %12, %20
    %17 = select i64 %13, %4, %3
    %14 = add i64 %10, %17
"""), "s += (a[i] == k) ? 1 : 0;", True, "cmeq.2d", False),
    "clamp": (red("""    %13 = icmp sgt i64 %12, %3
    %17 = select i64 %13, %12, %3
    %14 = add i64 %10, %17
"""), "s += ((int64_t)a[i] > 0) ? (uint64_t)a[i] : 0;", True, "cmgt.2d", False),
    "smin": (red("""    %13 = icmp slt i64 %12, %10
    %14 = select i64 %13, %12, %10
""", init="5"), "s = ((int64_t)a[i] < (int64_t)s) ? a[i] : s;", True, "cmgt.2d", False),
    "smax": (red("""    %13 = icmp sgt i64 %12, %10
    %14 = select i64 %13, %12, %10
""", init="6"), "s = ((int64_t)a[i] > (int64_t)s) ? a[i] : s;", True, "cmgt.2d", False),
    "umin": (red("""    %13 = icmp ult i64 %12, %10
    %14 = select i64 %13, %12, %10
""", init="7"), "s = (a[i] < s) ? a[i] : s;", True, "cmhi.2d", False),
    "umax": (red("""    %13 = icmp ugt i64 %12, %10
    %14 = select i64 %13, %12, %10
""", init="3"), "s = (a[i] > s) ? a[i] : s;", True, "cmhi.2d", False),
    "xorred": (red("""    %14 = xor i64 %10, %12
"""), "s ^= a[i];", True, "eor.16b", False),
    "prod": (red("""    %14 = mul i64 %10, %12
""", init="4"), "s *= a[i];", False, "", False),
    "mapadd": (MAP_TMPL.format(op="add"), "a[i] = b[i] + 7;", True, ("st1.2d","stp"), True),
    "mapmul": (MAP_TMPL.format(op="mul"), "a[i] = b[i] * 7;", False, "", True),
}

INITS = {"smin": "0x7FFFFFFFFFFFFFFF", "smax": "0x8000000000000000",
         "umin": "0xFFFFFFFFFFFFFFFF", "prod": "1"}

CRED_TMPL = """#include <stdint.h>
uint64_t kernel(uint64_t* a, int64_t n, uint64_t k){{
  uint64_t s = {init};
  (void)k;
  for (int64_t i = 0; i < n; i++) {{ {body} }}
  return s;
}}
"""
CMAP_TMPL = """#include <stdint.h>
uint64_t kernel(uint64_t* restrict a, uint64_t* restrict b, int64_t n){{
  for (int64_t i = 0; i < n; i++) {{ {body} }}
  return 0;
}}
"""

DRIVER_RED = """#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
extern uint64_t kernel(uint64_t*, int64_t, uint64_t);
int main(int argc, char** argv){
  long n = atol(argv[1]); int pat = atoi(argv[2]);
  long m = n > 0 ? n : 1;
  uint64_t* a = malloc(sizeof(uint64_t)*m);
  uint64_t s = 88172645463325252ull;
  for (long i = 0; i < n; i++){
    uint64_t v;
    switch (pat){
      case 0: v = 0; break;
      case 1: v = 0xFFFFFFFFFFFFFFFFull; break;               /* -1 */
      case 2: v = 0x8000000000000000ull; break;               /* INT64_MIN */
      case 3: v = (i & 1) ? 1 : 0xFFFFFFFFFFFFFFFFull; break; /* +1/-1 */
      case 4: v = (i & 1) ? 0x7FFFFFFFFFFFFFFFull : 0x8000000000000000ull; break;
      default: {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17; v = s;
        int r = i % 9;
        if (r==0) v=0; else if (r==1) v=0xFFFFFFFFFFFFFFFFull;
        else if (r==2) v=0x8000000000000000ull; else if (r==3) v=0x7FFFFFFFFFFFFFFFull;
        else if (r==4) v=42;
      }
    }
    a[i] = v;
  }
  printf("%llu\\n", (unsigned long long)kernel(a, n, 42));
  return 0;
}
"""

DRIVER_MAP = """#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
extern uint64_t kernel(uint64_t*, uint64_t*, int64_t);
int main(int argc, char** argv){
  long n = atol(argv[1]); int pat = atoi(argv[2]);
  long m = n > 0 ? n : 1;
  uint64_t* a = malloc(sizeof(uint64_t)*m);
  uint64_t* b = malloc(sizeof(uint64_t)*m);
  uint64_t s = 88172645463325252ull;
  for (long i = 0; i < n; i++){
    uint64_t v;
    switch (pat){
      case 0: v = 0; break;
      case 1: v = 0xFFFFFFFFFFFFFFFFull; break;
      case 2: v = 0x8000000000000000ull; break;
      case 3: v = (i & 1) ? 1 : 0xFFFFFFFFFFFFFFFFull; break;
      case 4: v = (i & 1) ? 0x7FFFFFFFFFFFFFFFull : 0x8000000000000000ull; break;
      default: { s ^= s << 13; s ^= s >> 7; s ^= s << 17; v = s; }
    }
    b[i] = v; a[i] = 0xCCCCCCCCCCCCCCCCull;
  }
  kernel(a, b, n);
  uint64_t h = 1469598103934665603ull; /* FNV over the output array */
  for (long i = 0; i < n; i++){ h ^= a[i]; h *= 1099511628211ull; }
  printf("%llu\\n", (unsigned long long)h);
  return 0;
}
"""

NS = [0,1,2,3,7,8,9,15,16,17,31,32,33,63,64,65,100,127,128,129,255,256,1000,4095,4096,4097]
PATS = [0,1,2,3,4,5]
def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

def main():
    tcg = sys.argv[1]
    wd = tempfile.mkdtemp(prefix="i64widefuzz_")
    total = ok = mism = 0
    fails = []
    for name, (tir_text, cbody, expect_fire, opsub, is_map) in KERNELS.items():
        init = INITS.get(name, "0")
        t = os.path.join(wd, name + ".trust_ir"); open(t, "w").write(tir_text)
        c = os.path.join(wd, name + ".c")
        open(c, "w").write((CMAP_TMPL if is_map else CRED_TMPL).format(init=init, body=cbody))
        d = os.path.join(wd, name + "_drv.c")
        open(d, "w").write(DRIVER_MAP if is_map else DRIVER_RED)
        # patch trust_ir init constant for min/max/prod identities
        if name in INITS:
            txt = open(t).read()
            iv = {"smin": "9223372036854775807", "smax": "-9223372036854775808",
                  "umin": "-1", "prod": "1"}[name]
            which = {"smin": "%5", "smax": "%6", "umin": "%7", "prod": "%4x"}.get(name)
            # simpler: add a dedicated const line for the init reg used by RED_TMPL
            num = {"smin": "5", "smax": "6", "umin": "7", "prod": "4"}[name]
            if name == "prod":
                pass  # init=%4 (const 1) already exists
            else:
                txt = txt.replace("    %4 = const i64 1\n",
                                  "    %4 = const i64 1\n    %" + num + " = const i64 " + iv + "\n")
            open(t, "w").write(txt)
        on_o, off_o, cl_o = [os.path.join(wd, name + x) for x in ("_on.o", "_off.o", "_cl.o")]
        env = dict(os.environ)
        env["TRUST_CG_DUMP_NEONPREDSUM"] = "1"; env["TRUST_CG_DUMP_NEONMINMAX"] = "1"
        env["TRUST_CG_DUMP_NEONMAP"] = "1"; env["TRUST_CG_DUMP_NEONARRAY"] = "1"
        r = run([tcg, "--format=text", "--target", "aarch64", "-O2", "-c", t, "-o", on_o], env=env)
        if r.returncode != 0:
            print(f"{name}: COMPILE_ON failed\n{r.stderr}"); sys.exit(2)
        fired = any(x in r.stderr for x in ("neon-predsum", "neon-minmax", "neon-map", "neon-array"))
        dis = run(["otool", "-tvV", on_o]).stdout
        has_op = (any(t in dis for t in opsub) if isinstance(opsub, tuple) else opsub in dis) if opsub else True
        vec_ops = sum(dis.count(x) for x in (".2d", "cmeq", "cmgt", "cmhi", "st1", "stp", "ldp q"))
        if expect_fire:
            if not (fired and has_op):
                print(f"{name}: expected to FIRE with {opsub}; fired={fired} has_op={has_op}")
                sys.exit(2)
        else:
            if fired or ("mul.2d" in dis):
                print(f"{name}: expected BAIL but fired={fired} (mul.2d={'mul.2d' in dis})")
                sys.exit(2)
        envoff = dict(os.environ)
        envoff["TRUST_CG_DISABLE_PASSES"] = "neon_predsum,neon_minmax,neon_map,neon_array"
        assert run([tcg, "--format=text", "--target", "aarch64", "-O2", "-c", t, "-o", off_o], env=envoff).returncode == 0
        assert run(["cc", "-O2", "-c", c, "-o", cl_o]).returncode == 0
        on_b, off_b, cl_b = [os.path.join(wd, name + x) for x in ("_on", "_off", "_cl")]
        for (obj, binp) in ((on_o, on_b), (off_o, off_b), (cl_o, cl_b)):
            assert run(["cc", d, obj, "-o", binp]).returncode == 0
        k_ok = k_mism = 0
        for pat in PATS:
            for n in NS:
                total += 1
                von = run([on_b, str(n), str(pat)]).stdout.strip()
                voff = run([off_b, str(n), str(pat)]).stdout.strip()
                vcl = run([cl_b, str(n), str(pat)]).stdout.strip()
                if von == voff == vcl and von != "":
                    ok += 1; k_ok += 1
                else:
                    mism += 1; k_mism += 1
                    fails.append((name, f"pat={pat} n={n}", f"on={von} off={voff} clang={vcl}"))
        state = "FIRED" if expect_fire else "BAILED(correct)"
        print(f"{name}: {state} ok={k_ok} mismatch={k_mism}")
    print(f"\n=== i64 .2D differential: {total} runs, OK={ok} MISMATCH={mism} ===")
    if fails:
        for f in fails[:20]:
            print("FAIL:", f)
        sys.exit(1)
    print("ALL BIT-IDENTICAL (on == off == clang)")

if __name__ == "__main__":
    main()
