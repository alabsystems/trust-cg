// gen_x86_fp_rosetta_truth.c — THE ROSETTA SCALAR-FP (SSE/SSE2) x86 ORACLE HARNESS.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// What this is
// ===========================================================================
// The SCALAR-FP analog of gen_x86_rosetta_truth.c (scalar int) and
// gen_x86_packed_rosetta_truth.c (packed int). It executes each trust-cg scalar
// SSE/SSE2 floating-point op as ONE faithful instruction over an IEEE bit-pattern
// EDGE GRID and records the REAL x86 result, read back AS BIT PATTERNS. The
// "chip" here is Rosetta 2 — Apple's INDEPENDENT x86-64 binary translator —
// exercised by building this program with `clang -arch x86_64` and running it
// under `arch -x86_64`. Rosetta is a TRUE independent x86 implementation (NOT a
// second in-house model), so the facts it emits real-emulation-VALIDATE
// trust-cg's x86 scalar-FP SmtExpr encoders (x86_64_semantics.rs:
// encode_fp_add_rr/sub/mul/div/sqrt, encode_cvt*, encode_fp_minsd/maxsd,
// encode_fp_cmp_mask) and defeat root-cause #2 (both equivalence sides in-house)
// for x86 scalar-FP ops. These encoders evaluate (via smt.rs try_eval) through
// the SILICON-VALIDATED integer-only fp_bitmodel.rs (host FPU EVICTED for f32/f64
// arithmetic, #89/#91/#94), so this bridge cross-checks that integer-only model
// against an INDEPENDENT real x86 FP unit (Rosetta), at x86 SEMANTICS.
//
// ===========================================================================
// How each op is recorded (xmm bit readback — the load-bearing part)
// ===========================================================================
// Every operand is supplied as a RAW BIT PATTERN (u32 for f32, u64 for f64)
// transmuted to the float (movd/movq into xmm), so we exercise EXACT inputs:
// +-0, +-Inf, qNaN, sNaN, subnormals, min/max normal, rounding-tie values, etc.
// We execute the single SSE scalar instruction (the intrinsic / inline-asm the op
// name says, NOT a hand-coded model) and read the result BACK as bits (movd/movq
// from xmm for FP results; the GPR for f->int conversions). Comparing exact bit
// patterns (not float values) is the only faithful comparison for FP — it pins
// signed zeros, NaN payloads, and every rounding boundary.
//
// FP arithmetic NEVER traps (div-by-0 gives +-Inf; invalid gives a qNaN), so no
// fork/SIGFPE machinery is needed — every fact is a VALUE fact. The non-trapping
// f->int conversions that are out-of-range give the x86 "integer indefinite"
// 0x80000000 / 0x8000000000000000 result, which we record verbatim.
//
// ===========================================================================
// Output
// ===========================================================================
// Emits x86_fp_rosetta_truth.json: a provenance `_header` (oracle, macOS +
// Rosetta version + date passed in by the regen script, exact accounting) plus a
// `facts` array of {op, theorem id, kind, in_widths, operands (input bit patterns
// as decimal u64), imm (cmp predicate; cmp ops only), result (hex bits),
// result_kind, result_width}. Consumed by tests/bdefs_differential_bridge_x86_fp.rs.
//
// ===========================================================================
// Build + run (done by gen_x86_fp_rosetta_truth.sh)
// ===========================================================================
//   clang -arch x86_64 -O0 -msse4.2 -o BIN gen_x86_fp_rosetta_truth.c
//   arch -x86_64 ./BIN "<macos_ver>" "<rosetta_ver>" "<date>" > out.json

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <xmmintrin.h>  // SSE  (ss)
#include <emmintrin.h>  // SSE2 (sd, conversions)

// ---------------------------------------------------------------------------
// Bit<->float transmute helpers (no host arithmetic; pure reinterpretation).
// ---------------------------------------------------------------------------
static float    b2f(uint32_t b){ float f;  memcpy(&f,&b,4); return f; }
static double   b2d(uint64_t b){ double d; memcpy(&d,&b,8); return d; }
static uint32_t f2b(float f)   { uint32_t b; memcpy(&b,&f,4); return b; }
static uint64_t d2b(double d)  { uint64_t b; memcpy(&b,&d,8); return b; }

// ---------------------------------------------------------------------------
// Single-instruction scalar-FP primitives. Each is exactly ONE SSE/SSE2 scalar
// instruction; names mirror the trust-cg encoder family they validate. We use
// inline asm with explicit xmm operands so the compiler cannot constant-fold the
// FP op at -O0 and so the EXACT instruction (addss/.../cvttsd2si) is emitted.
// ---------------------------------------------------------------------------

// ADDSS/ADDSD/SUBSS/SUBSD/MULSS/MULSD/DIVSS/DIVSD/SQRTSS/SQRTSD/MINSS/MINSD/
// MAXSS/MAXSD — binary/unary scalar FP arithmetic on the low lane.
#define BIN_SS(NAME,INSN) \
  static uint32_t NAME(uint32_t a,uint32_t b){ float x=b2f(a),y=b2f(b); \
    __asm__ volatile(INSN " %2,%0":"=x"(x):"0"(x),"x"(y)); return f2b(x); }
#define BIN_SD(NAME,INSN) \
  static uint64_t NAME(uint64_t a,uint64_t b){ double x=b2d(a),y=b2d(b); \
    __asm__ volatile(INSN " %2,%0":"=x"(x):"0"(x),"x"(y)); return d2b(x); }
#define UN_SS(NAME,INSN) \
  static uint32_t NAME(uint32_t a){ float x=b2f(a),r; \
    __asm__ volatile(INSN " %1,%0":"=x"(r):"x"(x)); return f2b(r); }
#define UN_SD(NAME,INSN) \
  static uint64_t NAME(uint64_t a){ double x=b2d(a),r; \
    __asm__ volatile(INSN " %1,%0":"=x"(r):"x"(x)); return d2b(r); }

BIN_SS(x_addss,"addss") BIN_SD(x_addsd,"addsd")
BIN_SS(x_subss,"subss") BIN_SD(x_subsd,"subsd")
BIN_SS(x_mulss,"mulss") BIN_SD(x_mulsd,"mulsd")
BIN_SS(x_divss,"divss") BIN_SD(x_divsd,"divsd")
UN_SS (x_sqrtss,"sqrtss") UN_SD(x_sqrtsd,"sqrtsd")
// MINSS/MINSD/MAXSS/MAXSD: x86-QUIRKY — the SECOND operand wins on unordered
// (NaN) OR equal (incl. +0/-0); result = dest only when (min: dest<src, max:
// dest>src). We record exact bits so the quirk is visible to the bridge.
BIN_SS(x_minss,"minss") BIN_SD(x_minsd,"minsd")
BIN_SS(x_maxss,"maxss") BIN_SD(x_maxsd,"maxsd")

// CVTSS2SD (single->double, widen) / CVTSD2SS (double->single, narrow RNE).
UN_SD(x_cvtss2sd_raw_unused,"sqrtsd") // placeholder to keep macro symmetry (unused)
static uint64_t x_cvtss2sd(uint32_t a){ float x=b2f(a); double r;
  __asm__ volatile("cvtss2sd %1,%0":"=x"(r):"x"(x)); return d2b(r); }
static uint32_t x_cvtsd2ss(uint64_t a){ double x=b2d(a); float r;
  __asm__ volatile("cvtsd2ss %1,%0":"=x"(r):"x"(x)); return f2b(r); }

// CVTSI2SS / CVTSI2SD — signed int (32 or 64) -> scalar single/double (RNE).
static uint32_t x_cvtsi2ss_32(int32_t a){ float r;
  __asm__ volatile("cvtsi2ss %1,%0":"=x"(r):"r"(a)); return f2b(r); }
static uint64_t x_cvtsi2sd_32(int32_t a){ double r;
  __asm__ volatile("cvtsi2sd %1,%0":"=x"(r):"r"(a)); return d2b(r); }
static uint32_t x_cvtsi2ss_64(int64_t a){ float r;
  __asm__ volatile("cvtsi2ssq %1,%0":"=x"(r):"r"(a)); return f2b(r); }
static uint64_t x_cvtsi2sd_64(int64_t a){ double r;
  __asm__ volatile("cvtsi2sdq %1,%0":"=x"(r):"r"(a)); return d2b(r); }

// CVTTSS2SI / CVTTSD2SI — TRUNCATING (RTZ) float -> signed int (32 or 64).
static int32_t x_cvttss2si_32(uint32_t a){ float x=b2f(a); int32_t r;
  __asm__ volatile("cvttss2si %1,%0":"=r"(r):"x"(x)); return r; }
static int64_t x_cvttss2si_64(uint32_t a){ float x=b2f(a); int64_t r;
  __asm__ volatile("cvttss2siq %1,%0":"=r"(r):"x"(x)); return r; }
static int32_t x_cvttsd2si_32(uint64_t a){ double x=b2d(a); int32_t r;
  __asm__ volatile("cvttsd2si %1,%0":"=r"(r):"x"(x)); return r; }
static int64_t x_cvttsd2si_64(uint64_t a){ double x=b2d(a); int64_t r;
  __asm__ volatile("cvttsd2siq %1,%0":"=r"(r):"x"(x)); return r; }

// CVTSS2SI / CVTSD2SI — NON-truncating (MXCSR.RC = RNE default) float -> signed int.
static int32_t x_cvtss2si_32(uint32_t a){ float x=b2f(a); int32_t r;
  __asm__ volatile("cvtss2si %1,%0":"=r"(r):"x"(x)); return r; }
static int64_t x_cvtss2si_64(uint32_t a){ float x=b2f(a); int64_t r;
  __asm__ volatile("cvtss2siq %1,%0":"=r"(r):"x"(x)); return r; }
static int32_t x_cvtsd2si_32(uint64_t a){ double x=b2d(a); int32_t r;
  __asm__ volatile("cvtsd2si %1,%0":"=r"(r):"x"(x)); return r; }
static int64_t x_cvtsd2si_64(uint64_t a){ double x=b2d(a); int64_t r;
  __asm__ volatile("cvtsd2siq %1,%0":"=r"(r):"x"(x)); return r; }

// CMPSS / CMPSD with a literal imm8 predicate -> all-ones/all-zero lane mask.
// We expand each of the 8 basic predicates as its own single-instruction fn (the
// imm8 must be a literal in the encoding). The result mask is read back as bits.
#define CMP_SS(NAME,IMM) \
  static uint32_t NAME(uint32_t a,uint32_t b){ float x=b2f(a),y=b2f(b); \
    __asm__ volatile("cmpss $" #IMM ",%2,%0":"=x"(x):"0"(x),"x"(y)); return f2b(x); }
#define CMP_SD(NAME,IMM) \
  static uint64_t NAME(uint64_t a,uint64_t b){ double x=b2d(a),y=b2d(b); \
    __asm__ volatile("cmpsd $" #IMM ",%2,%0":"=x"(x):"0"(x),"x"(y)); return d2b(x); }
CMP_SS(x_cmpss_0,0) CMP_SS(x_cmpss_1,1) CMP_SS(x_cmpss_2,2) CMP_SS(x_cmpss_3,3)
CMP_SS(x_cmpss_4,4) CMP_SS(x_cmpss_5,5) CMP_SS(x_cmpss_6,6) CMP_SS(x_cmpss_7,7)
CMP_SD(x_cmpsd_0,0) CMP_SD(x_cmpsd_1,1) CMP_SD(x_cmpsd_2,2) CMP_SD(x_cmpsd_3,3)
CMP_SD(x_cmpsd_4,4) CMP_SD(x_cmpsd_5,5) CMP_SD(x_cmpsd_6,6) CMP_SD(x_cmpsd_7,7)

// ---------------------------------------------------------------------------
// Bit-pattern EDGE GRIDS. f32 (u32) and f64 (u64), covering the IEEE special
// classes + rounding-tie values + min/max normal/subnormal.
// ---------------------------------------------------------------------------
static const uint32_t F32G[] = {
  0x00000000u, // +0
  0x80000000u, // -0
  0x3f800000u, // +1.0
  0xbf800000u, // -1.0
  0x40000000u, // +2.0
  0x40400000u, // +3.0
  0x7f800000u, // +Inf
  0xff800000u, // -Inf
  0x7fc00000u, // qNaN
  0x7fa00000u, // sNaN
  0xffc00000u, // -qNaN
  0x00000001u, // smallest positive subnormal
  0x007fffffu, // largest subnormal
  0x00800000u, // smallest positive normal
  0x7f7fffffu, // largest normal (FLT_MAX)
  0xff7fffffu, // -FLT_MAX
  0x3fc00000u, // 1.5 (tie helper)
  0x3f000000u, // 0.5
  0x4b000000u, // 2^23 (integer boundary)
  0x4f000000u, // 2^31 (cvt overflow boundary for i32)
  0x5f000000u, // 2^63 (cvt overflow boundary for i64)
  0x3eaaaaabu, // 1/3 rounded
  0x40490fdbu, // pi
  0x42f60000u, // 123.0
};
static const uint64_t F64G[] = {
  0x0000000000000000ull, // +0
  0x8000000000000000ull, // -0
  0x3ff0000000000000ull, // +1.0
  0xbff0000000000000ull, // -1.0
  0x4000000000000000ull, // +2.0
  0x4008000000000000ull, // +3.0
  0x7ff0000000000000ull, // +Inf
  0xfff0000000000000ull, // -Inf
  0x7ff8000000000000ull, // qNaN
  0x7ff4000000000000ull, // sNaN
  0xfff8000000000000ull, // -qNaN
  0x0000000000000001ull, // smallest positive subnormal
  0x000fffffffffffffull, // largest subnormal
  0x0010000000000000ull, // smallest positive normal
  0x7fefffffffffffffull, // largest normal (DBL_MAX)
  0xffefffffffffffffull, // -DBL_MAX
  0x3ff8000000000000ull, // 1.5
  0x3fe0000000000000ull, // 0.5
  0x4330000000000000ull, // 2^52 (integer boundary)
  0x41e0000000000000ull, // 2^31
  0x43e0000000000000ull, // 2^63
  0x3fd5555555555555ull, // 1/3
  0x400921fb54442d18ull, // pi
  0x405ec00000000000ull, // 123.0
};
// Signed-integer source grid for CVTSI2* (32 + 64 bit).
static const int64_t IG[] = {
  0, 1, -1, 2, -2, 3, 100, -100, 1000000, -1000000,
  0x7fffffff, -2147483647-1 /* INT32_MIN */, 0x7fffffffffffffffll,
  (int64_t)0x8000000000000000ull /* INT64_MIN */, 16777217 /* 2^24+1 (f32 inexact) */,
  9007199254740993ll /* 2^53+1 (f64 inexact) */, 123456789, -987654321,
};

#define NF32 ((int)(sizeof(F32G)/sizeof(F32G[0])))
#define NF64 ((int)(sizeof(F64G)/sizeof(F64G[0])))
#define NIG  ((int)(sizeof(IG)/sizeof(IG[0])))

// ---------------------------------------------------------------------------
// JSON emission with exact accounting.
// ---------------------------------------------------------------------------
static long g_total_attempted = 0;
static long g_emitted = 0;
static int  g_first = 1;

// A scalar-FP VALUE fact. `kind` is "arith"/"cvt"/"minmax"/"cmp". in_widths and
// operands describe the input bit patterns; result is hex bits; result_kind is
// "bits"; result_width is the lane/int width. `imm` < 0 means "no imm field".
static void emit(const char *op, const char *kind, int in_w0, int in_w1,
                 const uint64_t *ops, int nops, int imm,
                 uint64_t result, int result_width){
  g_total_attempted++;
  if(!g_first) printf(",\n"); g_first=0;
  printf("  {\"op\":\"%s\",\"theorem\":\"rosetta_fp_%s_%ld\",\"kind\":\"%s\",\"in_widths\":[",
         op, op, g_emitted, kind);
  if(in_w1>0) printf("%d,%d", in_w0, in_w1); else printf("%d", in_w0);
  printf("],\"operands\":[");
  for(int i=0;i<nops;i++) printf("%s%llu", i?",":"", (unsigned long long)ops[i]);
  printf("]");
  if(imm>=0) printf(",\"imm\":%d", imm);
  printf(",\"result\":\"0x%llx\",\"result_kind\":\"bits\",\"result_width\":%d}",
         (unsigned long long)result, result_width);
  g_emitted++;
}

int main(int argc, char **argv){
  const char *macos_ver   = argc>1 ? argv[1] : "unknown";
  const char *rosetta_ver = argc>2 ? argv[2] : "unknown";
  const char *date        = argc>3 ? argv[3] : "unknown";

  printf("{\n");
  printf(" \"_header\": {\n");
  printf("  \"purpose\": \"x86-64 SCALAR-FP (SSE/SSE2) REAL-x86 ground truth for the B-x86-sse-fp differential bridge: each fact is a result produced by Rosetta 2 (Apple's independent x86-64 translator), an independent x86 implementation (NOT a second in-house model), validating trust-cg's x86 scalar-FP SmtExpr encoders (which evaluate through the silicon-validated integer-only fp_bitmodel). Operands and results are EXACT BIT PATTERNS so signed zeros, NaN payloads, subnormals and rounding boundaries are pinned.\",\n");
  printf("  \"oracle\": \"rosetta2\",\n");
  printf("  \"oracle_note\": \"Rosetta 2 binary translation on Apple silicon; one notch below bare silicon. Reproduces IEEE-754 scalar SSE FP incl. x86-QUIRKY MINSS/MAXSS (second operand on unordered/equal) and the 8 CMPSS/CMPSD predicate masks. FP arithmetic does not trap (div0 -> +-Inf, invalid -> qNaN).\",\n");
  printf("  \"macos_version\": \"%s\",\n", macos_ver);
  printf("  \"rosetta_version\": \"%s\",\n", rosetta_ver);
  printf("  \"recorded_on\": \"%s\",\n", date);
  printf("  \"build\": \"clang -arch x86_64 -msse4.2 gen_x86_fp_rosetta_truth.c; run via arch -x86_64\",\n");
  printf("  \"regen\": \"crates/trust-cg-verify/tests/fixtures/gen_x86_fp_rosetta_truth.sh\",\n");
  printf("  \"inclusion_policy\": \"scalar SSE/SSE2 FP ops with an in-house encoder in x86_64_semantics.rs: addss/sd, subss/sd, mulss/sd, divss/sd, sqrtss/sd; cvtss2sd, cvtsd2ss; cvtsi2ss/sd (i32,i64); cvttss2si/cvttsd2si (RTZ, i32+i64); cvtss2si/cvtsd2si (RNE, i32+i64); minss/sd, maxss/sd (x86-quirky); cmpss/cmpsd over the 8 basic predicates (0..7). Sampled over an IEEE bit-pattern edge grid (+-0, +-Inf, qNaN, sNaN, subnormals, min/max normal, ties). Packed-FP is out of scope (separate frontier).\",\n");
  printf("  \"operands_encoding\": \"each operand is an INPUT BIT PATTERN (f32 -> low 32 bits, f64 -> 64 bits; int source for cvtsi2* -> the two's-complement value as u64) as an unsigned decimal u64; result is hex (0x..) BIT PATTERN (FP result bits, or the signed-int result for f->int). cmp ops carry the imm8 predicate.\"\n");
  printf(" },\n");
  printf(" \"facts\": [\n");

  uint64_t ops[2];

  // ===================== binary arithmetic (SS + SD) =====================
  for(int i=0;i<NF32;i++) for(int j=0;j<NF32;j++){
    uint32_t a=F32G[i], b=F32G[j]; ops[0]=a; ops[1]=b;
    emit("addss","arith",32,32,ops,2,-1, x_addss(a,b),32);
    emit("subss","arith",32,32,ops,2,-1, x_subss(a,b),32);
    emit("mulss","arith",32,32,ops,2,-1, x_mulss(a,b),32);
    emit("divss","arith",32,32,ops,2,-1, x_divss(a,b),32);
    emit("minss","minmax",32,32,ops,2,-1, x_minss(a,b),32);
    emit("maxss","minmax",32,32,ops,2,-1, x_maxss(a,b),32);
  }
  for(int i=0;i<NF64;i++) for(int j=0;j<NF64;j++){
    uint64_t a=F64G[i], b=F64G[j]; ops[0]=a; ops[1]=b;
    emit("addsd","arith",64,64,ops,2,-1, x_addsd(a,b),64);
    emit("subsd","arith",64,64,ops,2,-1, x_subsd(a,b),64);
    emit("mulsd","arith",64,64,ops,2,-1, x_mulsd(a,b),64);
    emit("divsd","arith",64,64,ops,2,-1, x_divsd(a,b),64);
    emit("minsd","minmax",64,64,ops,2,-1, x_minsd(a,b),64);
    emit("maxsd","minmax",64,64,ops,2,-1, x_maxsd(a,b),64);
  }

  // ===================== unary SQRT (SS + SD) =====================
  for(int i=0;i<NF32;i++){ uint32_t a=F32G[i]; ops[0]=a;
    emit("sqrtss","arith",32,0,ops,1,-1, x_sqrtss(a),32);
  }
  for(int i=0;i<NF64;i++){ uint64_t a=F64G[i]; ops[0]=a;
    emit("sqrtsd","arith",64,0,ops,1,-1, x_sqrtsd(a),64);
  }

  // ===================== f<->f conversions =====================
  for(int i=0;i<NF32;i++){ uint32_t a=F32G[i]; ops[0]=a;
    emit("cvtss2sd","cvt",32,0,ops,1,-1, x_cvtss2sd(a),64);
  }
  for(int i=0;i<NF64;i++){ uint64_t a=F64G[i]; ops[0]=a;
    emit("cvtsd2ss","cvt",64,0,ops,1,-1, x_cvtsd2ss(a),32);
  }

  // ===================== int -> f conversions (i32, i64) =====================
  for(int i=0;i<NIG;i++){
    int64_t v=IG[i];
    // i32 source: take the low 32 bits as the signed i32.
    int32_t v32=(int32_t)v; ops[0]=(uint32_t)v32;
    emit("cvtsi2ss_32","cvt",32,0,ops,1,-1, x_cvtsi2ss_32(v32),32);
    emit("cvtsi2sd_32","cvt",32,0,ops,1,-1, x_cvtsi2sd_32(v32),64);
    // i64 source.
    ops[0]=(uint64_t)v;
    emit("cvtsi2ss_64","cvt",64,0,ops,1,-1, x_cvtsi2ss_64(v),32);
    emit("cvtsi2sd_64","cvt",64,0,ops,1,-1, x_cvtsi2sd_64(v),64);
  }

  // ===================== f -> int conversions (trunc RTZ + RNE) =====================
  for(int i=0;i<NF32;i++){ uint32_t a=F32G[i]; ops[0]=a;
    emit("cvttss2si_32","cvt",32,0,ops,1,-1, (uint32_t)x_cvttss2si_32(a),32);
    emit("cvttss2si_64","cvt",32,0,ops,1,-1, (uint64_t)x_cvttss2si_64(a),64);
    emit("cvtss2si_32", "cvt",32,0,ops,1,-1, (uint32_t)x_cvtss2si_32(a),32);
    emit("cvtss2si_64", "cvt",32,0,ops,1,-1, (uint64_t)x_cvtss2si_64(a),64);
  }
  for(int i=0;i<NF64;i++){ uint64_t a=F64G[i]; ops[0]=a;
    emit("cvttsd2si_32","cvt",64,0,ops,1,-1, (uint32_t)x_cvttsd2si_32(a),32);
    emit("cvttsd2si_64","cvt",64,0,ops,1,-1, (uint64_t)x_cvttsd2si_64(a),64);
    emit("cvtsd2si_32", "cvt",64,0,ops,1,-1, (uint32_t)x_cvtsd2si_32(a),32);
    emit("cvtsd2si_64", "cvt",64,0,ops,1,-1, (uint64_t)x_cvtsd2si_64(a),64);
  }

  // ===================== CMPSS / CMPSD (8 predicates) =====================
  // dispatch tables by predicate so each is its literal-imm single instruction.
  uint32_t (*cmpss[8])(uint32_t,uint32_t) = {
    x_cmpss_0,x_cmpss_1,x_cmpss_2,x_cmpss_3,x_cmpss_4,x_cmpss_5,x_cmpss_6,x_cmpss_7 };
  uint64_t (*cmpsd[8])(uint64_t,uint64_t) = {
    x_cmpsd_0,x_cmpsd_1,x_cmpsd_2,x_cmpsd_3,x_cmpsd_4,x_cmpsd_5,x_cmpsd_6,x_cmpsd_7 };
  for(int p=0;p<8;p++){
    for(int i=0;i<NF32;i++) for(int j=0;j<NF32;j++){
      uint32_t a=F32G[i], b=F32G[j]; ops[0]=a; ops[1]=b;
      emit("cmpss","cmp",32,32,ops,2,p, cmpss[p](a,b),32);
    }
    for(int i=0;i<NF64;i++) for(int j=0;j<NF64;j++){
      uint64_t a=F64G[i], b=F64G[j]; ops[0]=a; ops[1]=b;
      emit("cmpsd","cmp",64,64,ops,2,p, cmpsd[p](a,b),64);
    }
  }

  printf("\n ],\n");
  printf(" \"_accounting\": {\n");
  printf("  \"total_attempted\": %ld,\n", g_total_attempted);
  printf("  \"emitted\": %ld,\n", g_emitted);
  printf("  \"value_facts\": %ld,\n", g_emitted);
  printf("  \"trap_facts\": 0,\n");
  printf("  \"sampled_grid\": {\"f32\":%d,\"f64\":%d,\"int\":%d,\"cmp_predicates\":8}\n", NF32, NF64, NIG);
  printf(" }\n");
  printf("}\n");

  if(g_total_attempted != g_emitted){
    fprintf(stderr,"ACCOUNTING ERROR: attempted %ld != emitted %ld\n", g_total_attempted, g_emitted);
    return 4;
  }
  fprintf(stderr,"emitted %ld FP facts (all value)\n", g_emitted);
  (void)x_cvtss2sd_raw_unused; // silence unused (kept for macro symmetry)
  return 0;
}
