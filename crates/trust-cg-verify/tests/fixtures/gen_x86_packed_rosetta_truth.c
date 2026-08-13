// gen_x86_packed_rosetta_truth.c — THE ROSETTA PACKED-SSE2 x86 ORACLE HARNESS.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// What this is
// ===========================================================================
// The PACKED-SSE2-integer analog of gen_x86_rosetta_truth.c (the scalar x86
// Rosetta oracle). It executes each trust-cg packed-SSE2 integer op as ONE
// faithful SSE2/SSE4 instruction over a 128-bit operand grid and records the
// REAL x86 result. The "chip" here is Rosetta 2 — Apple's INDEPENDENT x86-64
// binary translator — exercised by building this program with `clang -arch
// x86_64` and running it under `arch -x86_64`. Rosetta is a TRUE independent x86
// implementation (NOT a second in-house model), so the facts it emits
// real-emulation-VALIDATE trust-cg's packed-SSE2 SmtExpr encoders
// (x86_64_semantics.rs: encode_padd{b,w,d,q}, encode_psub{b,w,d,q},
// encode_pmulld/pmullw, encode_pand/pandn/por/pxor, encode_pcmpeq{b,w,d,q},
// encode_pcmpgt{b,w,d,q}, encode_pslld_imm/psrld_imm/psrad_imm) and defeat
// root-cause #2 (both equivalence sides in-house) for x86 PACKED-integer ops.
//
// ===========================================================================
// How each op is recorded (xmm readback, the load-bearing part)
// ===========================================================================
// For each op we LOAD two xmm registers from 16-byte buffers via `movdqu`
// (_mm_loadu_si128), execute the single packed instruction (the intrinsic the
// op name says, NOT a hand-coded model), and STORE the 128-bit result back to a
// 16-byte buffer via `movdqu` (_mm_storeu_si128). The two 64-bit halves of each
// buffer are emitted as a_lo/a_hi/b_lo/b_hi and the result as result_lo/result_hi
// (plus a 128-bit "result" hex string), so the bridge can rebuild the exact
// 128-bit operands as SmtExpr Bv128 constant leaves. Packed-SSE2 integer ops do
// NOT trap, so every fact is a VALUE fact (no fork/SIGFPE machinery needed).
//
// The IMMEDIATE shifts (PSLLD/PSRLD/PSRAD) take a literal shift count baked into
// the instruction encoding; we sample a fixed set of counts (incl. counts > 31,
// where x86 saturates each dword lane to 0 / sign for PSRAD — NOT a mask, unlike
// the scalar SHL — exactly what encode_pslld_imm etc. model via the SMT clamp).
//
// ===========================================================================
// Output
// ===========================================================================
// Emits x86_packed_rosetta_truth.json: a provenance `_header` (oracle, macOS +
// Rosetta version + date passed in by the regen script, exact accounting) plus a
// `facts` array of {op, theorem id, lane_bits, a_lo/a_hi, b_lo/b_hi, imm (shifts
// only), result (128-bit hex) + result_lo/result_hi}. Consumed by
// tests/bdefs_differential_bridge_x86_packed.rs.
//
// ===========================================================================
// Build + run (done by gen_x86_packed_rosetta_truth.sh)
// ===========================================================================
//   clang -arch x86_64 -O0 -msse4.2 -o BIN gen_x86_packed_rosetta_truth.c
//   arch -x86_64 ./BIN "<macos_ver>" "<rosetta_ver>" "<date>" > out.json

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <emmintrin.h> // SSE2
#include <smmintrin.h> // SSE4.1 (pmulld, pcmpeqq)
#include <nmmintrin.h> // SSE4.2 (pcmpgtq)

// ---------------------------------------------------------------------------
// A 128-bit operand carried as two 64-bit halves (lo = bits 0..63, hi = 64..127).
// load128/store128 are the movdqu round-trip the harness uses for every op.
// ---------------------------------------------------------------------------
typedef struct { uint64_t lo, hi; } u128_t;

static __m128i load128(u128_t v) {
  uint64_t buf[2] = { v.lo, v.hi }; // little-endian: buf[0]=low qword
  return _mm_loadu_si128((const __m128i *)buf); // movdqu
}
static u128_t store128(__m128i x) {
  uint64_t buf[2];
  _mm_storeu_si128((__m128i *)buf, x); // movdqu
  u128_t r; r.lo = buf[0]; r.hi = buf[1]; return r;
}

// ---------------------------------------------------------------------------
// The 128-bit operand grid: edge lane patterns per width, packed into 128 bits.
// Each entry is the SAME bit pattern broadcast/packed so every lane sees an edge
// value (0, -1, INT_MIN/MAX per width, alternating), plus a couple of random-ish
// 128-bit values so cross-lane mistakes (wrong lane width) surface.
// ---------------------------------------------------------------------------
static const u128_t GRID[] = {
  // all zero / all ones
  { 0x0000000000000000ULL, 0x0000000000000000ULL },
  { 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL },
  // byte edges packed 16x: 0x80 (INT8_MIN), 0x7F (INT8_MAX), 0x01
  { 0x8080808080808080ULL, 0x8080808080808080ULL },
  { 0x7F7F7F7F7F7F7F7FULL, 0x7F7F7F7F7F7F7F7FULL },
  { 0x0101010101010101ULL, 0x0101010101010101ULL },
  // word edges packed 8x: 0x8000 (INT16_MIN), 0x7FFF (INT16_MAX), 0x0001
  { 0x8000800080008000ULL, 0x8000800080008000ULL },
  { 0x7FFF7FFF7FFF7FFFULL, 0x7FFF7FFF7FFF7FFFULL },
  { 0x0001000100010001ULL, 0x0001000100010001ULL },
  // dword edges packed 4x: 0x80000000 (INT32_MIN), 0x7FFFFFFF (INT32_MAX), 1
  { 0x8000000080000000ULL, 0x8000000080000000ULL },
  { 0x7FFFFFFF7FFFFFFFULL, 0x7FFFFFFF7FFFFFFFULL },
  { 0x0000000100000001ULL, 0x0000000100000001ULL },
  // qword edges packed 2x: 0x8000000000000000 (INT64_MIN), INT64_MAX, 1
  { 0x8000000000000000ULL, 0x8000000000000000ULL },
  { 0x7FFFFFFFFFFFFFFFULL, 0x7FFFFFFFFFFFFFFFULL },
  { 0x0000000000000001ULL, 0x0000000000000001ULL },
  // alternating bit patterns (cross-lane carry probes)
  { 0xAAAAAAAAAAAAAAAAULL, 0x5555555555555555ULL },
  { 0x5555555555555555ULL, 0xAAAAAAAAAAAAAAAAULL },
  { 0x0102040810204080ULL, 0x8040201008040201ULL },
  // "random" 128-bit values (deterministic literals; cross-lane mistakes show)
  { 0xDEADBEEFCAFEBABEULL, 0x0123456789ABCDEFULL },
  { 0xFEDCBA9876543210ULL, 0x13579BDF2468ACE0ULL },
  { 0x00000001FFFFFFFFULL, 0xFFFFFFFF00000001ULL },
  { 0xFFFF0000FFFF0000ULL, 0x0000FFFF0000FFFFULL },
};
#define NGRID ((int)(sizeof(GRID)/sizeof(GRID[0])))

// Immediate shift counts: in-range and out-of-range (x86 packed imm-shift
// SATURATES to 0 / sign at count >= lane width — NOT a mask). 0,1,7,15,16,31 are
// in range for dwords; 32,33,40,63,64,255 are out of range (-> 0 / sign).
static const uint8_t SHIFTC[] = { 0, 1, 7, 8, 15, 16, 31, 32, 33, 40, 63, 64, 255 };
#define NSC ((int)(sizeof(SHIFTC)/sizeof(SHIFTC[0])))

// ---------------------------------------------------------------------------
// JSON emission with exact accounting.
// ---------------------------------------------------------------------------
static long g_total_attempted = 0; // facts the grid asked for
static long g_emitted = 0;         // facts actually written
static int  g_first = 1;           // comma control

// Binary packed op (two 128-bit inputs, one 128-bit output). lane_bits is the
// SDM lane width of the op (8/16/32/64); imm is -1 (none).
static void emit_bin(const char *op, int lane_bits, u128_t a, u128_t b, u128_t r) {
  g_total_attempted++;
  if (!g_first) printf(",\n"); g_first = 0;
  printf("  {\"op\":\"%s\",\"theorem\":\"rosetta_packed_%s_%ld\",\"lane_bits\":%d,"
         "\"a_lo\":\"0x%016llx\",\"a_hi\":\"0x%016llx\","
         "\"b_lo\":\"0x%016llx\",\"b_hi\":\"0x%016llx\","
         "\"result_lo\":\"0x%016llx\",\"result_hi\":\"0x%016llx\","
         "\"result\":\"0x%016llx%016llx\"}",
         op, op, g_emitted, lane_bits,
         (unsigned long long)a.lo, (unsigned long long)a.hi,
         (unsigned long long)b.lo, (unsigned long long)b.hi,
         (unsigned long long)r.lo, (unsigned long long)r.hi,
         (unsigned long long)r.hi, (unsigned long long)r.lo);
  g_emitted++;
}

// Immediate-shift packed op (one 128-bit input, one literal count, one output).
static void emit_imm(const char *op, int lane_bits, u128_t a, int imm, u128_t r) {
  g_total_attempted++;
  if (!g_first) printf(",\n"); g_first = 0;
  printf("  {\"op\":\"%s\",\"theorem\":\"rosetta_packed_%s_%ld\",\"lane_bits\":%d,"
         "\"a_lo\":\"0x%016llx\",\"a_hi\":\"0x%016llx\",\"imm\":%d,"
         "\"result_lo\":\"0x%016llx\",\"result_hi\":\"0x%016llx\","
         "\"result\":\"0x%016llx%016llx\"}",
         op, op, g_emitted, lane_bits,
         (unsigned long long)a.lo, (unsigned long long)a.hi, imm,
         (unsigned long long)r.lo, (unsigned long long)r.hi,
         (unsigned long long)r.hi, (unsigned long long)r.lo);
  g_emitted++;
}

// Run one binary op: load both operands, run intrinsic, store, emit.
#define RUN_BIN(NAME, LANE, INTRIN) \
  do { u128_t r = store128(INTRIN(load128(a), load128(b))); emit_bin(NAME, LANE, a, b, r); } while (0)

// Run one immediate-shift op. The intrinsic needs a COMPILE-TIME-CONSTANT count
// argument, so we dispatch via a switch over the sampled SHIFTC values.
#define RUN_IMM_SHIFT(NAME, INTRIN_PREFIX) \
  do { \
    __m128i x = load128(a); __m128i y; \
    switch (c) { \
      case 0:  y = INTRIN_PREFIX(x, 0);  break; \
      case 1:  y = INTRIN_PREFIX(x, 1);  break; \
      case 7:  y = INTRIN_PREFIX(x, 7);  break; \
      case 8:  y = INTRIN_PREFIX(x, 8);  break; \
      case 15: y = INTRIN_PREFIX(x, 15); break; \
      case 16: y = INTRIN_PREFIX(x, 16); break; \
      case 31: y = INTRIN_PREFIX(x, 31); break; \
      case 32: y = INTRIN_PREFIX(x, 32); break; \
      case 33: y = INTRIN_PREFIX(x, 33); break; \
      case 40: y = INTRIN_PREFIX(x, 40); break; \
      case 63: y = INTRIN_PREFIX(x, 63); break; \
      case 64: y = INTRIN_PREFIX(x, 64); break; \
      default: y = INTRIN_PREFIX(x, 255); break; \
    } \
    u128_t r = store128(y); emit_imm(NAME, 32, a, (int)c, r); \
  } while (0)

int main(int argc, char **argv) {
  const char *macos_ver   = argc > 1 ? argv[1] : "unknown";
  const char *rosetta_ver = argc > 2 ? argv[2] : "unknown";
  const char *date        = argc > 3 ? argv[3] : "unknown";

  printf("{\n");
  printf(" \"_header\": {\n");
  printf("  \"purpose\": \"x86-64 PACKED-SSE2 integer REAL-x86 ground truth for the B-x86-sse-packed differential bridge: each fact is a 128-bit result produced by Rosetta 2 (Apple's independent x86-64 translator), an independent x86 implementation (NOT a second in-house model), validating trust-cg's packed-SSE2 SmtExpr encoders.\",\n");
  printf("  \"oracle\": \"rosetta2\",\n");
  printf("  \"oracle_note\": \"Rosetta 2 binary translation on Apple silicon; one notch below bare silicon. Reproduces x86 packed-SSE2/SSE4 integer semantics: lane-wise wrap-around add/sub/mul, all-ones/all-zero compare masks, and packed imm-shift SATURATION (count >= lane width -> 0 for PSLLD/PSRLD, sign for PSRAD — NOT a count mask, unlike the scalar SHL).\",\n");
  printf("  \"macos_version\": \"%s\",\n", macos_ver);
  printf("  \"rosetta_version\": \"%s\",\n", rosetta_ver);
  printf("  \"recorded_on\": \"%s\",\n", date);
  printf("  \"build\": \"clang -arch x86_64 -msse4.2 gen_x86_packed_rosetta_truth.c; run via arch -x86_64\",\n");
  printf("  \"readback\": \"each op LOADs two xmm regs from 16-byte buffers (movdqu), runs ONE packed SSE2/SSE4 instruction, and STOREs the 128-bit result (movdqu); operands+result are emitted as lo/hi qwords and a 128-bit hex string.\",\n");
  printf("  \"regen\": \"crates/trust-cg-verify/tests/fixtures/gen_x86_packed_rosetta_truth.sh\",\n");
  printf("  \"inclusion_policy\": \"packed-SSE2 integer ops with an in-house encoder in x86_64_semantics.rs (padd{b,w,d,q}, psub{b,w,d,q}, pmulld, pmullw, pand, pandn, por, pxor, pcmpeq{b,w,d,q}, pcmpgt{b,w,d,q}, pslld/psrld/psrad imm-shift), sampled over an edge-case 128-bit lane grid (0, -1, INT_MIN/MAX per lane width, alternating, random) packed into 128 bits; imm-shifts sample fixed counts incl. counts >= lane width to exercise the saturation contract. Packed-int ops do not trap -> all VALUE facts.\",\n");
  printf("  \"operands_encoding\": \"each 128-bit operand is two 64-bit hex halves (a_lo = bits 0..63, a_hi = bits 64..127); result is a 128-bit hex string plus result_lo/result_hi.\"\n");
  printf(" },\n");
  printf(" \"facts\": [\n");

  // ===================== binary lane-wise ops (a op b) =====================
  for (int i = 0; i < NGRID; i++) {
    for (int j = 0; j < NGRID; j++) {
      u128_t a = GRID[i], b = GRID[j];
      // packed ADD (byte/word/dword/qword)
      RUN_BIN("paddb",  8,  _mm_add_epi8);
      RUN_BIN("paddw",  16, _mm_add_epi16);
      RUN_BIN("paddd",  32, _mm_add_epi32);
      RUN_BIN("paddq",  64, _mm_add_epi64);
      // packed SUB
      RUN_BIN("psubb",  8,  _mm_sub_epi8);
      RUN_BIN("psubw",  16, _mm_sub_epi16);
      RUN_BIN("psubd",  32, _mm_sub_epi32);
      RUN_BIN("psubq",  64, _mm_sub_epi64);
      // packed low-multiply
      RUN_BIN("pmulld", 32, _mm_mullo_epi32); // SSE4.1
      RUN_BIN("pmullw", 16, _mm_mullo_epi16); // SSE2
      // packed bitwise (whole-128-bit, lane_bits=128 marker)
      RUN_BIN("pand",   128, _mm_and_si128);
      RUN_BIN("pandn",  128, _mm_andnot_si128); // andnot(a,b) = (~a) & b
      RUN_BIN("por",    128, _mm_or_si128);
      RUN_BIN("pxor",   128, _mm_xor_si128);
      // packed equality compare (all-ones / all-zero lane masks)
      RUN_BIN("pcmpeqb", 8,  _mm_cmpeq_epi8);
      RUN_BIN("pcmpeqw", 16, _mm_cmpeq_epi16);
      RUN_BIN("pcmpeqd", 32, _mm_cmpeq_epi32);
      RUN_BIN("pcmpeqq", 64, _mm_cmpeq_epi64); // SSE4.1
      // packed signed greater-than compare
      RUN_BIN("pcmpgtb", 8,  _mm_cmpgt_epi8);
      RUN_BIN("pcmpgtw", 16, _mm_cmpgt_epi16);
      RUN_BIN("pcmpgtd", 32, _mm_cmpgt_epi32);
      RUN_BIN("pcmpgtq", 64, _mm_cmpgt_epi64); // SSE4.2
    }
  }

  // ===================== immediate dword shifts (a >> imm) =====================
  for (int i = 0; i < NGRID; i++) {
    for (int k = 0; k < NSC; k++) {
      u128_t a = GRID[i]; uint8_t c = SHIFTC[k];
      RUN_IMM_SHIFT("pslld", _mm_slli_epi32);
      RUN_IMM_SHIFT("psrld", _mm_srli_epi32);
      RUN_IMM_SHIFT("psrad", _mm_srai_epi32);
    }
  }

  printf("\n ],\n");
  printf(" \"_accounting\": {\n");
  printf("  \"total_attempted\": %ld,\n", g_total_attempted);
  printf("  \"emitted\": %ld,\n", g_emitted);
  printf("  \"value_facts\": %ld,\n", g_emitted);
  printf("  \"trap_facts\": 0,\n");
  printf("  \"sampled_grid\": {\"grid\":%d,\"shift_counts\":%d}\n", NGRID, NSC);
  printf(" }\n");
  printf("}\n");

  if (g_total_attempted != g_emitted) {
    fprintf(stderr, "ACCOUNTING ERROR: attempted %ld != emitted %ld\n", g_total_attempted, g_emitted);
    return 4;
  }
  fprintf(stderr, "emitted %ld packed facts (all value)\n", g_emitted);
  return 0;
}
