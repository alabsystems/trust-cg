// gen_aarch64_nzcv_silicon_truth.c — NATIVE AArch64 NZCV producer/consumer
// ground-truth harness (L04-P8).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// What this is
// ===========================================================================
// The integer silicon fixture (aarch64_silicon_truth.json) holds value results
// only: its Clean chip grid logs every NZCV flag definition as excluded. This
// harness records the flag results themselves, natively, on the Apple silicon
// it runs on. Each fact executes ONE architectural instruction inside a single
// inline-asm block that
//
//   1. writes a chosen incoming NZCV with `MSR NZCV, Xt`,
//   2. executes the instruction under test on register operands, and
//   3. reads the resulting NZCV back with `MRS Xt, NZCV`,
//
// so no compiler-generated code sits between the flag producer and the read.
// Covered instruction forms, each at W (32-bit) and X (64-bit) width:
//
//   producers : ADDS, SUBS, CMP (register and #imm12), ADCS, SBCS, TST
//               (register and logical #imm)
//   carry use : ADC, SBC (value only; NZCV must be preserved), for carry-in
//               0 and 1, as ADCS/SBCS are
//   consumers : CSEL, CSINC, CSINV, CSNEG for all 16 conditions and all 16
//               incoming NZCV values
//   FP        : FCMP Sn, Sm / FCMP Dn, Dm over an IEEE edge grid (zeros,
//               subnormals, normals, infinities, quiet and signaling NaNs)
//
// W-form operands are passed in full X registers whose upper halves are
// deliberately NONZERO, so a model that reads bits 63:32 of a W operand
// mismatches. Facts record the full 64-bit register values; the replay test
// (tests/aarch64_nzcv_silicon_bridge.rs) truncates as the architecture does.
//
// The facts are regression evidence for crate::nzcv and the conditional-select
// and FCMP models on ONE host CPU. They are not a proof, they do not sample
// every input, and they say nothing about other implementations.
//
// Build + run: gen_aarch64_nzcv_silicon_truth.sh (native arm64 only).

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#if !defined(__aarch64__)
#error "gen_aarch64_nzcv_silicon_truth.c must be compiled natively for AArch64"
#endif

// ---------------------------------------------------------------------------
// Operand grids
// ---------------------------------------------------------------------------

// Integer boundary grid. Every value is also used for W forms, whose upper
// halves are then replaced by a nonzero garbage pattern (see w_operand).
static const uint64_t G[] = {
  0x0ULL, 0x1ULL, 0x2ULL, 0x3ULL, 0x7fULL, 0x80ULL, 0xffULL, 0x100ULL,
  0x7fffULL, 0x8000ULL, 0xffffULL,
  0x7fffffffULL, 0x80000000ULL, 0x80000001ULL, 0xfffffffeULL, 0xffffffffULL,
  0x100000000ULL, 0x100000001ULL,
  0x7ffffffffffffffeULL, 0x7fffffffffffffffULL,
  0x8000000000000000ULL, 0x8000000000000001ULL,
  0xfffffffffffffffeULL, 0xffffffffffffffffULL,
  0x0123456789abcdefULL, 0xfedcba9876543210ULL,
  0x5555555555555555ULL, 0xaaaaaaaaaaaaaaaaULL,
  0xdeadbeef00000001ULL, 0x00000001ffffffffULL,
};
#define NG ((int)(sizeof(G) / sizeof(G[0])))

// W-form operand: the low 32 bits of the grid value under a nonzero upper
// half, so the architectural W read (bits 31:0 only) is observable.
static uint64_t w_operand(uint64_t v, int salt) {
  static const uint64_t HI[] = {0xa5a5a5a5ULL, 0xffffffffULL, 0x00000001ULL, 0x80000000ULL};
  return (HI[salt & 3] << 32) | (v & 0xffffffffULL);
}

// Select operand pairs (true arm, false arm): distinct values, extremes, and
// an increment/negation wrap for CSINC/CSNEG.
static const uint64_t SEL[][2] = {
  {0x0000000000000011ULL, 0x0000000000000022ULL},
  {0xffffffffffffffffULL, 0x0000000000000000ULL},
  {0x7fffffffffffffffULL, 0x8000000000000000ULL},
  {0xfedcba9876543210ULL, 0x00000000ffffffffULL},
};
#define NSEL ((int)(sizeof(SEL) / sizeof(SEL[0])))

// IEEE edge grids (raw bits).
static const uint32_t F32[] = {
  0x00000000u, 0x80000000u, 0x00000001u, 0x80000001u, 0x007fffffu, 0x807fffffu,
  0x00800000u, 0x80800000u, 0x3f800000u, 0xbf800000u, 0x3f800001u, 0x40000000u,
  0x7f7fffffu, 0xff7fffffu, 0x7f800000u, 0xff800000u,
  0x7fc00000u, 0xffc00000u, 0x7fc12345u, 0x7f812345u, 0xff812346u, 0x7fbfffffu,
};
#define NF32 ((int)(sizeof(F32) / sizeof(F32[0])))
static const uint64_t F64[] = {
  0x0000000000000000ULL, 0x8000000000000000ULL, 0x0000000000000001ULL,
  0x8000000000000001ULL, 0x000fffffffffffffULL, 0x800fffffffffffffULL,
  0x0010000000000000ULL, 0x8010000000000000ULL, 0x3ff0000000000000ULL,
  0xbff0000000000000ULL, 0x3ff0000000000001ULL, 0x4000000000000000ULL,
  0x7fefffffffffffffULL, 0xffefffffffffffffULL, 0x7ff0000000000000ULL,
  0xfff0000000000000ULL, 0x7ff8000000000000ULL, 0xfff8000000000000ULL,
  0x7ff8123456789abcULL, 0x7ff0123456789abcULL, 0xfff0123456789abdULL,
  0x7ff7ffffffffffffULL,
};
#define NF64 ((int)(sizeof(F64) / sizeof(F64[0])))

// ---------------------------------------------------------------------------
// Flag producers: msr nzcv; <insn>; mrs nzcv inside ONE asm block.
// ---------------------------------------------------------------------------

#define BIN_FLAGS_X(NAME, MNEMONIC)                                                 \
  static uint64_t NAME(uint64_t a, uint64_t b, uint64_t in, uint64_t *flags) {      \
    uint64_t r, f;                                                                  \
    __asm__ volatile("msr nzcv, %4\n\t" MNEMONIC " %0, %2, %3\n\tmrs %1, nzcv"      \
                     : "=&r"(r), "=&r"(f)                                           \
                     : "r"(a), "r"(b), "r"(in << 28)                                \
                     : "cc");                                                       \
    *flags = f >> 28;                                                               \
    return r;                                                                       \
  }
#define BIN_FLAGS_W(NAME, MNEMONIC)                                                 \
  static uint64_t NAME(uint64_t a, uint64_t b, uint64_t in, uint64_t *flags) {      \
    uint64_t r, f;                                                                  \
    __asm__ volatile("msr nzcv, %4\n\t" MNEMONIC " %w0, %w2, %w3\n\tmrs %1, nzcv"   \
                     : "=&r"(r), "=&r"(f)                                           \
                     : "r"(a), "r"(b), "r"(in << 28)                                \
                     : "cc");                                                       \
    *flags = f >> 28;                                                               \
    return r;                                                                       \
  }

BIN_FLAGS_X(adds_x, "adds")
BIN_FLAGS_W(adds_w, "adds")
BIN_FLAGS_X(subs_x, "subs")
BIN_FLAGS_W(subs_w, "subs")
BIN_FLAGS_X(adcs_x, "adcs")
BIN_FLAGS_W(adcs_w, "adcs")
BIN_FLAGS_X(sbcs_x, "sbcs")
BIN_FLAGS_W(sbcs_w, "sbcs")
BIN_FLAGS_X(adc_x, "adc")
BIN_FLAGS_W(adc_w, "adc")
BIN_FLAGS_X(sbc_x, "sbc")
BIN_FLAGS_W(sbc_w, "sbc")

#define CMP_FLAGS(NAME, MNEMONIC, REG)                                              \
  static uint64_t NAME(uint64_t a, uint64_t b, uint64_t in) {                       \
    uint64_t f;                                                                     \
    __asm__ volatile("msr nzcv, %3\n\t" MNEMONIC " %" REG "1, %" REG "2\n\t"        \
                     "mrs %0, nzcv"                                                 \
                     : "=&r"(f)                                                     \
                     : "r"(a), "r"(b), "r"(in << 28)                                \
                     : "cc");                                                       \
    return f >> 28;                                                                 \
  }
CMP_FLAGS(cmp_x, "cmp", "x")
CMP_FLAGS(cmp_w, "cmp", "w")
CMP_FLAGS(tst_x, "tst", "x")
CMP_FLAGS(tst_w, "tst", "w")

// Immediate forms: the immediate is an assembler literal, so a small fixed set.
#define CMP_IMM(NAME, MNEMONIC, REG, IMM)                                           \
  static uint64_t NAME(uint64_t a, uint64_t in) {                                   \
    uint64_t f;                                                                     \
    __asm__ volatile("msr nzcv, %2\n\t" MNEMONIC " %" REG "1, #" #IMM "\n\t"        \
                     "mrs %0, nzcv"                                                 \
                     : "=&r"(f)                                                     \
                     : "r"(a), "r"(in << 28)                                        \
                     : "cc");                                                       \
    return f >> 28;                                                                 \
  }
CMP_IMM(cmp_x_0, "cmp", "x", 0)
CMP_IMM(cmp_x_1, "cmp", "x", 1)
CMP_IMM(cmp_x_4095, "cmp", "x", 4095)
CMP_IMM(cmp_w_0, "cmp", "w", 0)
CMP_IMM(cmp_w_1, "cmp", "w", 1)
CMP_IMM(cmp_w_4095, "cmp", "w", 4095)
CMP_IMM(tst_x_1, "tst", "x", 0x1)
CMP_IMM(tst_x_ff, "tst", "x", 0xff)
CMP_IMM(tst_x_msb, "tst", "x", 0x8000000000000000)
CMP_IMM(tst_w_1, "tst", "w", 0x1)
CMP_IMM(tst_w_ff, "tst", "w", 0xff)
CMP_IMM(tst_w_msb, "tst", "w", 0x80000000)

typedef uint64_t (*cmp_imm_fn)(uint64_t, uint64_t);
struct imm_form {
  const char *op;
  int width;
  uint64_t imm;
  cmp_imm_fn fn;
};
static const struct imm_form IMM_FORMS[] = {
  {"cmp_imm", 64, 0, cmp_x_0},       {"cmp_imm", 64, 1, cmp_x_1},
  {"cmp_imm", 64, 4095, cmp_x_4095}, {"cmp_imm", 32, 0, cmp_w_0},
  {"cmp_imm", 32, 1, cmp_w_1},       {"cmp_imm", 32, 4095, cmp_w_4095},
  {"tst_imm", 64, 0x1, tst_x_1},     {"tst_imm", 64, 0xff, tst_x_ff},
  {"tst_imm", 64, 0x8000000000000000ULL, tst_x_msb},
  {"tst_imm", 32, 0x1, tst_w_1},     {"tst_imm", 32, 0xff, tst_w_ff},
  {"tst_imm", 32, 0x80000000ULL, tst_w_msb},
};
#define NIMM ((int)(sizeof(IMM_FORMS) / sizeof(IMM_FORMS[0])))

// ---------------------------------------------------------------------------
// Conditional selects: one function per (operation, width, condition).
// ---------------------------------------------------------------------------

#define SEL_FN(NAME, MNEMONIC, REG, COND)                                           \
  static uint64_t NAME(uint64_t n, uint64_t m, uint64_t in, uint64_t *flags) {      \
    uint64_t r, f;                                                                  \
    __asm__ volatile("msr nzcv, %4\n\t" MNEMONIC " %" REG "0, %" REG "2, %" REG     \
                     "3, " COND "\n\tmrs %1, nzcv"                                  \
                     : "=&r"(r), "=&r"(f)                                           \
                     : "r"(n), "r"(m), "r"(in << 28)                                \
                     : "cc");                                                       \
    *flags = f >> 28;                                                               \
    return r;                                                                       \
  }

#define SEL_CONDS(OPNAME, MNEMONIC, REG, W)                                         \
  SEL_FN(OPNAME##_##W##_0, MNEMONIC, REG, "eq")                                     \
  SEL_FN(OPNAME##_##W##_1, MNEMONIC, REG, "ne")                                     \
  SEL_FN(OPNAME##_##W##_2, MNEMONIC, REG, "hs")                                     \
  SEL_FN(OPNAME##_##W##_3, MNEMONIC, REG, "lo")                                     \
  SEL_FN(OPNAME##_##W##_4, MNEMONIC, REG, "mi")                                     \
  SEL_FN(OPNAME##_##W##_5, MNEMONIC, REG, "pl")                                     \
  SEL_FN(OPNAME##_##W##_6, MNEMONIC, REG, "vs")                                     \
  SEL_FN(OPNAME##_##W##_7, MNEMONIC, REG, "vc")                                     \
  SEL_FN(OPNAME##_##W##_8, MNEMONIC, REG, "hi")                                     \
  SEL_FN(OPNAME##_##W##_9, MNEMONIC, REG, "ls")                                     \
  SEL_FN(OPNAME##_##W##_10, MNEMONIC, REG, "ge")                                    \
  SEL_FN(OPNAME##_##W##_11, MNEMONIC, REG, "lt")                                    \
  SEL_FN(OPNAME##_##W##_12, MNEMONIC, REG, "gt")                                    \
  SEL_FN(OPNAME##_##W##_13, MNEMONIC, REG, "le")                                    \
  SEL_FN(OPNAME##_##W##_14, MNEMONIC, REG, "al")                                    \
  SEL_FN(OPNAME##_##W##_15, MNEMONIC, REG, "nv")

SEL_CONDS(csel, "csel", "x", x)
SEL_CONDS(csel, "csel", "w", w)
SEL_CONDS(csinc, "csinc", "x", x)
SEL_CONDS(csinc, "csinc", "w", w)
SEL_CONDS(csinv, "csinv", "x", x)
SEL_CONDS(csinv, "csinv", "w", w)
SEL_CONDS(csneg, "csneg", "x", x)
SEL_CONDS(csneg, "csneg", "w", w)

typedef uint64_t (*sel_fn)(uint64_t, uint64_t, uint64_t, uint64_t *);
#define SEL_TABLE(OPNAME, W)                                                        \
  {OPNAME##_##W##_0, OPNAME##_##W##_1, OPNAME##_##W##_2, OPNAME##_##W##_3,          \
   OPNAME##_##W##_4, OPNAME##_##W##_5, OPNAME##_##W##_6, OPNAME##_##W##_7,          \
   OPNAME##_##W##_8, OPNAME##_##W##_9, OPNAME##_##W##_10, OPNAME##_##W##_11,        \
   OPNAME##_##W##_12, OPNAME##_##W##_13, OPNAME##_##W##_14, OPNAME##_##W##_15}
static const sel_fn SEL_FNS[4][2][16] = {
  {SEL_TABLE(csel, w), SEL_TABLE(csel, x)},
  {SEL_TABLE(csinc, w), SEL_TABLE(csinc, x)},
  {SEL_TABLE(csinv, w), SEL_TABLE(csinv, x)},
  {SEL_TABLE(csneg, w), SEL_TABLE(csneg, x)},
};
static const char *const SEL_OPS[4] = {"csel", "csinc", "csinv", "csneg"};

// ---------------------------------------------------------------------------
// FCMP
// ---------------------------------------------------------------------------

static uint64_t fcmp_s(uint32_t a_bits, uint32_t b_bits, uint64_t in) {
  float a, b;
  uint64_t f;
  memcpy(&a, &a_bits, sizeof a);
  memcpy(&b, &b_bits, sizeof b);
  __asm__ volatile("msr nzcv, %3\n\tfcmp %s1, %s2\n\tmrs %0, nzcv"
                   : "=&r"(f)
                   : "w"(a), "w"(b), "r"(in << 28)
                   : "cc");
  return f >> 28;
}
static uint64_t fcmp_d(uint64_t a_bits, uint64_t b_bits, uint64_t in) {
  double a, b;
  uint64_t f;
  memcpy(&a, &a_bits, sizeof a);
  memcpy(&b, &b_bits, sizeof b);
  __asm__ volatile("msr nzcv, %3\n\tfcmp %d1, %d2\n\tmrs %0, nzcv"
                   : "=&r"(f)
                   : "w"(a), "w"(b), "r"(in << 28)
                   : "cc");
  return f >> 28;
}

// ---------------------------------------------------------------------------
// JSON emission with exact accounting
// ---------------------------------------------------------------------------

static long g_facts = 0;
static int g_first = 1;
enum { K_ADDS, K_SUBS, K_CMP, K_CMP_IMM, K_TST, K_TST_IMM, K_ADCS, K_SBCS, K_ADC, K_SBC,
       K_CSEL, K_CSINC, K_CSINV, K_CSNEG, K_FCMP, K_COUNT };
static const char *const KIND_NAMES[K_COUNT] = {
  "adds", "subs", "cmp", "cmp_imm", "tst", "tst_imm", "adcs", "sbcs", "adc", "sbc",
  "csel", "csinc", "csinv", "csneg", "fcmp"};
static long g_per_kind[K_COUNT];

static void sep(void) {
  if (!g_first) printf(",\n");
  g_first = 0;
  g_facts++;
}

static int kind_of(const char *op) {
  for (int k = 0; k < K_COUNT; k++)
    if (strcmp(op, KIND_NAMES[k]) == 0) return k;
  return -1;
}

// {op,width,a,b,nzcv_in,result|null,nzcv}
static void emit_int(const char *op, int width, uint64_t a, uint64_t b, uint64_t in,
                     int has_result, uint64_t result, uint64_t out) {
  sep();
  g_per_kind[kind_of(op)]++;
  printf("  {\"op\":\"%s\",\"width\":%d,\"a\":\"0x%llx\",\"b\":\"0x%llx\",\"nzcv_in\":%llu,",
         op, width, (unsigned long long)a, (unsigned long long)b, (unsigned long long)in);
  if (has_result)
    printf("\"result\":\"0x%llx\",", (unsigned long long)result);
  else
    printf("\"result\":null,");
  printf("\"nzcv\":%llu}", (unsigned long long)out);
}

static void emit_sel(const char *op, int width, int cond, uint64_t n, uint64_t m, uint64_t in,
                     uint64_t result, uint64_t out) {
  sep();
  g_per_kind[kind_of(op)]++;
  printf("  {\"op\":\"%s\",\"width\":%d,\"cond\":%d,\"a\":\"0x%llx\",\"b\":\"0x%llx\","
         "\"nzcv_in\":%llu,\"result\":\"0x%llx\",\"nzcv\":%llu}",
         op, width, cond, (unsigned long long)n, (unsigned long long)m,
         (unsigned long long)in, (unsigned long long)result, (unsigned long long)out);
}

static void emit_fcmp(int width, uint64_t a, uint64_t b, uint64_t in, uint64_t out) {
  sep();
  g_per_kind[K_FCMP]++;
  printf("  {\"op\":\"fcmp\",\"width\":%d,\"a\":\"0x%llx\",\"b\":\"0x%llx\",\"nzcv_in\":%llu,"
         "\"result\":null,\"nzcv\":%llu}",
         width, (unsigned long long)a, (unsigned long long)b, (unsigned long long)in,
         (unsigned long long)out);
}

int main(int argc, char **argv) {
  const char *cpu = argc > 1 ? argv[1] : "unknown";
  const char *model = argc > 2 ? argv[2] : "unknown";
  const char *os = argc > 3 ? argv[3] : "unknown";
  const char *cc = argc > 4 ? argv[4] : "unknown";
  const char *date = argc > 5 ? argv[5] : "unknown";

  printf("{\n \"_header\": {\n");
  printf("  \"purpose\": \"AArch64 NZCV producer/consumer ground truth recorded NATIVELY: each "
         "fact executes one architectural instruction between MSR NZCV and MRS NZCV in a single "
         "inline-asm block and records the result register and the resulting NZCV. Replayed "
         "against crate::nzcv, the conditional-select decoder/model and the integer-only FCMP "
         "model by tests/aarch64_nzcv_silicon_bridge.rs.\",\n");
  printf("  \"recorded_on_cpu\": \"%s\",\n", cpu);
  printf("  \"hardware_model\": \"%s\",\n", model);
  printf("  \"os\": \"%s\",\n", os);
  printf("  \"compiler\": \"%s\",\n", cc);
  printf("  \"recorded_at\": \"%s\",\n", date);
  printf("  \"regen\": \"crates/trust-cg-verify/tests/fixtures/gen_aarch64_nzcv_silicon_truth.sh\",\n");
  printf("  \"encoding\": \"a/b/result are hex strings of the FULL 64-bit register values "
         "(W-form operands carry nonzero upper halves; the architecture reads bits 31:0); nzcv "
         "and nzcv_in are 4-bit N:Z:C:V integers (N = bit 3); cond is the 4-bit condition field; "
         "result is null for CMP/TST/FCMP, which write no general register.\",\n");
  printf("  \"scope\": \"regression evidence for one host CPU over a finite boundary grid; not a "
         "proof and not a claim about other AArch64 implementations.\"\n");
  printf(" },\n \"facts\": [\n");

  // ---- two-operand producers: ADDS/SUBS/CMP/TST, incoming NZCV varied ----
  for (int i = 0; i < NG; i++)
    for (int j = 0; j < NG; j++) {
      uint64_t a = G[i], b = G[j], f;
      uint64_t in = (uint64_t)((i * 7 + j * 3) & 15);
      uint64_t aw = w_operand(a, i), bw = w_operand(b, j + 1);
      uint64_t r;
      r = adds_x(a, b, in, &f);
      emit_int("adds", 64, a, b, in, 1, r, f);
      r = adds_w(aw, bw, in, &f);
      emit_int("adds", 32, aw, bw, in, 1, r, f);
      r = subs_x(a, b, in, &f);
      emit_int("subs", 64, a, b, in, 1, r, f);
      r = subs_w(aw, bw, in, &f);
      emit_int("subs", 32, aw, bw, in, 1, r, f);
      emit_int("cmp", 64, a, b, in, 0, 0, cmp_x(a, b, in));
      emit_int("cmp", 32, aw, bw, in, 0, 0, cmp_w(aw, bw, in));
      emit_int("tst", 64, a, b, in, 0, 0, tst_x(a, b, in));
      emit_int("tst", 32, aw, bw, in, 0, 0, tst_w(aw, bw, in));
    }

  // ---- carry consumers/producers: carry-in 0 and 1 (plus other flags set) ----
  for (int i = 0; i < NG; i++)
    for (int j = 0; j < NG; j++)
      for (int carry = 0; carry < 2; carry++) {
        uint64_t a = G[i], b = G[j], f;
        // Vary N/Z/V around the carry so ADC/SBC preservation covers them.
        uint64_t in = (uint64_t)(((i + j) & 1) ? 0xd : 0x4) & ~2ULL;
        in |= (uint64_t)carry << 1;
        uint64_t aw = w_operand(a, j), bw = w_operand(b, i + 2);
        uint64_t r;
        r = adcs_x(a, b, in, &f);
        emit_int("adcs", 64, a, b, in, 1, r, f);
        r = adcs_w(aw, bw, in, &f);
        emit_int("adcs", 32, aw, bw, in, 1, r, f);
        r = sbcs_x(a, b, in, &f);
        emit_int("sbcs", 64, a, b, in, 1, r, f);
        r = sbcs_w(aw, bw, in, &f);
        emit_int("sbcs", 32, aw, bw, in, 1, r, f);
        r = adc_x(a, b, in, &f);
        emit_int("adc", 64, a, b, in, 1, r, f);
        r = adc_w(aw, bw, in, &f);
        emit_int("adc", 32, aw, bw, in, 1, r, f);
        r = sbc_x(a, b, in, &f);
        emit_int("sbc", 64, a, b, in, 1, r, f);
        r = sbc_w(aw, bw, in, &f);
        emit_int("sbc", 32, aw, bw, in, 1, r, f);
      }

  // ---- immediate CMP/TST forms ----
  for (int k = 0; k < NIMM; k++)
    for (int i = 0; i < NG; i++) {
      const struct imm_form *form = &IMM_FORMS[k];
      uint64_t a = form->width == 32 ? w_operand(G[i], i + k) : G[i];
      uint64_t in = (uint64_t)((i + k) & 15);
      emit_int(form->op, form->width, a, form->imm, in, 0, 0, form->fn(a, in));
    }

  // ---- conditional selects: every condition x every incoming NZCV ----
  for (int op = 0; op < 4; op++)
    for (int w = 0; w < 2; w++)
      for (int cond = 0; cond < 16; cond++)
        for (int in = 0; in < 16; in++)
          for (int p = 0; p < NSEL; p++) {
            uint64_t n = SEL[p][0], m = SEL[p][1], f;
            if (w == 0) {
              n = w_operand(n, p + cond);
              m = w_operand(m, p + in);
            }
            uint64_t r = SEL_FNS[op][w][cond](n, m, (uint64_t)in, &f);
            emit_sel(SEL_OPS[op], w ? 64 : 32, cond, n, m, (uint64_t)in, r, f);
          }

  // ---- FCMP S/D over the IEEE edge grid ----
  for (int i = 0; i < NF32; i++)
    for (int j = 0; j < NF32; j++) {
      uint64_t in = (uint64_t)((i * 5 + j) & 15);
      emit_fcmp(32, F32[i], F32[j], in, fcmp_s(F32[i], F32[j], in));
    }
  for (int i = 0; i < NF64; i++)
    for (int j = 0; j < NF64; j++) {
      uint64_t in = (uint64_t)((i * 5 + j) & 15);
      emit_fcmp(64, F64[i], F64[j], in, fcmp_d(F64[i], F64[j], in));
    }

  printf("\n ],\n \"_accounting\": {\n  \"facts\": %ld,\n  \"per_op\": {", g_facts);
  for (int k = 0; k < K_COUNT; k++)
    printf("%s\"%s\": %ld", k ? ", " : "", KIND_NAMES[k], g_per_kind[k]);
  printf("}\n }\n}\n");
  return 0;
}
