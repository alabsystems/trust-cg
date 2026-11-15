// trust-cg-codegen/tests/e2e_aarch64_bit_intrinsics_bulk_memory.rs
//
// Native AArch64 control for the trust-ir WS3.20 (F-057) constructs:
// `BinOp::RotL`/`RotR`/`FCopySign`, `UnOp::CtLz`/`CtTz`/`BSwap`/`BitReverse`
// and `Inst::MemCopy`/`MemSet`. None has a single LIR opcode; the adapter
// expands the bit operations into covered shift/mask/popcount opcodes and the
// bulk-memory pair into the libc memcpy/memmove/memset intrinsics. This
// compiles one module at O0-O3, links it against a C driver that recomputes
// every result with its own bit-by-bit reference (not a compiler builtin), and
// executes it: every width, the zero operand (`ctlz 0 = cttz 0 = width`),
// dynamic and constant rotate amounts including ones at and beyond the width,
// signed zeros / infinities / NaN payloads for copySign, and overlapping,
// empty (null-pointer) and constant-length bulk copies and fills.
//
// Execution evidence on this host, not a proof of the expansion.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{BinOp, Ty, UnOp};
use trust_ir_build::ModuleBuilder;

#[path = "common/native_host.rs"]
mod native_host;

/// `fn name(x: ty, n: ty) -> ty { op x, n }`.
fn binary(builder: &mut ModuleBuilder, name: &str, op: BinOp, ty: Ty) {
    let sig = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let mut f = builder.function(name, sig);
    let entry = f.create_block();
    let x = f.add_block_param(entry, ty.clone());
    let n = f.add_block_param(entry, ty.clone());
    f.switch_to_block(entry);
    let r = f.binop(op, ty, x, n);
    f.ret(vec![r]);
    f.build();
}

/// `fn name(x: ty) -> ty { op x, <amount> }` with a constant amount.
fn rotate_by_constant(builder: &mut ModuleBuilder, name: &str, op: BinOp, ty: Ty, amount: i128) {
    let sig = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
    let mut f = builder.function(name, sig);
    let entry = f.create_block();
    let x = f.add_block_param(entry, ty.clone());
    f.switch_to_block(entry);
    let n = f.iconst(ty.clone(), amount);
    let r = f.binop(op, ty, x, n);
    f.ret(vec![r]);
    f.build();
}

/// `fn name(x: ty) -> ty { op x }`.
fn unary(builder: &mut ModuleBuilder, name: &str, op: UnOp, ty: Ty) {
    let sig = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
    let mut f = builder.function(name, sig);
    let entry = f.create_block();
    let x = f.add_block_param(entry, ty.clone());
    f.switch_to_block(entry);
    let r = f.unop(op, ty, x);
    f.ret(vec![r]);
    f.build();
}

/// `fn name(dst: ptr, src: ptr, n: u64) { memcopy[overlap] dst, src, n }`.
fn mem_copy(builder: &mut ModuleBuilder, name: &str, overlap: bool) {
    let sig = builder.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64], vec![]);
    let mut f = builder.function(name, sig);
    let entry = f.create_block();
    let dst = f.add_block_param(entry, Ty::Ptr);
    let src = f.add_block_param(entry, Ty::Ptr);
    let n = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    f.memcopy(dst, src, n, overlap);
    f.ret(vec![]);
    f.build();
}

/// `fn copy16(dst: ptr, src: ptr) { memcopy dst, src, 16 }`: a constant
/// count, which instruction selection copies inline.
fn mem_copy_constant(builder: &mut ModuleBuilder, name: &str, count: i128) {
    let sig = builder.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![]);
    let mut f = builder.function(name, sig);
    let entry = f.create_block();
    let dst = f.add_block_param(entry, Ty::Ptr);
    let src = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    let n = f.iconst(Ty::U64, count);
    f.memcopy(dst, src, n, false);
    f.ret(vec![]);
    f.build();
}

/// `fn name(dst: ptr, byte: u8, n: u64) { memset dst, byte, n }`.
fn mem_set(builder: &mut ModuleBuilder, name: &str) {
    let sig = builder.add_func_type(vec![Ty::Ptr, Ty::U8, Ty::U64], vec![]);
    let mut f = builder.function(name, sig);
    let entry = f.create_block();
    let dst = f.add_block_param(entry, Ty::Ptr);
    let byte = f.add_block_param(entry, Ty::U8);
    let n = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    f.memset(dst, byte, n);
    f.ret(vec![]);
    f.build();
}

/// `fn zero(dst: ptr, n: u64) { memset dst, 0, n }`: a constant fill byte.
fn mem_zero(builder: &mut ModuleBuilder, name: &str) {
    let sig = builder.add_func_type(vec![Ty::Ptr, Ty::U64], vec![]);
    let mut f = builder.function(name, sig);
    let entry = f.create_block();
    let dst = f.add_block_param(entry, Ty::Ptr);
    let n = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::U8, 0);
    f.memset(dst, zero, n);
    f.ret(vec![]);
    f.build();
}

const WIDTHS: [(Ty, &str); 5] = [
    (Ty::U8, "u8"),
    (Ty::U16, "u16"),
    (Ty::U32, "u32"),
    (Ty::U64, "u64"),
    // Register pairs: the expansion's 128-bit shifts, masks (`Iconst128`)
    // and popcount run on the i128 lowering.
    (Ty::U128, "u128"),
];

fn bit_intrinsics_module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("ws320_bit_intrinsics");
    for (ty, suffix) in WIDTHS {
        binary(
            &mut builder,
            &format!("rotl_{suffix}"),
            BinOp::RotL,
            ty.clone(),
        );
        binary(
            &mut builder,
            &format!("rotr_{suffix}"),
            BinOp::RotR,
            ty.clone(),
        );
        unary(
            &mut builder,
            &format!("ctlz_{suffix}"),
            UnOp::CtLz,
            ty.clone(),
        );
        unary(
            &mut builder,
            &format!("cttz_{suffix}"),
            UnOp::CtTz,
            ty.clone(),
        );
        unary(
            &mut builder,
            &format!("bswap_{suffix}"),
            UnOp::BSwap,
            ty.clone(),
        );
        unary(
            &mut builder,
            &format!("bitrev_{suffix}"),
            UnOp::BitReverse,
            ty,
        );
    }
    // Constant amounts: in range, a multiple of the width (the identity),
    // beyond the width, and a negative signed spelling (-1 mod 8 = 7).
    rotate_by_constant(&mut builder, "rotl_u32_by5", BinOp::RotL, Ty::U32, 5);
    rotate_by_constant(&mut builder, "rotr_u64_by13", BinOp::RotR, Ty::U64, 13);
    rotate_by_constant(&mut builder, "rotl_u16_by32", BinOp::RotL, Ty::U16, 32);
    rotate_by_constant(&mut builder, "rotr_u8_by11", BinOp::RotR, Ty::U8, 11);
    rotate_by_constant(&mut builder, "rotl_i8_bym1", BinOp::RotL, Ty::I8, -1);
    // A signed carrier: the rotate must not see the sign extension.
    binary(&mut builder, "rotr_i16", BinOp::RotR, Ty::I16);
    binary(&mut builder, "copysign_f32", BinOp::FCopySign, Ty::F32);
    binary(&mut builder, "copysign_f64", BinOp::FCopySign, Ty::F64);
    mem_copy(&mut builder, "mem_copy", false);
    mem_copy(&mut builder, "mem_move", true);
    mem_copy_constant(&mut builder, "mem_copy16", 16);
    mem_set(&mut builder, "mem_set");
    mem_zero(&mut builder, "mem_zero");
    builder.build().expect("ModuleBuilder::build: test fixture")
}

const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern uint8_t  rotl_u8(uint8_t, uint8_t);    extern uint8_t  rotr_u8(uint8_t, uint8_t);
extern uint16_t rotl_u16(uint16_t, uint16_t); extern uint16_t rotr_u16(uint16_t, uint16_t);
extern uint32_t rotl_u32(uint32_t, uint32_t); extern uint32_t rotr_u32(uint32_t, uint32_t);
extern uint64_t rotl_u64(uint64_t, uint64_t); extern uint64_t rotr_u64(uint64_t, uint64_t);
extern uint8_t  ctlz_u8(uint8_t);   extern uint16_t ctlz_u16(uint16_t);
extern uint32_t ctlz_u32(uint32_t); extern uint64_t ctlz_u64(uint64_t);
extern uint8_t  cttz_u8(uint8_t);   extern uint16_t cttz_u16(uint16_t);
extern uint32_t cttz_u32(uint32_t); extern uint64_t cttz_u64(uint64_t);
extern uint8_t  bswap_u8(uint8_t);   extern uint16_t bswap_u16(uint16_t);
extern uint32_t bswap_u32(uint32_t); extern uint64_t bswap_u64(uint64_t);
extern uint8_t  bitrev_u8(uint8_t);   extern uint16_t bitrev_u16(uint16_t);
extern uint32_t bitrev_u32(uint32_t); extern uint64_t bitrev_u64(uint64_t);
extern uint32_t rotl_u32_by5(uint32_t);  extern uint64_t rotr_u64_by13(uint64_t);
extern uint16_t rotl_u16_by32(uint16_t); extern uint8_t  rotr_u8_by11(uint8_t);
extern int8_t   rotl_i8_bym1(int8_t);    extern int16_t  rotr_i16(int16_t, int16_t);
extern float  copysign_f32(float, float);
extern double copysign_f64(double, double);
extern void mem_copy(void *, const void *, uint64_t);
extern void mem_move(void *, const void *, uint64_t);
extern void mem_copy16(void *, const void *);
extern void mem_set(void *, uint8_t, uint64_t);
extern void mem_zero(void *, uint64_t);

static uint64_t mask(unsigned w) { return w == 64 ? ~0ull : ((1ull << w) - 1); }
static uint64_t ref_rot(uint64_t x, uint64_t n, unsigned w, int left) {
    x &= mask(w);
    unsigned k = (unsigned)(n % w);
    if (k == 0) return x;
    return left ? ((x << k) | (x >> (w - k))) & mask(w) : ((x >> k) | (x << (w - k))) & mask(w);
}
static uint64_t ref_clz(uint64_t x, unsigned w) {
    uint64_t c = 0;
    for (int i = (int)w - 1; i >= 0 && !((x >> i) & 1); i--) c++;
    return c;
}
static uint64_t ref_ctz(uint64_t x, unsigned w) {
    uint64_t c = 0;
    for (unsigned i = 0; i < w && !((x >> i) & 1); i++) c++;
    return c;
}
static uint64_t ref_bswap(uint64_t x, unsigned w) {
    uint64_t r = 0;
    for (unsigned i = 0; i < w / 8; i++) r |= ((x >> (8 * i)) & 0xff) << (w - 8 - 8 * i);
    return r;
}
typedef unsigned __int128 u128;
extern u128 rotl_u128(u128, u128);  extern u128 rotr_u128(u128, u128);
extern u128 ctlz_u128(u128); extern u128 cttz_u128(u128);
extern u128 bswap_u128(u128); extern u128 bitrev_u128(u128);
static u128 ref_rot128(u128 x, u128 n, int left) {
    unsigned k = (unsigned)(n % 128);
    if (k == 0) return x;
    return left ? (x << k) | (x >> (128 - k)) : (x >> k) | (x << (128 - k));
}
static u128 ref_clz128(u128 x) {
    u128 c = 0;
    for (int i = 127; i >= 0 && !((x >> i) & 1); i--) c++;
    return c;
}
static u128 ref_ctz128(u128 x) {
    u128 c = 0;
    for (int i = 0; i < 128 && !((x >> i) & 1); i++) c++;
    return c;
}
static u128 ref_bswap128(u128 x) {
    u128 r = 0;
    for (int i = 0; i < 16; i++) r |= ((x >> (8 * i)) & 0xff) << (120 - 8 * i);
    return r;
}
static u128 ref_bitrev128(u128 x) {
    u128 r = 0;
    for (int i = 0; i < 128; i++) if ((x >> i) & 1) r |= (u128)1 << (127 - i);
    return r;
}
static int failures128 = 0;
static void check128(const char *what, u128 x, u128 n, u128 got, u128 want) {
    if (got != want && failures128++ < 20)
        printf("MISMATCH %s x=%#llx:%016llx n=%llu got=%#llx:%016llx want=%#llx:%016llx\n",
               what, (unsigned long long)(x >> 64), (unsigned long long)x,
               (unsigned long long)n, (unsigned long long)(got >> 64), (unsigned long long)got,
               (unsigned long long)(want >> 64), (unsigned long long)want);
}

static uint64_t ref_bitrev(uint64_t x, unsigned w) {
    uint64_t r = 0;
    for (unsigned i = 0; i < w; i++) if ((x >> i) & 1) r |= 1ull << (w - 1 - i);
    return r;
}

static const uint64_t PATTERNS[] = {
    0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x100, 0x5555555555555555ull, 0xaaaaaaaaaaaaaaaaull,
    0x0f0f0f0f0f0f0f0full, 0x8000000000000000ull, 0x7fffffffffffffffull, ~0ull,
    0x0123456789abcdefull, 0xfedcba9876543210ull, 0xdeadbeefcafebabeull, 0x8000ull, 0x80000000ull,
};
#define NP (sizeof(PATTERNS) / sizeof(PATTERNS[0]))

static int failures = 0;
static void check(const char *what, uint64_t x, uint64_t n, uint64_t got, uint64_t want) {
    if (got != want && failures++ < 20)
        printf("MISMATCH %s x=%#llx n=%llu got=%#llx want=%#llx\n", what,
               (unsigned long long)x, (unsigned long long)n,
               (unsigned long long)got, (unsigned long long)want);
}

#define WIDTH_CASES(W, T)                                                              \
    for (unsigned i = 0; i < NP; i++) {                                                \
        T x = (T)PATTERNS[i];                                                          \
        for (uint64_t n = 0; n <= 2 * W + 3; n++) {                                    \
            check("rotl_" #T, x, n, rotl_##T##_fn(x, (T)n), ref_rot(x, n, W, 1));       \
            check("rotr_" #T, x, n, rotr_##T##_fn(x, (T)n), ref_rot(x, n, W, 0));       \
        }                                                                              \
        check("rotl_" #T " max", x, (T)~0ull, rotl_##T##_fn(x, (T)~0ull),              \
              ref_rot(x, (T)~0ull, W, 1));                                             \
        check("ctlz_" #T, x, 0, ctlz_##T##_fn(x), ref_clz(x, W));                      \
        check("cttz_" #T, x, 0, cttz_##T##_fn(x), ref_ctz(x, W));                      \
        check("bswap_" #T, x, 0, bswap_##T##_fn(x), W == 8 ? x : ref_bswap(x, W));     \
        check("bitrev_" #T, x, 0, bitrev_##T##_fn(x), ref_bitrev(x, W));               \
    }

#define rotl_uint8_t_fn rotl_u8
#define rotr_uint8_t_fn rotr_u8
#define ctlz_uint8_t_fn ctlz_u8
#define cttz_uint8_t_fn cttz_u8
#define bswap_uint8_t_fn bswap_u8
#define bitrev_uint8_t_fn bitrev_u8
#define rotl_uint16_t_fn rotl_u16
#define rotr_uint16_t_fn rotr_u16
#define ctlz_uint16_t_fn ctlz_u16
#define cttz_uint16_t_fn cttz_u16
#define bswap_uint16_t_fn bswap_u16
#define bitrev_uint16_t_fn bitrev_u16
#define rotl_uint32_t_fn rotl_u32
#define rotr_uint32_t_fn rotr_u32
#define ctlz_uint32_t_fn ctlz_u32
#define cttz_uint32_t_fn cttz_u32
#define bswap_uint32_t_fn bswap_u32
#define bitrev_uint32_t_fn bitrev_u32
#define rotl_uint64_t_fn rotl_u64
#define rotr_uint64_t_fn rotr_u64
#define ctlz_uint64_t_fn ctlz_u64
#define cttz_uint64_t_fn cttz_u64
#define bswap_uint64_t_fn bswap_u64
#define bitrev_uint64_t_fn bitrev_u64

static uint32_t f32_bits(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }
static float f32_of(uint32_t u) { float f; memcpy(&f, &u, 4); return f; }
static uint64_t f64_bits(double d) { uint64_t u; memcpy(&u, &d, 8); return u; }
static double f64_of(uint64_t u) { double d; memcpy(&d, &u, 8); return d; }

int main(void) {
    WIDTH_CASES(8, uint8_t)
    WIDTH_CASES(16, uint16_t)
    WIDTH_CASES(32, uint32_t)
    WIDTH_CASES(64, uint64_t)

    for (unsigned i = 0; i < NP; i++) {
        for (unsigned j = 0; j < NP; j++) {
            u128 x = ((u128)PATTERNS[i] << 64) | PATTERNS[j];
            for (unsigned n = 0; n <= 259; n += (n < 131 ? 1 : 64)) {
                check128("rotl_u128", x, n, rotl_u128(x, n), ref_rot128(x, n, 1));
                check128("rotr_u128", x, n, rotr_u128(x, n), ref_rot128(x, n, 0));
            }
            u128 huge = ~(u128)0 - 2;
            check128("rotl_u128 huge", x, huge, rotl_u128(x, huge), ref_rot128(x, huge, 1));
            check128("ctlz_u128", x, 0, ctlz_u128(x), ref_clz128(x));
            check128("cttz_u128", x, 0, cttz_u128(x), ref_ctz128(x));
            check128("bswap_u128", x, 0, bswap_u128(x), ref_bswap128(x));
            check128("bitrev_u128", x, 0, bitrev_u128(x), ref_bitrev128(x));
        }
    }
    failures += failures128;

    for (unsigned i = 0; i < NP; i++) {
        uint64_t x = PATTERNS[i];
        check("rotl_u32_by5", x, 5, rotl_u32_by5((uint32_t)x), ref_rot(x, 5, 32, 1));
        check("rotr_u64_by13", x, 13, rotr_u64_by13(x), ref_rot(x, 13, 64, 0));
        check("rotl_u16_by32", x, 32, rotl_u16_by32((uint16_t)x), ref_rot(x, 32, 16, 1));
        check("rotr_u8_by11", x, 11, rotr_u8_by11((uint8_t)x), ref_rot(x, 11, 8, 0));
        check("rotl_i8_bym1", x, 255, (uint8_t)rotl_i8_bym1((int8_t)x), ref_rot(x, 255, 8, 1));
        for (uint64_t n = 0; n < 40; n++)
            check("rotr_i16", x, n, (uint16_t)rotr_i16((int16_t)x, (int16_t)n),
                  ref_rot(x, n, 16, 0));
    }

    static const uint32_t F32[] = {0x00000000u, 0x80000000u, 0x3fc00000u, 0xc0100000u,
                                   0x7f800000u, 0xff800000u, 0x7fc01234u, 0xffa00001u,
                                   0x00000001u, 0x807fffffu};
    for (unsigned i = 0; i < sizeof(F32) / 4; i++)
        for (unsigned j = 0; j < sizeof(F32) / 4; j++)
            check("copysign_f32", F32[i], F32[j],
                  f32_bits(copysign_f32(f32_of(F32[i]), f32_of(F32[j]))),
                  (F32[i] & 0x7fffffffu) | (F32[j] & 0x80000000u));
    static const uint64_t F64[] = {0, 0x8000000000000000ull, 0x3ff8000000000000ull,
                                   0xc002000000000000ull, 0x7ff0000000000000ull,
                                   0xfff0000000000000ull, 0x7ff8000000001234ull,
                                   0xfff4000000000001ull, 1, 0x800fffffffffffffull};
    for (unsigned i = 0; i < sizeof(F64) / 8; i++)
        for (unsigned j = 0; j < sizeof(F64) / 8; j++)
            check("copysign_f64", F64[i], F64[j],
                  f64_bits(copysign_f64(f64_of(F64[i]), f64_of(F64[j]))),
                  (F64[i] & 0x7fffffffffffffffull) | (F64[j] & 0x8000000000000000ull));

    static const uint64_t COUNTS[] = {0, 1, 7, 8, 15, 16, 17, 31, 33, 64};
    for (unsigned c = 0; c < sizeof(COUNTS) / 8; c++) {
        uint64_t n = COUNTS[c];
        unsigned char src[80], got[80], want[80];
        for (unsigned i = 0; i < 80; i++) { src[i] = (unsigned char)(i * 37 + 11); got[i] = want[i] = 0xee; }
        mem_copy(got + 3, src + 1, n);
        memcpy(want + 3, src + 1, n);
        check("mem_copy", n, 0, (uint64_t)memcmp(got, want, 80), 0);

        for (int dir = 0; dir < 2; dir++) {
            for (unsigned i = 0; i < 80; i++) got[i] = want[i] = (unsigned char)(i * 13 + 5);
            unsigned d = dir ? 0 : 5, s = dir ? 5 : 0;
            mem_move(got + d, got + s, n);
            memmove(want + d, want + s, n);
            check(dir ? "mem_move down" : "mem_move up", n, 0,
                  (uint64_t)memcmp(got, want, 80), 0);
        }

        static const unsigned char FILLS[] = {0x00, 0x5a, 0xff};
        for (unsigned f = 0; f < sizeof(FILLS); f++) {
            for (unsigned i = 0; i < 80; i++) got[i] = want[i] = 0x11;
            mem_set(got + 2, FILLS[f], n);
            memset(want + 2, FILLS[f], n);
            check("mem_set", n, FILLS[f], (uint64_t)memcmp(got, want, 80), 0);
        }
        for (unsigned i = 0; i < 80; i++) got[i] = want[i] = 0x33;
        mem_zero(got + 9, n);
        memset(want + 9, 0, n);
        check("mem_zero", n, 0, (uint64_t)memcmp(got, want, 80), 0);
    }
    {
        unsigned char src[32], got[32], want[32];
        for (unsigned i = 0; i < 32; i++) { src[i] = (unsigned char)(200 - i); got[i] = want[i] = 0x77; }
        mem_copy16(got + 4, src + 3);
        memcpy(want + 4, src + 3, 16);
        check("mem_copy16", 16, 0, (uint64_t)memcmp(got, want, 32), 0);
    }
    /* A zero count is a no-op for any pointer. */
    mem_copy(NULL, NULL, 0);
    mem_move(NULL, NULL, 0);
    mem_set(NULL, 0xab, 0);
    mem_zero(NULL, 0);

    if (failures) { printf("%d mismatch(es)\n", failures); return 1; }
    printf("ws320: rotates, bit counts, byte/bit reversal, copysign and bulk memory match\n");
    return 0;
}
"#;

fn link_run(object: &[u8], tag: &str) -> Option<(i32, String)> {
    if !native_host::NATIVE {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_ws320_{tag}_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let object_path = dir.join("module.o");
    let driver_path = dir.join("driver.c");
    let binary_path = dir.join("driver");
    fs::write(&object_path, object).unwrap();
    fs::write(&driver_path, DRIVER).unwrap();
    let link = Command::new("cc")
        .arg("-O1")
        .arg("-fno-builtin")
        .arg(&driver_path)
        .arg(&object_path)
        .arg("-o")
        .arg(&binary_path)
        .args(native_host::c_math_library_args())
        .output()
        .expect("cc");
    assert!(
        link.status.success(),
        "{tag}: link failed (files kept in {dir:?}):\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&binary_path).output().expect("run driver");
    let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
    let code = run.status.code().unwrap_or(-1);
    if code == 0 {
        let _ = fs::remove_dir_all(&dir);
    }
    Some((code, stdout))
}

#[test]
fn e2e_aarch64_ws320_bit_intrinsics_and_bulk_memory_match_c_reference() {
    let module = bit_intrinsics_module();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let compiler = Compiler::new(CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        })
        .with_codegen_license(permit_unlicensed());
        let object = compiler
            .compile(&module)
            .map(|output| output.object_code)
            .unwrap_or_else(|error| panic!("{opt_level:?}: WS3.20 module must compile: {error:?}"));
        let Some((code, stdout)) = link_run(&object, &format!("{opt_level:?}")) else {
            return;
        };
        assert_eq!(code, 0, "{opt_level:?}: {stdout}");
        eprintln!("{opt_level:?}: {}", stdout.trim());
    }
}

/// Since trust-ir's v51 INST wire batch (`e2154f00`) every WS3.20 sub-op and
/// both bulk-memory instructions have a binary tag, so the module has a tMBC
/// image (before v51 every identity keyed by one refused it by name as
/// `NoTmbcWireImage`): the writer raises the header to 51 for it alone and
/// trust-ir's reader decodes it back to the same module. trust-cg's reader
/// then applies the v41+ producer rule to this unstamped test module, and a
/// proof-required compile binds the image and still fails CLOSED, at proof
/// promotion, for want of complete evidence for the emitted opcodes.
#[test]
fn ws320_module_has_a_v51_tmbc_wire_image_and_proof_custody_stays_fail_closed() {
    let module = bit_intrinsics_module();
    let envelope = trust_cg_codegen::pipeline::encode_tmbc(&module)
        .expect("every WS3.20 construct has a wire tag at v51");
    let payload = &envelope[8..];
    assert_eq!(&payload[..8], b"TRUST_IR");
    assert_eq!(
        u32::from_le_bytes(payload[8..12].try_into().expect("header word")),
        51,
        "a module carrying an INST wire batch member is written at v51"
    );
    assert_eq!(
        trust_ir::binary::deserialize_module(payload).expect("trust-ir reads the v51 image"),
        module,
        "the tMBC image carries the module exactly"
    );
    let unstamped = trust_cg_codegen::pipeline::decode_tmbc(&envelope)
        .expect_err("a v41+ image with an unstamped body is a producer omission")
        .to_string();
    assert!(
        unstamped.contains("producer omission") && unstamped.contains("v51"),
        "{unstamped}"
    );
    let proof_compiler = Compiler::new(CompilerConfig {
        emit_proofs: true,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    let refused = proof_compiler
        .compile(&module)
        .expect_err("proof custody still requires complete evidence")
        .to_string();
    assert!(!refused.contains("no tMBC wire image"), "{refused}");
    assert!(refused.contains("proof promotion rejected"), "{refused}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
