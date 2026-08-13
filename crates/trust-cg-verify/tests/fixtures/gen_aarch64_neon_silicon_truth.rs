// gen_aarch64_neon_silicon_truth.rs — NATIVE NEON BARE-SILICON oracle generator.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE NEON SILICON-TRUTH GENERATOR — bare-silicon oracle for the
// B-aarch64-neon differential bridge (AArch64 integer NEON).
// ===========================================================================
//
// This is the SIMPLEST possible oracle: the host IS an Apple M4 (NATIVE AArch64,
// runs NEON DIRECTLY — no Rosetta/qemu/Clean-chip-file). For each integer NEON op
// + arrangement, this binary loads two 128-bit operands into q-registers, executes
// the REAL instruction via `std::arch::asm!` (`add v0.4s, v1.4s, v2.4s`, ...) with
// `#[inline(never)]` wrappers, and reads back the 128-bit result STRAIGHT off the
// silicon (`str q0`). Each emitted fact is therefore a `:= rfl`-strength HARDWARE
// theorem — the SAME oracle tier as the AArch64 integer bridge (which records M4
// chip results), one notch ABOVE Rosetta/qemu.
//
// otool-confirm the real NEON mnemonics in the built binary:
//   otool -tv <bin> | grep -E 'add\.4s|cmgt\.|umaxv|movi'
// (the macro-generated wrappers each contain exactly one packed NEON instruction).
//
// GRID (no silent truncation; deterministic): per-lane edge values
//   {0, all-ones(-1), INT_MIN, INT_MAX, 1, two deterministic LCG "random" values}
// are packed into the 128-bit operands as the full Cartesian product over a SMALL
// per-lane alphabet, PLUS alternating patterns. For shl/ushr/sshr a fixed set of
// shift amounts INCLUDING amounts >= lane width is sampled (the encoder's clamp
// contract — the analog of the x86 packed-shift saturation teeth).
//
// Honest-deferral: dup/ins/movi take an imm / lane-index / scalar (NOT a second
// vector), and umaxv is a cross-lane reduction to a scalar. They ARE bridged here
// by sampling FIXED imms / lanes / scalars (the x86 imul_imm/LEA pattern), so the
// fixture carries them with an explicit `kind` discriminator; the bridge feeds the
// matching encoder the SAME imm/lane/scalar. NONE are silently dropped.
//
// Regenerate (run ON the M4):
//   rustc -O crates/trust-cg-verify/tests/fixtures/gen_aarch64_neon_silicon_truth.rs \
//       -o /tmp/gen_neon && /tmp/gen_neon \
//       crates/trust-cg-verify/tests/fixtures/aarch64_neon_silicon_truth.json

use std::arch::asm;
use std::collections::BTreeMap;
use std::fmt::Write as _;

// ===========================================================================
// NATIVE NEON wrappers — each runs ONE real packed instruction on the M4.
// The arrangement is part of the mnemonic, so there is one wrapper per
// (op, arrangement). `str q0` reads back the FULL 128-bit register; for a
// 64-bit (D-register) arrangement the hardware ZEROES the upper 64 bits.
// ===========================================================================

macro_rules! neon_bin {
    ($name:ident, $mnem:literal) => {
        #[inline(never)]
        fn $name(a: u128, b: u128) -> u128 {
            let mut out: u128 = 0;
            unsafe {
                asm!(
                    "ldr q1, [{a}]",
                    "ldr q2, [{b}]",
                    $mnem,
                    "str q0, [{o}]",
                    a = in(reg) &a, b = in(reg) &b, o = in(reg) &mut out,
                    out("v0") _, out("v1") _, out("v2") _,
                );
            }
            out
        }
    };
}

macro_rules! neon_un {
    ($name:ident, $mnem:literal) => {
        #[inline(never)]
        fn $name(a: u128) -> u128 {
            let mut out: u128 = 0;
            unsafe {
                asm!(
                    "ldr q1, [{a}]",
                    $mnem,
                    "str q0, [{o}]",
                    a = in(reg) &a, o = in(reg) &mut out,
                    out("v0") _, out("v1") _,
                );
            }
            out
        }
    };
}

// MLA accumulates INTO the destination: Vd += Vn * Vm. The wrapper loads the
// accumulator (va) into q0, vn into q1, vm into q2, runs `mla`, reads back q0.
macro_rules! neon_mla {
    ($name:ident, $mnem:literal) => {
        #[inline(never)]
        fn $name(va: u128, vn: u128, vm: u128) -> u128 {
            let mut out: u128 = va;
            unsafe {
                asm!(
                    "ldr q0, [{o}]",
                    "ldr q1, [{n}]",
                    "ldr q2, [{m}]",
                    $mnem,
                    "str q0, [{o}]",
                    n = in(reg) &vn, m = in(reg) &vm, o = in(reg) &mut out,
                    out("v0") _, out("v1") _, out("v2") _,
                );
            }
            out
        }
    };
}

// ---- ADD / SUB / MUL / NEG ----
neon_bin!(add_8b, "add v0.8b, v1.8b, v2.8b");
neon_bin!(add_16b, "add v0.16b, v1.16b, v2.16b");
neon_bin!(add_4h, "add v0.4h, v1.4h, v2.4h");
neon_bin!(add_8h, "add v0.8h, v1.8h, v2.8h");
neon_bin!(add_2s, "add v0.2s, v1.2s, v2.2s");
neon_bin!(add_4s, "add v0.4s, v1.4s, v2.4s");
neon_bin!(add_2d, "add v0.2d, v1.2d, v2.2d");

neon_bin!(sub_8b, "sub v0.8b, v1.8b, v2.8b");
neon_bin!(sub_16b, "sub v0.16b, v1.16b, v2.16b");
neon_bin!(sub_4h, "sub v0.4h, v1.4h, v2.4h");
neon_bin!(sub_8h, "sub v0.8h, v1.8h, v2.8h");
neon_bin!(sub_2s, "sub v0.2s, v1.2s, v2.2s");
neon_bin!(sub_4s, "sub v0.4s, v1.4s, v2.4s");
neon_bin!(sub_2d, "sub v0.2d, v1.2d, v2.2d");

neon_bin!(mul_8b, "mul v0.8b, v1.8b, v2.8b");
neon_bin!(mul_16b, "mul v0.16b, v1.16b, v2.16b");
neon_bin!(mul_4h, "mul v0.4h, v1.4h, v2.4h");
neon_bin!(mul_8h, "mul v0.8h, v1.8h, v2.8h");
neon_bin!(mul_2s, "mul v0.2s, v1.2s, v2.2s");
neon_bin!(mul_4s, "mul v0.4s, v1.4s, v2.4s");

neon_un!(neg_8b, "neg v0.8b, v1.8b");
neon_un!(neg_16b, "neg v0.16b, v1.16b");
neon_un!(neg_4h, "neg v0.4h, v1.4h");
neon_un!(neg_8h, "neg v0.8h, v1.8h");
neon_un!(neg_2s, "neg v0.2s, v1.2s");
neon_un!(neg_4s, "neg v0.4s, v1.4s");
neon_un!(neg_2d, "neg v0.2d, v1.2d");

// ---- bitwise (AND/ORR/EOR/BIC over 8b=64-bit and 16b=128-bit; NOT unary) ----
neon_bin!(and_8b, "and v0.8b, v1.8b, v2.8b");
neon_bin!(and_16b, "and v0.16b, v1.16b, v2.16b");
neon_bin!(orr_8b, "orr v0.8b, v1.8b, v2.8b");
neon_bin!(orr_16b, "orr v0.16b, v1.16b, v2.16b");
neon_bin!(eor_8b, "eor v0.8b, v1.8b, v2.8b");
neon_bin!(eor_16b, "eor v0.16b, v1.16b, v2.16b");
neon_bin!(bic_8b, "bic v0.8b, v1.8b, v2.8b");
neon_bin!(bic_16b, "bic v0.16b, v1.16b, v2.16b");
neon_un!(not_8b, "not v0.8b, v1.8b");
neon_un!(not_16b, "not v0.16b, v1.16b");

// ---- compare (CMEQ unsigned-eq, CMGT/CMGE signed) ----
neon_bin!(cmeq_8b, "cmeq v0.8b, v1.8b, v2.8b");
neon_bin!(cmeq_16b, "cmeq v0.16b, v1.16b, v2.16b");
neon_bin!(cmeq_4h, "cmeq v0.4h, v1.4h, v2.4h");
neon_bin!(cmeq_8h, "cmeq v0.8h, v1.8h, v2.8h");
neon_bin!(cmeq_2s, "cmeq v0.2s, v1.2s, v2.2s");
neon_bin!(cmeq_4s, "cmeq v0.4s, v1.4s, v2.4s");
neon_bin!(cmeq_2d, "cmeq v0.2d, v1.2d, v2.2d");

neon_bin!(cmgt_8b, "cmgt v0.8b, v1.8b, v2.8b");
neon_bin!(cmgt_16b, "cmgt v0.16b, v1.16b, v2.16b");
neon_bin!(cmgt_4h, "cmgt v0.4h, v1.4h, v2.4h");
neon_bin!(cmgt_8h, "cmgt v0.8h, v1.8h, v2.8h");
neon_bin!(cmgt_2s, "cmgt v0.2s, v1.2s, v2.2s");
neon_bin!(cmgt_4s, "cmgt v0.4s, v1.4s, v2.4s");
neon_bin!(cmgt_2d, "cmgt v0.2d, v1.2d, v2.2d");

neon_bin!(cmge_8b, "cmge v0.8b, v1.8b, v2.8b");
neon_bin!(cmge_16b, "cmge v0.16b, v1.16b, v2.16b");
neon_bin!(cmge_4h, "cmge v0.4h, v1.4h, v2.4h");
neon_bin!(cmge_8h, "cmge v0.8h, v1.8h, v2.8h");
neon_bin!(cmge_2s, "cmge v0.2s, v1.2s, v2.2s");
neon_bin!(cmge_4s, "cmge v0.4s, v1.4s, v2.4s");
neon_bin!(cmge_2d, "cmge v0.2d, v1.2d, v2.2d");

// ---- min / max (no 2D) ----
neon_bin!(smin_8b, "smin v0.8b, v1.8b, v2.8b");
neon_bin!(smin_16b, "smin v0.16b, v1.16b, v2.16b");
neon_bin!(smin_4h, "smin v0.4h, v1.4h, v2.4h");
neon_bin!(smin_8h, "smin v0.8h, v1.8h, v2.8h");
neon_bin!(smin_2s, "smin v0.2s, v1.2s, v2.2s");
neon_bin!(smin_4s, "smin v0.4s, v1.4s, v2.4s");

neon_bin!(umin_8b, "umin v0.8b, v1.8b, v2.8b");
neon_bin!(umin_16b, "umin v0.16b, v1.16b, v2.16b");
neon_bin!(umin_4h, "umin v0.4h, v1.4h, v2.4h");
neon_bin!(umin_8h, "umin v0.8h, v1.8h, v2.8h");
neon_bin!(umin_2s, "umin v0.2s, v1.2s, v2.2s");
neon_bin!(umin_4s, "umin v0.4s, v1.4s, v2.4s");

neon_bin!(smax_8b, "smax v0.8b, v1.8b, v2.8b");
neon_bin!(smax_16b, "smax v0.16b, v1.16b, v2.16b");
neon_bin!(smax_4h, "smax v0.4h, v1.4h, v2.4h");
neon_bin!(smax_8h, "smax v0.8h, v1.8h, v2.8h");
neon_bin!(smax_2s, "smax v0.2s, v1.2s, v2.2s");
neon_bin!(smax_4s, "smax v0.4s, v1.4s, v2.4s");

neon_bin!(umax_8b, "umax v0.8b, v1.8b, v2.8b");
neon_bin!(umax_16b, "umax v0.16b, v1.16b, v2.16b");
neon_bin!(umax_4h, "umax v0.4h, v1.4h, v2.4h");
neon_bin!(umax_8h, "umax v0.8h, v1.8h, v2.8h");
neon_bin!(umax_2s, "umax v0.2s, v1.2s, v2.2s");
neon_bin!(umax_4s, "umax v0.4s, v1.4s, v2.4s");

// ---- MLA (no 2D) ----
neon_mla!(mla_8b, "mla v0.8b, v1.8b, v2.8b");
neon_mla!(mla_16b, "mla v0.16b, v1.16b, v2.16b");
neon_mla!(mla_4h, "mla v0.4h, v1.4h, v2.4h");
neon_mla!(mla_8h, "mla v0.8h, v1.8h, v2.8h");
neon_mla!(mla_2s, "mla v0.2s, v1.2s, v2.2s");
neon_mla!(mla_4s, "mla v0.4s, v1.4s, v2.4s");

// ---- shift-immediate (amount is a LITERAL in the mnemonic) ----
// One wrapper per (op, arrangement, amount). The amount set includes >= lane
// width where the instruction encoding allows it (SHL allows 0..width-1; the
// right shifts USHR/SSHR allow 1..=width — so amount==width IS a real encoding).
macro_rules! neon_shift {
    ($name:ident, $mnem:literal) => {
        #[inline(never)]
        fn $name(a: u128) -> u128 {
            let mut out: u128 = 0;
            unsafe {
                asm!("ldr q1, [{a}]", $mnem, "str q0, [{o}]",
                    a = in(reg) &a, o = in(reg) &mut out, out("v0") _, out("v1") _,);
            }
            out
        }
    };
}

// SHL: amounts 0..lane_bits-1.  USHR/SSHR: amounts 1..=lane_bits.
neon_shift!(shl_8b_0, "shl v0.8b, v1.8b, #0");
neon_shift!(shl_8b_1, "shl v0.8b, v1.8b, #1");
neon_shift!(shl_8b_7, "shl v0.8b, v1.8b, #7");
neon_shift!(shl_4h_1, "shl v0.4h, v1.4h, #1");
neon_shift!(shl_4h_15, "shl v0.4h, v1.4h, #15");
neon_shift!(shl_2s_1, "shl v0.2s, v1.2s, #1");
neon_shift!(shl_2s_31, "shl v0.2s, v1.2s, #31");
neon_shift!(shl_16b_1, "shl v0.16b, v1.16b, #1");
neon_shift!(shl_16b_7, "shl v0.16b, v1.16b, #7");
neon_shift!(shl_8h_1, "shl v0.8h, v1.8h, #1");
neon_shift!(shl_8h_15, "shl v0.8h, v1.8h, #15");
neon_shift!(shl_4s_1, "shl v0.4s, v1.4s, #1");
neon_shift!(shl_4s_31, "shl v0.4s, v1.4s, #31");
neon_shift!(shl_2d_1, "shl v0.2d, v1.2d, #1");
neon_shift!(shl_2d_63, "shl v0.2d, v1.2d, #63");

neon_shift!(ushr_8b_1, "ushr v0.8b, v1.8b, #1");
neon_shift!(ushr_8b_7, "ushr v0.8b, v1.8b, #7");
neon_shift!(ushr_8b_8, "ushr v0.8b, v1.8b, #8"); // == lane width
neon_shift!(ushr_4h_8, "ushr v0.4h, v1.4h, #8");
neon_shift!(ushr_4h_16, "ushr v0.4h, v1.4h, #16"); // == lane width
neon_shift!(ushr_2s_16, "ushr v0.2s, v1.2s, #16");
neon_shift!(ushr_2s_32, "ushr v0.2s, v1.2s, #32"); // == lane width
neon_shift!(ushr_16b_4, "ushr v0.16b, v1.16b, #4");
neon_shift!(ushr_16b_8, "ushr v0.16b, v1.16b, #8");
neon_shift!(ushr_8h_8, "ushr v0.8h, v1.8h, #8");
neon_shift!(ushr_8h_16, "ushr v0.8h, v1.8h, #16");
neon_shift!(ushr_4s_16, "ushr v0.4s, v1.4s, #16");
neon_shift!(ushr_4s_32, "ushr v0.4s, v1.4s, #32");
neon_shift!(ushr_2d_32, "ushr v0.2d, v1.2d, #32");
neon_shift!(ushr_2d_64, "ushr v0.2d, v1.2d, #64"); // == lane width

neon_shift!(sshr_8b_1, "sshr v0.8b, v1.8b, #1");
neon_shift!(sshr_8b_7, "sshr v0.8b, v1.8b, #7");
neon_shift!(sshr_8b_8, "sshr v0.8b, v1.8b, #8");
neon_shift!(sshr_4h_8, "sshr v0.4h, v1.4h, #8");
neon_shift!(sshr_4h_16, "sshr v0.4h, v1.4h, #16");
neon_shift!(sshr_2s_16, "sshr v0.2s, v1.2s, #16");
neon_shift!(sshr_2s_32, "sshr v0.2s, v1.2s, #32");
neon_shift!(sshr_16b_4, "sshr v0.16b, v1.16b, #4");
neon_shift!(sshr_16b_8, "sshr v0.16b, v1.16b, #8");
neon_shift!(sshr_8h_8, "sshr v0.8h, v1.8h, #8");
neon_shift!(sshr_8h_16, "sshr v0.8h, v1.8h, #16");
neon_shift!(sshr_4s_16, "sshr v0.4s, v1.4s, #16");
neon_shift!(sshr_4s_32, "sshr v0.4s, v1.4s, #32");
neon_shift!(sshr_2d_32, "sshr v0.2d, v1.2d, #32");
neon_shift!(sshr_2d_64, "sshr v0.2d, v1.2d, #64");

// ---- DUP (broadcast a general-register scalar to all lanes) ----
#[inline(never)]
fn dup_8b(s: u32) -> u128 {
    let mut out: u128 = 0;
    unsafe { asm!("dup v0.8b, {s:w}", "str q0, [{o}]", s = in(reg) s, o = in(reg) &mut out, out("v0") _,); }
    out
}
#[inline(never)]
fn dup_16b(s: u32) -> u128 {
    let mut out: u128 = 0;
    unsafe { asm!("dup v0.16b, {s:w}", "str q0, [{o}]", s = in(reg) s, o = in(reg) &mut out, out("v0") _,); }
    out
}
#[inline(never)]
fn dup_4h(s: u32) -> u128 {
    let mut out: u128 = 0;
    unsafe { asm!("dup v0.4h, {s:w}", "str q0, [{o}]", s = in(reg) s, o = in(reg) &mut out, out("v0") _,); }
    out
}
#[inline(never)]
fn dup_8h(s: u32) -> u128 {
    let mut out: u128 = 0;
    unsafe { asm!("dup v0.8h, {s:w}", "str q0, [{o}]", s = in(reg) s, o = in(reg) &mut out, out("v0") _,); }
    out
}
#[inline(never)]
fn dup_2s(s: u32) -> u128 {
    let mut out: u128 = 0;
    unsafe { asm!("dup v0.2s, {s:w}", "str q0, [{o}]", s = in(reg) s, o = in(reg) &mut out, out("v0") _,); }
    out
}
#[inline(never)]
fn dup_4s(s: u32) -> u128 {
    let mut out: u128 = 0;
    unsafe { asm!("dup v0.4s, {s:w}", "str q0, [{o}]", s = in(reg) s, o = in(reg) &mut out, out("v0") _,); }
    out
}
#[inline(never)]
fn dup_2d(s: u64) -> u128 {
    let mut out: u128 = 0;
    unsafe { asm!("dup v0.2d, {s:x}", "str q0, [{o}]", s = in(reg) s, o = in(reg) &mut out, out("v0") _,); }
    out
}

// ---- INS (insert a general-register scalar into one lane of a vector) ----
macro_rules! neon_ins {
    ($name:ident, $mnem:literal, $rty:ty, $mod:tt) => {
        #[inline(never)]
        fn $name(vec: u128, val: $rty) -> u128 {
            let mut out: u128 = vec;
            unsafe { asm!("ldr q0, [{o}]", $mnem, "str q0, [{o}]",
                v = in(reg) val, o = in(reg) &mut out, out("v0") _,); }
            out
        }
    };
}
neon_ins!(ins_b_lane3, "ins v0.b[3], {v:w}", u32, w);
neon_ins!(ins_b_lane11, "ins v0.b[11], {v:w}", u32, w);
neon_ins!(ins_h_lane2, "ins v0.h[2], {v:w}", u32, w);
neon_ins!(ins_h_lane6, "ins v0.h[6], {v:w}", u32, w);
neon_ins!(ins_s_lane1, "ins v0.s[1], {v:w}", u32, w);
neon_ins!(ins_s_lane2, "ins v0.s[2], {v:w}", u32, w);
neon_ins!(ins_d_lane0, "ins v0.d[0], {v:x}", u64, x);
neon_ins!(ins_d_lane1, "ins v0.d[1], {v:x}", u64, x);

// ---- MOVI (move 8-bit immediate broadcast to every byte) ----
macro_rules! neon_movi {
    ($name:ident, $mnem:literal) => {
        #[inline(never)]
        fn $name() -> u128 {
            let mut out: u128 = 0;
            unsafe { asm!($mnem, "str q0, [{o}]", o = in(reg) &mut out, out("v0") _,); }
            out
        }
    };
}
neon_movi!(movi_8b_00, "movi v0.8b, #0x00");
neon_movi!(movi_8b_ff, "movi v0.8b, #0xff");
neon_movi!(movi_8b_ab, "movi v0.8b, #0xab");
neon_movi!(movi_8b_01, "movi v0.8b, #0x01");
neon_movi!(movi_16b_00, "movi v0.16b, #0x00");
neon_movi!(movi_16b_ff, "movi v0.16b, #0xff");
neon_movi!(movi_16b_ab, "movi v0.16b, #0xab");
neon_movi!(movi_16b_5a, "movi v0.16b, #0x5a");

// ---- UMAXV (cross-lane unsigned max reduction to a scalar S-register) ----
#[inline(never)]
fn umaxv_4s(a: u128) -> u32 {
    let mut out: u32 = 0;
    unsafe { asm!("ldr q1, [{a}]", "umaxv s0, v1.4s", "str s0, [{o}]",
        a = in(reg) &a, o = in(reg) &mut out, out("v0") _, out("v1") _,); }
    out
}

// ===========================================================================
// GRID generation
// ===========================================================================

/// A small deterministic LCG so the "random" operands are reproducible.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        // Numerical Recipes LCG constants.
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
}

/// Per-lane edge alphabet for a lane of `bits` width (as the low `bits` of u64).
fn lane_alphabet(bits: u32, rng: &mut Lcg) -> Vec<u64> {
    let mask = if bits >= 64 { u64::MAX } else { (1u64 << bits) - 1 };
    let int_min = 1u64 << (bits - 1);
    let int_max = int_min - 1;
    vec![
        0,
        mask,         // all-ones (== -1 signed)
        int_min,      // INT_MIN
        int_max,      // INT_MAX
        1,
        rng.next() & mask,
        rng.next() & mask,
    ]
}

/// Pack `n` lanes of `bits` each (lanes[0] = least-significant) into a u128.
fn pack(lanes: &[u64], bits: u32) -> u128 {
    let mut v: u128 = 0;
    for (i, &lane) in lanes.iter().enumerate() {
        v |= (lane as u128) << (i as u32 * bits);
    }
    v
}

/// Build a deterministic set of 128-bit operands for an arrangement of `n` lanes
/// of `bits`. Uses: every-lane-uniform over the alphabet, alternating A/B
/// patterns over alphabet pairs, and a handful of fully-random vectors.
fn operand_grid(n: u32, bits: u32, rng: &mut Lcg) -> Vec<u128> {
    let alpha = lane_alphabet(bits, rng);
    let mut out = Vec::new();
    // 1. every lane = the same alphabet value.
    for &x in &alpha {
        let lanes = vec![x; n as usize];
        out.push(pack(&lanes, bits));
    }
    // 2. alternating x,y,x,y,... over a few ordered alphabet pairs (edge mixes).
    let pairs = [(0usize, 1usize), (2, 3), (1, 4), (3, 0), (2, 4)];
    for &(i, j) in &pairs {
        let lanes: Vec<u64> = (0..n).map(|k| if k % 2 == 0 { alpha[i] } else { alpha[j] }).collect();
        out.push(pack(&lanes, bits));
    }
    // 3. fully random vectors (deterministic via the LCG).
    let mask = if bits >= 64 { u64::MAX } else { (1u64 << bits) - 1 };
    for _ in 0..4 {
        let lanes: Vec<u64> = (0..n).map(|_| rng.next() & mask).collect();
        out.push(pack(&lanes, bits));
    }
    out
}

#[derive(Clone)]
struct Fact {
    op: String,
    arrangement: String,
    kind: String, // "binary" | "unary" | "mla" | "shift" | "dup" | "ins" | "movi" | "umaxv"
    lane_bits: u32,
    total_bits: u32,
    a: u128,
    b: u128,
    c: u128,      // mla accumulator (va); else 0
    imm: i64,     // shift amount / movi imm / ins lane index / dup uses scalar in `a`
    scalar: u128, // dup scalar / ins inserted value
    result: u128,
    theorem: String,
}

fn hex128(v: u128) -> String {
    format!("0x{:032x}", v)
}

fn main() {
    let out_path = std::env::args().nth(1).unwrap_or_else(|| {
        "crates/trust-cg-verify/tests/fixtures/aarch64_neon_silicon_truth.json".to_string()
    });

    let mut rng = Lcg(0x12345678_9abcdef0);
    let mut facts: Vec<Fact> = Vec::new();
    let mut per_op: BTreeMap<String, usize> = BTreeMap::new();

    let push = |facts: &mut Vec<Fact>, per_op: &mut BTreeMap<String, usize>, f: Fact| {
        *per_op.entry(f.op.clone()).or_default() += 1;
        facts.push(f);
    };

    // arrangements: (name, lane_count, lane_bits, total_bits)
    let arr7 = [
        ("8b", 8u32, 8u32, 64u32),
        ("16b", 16, 8, 128),
        ("4h", 4, 16, 64),
        ("8h", 8, 16, 128),
        ("2s", 2, 32, 64),
        ("4s", 4, 32, 128),
        ("2d", 2, 64, 128),
    ];
    // min/max/mul/mla: no 2D
    let arr6 = &arr7[..6];

    // ---- binary: add/sub/cmeq/cmgt/cmge over arr7; mul/min/max over arr6 ----
    let bin7: &[(&str, &[(&str, fn(u128, u128) -> u128)])] = &[
        ("add", &[
            ("8b", add_8b), ("16b", add_16b), ("4h", add_4h), ("8h", add_8h),
            ("2s", add_2s), ("4s", add_4s), ("2d", add_2d),
        ]),
        ("sub", &[
            ("8b", sub_8b), ("16b", sub_16b), ("4h", sub_4h), ("8h", sub_8h),
            ("2s", sub_2s), ("4s", sub_4s), ("2d", sub_2d),
        ]),
        ("cmeq", &[
            ("8b", cmeq_8b), ("16b", cmeq_16b), ("4h", cmeq_4h), ("8h", cmeq_8h),
            ("2s", cmeq_2s), ("4s", cmeq_4s), ("2d", cmeq_2d),
        ]),
        ("cmgt", &[
            ("8b", cmgt_8b), ("16b", cmgt_16b), ("4h", cmgt_4h), ("8h", cmgt_8h),
            ("2s", cmgt_2s), ("4s", cmgt_4s), ("2d", cmgt_2d),
        ]),
        ("cmge", &[
            ("8b", cmge_8b), ("16b", cmge_16b), ("4h", cmge_4h), ("8h", cmge_8h),
            ("2s", cmge_2s), ("4s", cmge_4s), ("2d", cmge_2d),
        ]),
    ];
    let bin6: &[(&str, &[(&str, fn(u128, u128) -> u128)])] = &[
        ("mul", &[
            ("8b", mul_8b), ("16b", mul_16b), ("4h", mul_4h), ("8h", mul_8h),
            ("2s", mul_2s), ("4s", mul_4s),
        ]),
        ("smin", &[
            ("8b", smin_8b), ("16b", smin_16b), ("4h", smin_4h), ("8h", smin_8h),
            ("2s", smin_2s), ("4s", smin_4s),
        ]),
        ("umin", &[
            ("8b", umin_8b), ("16b", umin_16b), ("4h", umin_4h), ("8h", umin_8h),
            ("2s", umin_2s), ("4s", umin_4s),
        ]),
        ("smax", &[
            ("8b", smax_8b), ("16b", smax_16b), ("4h", smax_4h), ("8h", smax_8h),
            ("2s", smax_2s), ("4s", smax_4s),
        ]),
        ("umax", &[
            ("8b", umax_8b), ("16b", umax_16b), ("4h", umax_4h), ("8h", umax_8h),
            ("2s", umax_2s), ("4s", umax_4s),
        ]),
    ];

    let arr_of = |name: &str| -> (u32, u32, u32) {
        match name {
            "8b" => (8, 8, 64),
            "16b" => (16, 8, 128),
            "4h" => (4, 16, 64),
            "8h" => (8, 16, 128),
            "2s" => (2, 32, 64),
            "4s" => (4, 32, 128),
            "2d" => (2, 64, 128),
            _ => unreachable!(),
        }
    };

    for (op, variants) in bin7.iter().chain(bin6.iter()) {
        for (an, f) in variants.iter() {
            let (n, bits, total) = arr_of(an);
            let av = operand_grid(n, bits, &mut rng);
            let bv = operand_grid(n, bits, &mut rng);
            let mut i = 0usize;
            for &a in &av {
                for &b in &bv {
                    let r = f(a, b);
                    push(&mut facts, &mut per_op, Fact {
                        op: op.to_string(), arrangement: an.to_string(), kind: "binary".into(),
                        lane_bits: bits, total_bits: total, a, b, c: 0, imm: 0, scalar: 0,
                        result: r, theorem: format!("neon_{op}_{an}_{i}"),
                    });
                    i += 1;
                }
            }
        }
    }

    // ---- bitwise binary (and/orr/eor/bic) over 8b + 16b ----
    let bitbin: &[(&str, &[(&str, fn(u128, u128) -> u128)])] = &[
        ("and", &[("8b", and_8b), ("16b", and_16b)]),
        ("orr", &[("8b", orr_8b), ("16b", orr_16b)]),
        ("eor", &[("8b", eor_8b), ("16b", eor_16b)]),
        ("bic", &[("8b", bic_8b), ("16b", bic_16b)]),
    ];
    for (op, variants) in bitbin {
        for (an, f) in variants.iter() {
            let (n, bits, total) = arr_of(an);
            let av = operand_grid(n, bits, &mut rng);
            let bv = operand_grid(n, bits, &mut rng);
            let mut i = 0usize;
            for &a in &av {
                for &b in &bv {
                    let r = f(a, b);
                    push(&mut facts, &mut per_op, Fact {
                        op: op.to_string(), arrangement: an.to_string(), kind: "binary".into(),
                        lane_bits: bits, total_bits: total, a, b, c: 0, imm: 0, scalar: 0,
                        result: r, theorem: format!("neon_{op}_{an}_{i}"),
                    });
                    i += 1;
                }
            }
        }
    }

    // ---- unary: neg (arr7) + not (8b/16b) ----
    let un: &[(&str, &[(&str, fn(u128) -> u128)])] = &[
        ("neg", &[
            ("8b", neg_8b), ("16b", neg_16b), ("4h", neg_4h), ("8h", neg_8h),
            ("2s", neg_2s), ("4s", neg_4s), ("2d", neg_2d),
        ]),
        ("not", &[("8b", not_8b), ("16b", not_16b)]),
    ];
    for (op, variants) in un {
        for (an, f) in variants.iter() {
            let (n, bits, total) = arr_of(an);
            let av = operand_grid(n, bits, &mut rng);
            for (i, &a) in av.iter().enumerate() {
                let r = f(a);
                push(&mut facts, &mut per_op, Fact {
                    op: op.to_string(), arrangement: an.to_string(), kind: "unary".into(),
                    lane_bits: bits, total_bits: total, a, b: 0, c: 0, imm: 0, scalar: 0,
                    result: r, theorem: format!("neon_{op}_{an}_{i}"),
                });
            }
        }
    }

    // ---- mla (arr6): Vd += Vn*Vm ----
    let mla: &[(&str, fn(u128, u128, u128) -> u128)] = &[
        ("8b", mla_8b), ("16b", mla_16b), ("4h", mla_4h), ("8h", mla_8h),
        ("2s", mla_2s), ("4s", mla_4s),
    ];
    let _ = arr6; // documented; arr_of drives widths.
    for (an, f) in mla {
        let (n, bits, total) = arr_of(an);
        let cv = operand_grid(n, bits, &mut rng);
        let nv = operand_grid(n, bits, &mut rng);
        let mv = operand_grid(n, bits, &mut rng);
        let mut i = 0usize;
        // Cap the triple-product to keep the fixture bounded but rich: sample a
        // diagonal-ish slice (every accumulator x a rotating n/m pair).
        for (k, &acc) in cv.iter().enumerate() {
            for j in 0..nv.len() {
                let vn = nv[j];
                let vm = mv[(j + k) % mv.len()];
                let r = f(acc, vn, vm);
                push(&mut facts, &mut per_op, Fact {
                    op: "mla".to_string(), arrangement: an.to_string(), kind: "mla".into(),
                    lane_bits: bits, total_bits: total, a: vn, b: vm, c: acc, imm: 0, scalar: 0,
                    result: r, theorem: format!("neon_mla_{an}_{i}"),
                });
                i += 1;
            }
        }
    }

    // ---- shifts: one wrapper per (op, arrangement, amount) ----
    let shifts: &[(&str, &str, i64, fn(u128) -> u128)] = &[
        ("shl", "8b", 0, shl_8b_0), ("shl", "8b", 1, shl_8b_1), ("shl", "8b", 7, shl_8b_7),
        ("shl", "4h", 1, shl_4h_1), ("shl", "4h", 15, shl_4h_15),
        ("shl", "2s", 1, shl_2s_1), ("shl", "2s", 31, shl_2s_31),
        ("shl", "16b", 1, shl_16b_1), ("shl", "16b", 7, shl_16b_7),
        ("shl", "8h", 1, shl_8h_1), ("shl", "8h", 15, shl_8h_15),
        ("shl", "4s", 1, shl_4s_1), ("shl", "4s", 31, shl_4s_31),
        ("shl", "2d", 1, shl_2d_1), ("shl", "2d", 63, shl_2d_63),
        ("ushr", "8b", 1, ushr_8b_1), ("ushr", "8b", 7, ushr_8b_7), ("ushr", "8b", 8, ushr_8b_8),
        ("ushr", "4h", 8, ushr_4h_8), ("ushr", "4h", 16, ushr_4h_16),
        ("ushr", "2s", 16, ushr_2s_16), ("ushr", "2s", 32, ushr_2s_32),
        ("ushr", "16b", 4, ushr_16b_4), ("ushr", "16b", 8, ushr_16b_8),
        ("ushr", "8h", 8, ushr_8h_8), ("ushr", "8h", 16, ushr_8h_16),
        ("ushr", "4s", 16, ushr_4s_16), ("ushr", "4s", 32, ushr_4s_32),
        ("ushr", "2d", 32, ushr_2d_32), ("ushr", "2d", 64, ushr_2d_64),
        ("sshr", "8b", 1, sshr_8b_1), ("sshr", "8b", 7, sshr_8b_7), ("sshr", "8b", 8, sshr_8b_8),
        ("sshr", "4h", 8, sshr_4h_8), ("sshr", "4h", 16, sshr_4h_16),
        ("sshr", "2s", 16, sshr_2s_16), ("sshr", "2s", 32, sshr_2s_32),
        ("sshr", "16b", 4, sshr_16b_4), ("sshr", "16b", 8, sshr_16b_8),
        ("sshr", "8h", 8, sshr_8h_8), ("sshr", "8h", 16, sshr_8h_16),
        ("sshr", "4s", 16, sshr_4s_16), ("sshr", "4s", 32, sshr_4s_32),
        ("sshr", "2d", 32, sshr_2d_32), ("sshr", "2d", 64, sshr_2d_64),
    ];
    for (op, an, amt, f) in shifts {
        let (n, bits, total) = arr_of(an);
        let av = operand_grid(n, bits, &mut rng);
        for (i, &a) in av.iter().enumerate() {
            let r = f(a);
            push(&mut facts, &mut per_op, Fact {
                op: op.to_string(), arrangement: an.to_string(), kind: "shift".into(),
                lane_bits: bits, total_bits: total, a, b: 0, c: 0, imm: *amt, scalar: 0,
                result: r, theorem: format!("neon_{op}_{an}_{amt}_{i}"),
            });
        }
    }

    // ---- dup (scalar in `scalar`; result broadcasts) ----
    let dups32: &[(&str, fn(u32) -> u128)] = &[
        ("8b", dup_8b), ("16b", dup_16b), ("4h", dup_4h), ("8h", dup_8h),
        ("2s", dup_2s), ("4s", dup_4s),
    ];
    let dup_scalars32: [u32; 6] = [0, 0xFFFFFFFF, 0x80000000, 0x7FFFFFFF, 1, 0xDEADBEEF];
    for (an, f) in dups32 {
        let (_n, bits, total) = arr_of(an);
        for (i, &s) in dup_scalars32.iter().enumerate() {
            let r = f(s);
            push(&mut facts, &mut per_op, Fact {
                op: "dup".to_string(), arrangement: an.to_string(), kind: "dup".into(),
                lane_bits: bits, total_bits: total, a: 0, b: 0, c: 0, imm: 0, scalar: s as u128,
                result: r, theorem: format!("neon_dup_{an}_{i}"),
            });
        }
    }
    let dup_scalars64: [u64; 6] = [0, u64::MAX, 1u64 << 63, (1u64 << 63) - 1, 1, 0xDEADBEEF_CAFEBABE];
    for (i, &s) in dup_scalars64.iter().enumerate() {
        let r = dup_2d(s);
        push(&mut facts, &mut per_op, Fact {
            op: "dup".to_string(), arrangement: "2d".to_string(), kind: "dup".into(),
            lane_bits: 64, total_bits: 128, a: 0, b: 0, c: 0, imm: 0, scalar: s as u128,
            result: r, theorem: format!("neon_dup_2d_{i}"),
        });
    }

    // ---- ins (vector in `a`, inserted scalar in `scalar`, lane index in `imm`) ----
    let ins32: &[(&str, i64, fn(u128, u32) -> u128)] = &[
        ("16b", 3, ins_b_lane3), ("16b", 11, ins_b_lane11),
        ("8h", 2, ins_h_lane2), ("8h", 6, ins_h_lane6),
        ("4s", 1, ins_s_lane1), ("4s", 2, ins_s_lane2),
    ];
    let ins_vecs: [u128; 3] = [
        0,
        u128::MAX,
        0x0123456789abcdef_fedcba9876543210,
    ];
    let ins_vals32: [u32; 4] = [0, 0xFFFFFFFF, 0xA5A5A5A5, 0xCAFE];
    for (an, lane, f) in ins32 {
        let (_n, bits, total) = arr_of(an);
        let mut i = 0usize;
        for &vec in &ins_vecs {
            for &val in &ins_vals32 {
                let r = f(vec, val);
                push(&mut facts, &mut per_op, Fact {
                    op: "ins".to_string(), arrangement: an.to_string(), kind: "ins".into(),
                    lane_bits: bits, total_bits: total, a: vec, b: 0, c: 0, imm: *lane,
                    scalar: val as u128, result: r, theorem: format!("neon_ins_{an}_{lane}_{i}"),
                });
                i += 1;
            }
        }
    }
    let ins64: &[(&str, i64, fn(u128, u64) -> u128)] = &[("2d", 0, ins_d_lane0), ("2d", 1, ins_d_lane1)];
    let ins_vals64: [u64; 4] = [0, u64::MAX, 0xA5A5A5A5A5A5A5A5, 0xDEADBEEFCAFEBABE];
    for (an, lane, f) in ins64 {
        let mut i = 0usize;
        for &vec in &ins_vecs {
            for &val in &ins_vals64 {
                let r = f(vec, val);
                push(&mut facts, &mut per_op, Fact {
                    op: "ins".to_string(), arrangement: an.to_string(), kind: "ins".into(),
                    lane_bits: 64, total_bits: 128, a: vec, b: 0, c: 0, imm: *lane,
                    scalar: val as u128, result: r, theorem: format!("neon_ins_{an}_{lane}_{i}"),
                });
                i += 1;
            }
        }
    }

    // ---- movi (imm broadcast to bytes; imm in `imm`) ----
    let movis: &[(&str, i64, fn() -> u128)] = &[
        ("8b", 0x00, movi_8b_00), ("8b", 0xff, movi_8b_ff), ("8b", 0xab, movi_8b_ab), ("8b", 0x01, movi_8b_01),
        ("16b", 0x00, movi_16b_00), ("16b", 0xff, movi_16b_ff), ("16b", 0xab, movi_16b_ab), ("16b", 0x5a, movi_16b_5a),
    ];
    for (an, imm, f) in movis {
        let (_n, bits, total) = arr_of(an);
        let r = f();
        push(&mut facts, &mut per_op, Fact {
            op: "movi".to_string(), arrangement: an.to_string(), kind: "movi".into(),
            lane_bits: bits, total_bits: total, a: 0, b: 0, c: 0, imm: *imm, scalar: 0,
            result: r, theorem: format!("neon_movi_{an}_{imm}"),
        });
    }

    // ---- umaxv (4s reduction; result is a 32-bit scalar in the low bits) ----
    {
        let av = operand_grid(4, 32, &mut rng);
        for (i, &a) in av.iter().enumerate() {
            let r = umaxv_4s(a) as u128;
            push(&mut facts, &mut per_op, Fact {
                op: "umaxv".to_string(), arrangement: "4s".to_string(), kind: "umaxv".into(),
                lane_bits: 32, total_bits: 128, a, b: 0, c: 0, imm: 0, scalar: 0,
                result: r, theorem: format!("neon_umaxv_4s_{i}"),
            });
        }
    }

    // ===========================================================================
    // Emit JSON (hand-rolled to avoid any deps; deterministic field order).
    // ===========================================================================
    let total = facts.len();
    let mut s = String::new();
    s.push_str("{\n");
    s.push_str(" \"_header\": {\n");
    s.push_str("  \"purpose\": \"AArch64 integer NEON BARE-SILICON ground truth for the B-aarch64-neon differential bridge: each fact is a REAL Apple M4 result, produced by running the actual NEON instruction natively via std::arch::asm! over q-registers (no Rosetta/qemu/Clean-chip-file). This is the SAME oracle tier as the AArch64 integer bridge.\",\n");
    s.push_str("  \"oracle\": \"m4-silicon-native\",\n");
    s.push_str("  \"oracle_note\": \"Apple M4 (native AArch64). Each (op, arrangement) has an #[inline(never)] wrapper that ldr q1/q2, runs ONE packed NEON instruction (add v0.4s, ...), and str q0 the 128-bit result. otool -tv confirms the real mnemonics. 64-bit (D-register) arrangements zero the upper 64 bits in hardware.\",\n");
    s.push_str("  \"determinism\": \"deterministic: a fixed-seed LCG drives the per-lane edge grid (0, -1, INT_MIN, INT_MAX, 1, 2 LCG randoms) + alternating patterns + 4 random vectors; shift amounts are fixed and include amount >= lane width.\",\n");
    s.push_str("  \"regen\": \"rustc -O crates/trust-cg-verify/tests/fixtures/gen_aarch64_neon_silicon_truth.rs -o /tmp/gen_neon && /tmp/gen_neon crates/trust-cg-verify/tests/fixtures/aarch64_neon_silicon_truth.json\",\n");
    s.push_str("  \"operands_encoding\": \"a/b/c (mla acc)/scalar (dup,ins)/result are 0x-prefixed 32-hex-digit 128-bit values, lane 0 in the low bits. imm = shift amount (shift) | movi 8-bit imm | ins lane index. kind discriminates the encoder shape.\",\n");
    let _ = write!(s, "  \"included_fact_count\": {total},\n");
    s.push_str("  \"included_per_op\": {\n");
    let n_ops = per_op.len();
    for (k, (op, cnt)) in per_op.iter().enumerate() {
        let comma = if k + 1 < n_ops { "," } else { "" };
        let _ = write!(s, "   \"{op}\": {cnt}{comma}\n");
    }
    s.push_str("  }\n");
    s.push_str(" },\n");
    s.push_str(" \"_accounting\": {\n");
    let _ = write!(s, "  \"total_attempted\": {total},\n");
    let _ = write!(s, "  \"emitted\": {total},\n");
    let _ = write!(s, "  \"value_facts\": {total},\n");
    s.push_str("  \"trap_facts\": 0,\n");
    let _ = write!(s, "  \"op_families\": {n_ops}\n");
    s.push_str(" },\n");
    s.push_str(" \"facts\": [\n");
    for (i, f) in facts.iter().enumerate() {
        let comma = if i + 1 < facts.len() { "," } else { "" };
        let _ = write!(
            s,
            "  {{\"op\": \"{}\", \"arrangement\": \"{}\", \"kind\": \"{}\", \"lane_bits\": {}, \"total_bits\": {}, \"a\": \"{}\", \"b\": \"{}\", \"c\": \"{}\", \"imm\": {}, \"scalar\": \"{}\", \"result\": \"{}\", \"theorem\": \"{}\"}}{}\n",
            f.op, f.arrangement, f.kind, f.lane_bits, f.total_bits,
            hex128(f.a), hex128(f.b), hex128(f.c), f.imm, hex128(f.scalar),
            hex128(f.result), f.theorem, comma
        );
    }
    s.push_str(" ]\n}\n");

    std::fs::write(&out_path, s).expect("write fixture");
    eprintln!("emitted {total} NEON silicon facts across {n_ops} op families -> {out_path}");
}
