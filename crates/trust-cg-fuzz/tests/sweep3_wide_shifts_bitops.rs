// trust-cg-fuzz/tests/sweep3_wide_shifts_bitops.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sweep3 surface: "wide_shifts_bitops".
//
// FOCUS:
//   * i64/i32 shift by *register* amounts near the width boundary (masked).
//   * rotate idioms (rotl/rotr) synthesized from shift + shift + or.
//   * and / or / xor / bic (and-not) chains.
//   * ctpop, and clz synthesized from shifts/masks.
//   * bitfield insert / extract with register-controlled offsets.
//   * sign / zero extend ladders i8 <-> i16 <-> i32 <-> i64.
//
// ORACLE CHOICE.
//   The trust_cg interpreter is a *faithful* oracle for shifts/and/or/xor/ctpop
//   *as long as every operation is computed at the program's full i64 width*:
//     - shift amounts are reduced modulo the type width (interpreter
//       `shift_amount` = amount % width), which for the power-of-two widths
//       8/16/32/64 coincides exactly with the AArch64 "mask by width-1"
//       hardware rule, so register-amount shifts agree;
//     - and/or/xor/ctpop are width-precise.
//   The interpreter is NOT faithful for narrowing/extending casts: it models
//   Trunc/ZExt/SExt as i128 no-ops, and `Not`/`Neg` are computed on the full
//   i128 rather than at the declared width. Therefore:
//     - i64-width shift/bitop/ctpop tests use the interpreter oracle AND a
//       native-Rust ground truth AND cross-config JIT agreement;
//     - i32-width and any cast-ladder / synthesized-clz / bic(via Not) tests
//       drop the interpreter oracle and rely on native-Rust ground truth plus
//       cross-config JIT agreement (O0..O3 x fast/precise regalloc).
//
// Anti-false-positive discipline (per task):
//   * all arithmetic uses wrapping semantics;
//   * divisors never used here;
//   * register shift amounts are explicitly masked to a legal range before use
//     so behaviour is well-defined under BOTH the interpreter's modulo rule and
//     the hardware mask rule, and the native-Rust truth uses the same mask;
//   * float/exact-small: not used on this surface;
//   * no memory: every module is pure register dataflow.
//
// Every former defect reproducer remains an always-on regression test.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::run_oracle_one;
use trust_ir::{BinOp, CastOp, Ty, UnOp};
use trust_ir_build::ModuleBuilder;

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Compile `module` at `opt` with the chosen regalloc and JIT-run `fuzz_fn`.
fn jit(module: &trust_ir::Module, opt: OptLevel, fast: bool, row: [i64; 4]) -> Result<i64, String> {
    let externs: HashMap<String, *const u8> = HashMap::new();
    let mut cfg = if fast {
        CompilerConfig::jit_fast(Target::host())
    } else {
        let mut c = CompilerConfig::for_host_jit();
        c.enable_jit_fast_regalloc = false;
        c
    };
    cfg.opt_level = opt;
    let buf = Compiler::new(cfg)
        .compile_module_to_jit(module, &externs)
        .map_err(|e| format!("compile_err: {e:?}"))?
        .buffer;
    let f = unsafe { buf.get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>("fuzz_fn") }
        .ok_or_else(|| "symbol_not_found".to_string())?
        .into_inner();
    let v = f(row[0], row[1], row[2], row[3]);
    drop(buf);
    Ok(v)
}

/// Differential check.
///
/// `use_interp`: when true, also assert the trust_cg interpreter oracle agrees
/// (only valid for full-width-i64 modules — see the module header).
///
/// A DEFECT is any of: a native-truth mismatch, an interpreter-oracle mismatch,
/// a JIT-vs-JIT divergence across the 8 (opt x regalloc) configs, or a
/// compile-error / panic on an oracle-accepted module.
fn check<F>(label: &str, module: &trust_ir::Module, rows: &[[i64; 4]], use_interp: bool, truth: F)
where
    F: Fn([i64; 4]) -> i64,
{
    for &row in rows {
        let want = truth(row);

        // Oracle: only meaningful for full-width i64 programs.
        if use_interp {
            match run_oracle_one(module, &row) {
                Ok(o) => assert_eq!(
                    o, want,
                    "{label}: INTERP-ORACLE vs TRUTH MISMATCH row={row:?} interp={o} want={want}"
                ),
                Err(e) => panic!("{label}: oracle rejected accepted module row={row:?}: {e}"),
            }
        }

        let mut jit_vals: Vec<(OptLevel, bool, i64)> = Vec::new();
        for fast in [true, false] {
            for opt in OPTS {
                match jit(module, opt, fast, row) {
                    Ok(v) => jit_vals.push((opt, fast, v)),
                    Err(e) => panic!("{label}: row={row:?} opt={opt:?} fast={fast}: {e}"),
                }
            }
        }
        // Native ground truth vs every JIT config.
        for (opt, fast, got) in &jit_vals {
            assert_eq!(
                *got, want,
                "{label}: TRUTH MISMATCH row={row:?} opt={opt:?} fast={fast} got={got} want={want}"
            );
        }
        // Cross-config JIT agreement.
        if let Some((opt0, fast0, v0)) = jit_vals.first().copied() {
            for (opt, fast, got) in &jit_vals[1..] {
                assert_eq!(
                    *got, v0,
                    "{label}: JIT DIVERGENCE row={row:?} \
                     ({opt0:?},fast={fast0})={v0} vs ({opt:?},fast={fast})={got}"
                );
            }
        }
    }
}

/// `fuzz_fn(a,b,c,d): (i64,i64,i64,i64) -> i64`; `body` consumes the four i64
/// args and returns an i64 value.
fn build4<F>(name: &str, body: F) -> trust_ir::Module
where
    F: FnOnce(&mut trust_ir_build::FunctionBuilder, &[trust_ir::ValueId; 4]) -> trust_ir::ValueId,
{
    let mut mb = ModuleBuilder::new(name);
    let ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let r = body(&mut fb, &[a, b, c, d]);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

// Rows chosen to stress boundary shift amounts (0, width-1, width, width+1),
// sign bits, alternating bit patterns, and both halves of the word.
const ROWS: &[[i64; 4]] = &[
    [0, 0, 0, 0],
    [1, 1, 1, 1],
    [-1, -1, -1, -1],
    [i64::MAX, i64::MIN, 1, -1],
    [i64::MIN, i64::MAX, -1, 1],
    [0x5555_5555_5555_5555, 0xaaaa_aaaa_aaaa_aaaau64 as i64, 0, 0],
    [
        0x0123_4567_89ab_cdef,
        0xfedc_ba98_7654_3210u64 as i64,
        7,
        13,
    ],
    [
        0xdead_beef_dead_beefu64 as i64,
        0xcafe_babe_cafe_babeu64 as i64,
        31,
        32,
    ],
    [
        0x0000_0000_ffff_ffff,
        0xffff_ffff_0000_0000u64 as i64,
        33,
        63,
    ],
    [
        0x8000_0000_0000_0000u64 as i64,
        0x7fff_ffff_ffff_ffff,
        63,
        64,
    ],
    [
        0x0000_0000_ffff_ffff,
        0xffff_ffff_0000_0000u64 as i64,
        1,
        62,
    ],
    [42, -42, 64, 65],
    [
        0x00ff_00ff_00ff_00ff,
        0xff00_ff00_ff00_ff00u64 as i64,
        95,
        96,
    ],
    [-256, 256, 127, 128],
];

// ===========================================================================
// 1. i64 shifts by register amounts near the width boundary (masked).
// ===========================================================================

#[test]
fn shl_i64_reg_masked() {
    // r = a << (c & 63)
    let m = build4("shl64_reg", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let amt = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        fb.binop(BinOp::Shl, Ty::I64, x[0], amt)
    });
    check("shl_i64_reg_masked", &m, ROWS, true, |row| {
        (row[0] as u64).wrapping_shl((row[2] as u64 & 63) as u32) as i64
    });
}

#[test]
fn lshr_i64_reg_masked() {
    // r = (u64)a >> (c & 63)
    let m = build4("lshr64_reg", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let amt = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        fb.binop(BinOp::LShr, Ty::I64, x[0], amt)
    });
    check("lshr_i64_reg_masked", &m, ROWS, true, |row| {
        ((row[0] as u64) >> (row[2] as u64 & 63)) as i64
    });
}

#[test]
fn ashr_i64_reg_masked() {
    // r = (i64)a >> (c & 63)  (arithmetic)
    let m = build4("ashr64_reg", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let amt = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        fb.binop(BinOp::AShr, Ty::I64, x[0], amt)
    });
    check("ashr_i64_reg_masked", &m, ROWS, true, |row| {
        row[0] >> (row[2] as u64 & 63)
    });
}

#[test]
fn shl_i64_by_full_unmasked_register() {
    // r = a << c  where c ranges over {63,64,65,95,96,127,128,...}.
    // BOTH the interpreter (amount % 64) and AArch64 (amount & 63) reduce the
    // amount the same way, so this is well-defined and oracle-faithful even
    // without an explicit mask. The native truth applies the same reduction.
    let m = build4("shl64_full", |fb, x| {
        fb.binop(BinOp::Shl, Ty::I64, x[0], x[2])
    });
    check("shl_i64_by_full_unmasked_register", &m, ROWS, true, |row| {
        (row[0] as u64).wrapping_shl((row[2] as u64 % 64) as u32) as i64
    });
}

#[test]
fn double_shift_chain_i64() {
    // r = ((a << (c&63)) >> (d&63))   logical-then-logical, both register amts
    let m = build4("dshift64", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let ca = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        let da = fb.binop(BinOp::And, Ty::I64, x[3], m63);
        let l = fb.binop(BinOp::Shl, Ty::I64, x[0], ca);
        fb.binop(BinOp::LShr, Ty::I64, l, da)
    });
    check("double_shift_chain_i64", &m, ROWS, true, |row| {
        let l = (row[0] as u64).wrapping_shl((row[2] as u64 & 63) as u32);
        (l >> (row[3] as u64 & 63)) as i64
    });
}

// ===========================================================================
// 2. Rotate idioms (rotl / rotr) synthesized from shift + shift + or.
//    Use a masked, NON-ZERO shaped amount so the complementary shift is also
//    in-range under the interpreter's modulo rule:
//      rotl(a, s) = (a << s) | (a >> ((64 - s) & 63))
//    For s in 0..64, (64 - s) & 63 == (-s) & 63 == the correct complement,
//    and at s==0 both complement and result are well-defined (a >> 0 == a, the
//    high term is a<<0; OR gives a). This matches u64::rotate_left exactly.
// ===========================================================================

#[test]
fn rotl_i64_reg() {
    let m = build4("rotl64", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let s = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        let lo = fb.binop(BinOp::Shl, Ty::I64, x[0], s);
        // comp = (64 - s) & 63 == (-s) & 63
        let zero = fb.iconst(Ty::I64, 0);
        let neg = fb.binop(BinOp::Sub, Ty::I64, zero, s);
        let comp = fb.binop(BinOp::And, Ty::I64, neg, m63);
        let hi = fb.binop(BinOp::LShr, Ty::I64, x[0], comp);
        fb.binop(BinOp::Or, Ty::I64, lo, hi)
    });
    check("rotl_i64_reg", &m, ROWS, true, |row| {
        (row[0] as u64).rotate_left((row[2] as u64 & 63) as u32) as i64
    });
}

#[test]
fn rotr_i64_reg() {
    let m = build4("rotr64", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let s = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        let lo = fb.binop(BinOp::LShr, Ty::I64, x[0], s);
        let zero = fb.iconst(Ty::I64, 0);
        let neg = fb.binop(BinOp::Sub, Ty::I64, zero, s);
        let comp = fb.binop(BinOp::And, Ty::I64, neg, m63);
        let hi = fb.binop(BinOp::Shl, Ty::I64, x[0], comp);
        fb.binop(BinOp::Or, Ty::I64, lo, hi)
    });
    check("rotr_i64_reg", &m, ROWS, true, |row| {
        (row[0] as u64).rotate_right((row[2] as u64 & 63) as u32) as i64
    });
}

#[test]
fn rotl_i32_reg() {
    // 32-bit rotate, computed entirely in i32, then zero-extended to i64.
    // Interpreter cannot model the i32 width faithfully (cast no-op + i128
    // upper bits), so: native truth + cross-config JIT agreement only.
    let m = build4("rotl32", |fb, x| {
        let a32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[0]);
        let s_full = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[2]);
        let m31 = fb.iconst(Ty::I32, 31);
        let s = fb.binop(BinOp::And, Ty::I32, s_full, m31);
        let lo = fb.binop(BinOp::Shl, Ty::I32, a32, s);
        let zero = fb.iconst(Ty::I32, 0);
        let neg = fb.binop(BinOp::Sub, Ty::I32, zero, s);
        let comp = fb.binop(BinOp::And, Ty::I32, neg, m31);
        let hi = fb.binop(BinOp::LShr, Ty::I32, a32, comp);
        let r32 = fb.binop(BinOp::Or, Ty::I32, lo, hi);
        fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, r32)
    });
    check("rotl_i32_reg", &m, ROWS, false, |row| {
        let r = (row[0] as u32).rotate_left((row[2] as u32) & 31);
        r as u64 as i64
    });
}

// ===========================================================================
// 3. and / or / xor / bic (and-not) chains.
//    `bic(a,b) = a & ~b`.  `~b` synthesized via UnOp::Not. At full i64 width
//    Not is faithful in the interpreter (no narrowing), so use_interp=true.
// ===========================================================================

#[test]
fn andorxor_chain_i64() {
    // r = ((a & b) | (c ^ d)) ^ (a | d)
    let m = build4("aox64", |fb, x| {
        let ab = fb.binop(BinOp::And, Ty::I64, x[0], x[1]);
        let cd = fb.binop(BinOp::Xor, Ty::I64, x[2], x[3]);
        let l = fb.binop(BinOp::Or, Ty::I64, ab, cd);
        let ad = fb.binop(BinOp::Or, Ty::I64, x[0], x[3]);
        fb.binop(BinOp::Xor, Ty::I64, l, ad)
    });
    check("andorxor_chain_i64", &m, ROWS, true, |row| {
        let (a, b, c, d) = (row[0], row[1], row[2], row[3]);
        ((a & b) | (c ^ d)) ^ (a | d)
    });
}

#[test]
fn bic_chain_i64() {
    // r = (a & ~b) | (c & ~d)   (two bit-clear / and-not terms or'd together)
    let m = build4("bic64", |fb, x| {
        let nb = fb.unop(UnOp::Not, Ty::I64, x[1]);
        let nd = fb.unop(UnOp::Not, Ty::I64, x[3]);
        let t0 = fb.binop(BinOp::And, Ty::I64, x[0], nb);
        let t1 = fb.binop(BinOp::And, Ty::I64, x[2], nd);
        fb.binop(BinOp::Or, Ty::I64, t0, t1)
    });
    check("bic_chain_i64", &m, ROWS, true, |row| {
        let (a, b, c, d) = (row[0], row[1], row[2], row[3]);
        (a & !b) | (c & !d)
    });
}

#[test]
fn orn_eon_i64() {
    // ARM ORN/EON idioms:  r = (a | ~b) ^ (c ^ ~d)
    let m = build4("orn_eon64", |fb, x| {
        let nb = fb.unop(UnOp::Not, Ty::I64, x[1]);
        let nd = fb.unop(UnOp::Not, Ty::I64, x[3]);
        let orn = fb.binop(BinOp::Or, Ty::I64, x[0], nb);
        let eon = fb.binop(BinOp::Xor, Ty::I64, x[2], nd);
        fb.binop(BinOp::Xor, Ty::I64, orn, eon)
    });
    check("orn_eon_i64", &m, ROWS, true, |row| {
        let (a, b, c, d) = (row[0], row[1], row[2], row[3]);
        (a | !b) ^ (c ^ !d)
    });
}

#[test]
fn shifted_bic_register_amount() {
    // ARM shifted-register bit-clear:  r = a & ~(b << (c & 63))
    let m = build4("sh_bic64", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let s = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        let shifted = fb.binop(BinOp::Shl, Ty::I64, x[1], s);
        let n = fb.unop(UnOp::Not, Ty::I64, shifted);
        fb.binop(BinOp::And, Ty::I64, x[0], n)
    });
    check("shifted_bic_register_amount", &m, ROWS, true, |row| {
        let (a, b) = (row[0] as u64, row[1] as u64);
        let shifted = b.wrapping_shl((row[2] as u64 & 63) as u32);
        (a & !shifted) as i64
    });
}

// ===========================================================================
// 4. ctpop, and clz synthesized from shifts/masks.
// ===========================================================================

#[test]
fn ctpop_after_shift_mix_i64() {
    // r = ctpop( rotl(a, c&63) ^ (b >> (d&63)) )
    let m = build4("ctpop_mix", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let s = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        let lo = fb.binop(BinOp::Shl, Ty::I64, x[0], s);
        let zero = fb.iconst(Ty::I64, 0);
        let neg = fb.binop(BinOp::Sub, Ty::I64, zero, s);
        let comp = fb.binop(BinOp::And, Ty::I64, neg, m63);
        let hi = fb.binop(BinOp::LShr, Ty::I64, x[0], comp);
        let rot = fb.binop(BinOp::Or, Ty::I64, lo, hi);
        let dm = fb.binop(BinOp::And, Ty::I64, x[3], m63);
        let br = fb.binop(BinOp::LShr, Ty::I64, x[1], dm);
        let xored = fb.binop(BinOp::Xor, Ty::I64, rot, br);
        fb.ctpop(Ty::I64, xored)
    });
    check("ctpop_after_shift_mix_i64", &m, ROWS, true, |row| {
        let rot = (row[0] as u64).rotate_left((row[2] as u64 & 63) as u32);
        let br = (row[1] as u64) >> (row[3] as u64 & 63);
        (rot ^ br).count_ones() as i64
    });
}

// Synthesized count-leading-zeros at i64 via the classic "smear then popcount
// the complement" trick:
//   x |= x>>1; x |= x>>2; ... x |= x>>32;  clz = 64 - popcount(x)
// All shift amounts are small constants, so this is well-defined; computed at
// full i64 width, so the interpreter oracle is faithful.
fn build_clz64() -> trust_ir::Module {
    build4("clz64", |fb, x| {
        let mut v = x[0];
        for sh in [1i128, 2, 4, 8, 16, 32] {
            let k = fb.iconst(Ty::I64, sh);
            let s = fb.binop(BinOp::LShr, Ty::I64, v, k);
            v = fb.binop(BinOp::Or, Ty::I64, v, s);
        }
        let pc = fb.ctpop(Ty::I64, v);
        let c64 = fb.iconst(Ty::I64, 64);
        fb.binop(BinOp::Sub, Ty::I64, c64, pc)
    })
}

#[test]
fn clz_i64_synthesized() {
    let m = build_clz64();
    check("clz_i64_synthesized", &m, ROWS, true, |row| {
        (row[0] as u64).leading_zeros() as i64
    });
}

// ===========================================================================
// 5. Bitfield insert / extract with REGISTER-controlled offsets.
// ===========================================================================

#[test]
fn bitfield_extract_reg_offset_i64() {
    // Extract 8 bits at a register-controlled offset:  (a >> (c & 63)) & 0xff
    let m = build4("bfx_reg", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let off = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        let sh = fb.binop(BinOp::LShr, Ty::I64, x[0], off);
        let mask = fb.iconst(Ty::I64, 0xff);
        fb.binop(BinOp::And, Ty::I64, sh, mask)
    });
    check("bitfield_extract_reg_offset_i64", &m, ROWS, true, |row| {
        (((row[0] as u64) >> (row[2] as u64 & 63)) & 0xff) as i64
    });
}

#[test]
fn bitfield_insert_reg_offset_i64() {
    // Insert b's low byte into a at a register offset (masked so the field stays
    // inside the word: offset in 0..=56 via & 56):
    //   off    = c & 56
    //   field  = (b & 0xff) << off
    //   hole   = ~(0xff << off)
    //   r      = (a & hole) | field
    let m = build4("bfi_reg", |fb, x| {
        let m56 = fb.iconst(Ty::I64, 56);
        let off = fb.binop(BinOp::And, Ty::I64, x[2], m56);
        let lowb = fb.iconst(Ty::I64, 0xff);
        let bm = fb.binop(BinOp::And, Ty::I64, x[1], lowb);
        let field = fb.binop(BinOp::Shl, Ty::I64, bm, off);
        let mask = fb.binop(BinOp::Shl, Ty::I64, lowb, off);
        let hole = fb.unop(UnOp::Not, Ty::I64, mask);
        let cleared = fb.binop(BinOp::And, Ty::I64, x[0], hole);
        fb.binop(BinOp::Or, Ty::I64, cleared, field)
    });
    check("bitfield_insert_reg_offset_i64", &m, ROWS, true, |row| {
        let a = row[0] as u64;
        let b = row[1] as u64;
        let off = (row[2] as u64) & 56;
        let field = (b & 0xff) << off;
        let mask = 0xffu64 << off;
        ((a & !mask) | field) as i64
    });
}

// ===========================================================================
// 6. Sign / zero extend ladders i8 <-> i16 <-> i32 <-> i64.
//    Interpreter models extends as no-ops, so: native truth + cross-config JIT.
// ===========================================================================

#[test]
fn sext_ladder_i8_i16_i32_i64() {
    // a -> trunc i8 -> sext i16 -> sext i32 -> sext i64 (full sign ladder)
    let m = build4("sext_ladder", |fb, x| {
        let x8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[0]);
        let x16 = fb.cast(CastOp::SExt, Ty::I8, Ty::I16, x8);
        let x32 = fb.cast(CastOp::SExt, Ty::I16, Ty::I32, x16);
        fb.cast(CastOp::SExt, Ty::I32, Ty::I64, x32)
    });
    check("sext_ladder_i8_i16_i32_i64", &m, ROWS, false, |row| {
        (row[0] as i8) as i16 as i32 as i64
    });
}

#[test]
fn zext_ladder_i8_i16_i32_i64() {
    // a -> trunc i8 -> zext i16 -> zext i32 -> zext i64
    let m = build4("zext_ladder", |fb, x| {
        let x8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[0]);
        let x16 = fb.cast(CastOp::ZExt, Ty::I8, Ty::I16, x8);
        let x32 = fb.cast(CastOp::ZExt, Ty::I16, Ty::I32, x16);
        fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, x32)
    });
    check("zext_ladder_i8_i16_i32_i64", &m, ROWS, false, |row| {
        ((row[0] as u8) as u16 as u32 as u64) as i64
    });
}

#[test]
fn mixed_extend_ladder() {
    // sign at the bottom, zero in the middle, sign at the top:
    //   x8  = trunc i8 a
    //   x16 = sext i8 -> i16
    //   x32 = zext i16 -> i32   (kills the sign of x16's high bits at i32)
    //   r   = sext i32 -> i64
    let m = build4("mixed_ladder", |fb, x| {
        let x8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[0]);
        let x16 = fb.cast(CastOp::SExt, Ty::I8, Ty::I16, x8);
        let x32 = fb.cast(CastOp::ZExt, Ty::I16, Ty::I32, x16);
        fb.cast(CastOp::SExt, Ty::I32, Ty::I64, x32)
    });
    check("mixed_extend_ladder", &m, ROWS, false, |row| {
        let x8 = row[0] as i8;
        let x16 = x8 as i16;
        let x32 = (x16 as u16) as u32; // zext i16->i32
        (x32 as i32) as i64 // sext i32->i64
    });
}

#[test]
fn shift_then_extend_i32_to_i64() {
    // Compute a 32-bit logical shift, then sign-extend the i32 result to i64.
    // Exercises the interaction of a width-32 shift with the final SExt; this is
    // exactly where an i32 op that fails to clear/keep the high 32 bits before
    // sign-extension would diverge.
    //   x32  = (i32)a
    //   sh   = (i32)c & 31
    //   r32  = x32 << sh        (logical, i32)
    //   r    = sext i32 -> i64
    let m = build4("shext32", |fb, x| {
        let x32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[0]);
        let c32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[2]);
        let m31 = fb.iconst(Ty::I32, 31);
        let sh = fb.binop(BinOp::And, Ty::I32, c32, m31);
        let r32 = fb.binop(BinOp::Shl, Ty::I32, x32, sh);
        fb.cast(CastOp::SExt, Ty::I32, Ty::I64, r32)
    });
    check("shift_then_extend_i32_to_i64", &m, ROWS, false, |row| {
        let r32 = (row[0] as u32).wrapping_shl((row[2] as u32) & 31) as i32;
        r32 as i64
    });
}

#[test]
fn ashr_i32_then_zext() {
    // 32-bit arithmetic shift right by a register amount, then ZERO-extend the
    // i32 result. The zext must see only the low 32 bits, regardless of how the
    // i32 ashr filled the (logical) high 32 bits of the host register.
    let m = build4("ashr32_zext", |fb, x| {
        let x32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[0]);
        let c32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[2]);
        let m31 = fb.iconst(Ty::I32, 31);
        let sh = fb.binop(BinOp::And, Ty::I32, c32, m31);
        let r32 = fb.binop(BinOp::AShr, Ty::I32, x32, sh);
        fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, r32)
    });
    check("ashr_i32_then_zext", &m, ROWS, false, |row| {
        let r32 = (row[0] as i32) >> ((row[2] as u32) & 31);
        (r32 as u32) as u64 as i64
    });
}

// ===========================================================================
// 7. i32-width shifts by *unmasked* register amounts near the i32 boundary.
//    AArch64 32-bit (w-register) variable shifts mask the amount by 31, so an
//    unmasked `c` of 31/32/33/63/64/95/96/... must reduce identically. This is
//    the i32 analogue of `shl_i64_by_full_unmasked_register`; it catches a
//    lowering that masks by 63 (x-register rule) instead of 31 for a 32-bit op,
//    or one that emits a 64-bit shift for an i32 value. Interpreter is NOT used
//    (cast no-ops + i128 upper bits), so: native truth + cross-config JIT.
// ===========================================================================

#[test]
fn shl_i32_unmasked_reg_then_zext() {
    // r = zext( (i32)a << (i32)c )  -- amount reduced mod 32 by hardware.
    let m = build4("shl32_full", |fb, x| {
        let a32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[0]);
        let c32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[2]);
        let r32 = fb.binop(BinOp::Shl, Ty::I32, a32, c32);
        fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, r32)
    });
    check("shl_i32_unmasked_reg_then_zext", &m, ROWS, false, |row| {
        let r = (row[0] as u32).wrapping_shl((row[2] as u32) & 31);
        r as u64 as i64
    });
}

#[test]
fn lshr_i32_unmasked_reg_then_zext() {
    let m = build4("lshr32_full", |fb, x| {
        let a32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[0]);
        let c32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[2]);
        let r32 = fb.binop(BinOp::LShr, Ty::I32, a32, c32);
        fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, r32)
    });
    check("lshr_i32_unmasked_reg_then_zext", &m, ROWS, false, |row| {
        let r = (row[0] as u32) >> ((row[2] as u32) & 31);
        r as u64 as i64
    });
}

#[test]
fn ashr_i32_unmasked_reg_then_sext() {
    // 32-bit arithmetic shift by an unmasked amount, then SIGN-extend. Catches a
    // lowering that sign-extends a value that wasn't a clean i32, or masks the
    // amount by the wrong width.
    let m = build4("ashr32_full", |fb, x| {
        let a32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[0]);
        let c32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[2]);
        let r32 = fb.binop(BinOp::AShr, Ty::I32, a32, c32);
        fb.cast(CastOp::SExt, Ty::I32, Ty::I64, r32)
    });
    check("ashr_i32_unmasked_reg_then_sext", &m, ROWS, false, |row| {
        let r32 = (row[0] as i32) >> ((row[2] as u32) & 31);
        r32 as i64
    });
}

// ===========================================================================
// 8. Narrow-width (i16 / i8) variable shifts and bitops.
//    AArch64 has no native 8/16-bit variable shift; these lower through 32-bit
//    ops with width-correct masking of the result. The hazard is the *result*
//    width: an i16 shift must only keep 16 bits before the final extend, and the
//    amount must be reduced mod 16 (resp. mod 8). We mask the amount explicitly
//    to a legal range and zero-extend the result, then compare to a native u16/
//    u8 truth. Interpreter NOT used (it models narrow ops on i128).
// ===========================================================================

#[test]
fn shl_i16_reg_masked_then_zext() {
    // r = zext_u16( (u16)a << (c & 15) )
    let m = build4("shl16_reg", |fb, x| {
        let a16 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[0]);
        let c16 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[2]);
        let m15 = fb.iconst(Ty::I16, 15);
        let amt = fb.binop(BinOp::And, Ty::I16, c16, m15);
        let r16 = fb.binop(BinOp::Shl, Ty::I16, a16, amt);
        fb.cast(CastOp::ZExt, Ty::I16, Ty::I64, r16)
    });
    check("shl_i16_reg_masked_then_zext", &m, ROWS, false, |row| {
        let r = (row[0] as u16).wrapping_shl((row[2] as u32) & 15);
        r as u64 as i64
    });
}

#[test]
fn lshr_i16_reg_masked_then_zext() {
    // r = zext_u16( (u16)a >> (c & 15) ) -- logical right must NOT sign-fill.
    let m = build4("lshr16_reg", |fb, x| {
        let a16 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[0]);
        let c16 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[2]);
        let m15 = fb.iconst(Ty::I16, 15);
        let amt = fb.binop(BinOp::And, Ty::I16, c16, m15);
        let r16 = fb.binop(BinOp::LShr, Ty::I16, a16, amt);
        fb.cast(CastOp::ZExt, Ty::I16, Ty::I64, r16)
    });
    check("lshr_i16_reg_masked_then_zext", &m, ROWS, false, |row| {
        let r = (row[0] as u16) >> ((row[2] as u32) & 15);
        r as u64 as i64
    });
}

#[test]
fn ashr_i16_reg_masked_then_sext() {
    // r = sext_i16( (i16)a >> (c & 15) ) -- arithmetic right must sign-fill at
    // bit 15, NOT at bit 31/63. A lowering that sign-extends from the wrong bit
    // position before the shift would diverge.
    let m = build4("ashr16_reg", |fb, x| {
        let a16 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[0]);
        let c16 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[2]);
        let m15 = fb.iconst(Ty::I16, 15);
        let amt = fb.binop(BinOp::And, Ty::I16, c16, m15);
        let r16 = fb.binop(BinOp::AShr, Ty::I16, a16, amt);
        fb.cast(CastOp::SExt, Ty::I16, Ty::I64, r16)
    });
    check("ashr_i16_reg_masked_then_sext", &m, ROWS, false, |row| {
        let r16 = (row[0] as i16) >> ((row[2] as u32) & 15);
        r16 as i64
    });
}

#[test]
fn shl_i8_reg_masked_then_zext() {
    // r = zext_u8( (u8)a << (c & 7) )
    let m = build4("shl8_reg", |fb, x| {
        let a8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[0]);
        let c8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[2]);
        let m7 = fb.iconst(Ty::I8, 7);
        let amt = fb.binop(BinOp::And, Ty::I8, c8, m7);
        let r8 = fb.binop(BinOp::Shl, Ty::I8, a8, amt);
        fb.cast(CastOp::ZExt, Ty::I8, Ty::I64, r8)
    });
    check("shl_i8_reg_masked_then_zext", &m, ROWS, false, |row| {
        let r = (row[0] as u8).wrapping_shl((row[2] as u32) & 7);
        r as u64 as i64
    });
}

#[test]
fn ashr_i8_reg_masked_then_sext() {
    let m = build4("ashr8_reg", |fb, x| {
        let a8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[0]);
        let c8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[2]);
        let m7 = fb.iconst(Ty::I8, 7);
        let amt = fb.binop(BinOp::And, Ty::I8, c8, m7);
        let r8 = fb.binop(BinOp::AShr, Ty::I8, a8, amt);
        fb.cast(CastOp::SExt, Ty::I8, Ty::I64, r8)
    });
    check("ashr_i8_reg_masked_then_sext", &m, ROWS, false, |row| {
        let r8 = (row[0] as i8) >> ((row[2] as u32) & 7);
        r8 as i64
    });
}

#[test]
fn narrow_bitop_chain_i16_then_zext() {
    // and/or/xor/not chain computed entirely at i16, then zero-extended. A `Not`
    // at i16 in the interpreter is computed on i128 (header note), so we use
    // cross-config JIT + native u16 truth: r = zext_u16( ((a & b) ^ ~c) | (a ^ d) )
    let m = build4("nbit16", |fb, x| {
        let a = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[0]);
        let b = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[1]);
        let c = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[2]);
        let d = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[3]);
        let ab = fb.binop(BinOp::And, Ty::I16, a, b);
        let nc = fb.unop(UnOp::Not, Ty::I16, c);
        let l = fb.binop(BinOp::Xor, Ty::I16, ab, nc);
        let ad = fb.binop(BinOp::Xor, Ty::I16, a, d);
        let r16 = fb.binop(BinOp::Or, Ty::I16, l, ad);
        fb.cast(CastOp::ZExt, Ty::I16, Ty::I64, r16)
    });
    check("narrow_bitop_chain_i16_then_zext", &m, ROWS, false, |row| {
        let a = row[0] as u16;
        let b = row[1] as u16;
        let c = row[2] as u16;
        let d = row[3] as u16;
        let r = ((a & b) ^ !c) | (a ^ d);
        r as u64 as i64
    });
}

// ===========================================================================
// 9. i32 rotate by an *unmasked* register amount, zero-extended.
//    rotl32 synthesized from i32 shl/lshr/or with the complement amount masked
//    by 31. Feeding an unmasked `c` (so the low shl uses c & 31 by hardware, and
//    the complement is (32 - (c & 31)) & 31) must match u32::rotate_left exactly.
// ===========================================================================

#[test]
fn rotr_i32_unmasked_reg() {
    let m = build4("rotr32", |fb, x| {
        let a32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[0]);
        let s_full = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[2]);
        let m31 = fb.iconst(Ty::I32, 31);
        let s = fb.binop(BinOp::And, Ty::I32, s_full, m31);
        let lo = fb.binop(BinOp::LShr, Ty::I32, a32, s);
        let zero = fb.iconst(Ty::I32, 0);
        let neg = fb.binop(BinOp::Sub, Ty::I32, zero, s);
        let comp = fb.binop(BinOp::And, Ty::I32, neg, m31);
        let hi = fb.binop(BinOp::Shl, Ty::I32, a32, comp);
        let r32 = fb.binop(BinOp::Or, Ty::I32, lo, hi);
        fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, r32)
    });
    check("rotr_i32_unmasked_reg", &m, ROWS, false, |row| {
        let r = (row[0] as u32).rotate_right((row[2] as u32) & 31);
        r as u64 as i64
    });
}

// ===========================================================================
// 10. Synthesized count-trailing-zeros at i64 width.
//    ctz(x) = popcount( (x & (-x)) - 1 )   for x != 0, and 64 for x == 0.
//    We compute the popcount-of-(isolate-lowest-set-minus-1) form and special-
//    case zero in the native truth to 64. To keep the IR branch-free we OR a
//    "was-zero" correction: if x==0 the isolate term is 0, (0-1) = all-ones,
//    popcount(all-ones)=64, which already equals ctz(0)=64. So the single
//    formula popcount((x & -x) - 1) is exact for ALL x including 0. Full i64
//    width, so the interpreter oracle is faithful.
// ===========================================================================

#[test]
fn ctz_i64_synthesized() {
    let m = build4("ctz64", |fb, x| {
        let zero = fb.iconst(Ty::I64, 0);
        let neg = fb.binop(BinOp::Sub, Ty::I64, zero, x[0]); // -x
        let iso = fb.binop(BinOp::And, Ty::I64, x[0], neg); // lowest set bit
        let one = fb.iconst(Ty::I64, 1);
        let m1 = fb.binop(BinOp::Sub, Ty::I64, iso, one); // iso - 1
        fb.ctpop(Ty::I64, m1)
    });
    check("ctz_i64_synthesized", &m, ROWS, true, |row| {
        (row[0] as u64).trailing_zeros() as i64
    });
}

// ===========================================================================
// 11. Multi-byte bitfield extract at a register-controlled offset, full i64.
//    Extract a 16-bit field at a byte-aligned register offset (0..=48 via &48):
//      r = (a >> (c & 48)) & 0xffff
//    Full i64 width: interpreter oracle is faithful.
// ===========================================================================

#[test]
fn bitfield_extract16_reg_offset_i64() {
    let m = build4("bfx16_reg", |fb, x| {
        let m48 = fb.iconst(Ty::I64, 48);
        let off = fb.binop(BinOp::And, Ty::I64, x[2], m48);
        let sh = fb.binop(BinOp::LShr, Ty::I64, x[0], off);
        let mask = fb.iconst(Ty::I64, 0xffff);
        fb.binop(BinOp::And, Ty::I64, sh, mask)
    });
    check("bitfield_extract16_reg_offset_i64", &m, ROWS, true, |row| {
        (((row[0] as u64) >> (row[2] as u64 & 48)) & 0xffff) as i64
    });
}

// ===========================================================================
// 12. Extend / shift / extend interleave: trunc i8 -> sext i32 -> i32 shift ->
//     sext i64.  Forces the sign of the byte to survive a 32-bit variable shift
//     and a final 64-bit sign extend. Narrow widths => native truth + JIT.
// ===========================================================================

#[test]
fn sext_byte_then_i32_shift_then_sext64() {
    let m = build4("sb_sh_s64", |fb, x| {
        let a8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[0]);
        let a32 = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, a8);
        let c32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[2]);
        let m31 = fb.iconst(Ty::I32, 31);
        let sh = fb.binop(BinOp::And, Ty::I32, c32, m31);
        let r32 = fb.binop(BinOp::AShr, Ty::I32, a32, sh);
        fb.cast(CastOp::SExt, Ty::I32, Ty::I64, r32)
    });
    check(
        "sext_byte_then_i32_shift_then_sext64",
        &m,
        ROWS,
        false,
        |row| {
            let a32 = (row[0] as i8) as i32;
            let r32 = a32 >> ((row[2] as u32) & 31);
            r32 as i64
        },
    );
}

// ===========================================================================
// 13. Shifted-register AND/ORR/EOR with register shift amounts, full i64.
//     ARM "op Xd, Xn, Xm, LSL #s" idioms but with a *register* shift amount:
//       r = (a & (b << (c & 63))) ^ (a | (b >> (d & 63)))
//     Full i64 width: interpreter oracle is faithful.
// ===========================================================================

#[test]
fn shifted_reg_logical_mix_i64() {
    let m = build4("shreg_log64", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let cs = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        let ds = fb.binop(BinOp::And, Ty::I64, x[3], m63);
        let bl = fb.binop(BinOp::Shl, Ty::I64, x[1], cs);
        let br = fb.binop(BinOp::LShr, Ty::I64, x[1], ds);
        let t0 = fb.binop(BinOp::And, Ty::I64, x[0], bl);
        let t1 = fb.binop(BinOp::Or, Ty::I64, x[0], br);
        fb.binop(BinOp::Xor, Ty::I64, t0, t1)
    });
    check("shifted_reg_logical_mix_i64", &m, ROWS, true, |row| {
        let a = row[0] as u64;
        let b = row[1] as u64;
        let cs = row[2] as u64 & 63;
        let ds = row[3] as u64 & 63;
        let bl = b.wrapping_shl(cs as u32);
        let br = b >> ds;
        ((a & bl) ^ (a | br)) as i64
    });
}

// ===========================================================================
// 14. Narrow-width UNMASKED variable shifts.
//
//   The masked narrow shifts in section 8 (which explicitly `& 7` / `& 15` the
//   amount) all pass. The cases below instead feed the *un-pre-masked* amount to
//   a narrow shift, relying on the IR's defined shift semantics to reduce it.
//   They are kept as always-on guards, including the three smallest former
//   reproducers of DEFECT W below.
//
// DEFECT W — narrow (i8/i16) variable shift reduces the amount by the wrong
// modulus on the JIT.
//
//   trust_ir shift semantics are width-modular. The interpreter (the defining
//   oracle, crates/trust-cg-codegen/src/interpreter.rs `shift_amount`) computes
//       shift_amount(value, width) = value % width
//   so an i8 `Shl`/`LShr`/`AShr` reduces the amount mod 8, an i16 shift mod 16.
//   Every config of the JIT instead shifts by the full amount (it masks by 31 /
//   does a 32-bit shift), so for an amount equal to the operand width the JIT
//   shifts the value entirely out (or sign-smears, for i8 AShr) while the oracle
//   returns the value unchanged (shift by 0).
//
//   The i16 LShr and i8 AShr reproducers are confirmed THREE ways — the
//   interpreter oracle (use_interp=true) agrees with the native truth, and only
//   the JIT diverges:
//     i16 LShr: oracle/native 0xab >> (16 % 16)=0 = 0xab (171); JIT = 0
//     i8  AShr: oracle/native (i8)0xab=-85 >> (16 % 8)=0 = -85; JIT = -1
//   The i8 Shl reproducer is confirmed by native truth + JIT cross-config only.
//   The interpreter is NOT a faithful oracle for it: `Ty::I8` is signed and the
//   interpreter models ZExt i8->i64 as an i128 no-op, so it sign-extends the i8
//   shift result (0xff -> -1) instead of zero-extending, returning -1. That is a
//   *modeling* artifact of the oracle's narrow-cast no-op, not the shift bug, so
//   we drop the oracle here (use_interp=false) exactly as the module header
//   prescribes for narrow casts, and rely on native u8 truth + JIT agreement.
//     i8  Shl : native 0xff << (8 % 8)=0 = 0xff (255); every JIT config = 0
//
//   Minimal build_module body for the i8 Shl reproducer:
//       let a8 = cast Trunc i64 -> i8, a
//       let c8 = cast Trunc i64 -> i8, c
//       let r8 = binop Shl i8, a8, c8     // JIT shifts by 8 (=> 0); defined: by 0
//       let r  = cast ZExt i8 -> i64, r8
//       ret [r]
// ===========================================================================

// Single-row reproducers (minimized).
const ROW_I8_SHL: &[[i64; 4]] = &[[0xff, 0, 8, 0]];
const ROW_I16_LSHR: &[[i64; 4]] = &[[0xab, 0, 16, 0]];
const ROW_I8_ASHR: &[[i64; 4]] = &[[0xab, 0, 16, 0]];

// Regression for DEFECT W (FIXED): narrow (i8/i16) register-amount shifts now
// mask the amount to width-1 (select_shift), so the 32-bit ASR/LSL/LSR matches
// the mod-width interpreter semantics.
#[test]
fn shl_i8_unmasked_reg_then_zext() {
    // r = zext_u8( (u8)a << (u8)c ). use_interp=false: the interpreter's narrow
    // ZExt no-op sign-corrupts 0xff -> -1 (see DEFECT W note), so we confirm via
    // native u8 truth + cross-config JIT. Native truth = a << (c % 8) = 0xff; the
    // JIT shifts by the full 8 and returns 0.
    let m = build4("shl8_full", |fb, x| {
        let a8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[0]);
        let c8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[2]);
        let r8 = fb.binop(BinOp::Shl, Ty::I8, a8, c8);
        fb.cast(CastOp::ZExt, Ty::I8, Ty::I64, r8)
    });
    check(
        "shl_i8_unmasked_reg_then_zext",
        &m,
        ROW_I8_SHL,
        false,
        |row| {
            let r = (row[0] as u8).wrapping_shl((row[2] as u32) & 7);
            r as u64 as i64
        },
    );
}

#[test]
fn lshr_i16_unmasked_reg_then_zext() {
    // r = zext_u16( (u16)a >> (u16)c ); the i16 `LShr` is oracle-evaluated at
    // width 16, so use_interp=true confirms the defined result is `a >> (c % 16)`.
    let m = build4("lshr16_full", |fb, x| {
        let a16 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[0]);
        let c16 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[2]);
        let r16 = fb.binop(BinOp::LShr, Ty::I16, a16, c16);
        fb.cast(CastOp::ZExt, Ty::I16, Ty::I64, r16)
    });
    check(
        "lshr_i16_unmasked_reg_then_zext",
        &m,
        ROW_I16_LSHR,
        true,
        |row| {
            let r = (row[0] as u16) >> ((row[2] as u32) & 15);
            r as u64 as i64
        },
    );
}

#[test]
fn ashr_i8_unmasked_reg_then_sext() {
    // r = sext_i8( (i8)a >> (i8)c ); the i8 `AShr` is oracle-evaluated at width 8,
    // so use_interp=true confirms the defined result is `(i8)a >> (c % 8)`.
    let m = build4("ashr8_full", |fb, x| {
        let a8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[0]);
        let c8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[2]);
        let r8 = fb.binop(BinOp::AShr, Ty::I8, a8, c8);
        fb.cast(CastOp::SExt, Ty::I8, Ty::I64, r8)
    });
    check(
        "ashr_i8_unmasked_reg_then_sext",
        &m,
        ROW_I8_ASHR,
        true,
        |row| {
            let r8 = (row[0] as i8) >> ((row[2] as u32) & 7);
            r8 as i64
        },
    );
}

// Regression guard: the EXPLICITLY masked i16 shift over the same boundary
// amounts (8/16/24/32/...) is correct on every config and stays enabled. This
// pins the contrast: masking the amount in the IR avoids DEFECT W.
const NARROW_AMT_ROWS: &[[i64; 4]] = &[
    [0xff, 0, 8, 8],
    [0xab, 0, 16, 16],
    [0x80, 0, 24, 24],
    [0x7f, 0, 7, 15],
    [-1, 0, 9, 17],
    [0x3c, 0, 33, 49],
    [0x01, 0, 31, 32],
    [0xfe, 0, 1, 2],
];

#[test]
fn shl_i16_masked_on_narrow_rows() {
    let m = build4("shl16_reg2", |fb, x| {
        let a16 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[0]);
        let c16 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[2]);
        let m15 = fb.iconst(Ty::I16, 15);
        let amt = fb.binop(BinOp::And, Ty::I16, c16, m15);
        let r16 = fb.binop(BinOp::Shl, Ty::I16, a16, amt);
        fb.cast(CastOp::ZExt, Ty::I16, Ty::I64, r16)
    });
    check(
        "shl_i16_masked_on_narrow_rows",
        &m,
        NARROW_AMT_ROWS,
        false,
        |row| {
            let r = (row[0] as u16).wrapping_shl((row[2] as u32) & 15);
            r as u64 as i64
        },
    );
}
