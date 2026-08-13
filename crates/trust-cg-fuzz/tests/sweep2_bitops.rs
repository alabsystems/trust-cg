// trust-cg-fuzz/tests/sweep2_bitops.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sweep2 surface: bit-population count (`ctpop`) and synthesized bitfield
// extract / insert / reverse-byte sequences built from shift + mask + or.
//
// The trust_ir IR exposes `ctpop` directly (UnOp::CtPop); there is no dedicated
// clz / rbit / bswap opcode, so those are synthesized from primitive shifts and
// masks. `ctpop` at i64 width is faithfully modeled by the interpreter, but to
// stay width-precise (and to cover the narrow-width ctpop path) this sweep uses:
//   * a Rust ground-truth (`count_ones` at the declared width), and
//   * cross-config JIT agreement (O0..O3 x fast/precise regalloc).
//
// All shift amounts are constants in 0..64, so every operation is well-defined.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{BinOp, CastOp, Ty};
use trust_ir_build::ModuleBuilder;

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

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

fn check<F>(label: &str, module: &trust_ir::Module, rows: &[[i64; 4]], truth: F)
where
    F: Fn([i64; 4]) -> i64,
{
    for &row in rows {
        let want = truth(row);
        let mut jit_vals: Vec<(OptLevel, bool, i64)> = Vec::new();
        for fast in [true, false] {
            for opt in OPTS {
                match jit(module, opt, fast, row) {
                    Ok(v) => jit_vals.push((opt, fast, v)),
                    Err(e) => panic!("{label}: row={row:?} opt={opt:?} fast={fast}: {e}"),
                }
            }
        }
        for (opt, fast, got) in &jit_vals {
            assert_eq!(
                *got, want,
                "{label}: TRUTH MISMATCH row={row:?} opt={opt:?} fast={fast} got={got} want={want}"
            );
        }
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

/// `fuzz_fn(a,b,c,d)` where `body` consumes the four i64 args and returns an i64.
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
    [255, 256, 65535, 65536],
    [
        0x8000_0000_0000_0000u64 as i64,
        0x7fff_ffff_ffff_ffff,
        63,
        0,
    ],
    [
        0x0000_0000_ffff_ffff,
        0xffff_ffff_0000_0000u64 as i64,
        1,
        62,
    ],
    [42, -42, 100, -100],
];

#[test]
fn ctpop_i64() {
    let m = build4("ctpop64", |fb, x| fb.ctpop(Ty::I64, x[0]));
    check("ctpop_i64", &m, ROWS, |row| {
        (row[0] as u64).count_ones() as i64
    });
}

#[test]
fn ctpop_i32_after_trunc() {
    // ctpop on the low 32 bits.
    let m = build4("ctpop32", |fb, x| {
        let t = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[0]);
        let p = fb.ctpop(Ty::I32, t);
        fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, p)
    });
    check("ctpop_i32_after_trunc", &m, ROWS, |row| {
        (row[0] as u32).count_ones() as i64
    });
}

// DEFECT C (FIXED) — non-encodable logical immediate in the 8-bit ctpop (SWAR)
// lowering. `ctpop` at `Ty::I8` used to lower into a software popcount whose
// mask constants were narrowed to the operand width (0x55, 0x33, ...) and
// emitted as `AND Wd, Wn, #imm`. The SWAR mask 0x55 is NOT a valid AArch64
// logical immediate at 32-bit (w-register) width, so the encoder aborted the
// whole compile:
//     Jit(Pipeline(Encoding(
//       "invalid operand at index 2 for AndRI: expected register,
//        got logical immediate 0x55 is not encodable ... opcode AndRI
//        operands [PReg(w2), PReg(w0), Imm(85)]")))
// The fix (trust-cg-lower `ctpop_swar_mask`) widens the narrow SWAR masks to the
// full 32-bit repeating constants 0x5555_5555 / 0x3333_3333 / 0x0f0f_0f0f, which
// ARE encodable. The narrow input is zero-extended (upper bits 0), so the wider
// masks yield the identical low-byte popcount. This case is now enabled.
//
// Minimal `build_module` body:
//     let a = block param i64
//     let t = cast Trunc i64 -> i8, a
//     let p = unop  CtPop i8, t            // formerly aborted on AND Wd,Wn,#0x55
//     let r = cast ZExt  i8 -> i64, p
//     ret [r]
#[test]
fn ctpop_i8_after_trunc() {
    let m = build4("ctpop8", |fb, x| {
        let t = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[0]);
        let p = fb.ctpop(Ty::I8, t);
        fb.cast(CastOp::ZExt, Ty::I8, Ty::I64, p)
    });
    check("ctpop_i8_after_trunc", &m, ROWS, |row| {
        (row[0] as u8).count_ones() as i64
    });
}

#[test]
fn ctpop_xor_of_two_args() {
    // popcount(a ^ b) == Hamming distance; exercises ctpop fed by a binop.
    let m = build4("ctpop_xor", |fb, x| {
        let t = fb.binop(BinOp::Xor, Ty::I64, x[0], x[1]);
        fb.ctpop(Ty::I64, t)
    });
    check("ctpop_xor_of_two_args", &m, ROWS, |row| {
        ((row[0] as u64) ^ (row[1] as u64)).count_ones() as i64
    });
}

#[test]
fn bitfield_extract_const() {
    // Extract the byte at bit offset 16, width 8:  (a >> 16) & 0xff
    let m = build4("bf_extract", |fb, x| {
        let sh = fb.iconst(Ty::I64, 16);
        let shifted = fb.binop(BinOp::LShr, Ty::I64, x[0], sh);
        let mask = fb.iconst(Ty::I64, 0xff);
        fb.binop(BinOp::And, Ty::I64, shifted, mask)
    });
    check("bitfield_extract_const", &m, ROWS, |row| {
        (((row[0] as u64) >> 16) & 0xff) as i64
    });
}

#[test]
fn bitfield_insert_const() {
    // Insert b's low 8 bits into a at bit offset 24:
    //   cleared = a & ~(0xff << 24)
    //   r       = cleared | ((b & 0xff) << 24)
    let m = build4("bf_insert", |fb, x| {
        let off = fb.iconst(Ty::I64, 24);
        let field_mask = fb.iconst(Ty::I64, 0xff << 24);
        let inv = fb.iconst(Ty::I64, !(0xff_i128 << 24));
        let cleared = fb.binop(BinOp::And, Ty::I64, x[0], inv);
        let low = fb.iconst(Ty::I64, 0xff);
        let bmasked = fb.binop(BinOp::And, Ty::I64, x[1], low);
        let bshift = fb.binop(BinOp::Shl, Ty::I64, bmasked, off);
        let _ = field_mask;
        fb.binop(BinOp::Or, Ty::I64, cleared, bshift)
    });
    check("bitfield_insert_const", &m, ROWS, |row| {
        let a = row[0] as u64;
        let b = row[1] as u64;
        let cleared = a & !(0xffu64 << 24);
        (cleared | ((b & 0xff) << 24)) as i64
    });
}

#[test]
fn byte_swap_synthesized_32() {
    // Synthesize bswap32 on the low 32 bits via shifts and masks.
    let m = build4("bswap32", |fb, x| {
        let t = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x[0]);
        let v = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, t); // zero-extended low 32
        // b0 = (v & 0xff) << 24
        let m_ff = fb.iconst(Ty::I64, 0xff);
        let s24 = fb.iconst(Ty::I64, 24);
        let s8 = fb.iconst(Ty::I64, 8);
        let b0 = {
            let x0 = fb.binop(BinOp::And, Ty::I64, v, m_ff);
            fb.binop(BinOp::Shl, Ty::I64, x0, s24)
        };
        // b1 = ((v >> 8) & 0xff) << 16
        let b1 = {
            let x1 = fb.binop(BinOp::LShr, Ty::I64, v, s8);
            let x1 = fb.binop(BinOp::And, Ty::I64, x1, m_ff);
            let s16 = fb.iconst(Ty::I64, 16);
            fb.binop(BinOp::Shl, Ty::I64, x1, s16)
        };
        // b2 = ((v >> 16) & 0xff) << 8
        let b2 = {
            let s16 = fb.iconst(Ty::I64, 16);
            let x2 = fb.binop(BinOp::LShr, Ty::I64, v, s16);
            let x2 = fb.binop(BinOp::And, Ty::I64, x2, m_ff);
            fb.binop(BinOp::Shl, Ty::I64, x2, s8)
        };
        // b3 = (v >> 24) & 0xff
        let b3 = {
            let x3 = fb.binop(BinOp::LShr, Ty::I64, v, s24);
            fb.binop(BinOp::And, Ty::I64, x3, m_ff)
        };
        let t01 = fb.binop(BinOp::Or, Ty::I64, b0, b1);
        let t23 = fb.binop(BinOp::Or, Ty::I64, b2, b3);
        fb.binop(BinOp::Or, Ty::I64, t01, t23)
    });
    check("byte_swap_synthesized_32", &m, ROWS, |row| {
        let v = (row[0] as u32) as u64;
        let r = ((v & 0xff) << 24)
            | (((v >> 8) & 0xff) << 16)
            | (((v >> 16) & 0xff) << 8)
            | ((v >> 24) & 0xff);
        r as i64
    });
}

#[test]
fn popcount_of_bitfield_chain() {
    // Deep mix: r = ctpop( ((a >> (c&63)) & b) | (d << (c&31)) )
    let m = build4("pc_chain", |fb, x| {
        let m63 = fb.iconst(Ty::I64, 63);
        let amt = fb.binop(BinOp::And, Ty::I64, x[2], m63);
        let shifted = fb.binop(BinOp::LShr, Ty::I64, x[0], amt);
        let anded = fb.binop(BinOp::And, Ty::I64, shifted, x[1]);
        let m31 = fb.iconst(Ty::I64, 31);
        let amt2 = fb.binop(BinOp::And, Ty::I64, x[2], m31);
        let dshift = fb.binop(BinOp::Shl, Ty::I64, x[3], amt2);
        let ored = fb.binop(BinOp::Or, Ty::I64, anded, dshift);
        fb.ctpop(Ty::I64, ored)
    });
    check("popcount_of_bitfield_chain", &m, ROWS, |row| {
        let a = row[0] as u64;
        let b = row[1] as u64;
        let c = row[2] as u64;
        let d = row[3] as u64;
        let shifted = a >> (c & 63);
        let anded = shifted & b;
        let dshift = d.wrapping_shl((c & 31) as u32);
        (anded | dshift).count_ones() as i64
    });
}
