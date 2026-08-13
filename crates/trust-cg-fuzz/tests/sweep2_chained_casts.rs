// trust-cg-fuzz/tests/sweep2_chained_casts.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sweep2 surface: chained integer/float casts (i8 <-> i16 <-> i32 <-> i64 <->
// i128 and integer <-> f32/f64), where the *bit width* matters.
//
// Oracle choice. The trust_cg interpreter models Trunc/ZExt/SExt as no-ops on
// its internal i128 representation, so it is NOT a faithful oracle for these
// programs (it cannot distinguish `zext i8->i64` from `sext i8->i64`). Per the
// task's guidance, width-dependent casts therefore use:
//   * a Rust ground-truth computed with real fixed-width semantics, and
//   * cross-config JIT agreement (every O0..O3 x fast/precise regalloc).
//
// Float chains use only exact-small integer-valued floats so that the round trip
// i64 -> f64 -> i64 is exact and the result is deterministic.
//
// ---------------------------------------------------------------------------
// FINDING — DEFECT B (caught by the now-always-on `ladder_through_i128`).
//
// `Trunc i128 -> i64` (and `Trunc i128 -> i32`) of an i128 value produced by
// `SExt`/`ZExt` i64->i128 returns 0 instead of the low bits, at EVERY opt level
// (O0..O3) and BOTH regallocs — so cross-config JIT agreement alone does not
// catch it; only the Rust ground truth does. The identical truncation done
// purely in i64 (`Trunc i64->i32` then `ZExt`) is correct, so the bug is in the
// i128 extend/truncate register-pair handling, not in narrow truncation.
//
// Minimal `build_module` body (smallest reproduction, returns 0 for any input):
//     let a  = block param i64
//     let w  = cast SExt  i64  -> i128, a      // any nonzero input
//     let r  = cast Trunc i128 -> i64,  w      // <- yields 0, should be a
//     ret [r]
//
// The regression runs in the ordinary target-appropriate test lane.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{CastOp, Ty};
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

/// Build `fuzz_fn(a,_,_,_)` whose body maps the single i64 arg `a` through a
/// cast chain `body` and returns the resulting i64.
fn build_chain<F>(name: &str, body: F) -> trust_ir::Module
where
    F: FnOnce(&mut trust_ir_build::FunctionBuilder, trust_ir::ValueId) -> trust_ir::ValueId,
{
    let mut mb = ModuleBuilder::new(name);
    let ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let _b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let r = body(&mut fb, a);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

const ROWS: &[[i64; 4]] = &[
    [0, 0, 0, 0],
    [1, 0, 0, 0],
    [-1, 0, 0, 0],
    [127, 0, 0, 0],
    [128, 0, 0, 0],
    [255, 0, 0, 0],
    [256, 0, 0, 0],
    [-128, 0, 0, 0],
    [-129, 0, 0, 0],
    [32767, 0, 0, 0],
    [32768, 0, 0, 0],
    [65535, 0, 0, 0],
    [65536, 0, 0, 0],
    [i64::MAX, 0, 0, 0],
    [i64::MIN, 0, 0, 0],
    [0x7fff_ffff, 0, 0, 0],
    [0x8000_0000u32 as i64, 0, 0, 0],
    [-0x8000_0000i64, 0, 0, 0],
    [0xdead_beef_dead_beefu64 as i64, 0, 0, 0],
    [0x0123_4567_89ab_cdef, 0, 0, 0],
];

#[test]
fn trunc_i64_to_i8_then_sext_back() {
    // (i64) sext (i8) trunc a   ==   a sign-extended from its low byte.
    let m = build_chain("trunc_sext8", |fb, a| {
        let t = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, a);
        fb.cast(CastOp::SExt, Ty::I8, Ty::I64, t)
    });
    check("trunc_i64_to_i8_then_sext_back", &m, ROWS, |row| {
        (row[0] as i8) as i64
    });
}

#[test]
fn trunc_i64_to_i8_then_zext_back() {
    let m = build_chain("trunc_zext8", |fb, a| {
        let t = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, a);
        fb.cast(CastOp::ZExt, Ty::I8, Ty::I64, t)
    });
    check("trunc_i64_to_i8_then_zext_back", &m, ROWS, |row| {
        (row[0] as u8) as u64 as i64
    });
}

#[test]
fn trunc_i64_to_i16_zext_and_sext() {
    for signed in [false, true] {
        let m = build_chain(if signed { "tz16_s" } else { "tz16_u" }, |fb, a| {
            let t = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, a);
            if signed {
                fb.cast(CastOp::SExt, Ty::I16, Ty::I64, t)
            } else {
                fb.cast(CastOp::ZExt, Ty::I16, Ty::I64, t)
            }
        });
        check(
            if signed {
                "trunc16_sext"
            } else {
                "trunc16_zext"
            },
            &m,
            ROWS,
            |row| {
                if signed {
                    (row[0] as i16) as i64
                } else {
                    (row[0] as u16) as u64 as i64
                }
            },
        );
    }
}

#[test]
fn ladder_i64_i8_i32_i16_i64() {
    // A multi-step ladder mixing widths and signedness:
    //   x8  = (i8)  trunc a
    //   x32 = (i32) sext x8
    //   x16 = (i16) trunc x32
    //   r   = (i64) zext x16
    let m = build_chain("ladder", |fb, a| {
        let x8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, a);
        let x32 = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, x8);
        let x16 = fb.cast(CastOp::Trunc, Ty::I32, Ty::I16, x32);
        fb.cast(CastOp::ZExt, Ty::I16, Ty::I64, x16)
    });
    check("ladder_i64_i8_i32_i16_i64", &m, ROWS, |row| {
        let x8 = row[0] as i8; // trunc + (sign matters next)
        let x32 = x8 as i32; // sext i8->i32
        let x16 = x32 as i16; // trunc i32->i16
        (x16 as u16) as u64 as i64 // zext i16->i64
    });
}

#[test]
fn ladder_through_i128() {
    // a -> sext i64->i128 -> trunc i128->i32 -> zext i32->i64
    let m = build_chain("ladder128", |fb, a| {
        let x128 = fb.cast(CastOp::SExt, Ty::I64, Ty::I128, a);
        let x32 = fb.cast(CastOp::Trunc, Ty::I128, Ty::I32, x128);
        fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, x32)
    });
    check("ladder_through_i128", &m, ROWS, |row| {
        let x32 = row[0] as i32; // low 32 bits
        (x32 as u32) as u64 as i64 // zext
    });
}

// --- Integer <-> float round trips (exact small magnitudes only) ---

/// Only exact integer-valued rows whose magnitude is < 2^52 so the i64->f64->i64
/// round trip is exact.
const FLOAT_ROWS: &[[i64; 4]] = &[
    [0, 0, 0, 0],
    [1, 0, 0, 0],
    [-1, 0, 0, 0],
    [2, 0, 0, 0],
    [-2, 0, 0, 0],
    [42, 0, 0, 0],
    [-42, 0, 0, 0],
    [127, 0, 0, 0],
    [128, 0, 0, 0],
    [255, 0, 0, 0],
    [256, 0, 0, 0],
    [1000, 0, 0, 0],
    [-1000, 0, 0, 0],
    [65536, 0, 0, 0],
    [1_000_000, 0, 0, 0],
    [-1_000_000, 0, 0, 0],
    [16_777_216, 0, 0, 0], // 2^24, exact in f32 too
];

#[test]
fn i64_f64_i64_roundtrip() {
    // (i64) fptosi (f64) sitofp a
    let m = build_chain("rt_f64", |fb, a| {
        let f = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, a);
        fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, f)
    });
    check("i64_f64_i64_roundtrip", &m, FLOAT_ROWS, |row| row[0]);
}

#[test]
fn i8_f64_i64_chain() {
    // a -> trunc i8 -> sext i32 -> sitofp f64 -> fptosi i64
    let m = build_chain("i8_f64", |fb, a| {
        let x8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, a);
        let x32 = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, x8);
        let f = fb.cast(CastOp::SIToFP, Ty::I32, Ty::F64, x32);
        fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, f)
    });
    check("i8_f64_i64_chain", &m, ROWS, |row| {
        let x8 = row[0] as i8;
        let x32 = x8 as i32;
        x32 as f64 as i64
    });
}

#[test]
fn f32_f64_narrowing_chain() {
    // a (small) -> sitofp f32 -> fpext f64 -> fptosi i64
    let m = build_chain("f32_f64", |fb, a| {
        let f32v = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F32, a);
        let f64v = fb.cast(CastOp::FPExt, Ty::F32, Ty::F64, f32v);
        fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, f64v)
    });
    check("f32_f64_narrowing_chain", &m, FLOAT_ROWS, |row| {
        // Rows are all <= 2^24, exactly representable in f32.
        ((row[0] as f32) as f64) as i64
    });
}
