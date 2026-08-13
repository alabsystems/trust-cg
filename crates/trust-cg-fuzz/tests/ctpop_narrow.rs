// trust-cg-fuzz/tests/ctpop_narrow.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential regression for the narrow-width (i8/i16) ctpop SWAR lowering.
//
// Defect history (DEFECT C): the scalar SWAR popcount for an 8-bit (and 16-bit)
// value used to mask its constants down to the operand width, emitting
// `AND Wd, Wn, #0x55` (also 0x33, 0x0f0f-style narrowed values). 0x55 / 0x5555 /
// 0x3333 / 0x0f0f are NOT valid AArch64 32-bit logical immediates, so the
// encoder aborted with "logical immediate 0x55 is not encodable" on `AndRI`.
//
// The fix widens the narrow SWAR masks to the full 32-bit repeating constants
// 0x5555_5555 / 0x3333_3333 / 0x0f0f_0f0f, which ARE encodable. Since the narrow
// input is zero-extended (upper bits 0) the wider masks yield the identical
// low-byte popcount (range 0..=8 for i8, 0..=16 for i16).
//
// This test differentially compares the compiled `fuzz_fn` against a Rust
// `count_ones` reference across all O0..O3 optimization levels x both register
// allocators (fast / precise), for both:
//   - zext(ctpop(trunc(a, i8)))  -> popcount of the low 8 bits
//   - zext(ctpop(trunc(a, i16))) -> popcount of the low 16 bits

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

/// A spread of `a` values exercising every i8 popcount (0..=8) and a range of
/// i16 popcounts, including boundary patterns (all-zero, saturated byte, single
/// bits, alternating bits, and high-garbage values whose upper bits must NOT
/// leak into the narrow popcount because the operand is zero-extended).
const ROWS: &[[i64; 4]] = &[
    [0x0000_0000_0000_0000, 0, 0, 0],           // i8: 0, i16: 0
    [0x0000_0000_0000_0001, 0, 0, 0],           // i8: 1, i16: 1
    [0x0000_0000_0000_0080, 0, 0, 0],           // i8: 1 (high bit of the byte)
    [0x0000_0000_0000_00ff, 0, 0, 0],           // i8: 8 (saturated byte)
    [0x0000_0000_0000_0055, 0, 0, 0],           // i8: 4 (the historical bad-mask pattern)
    [0x0000_0000_0000_00aa, 0, 0, 0],           // i8: 4
    [0x0000_0000_0000_000f, 0, 0, 0],           // i8: 4
    [0x0000_0000_0000_00f0, 0, 0, 0],           // i8: 4
    [0x0000_0000_0000_0007, 0, 0, 0],           // i8: 3
    [0x0000_0000_0000_007f, 0, 0, 0],           // i8: 7
    [0x0000_0000_0000_00fe, 0, 0, 0],           // i8: 7
    [0x0000_0000_0000_0003, 0, 0, 0],           // i8: 2
    [0x0000_0000_0000_001f, 0, 0, 0],           // i8: 5
    [0x0000_0000_0000_003f, 0, 0, 0],           // i8: 6
    [0x0000_0000_0000_ffff, 0, 0, 0],           // i8: 8, i16: 16
    [0x0000_0000_0000_aa55, 0, 0, 0],           // i8: 4, i16: 8
    [0x0000_0000_0000_8001, 0, 0, 0],           // i8: 1, i16: 2
    [0x0000_0000_0000_7fff, 0, 0, 0],           // i8: 8, i16: 15
    [0xffff_ffff_ffff_ff00u64 as i64, 0, 0, 0], // i8: 0, i16: 0 (garbage upper bits)
    [0xdead_beef_cafe_ba5eu64 as i64, 0, 0, 0], // low byte 0x5e, low half 0xba5e
    [0x1234_5678_9abc_def0u64 as i64, 0, 0, 0], // low byte 0xf0, low half 0xdef0
    [-1, 0, 0, 0],                              // all ones: i8 8, i16 16
];

#[test]
fn ctpop_trunc_i8_zext_matches_reference() {
    let m = build4("ctpop_narrow_i8", |fb, x| {
        let t = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, x[0]);
        let p = fb.ctpop(Ty::I8, t);
        fb.cast(CastOp::ZExt, Ty::I8, Ty::I64, p)
    });
    check("ctpop_trunc_i8_zext", &m, ROWS, |row| {
        (row[0] as u8).count_ones() as i64
    });
}

#[test]
fn ctpop_trunc_i16_zext_matches_reference() {
    let m = build4("ctpop_narrow_i16", |fb, x| {
        let t = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, x[0]);
        let p = fb.ctpop(Ty::I16, t);
        fb.cast(CastOp::ZExt, Ty::I16, Ty::I64, p)
    });
    check("ctpop_trunc_i16_zext", &m, ROWS, |row| {
        (row[0] as u16).count_ones() as i64
    });
}
