// trust-cg-fuzz/tests/fp_const_and_fcmp.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Regressions for two FP codegen defects found by the int_fp_mix differential
// sweep:
//  1. A floating-point constant outside the AArch64 FMOV-immediate range
//     (including 0.0) was silently materialized as +2.0, because the 8-bit
//     immediate encoder returns 0 (= +2.0) for non-encodable values and
//     select_fconst emitted FMOV-immediate unconditionally. Now non-encodable
//     constants are materialized via GPR bit pattern + FMOV.
//  2. FCmpOp::UEq feeding a select failed to encode (`Csinc` with an `Imm`
//     operand where a register is required). UEq has no single AArch64
//     condition code; it is now lowered as `CSET eq; CSET vs; ORR`.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::run_oracle_one;
use trust_ir::{CastOp, FCmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn jit(module: &trust_ir::Module, opt: OptLevel, fast: bool, row: [i64; 4]) -> i64 {
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
        .expect("compile")
        .buffer;
    let f = unsafe { buf.get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>("fuzz_fn") }
        .expect("symbol")
        .into_inner();
    let v = f(row[0], row[1], row[2], row[3]);
    drop(buf);
    v
}

/// `fuzz_fn(_,_,_,_) = (i64) fptosi(fconst ty K)`.
fn build_fconst(ty: Ty, k: f64) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("fc");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", entry_ty);
    let e = fb.create_block();
    for _ in 0..4 {
        fb.add_block_param(e, Ty::I64);
    }
    fb.switch_to_block(e);
    let c = fb.fconst(ty.clone(), k);
    let r = fb.cast(CastOp::FPToSI, ty, Ty::I64, c);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

#[test]
fn non_encodable_fp_constants_materialize_correctly() {
    // Every one of these is outside the FMOV-immediate range (or is 0.0), so it
    // exercised the broken path. fptosi truncates toward zero.
    let f64_vals: &[f64] = &[
        0.0,
        32.0,
        50.0,
        100.0,
        1000.0,
        1_000_000.0,
        -100.0,
        -1_000_000.0,
        3.7,
        -3.7,
        0.0,
        12345.0,
        65536.0,
        0.25, // 0.25 IS encodable — sanity that the encodable path still works
        1.0,
        2.0,
        31.0,
        -1.5,
    ];
    for ty in [Ty::F64, Ty::F32] {
        for &k in f64_vals {
            let m = build_fconst(ty.clone(), k);
            let oracle = run_oracle_one(&m, &[0, 0, 0, 0]).expect("oracle");
            for fast in [true, false] {
                for opt in OPTS {
                    let got = jit(&m, opt, fast, [0, 0, 0, 0]);
                    assert_eq!(
                        got, oracle,
                        "fconst {ty:?} {k}: opt={opt:?} fast={fast} got={got} want={oracle}"
                    );
                }
            }
        }
    }
}

/// `fuzz_fn(a,b,c,d) = select(fcmp(pred, (f)a, (f)b), c, d)`.
fn build_fcmp_select(pred: FCmpOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("fcs");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let fa = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, a);
    let fbv = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, b);
    let cond = fb.fcmp(pred, Ty::F64, fa, fbv);
    let sel = fb.select(Ty::I64, cond, c, d);
    fb.ret(vec![sel]);
    fb.build();
    mb.build()
}

#[test]
fn all_fcmp_predicates_compile_and_match_oracle() {
    use FCmpOp::*;
    let preds = [OEq, ONe, OLt, OLe, OGt, OGe, UEq, UNe, ULt, ULe, UGt, UGe];
    let rows: [[i64; 4]; 5] = [
        [1, 1, 7, 9],
        [1, 2, 7, 9],
        [2, 1, 7, 9],
        [-3, -3, 7, 9],
        [0, 5, 7, 9],
    ];
    for pred in preds {
        let m = build_fcmp_select(pred);
        for row in rows {
            let oracle = run_oracle_one(&m, &row).expect("oracle");
            for fast in [true, false] {
                for opt in OPTS {
                    let got = jit(&m, opt, fast, row);
                    assert_eq!(
                        got, oracle,
                        "fcmp {pred:?} row={row:?}: opt={opt:?} fast={fast} got={got} want={oracle}"
                    );
                }
            }
        }
    }
}
