// trust-cg-fuzz/tests/verify_narrow_int_2.rs
//
// INDEPENDENT VERIFICATION of a claimed "narrow_int" miscompile:
//   fuzz_fn(a,b,_,_) = sext_i64( trunc_i8(a) AShr trunc_i8(b) )
//   Call with a=-1, b=1. Correct = -1; trust-cg allegedly returns 127.
//
// Reproduces the EXACT module from the claim, runs O0/O1/O2/O3 x {std,fast}
// allocators + the interpreter oracle, and decides real-defect vs artifact.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::panic;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::run_oracle_one;
use trust_ir::{BinOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "fuzz_fn";

#[derive(Debug, Clone, PartialEq, Eq)]
enum Run {
    Value(i64),
    CompileErr,
    SymbolMissing,
    Panic,
}

fn jit_run(m: &trust_ir::Module, opt: OptLevel, fast: bool, row: &[i64; 4]) -> Run {
    let ext: HashMap<String, *const u8> = HashMap::new();
    let mut cfg = if fast {
        CompilerConfig::jit_fast(Target::host())
    } else {
        let mut c = CompilerConfig::for_host_jit();
        c.enable_jit_fast_regalloc = false;
        c
    };
    cfg.opt_level = opt;

    let compiled = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        Compiler::new(cfg)
            .compile_module_to_jit(m, &ext)
            .map_err(Box::new)
    }));
    let buf = match compiled {
        Ok(Ok(r)) => r.buffer,
        Ok(Err(_)) => return Run::CompileErr,
        Err(_) => return Run::Panic,
    };
    let f = match unsafe { buf.get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>(ENTRY) } {
        Some(p) => p.into_inner(),
        None => return Run::SymbolMissing,
    };
    let called = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        f(row[0], row[1], row[2], row[3])
    }));
    let out = match called {
        Ok(v) => Run::Value(v),
        Err(_) => Run::Panic,
    };
    drop(buf);
    out
}

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// EXACT module from the claim:
///   fuzz_fn(a,b,_,_) = sext_i64( trunc_i8(a) AShr trunc_i8(b) )
fn build_module_i8_ashr() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let na = fb.trunc(Ty::I64, Ty::I8, a);
    let nb = fb.trunc(Ty::I64, Ty::I8, b);
    let r = fb.binop(BinOp::AShr, Ty::I8, na, nb);
    let wide = fb.sext(Ty::I8, Ty::I64, r);
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

/// i16 variant: sext_i64( trunc_i16(a) AShr trunc_i16(b) )
fn build_module_i16_ashr() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let na = fb.trunc(Ty::I64, Ty::I16, a);
    let nb = fb.trunc(Ty::I64, Ty::I16, b);
    let r = fb.binop(BinOp::AShr, Ty::I16, na, nb);
    let wide = fb.sext(Ty::I16, Ty::I64, r);
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

/// i32 control: sext_i64( trunc_i32(a) AShr trunc_i32(b) ). Should be correct
/// (value fills the lane), so this isolates the narrow-source hypothesis.
fn build_module_i32_ashr() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let na = fb.trunc(Ty::I64, Ty::I32, a);
    let nb = fb.trunc(Ty::I64, Ty::I32, b);
    let r = fb.binop(BinOp::AShr, Ty::I32, na, nb);
    let wide = fb.sext(Ty::I32, Ty::I64, r);
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

fn report_case(label: &str, m: &trust_ir::Module, row: &[i64; 4], expect: i64) -> bool {
    let oracle = run_oracle_one(m, row);
    eprintln!("=== {label} row={row:?} hand-expected={expect} ===");
    eprintln!("  oracle = {oracle:?}");
    let mut any_wrong = false;
    let mut first: Option<i64> = None;
    let mut all_agree = true;
    for &fast in &[false, true] {
        for &opt in &OPTS {
            let tag = format!("{:?}/{}", opt, if fast { "fast" } else { "std" });
            let r = jit_run(m, opt, fast, row);
            if let Run::Value(v) = r {
                match first {
                    None => first = Some(v),
                    Some(f0) => {
                        if v != f0 {
                            all_agree = false;
                        }
                    }
                }
                if v != expect {
                    any_wrong = true;
                }
            }
            eprintln!("  jit[{tag}] = {r:?}");
        }
    }
    eprintln!(
        "  -> all8_agree={all_agree} first_jit={:?} matches_oracle={:?}",
        first,
        match (first, &oracle) {
            (Some(v), Ok(o)) => Some(v == *o),
            _ => None,
        }
    );
    any_wrong
}

#[test]
fn verify_narrow_ashr_claim() {
    // The headline witness.
    let i8m = build_module_i8_ashr();
    report_case("i8 AShr", &i8m, &[-1, 1, 0, 0], -1);
    report_case("i8 AShr", &i8m, &[-2, 1, 0, 0], -1);

    let i16m = build_module_i16_ashr();
    report_case("i16 AShr", &i16m, &[-2, 1, 0, 0], -1);

    let i32m = build_module_i32_ashr();
    // i32: -2 >> 1 (arith) = -1. Control: expect correct.
    report_case("i32 AShr (control)", &i32m, &[-2, 1, 0, 0], -1);

    // Oracle sanity: oracle MUST be -1 for the i8 witness.
    let oracle = run_oracle_one(&i8m, &[-1, 1, 0, 0]);
    assert_eq!(
        oracle,
        Ok(-1),
        "oracle must compute arithmetic shift correctly"
    );

    // Now decide: do all 8 JIT configs return 127 (= logical shift)?
    let mut jit_vals = Vec::new();
    for &fast in &[false, true] {
        for &opt in &OPTS {
            if let Run::Value(v) = jit_run(&i8m, opt, fast, &[-1, 1, 0, 0]) {
                jit_vals.push(v);
            }
        }
    }
    eprintln!("i8 AShr -1>>1 : oracle=-1, jit_vals={jit_vals:?}");
    let all_127 = !jit_vals.is_empty() && jit_vals.iter().all(|&v| v == 127);
    let all_neg1 = !jit_vals.is_empty() && jit_vals.iter().all(|&v| v == -1);
    eprintln!("VERDICT-DATA: all_127={all_127} all_neg1={all_neg1}");
}
