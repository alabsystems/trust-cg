// trust-cg-fuzz/tests/verify_narrow_int_0.rs
//
// INDEPENDENT VERIFICATION of a claimed "narrow_int" miscompile:
//   fuzz_fn(a,b,_,_) = sext_i64( trunc_i8(a) SDiv trunc_i8(b) )
// Claim: i8 SDiv with a=42, b=-41 should be -1 (oracle), but all 8 JIT configs
// return 0 (== unsigned 42/215). Verify across O0/O1/O2/O3 x {std,fast} +
// interpreter oracle.
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

fn all_jit_runs(m: &trust_ir::Module, row: &[i64; 4]) -> Vec<(String, Run)> {
    let mut out = Vec::new();
    for &fast in &[false, true] {
        for &opt in &OPTS {
            let tag = format!("{:?}/{}", opt, if fast { "fast" } else { "std" });
            out.push((tag, jit_run(m, opt, fast, row)));
        }
    }
    out
}

/// EXACT module from the claim:
/// fuzz_fn(a,b,_,_) = sext_i64( trunc_<nty>(a) SDiv trunc_<nty>(b) )
fn build_module(nty: Ty, op: BinOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let na = fb.trunc(Ty::I64, nty.clone(), a);
    let nb = fb.trunc(Ty::I64, nty.clone(), b);
    let r = fb.binop(op, nty.clone(), na, nb);
    let wide = fb.sext(nty.clone(), Ty::I64, r);
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

#[test]
fn verify_narrow_int_0() {
    // (label, narrow type, op, [a,b,_,_], claimed-correct value)
    let cases: &[(&str, Ty, BinOp, [i64; 4], i64)] = &[
        ("i8 SDiv 42/-41", Ty::I8, BinOp::SDiv, [42, -41, 0, 0], -1),
        ("i8 SDiv -100/7", Ty::I8, BinOp::SDiv, [-100, 7, 0, 0], -14),
        ("i8 SDiv -100/-7", Ty::I8, BinOp::SDiv, [-100, -7, 0, 0], 14),
        ("i16 SDiv 42/-41", Ty::I16, BinOp::SDiv, [42, -41, 0, 0], -1),
        // i32 control: claim says NOT affected.
        ("i32 SDiv 42/-41", Ty::I32, BinOp::SDiv, [42, -41, 0, 0], -1),
    ];

    let mut findings: Vec<String> = Vec::new();
    let mut configs = 0usize;

    for (label, nty, op, row, claimed) in cases {
        let m = build_module(nty.clone(), *op);
        let oracle = run_oracle_one(&m, row);
        let runs = all_jit_runs(&m, row);
        configs += runs.len();

        // Gather JIT values + agreement.
        let mut jit_values: Vec<(String, i64)> = Vec::new();
        for (tag, r) in &runs {
            match r {
                Run::Value(v) => jit_values.push((tag.clone(), *v)),
                Run::CompileErr => findings.push(format!("{label}: {tag} COMPILE_ERROR")),
                Run::SymbolMissing => findings.push(format!("{label}: {tag} SYMBOL_MISSING")),
                Run::Panic => findings.push(format!("{label}: {tag} PANIC")),
            }
        }
        let first = jit_values.first().cloned();
        let all_agree = match &first {
            Some((_, v0)) => jit_values.iter().all(|(_, v)| v == v0),
            None => false,
        };

        eprintln!(
            "{label}: oracle={:?} claimed={} jit_values={:?} all8agree={}",
            oracle, claimed, jit_values, all_agree
        );

        // Record oracle-vs-JIT mismatch (the real defect signal).
        if let (Ok(ov), Some((tag0, v0))) = (&oracle, &first)
            && ov != v0
        {
            findings.push(format!(
                "{label}: ORACLE={ov} vs JIT({tag0})={v0} (all8agree={all_agree})"
            ));
        }
        // Cross-JIT disagreement is its own (different) defect class.
        if let Some((tag0, v0)) = &first {
            for (tag, v) in &jit_values {
                if v != v0 {
                    findings.push(format!("{label}: JIT DISAGREE {tag0}={v0} vs {tag}={v}"));
                }
            }
        }
    }

    eprintln!(
        "verify_narrow_int_0: {} configs, {} findings",
        configs,
        findings.len()
    );
    for f in &findings {
        eprintln!("  FINDING: {f}");
    }

    // This test is a VERIFICATION probe: we EXPECT the claimed defect to
    // reproduce, so findings should be non-empty if the claim is real.
    // We do not fail the test either way; the eprintln output is the evidence.
}
