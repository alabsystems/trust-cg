// verify_narrow_int_1.rs
//
// Independent verification of a claimed "narrow_int" miscompile:
//   fuzz_fn(a,b,_,_) = sext_i64( trunc_i8(a) SRem trunc_i8(b) )
//   Claim: narrow signed remainder (SRem) on i8/i16 is computed as if the
//   operands were unsigned (URem) because narrow operands are not sign-extended
//   before the 32-bit signed remainder computation.
//   Witness: i8 SRem a=42, b=-41 -> correct 1, claimed JIT returns 42.
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

/// EXACT module from the claimed repro:
///   fuzz_fn(a,b,_,_) = sext_i64( trunc_i8(a) SRem trunc_i8(b) )
fn build_module_srem(nty: Ty) -> trust_ir::Module {
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
    let r = fb.binop(BinOp::SRem, nty.clone(), na, nb);
    let wide = fb.sext(nty, Ty::I64, r);
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

fn check(label: &str, nty: Ty, a: i64, b: i64, expect_correct: i64) -> Vec<String> {
    let m = build_module_srem(nty);
    let row = [a, b, 0, 0];
    let mut defects = Vec::new();

    let oracle = run_oracle_one(&m, &row);
    eprintln!("[{label}] inputs a={a} b={b}  oracle={oracle:?}  (correct={expect_correct})");

    let runs = all_jit_runs(&m, &row);
    let mut values = Vec::new();
    for (tag, r) in &runs {
        eprintln!("    {tag:>10}: {r:?}");
        if let Run::Value(v) = r {
            values.push(*v);
        }
        if matches!(r, Run::CompileErr | Run::SymbolMissing | Run::Panic) {
            defects.push(format!("[{label}] {tag} -> {r:?} (non-value)"));
        }
    }

    // Compare oracle (if Ok) against every JIT value.
    if let Ok(ov) = oracle {
        for (tag, r) in &runs {
            if let Run::Value(v) = r
                && *v != ov
            {
                defects.push(format!(
                    "[{label}] oracle={ov} but {tag}={v} (inputs a={a} b={b})"
                ));
            }
        }
    }
    // Cross-config agreement among JIT values (oracle-free check).
    if let Some(&first) = values.first()
        && values.iter().any(|&v| v != first)
    {
        defects.push(format!("[{label}] JIT configs disagree: {values:?}"));
    }
    defects
}

#[test]
fn verify_narrow_int_1_srem_signedness() {
    let mut defects = Vec::new();

    // The exact claimed witness.
    defects.extend(check("i8 42%-41", Ty::I8, 42, -41, 1));
    // Additional claimed witnesses.
    defects.extend(check("i8 100%-7", Ty::I8, 100, -7, 2));
    defects.extend(check("i16 42%-41", Ty::I16, 42, -41, 1));

    // Extra signed-remainder probes (nonzero divisor, no INT_MIN/-1 edge).
    defects.extend(check("i8 -42%5", Ty::I8, -42, 5, -2));
    defects.extend(check("i8 -100%7", Ty::I8, -100, 7, -2));
    defects.extend(check("i16 -1000%37", Ty::I16, -1000, 37, -1000 % 37));
    defects.extend(check("i32 -42%-41", Ty::I32, -42, -41, -42 % -41));

    eprintln!(
        "verify_narrow_int_1: 8 configs x several rows, {} defects",
        defects.len()
    );
    for d in &defects {
        eprintln!("DEFECT: {d}");
    }
    assert!(defects.is_empty(), "narrow_int SRem defects: {defects:#?}");
}
