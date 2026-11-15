// trust-cg-codegen - CSEL->CSINC fold on a select whose two arms are one register
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `csinc-fold` (`if_convert::CsincFold`) rewrites `Csel d, T, v, cc` with
//! `v = AddRI t, #1` into `Csinc d, T, t, cc` and deletes the add. That is
//! sound only when the rewritten operand is the ONLY read of `v` in the
//! function. A select whose two arms are the same register, `Csel d, v, v,
//! cc`, reads `v` twice: folding one operand and deleting the add leaves the
//! other reading a register no instruction defines. The fold counts reads per
//! operand (`effects::build_vreg_read_counts`) and leaves that select alone.
//!
//! `if-convert` produces exactly that select (`Csel m, x, x, eq`) from a loop
//! diamond whose two arms forward the same value to the join, and its loop
//! admission accepts it because the branch tests the merged value's previous
//! iteration. The declarative rewrite that folds `Csel d, x, x` runs before
//! `if-convert`, so the select reaches `csinc-fold` intact. The rows below
//! JIT-run, at O2 and O3,
//!
//! ```text
//! m = a
//! for _ in 0..(c & 63) {
//!     x = f(m)                // f(m) = m + 1, or (m - 5) + 1
//!     m = if m & 1 == 0 { x } else { x }   // or { m } on the odd arm
//! }
//! return m
//! ```
//!
//! compare with a plain Rust model and with the trust-ir interpreter, and
//! require `if-convert` to have changed the function, so the select reaches
//! `csinc-fold`. The row whose odd arm keeps `m` is the positive control:
//! `csinc-fold` must still fold its one-read increment. Host-bounded
//! executions: tests, not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, InterpretOptions, InterpretValue, Interpreter, Ty};
use trust_ir_build::ModuleBuilder;

const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};
const ENTRY: &str = "same_arm_select";

/// What the loop body computes before the diamond.
#[derive(Clone, Copy, Debug)]
enum Step {
    /// `x = m + 1`.
    Inc,
    /// `x = (m - 5) + 1`.
    SubThenInc,
}

impl Step {
    fn apply(self, m: u64) -> u64 {
        match self {
            Step::Inc => m.wrapping_add(1),
            Step::SubThenInc => m.wrapping_sub(5).wrapping_add(1),
        }
    }
}

/// What the odd (`m & 1 != 0`) arm forwards to the latch.
#[derive(Clone, Copy, Debug)]
enum OddArm {
    /// `x`, the even arm's value: `Csel m, x, x`.
    Same,
    /// `m` itself: `Csel m, x, m`, a one-read increment `csinc-fold` folds.
    Keep,
}

/// The Rust model of [`build_module`].
fn model(step: Step, odd: OddArm, a: u64, c: u64) -> u64 {
    let mut m = a;
    for _ in 0..(c & 63) {
        m = match odd {
            OddArm::Keep if m & 1 != 0 => m,
            _ => step.apply(m),
        };
    }
    m
}

/// `same_arm_select(a, c)`: header `H(m, i)`, body `x = f(m)` and a diamond
/// on `m & 1 == 0` whose two arms both branch to the latch `L(..)`.
fn build_module(step: Step, odd: OddArm) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_csinc_fold_identical_select_arms");
    let ty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let c = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let m = fb.add_block_param(header, Ty::U64);
    let i = fb.add_block_param(header, Ty::U64);
    let body = fb.create_block();
    let even_arm = fb.create_block();
    let odd_arm = fb.create_block();
    let latch = fb.create_block();
    let merged = fb.add_block_param(latch, Ty::U64);
    let exit = fb.create_block();
    let result = fb.add_block_param(exit, Ty::U64);

    fb.switch_to_block(entry);
    let mask = fb.iconst(Ty::U64, 63);
    let n = fb.binop(BinOp::And, Ty::U64, c, mask);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![a, zero]);

    fb.switch_to_block(header);
    let go = fb.icmp(ICmpOp::Ult, Ty::U64, i, n);
    fb.condbr(go, body, vec![], exit, vec![m]);

    fb.switch_to_block(body);
    let one = fb.iconst(Ty::U64, 1);
    let x = match step {
        Step::Inc => fb.binop(BinOp::Add, Ty::U64, m, one),
        Step::SubThenInc => {
            let five = fb.iconst(Ty::U64, 5);
            let y = fb.binop(BinOp::Sub, Ty::U64, m, five);
            fb.binop(BinOp::Add, Ty::U64, y, one)
        }
    };
    let bit = fb.binop(BinOp::And, Ty::U64, m, one);
    let zero = fb.iconst(Ty::U64, 0);
    let even = fb.icmp(ICmpOp::Eq, Ty::U64, bit, zero);
    fb.condbr(even, even_arm, vec![], odd_arm, vec![]);

    fb.switch_to_block(even_arm);
    fb.br(latch, vec![x]);
    fb.switch_to_block(odd_arm);
    match odd {
        OddArm::Same => fb.br(latch, vec![x]),
        OddArm::Keep => fb.br(latch, vec![m]),
    }

    fb.switch_to_block(latch);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.br(header, vec![merged, next]);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Changing runs of `pass` when `module` is prepared at `opt_level` with
/// every pass enabled.
fn pass_changes(module: &trust_ir::Module, opt_level: OptLevel, pass: &str) -> u32 {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("lowering");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    });
    let mut changes = 0;
    for (function, _) in &lowered {
        let (_, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .expect("prepare");
        for (name, count) in &metrics.optimization_pass_changes {
            if name == pass {
                changes += count;
            }
        }
    }
    changes
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> Result<JitCompilationResult, String> {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .map_err(|error| error.to_string())
}

fn interpret(module: &trust_ir::Module, a: u64, c: u64) -> u64 {
    let func = module.function_by_name(ENTRY).expect("entry");
    let args: Vec<InterpretValue> = [a, c]
        .iter()
        .map(|&v| InterpretValue::int(Ty::U64, i128::from(v)).expect("u64 argument"))
        .collect();
    let outcome = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 8,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(func.id, args)
        .expect("interpreter run");
    outcome.returns[0]
        .as_int()
        .expect("integer return")
        .as_unsigned() as u64
}

const INPUTS: [u64; 8] = [
    0,
    1,
    2,
    7,
    0x7fff_ffff_ffff_fffe,
    0x8000_0000_0000_0000,
    u64::MAX - 1,
    u64::MAX,
];
const COUNTS: [u64; 6] = [0, 1, 2, 3, 17, 63];

fn check(step: Step, odd: OddArm) {
    let module = build_module(step, odd);
    let required: &[&str] = match odd {
        OddArm::Same => &["if-convert"],
        OddArm::Keep => &["if-convert", "csinc-fold"],
    };
    let mut failures = Vec::new();
    for level in [OptLevel::O2, OptLevel::O3] {
        for pass in required {
            if pass_changes(&module, level, pass) == 0 {
                failures.push(format!(
                    "{step:?} {odd:?} {level:?}: {pass} did not change the function"
                ));
            }
        }
        let compiled = match jit(&module, level) {
            Ok(compiled) => compiled,
            Err(error) => {
                failures.push(format!("{step:?} {odd:?} {level:?}: refused: {error}"));
                continue;
            }
        };
        let kernel = unsafe {
            compiled
                .buffer
                .get_fn_bound::<extern "C" fn(u64, u64) -> u64>(ENTRY)
        }
        .expect("entry symbol");
        for a in INPUTS {
            for c in COUNTS {
                let want = model(step, odd, a, c);
                assert_eq!(
                    interpret(&module, a, c),
                    want,
                    "model disagrees with the interpreter"
                );
                let got = kernel.as_ref()(a, c);
                if got != want {
                    failures.push(format!(
                        "{step:?} {odd:?} {level:?} a={a:#x} c={c}: got {got:#x}, want {want:#x}"
                    ));
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `x = m + 1` on both arms: `Csel m, x, x` reads `x` twice and must keep the
/// add that defines it.
#[test]
fn same_increment_on_both_arms() {
    check(Step::Inc, OddArm::Same);
}

/// `x = (m - 5) + 1` on both arms: the base would be the subtraction's result.
#[test]
fn same_offset_increment_on_both_arms() {
    check(Step::SubThenInc, OddArm::Same);
}

/// `x = m + 1` on the even arm only: `Csel m, x, m` reads `x` once, and the
/// fold to `Csinc` still fires.
#[test]
fn increment_on_one_arm_still_folds() {
    check(Step::Inc, OddArm::Keep);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
