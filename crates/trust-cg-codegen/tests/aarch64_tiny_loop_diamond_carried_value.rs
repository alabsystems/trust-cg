// trust-cg-codegen - tiny-loop-diamond hoisting a write to a loop-carried value
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `tiny-loop-diamond` (`if_convert::TinyLoopDiamondConvert`) hoists the
//! non-final instructions of its compute arm (one pure compute and at most one
//! `MovR`, then `MovR merge, value`) into the diamond header, where they run on
//! BOTH paths, and merges with `Csel merge, value, identity, cc`. That is
//! sound only when every register the hoisted code defines is local to the
//! compute arm: not read by the identity arm, after the diamond, or by the
//! compute arm itself before the arm writes it, as a register carried around
//! the loop would be (`if_convert::arm_defs_observable`).
//!
//! When the arms branch straight back to the loop header, the compute arm's
//! hoisted part can be the edge copy into a loop-carried header parameter
//! (`EorRR t, p, k; MovR p, t`). A parameter the identity arm forwards
//! unchanged gets no copy on that arm, so hoisting the copy would make the
//! identity path overwrite it too, and `Csel m, q, p` would read the
//! overwritten `p`. Even when no arm forwards `p`, the compute arm reads it on
//! a later iteration. The pass must leave those diamonds branchy.
//!
//! Every row has the shape
//!
//! ```text
//! p = b; m = a | 1
//! for _ in 0..(c & 63) {                   // counter in a stack slot
//!     q = xorshift(m)                      // m ^= m << 13; m ^= m >> 7
//!     if (m & 6) == 2 { (p, m) = compute } else { (p, m) = identity }
//! }
//! return m
//! ```
//!
//! whose condition reaches the EOR self-recurrence the pass requires, and is
//! JIT-run at O2 and O3 against a plain Rust model and the trust-ir
//! interpreter. The `RotateAccumulator` row is the positive control: its arms
//! go through a latch, the hoisted rotate writes only an arm-local temp, and
//! `tiny-loop-diamond` must still convert it. Host-bounded executions: tests,
//! not a proof.
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
const ENTRY: &str = "carried_diamond";
const PASS: &str = "tiny-loop-diamond";
const KEY: u64 = 0x5555;

/// The two arms' outgoing `(p, m)` header arguments.
#[derive(Clone, Copy, Debug)]
enum Row {
    /// Taken: `(rotl(p, 7), q)`; not taken: `(p, p)`.
    RotateThenForward,
    /// Taken: `(p ^ KEY, q)`; not taken: `(p, p)`.
    XorThenForward,
    /// As `XorThenForward` with the condition inverted, so the identity arm is
    /// the branch target.
    XorThenForwardInverted,
    /// Taken: `(p ^ KEY, p ^ KEY)`; not taken: `(p, q)`. Only the compute arm
    /// reads `p`, on the next iteration.
    XorCarriedOnly,
    /// Positive control: both arms go to a latch `L(x)` with taken `x =
    /// rotl(p, 7)` and not taken `x = p`, and the latch continues with `(x,
    /// q)`. The loop returns `p`.
    RotateAccumulator,
}

fn xorshift(m: u64) -> u64 {
    let q = m ^ (m << 13);
    q ^ (q >> 7)
}

/// The Rust model of [`build_module`].
fn model(row: Row, a: u64, b: u64, c: u64) -> u64 {
    let (mut p, mut m) = (b, a | 1);
    for _ in 0..(c & 63) {
        let q = xorshift(m);
        let cond = m & 6 == 2;
        (p, m) = match row {
            Row::RotateThenForward if cond => (p.rotate_left(7), q),
            Row::XorThenForward if cond => (p ^ KEY, q),
            Row::XorThenForwardInverted if !cond => (p ^ KEY, q),
            Row::XorCarriedOnly if cond => (p ^ KEY, p ^ KEY),
            Row::XorCarriedOnly => (p, q),
            Row::RotateAccumulator if cond => (p.rotate_left(7), q),
            Row::RotateAccumulator => (p, q),
            _ => (p, p),
        };
    }
    match row {
        Row::RotateAccumulator => p,
        _ => m,
    }
}

/// `carried_diamond(a, b, c)`; see the module docs.
fn build_module(row: Row) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_tiny_loop_diamond_carried_value");
    let ty = mb.add_func_type(vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    let c = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let p = fb.add_block_param(header, Ty::U64);
    let m = fb.add_block_param(header, Ty::U64);
    let body = fb.create_block();
    let compute = fb.create_block();
    let identity = fb.create_block();
    let exit = fb.create_block();
    let result = fb.add_block_param(exit, Ty::U64);
    // Only the positive control has a latch; the other rows' arms branch
    // straight back to the header.
    let latch = matches!(row, Row::RotateAccumulator).then(|| {
        let latch = fb.create_block();
        (latch, fb.add_block_param(latch, Ty::U64))
    });

    fb.switch_to_block(entry);
    let mask = fb.iconst(Ty::U64, 63);
    let n = fb.binop(BinOp::And, Ty::U64, c, mask);
    let counter = fb.alloca(Ty::U64);
    let zero = fb.iconst(Ty::U64, 0);
    fb.store(Ty::U64, counter, zero);
    let one = fb.iconst(Ty::U64, 1);
    let m0 = fb.binop(BinOp::Or, Ty::U64, a, one);
    fb.br(header, vec![b, m0]);

    fb.switch_to_block(header);
    let i = fb.load(Ty::U64, counter);
    let done = fb.icmp(ICmpOp::Uge, Ty::U64, i, n);
    let out = match row {
        Row::RotateAccumulator => p,
        _ => m,
    };
    fb.condbr(done, exit, vec![out], body, vec![]);

    fb.switch_to_block(body);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.store(Ty::U64, counter, next);
    let k13 = fb.iconst(Ty::U64, 13);
    let shifted = fb.binop(BinOp::Shl, Ty::U64, m, k13);
    let q = fb.binop(BinOp::Xor, Ty::U64, m, shifted);
    let k7 = fb.iconst(Ty::U64, 7);
    let shifted = fb.binop(BinOp::LShr, Ty::U64, q, k7);
    let q = fb.binop(BinOp::Xor, Ty::U64, q, shifted);
    let k6 = fb.iconst(Ty::U64, 6);
    let bits = fb.binop(BinOp::And, Ty::U64, m, k6);
    let k2 = fb.iconst(Ty::U64, 2);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U64, bits, k2);
    match row {
        Row::XorThenForwardInverted => fb.condbr(cond, identity, vec![], compute, vec![]),
        _ => fb.condbr(cond, compute, vec![], identity, vec![]),
    }

    fb.switch_to_block(compute);
    let p_next = match row {
        Row::RotateThenForward | Row::RotateAccumulator => {
            let k = fb.iconst(Ty::U64, 7);
            fb.binop(BinOp::RotL, Ty::U64, p, k)
        }
        _ => {
            let k = fb.iconst(Ty::U64, i128::from(KEY));
            fb.binop(BinOp::Xor, Ty::U64, p, k)
        }
    };
    match (row, latch) {
        (_, Some((latch, _))) => fb.br(latch, vec![p_next]),
        (Row::XorCarriedOnly, None) => fb.br(header, vec![p_next, p_next]),
        (_, None) => fb.br(header, vec![p_next, q]),
    }

    fb.switch_to_block(identity);
    match (row, latch) {
        (_, Some((latch, _))) => fb.br(latch, vec![p]),
        (Row::XorCarriedOnly, None) => fb.br(header, vec![p, q]),
        (_, None) => fb.br(header, vec![p, p]),
    }

    if let Some((latch, accumulated)) = latch {
        fb.switch_to_block(latch);
        fb.br(header, vec![accumulated, q]);
    }

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

fn interpret(module: &trust_ir::Module, args: [u64; 3]) -> u64 {
    let func = module.function_by_name(ENTRY).expect("entry");
    let args: Vec<InterpretValue> = args
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

const INPUTS: [u64; 7] = [0, 1, 2, 5, 0xdead_beef, 0x8000_0000_0000_0000, u64::MAX];
const COUNTS: [u64; 6] = [0, 1, 2, 7, 31, 63];

fn check(row: Row) {
    let module = build_module(row);
    let mut failures = Vec::new();
    for level in [OptLevel::O2, OptLevel::O3] {
        let changes = pass_changes(&module, level, PASS);
        match row {
            Row::RotateAccumulator if changes == 0 => failures.push(format!(
                "{row:?} {level:?}: {PASS} did not change the function"
            )),
            Row::RotateAccumulator => {}
            _ if changes != 0 => failures.push(format!(
                "{row:?} {level:?}: {PASS} hoisted a loop-carried write ({changes} changes)"
            )),
            _ => {}
        }
        let compiled = match jit(&module, level) {
            Ok(compiled) => compiled,
            Err(error) => {
                failures.push(format!("{row:?} {level:?}: refused: {error}"));
                continue;
            }
        };
        let kernel = unsafe {
            compiled
                .buffer
                .get_fn_bound::<extern "C" fn(u64, u64, u64) -> u64>(ENTRY)
        }
        .expect("entry symbol");
        for a in INPUTS {
            for b in INPUTS {
                for c in COUNTS {
                    let want = model(row, a, b, c);
                    assert_eq!(
                        interpret(&module, [a, b, c]),
                        want,
                        "model disagrees with the interpreter"
                    );
                    let got = kernel.as_ref()(a, b, c);
                    if got != want {
                        failures.push(format!(
                            "{row:?} {level:?} a={a:#x} b={b:#x} c={c}: got {got:#x}, want {want:#x}"
                        ));
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The identity arm forwards `p`, which a hoisted `RorRI t, p; MovR p, t`
/// would already have rotated.
#[test]
fn rotate_arm_overwrites_forwarded_parameter() {
    check(Row::RotateThenForward);
}

/// The identity arm forwards `p`, which a hoisted `EorRR t, p, k; MovR p, t`
/// would already have changed.
#[test]
fn xor_arm_overwrites_forwarded_parameter() {
    check(Row::XorThenForward);
}

/// As above with the identity arm as the branch target.
#[test]
fn xor_arm_overwrites_forwarded_parameter_inverted() {
    check(Row::XorThenForwardInverted);
}

/// No arm forwards `p`; a hoisted `MovR p, t` would still run on the identity
/// path, and the compute arm would read the changed `p` on a later iteration.
#[test]
fn xor_arm_advances_parameter_on_identity_path() {
    check(Row::XorCarriedOnly);
}

/// The rotate writes an arm-local temp the latch copy reads through the merge:
/// the pass still converts this diamond.
#[test]
fn rotate_accumulator_through_a_latch_still_converts() {
    check(Row::RotateAccumulator);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
