// trust-cg-codegen - rotated reduction loops whose exit reads pre-step state
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = START; acc = 0; loop { sum = acc + a[i]; if i + 1 >= n { *out = sum;
//! return i } acc = sum; i += 1 }` — a rotated (bottom-tested) `i32` sum
//! whose exit reads the induction `i`, the value BEFORE the step — run
//! through the JIT at every optimization level against a scalar Rust
//! reference, with an `i32` and an `i64` index.
//!
//! Entered below its bound the loop returns `n - 1`. The NEON array-reduction
//! vectorizer (`neon_array`) rewrites this shape when the exit does not read
//! `i`. Its drain branches straight to the exit once every element is
//! consumed, holding `i = n`, one past the scalar loop's exit value.
//!
//! The accumulator is the same case: the exit leaves before `acc = sum`, so
//! an exit that stores `acc` instead of `sum` stores the sum of
//! `a[START..n-1)`, without the last element, while the drain holds the full
//! sum in both. That holds too when `acc` reaches the exit as a block argument
//! of a join that a guard skipping the loop also feeds. The cases are bounded
//! executions on the host, not a proof of the transform.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "rotated_sum";
/// Elements of `a`; the highest bound reads up to `a[179]`.
const LEN: usize = 192;
/// Bounds relative to the start: below, at, just past, and across multiples
/// of the vector widths, where the vector code consumes every element.
const DELTAS: [i64; 13] = [-25, -20, 0, 1, 7, 8, 9, 15, 16, 17, 32, 64, 160];

/// What the exit reads besides the stored value.
#[derive(Clone, Copy, Debug, PartialEq)]
enum ExitRead {
    /// Stores `sum` and returns the constant 7: no pre-step state is read.
    Nothing,
    /// Stores `sum` and returns `i`.
    Induction,
    /// Stores `acc`, the sum before this iteration's element, and returns 7.
    OldSum,
    /// The same through a join: a guard skips the loop unless `start < n`,
    /// and the exit takes `acc` from the loop, or 0 from the guard, as a
    /// block argument.
    GuardedOldSum,
}

/// The loop above with an `idx`-typed induction and bound, entered at
/// `start`, whose exit reads `read`.
fn sum_module(idx: Ty, start: i64, read: ExitRead) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_neon_array_rotated_live_iv");
    let sig = mb.add_func_type(vec![Ty::Ptr, idx.clone(), Ty::Ptr], vec![idx.clone()]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, idx.clone());
    let out = fb.add_block_param(entry, Ty::Ptr);
    let head = fb.create_block();
    let i = fb.add_block_param(head, idx.clone());
    let acc = fb.add_block_param(head, Ty::I32);
    let exit = fb.create_block();
    let guarded = read == ExitRead::GuardedOldSum;
    let joined = guarded.then(|| fb.add_block_param(exit, Ty::I32));

    fb.switch_to_block(entry);
    let first = fb.iconst(idx.clone(), i128::from(start));
    let zero = fb.iconst(Ty::I32, 0);
    if guarded {
        let enter = fb.icmp(ICmpOp::Slt, idx.clone(), first, n);
        fb.condbr(enter, head, vec![first, zero], exit, vec![zero]);
    } else {
        fb.br(head, vec![first, zero]);
    }

    fb.switch_to_block(head);
    let p = fb.gep(Ty::I32, a, vec![i]);
    let v = fb.load(Ty::I32, p);
    let sum = fb.binop(BinOp::Add, Ty::I32, acc, v);
    let one = fb.iconst(idx.clone(), 1);
    let next = fb.binop(BinOp::Add, idx.clone(), i, one);
    let done = fb.icmp(ICmpOp::Sge, idx.clone(), next, n);
    let leaving = if guarded { vec![acc] } else { vec![] };
    fb.condbr(done, exit, leaving, head, vec![next, sum]);

    fb.switch_to_block(exit);
    let stored = match (read, joined) {
        (_, Some(joined)) => joined,
        (ExitRead::OldSum, None) => acc,
        _ => sum,
    };
    fb.store(Ty::I32, out, stored);
    if read == ExitRead::Induction {
        fb.ret(vec![i]);
    } else {
        let seven = fb.iconst(idx, 7);
        fb.ret(vec![seven]);
    }
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Changing runs of `neon-array` over `module` in the `opt_level` pipeline.
fn neon_array_changes(module: &trust_ir::Module, opt_level: OptLevel) -> u32 {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("lowering");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        ..PipelineConfig::for_target("aarch64-apple-darwin")
    });
    let mut changes = 0;
    for (function, _) in &lowered {
        let (_, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        changes += metrics
            .optimization_pass_changes
            .iter()
            .filter(|(name, _)| name == "neon-array")
            .map(|(_, count)| count)
            .sum::<u32>();
    }
    changes
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

/// The scalar reference: the value it stores and the value it returns.
fn reference(a: &[i32], start: i64, n: i64, read: ExitRead) -> (i32, i64) {
    if read == ExitRead::GuardedOldSum && start >= n {
        return (0, 7);
    }
    let (mut acc, mut i) = (0i32, start);
    loop {
        let sum = acc.wrapping_add(a[i as usize]);
        if i + 1 >= n {
            return match read {
                ExitRead::Nothing => (sum, 7),
                ExitRead::Induction => (sum, i),
                ExitRead::OldSum | ExitRead::GuardedOldSum => (acc, 7),
            };
        }
        acc = sum;
        i += 1;
    }
}

/// Run the `read` module for `idx` at every level from each start, and
/// return one line per wrong stored or returned value.
fn mismatches(idx: Ty, read: ExitRead) -> Vec<String> {
    let mut wrong = Vec::new();
    for start in [0i64, 20] {
        let module = sum_module(idx.clone(), start, read);
        for opt_level in LEVELS {
            let result = jit(&module, opt_level);
            for delta in DELTAS {
                let n = start + delta;
                let a: Vec<i32> = (0..LEN as i32).map(|x| x * 3 + 1).collect();
                let (want_acc, want_ret) = reference(&a, start, n, read);
                let mut got_acc = 0i32;
                // The loop reads `a[start..max(n, start + 1))`, inside `a`,
                // and writes only `out`.
                let got_ret = if idx == Ty::I32 {
                    // SAFETY: the trust-ir signature is (ptr, i32, ptr) -> i32,
                    // and `result` outlives the call.
                    let kernel = unsafe {
                        result
                            .buffer
                            .get_fn_bound::<extern "C" fn(*const i32, i32, *mut i32) -> i32>(ENTRY)
                    }
                    .expect("entry symbol");
                    i64::from(kernel.as_ref()(a.as_ptr(), n as i32, &mut got_acc))
                } else {
                    // SAFETY: the trust-ir signature is (ptr, i64, ptr) -> i64,
                    // and `result` outlives the call.
                    let kernel = unsafe {
                        result
                            .buffer
                            .get_fn_bound::<extern "C" fn(*const i32, i64, *mut i32) -> i64>(ENTRY)
                    }
                    .expect("entry symbol");
                    kernel.as_ref()(a.as_ptr(), n, &mut got_acc)
                };
                if got_ret != want_ret || got_acc != want_acc {
                    wrong.push(format!(
                        "{idx:?} {read:?} start={start} {opt_level:?} n={n}: returned \
                         {got_ret} (want {want_ret}), stored {got_acc} (want {want_acc})"
                    ));
                }
            }
        }
    }
    wrong
}

/// The same loops with no pre-step state read at the exit are vectorized,
/// so the cases below run the shape the vector code covers.
#[test]
fn the_loop_without_the_read_is_vectorized_and_exact() {
    for idx in [Ty::I32, Ty::I64] {
        for start in [0i64, 20] {
            let module = sum_module(idx.clone(), start, ExitRead::Nothing);
            for opt_level in [OptLevel::O2, OptLevel::O3] {
                assert!(
                    neon_array_changes(&module, opt_level) > 0,
                    "{idx:?} start={start} {opt_level:?}: neon-array did not fire"
                );
            }
        }
        let wrong = mismatches(idx, ExitRead::Nothing);
        assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
    }
}

#[test]
fn a_rotated_sum_returns_its_last_index() {
    let mut wrong = mismatches(Ty::I32, ExitRead::Induction);
    wrong.extend(mismatches(Ty::I64, ExitRead::Induction));
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn a_rotated_sum_stores_its_accumulator_before_the_last_element() {
    let mut wrong = Vec::new();
    for read in [ExitRead::OldSum, ExitRead::GuardedOldSum] {
        wrong.extend(mismatches(Ty::I32, read));
        wrong.extend(mismatches(Ty::I64, read));
    }
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
