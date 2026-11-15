// trust-cg-codegen - rotated reverse maps entered at or below one
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = n; do { y[i - 1] += t } while (i-- > 1)` — the rotated reverse map the
//! NEON map vectorizer (`neon_map`) recognizes by its `cmp i, 1; b.gt`
//! continue test — run through the JIT at every optimization level against a
//! scalar Rust reference. `t` is `5` (one array) or `x[i - 1]` (two arrays,
//! which `neon_map` versions with a runtime range check). The count is an
//! `i64` parameter or an `i32` one zero-extended to `i64` (clang's
//! `uxtw(n)`), with no entry guard in front of the loop.
//!
//! The loop is bottom-tested: entered with `n <= 0` it still runs its body
//! once, at `y[n - 1]`, and stops. The vector plan covers `[0, n - 1]` and is
//! exact only for a start `n >= 1`; below that the scalar do-while must run.
//! `y` and `x` point [`OFF`] elements into their buffers so that the one
//! iteration's element is in bounds. The cases are bounded executions on the
//! host, not a proof of the transform.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "reverse_entry";
/// Elements of each buffer below `y` and `x`; the lowest count's one
/// iteration stores `y[-41]`.
const OFF: usize = 64;
/// Elements of each buffer; the highest count stores up to `y[99]`.
const LEN: usize = OFF + 128;
/// Counts at and below zero, then across the `.4S` vector width (16).
const COUNTS: [i64; 15] = [-40, -17, -16, -15, -5, -1, 0, 1, 2, 15, 16, 17, 32, 33, 100];

/// The loop above over `i32` elements. `count` is the count parameter's type
/// (`I64`, or `I32` zero-extended in the entry block); `two_arrays` adds the
/// `x` parameter and reads `x[i - 1]` in place of the constant `5`.
fn reverse_module(count: Ty, two_arrays: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_neon_map_rotated_reverse_entry");
    let mut params = vec![Ty::Ptr];
    if two_arrays {
        params.push(Ty::Ptr);
    }
    params.push(count.clone());
    let sig = mb.add_func_type(params, vec![]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let y = fb.add_block_param(entry, Ty::Ptr);
    let x = two_arrays.then(|| fb.add_block_param(entry, Ty::Ptr));
    let n_param = fb.add_block_param(entry, count.clone());
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::I64);
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let n = if count == Ty::I64 {
        n_param
    } else {
        fb.zext(count, Ty::I64, n_param)
    };
    fb.br(head, vec![n]);

    fb.switch_to_block(head);
    let one = fb.iconst(Ty::I64, 1);
    let next = fb.binop(BinOp::Sub, Ty::I64, i, one);
    let term = match x {
        Some(x) => {
            let px = fb.gep(Ty::I32, x, vec![next]);
            fb.load(Ty::I32, px)
        }
        None => fb.iconst(Ty::I32, 5),
    };
    let py = fb.gep(Ty::I32, y, vec![next]);
    let v = fb.load(Ty::I32, py);
    let bumped = fb.binop(BinOp::Add, Ty::I32, v, term);
    fb.store(Ty::I32, py, bumped);
    let more = fb.icmp(ICmpOp::Sgt, Ty::I64, i, one);
    fb.condbr(more, head, vec![next], exit, vec![]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Changing runs of `neon-map` over `module` in the `opt_level` pipeline.
fn neon_map_changes(module: &trust_ir::Module, opt_level: OptLevel) -> u32 {
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
            .filter(|(name, _)| name == "neon-map")
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

/// The scalar reference: the do-while over `y`, `x` (each [`OFF`] into its
/// buffer), adding `x[i - 1]` when `two_arrays`, else `5`.
fn reference(y: &mut [i32], x: &[i32], n: i64, two_arrays: bool) {
    let mut i = n;
    loop {
        let at = (OFF as i64 + i - 1) as usize;
        y[at] += if two_arrays { x[at] } else { 5 };
        let more = i > 1;
        i -= 1;
        if !more {
            break;
        }
    }
}

/// Run `module` at every level on each of `counts` and return one line per
/// wrong element. `call` invokes the kernel on `(y, x, n)`.
fn mismatches(
    counts: &[i64],
    two_arrays: bool,
    module: &trust_ir::Module,
    call: impl Fn(&JitCompilationResult, *mut i32, *const i32, i64),
) -> Vec<String> {
    let mut wrong = Vec::new();
    for opt_level in LEVELS {
        let result = jit(module, opt_level);
        for &n in counts {
            let mut y: Vec<i32> = (0..LEN as i32).collect();
            let x: Vec<i32> = (0..LEN as i32).map(|v| 3 * v + 1).collect();
            let mut want = y.clone();
            reference(&mut want, &x, n, two_arrays);
            // SAFETY: `y` and `x` hold LEN elements, and the scalar loop
            // touches only `[OFF + min(n, 1) - 1, OFF + max(n, 1)) ⊆ [0, LEN)`.
            let (yp, xp) = unsafe { (y.as_mut_ptr().add(OFF), x.as_ptr().add(OFF)) };
            call(&result, yp, xp, n);
            if y != want {
                let first = (0..LEN).find(|&at| y[at] != want[at]).unwrap();
                wrong.push(format!(
                    "{opt_level:?} n={n}: y[{}] = {} (want {})",
                    first as i64 - OFF as i64,
                    y[first],
                    want[first]
                ));
            }
        }
    }
    wrong
}

/// The cases below exercise the vector code: `neon-map` rewrites each loop
/// at O2 and O3.
#[test]
fn each_rotated_reverse_map_is_vectorized_at_o2_and_o3() {
    for (label, module) in [
        ("i64 count", reverse_module(Ty::I64, false)),
        ("zext i32 count", reverse_module(Ty::I32, false)),
        ("two arrays", reverse_module(Ty::I64, true)),
    ] {
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            assert!(
                neon_map_changes(&module, opt_level) > 0,
                "{label} {opt_level:?}: neon-map did not fire"
            );
        }
    }
}

#[test]
fn an_i64_count_at_or_below_zero_runs_its_one_iteration() {
    let module = reverse_module(Ty::I64, false);
    let wrong = mismatches(&COUNTS, false, &module, |result, y, _, n| {
        // SAFETY: the trust-ir signature is (ptr, i64) -> (), and `result`
        // outlives the call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut i32, i64)>(ENTRY)
        }
        .expect("entry symbol");
        kernel.as_ref()(y, n);
    });
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

/// A zero-extended `i32` count is never negative, so `0` is its only start
/// below one.
#[test]
fn a_zero_extended_count_of_zero_runs_its_one_iteration() {
    let module = reverse_module(Ty::I32, false);
    let counts: Vec<i64> = COUNTS.iter().copied().filter(|&n| n >= 0).collect();
    let wrong = mismatches(&counts, false, &module, |result, y, _, n| {
        // SAFETY: the trust-ir signature is (ptr, i32) -> (), and `result`
        // outlives the call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut i32, i32)>(ENTRY)
        }
        .expect("entry symbol");
        kernel.as_ref()(y, i32::try_from(n).expect("count in i32 range"));
    });
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

/// Two disjoint arrays go through the runtime range check, which reads the
/// count as a byte length; a start below one must not reach it.
#[test]
fn a_versioned_map_at_or_below_zero_runs_its_one_iteration() {
    let module = reverse_module(Ty::I64, true);
    let wrong = mismatches(&COUNTS, true, &module, |result, y, x, n| {
        // SAFETY: the trust-ir signature is (ptr, ptr, i64) -> (), and
        // `result` outlives the call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut i32, *const i32, i64)>(ENTRY)
        }
        .expect("entry symbol");
        kernel.as_ref()(y, x, n);
    });
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
