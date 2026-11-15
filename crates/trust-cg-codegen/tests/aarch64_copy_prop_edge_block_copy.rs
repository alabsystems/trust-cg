// trust-cg-codegen - copy-prop through a loop whose copy runs in the body's edge block
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The adapter lowers a counted loop's block arguments to copies in the edge
//! block that is the body's only predecessor. In `fsum` at O2 that block holds
//! `v8 = mov v6`, and the body reads v8 before it redefines the source with
//! `v6 = mov v15`. Every cycle back to the body runs the edge block and re-runs
//! the copy, so v8 equals v6 at each read. Copy-prop rewrites those reads to
//! the source (`copy_prop::use_block_reentered_without_copy`), and the later
//! loop passes match the rewritten body.
//!
//! The rows compile two of the compile corpus's `scripts/fuzz` kernels:
//! - `fsum`, a float sum, where `scalar-unroll` must change the function at O2
//!   and O3;
//! - `predmask`, a sum of the elements above a threshold, where `neon-predsum`
//!   must change it at O2 and O3.
//!
//! A copy-prop that refuses those rewrites leaves `fsum` at O2 and `predmask`
//! at O2 and O3 with no match. Each row also JIT-runs the kernel and compares
//! it with a plain Rust model. These are host-bounded executions: tests, not a
//! proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;

/// The host triple the metrics pipeline prepares for.
const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};

/// `scripts/fuzz/fsum.trust_ir`: `s = 0.0; for i in 0..n { s += a[i] }`.
const FSUM: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32) -> (f32)
fn @fsum(functy.0){
bb0(%0: ptr,%1: i32):
 %2=const i32 0
 %3=const i32 1
 %4=const f32 0.0
 br bb1(%2,%4)
bb1(%10: i32,%11: f32):
 %12=icmp slt i32 %10,%1
 condbr %12,bb3(%10,%11),bb2(%11)
bb3(%20: i32,%21: f32):
 %22=gep f32,ptr %0,%20
 %23=load f32,ptr %22
 %24=fadd f32 %21,%23
 %25=add i32 %20,%3
 br bb1(%25,%24)
bb2(%40: f32):
 ret %40
}
"#;

/// `scripts/fuzz/pm.trust_ir`: `s = 0; for i in 0..n { s += if a[i] > t {
/// a[i] } else { 0 } }`, wrapping.
const PREDMASK: &str = r#"; TrustIr text format v1
module "m"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, i32, i32) -> (i32)
fn @predmask(functy.0){
bb0(%0: ptr,%1: i32,%2: i32):
 %3=const i32 0
 %4=const i32 1
 br bb1(%3,%3)
bb1(%10: i32,%11: i32):
 %12=icmp slt i32 %10,%1
 condbr %12,bb3(%10,%11),bb2(%11)
bb3(%20: i32,%21: i32):
 %22=gep i32,ptr %0,%20
 %23=load i32,ptr %22
 %24=icmp sgt i32 %23,%2
 %25=select i32 %24,%23,%3
 %26=add i32 %21,%25
 %27=add i32 %20,%4
 br bb1(%27,%26)
bb2(%40: i32):
 ret %40
}
"#;

/// Trip counts: empty and negative, short and remainder-only, around the
/// vector and unroll widths, and long.
const COUNTS: [i32; 16] = [-3, 0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 64, 257];

fn parse(text: &str) -> trust_ir::Module {
    trust_ir::parser::parse_module(text).expect("parse kernel")
}

/// Changing runs of `pass` when `module` is prepared at `opt_level` with
/// every pass enabled (an explicit empty disable list).
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

/// `module` compiled for the AArch64 JIT at `opt_level`.
fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .expect("JIT compile")
}

/// `len` successive states of the xorshift32 (13, 17, 5) generator after
/// `seed`.
fn xorshift32(seed: u32, len: usize) -> Vec<u32> {
    let mut x = seed;
    (0..len)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            x
        })
        .collect()
}

/// The longest trip count in `COUNTS`, as a buffer length.
fn max_len() -> usize {
    COUNTS.iter().copied().max().unwrap_or(0).max(0) as usize
}

#[test]
fn fsum_scalar_unroll_matches_after_copy_prop() {
    let module = parse(FSUM);
    // Small integers keep every partial sum exact in f32, so the model's
    // order of additions cannot differ from the kernel's. No element is
    // -0.0, so with the kernel's +0.0 start a zero sum is +0.0 in any order.
    let data: Vec<f32> = xorshift32(0x9e37_79b9, max_len())
        .into_iter()
        .map(|x| (x % 101) as f32 - 50.0)
        .collect();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let fired = pass_changes(&module, opt_level, "scalar-unroll");
        assert!(
            fired > 0,
            "fsum {opt_level:?}: scalar-unroll did not change the function"
        );
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, i32) -> f32. The kernel
        // reads `n` elements of `data` when `n > 0`, every `n` is at most
        // `data.len()`, and `result` outlives every call.
        let fsum = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*const f32, i32) -> f32>("fsum")
        }
        .expect("fsum symbol");
        for n in COUNTS {
            // The kernel starts from +0.0, so the model folds from +0.0:
            // `Sum for f32` starts from -0.0, which an empty row returns.
            let want = data[..n.max(0) as usize].iter().fold(0.0f32, |s, &x| s + x);
            let got = fsum.as_ref()(data.as_ptr(), n);
            assert_eq!(got.to_bits(), want.to_bits(), "fsum {opt_level:?} n={n}");
        }
    }
}

#[test]
fn predmask_neon_predsum_matches_after_copy_prop() {
    let module = parse(PREDMASK);
    let data: Vec<i32> = xorshift32(0x2545_f491, max_len())
        .into_iter()
        .map(|x| x as i32)
        .collect();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let fired = pass_changes(&module, opt_level, "neon-predsum");
        assert!(
            fired > 0,
            "predmask {opt_level:?}: neon-predsum did not change the function"
        );
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, i32, i32) -> i32. The
        // kernel reads `n` elements of `data` when `n > 0`, every `n` is at
        // most `data.len()`, and `result` outlives every call.
        let predmask = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*const i32, i32, i32) -> i32>("predmask")
        }
        .expect("predmask symbol");
        for n in COUNTS {
            for t in [i32::MIN, -1_000_000_000, -1, 0, 7, 1_000_000_000, i32::MAX] {
                let want = data[..n.max(0) as usize]
                    .iter()
                    .fold(0i32, |s, &x| s.wrapping_add(if x > t { x } else { 0 }));
                let got = predmask.as_ref()(data.as_ptr(), n, t);
                assert_eq!(got, want, "predmask {opt_level:?} n={n} t={t}");
            }
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
