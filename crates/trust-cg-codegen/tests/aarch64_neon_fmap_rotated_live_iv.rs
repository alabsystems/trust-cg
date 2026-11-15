// trust-cg-codegen - rotated FP map loops whose exit reads the induction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = START; loop { y[i] = y[i] * 2.0; if i + 1 >= n { return i } i += 1 }`
//! — a rotated (bottom-tested) elementwise FP map whose exit reads the
//! induction `i`, the value BEFORE the step — run through the JIT at every
//! optimization level against a scalar Rust reference, over `f32` and `f64`
//! elements with an `i32` and an `i64` index.
//!
//! Entered below its bound the loop returns `n - 1`. The NEON FP map
//! vectorizer (`neon_fmap`) rewrites this shape when the exit does not read
//! `i`. Its vector exit branches straight to the exit once every element is
//! consumed, holding `i = n`, one past the scalar loop's exit value. The
//! cases are bounded executions on the host, not a proof of the transform.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "rotated_double";
/// Elements of `y`; the highest bound writes up to `y[179]`.
const LEN: usize = 192;
/// Bounds relative to the start: below, at, just past, and across multiples
/// of the vector widths, where the vector code consumes every element.
const DELTAS: [i64; 13] = [-25, -20, 0, 1, 7, 8, 9, 15, 16, 17, 32, 64, 160];

/// The loop above over `elem` elements with an `idx`-typed induction and
/// bound, entered at `start`. `read_i` returns `i`; otherwise the exit
/// returns the constant 7, which keeps `i` dead there.
fn double_module(elem: Ty, idx: Ty, start: i64, read_i: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_neon_fmap_rotated_live_iv");
    let sig = mb.add_func_type(vec![Ty::Ptr, idx.clone()], vec![idx.clone()]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let y = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, idx.clone());
    let head = fb.create_block();
    let i = fb.add_block_param(head, idx.clone());
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let first = fb.iconst(idx.clone(), i128::from(start));
    fb.br(head, vec![first]);

    fb.switch_to_block(head);
    let p = fb.gep(elem.clone(), y, vec![i]);
    let v = fb.load(elem.clone(), p);
    let two = fb.fconst(elem.clone(), 2.0);
    let doubled = fb.binop(BinOp::FMul, elem.clone(), v, two);
    fb.store(elem, p, doubled);
    let one = fb.iconst(idx.clone(), 1);
    let next = fb.binop(BinOp::Add, idx.clone(), i, one);
    let done = fb.icmp(ICmpOp::Sge, idx.clone(), next, n);
    fb.condbr(done, exit, vec![], head, vec![next]);

    fb.switch_to_block(exit);
    if read_i {
        fb.ret(vec![i]);
    } else {
        let seven = fb.iconst(idx, 7);
        fb.ret(vec![seven]);
    }
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Changing runs of `neon-fmap` over `module` in the `opt_level` pipeline.
fn neon_fmap_changes(module: &trust_ir::Module, opt_level: OptLevel) -> u32 {
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
            .filter(|(name, _)| name == "neon-fmap")
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

/// The element types the cases store, as their bit patterns.
trait Float: Copy {
    fn of(value: i64) -> Self;
    fn doubled(self) -> Self;
    fn bits(self) -> u64;
}

impl Float for f32 {
    fn of(value: i64) -> Self {
        value as f32 * 0.75
    }
    fn doubled(self) -> Self {
        self * 2.0
    }
    fn bits(self) -> u64 {
        u64::from(self.to_bits())
    }
}

impl Float for f64 {
    fn of(value: i64) -> Self {
        value as f64 * 0.75
    }
    fn doubled(self) -> Self {
        self * 2.0
    }
    fn bits(self) -> u64 {
        self.to_bits()
    }
}

/// The scalar reference over `y`: the `i` it returns.
fn reference<T: Float>(y: &mut [T], start: i64, n: i64) -> i64 {
    let mut i = start;
    loop {
        y[i as usize] = y[i as usize].doubled();
        if i + 1 >= n {
            return i;
        }
        i += 1;
    }
}

/// Call the kernel with an `idx`-typed bound and widen its return.
fn call<T>(result: &JitCompilationResult, idx: &Ty, y: *mut T, n: i64) -> i64 {
    if *idx == Ty::I32 {
        // SAFETY: the trust-ir signature is (ptr, i32) -> i32, and `result`
        // outlives the call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut T, i32) -> i32>(ENTRY)
        }
        .expect("entry symbol");
        i64::from(kernel.as_ref()(y, n as i32))
    } else {
        // SAFETY: the trust-ir signature is (ptr, i64) -> i64, and `result`
        // outlives the call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut T, i64) -> i64>(ENTRY)
        }
        .expect("entry symbol");
        kernel.as_ref()(y, n)
    }
}

/// Run the `read_i` module over `T` (`elem`) for `idx` at every level from
/// each start, and return one line per wrong element or return value.
fn mismatches<T: Float>(elem: Ty, idx: Ty, read_i: bool) -> Vec<String> {
    let mut wrong = Vec::new();
    for start in [0i64, 20] {
        let module = double_module(elem.clone(), idx.clone(), start, read_i);
        for opt_level in LEVELS {
            let result = jit(&module, opt_level);
            for delta in DELTAS {
                let n = start + delta;
                let mut y: Vec<T> = (0..LEN as i64).map(T::of).collect();
                let mut want = y.clone();
                let want_i = reference(&mut want, start, n);
                let want_ret = if read_i { want_i } else { 7 };
                // The loop writes `y[start..max(n, start + 1))`, inside `y`.
                let got_ret = call(&result, &idx, y.as_mut_ptr(), n);
                if got_ret != want_ret {
                    wrong.push(format!(
                        "{elem:?}/{idx:?} start={start} {opt_level:?} n={n}: returned {got_ret} \
                         (want {want_ret})"
                    ));
                }
                if let Some(at) = (0..LEN).find(|&at| y[at].bits() != want[at].bits()) {
                    wrong.push(format!(
                        "{elem:?}/{idx:?} start={start} {opt_level:?} n={n}: y[{at}] bits \
                         {:#x} (want {:#x})",
                        y[at].bits(),
                        want[at].bits()
                    ));
                }
            }
        }
    }
    wrong
}

/// The same loops with `i` dead at the exit are vectorized, so the cases
/// below run the shape the vector code covers.
#[test]
fn the_loop_without_the_read_is_vectorized_and_exact() {
    let mut wrong = Vec::new();
    for elem in [Ty::F32, Ty::F64] {
        for idx in [Ty::I32, Ty::I64] {
            for start in [0i64, 20] {
                let module = double_module(elem.clone(), idx.clone(), start, false);
                for opt_level in [OptLevel::O2, OptLevel::O3] {
                    assert!(
                        neon_fmap_changes(&module, opt_level) > 0,
                        "{elem:?}/{idx:?} start={start} {opt_level:?}: neon-fmap did not fire"
                    );
                }
            }
            if elem == Ty::F32 {
                wrong.extend(mismatches::<f32>(elem.clone(), idx, false));
            } else {
                wrong.extend(mismatches::<f64>(elem.clone(), idx, false));
            }
        }
    }
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn a_rotated_fp_map_returns_its_last_index() {
    let mut wrong = Vec::new();
    for idx in [Ty::I32, Ty::I64] {
        wrong.extend(mismatches::<f32>(Ty::F32, idx.clone(), true));
        wrong.extend(mismatches::<f64>(Ty::F64, idx, true));
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
