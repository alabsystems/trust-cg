// trust-cg-codegen - rotated map loops entered at or past their bound
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = 20; do { a[i] += 5; i += 1 } while !(i >= n)` — a bottom-tested map
//! with no entry guard and a signed `>=` exit — run through the JIT at every
//! optimization level against a scalar Rust reference, in the three element /
//! index widths the NEON map vectorizer (`neon_map`) lowers:
//!
//! * `.4S`: `i32` elements, `i32` index and bound;
//! * `.2D`: `i64` elements, `i64` index and bound;
//! * mixed: `i32` elements, `i64` index, `i32` bound sign-extended to `i64`.
//!
//! The body runs once whatever `n` is, so an `n <= 20` still stores `a[20]`.
//! The vector plan is exact only for an entry strictly below the bound; at or
//! past it the scalar do-while must run. The cases are bounded executions on
//! the host, not a proof of the transform.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::Add;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "rotated_bump";
/// The constant entry index.
const START: i64 = 20;
/// Elements of `a`; every case keeps `[START, max(n, START + 1))` inside it.
const LEN: usize = 160;
/// Bounds below, at, just past and well past the entry index.
const BOUNDS: [i64; 12] = [-5, 0, 1, 10, 20, 21, 22, 35, 36, 37, 100, 150];

/// The do-while above over `elem` elements with an `idx` index. The bound
/// parameter has type `bound`; when it is narrower than `idx` it is
/// sign-extended in the entry block.
fn rotated_module(elem: Ty, idx: Ty, bound: Ty) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_neon_map_rotated_entry");
    let sig = mb.add_func_type(vec![Ty::Ptr, bound.clone()], vec![]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let n_param = fb.add_block_param(entry, bound.clone());
    let head = fb.create_block();
    let i = fb.add_block_param(head, idx.clone());
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let n = if bound == idx {
        n_param
    } else {
        fb.sext(bound, idx.clone(), n_param)
    };
    let start = fb.iconst(idx.clone(), i128::from(START));
    fb.br(head, vec![start]);

    fb.switch_to_block(head);
    let p = fb.gep(elem.clone(), a, vec![i]);
    let v = fb.load(elem.clone(), p);
    let five = fb.iconst(elem.clone(), 5);
    let bumped = fb.binop(BinOp::Add, elem.clone(), v, five);
    fb.store(elem, p, bumped);
    let one = fb.iconst(idx.clone(), 1);
    let next = fb.binop(BinOp::Add, idx.clone(), i, one);
    let done = fb.icmp(ICmpOp::Sge, idx, next, n);
    fb.condbr(done, exit, vec![], head, vec![next]);

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

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> Result<JitCompilationResult, String> {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .map_err(|error| error.to_string())
}

/// Run `module` at every level on every bound in [`BOUNDS`] and return one
/// line per compile failure or wrong element.
fn mismatches<T, N>(module: &trust_ir::Module, bound: fn(i64) -> N) -> Vec<String>
where
    T: Copy + PartialEq + Debug + Add<Output = T> + From<i16>,
{
    let mut wrong = Vec::new();
    for opt_level in LEVELS {
        let result = match jit(module, opt_level) {
            Ok(result) => result,
            Err(error) => {
                wrong.push(format!("{opt_level:?}: compile failed: {error}"));
                continue;
            }
        };
        // SAFETY: the trust-ir signature is (ptr, T-bound) -> (), matching the
        // pointer and `N` arguments, and `result` outlives every call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut T, N)>(ENTRY)
        }
        .expect("entry symbol");
        for n in BOUNDS {
            let mut a: Vec<T> = (0..LEN as i16).map(T::from).collect();
            let mut want = a.clone();
            let mut i = START;
            loop {
                want[i as usize] = want[i as usize] + T::from(5);
                i += 1;
                if i >= n {
                    break;
                }
            }
            // `a` holds LEN elements and the scalar loop stores only
            // `[START, max(n, START + 1)) ⊆ [0, LEN)`.
            kernel.as_ref()(a.as_mut_ptr(), bound(n));
            if a != want {
                let first = (0..LEN).find(|&x| a[x] != want[x]).unwrap();
                wrong.push(format!(
                    "{opt_level:?} n={n}: a[{first}] = {:?} (want {:?})",
                    a[first], want[first]
                ));
            }
        }
    }
    wrong
}

/// The cases above exercise the vector code: `neon-map` rewrites every
/// width's loop at O2 and O3.
#[test]
fn every_width_is_vectorized_at_o2_and_o3() {
    for (label, module) in [
        (".4S", rotated_module(Ty::I32, Ty::I32, Ty::I32)),
        (".2D", rotated_module(Ty::I64, Ty::I64, Ty::I64)),
        ("mixed", rotated_module(Ty::I32, Ty::I64, Ty::I32)),
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
fn an_i32_rotated_map_entered_at_its_bound_runs_its_one_iteration() {
    let module = rotated_module(Ty::I32, Ty::I32, Ty::I32);
    let wrong = mismatches::<i32, i32>(&module, |n| n as i32);
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn an_i64_rotated_map_entered_at_its_bound_runs_its_one_iteration() {
    let module = rotated_module(Ty::I64, Ty::I64, Ty::I64);
    let wrong = mismatches::<i64, i64>(&module, |n| n);
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn a_mixed_width_rotated_map_compiles_and_runs_its_one_iteration() {
    let module = rotated_module(Ty::I32, Ty::I64, Ty::I32);
    let wrong = mismatches::<i32, i32>(&module, |n| n as i32);
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
