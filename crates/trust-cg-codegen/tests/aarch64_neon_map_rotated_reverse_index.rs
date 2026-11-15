// trust-cg-codegen - rotated reverse maps and the element they address
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = n; do { a[i - k] += 5 } while (i-- > 1)` with an `i64` count, run
//! through the JIT at every optimization level against a scalar Rust
//! reference. This is the rotated reverse map the NEON map vectorizer
//! (`neon_map`) recognizes by its `cmp i, 1; b.gt` continue test; its vector
//! blocks end at element `i - 1` (`k = 1`, clang's folded index).
//!
//! * `k = 1` over `i32` elements is that map, and must still vectorize;
//! * `k = 0` (the loop's own counter as the index) over `i32` or `i64`
//!   elements updates `a[1..=n]`, one element above those blocks, so its
//!   vector code must not be built from them.
//!
//! The cases are bounded executions on the host, not a proof of the
//! transform.
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
const ENTRY: &str = "reverse_bump";
/// Elements of `a`; every case keeps `[0, n]` inside it.
const LEN: usize = 128;
/// Counts below, at and across the `.4S` (16) and `.2D` (8) vector widths.
const COUNTS: [i64; 11] = [1, 5, 8, 9, 15, 16, 17, 32, 33, 40, 100];

/// The loop above over `elem` elements, indexing `a[i - k]`.
fn reverse_module(elem: Ty, k: i64) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_neon_map_rotated_reverse_index");
    let sig = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::I64);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::I64);
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    fb.br(head, vec![n]);

    fb.switch_to_block(head);
    let one = fb.iconst(Ty::I64, 1);
    let next = fb.binop(BinOp::Sub, Ty::I64, i, one);
    let index = match k {
        0 => i,
        1 => next,
        _ => unreachable!("k is 0 or 1"),
    };
    let p = fb.gep(elem.clone(), a, vec![index]);
    let v = fb.load(elem.clone(), p);
    let five = fb.iconst(elem.clone(), 5);
    let bumped = fb.binop(BinOp::Add, elem.clone(), v, five);
    fb.store(elem, p, bumped);
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

/// Run `module` (indexing `a[i - k]`) at every level on every count in
/// [`COUNTS`] and return one line per wrong element.
fn mismatches<T>(module: &trust_ir::Module, k: i64) -> Vec<String>
where
    T: Copy + PartialEq + Debug + Add<Output = T> + From<i16>,
{
    let mut wrong = Vec::new();
    for opt_level in LEVELS {
        let result = jit(module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, i64) -> (), and `result`
        // outlives every call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut T, i64)>(ENTRY)
        }
        .expect("entry symbol");
        for n in COUNTS {
            let mut a: Vec<T> = (0..LEN as i16).map(T::from).collect();
            let mut want = a.clone();
            for i in 1..=n {
                let x = (i - k) as usize;
                want[x] = want[x] + T::from(5);
            }
            // `a` holds LEN elements and the scalar loop stores only
            // `[1 - k, n - k] ⊆ [0, LEN)`.
            kernel.as_ref()(a.as_mut_ptr(), n);
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

#[test]
fn the_folded_index_map_still_vectorizes_and_updates_a_0_to_n() {
    let module = reverse_module(Ty::I32, 1);
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        assert!(
            neon_map_changes(&module, opt_level) > 0,
            "{opt_level:?}: neon-map did not fire"
        );
    }
    let wrong = mismatches::<i32>(&module, 1);
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn an_i32_map_indexed_by_its_counter_updates_a_1_to_n() {
    let module = reverse_module(Ty::I32, 0);
    let wrong = mismatches::<i32>(&module, 0);
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn an_i64_map_indexed_by_its_counter_updates_a_1_to_n() {
    let module = reverse_module(Ty::I64, 0);
    let wrong = mismatches::<i64>(&module, 0);
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
