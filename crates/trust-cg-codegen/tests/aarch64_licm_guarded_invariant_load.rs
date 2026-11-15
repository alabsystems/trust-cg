// trust-cg-codegen - LICM keeps an invariant load behind its in-loop guard
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `s = 0; i = 0; loop { assert!(k < 16); s += a[k]; i += 1; if i >= m { break } }`,
//! retained unchanged as a source-Assert admission control at every level.
//!
//! The guard on the invariant index `k` runs before the invariant load in the
//! first iteration. The earlier native controls required a generic guard trap
//! before the load. Under the v52 faithful-panic contract this kindless source
//! Assert refuses before optimization or JIT installation. Its native LICM
//! hazard credit is lost until an exact shared panic binding exists; it is not
//! silently converted to Assume. The machine-IR LICM guard controls remain
//! separate from these source admission checks.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "guarded_invariant_sum";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// `guarded_invariant_sum(a, k, m)`: a do-while over `i` whose body checks
/// `k < 16`, then adds `a[k]` to `s`; it exits once `i + 1 >= m`.
fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_licm_guarded_invariant_load");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let k = fb.add_block_param(entry, Ty::U64);
    let m = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let s = fb.add_block_param(header, Ty::U64);
    let exit = fb.create_block();
    let result = fb.add_block_param(exit, Ty::U64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero, zero]);

    fb.switch_to_block(header);
    let len = fb.iconst(Ty::U64, 16);
    let in_bounds = fb.icmp(ICmpOp::Ult, Ty::U64, k, len);
    fb.assert(in_bounds);
    let p = fb.gep(Ty::U64, a, vec![k]);
    let v = fb.load(Ty::U64, p);
    let sum = fb.binop(BinOp::Add, Ty::U64, s, v);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let done = fb.icmp(ICmpOp::Uge, Ty::U64, next, m);
    fb.condbr(done, exit, vec![sum], header, vec![next, sum]);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn assert_original_guard_refusal(error: impl std::fmt::Display) {
    let text = error.to_string();
    assert!(text.contains("fn guarded_invariant_sum: bb1#2"), "{text}");
    assert!(text.contains("unspecified panic kind"), "{text}");
    assert!(text.contains("require_assert_panic_kinds"), "{text}");
}

#[test]
fn the_original_source_guard_refuses_before_jit_installation() {
    let module = build_module();
    for opt_level in LEVELS {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let error = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_err();
        assert_original_guard_refusal(error);
    }
}

#[test]
fn the_original_source_guard_refuses_native_object_emission() {
    let module = build_module();
    for opt_level in LEVELS {
        let config = CompilerConfig {
            target: Target::Aarch64,
            opt_level,
            ..CompilerConfig::default()
        };
        let error = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .unwrap_err();
        assert_original_guard_refusal(error);
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
