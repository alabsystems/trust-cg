// trust-cg-codegen - a re-test of a copy taken before its slot was redefined
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The clang -O0 shape of
//! `int f(int b) { int old = b; b = b - 1; if (b == 0) return 1;
//!                 if (old != 0) return 2; return 3; }`:
//! after SROA the slot `b` is one multi-def vreg, `old` copies it before the
//! store of `b - 1`, and the second test reads that stale copy. CFG
//! simplification must not decide it from the first test's edge fact.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "stale_copy_retest";

fn reference(b: i32) -> i32 {
    let old = b;
    let b = b.wrapping_sub(1);
    if b == 0 {
        1
    } else if old != 0 {
        2
    } else {
        3
    }
}

fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_cfg_simplify_stale_copy_retest");
    let ty = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let b_in = fb.add_block_param(entry, Ty::I32);
    let then1 = fb.create_block();
    let end1 = fb.create_block();
    let then2 = fb.create_block();
    let end2 = fb.create_block();

    fb.switch_to_block(entry);
    let b_addr = fb.alloca(Ty::I32);
    let old_addr = fb.alloca(Ty::I32);
    fb.store(Ty::I32, b_addr, b_in);
    let b0 = fb.load(Ty::I32, b_addr);
    fb.store(Ty::I32, old_addr, b0);
    let b1 = fb.load(Ty::I32, b_addr);
    let one = fb.iconst(Ty::I32, 1);
    let b_minus_1 = fb.binop(BinOp::Sub, Ty::I32, b1, one);
    fb.store(Ty::I32, b_addr, b_minus_1);
    let b2 = fb.load(Ty::I32, b_addr);
    let zero = fb.iconst(Ty::I32, 0);
    let b_is_zero = fb.icmp(ICmpOp::Eq, Ty::I32, b2, zero);
    fb.condbr(b_is_zero, then1, vec![], end1, vec![]);

    fb.switch_to_block(then1);
    let r1 = fb.iconst(Ty::I32, 1);
    fb.ret(vec![r1]);

    fb.switch_to_block(end1);
    let old = fb.load(Ty::I32, old_addr);
    let zero2 = fb.iconst(Ty::I32, 0);
    let old_nonzero = fb.icmp(ICmpOp::Ne, Ty::I32, old, zero2);
    fb.condbr(old_nonzero, then2, vec![], end2, vec![]);

    fb.switch_to_block(then2);
    let r2 = fb.iconst(Ty::I32, 2);
    fb.ret(vec![r2]);

    fb.switch_to_block(end2);
    let r3 = fb.iconst(Ty::I32, 3);
    fb.ret(vec![r3]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_retest_of_a_copy_taken_before_the_slot_was_redefined_computes_the_reference() {
    let module = build_module();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        // SAFETY: the entry's trust-ir signature is (i32) -> i32, and
        // `result` outlives every call through `entry`.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(i32) -> i32>(ENTRY)
        }
        .expect("entry symbol");
        for b in [0, 1, 2, -5] {
            assert_eq!(entry.as_ref()(b), reference(b), "{opt_level:?}: f({b})");
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
