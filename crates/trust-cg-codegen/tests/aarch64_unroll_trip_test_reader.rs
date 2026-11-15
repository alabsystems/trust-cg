// trust-cg-codegen - a counted loop that also selects on its exit condition
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `for i in 1..=4 { acc += if i < 4 { a } else { b } }`, with the select and
//! the loop branch reading the same comparison: a full unroll that deletes
//! the loop test must not strand the select's reader of it.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "counted_loop_selecting_on_its_test";

fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_unroll_trip_test_reader");
    let ty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let acc = fb.add_block_param(header, Ty::U64);
    let exit = fb.create_block();
    let result = fb.add_block_param(exit, Ty::U64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero, zero]);

    fb.switch_to_block(header);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let four = fb.iconst(Ty::U64, 4);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, next, four);
    let picked = fb.select(Ty::U64, more, a, b);
    let sum = fb.binop(BinOp::Add, Ty::U64, acc, picked);
    fb.condbr(more, header, vec![next, sum], exit, vec![sum]);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_counted_loop_that_selects_on_its_exit_test_computes_the_reference() {
    let module = build_module();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        // SAFETY: the entry's trust-ir signature is (u64, u64) -> u64, and
        // `result` outlives every call through `entry`.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(u64, u64) -> u64>(ENTRY)
        }
        .expect("entry symbol");
        // Three trips take `a` (i = 1, 2, 3) and the last takes `b`.
        assert_eq!(entry.as_ref()(3, 5), 3 * 3 + 5, "{opt_level:?}");
    }
}

/// This file's fixture is hand-built and carries no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or fails by name) because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
