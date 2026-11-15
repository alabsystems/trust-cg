// trust-cg-codegen - an early-exit search loop whose exit reads its trip test
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `j` runs 1..=8 and the search stops early when `j == key`; the exit
//! returns the trip test `j != 8` (1 when the search stopped early, 0 when it
//! ran out). The bounded early-exit full unroll deletes that trip test from
//! every iteration, so it must not strand the exit's reader of it.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "early_exit_search_returning_its_trip_test";

fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_unroll_early_exit_trip_test_reader");
    let ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let key = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let test = fb.create_block();
    let exit = fb.create_block();
    let stopped_early = fb.add_block_param(exit, Ty::Bool);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero]);

    fb.switch_to_block(header);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.br(test, vec![]);

    fb.switch_to_block(test);
    let eight = fb.iconst(Ty::U64, 8);
    let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, eight);
    let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, key);
    let more = fb.binop(BinOp::BAnd, Ty::Bool, trip, not_found);
    fb.condbr(more, header, vec![next], exit, vec![trip]);

    fb.switch_to_block(exit);
    let yes = fb.iconst(Ty::U64, 1);
    let no = fb.iconst(Ty::U64, 0);
    let result = fb.select(Ty::U64, stopped_early, yes, no);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn an_early_exit_search_that_returns_its_trip_test_computes_the_reference() {
    let module = build_module();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        // SAFETY: the entry's trust-ir signature is (u64) -> u64, and
        // `result` outlives every call through `entry`.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(u64) -> u64>(ENTRY)
        }
        .expect("entry symbol");
        // A key in 1..=7 stops the search early; 8 is reached by the trip
        // test itself, and every other key runs the search out.
        for (key, expected) in [(0, 0), (3, 1), (5, 1), (7, 1), (8, 0), (100, 0)] {
            assert_eq!(entry.as_ref()(key), expected, "{opt_level:?} key={key}");
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
