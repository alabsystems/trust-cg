// trust-cg-codegen - a loop that starts where an earlier early-exit loop stopped
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A search `j` in 1..=8 stops early when `j == key`, and a second search
//! counts its steps from the `j` the first one stopped at up to 12. Both are
//! bounded early-exit loops. Fully unrolling the first rewrites its IV
//! increment into per-iteration constants; the second loop's start is still
//! the run-time stopping point, not the first iteration's constant.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "count_steps_from_where_the_search_stopped";

fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_unroll_later_loop_start");
    let ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let key = fb.add_block_param(entry, Ty::U64);
    let search = fb.create_block();
    let i = fb.add_block_param(search, Ty::U64);
    let search_test = fb.create_block();
    let count = fb.create_block();
    let t = fb.add_block_param(count, Ty::U64);
    let steps = fb.add_block_param(count, Ty::U64);
    let count_test = fb.create_block();
    let done = fb.create_block();
    let result = fb.add_block_param(done, Ty::U64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(search, vec![zero]);

    fb.switch_to_block(search);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.br(search_test, vec![]);

    fb.switch_to_block(search_test);
    let eight = fb.iconst(Ty::U64, 8);
    let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, eight);
    let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, key);
    let more = fb.binop(BinOp::BAnd, Ty::Bool, trip, not_found);
    let no_steps = fb.iconst(Ty::U64, 0);
    fb.condbr(more, search, vec![next], count, vec![next, no_steps]);

    fb.switch_to_block(count);
    let step = fb.iconst(Ty::U64, 1);
    let nt = fb.binop(BinOp::Add, Ty::U64, t, step);
    let steps2 = fb.binop(BinOp::Add, Ty::U64, steps, step);
    fb.br(count_test, vec![]);

    fb.switch_to_block(count_test);
    let sixteen = fb.iconst(Ty::U64, 16);
    let trip2 = fb.icmp(ICmpOp::Ne, Ty::U64, nt, sixteen);
    let twelve = fb.iconst(Ty::U64, 12);
    let below = fb.icmp(ICmpOp::Ult, Ty::U64, nt, twelve);
    let again = fb.binop(BinOp::BAnd, Ty::Bool, trip2, below);
    fb.condbr(again, count, vec![nt, steps2], done, vec![steps2]);

    fb.switch_to_block(done);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_loop_starting_where_an_unrolled_search_stopped_counts_from_there() {
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
        // The search stops at `key` for 1..=7 and at 8 otherwise; the second
        // loop then takes `12 - stop` steps.
        for (key, expected) in [(0, 4), (1, 11), (3, 9), (7, 5), (8, 4), (100, 4)] {
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
