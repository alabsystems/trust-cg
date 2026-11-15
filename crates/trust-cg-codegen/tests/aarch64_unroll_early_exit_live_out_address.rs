// trust-cg-codegen - an early-exit search that writes through the address it stopped at
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `j` runs 1..=8 over `base[j]` and stops early at the first `base[j] ==
//! key`; after the loop, the element it stopped at is zeroed through the
//! address the loop computed. The bounded early-exit full unroll folds each
//! iteration's constant-index address into its load, and must keep the
//! address the exit still reads.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "zero_where_the_search_stopped";

fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_unroll_early_exit_live_out_address");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64], vec![]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let base = fb.add_block_param(entry, Ty::Ptr);
    let key = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let test = fb.create_block();
    let exit = fb.create_block();
    let stopped_at = fb.add_block_param(exit, Ty::Ptr);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero]);

    fb.switch_to_block(header);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let address = fb.gep(Ty::U64, base, vec![next]);
    let value = fb.load(Ty::U64, address);
    fb.br(test, vec![]);

    fb.switch_to_block(test);
    let eight = fb.iconst(Ty::U64, 8);
    let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, eight);
    let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, value, key);
    let more = fb.binop(BinOp::BAnd, Ty::Bool, trip, not_found);
    fb.condbr(more, header, vec![next], exit, vec![address]);

    fb.switch_to_block(exit);
    let cleared = fb.iconst(Ty::U64, 0);
    fb.store(Ty::U64, stopped_at, cleared);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn an_early_exit_search_writes_through_the_address_it_stopped_at() {
    let module = build_module();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        // SAFETY: the entry's trust-ir signature is (ptr, u64) -> (), it
        // reads and writes only `base[1..=8]`, every call passes a 9-element
        // array, and `result` outlives every call through `entry`.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut u64, u64)>(ENTRY)
        }
        .expect("entry symbol");
        // `base[j] = 10 + j`: key 13 stops the search at j = 3, and a key no
        // element holds runs it out at j = 8.
        for (key, stop) in [(13, 3), (11, 1), (17, 7), (18, 8), (99, 8)] {
            let mut array: [u64; 9] = std::array::from_fn(|j| 10 + j as u64);
            entry.as_ref()(array.as_mut_ptr(), key);
            let mut expected: [u64; 9] = std::array::from_fn(|j| 10 + j as u64);
            expected[stop] = 0;
            assert_eq!(array, expected, "{opt_level:?} key={key}");
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
