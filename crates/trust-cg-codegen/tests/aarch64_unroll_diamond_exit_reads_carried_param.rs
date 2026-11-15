// trust-cg-codegen - a fully unrolled diamond loop whose exit reads a carried value
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `h(x, i): w = a[i]; v = 3 * if x & 1 == 0 { x + w } else { x ^ y };
//! i' = i + 1; if i' < T { h(v, i') } else { return x }`, run through the JIT
//! at every optimization level against a plain Rust model. The exit reads the
//! header's `x` either directly or as the exit block's parameter.
//!
//! The loop exits from its join block, so the value it returns is the
//! header's `x` of the LAST iteration: the back-edge copy `x = v` never runs
//! on the exit path. A full unroll of this diamond-body loop must not execute
//! that copy after the final iteration either.
//!
//! A constant between the join's compare and its branch keeps isel from
//! fusing them, so the trip test is `CmpRI` + `CSet` + `CmpRI #0` + `BCond`
//! (the dialect the diamond full unroller recognizes); the `a[i]` load gives
//! it the IV-indexed address it requires.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "diamond_loop_returning_its_carried_value";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const TRIPS: [u64; 6] = [2, 3, 4, 5, 8, 16];

/// How the exit block receives the header's `x`.
#[derive(Clone, Copy, Debug)]
enum ExitRead {
    /// The exit block reads the header's `x` by dominance.
    Direct,
    /// The exit edge passes `x` as the exit block's parameter.
    Param,
}

fn build_module(trip: u64, read: ExitRead) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_unroll_diamond_exit_reads_carried_param");
    let ty = mb.add_func_type(vec![Ty::U64, Ty::U64, Ty::Ptr], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let x0 = fb.add_block_param(entry, Ty::U64);
    let y = fb.add_block_param(entry, Ty::U64);
    let a = fb.add_block_param(entry, Ty::Ptr);
    let header = fb.create_block();
    let x = fb.add_block_param(header, Ty::U64);
    let i = fb.add_block_param(header, Ty::U64);
    let even_arm = fb.create_block();
    let odd_arm = fb.create_block();
    let join = fb.create_block();
    let v = fb.add_block_param(join, Ty::U64);
    let exit = fb.create_block();
    let exit_param = fb.add_block_param(exit, Ty::U64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![x0, zero]);

    fb.switch_to_block(header);
    let three = fb.iconst(Ty::U64, 3);
    let slot = fb.gep(Ty::U64, a, vec![i]);
    let w = fb.load(Ty::U64, slot);
    let one = fb.iconst(Ty::U64, 1);
    let bit = fb.binop(BinOp::And, Ty::U64, x, one);
    let zero = fb.iconst(Ty::U64, 0);
    let even = fb.icmp(ICmpOp::Eq, Ty::U64, bit, zero);
    fb.condbr(even, even_arm, vec![], odd_arm, vec![]);

    fb.switch_to_block(even_arm);
    let sum = fb.binop(BinOp::Add, Ty::U64, x, w);
    let sum = fb.binop(BinOp::Mul, Ty::U64, sum, three);
    fb.br(join, vec![sum]);

    fb.switch_to_block(odd_arm);
    let mixed = fb.binop(BinOp::Xor, Ty::U64, x, y);
    let mixed = fb.binop(BinOp::Mul, Ty::U64, mixed, three);
    fb.br(join, vec![mixed]);

    fb.switch_to_block(join);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let limit = fb.iconst(Ty::U64, i128::from(trip));
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, next, limit);
    let _apart = fb.iconst(Ty::U64, 0);
    fb.condbr(more, header, vec![v, next], exit, vec![x]);

    fb.switch_to_block(exit);
    let returned = match read {
        ExitRead::Direct => x,
        ExitRead::Param => exit_param,
    };
    fb.ret(vec![returned]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The header's `x` on the last of `trip` iterations, in plain Rust.
fn model(trip: u64, x0: u64, y: u64, a: &[u64]) -> u64 {
    let mut x = x0;
    for &w in &a[..trip as usize - 1] {
        let v = if x & 1 == 0 { x.wrapping_add(w) } else { x ^ y };
        x = v.wrapping_mul(3);
    }
    x
}

#[test]
fn a_fully_unrolled_diamond_loop_returns_its_last_header_value() {
    let a: Vec<u64> = (0..16u64)
        .map(|k| k.wrapping_mul(0x9e37_79b9) + 5)
        .collect();
    let mut wrong = Vec::new();
    for (trip, read) in TRIPS
        .into_iter()
        .flat_map(|trip| [(trip, ExitRead::Direct), (trip, ExitRead::Param)])
    {
        let module = build_module(trip, read);
        for opt_level in LEVELS {
            let mut config = CompilerConfig::jit_fast(Target::Aarch64);
            config.opt_level = opt_level;
            let result = Compiler::new(config)
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(&module, &HashMap::new())
                .unwrap_or_else(|error| panic!("trip {trip} {read:?} {opt_level:?}: {error}"));
            // SAFETY: the entry's trust-ir signature is (u64, u64, ptr) -> u64;
            // it reads `a[0..trip]` (trip <= 16 == a.len()), and `result` and
            // `a` outlive every call through `entry`.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(u64, u64, *const u64) -> u64>(ENTRY)
            }
            .expect("entry symbol");
            for (x0, y) in [(100u64, 7u64), (0xdead_beef, 0x1_0000_0001), (u64::MAX, 3)] {
                let want = model(trip, x0, y, &a);
                let got = entry.as_ref()(x0, y, a.as_ptr());
                if got != want {
                    wrong.push(format!(
                        "trip {trip} {read:?} {opt_level:?} x0={x0:#x} y={y:#x}: \
                         got {got:#x}, model {want:#x}"
                    ));
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
