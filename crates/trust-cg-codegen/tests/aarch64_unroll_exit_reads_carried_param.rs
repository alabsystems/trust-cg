// trust-cg-codegen - a fully unrolled loop whose exit reads a carried value
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `h(x, i): i' = i + 1; x' = x + y; if i' < T { h(x', i') } else { return x }`,
//! run through the JIT at every optimization level against the trust-ir
//! reference interpreter. The exit reads the header's `x` either directly or
//! as the exit block's parameter.
//!
//! The loop exits from its header, so the value it returns is the header's
//! `x` of the LAST iteration: the back-edge copy `x = x'` never runs on the
//! exit path. A full unroll of this copy-counted loop must not execute that
//! copy after the final iteration either; doing so returns `x0 + T*y` where
//! the source returns `x0 + (T-1)*y`.
//!
//! The compare is placed ahead of the other header instructions so that isel
//! materializes it as `CSet` + `CmpRI #0` + `BCond NE` (the copy-counted
//! dialect the full unroller recognizes) instead of fusing it into the branch.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, FuncId, ICmpOp, InterpretValue, Interpreter, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "counted_loop_returning_its_carried_value";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// How the exit block receives the header's `x`.
#[derive(Clone, Copy, Debug)]
enum ExitRead {
    /// The exit block reads the header's `x` by dominance.
    Direct,
    /// The exit edge passes `x` as the exit block's parameter.
    Param,
}

/// `entry(x0, y)`: `x = x0; i = 0; loop { i += 1; if i >= trip { return x };
/// x += y }`, the exit taken from the header before the back-edge copies.
fn build_module(trip: i128, read: ExitRead) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_unroll_exit_reads_carried_param");
    let ty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let x0 = fb.add_block_param(entry, Ty::U64);
    let y = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let x = fb.add_block_param(header, Ty::U64);
    let i = fb.add_block_param(header, Ty::U64);
    let exit = fb.create_block();
    let exit_param = fb.add_block_param(exit, Ty::U64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![x0, zero]);

    fb.switch_to_block(header);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let limit = fb.iconst(Ty::U64, trip);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, next, limit);
    let advanced = fb.binop(BinOp::Add, Ty::U64, x, y);
    fb.condbr(more, header, vec![advanced, next], exit, vec![x]);

    fb.switch_to_block(exit);
    let returned = match read {
        ExitRead::Direct => x,
        ExitRead::Param => exit_param,
    };
    fb.ret(vec![returned]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn reference(module: &trust_ir::Module, x0: u64, y: u64) -> u64 {
    let args = [
        InterpretValue::int(Ty::U64, i128::from(x0)).expect("x0"),
        InterpretValue::int(Ty::U64, i128::from(y)).expect("y"),
    ];
    let out = Interpreter::with_module(module)
        .execute_func(FuncId::new(0), args)
        .expect("reference interpreter runs the entry");
    out.returns[0]
        .as_int()
        .expect("integer result")
        .as_unsigned() as u64
}

#[test]
fn a_fully_unrolled_loop_returns_its_last_header_value() {
    let mut wrong = Vec::new();
    for (trip, read) in [1i128, 2, 3, 4]
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
            // SAFETY: the entry's trust-ir signature is (u64, u64) -> u64, and
            // `result` outlives every call through `entry`.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(u64, u64) -> u64>(ENTRY)
            }
            .expect("entry symbol");
            for (x0, y) in [(100u64, 7u64), (0xdead_beef, 0x1_0000_0001), (u64::MAX, 3)] {
                let want = reference(&module, x0, y);
                let trips = u64::try_from(trip).expect("small trip") - 1;
                assert_eq!(want, x0.wrapping_add(y.wrapping_mul(trips)), "oracle");
                let got = entry.as_ref()(x0, y);
                if got != want {
                    wrong.push(format!(
                        "trip {trip} {read:?} {opt_level:?} x0={x0:#x} y={y:#x}: \
                         got {got:#x}, reference {want:#x}"
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
