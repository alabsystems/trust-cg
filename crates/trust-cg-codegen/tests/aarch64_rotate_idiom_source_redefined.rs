// trust-cg-codegen - a rotate whose shift source is rewritten before the OR
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `h(x, i): i' = i + 1; l = x << 13; r = x >> 51; x' = x + y;
//! if i' < T { h(x', i') } else { return l | r }`, run through the JIT at
//! every optimization level against the trust-ir reference interpreter.
//!
//! `l | r` is a rotate of the LAST iteration's `x`. The machine IR is not SSA,
//! so a rotate rewrite placed at the `OrrRR` reads its source register at
//! THAT point and is sound only while the register still holds the value both
//! shifts read; rotating the next iteration's `x' = x + y` would return
//! `rotl(x0 + T*y, 13)` where the source returns `rotl(x0 + (T-1)*y, 13)`.
//!
//! This is a regression guard for the combined full-unroll + rotate-idiom
//! path, not a test of rotate-idiom's source-redefinition guard. A
//! copy-counted full unroll runs no back-edge copies after its final
//! iteration, so once its blocks are merged nothing redefines `x` between the
//! final shifts and the `OrrRR`, and rotate-idiom's rewrite here is sound. The
//! rows fail when both invariants are lost: the unroll then leaves the final
//! iteration's carried copy `x = x'` between the shifts and the `OrrRR`, and
//! the rotate reads the copied value. The guard on its own is covered by the
//! `rotate_idiom` unit tests in trust-cg-opt.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, FuncId, ICmpOp, InterpretValue, Interpreter, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "rotate_of_the_last_carried_value";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// `entry(x0, y)`: the shifts of the header's `x` are computed every
/// iteration and OR-ed together only in the exit block.
fn build_module(trip: i128) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_rotate_idiom_source_redefined");
    let ty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let x0 = fb.add_block_param(entry, Ty::U64);
    let y = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let x = fb.add_block_param(header, Ty::U64);
    let i = fb.add_block_param(header, Ty::U64);
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![x0, zero]);

    fb.switch_to_block(header);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let limit = fb.iconst(Ty::U64, trip);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, next, limit);
    let left_amount = fb.iconst(Ty::U64, 13);
    let right_amount = fb.iconst(Ty::U64, 51);
    let left = fb.binop(BinOp::Shl, Ty::U64, x, left_amount);
    let right = fb.binop(BinOp::LShr, Ty::U64, x, right_amount);
    let advanced = fb.binop(BinOp::Add, Ty::U64, x, y);
    fb.condbr(more, header, vec![advanced, next], exit, vec![]);

    fb.switch_to_block(exit);
    let rotated = fb.binop(BinOp::Or, Ty::U64, left, right);
    fb.ret(vec![rotated]);
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
fn the_rotate_reads_the_value_both_shifts_read() {
    for trip in [1i128, 2, 3, 4] {
        let module = build_module(trip);
        for opt_level in LEVELS {
            let mut config = CompilerConfig::jit_fast(Target::Aarch64);
            config.opt_level = opt_level;
            let result = Compiler::new(config)
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(&module, &HashMap::new())
                .unwrap_or_else(|error| panic!("trip {trip} {opt_level:?}: {error}"));
            // SAFETY: the entry's trust-ir signature is (u64, u64) -> u64, and
            // `result` outlives every call through `entry`.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(u64, u64) -> u64>(ENTRY)
            }
            .expect("entry symbol");
            for (x0, y) in [(1u64, 1u64), (0xdead_beef, 0x1_0000_0001), (u64::MAX, 3)] {
                let want = reference(&module, x0, y);
                let trips = u64::try_from(trip).expect("small trip") - 1;
                let last = x0.wrapping_add(y.wrapping_mul(trips));
                assert_eq!(want, last.rotate_left(13), "oracle");
                assert_eq!(
                    entry.as_ref()(x0, y),
                    want,
                    "trip {trip} {opt_level:?} x0={x0:#x} y={y:#x}"
                );
            }
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
