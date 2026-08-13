// trust-cg-fuzz/tests/dense_switch_blockarg_encode.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Regression: a dense switch (>=4 dense cases, density>0.4) whose case EDGES
// carry SSA block-arguments must COMPILE and RUN correctly. The adapter splits
// each block-arg edge into a synthetic "copy block" (edge-transfer block) that
// moves the switch's edge args into the target block's params, then jumps to
// the real target. The jump table's `targets` point at those COPY blocks, which
// are reachable ONLY through the data-driven indirect branch.
//
// This is the block-arg sibling of `dense_switch_encode.rs` (defect #5, which
// covered PLAIN jump-table edges with no args). Here each case returns its
// block-param, so a miscompile that drops the arg move — or dispatches to the
// wrong case — is caught behaviorally, not just by the encoder error
//   "Jump table target block ... has no byte offset".

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{BinOp, SwitchCase, Ty};
use trust_ir_build::ModuleBuilder;

/// AOT object-compile via `Compiler::compile` (the `trust-cg -c` path that runs
/// `encode_function_with_fixups`). Returns the Mach-O object bytes or an error
/// string. `CompilerConfig::default()` targets AArch64 objects.
fn aot_object(module: &trust_ir::Module, opt: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    })
    .compile(module)
    .map(|r| r.object_code)
    .map_err(|e| format!("{e:?}"))
}

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn jit1(module: &trust_ir::Module, opt: OptLevel, fast: bool, args: [i64; 4]) -> i64 {
    let externs: HashMap<String, *const u8> = HashMap::new();
    let mut cfg = if fast {
        CompilerConfig::jit_fast(Target::host())
    } else {
        let mut c = CompilerConfig::for_host_jit();
        c.enable_jit_fast_regalloc = false;
        c
    };
    cfg.opt_level = opt;
    let buf = Compiler::new(cfg)
        .compile_module_to_jit(module, &externs)
        .expect("compile")
        .buffer;
    let f = unsafe { buf.get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>("fuzz_fn") }
        .expect("symbol")
        .into_inner();
    let v = f(args[0], args[1], args[2], args[3]);
    drop(buf);
    v
}

/// `match (a & 3) { 0 => p1, 1 => p2, 2 => p3, 3 => a, _ => 0x5555 }`, where the
/// matched value is passed as a BLOCK ARGUMENT on the switch case edge and the
/// case block RETURNS its block-param.
///
/// Four dense cases (0..=3, density 1.0) force the `JumpTable` lowering. Every
/// case edge carries one i64 block-argument, so the adapter routes each through
/// a copy block that the jump table targets.
fn build_dense_switch_blockarg() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", entry_ty);

    let e = fb.create_block();
    let case0 = fb.create_block();
    let case1 = fb.create_block();
    let case2 = fb.create_block();
    let case3 = fb.create_block();
    let default_bb = fb.create_block();

    // Entry params: a (selector source), p1, p2, p3.
    let a = fb.add_block_param(e, Ty::I64);
    let p1 = fb.add_block_param(e, Ty::I64);
    let p2 = fb.add_block_param(e, Ty::I64);
    let p3 = fb.add_block_param(e, Ty::I64);

    // Each case block takes one i64 param (the SSA value carried on the edge).
    let c0v = fb.add_block_param(case0, Ty::I64);
    let c1v = fb.add_block_param(case1, Ty::I64);
    let c2v = fb.add_block_param(case2, Ty::I64);
    let c3v = fb.add_block_param(case3, Ty::I64);
    let dv = fb.add_block_param(default_bb, Ty::I64);

    fb.switch_to_block(e);
    let three = fb.iconst(Ty::I64, 3);
    let idx = fb.binop(BinOp::And, Ty::I64, a, three);
    let default_const = fb.iconst(Ty::I64, 0x5555);
    fb.switch(
        idx,
        vec![
            SwitchCase {
                value: trust_ir::Constant::Int(0),
                target: case0,
                args: vec![p1],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(1),
                target: case1,
                args: vec![p2],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(2),
                target: case2,
                args: vec![p3],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(3),
                target: case3,
                args: vec![a],
            },
        ],
        default_bb,
        vec![default_const],
    );

    // Each case returns its block-param — verifies the edge arg was moved.
    fb.switch_to_block(case0);
    fb.ret(vec![c0v]);

    fb.switch_to_block(case1);
    fb.ret(vec![c1v]);

    fb.switch_to_block(case2);
    fb.ret(vec![c2v]);

    fb.switch_to_block(case3);
    fb.ret(vec![c3v]);

    fb.switch_to_block(default_bb);
    fb.ret(vec![dv]);

    fb.build();
    mb.build()
}

fn expected(args: [i64; 4]) -> i64 {
    let [a, p1, p2, p3] = args;
    match a & 3 {
        0 => p1,
        1 => p2,
        2 => p3,
        3 => a,
        _ => 0x5555,
    }
}

#[test]
fn dense_switch_blockarg_compiles_and_runs_at_all_opts() {
    let m = build_dense_switch_blockarg();
    // Distinct sentinel block-arg values so a dropped/mis-moved arg is visible;
    // `a` sweeps every case (a&3 in {0,1,2,3}).
    let inputs: [[i64; 4]; 8] = [
        [0, 0x1111, 0x2222, 0x3333],
        [1, 0x1111, 0x2222, 0x3333],
        [2, 0x1111, 0x2222, 0x3333],
        [3, 0x1111, 0x2222, 0x3333],
        [4, 0xAAAA, 0xBBBB, 0xCCCC],
        [5, 0xAAAA, 0xBBBB, 0xCCCC],
        [6, 0xAAAA, 0xBBBB, 0xCCCC],
        [7, 0xAAAA, 0xBBBB, 0xCCCC],
    ];
    for &a in &inputs {
        let want = expected(a);
        for fast in [true, false] {
            for opt in OPTS {
                let got = jit1(&m, opt, fast, a);
                assert_eq!(
                    got,
                    want,
                    "dense switch block-arg: args={a:?} opt={opt:?} fast={fast} \
                     (want case a&3={} -> {want:#x}, got {got:#x})",
                    a[0] & 3
                );
            }
        }
    }
}

/// AOT object-compile of the same block-arg dense switch through the
/// `trust-cg -c` path (`encode_function_with_fixups`). Before the fix this
/// failed at O2/O3 with "Jump table target block ... has no byte offset"
/// because `cfg_simplify::eliminate_empty_blocks` dropped the switch's
/// block-argument edge-transfer blocks (which the jump table targeted) from
/// `block_order` without redirecting the table entries.
#[test]
fn dense_switch_blockarg_aot_object_encodes_at_all_opts() {
    let m = build_dense_switch_blockarg();
    for opt in OPTS {
        let obj = aot_object(&m, opt)
            .unwrap_or_else(|e| panic!("AOT object compile failed at {opt:?}: {e}"));
        assert!(
            !obj.is_empty(),
            "AOT object at {opt:?} produced empty object_code"
        );
    }
}
