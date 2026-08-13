// trust-cg-fuzz/tests/dense_switch_encode.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Regression for defect #5: a dense switch (>=4 dense cases, density>0.4) that
// lowers to a jump table must COMPILE and RUN correctly at O2/O3 under both
// allocators. The jump-table case blocks are reachable only through the
// data-driven indirect branch (recorded in func.jump_tables[..].targets, not as
// an explicit B/B.cond terminator). The regalloc/opt CFG round-trip used to
// rebuild block_order from explicit-terminator reachability only, dropping the
// jump-table targets from block_order and triggering an encoder error:
//   "Jump table target block ... has no byte offset"
// The fix seeds the CFG successor edges with the jump-table targets before
// reachability/block-order is recomputed, so the targets stay in block_order at
// their natural layout position.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{BinOp, SwitchCase, Ty};
use trust_ir_build::ModuleBuilder;

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn jit1(module: &trust_ir::Module, opt: OptLevel, fast: bool, a: i64) -> i64 {
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
    let v = f(a, 0, 0, 0);
    drop(buf);
    v
}

/// `match (a & 3) { 0 => K0, 1 => K1, 2 => K2, 3 => K3, _ => KD }` via fb.switch.
///
/// Four dense cases (0..=3, density 1.0) force the `JumpTable` lowering
/// (N >= 4, density > 0.4).
fn build_dense_switch() -> trust_ir::Module {
    const K0: i128 = 0x1111;
    const K1: i128 = 0x2222;
    const K2: i128 = 0x3333;
    const K3: i128 = 0x4444;
    const KD: i128 = 0x5555;

    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", entry_ty);

    let e = fb.create_block();
    let case0 = fb.create_block();
    let case1 = fb.create_block();
    let case2 = fb.create_block();
    let case3 = fb.create_block();
    let default_bb = fb.create_block();

    let a = fb.add_block_param(e, Ty::I64);
    for _ in 0..3 {
        fb.add_block_param(e, Ty::I64);
    }
    fb.switch_to_block(e);
    let three = fb.iconst(Ty::I64, 3);
    let idx = fb.binop(BinOp::And, Ty::I64, a, three);
    fb.switch(
        idx,
        vec![
            SwitchCase {
                value: trust_ir::Constant::Int(0),
                target: case0,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(1),
                target: case1,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(2),
                target: case2,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(3),
                target: case3,
                args: vec![],
            },
        ],
        default_bb,
        vec![],
    );

    fb.switch_to_block(case0);
    let r0 = fb.iconst(Ty::I64, K0);
    fb.ret(vec![r0]);

    fb.switch_to_block(case1);
    let r1 = fb.iconst(Ty::I64, K1);
    fb.ret(vec![r1]);

    fb.switch_to_block(case2);
    let r2 = fb.iconst(Ty::I64, K2);
    fb.ret(vec![r2]);

    fb.switch_to_block(case3);
    let r3 = fb.iconst(Ty::I64, K3);
    fb.ret(vec![r3]);

    fb.switch_to_block(default_bb);
    let rd = fb.iconst(Ty::I64, KD);
    fb.ret(vec![rd]);

    fb.build();
    mb.build()
}

#[test]
fn dense_switch_compiles_and_runs_at_all_opts() {
    let m = build_dense_switch();
    // Inputs hitting every case (0,1,2) and the default (3).
    let inputs = [0i64, 1, 2, 3, 4, 5, 6, 7, -1, -2, 100, 101, 102, 103];
    for &a in &inputs {
        let reference = jit1(&m, OptLevel::O0, true, a);
        for fast in [true, false] {
            for opt in OPTS {
                let got = jit1(&m, opt, fast, a);
                assert_eq!(
                    got, reference,
                    "dense switch: a={a} opt={opt:?} fast={fast}"
                );
            }
        }
    }
}
