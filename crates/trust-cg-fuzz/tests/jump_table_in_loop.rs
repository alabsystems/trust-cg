// trust-cg-fuzz/tests/jump_table_in_loop.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Regression for defect #6: a dense switch (jump table) inside a counted loop
// where a loop-invariant value (`a`) is live across the back-edge. Each case
// computes `a * k_i` and folds it into an accumulator. At O0 the invariant `a`
// was dropped/clobbered on the 2nd iteration (the per-case `Mul a, k` degraded
// to just `k`), because the O0/jit_fast allocator mishandled the loop-carried
// value's liveness in the presence of the jump-table dispatch scratch vregs and
// the missing jump-table CFG successor edges. O0 must match the (correct) O1
// reference for every input.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{BinOp, ICmpOp, SwitchCase, Ty};
use trust_ir_build::ModuleBuilder;

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

const ITERS: i64 = 3;
const K: [i128; 4] = [0x11, 0x22, 0x33, 0x44];

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

/// Pure-Rust two's-complement reference.
fn reference(a: i64) -> i64 {
    let mut acc: i64 = 0;
    for i in 0..ITERS {
        let k = K[(i & 3) as usize] as i64;
        acc = acc.wrapping_add(a.wrapping_mul(k));
    }
    acc
}

/// ```text
/// acc = 0; i = 0;
/// loop:
///   if i >= ITERS goto exit
///   switch (i & 3) { 0 => c0, 1 => c1, 2 => c2, 3 => c3 }  // dense -> jump table
///   ck: acc += a * K[k]; i += 1; goto loop
/// exit: ret acc
/// ```
/// `a` is a TRUE loop-invariant: it is the entry block parameter used directly
/// inside the loop-body cases (NOT threaded through the loop's block params), so
/// its value must survive across the back-edge purely by the allocator keeping
/// it live. This is the shape that triggered the O0/jit_fast miscompile where
/// `Mul a, K` degraded to just `K` on the 2nd iteration (defect #6).
fn build_jump_table_in_loop() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", entry_ty);

    let entry = fb.create_block();
    let header = fb.create_block();
    let body = fb.create_block();
    let case0 = fb.create_block();
    let case1 = fb.create_block();
    let case2 = fb.create_block();
    let case3 = fb.create_block();
    let latch = fb.create_block();
    let exit = fb.create_block();

    // Entry params: a (the loop-invariant) + 3 unused.
    let a = fb.add_block_param(entry, Ty::I64);
    for _ in 0..3 {
        fb.add_block_param(entry, Ty::I64);
    }

    // Header params: only the loop-carried (i, acc). `a` is NOT threaded — it is
    // used directly from the entry block, so it must stay live across the loop.
    let h_i = fb.add_block_param(header, Ty::I64);
    let h_acc = fb.add_block_param(header, Ty::I64);

    // Latch params: (i, acc, contribution) -> produces next-iteration values.
    let l_i = fb.add_block_param(latch, Ty::I64);
    let l_acc = fb.add_block_param(latch, Ty::I64);
    let l_contrib = fb.add_block_param(latch, Ty::I64);

    // Exit param: final accumulator.
    let e_acc = fb.add_block_param(exit, Ty::I64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    fb.br(header, vec![zero, zero]);

    fb.switch_to_block(header);
    let iters = fb.iconst(Ty::I64, ITERS as i128);
    let done = fb.icmp(ICmpOp::Sge, Ty::I64, h_i, iters);
    fb.condbr(done, exit, vec![h_acc], body, vec![]);

    fb.switch_to_block(body);
    let three = fb.iconst(Ty::I64, 3);
    let idx = fb.binop(BinOp::And, Ty::I64, h_i, three);
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
        case0,
        vec![],
    );

    // Each case: contribution = a * K[k]; jump to latch with (i, acc, contrib).
    // `a` is read directly here (the invariant live across the back-edge).
    for (case_bb, k) in [(case0, K[0]), (case1, K[1]), (case2, K[2]), (case3, K[3])] {
        fb.switch_to_block(case_bb);
        let kc = fb.iconst(Ty::I64, k);
        let contrib = fb.binop(BinOp::Mul, Ty::I64, a, kc);
        fb.br(latch, vec![h_i, h_acc, contrib]);
    }

    fb.switch_to_block(latch);
    let new_acc = fb.binop(BinOp::Add, Ty::I64, l_acc, l_contrib);
    let one = fb.iconst(Ty::I64, 1);
    let new_i = fb.binop(BinOp::Add, Ty::I64, l_i, one);
    fb.br(header, vec![new_i, new_acc]);

    fb.switch_to_block(exit);
    fb.ret(vec![e_acc]);

    fb.build();
    mb.build()
}

#[test]
fn jump_table_in_loop_matches_reference() {
    let m = build_jump_table_in_loop();
    let inputs = [0i64, 1, 2, 3, 7, -1, -3, 100, 12345, 0x7fff_ffff];
    for &a in &inputs {
        let want = reference(a);
        for fast in [true, false] {
            for opt in OPTS {
                let got = jit1(&m, opt, fast, a);
                assert_eq!(
                    got, want,
                    "jump table in loop: a={a} opt={opt:?} fast={fast} (want={want})"
                );
            }
        }
    }
}
