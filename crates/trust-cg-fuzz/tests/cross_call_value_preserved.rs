// trust-cg-fuzz/tests/cross_call_value_preserved.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Regression: a value that is LIVE ACROSS A CALL must survive the call at every
// optimization level under every register allocator. Before the post-RA
// coalescer fix, `try_rename_coalesce` would stop its forward scan at a call,
// fail to see (and rename) a use of the copy destination AFTER the call, and
// then remove the copy anyway — leaving the post-call use reading an undefined
// register. This reproduced as O3 returning the callee's result (or address
// garbage) instead of the value the caller stored before the call.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{BinOp, Ty};
use trust_ir_build::ModuleBuilder;

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn jit4(module: &trust_ir::Module, opt: OptLevel, fast: bool, row: [i64; 4]) -> i64 {
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
    let v = f(row[0], row[1], row[2], row[3]);
    drop(buf);
    v
}

/// `store a -> slot; call (clobbers caller-saved); load slot -> ret`.
/// The slot value (== a) is live across the call. Correct result is always a.
fn build_store_load_across_call() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let callee_ty = mb.add_func_type(vec![], vec![Ty::I64]);
    {
        let mut cb = mb.function("callee", callee_ty);
        let ce = cb.create_block();
        cb.switch_to_block(ce);
        let k = cb.iconst(Ty::I64, 999);
        cb.ret(vec![k]);
        cb.build();
    }
    let callee_id = trust_ir::FuncId::new(0);
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    for _ in 0..3 {
        fb.add_block_param(e, Ty::I64);
    }
    fb.switch_to_block(e);
    let slot = fb.alloca(Ty::I64);
    fb.store(Ty::I64, slot, a);
    let _ = fb.call(callee_id, vec![]);
    let loaded = fb.load(Ty::I64, slot);
    fb.ret(vec![loaded]);
    fb.build();
    mb.build()
}

#[test]
fn store_load_across_call_preserves_value() {
    let m = build_store_load_across_call();
    for &row in &[
        [123_456_789, 0, 0, 0],
        [1, 2, 3, 4],
        [-1, 7, 0, 0],
        [i64::MAX, 0, 0, 0],
    ] {
        let want = row[0];
        for fast in [true, false] {
            for opt in OPTS {
                let got = jit4(&m, opt, fast, row);
                assert_eq!(
                    got, want,
                    "store/load across call: opt={opt:?} fast={fast} row={row:?}"
                );
            }
        }
    }
}

/// A narrow (i16) value passed as `nargs` callee args AND kept live across the
/// call, then sign-extended after the call and combined with the call result.
fn build_narrow_across_call(nargs: usize) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let callee_ty = mb.add_func_type(vec![Ty::I16; nargs], vec![Ty::I64]);
    let callee_id = {
        let mut fb = mb.function("clobber", callee_ty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..nargs)
            .map(|_| fb.add_block_param(blk, Ty::I16))
            .collect();
        fb.switch_to_block(blk);
        let mut acc = p[0];
        for i in 0..nargs {
            let k = fb.iconst(Ty::I16, (0x9e37_79b1_i128 + (i as i128) * 0x193) & 0xffff);
            let m = fb.binop(BinOp::Mul, Ty::I16, p[i], k);
            acc = fb.binop(BinOp::Add, Ty::I16, acc, m);
            acc = fb.binop(BinOp::Xor, Ty::I16, acc, p[(i + 1) % nargs]);
        }
        let wide = fb.sext(Ty::I16, Ty::I64, acc);
        fb.ret(vec![wide]);
        fb.build()
    };
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    {
        let mut fb = mb.function("fuzz_fn", entry_ty);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I64);
        for _ in 0..3 {
            fb.add_block_param(e, Ty::I64);
        }
        fb.switch_to_block(e);
        let k = fb.iconst(Ty::I64, 0x0100_0193 + 0x55);
        let mixed = fb.binop(BinOp::Mul, Ty::I64, a, k);
        let mixed = fb.binop(BinOp::Xor, Ty::I64, mixed, a);
        let narrow = fb.trunc(Ty::I64, Ty::I16, mixed);
        let args: Vec<_> = (0..nargs).map(|_| narrow).collect();
        let call_ret = fb.call(callee_id, args);
        let widened = fb.sext(Ty::I16, Ty::I64, narrow);
        let out = fb.binop(BinOp::Add, Ty::I64, call_ret, widened);
        fb.ret(vec![out]);
        fb.build();
    }
    mb.build()
}

// Regression for defect #4b: a narrow (i16) value passed as 5+ callee args while
// also live across the call was miscompiled at O1+. The post-regalloc call-arg
// dest-preserve fixup (`aarch64_call_arg_dest_preserves`) inserted a spurious
// save/restore (`mov x9, x4` ... `mov x4, x9`) of a DEAD value the allocator had
// parked in the 5th arg register (x4), restoring it over the real argument that
// `uxth w4, w5` had just materialized. The fixup is now liveness-aware: it only
// preserves an arg register whose setup value actually reaches the call. (The
// scenario is *exposed* by the sound `uxtw(uxth(x))->uxth(x)` declarative-rewrite
// rule, which shifts which vreg the args read.)
#[test]
fn narrow_value_across_call_matches_o0() {
    // O0 is the trusted reference (it never runs the coalescer). Every higher
    // opt level under both allocators must agree with it.
    for nargs in [5usize, 6, 8] {
        let m = build_narrow_across_call(nargs);
        for a in [1i64, -1, 12345, 2, 3, 0x7fff_ffff] {
            let row = [a, 0, 0, 0];
            let reference = jit4(&m, OptLevel::O0, true, row);
            for fast in [true, false] {
                for opt in OPTS {
                    let got = jit4(&m, opt, fast, row);
                    assert_eq!(
                        got, reference,
                        "narrow across call: nargs={nargs} a={a} opt={opt:?} fast={fast}"
                    );
                }
            }
        }
    }
}
