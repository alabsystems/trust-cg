// trust-cg-fuzz/tests/sweep3_select_switch_calls.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// SWEEP3 surface: "select_switch_calls".
//
// Differential fuzzing of control flow whose arms / bodies invoke functions:
//   * select / switch whose arms call functions
//   * switch-in-loop with a call in the body
//   * phi (block params) of call results across many predecessors
//   * condbr trees feeding calls
//
// For every generated module we cross-check, on each input row:
//   * the trust_ir interpreter oracle (`run_oracle_one`),
//   * a pure-Rust two's-complement ground-truth reference,
//   * the JIT at O0/O1/O2/O3 under BOTH register allocators
//     (jit_fast == fast regalloc on; for_host_jit with fast regalloc OFF).
//
// A DEFECT is any disagreement among defined values (oracle vs any JIT, native
// reference vs any JIT, or JIT vs JIT), or a compile-error / panic on a module
// the oracle accepted.
//
// Anti-false-positive: all arithmetic is wrapping; divisors are forced nonzero
// (`x | 1`); shift amounts are masked; no floats; no uninitialized / OOB memory.
// Every callee and the entry use a plain 4xI64->I64 (or NxI64->I64) signature so
// the oracle accepts them and the native reference is exact.

// The jit_diff harness is unix-only (its per-invoke sandbox is a POSIX fork);
// mirror that gate here so the test compiles out cleanly on non-unix hosts
// rather than failing to resolve `trust_cg_fuzz::jit_diff`.
#![cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::run_oracle_one;
use trust_ir::{BinOp, ICmpOp, SwitchCase, Ty};
use trust_ir_build::ModuleBuilder;

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// All the input rows we exercise. Chosen to cover small-magnitude, negative,
/// boundary, and switch-index-selecting values.
fn rows() -> Vec<[i64; 4]> {
    vec![
        [0, 0, 0, 0],
        [1, 2, 3, 4],
        [-1, -2, -3, -4],
        [7, 11, 13, 17],
        [i64::MAX, i64::MIN, 0, 1],
        [i64::MIN, i64::MAX, -1, 2],
        [3, 0, 5, 8],
        [-7, 100, 0x7fff_ffff, -0x7fff_ffff],
        [123_456_789, 987_654_321, 42, -42],
        [2, 2, 2, 2],
        [5, 4, 3, 2],
        [0, 1, 2, 3],
        [4, 5, 6, 7],
        [-100, -200, 300, 400],
        [1_000_000, -1_000_000, 17, 19],
    ]
}

/// Compile `module` for one (opt, fast-regalloc) point and run `fuzz_fn(row)`.
/// Returns `Ok(value)` on a clean run, or `Err(reason)` on compile error /
/// panic (caught) so the caller can treat it as a defect against an
/// oracle-accepted module.
fn jit_run(
    module: &trust_ir::Module,
    opt: OptLevel,
    fast: bool,
    row: [i64; 4],
) -> Result<i64, String> {
    let externs: HashMap<String, *const u8> = HashMap::new();
    let mut cfg = if fast {
        CompilerConfig::jit_fast(Target::host())
    } else {
        let mut c = CompilerConfig::for_host_jit();
        c.enable_jit_fast_regalloc = false;
        c
    };
    cfg.opt_level = opt;

    let compiled = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        Compiler::new(cfg)
            .compile_module_to_jit(module, &externs)
            .map_err(Box::new)
    }));
    let buf = match compiled {
        Ok(Ok(result)) => result.buffer,
        Ok(Err(e)) => return Err(format!("compile_err: {:?}", e)),
        Err(_) => return Err("compile_panic".to_string()),
    };
    let f = match unsafe { buf.get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>("fuzz_fn") }
    {
        Some(p) => p.into_inner(),
        None => return Err("symbol_not_found".to_string()),
    };
    let called = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        f(row[0], row[1], row[2], row[3])
    }));
    drop(buf);
    match called {
        Ok(v) => Ok(v),
        Err(_) => Err("jit_call_panic".to_string()),
    }
}

/// Run the full differential matrix for `(module, native_ref)` over all rows.
/// Panics with a minimal description on the first disagreement found.
fn diff_module(label: &str, module: &trust_ir::Module, native: impl Fn(&[i64; 4]) -> i64) {
    for row in rows() {
        let want = native(&row);
        let oracle = run_oracle_one(module, &row);

        // Oracle must accept these modules (plain int signature, no alloca in
        // the call/select/switch shapes). If it does, it must equal the native
        // reference; if the native ref itself is wrong that is a test bug, not a
        // compiler defect, so assert it loudly.
        if let Ok(o) = oracle {
            assert_eq!(
                o, want,
                "[{label}] native reference disagrees with interpreter oracle: \
                 interp={o} native={want} row={row:?} (TEST BUG, not a compiler defect)"
            );
        } else {
            // Oracle rejected/erred: skip native cross-check but still require
            // cross-config JIT agreement below (handled by collecting results).
        }

        let mut results: Vec<(String, i64)> = Vec::new();
        for fast in [true, false] {
            for opt in OPTS {
                match jit_run(module, opt, fast, row) {
                    Ok(v) => {
                        let cfg = format!("opt={opt:?} fast={fast}");
                        // Against the native ground truth (always defined here).
                        assert_eq!(
                            v, want,
                            "[{label}] DEFECT: JIT disagrees with native reference: \
                             jit={v} native={want} {cfg} row={row:?}"
                        );
                        results.push((cfg, v));
                    }
                    Err(reason) => {
                        // Compile error / panic on an oracle-accepted module is a
                        // defect. If the oracle also rejected the module we do not
                        // flag it (kept defensive though all modules here are
                        // oracle-accepted by construction).
                        if oracle.is_ok() {
                            panic!(
                                "[{label}] DEFECT: {reason} on oracle-accepted module \
                                 at opt={opt:?} fast={fast} row={row:?}"
                            );
                        }
                    }
                }
            }
        }

        // Cross-config JIT agreement (redundant with the native check above when
        // every config returned a value, but catches the all-disagree-with-native
        // case explicitly and documents intent).
        if let Some((_, first)) = results.first() {
            for (cfg, v) in &results {
                assert_eq!(
                    v, first,
                    "[{label}] DEFECT: JIT configs disagree: {cfg}={v} differs from baseline \
                     {first} row={row:?}"
                );
            }
        }
    }
}

/// Differential check for a single explicit `(row, want)` pair. Same contract
/// as `diff_module` but lets a test supply its own rows / precomputed native
/// reference (used by shapes that want to land on specific switch values).
fn diff_one_module_row(label: &str, module: &trust_ir::Module, row: &[i64; 4], want: i64) {
    let oracle = run_oracle_one(module, row);
    if let Ok(o) = oracle {
        assert_eq!(
            o, want,
            "[{label}] native reference disagrees with interpreter oracle: \
             interp={o} native={want} row={row:?} (TEST BUG, not a compiler defect)"
        );
    }

    let mut results: Vec<(String, i64)> = Vec::new();
    for fast in [true, false] {
        for opt in OPTS {
            match jit_run(module, opt, fast, *row) {
                Ok(v) => {
                    let cfg = format!("opt={opt:?} fast={fast}");
                    assert_eq!(
                        v, want,
                        "[{label}] DEFECT: JIT disagrees with native reference: \
                         jit={v} native={want} {cfg} row={row:?}"
                    );
                    results.push((cfg, v));
                }
                Err(reason) => {
                    if oracle.is_ok() {
                        panic!(
                            "[{label}] DEFECT: {reason} on oracle-accepted module \
                             at opt={opt:?} fast={fast} row={row:?}"
                        );
                    }
                }
            }
        }
    }

    if let Some((_, first)) = results.first() {
        for (cfg, v) in &results {
            assert_eq!(
                v, first,
                "[{label}] DEFECT: JIT configs disagree: {cfg}={v} differs from baseline \
                 {first} row={row:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Shape 1: `select` whose two arms are CALL RESULTS.
//   r = cond ? callA(args) : callB(args)
// Both calls are evaluated (no short-circuit in select), then one result is
// chosen. This stresses keeping two call results live simultaneously and the
// select lowering picking the right one.
// ---------------------------------------------------------------------------

/// callA(a,b,c,d) = a*3 + b - c ^ d   (wrapping)
fn ref_call_a(a: i64, b: i64, c: i64, d: i64) -> i64 {
    a.wrapping_mul(3).wrapping_add(b).wrapping_sub(c) ^ d
}
/// callB(a,b,c,d) = (a ^ b) + c*5 - d   (wrapping)
fn ref_call_b(a: i64, b: i64, c: i64, d: i64) -> i64 {
    (a ^ b).wrapping_add(c.wrapping_mul(5)).wrapping_sub(d)
}

fn build_select_of_call_results() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    // callA
    let call_a = {
        let mut fb = mb.function("call_a", cty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        let three = fb.iconst(Ty::I64, 3);
        let t = fb.binop(BinOp::Mul, Ty::I64, p[0], three);
        let t = fb.binop(BinOp::Add, Ty::I64, t, p[1]);
        let t = fb.binop(BinOp::Sub, Ty::I64, t, p[2]);
        let t = fb.binop(BinOp::Xor, Ty::I64, t, p[3]);
        fb.ret(vec![t]);
        fb.build()
    };
    // callB
    let call_b = {
        let mut fb = mb.function("call_b", cty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        let xab = fb.binop(BinOp::Xor, Ty::I64, p[0], p[1]);
        let five = fb.iconst(Ty::I64, 5);
        let c5 = fb.binop(BinOp::Mul, Ty::I64, p[2], five);
        let t = fb.binop(BinOp::Add, Ty::I64, xab, c5);
        let t = fb.binop(BinOp::Sub, Ty::I64, t, p[3]);
        fb.ret(vec![t]);
        fb.build()
    };

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let ra = fb.call(call_a, vec![a, b, c, d]);
    let rb = fb.call(call_b, vec![a, b, c, d]);
    // cond = a > b (signed)
    let cond = fb.icmp(ICmpOp::Sgt, Ty::I64, a, b);
    let r = fb.select(Ty::I64, cond, ra, rb);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

#[test]
fn select_of_call_results() {
    let m = build_select_of_call_results();
    diff_module("select_of_call_results", &m, |r| {
        let (a, b, c, d) = (r[0], r[1], r[2], r[3]);
        if a > b {
            ref_call_a(a, b, c, d)
        } else {
            ref_call_b(a, b, c, d)
        }
    });
}

// ---------------------------------------------------------------------------
// Shape 2: dense `switch` whose arms each call a DIFFERENT function, results
// joined via a block param (phi) at the merge.
//   idx = a & 3
//   switch idx { 0 => f0(...), 1 => f1(...), 2 => f2(...), 3 => f3(...) }
//   merge(r): ret r
// ---------------------------------------------------------------------------

fn build_switch_arms_call() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    // Four distinct callees with distinct mixing so a mis-dispatch is visible.
    let mut callees = Vec::new();
    for (k_idx, (mul, add)) in [(2i128, 10i128), (3, 20), (5, 30), (7, 40)]
        .into_iter()
        .enumerate()
    {
        let f = {
            let name = format!("case_fn_{k_idx}");
            let mut fb = mb.function(name, cty);
            let blk = fb.create_block();
            let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
            fb.switch_to_block(blk);
            let m = fb.iconst(Ty::I64, mul);
            let ad = fb.iconst(Ty::I64, add);
            let t = fb.binop(BinOp::Mul, Ty::I64, p[0], m);
            let t = fb.binop(BinOp::Add, Ty::I64, t, ad);
            let t = fb.binop(BinOp::Xor, Ty::I64, t, p[1]);
            let t = fb.binop(BinOp::Add, Ty::I64, t, p[2]);
            let t = fb.binop(BinOp::Sub, Ty::I64, t, p[3]);
            fb.ret(vec![t]);
            fb.build()
        };
        callees.push(f);
    }

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);

    let case0 = fb.create_block();
    let case1 = fb.create_block();
    let case2 = fb.create_block();
    let case3 = fb.create_block();
    let merge = fb.create_block();
    let m_r = fb.add_block_param(merge, Ty::I64);

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
        case0,
        vec![],
    );

    for (case_bb, callee) in [
        (case0, callees[0]),
        (case1, callees[1]),
        (case2, callees[2]),
        (case3, callees[3]),
    ] {
        fb.switch_to_block(case_bb);
        let r = fb.call(callee, vec![a, b, c, d]);
        fb.br(merge, vec![r]);
    }

    fb.switch_to_block(merge);
    fb.ret(vec![m_r]);
    fb.build();
    mb.build()
}

fn ref_switch_arms_call(r: &[i64; 4]) -> i64 {
    let (a, b, c, d) = (r[0], r[1], r[2], r[3]);
    let (mul, add) = match a & 3 {
        0 => (2i64, 10i64),
        1 => (3, 20),
        2 => (5, 30),
        _ => (7, 40),
    };
    let t = a.wrapping_mul(mul).wrapping_add(add) ^ b;
    t.wrapping_add(c).wrapping_sub(d)
}

#[test]
fn switch_arms_call() {
    let m = build_switch_arms_call();
    diff_module("switch_arms_call", &m, ref_switch_arms_call);
}

// ---------------------------------------------------------------------------
// Shape 3: switch-in-loop with a call in the body.
//   acc = 0; i = 0
//   loop:
//     if i >= N goto exit
//     switch (i & 3) { 0..3 => caseK }
//     caseK: contrib = mixK(a, i, acc); acc += contrib; i++; goto loop
//   exit: ret acc
// `mixK` is a real function call inside the loop body; `a` is loop-invariant and
// live across the back-edge AND across the call.
// ---------------------------------------------------------------------------

const LOOP_N: i64 = 6;

fn ref_loop_mix(callee_idx: i64, a: i64, i: i64, acc: i64) -> i64 {
    // Must mirror the IR mixK exactly.
    let k = (callee_idx + 1).wrapping_mul(0x11);
    a.wrapping_mul(k).wrapping_add(i).wrapping_mul(acc | 1) ^ (i.wrapping_add(callee_idx))
}

fn ref_switch_in_loop(r: &[i64; 4]) -> i64 {
    let a = r[0];
    let mut acc: i64 = 0;
    let mut i: i64 = 0;
    while i < LOOP_N {
        let idx = i & 3;
        let contrib = ref_loop_mix(idx, a, i, acc);
        acc = acc.wrapping_add(contrib);
        i = i.wrapping_add(1);
    }
    acc
}

fn build_switch_in_loop_call() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    // mixK(a, i, acc, kidx) -> a*((kidx+1)*0x11) + i) * (acc|1) ^ (i + kidx)
    let mut mixers = Vec::new();
    for kidx in 0..4i128 {
        let f = {
            let name = format!("mix_{kidx}");
            let mut fb = mb.function(name, cty);
            let blk = fb.create_block();
            // params: a, i, acc, (unused)
            let pa = fb.add_block_param(blk, Ty::I64);
            let pi = fb.add_block_param(blk, Ty::I64);
            let pacc = fb.add_block_param(blk, Ty::I64);
            let _unused = fb.add_block_param(blk, Ty::I64);
            fb.switch_to_block(blk);
            let k = fb.iconst(Ty::I64, (kidx + 1) * 0x11);
            let t = fb.binop(BinOp::Mul, Ty::I64, pa, k);
            let t = fb.binop(BinOp::Add, Ty::I64, t, pi);
            let one = fb.iconst(Ty::I64, 1);
            let acc_or1 = fb.binop(BinOp::Or, Ty::I64, pacc, one);
            let t = fb.binop(BinOp::Mul, Ty::I64, t, acc_or1);
            let kc = fb.iconst(Ty::I64, kidx);
            let ik = fb.binop(BinOp::Add, Ty::I64, pi, kc);
            let t = fb.binop(BinOp::Xor, Ty::I64, t, ik);
            fb.ret(vec![t]);
            fb.build()
        };
        mixers.push(f);
    }

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);

    let entry = fb.create_block();
    let header = fb.create_block();
    let body = fb.create_block();
    let case0 = fb.create_block();
    let case1 = fb.create_block();
    let case2 = fb.create_block();
    let case3 = fb.create_block();
    let latch = fb.create_block();
    let exit = fb.create_block();

    let a = fb.add_block_param(entry, Ty::I64);
    for _ in 0..3 {
        fb.add_block_param(entry, Ty::I64);
    }
    // header params: i, acc
    let h_i = fb.add_block_param(header, Ty::I64);
    let h_acc = fb.add_block_param(header, Ty::I64);
    // latch params: i, acc, contrib
    let l_i = fb.add_block_param(latch, Ty::I64);
    let l_acc = fb.add_block_param(latch, Ty::I64);
    let l_contrib = fb.add_block_param(latch, Ty::I64);
    // exit param: final acc
    let e_acc = fb.add_block_param(exit, Ty::I64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    fb.br(header, vec![zero, zero]);

    fb.switch_to_block(header);
    let n = fb.iconst(Ty::I64, LOOP_N as i128);
    let done = fb.icmp(ICmpOp::Sge, Ty::I64, h_i, n);
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

    for (case_bb, mixer) in [
        (case0, mixers[0]),
        (case1, mixers[1]),
        (case2, mixers[2]),
        (case3, mixers[3]),
    ] {
        fb.switch_to_block(case_bb);
        // a is read directly from entry (loop-invariant live across back-edge AND call).
        let contrib = fb.call(mixer, vec![a, h_i, h_acc, a]);
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
fn switch_in_loop_call() {
    let m = build_switch_in_loop_call();
    diff_module("switch_in_loop_call", &m, ref_switch_in_loop);
}

// ---------------------------------------------------------------------------
// Shape 4: phi of CALL RESULTS across MANY predecessors.
//   A condbr tree routes to one of 8 blocks; each block calls a distinct
//   function and branches to a common merge block carrying the call result as
//   a block param. The merge then folds the phi'd value with another call.
// ---------------------------------------------------------------------------

const NUM_PREDS: usize = 8;

fn build_phi_of_calls_many_preds() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    // NUM_PREDS leaf callees + 1 finalizer callee.
    let mut leaves = Vec::new();
    for j in 0..NUM_PREDS as i128 {
        let f = {
            let name = format!("leaf_{j}");
            let mut fb = mb.function(name, cty);
            let blk = fb.create_block();
            let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
            fb.switch_to_block(blk);
            let kc = fb.iconst(Ty::I64, (j + 1) * 0x1000_0001);
            let t = fb.binop(BinOp::Mul, Ty::I64, p[0], kc);
            let t = fb.binop(BinOp::Add, Ty::I64, t, p[1]);
            let jc = fb.iconst(Ty::I64, j * 7 + 1);
            let t = fb.binop(BinOp::Xor, Ty::I64, t, jc);
            let t = fb.binop(BinOp::Sub, Ty::I64, t, p[2]);
            let t = fb.binop(BinOp::Add, Ty::I64, t, p[3]);
            fb.ret(vec![t]);
            fb.build()
        };
        leaves.push(f);
    }
    let finalizer = {
        let mut fb = mb.function("finalizer", cty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        // (phi ^ a) + b*9 - c + d
        let t = fb.binop(BinOp::Xor, Ty::I64, p[0], p[1]);
        let nine = fb.iconst(Ty::I64, 9);
        let b9 = fb.binop(BinOp::Mul, Ty::I64, p[2], nine);
        let t = fb.binop(BinOp::Add, Ty::I64, t, b9);
        let t = fb.binop(BinOp::Sub, Ty::I64, t, p[3]);
        fb.ret(vec![t]);
        fb.build()
    };

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);

    let pred_blocks: Vec<_> = (0..NUM_PREDS).map(|_| fb.create_block()).collect();
    let merge = fb.create_block();
    let m_phi = fb.add_block_param(merge, Ty::I64);

    // Use a switch (sel = a & 7) to fan out to NUM_PREDS predecessors. (Dense
    // switch == jump table; covers the many-pred phi join cleanly.)
    fb.switch_to_block(e);
    let seven = fb.iconst(Ty::I64, (NUM_PREDS - 1) as i128);
    let sel = fb.binop(BinOp::And, Ty::I64, a, seven);
    let cases: Vec<SwitchCase> = (0..NUM_PREDS)
        .map(|j| SwitchCase {
            value: trust_ir::Constant::Int(j as i128),
            target: pred_blocks[j],
            args: vec![],
        })
        .collect();
    fb.switch(sel, cases, pred_blocks[0], vec![]);

    for (j, &pb) in pred_blocks.iter().enumerate() {
        fb.switch_to_block(pb);
        let r = fb.call(leaves[j], vec![a, b, c, d]);
        fb.br(merge, vec![r]);
    }

    fb.switch_to_block(merge);
    // finalizer(phi, a, b, c)
    let fin = fb.call(finalizer, vec![m_phi, a, b, c]);
    fb.ret(vec![fin]);
    fb.build();
    mb.build()
}

fn ref_leaf(j: i64, a: i64, b: i64, c: i64, d: i64) -> i64 {
    let t = a.wrapping_mul((j + 1).wrapping_mul(0x1000_0001));
    let t = t.wrapping_add(b) ^ (j * 7 + 1);
    t.wrapping_sub(c).wrapping_add(d)
}

fn ref_phi_of_calls(r: &[i64; 4]) -> i64 {
    let (a, b, c, d) = (r[0], r[1], r[2], r[3]);
    let j = a & (NUM_PREDS as i64 - 1);
    let phi = ref_leaf(j, a, b, c, d);
    // finalizer(phi, a, b, c): (phi ^ a) + b*9 - c
    let t = (phi ^ a).wrapping_add(b.wrapping_mul(9));
    t.wrapping_sub(c)
}

#[test]
fn phi_of_calls_many_preds() {
    let m = build_phi_of_calls_many_preds();
    diff_module("phi_of_calls_many_preds", &m, ref_phi_of_calls);
}

// ---------------------------------------------------------------------------
// Shape 5: condbr TREE feeding calls.
//   A binary decision tree of condbr (depth 3 -> 8 leaves). Each interior node
//   tests a different predicate on (a,b,c,d); each leaf calls a function. The
//   results merge through a chain of block params (phi). This exercises the
//   condbr lowering + call-result liveness across an irregular CFG.
// ---------------------------------------------------------------------------

fn build_condbr_tree_calls() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    let mut leaves = Vec::new();
    for j in 0..8i128 {
        let f = {
            let name = format!("tleaf_{j}");
            let mut fb = mb.function(name, cty);
            let blk = fb.create_block();
            let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
            fb.switch_to_block(blk);
            let kc = fb.iconst(Ty::I64, (j + 3) * 0x101);
            let t = fb.binop(BinOp::Mul, Ty::I64, p[0], kc);
            let t = fb.binop(BinOp::Sub, Ty::I64, t, p[1]);
            let t = fb.binop(BinOp::Xor, Ty::I64, t, p[2]);
            let t = fb.binop(BinOp::Add, Ty::I64, t, p[3]);
            let jc = fb.iconst(Ty::I64, j);
            let t = fb.binop(BinOp::Add, Ty::I64, t, jc);
            fb.ret(vec![t]);
            fb.build()
        };
        leaves.push(f);
    }

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);

    // depth-1 nodes
    let n_l = fb.create_block();
    let n_r = fb.create_block();
    // depth-2 nodes
    let n_ll = fb.create_block();
    let n_lr = fb.create_block();
    let n_rl = fb.create_block();
    let n_rr = fb.create_block();
    // 8 leaf blocks
    let leaf_bb: Vec<_> = (0..8).map(|_| fb.create_block()).collect();
    // merge
    let merge = fb.create_block();
    let m_phi = fb.add_block_param(merge, Ty::I64);

    // Root: a > b
    fb.switch_to_block(e);
    let c0 = fb.icmp(ICmpOp::Sgt, Ty::I64, a, b);
    fb.condbr(c0, n_l, vec![], n_r, vec![]);

    // depth-1 left: c > d ; right: c < d
    fb.switch_to_block(n_l);
    let c1l = fb.icmp(ICmpOp::Sgt, Ty::I64, c, d);
    fb.condbr(c1l, n_ll, vec![], n_lr, vec![]);
    fb.switch_to_block(n_r);
    let c1r = fb.icmp(ICmpOp::Slt, Ty::I64, c, d);
    fb.condbr(c1r, n_rl, vec![], n_rr, vec![]);

    // depth-2: low-bit predicates. Routed so the left subtree uses bit0 of
    // (a^c)/(b^d), the right subtree bit0 of (a^d)/(b^c). Constants are
    // materialized inside each block so they dominate their uses.
    for (blk, lhs, rhs, then_bb, else_bb) in [
        (n_ll, a, c, leaf_bb[0], leaf_bb[1]),
        (n_lr, b, d, leaf_bb[2], leaf_bb[3]),
        (n_rl, a, d, leaf_bb[4], leaf_bb[5]),
        (n_rr, b, c, leaf_bb[6], leaf_bb[7]),
    ] {
        fb.switch_to_block(blk);
        let one = fb.iconst(Ty::I64, 1);
        let zero = fb.iconst(Ty::I64, 0);
        let x = fb.binop(BinOp::Xor, Ty::I64, lhs, rhs);
        let lsb = fb.binop(BinOp::And, Ty::I64, x, one);
        let p = fb.icmp(ICmpOp::Ne, Ty::I64, lsb, zero);
        fb.condbr(p, then_bb, vec![], else_bb, vec![]);
    }

    for (j, &lb) in leaf_bb.iter().enumerate() {
        fb.switch_to_block(lb);
        let r = fb.call(leaves[j], vec![a, b, c, d]);
        fb.br(merge, vec![r]);
    }

    fb.switch_to_block(merge);
    fb.ret(vec![m_phi]);
    fb.build();
    mb.build()
}

fn ref_tleaf(j: i64, a: i64, b: i64, c: i64, d: i64) -> i64 {
    let kc = (j + 3).wrapping_mul(0x101);
    let t = a.wrapping_mul(kc).wrapping_sub(b) ^ c;
    t.wrapping_add(d).wrapping_add(j)
}

fn ref_condbr_tree(r: &[i64; 4]) -> i64 {
    let (a, b, c, d) = (r[0], r[1], r[2], r[3]);
    let j = if a > b {
        // left
        if c > d {
            // n_ll: bit0 of (a^c)
            if ((a ^ c) & 1) != 0 { 0 } else { 1 }
        } else {
            // n_lr: bit0 of (b^d)
            if ((b ^ d) & 1) != 0 { 2 } else { 3 }
        }
    } else {
        // right
        if c < d {
            // n_rl: bit0 of (a^d)
            if ((a ^ d) & 1) != 0 { 4 } else { 5 }
        } else {
            // n_rr: bit0 of (b^c)
            if ((b ^ c) & 1) != 0 { 6 } else { 7 }
        }
    };
    ref_tleaf(j, a, b, c, d)
}

#[test]
fn condbr_tree_calls() {
    let m = build_condbr_tree_calls();
    diff_module("condbr_tree_calls", &m, ref_condbr_tree);
}

// ---------------------------------------------------------------------------
// Shape 6: select whose CONDITION is itself a call result, and whose arms are
// also call results, all live simultaneously across multiple calls.
//   p = pred(a,b)         // returns 0/1
//   x = compA(a,b,c,d)
//   y = compB(a,b,c,d)
//   r = (p != 0) ? x : y
// Stresses three call results live across the select.
// ---------------------------------------------------------------------------

fn build_select_cond_and_arms_calls() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let pred_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let comp_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    let pred = {
        let mut fb = mb.function("pred", pred_ty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        // returns 1 if (a+b) is even else 0
        let s = fb.binop(BinOp::Add, Ty::I64, p[0], p[1]);
        let one = fb.iconst(Ty::I64, 1);
        let lsb = fb.binop(BinOp::And, Ty::I64, s, one);
        // even -> lsb==0 -> return 1
        let zero = fb.iconst(Ty::I64, 0);
        let is_even = fb.icmp(ICmpOp::Eq, Ty::I64, lsb, zero);
        let z2 = fb.iconst(Ty::I64, 0);
        let o2 = fb.iconst(Ty::I64, 1);
        let res = fb.select(Ty::I64, is_even, o2, z2);
        fb.ret(vec![res]);
        fb.build()
    };
    let comp_a = {
        let mut fb = mb.function("comp_a", comp_ty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        let four = fb.iconst(Ty::I64, 4);
        let t = fb.binop(BinOp::Mul, Ty::I64, p[0], four);
        let t = fb.binop(BinOp::Add, Ty::I64, t, p[1]);
        let t = fb.binop(BinOp::Sub, Ty::I64, t, p[2]);
        let t = fb.binop(BinOp::Xor, Ty::I64, t, p[3]);
        fb.ret(vec![t]);
        fb.build()
    };
    let comp_b = {
        let mut fb = mb.function("comp_b", comp_ty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        let six = fb.iconst(Ty::I64, 6);
        let t = fb.binop(BinOp::Mul, Ty::I64, p[1], six);
        let t = fb.binop(BinOp::Xor, Ty::I64, t, p[0]);
        let t = fb.binop(BinOp::Add, Ty::I64, t, p[2]);
        let t = fb.binop(BinOp::Sub, Ty::I64, t, p[3]);
        fb.ret(vec![t]);
        fb.build()
    };

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let p = fb.call(pred, vec![a, b, c, d]);
    let x = fb.call(comp_a, vec![a, b, c, d]);
    let y = fb.call(comp_b, vec![a, b, c, d]);
    let zero = fb.iconst(Ty::I64, 0);
    let cond = fb.icmp(ICmpOp::Ne, Ty::I64, p, zero);
    let r = fb.select(Ty::I64, cond, x, y);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

fn ref_select_cond_and_arms(r: &[i64; 4]) -> i64 {
    let (a, b, c, d) = (r[0], r[1], r[2], r[3]);
    let p = if (a.wrapping_add(b) & 1) == 0 { 1 } else { 0 };
    let x = a.wrapping_mul(4).wrapping_add(b).wrapping_sub(c) ^ d;
    let y = b.wrapping_mul(6) ^ a;
    let y = y.wrapping_add(c).wrapping_sub(d);
    if p != 0 { x } else { y }
}

#[test]
fn select_cond_and_arms_calls() {
    let m = build_select_cond_and_arms_calls();
    diff_module("select_cond_and_arms_calls", &m, ref_select_cond_and_arms);
}

// ---------------------------------------------------------------------------
// Shape 7: SPARSE switch with a non-trivial DEFAULT that also calls a function.
//   Case values are non-contiguous (3, 17, 256, -5) so the switch cannot lower
//   to a dense jump table; the default arm is reachable and itself calls a
//   distinct function. The selector is `b` directly (full i64 range), so most
//   rows fall through to default and a few hit specific cases.
//   sel = b
//   switch sel { 3=>s0, 17=>s1, 256=>s2, -5=>s3, default=>sd }
//   each arm: r = fn_k(a,b,c,d); merge(r): ret r
// ---------------------------------------------------------------------------

fn sparse_callee_mix(k: i64, a: i64, b: i64, c: i64, d: i64) -> i64 {
    // Distinct per-arm mixing so a mis-dispatch (wrong arm taken) is visible.
    let kk = (k.wrapping_add(1)).wrapping_mul(0x97);
    let t = a.wrapping_mul(kk).wrapping_add(b);
    let t = t ^ c.wrapping_mul(k.wrapping_add(2));
    t.wrapping_sub(d).wrapping_add(k.wrapping_mul(0x3ff))
}

fn build_sparse_switch_default_call() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    // 5 callees: indices 0..3 for the explicit cases, 4 for default.
    let mut callees = Vec::new();
    for k in 0..5i128 {
        let f = {
            let name = format!("sparse_fn_{k}");
            let mut fb = mb.function(name, cty);
            let blk = fb.create_block();
            let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
            fb.switch_to_block(blk);
            let kk = fb.iconst(Ty::I64, (k + 1) * 0x97);
            let t = fb.binop(BinOp::Mul, Ty::I64, p[0], kk);
            let t = fb.binop(BinOp::Add, Ty::I64, t, p[1]);
            let k2 = fb.iconst(Ty::I64, k + 2);
            let ck = fb.binop(BinOp::Mul, Ty::I64, p[2], k2);
            let t = fb.binop(BinOp::Xor, Ty::I64, t, ck);
            let t = fb.binop(BinOp::Sub, Ty::I64, t, p[3]);
            let k3 = fb.iconst(Ty::I64, k * 0x3ff);
            let t = fb.binop(BinOp::Add, Ty::I64, t, k3);
            fb.ret(vec![t]);
            fb.build()
        };
        callees.push(f);
    }

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);

    let s0 = fb.create_block();
    let s1 = fb.create_block();
    let s2 = fb.create_block();
    let s3 = fb.create_block();
    let sd = fb.create_block();
    let merge = fb.create_block();
    let m_r = fb.add_block_param(merge, Ty::I64);

    fb.switch_to_block(e);
    fb.switch(
        b,
        vec![
            SwitchCase {
                value: trust_ir::Constant::Int(3),
                target: s0,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(17),
                target: s1,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(256),
                target: s2,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(-5),
                target: s3,
                args: vec![],
            },
        ],
        sd,
        vec![],
    );

    for (case_bb, callee) in [
        (s0, callees[0]),
        (s1, callees[1]),
        (s2, callees[2]),
        (s3, callees[3]),
        (sd, callees[4]),
    ] {
        fb.switch_to_block(case_bb);
        let r = fb.call(callee, vec![a, b, c, d]);
        fb.br(merge, vec![r]);
    }

    fb.switch_to_block(merge);
    fb.ret(vec![m_r]);
    fb.build();
    mb.build()
}

fn ref_sparse_switch_default_call(r: &[i64; 4]) -> i64 {
    let (a, b, c, d) = (r[0], r[1], r[2], r[3]);
    let k = match b {
        3 => 0,
        17 => 1,
        256 => 2,
        -5 => 3,
        _ => 4,
    };
    sparse_callee_mix(k, a, b, c, d)
}

// Regression for #366: sparse switches with a negative case once attempted to
// materialize -5 with one `Movz`, which cannot encode the full 64-bit value.
// The case compare must use the canonical hw0 seed plus MOVK repair sequence.
//
// Bisection (empirically verified, see `sparse_switch_neg_case_min`): the calls
// in the arms are NOT required; the trigger is a SPARSE (low-density) switch with
// >=4 cases where one case value is negative / does not fit in an unsigned 16-bit
// immediate. A dense set like {1,2,3,-5} compiles fine (it picks a different
// dispatch strategy); the sparse set {3,17,256,-5} routes through the
// binary-search path where the historical bug lived.
#[test]
fn sparse_switch_default_call() {
    let m = build_sparse_switch_default_call();
    // Add rows that deliberately land on each explicit sparse case value of `b`.
    let mut all_rows = rows();
    all_rows.push([10, 3, 20, 30]);
    all_rows.push([11, 17, 21, 31]);
    all_rows.push([12, 256, 22, 32]);
    all_rows.push([13, -5, 23, 33]);
    all_rows.push([14, 4, 24, 34]); // default
    for row in all_rows {
        let want = ref_sparse_switch_default_call(&row);
        diff_one_module_row("sparse_switch_default_call", &m, &row, want);
    }
}

/// Minimized regression for #366 (NO calls, NO merge phi).
///
/// Bisection (verified empirically against this exact module):
///   * The calls in the arms of `build_sparse_switch_default_call` are NOT
///     required — a plain `switch` with `ret <const>` arms still triggers it.
///   * A DENSE 4-case set like {1,2,3,-5} compiles CLEANLY: density is high
///     enough that switch lowering picks a non-comparison dispatch strategy.
///   * The trigger is a SPARSE (low-density) switch with >=4 cases where one
///     case value is negative / does not fit in an unsigned 16-bit immediate.
///     The sparse spread {3, 17, 256, -5} routes through the binary-search
///     path. Its `emit_cmp` must materialize wide or negative values with the
///     canonical hw0 seed plus MOVK repair sequence before `CmpRR`.
///
/// The interpreter oracle and native execution must agree for every selector.
///
///   fuzz_fn(a,b,c,d):
///     switch b { 3 => r10, 17 => r20, 256 => r30, -5 => r99 }  default => r0
fn build_sparse_switch_neg_case_min() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let _a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);

    // Sparse spread incl. one negative value. Low density forces the
    // binary-search lowering that exposed the historical #366 materialization
    // bug.
    let case_vals: [i128; 4] = [3, 17, 256, -5];
    let case_rets: [i128; 4] = [10, 20, 30, 99];
    let case_blocks: Vec<_> = case_vals.iter().map(|_| fb.create_block()).collect();
    let def = fb.create_block();

    fb.switch_to_block(e);
    let cases: Vec<SwitchCase> = case_vals
        .iter()
        .zip(&case_blocks)
        .map(|(&v, &t)| SwitchCase {
            value: trust_ir::Constant::Int(v),
            target: t,
            args: vec![],
        })
        .collect();
    fb.switch(b, cases, def, vec![]);

    for (i, &cb) in case_blocks.iter().enumerate() {
        fb.switch_to_block(cb);
        let r = fb.iconst(Ty::I64, case_rets[i]);
        fb.ret(vec![r]);
    }

    fb.switch_to_block(def);
    let zero = fb.iconst(Ty::I64, 0);
    fb.ret(vec![zero]);
    fb.build();
    mb.build()
}

fn ref_sparse_switch_neg_case_min(b: i64) -> i64 {
    match b {
        3 => 10,
        17 => 20,
        256 => 30,
        -5 => 99,
        _ => 0,
    }
}

#[test]
fn sparse_switch_neg_case_min() {
    let m = build_sparse_switch_neg_case_min();
    // Oracle accepts and runs it for every selector value.
    for b in [-5i64, 0, 3, 17, 256, 7] {
        let row = [0i64, b, 0, 0];
        let want = ref_sparse_switch_neg_case_min(b);
        let oracle = run_oracle_one(&m, &row).expect("oracle must accept this module");
        assert_eq!(
            oracle, want,
            "oracle mismatch indicates a regression-test harness error"
        );
        let got = jit_run(&m, OptLevel::O0, true, row);
        assert_eq!(
            got,
            Ok(want),
            "#366 regression: JIT failed to compile/run sparse negative switch case: {got:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Shape 8: switch where MANY case values route to the SAME target block (call).
//   sel = a & 7  (0..7)
//   values {0,2,4,6} -> even_bb (calls even_fn)
//   values {1,3,5}   -> odd_bb  (calls odd_fn)
//   value  7         -> seven_bb (calls seven_fn)
// Tests case-merging / coalescing of switch targets that contain calls.
// ---------------------------------------------------------------------------

fn build_switch_shared_targets_call() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    let make = |mb: &mut ModuleBuilder, name: &str, mul: i128, add: i128| {
        let mut fb = mb.function(name, cty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        let mc = fb.iconst(Ty::I64, mul);
        let t = fb.binop(BinOp::Mul, Ty::I64, p[0], mc);
        let t = fb.binop(BinOp::Add, Ty::I64, t, p[1]);
        let ac = fb.iconst(Ty::I64, add);
        let t = fb.binop(BinOp::Add, Ty::I64, t, ac);
        let t = fb.binop(BinOp::Xor, Ty::I64, t, p[2]);
        let t = fb.binop(BinOp::Sub, Ty::I64, t, p[3]);
        fb.ret(vec![t]);
        fb.build()
    };
    let even_fn = make(&mut mb, "even_fn", 13, 100);
    let odd_fn = make(&mut mb, "odd_fn", 29, 200);
    let seven_fn = make(&mut mb, "seven_fn", 41, 300);

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);

    let even_bb = fb.create_block();
    let odd_bb = fb.create_block();
    let seven_bb = fb.create_block();
    let merge = fb.create_block();
    let m_r = fb.add_block_param(merge, Ty::I64);

    fb.switch_to_block(e);
    let seven = fb.iconst(Ty::I64, 7);
    let sel = fb.binop(BinOp::And, Ty::I64, a, seven);
    fb.switch(
        sel,
        vec![
            SwitchCase {
                value: trust_ir::Constant::Int(0),
                target: even_bb,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(2),
                target: even_bb,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(4),
                target: even_bb,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(6),
                target: even_bb,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(1),
                target: odd_bb,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(3),
                target: odd_bb,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(5),
                target: odd_bb,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(7),
                target: seven_bb,
                args: vec![],
            },
        ],
        // default unreachable for sel in 0..7, but must be valid; route to odd.
        odd_bb,
        vec![],
    );

    for (bb, callee) in [(even_bb, even_fn), (odd_bb, odd_fn), (seven_bb, seven_fn)] {
        fb.switch_to_block(bb);
        let r = fb.call(callee, vec![a, b, c, d]);
        fb.br(merge, vec![r]);
    }

    fb.switch_to_block(merge);
    fb.ret(vec![m_r]);
    fb.build();
    mb.build()
}

fn ref_switch_shared_targets_call(r: &[i64; 4]) -> i64 {
    let (a, b, c, d) = (r[0], r[1], r[2], r[3]);
    let sel = a & 7;
    let (mul, add) = match sel {
        0 | 2 | 4 | 6 => (13i64, 100i64),
        7 => (41, 300),
        _ => (29, 200), // 1,3,5 (and default, unreachable here)
    };
    let t = a.wrapping_mul(mul).wrapping_add(b).wrapping_add(add) ^ c;
    t.wrapping_sub(d)
}

#[test]
fn switch_shared_targets_call() {
    let m = build_switch_shared_targets_call();
    // Cover every value of a&7 to exercise each merged-target path.
    let mut all_rows = rows();
    for s in 0..8i64 {
        all_rows.push([s, 1000 + s, 7 - s, s * 3]);
    }
    for row in all_rows {
        let want = ref_switch_shared_targets_call(&row);
        diff_one_module_row("switch_shared_targets_call", &m, &row, want);
    }
}

// ---------------------------------------------------------------------------
// Shape 9: NESTED switch (switch-in-switch) whose innermost arms call functions.
//   outer = a & 1
//   if outer==0: inner = b & 1 -> {g00, g01}
//   if outer==1: inner = c & 1 -> {g10, g11}
//   all four call distinct functions, results phi up through two merges.
// Stresses nested dispatch + phi chains feeding/consuming calls.
// ---------------------------------------------------------------------------

fn build_nested_switch_calls() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    let make = |mb: &mut ModuleBuilder, name: &str, tag: i128| {
        let mut fb = mb.function(name, cty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        let tg = fb.iconst(Ty::I64, tag.wrapping_mul(0x5bd1_e995));
        let t = fb.binop(BinOp::Add, Ty::I64, p[0], tg);
        let t = fb.binop(BinOp::Mul, Ty::I64, t, p[1]);
        let t = fb.binop(BinOp::Xor, Ty::I64, t, p[2]);
        let t = fb.binop(BinOp::Sub, Ty::I64, t, p[3]);
        fb.ret(vec![t]);
        fb.build()
    };
    let g00 = make(&mut mb, "g00", 1);
    let g01 = make(&mut mb, "g01", 2);
    let g10 = make(&mut mb, "g10", 3);
    let g11 = make(&mut mb, "g11", 4);

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);

    let outer0 = fb.create_block(); // inner switch on b&1
    let outer1 = fb.create_block(); // inner switch on c&1
    let bb00 = fb.create_block();
    let bb01 = fb.create_block();
    let bb10 = fb.create_block();
    let bb11 = fb.create_block();
    let merge = fb.create_block();
    let m_r = fb.add_block_param(merge, Ty::I64);

    fb.switch_to_block(e);
    let one = fb.iconst(Ty::I64, 1);
    let osel = fb.binop(BinOp::And, Ty::I64, a, one);
    fb.switch(
        osel,
        vec![
            SwitchCase {
                value: trust_ir::Constant::Int(0),
                target: outer0,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(1),
                target: outer1,
                args: vec![],
            },
        ],
        outer0,
        vec![],
    );

    fb.switch_to_block(outer0);
    let one0 = fb.iconst(Ty::I64, 1);
    let isel0 = fb.binop(BinOp::And, Ty::I64, b, one0);
    fb.switch(
        isel0,
        vec![
            SwitchCase {
                value: trust_ir::Constant::Int(0),
                target: bb00,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(1),
                target: bb01,
                args: vec![],
            },
        ],
        bb00,
        vec![],
    );

    fb.switch_to_block(outer1);
    let one1 = fb.iconst(Ty::I64, 1);
    let isel1 = fb.binop(BinOp::And, Ty::I64, c, one1);
    fb.switch(
        isel1,
        vec![
            SwitchCase {
                value: trust_ir::Constant::Int(0),
                target: bb10,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(1),
                target: bb11,
                args: vec![],
            },
        ],
        bb10,
        vec![],
    );

    for (bb, callee) in [(bb00, g00), (bb01, g01), (bb10, g10), (bb11, g11)] {
        fb.switch_to_block(bb);
        let r = fb.call(callee, vec![a, b, c, d]);
        fb.br(merge, vec![r]);
    }

    fb.switch_to_block(merge);
    fb.ret(vec![m_r]);
    fb.build();
    mb.build()
}

fn nested_g(tag: i64, a: i64, b: i64, c: i64, d: i64) -> i64 {
    let tg = tag.wrapping_mul(0x5bd1_e995);
    let t = a.wrapping_add(tg).wrapping_mul(b) ^ c;
    t.wrapping_sub(d)
}

fn ref_nested_switch_calls(r: &[i64; 4]) -> i64 {
    let (a, b, c, d) = (r[0], r[1], r[2], r[3]);
    let tag = if a & 1 == 0 {
        if b & 1 == 0 { 1 } else { 2 }
    } else if c & 1 == 0 {
        3
    } else {
        4
    };
    nested_g(tag, a, b, c, d)
}

#[test]
fn nested_switch_calls() {
    let m = build_nested_switch_calls();
    let mut all_rows = rows();
    // Cover the 4 (a&1,b&1,c&1) combinations explicitly.
    all_rows.push([0, 0, 0, 9]);
    all_rows.push([0, 1, 0, 9]);
    all_rows.push([1, 0, 0, 9]);
    all_rows.push([1, 0, 1, 9]);
    for row in all_rows {
        let want = ref_nested_switch_calls(&row);
        diff_one_module_row("nested_switch_calls", &m, &row, want);
    }
}

// ---------------------------------------------------------------------------
// Shape 10: condbr tree whose INTERIOR predicates are CALL RESULTS.
//   Each decision node calls a predicate function returning 0/1, branches on it,
//   and the leaves call value functions. This keeps a predicate-call result live
//   only briefly but forces calls on the "spine" of an irregular CFG, with
//   call-clobbered registers between consecutive decisions.
//   p0 = pred0(a,b,c,d); if p0 -> L else R
//   L: p1 = pred1(...); leaf l0/l1 ; R: p2 = pred2(...); leaf l2/l3
// ---------------------------------------------------------------------------

fn build_condbr_call_predicates() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    // predicate funcs return 0/1 based on a parity/threshold of a mix.
    let make_pred = |mb: &mut ModuleBuilder, name: &str, salt: i128| {
        let mut fb = mb.function(name, cty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        let sc = fb.iconst(Ty::I64, salt);
        let t = fb.binop(BinOp::Add, Ty::I64, p[0], p[1]);
        let t = fb.binop(BinOp::Add, Ty::I64, t, p[2]);
        let t = fb.binop(BinOp::Add, Ty::I64, t, p[3]);
        let t = fb.binop(BinOp::Add, Ty::I64, t, sc);
        let one = fb.iconst(Ty::I64, 1);
        let lsb = fb.binop(BinOp::And, Ty::I64, t, one);
        let zero = fb.iconst(Ty::I64, 0);
        let isodd = fb.icmp(ICmpOp::Ne, Ty::I64, lsb, zero);
        let o = fb.iconst(Ty::I64, 1);
        let z = fb.iconst(Ty::I64, 0);
        let res = fb.select(Ty::I64, isodd, o, z);
        fb.ret(vec![res]);
        fb.build()
    };
    let pred0 = make_pred(&mut mb, "pred0", 0);
    let pred1 = make_pred(&mut mb, "pred1", 1);
    let pred2 = make_pred(&mut mb, "pred2", 2);

    let make_leaf = |mb: &mut ModuleBuilder, name: &str, j: i128| {
        let mut fb = mb.function(name, cty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        let kc = fb.iconst(Ty::I64, (j + 1) * 0x0001_2345);
        let t = fb.binop(BinOp::Mul, Ty::I64, p[0], kc);
        let t = fb.binop(BinOp::Sub, Ty::I64, t, p[1]);
        let t = fb.binop(BinOp::Add, Ty::I64, t, p[2]);
        let t = fb.binop(BinOp::Xor, Ty::I64, t, p[3]);
        fb.ret(vec![t]);
        fb.build()
    };
    let l0 = make_leaf(&mut mb, "cl0", 0);
    let l1 = make_leaf(&mut mb, "cl1", 1);
    let l2 = make_leaf(&mut mb, "cl2", 2);
    let l3 = make_leaf(&mut mb, "cl3", 3);

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);

    let left = fb.create_block();
    let right = fb.create_block();
    let bl0 = fb.create_block();
    let bl1 = fb.create_block();
    let bl2 = fb.create_block();
    let bl3 = fb.create_block();
    let merge = fb.create_block();
    let m_r = fb.add_block_param(merge, Ty::I64);

    fb.switch_to_block(e);
    let p0 = fb.call(pred0, vec![a, b, c, d]);
    let zero0 = fb.iconst(Ty::I64, 0);
    let c0 = fb.icmp(ICmpOp::Ne, Ty::I64, p0, zero0);
    fb.condbr(c0, left, vec![], right, vec![]);

    fb.switch_to_block(left);
    let p1 = fb.call(pred1, vec![a, b, c, d]);
    let zero1 = fb.iconst(Ty::I64, 0);
    let c1 = fb.icmp(ICmpOp::Ne, Ty::I64, p1, zero1);
    fb.condbr(c1, bl0, vec![], bl1, vec![]);

    fb.switch_to_block(right);
    let p2 = fb.call(pred2, vec![a, b, c, d]);
    let zero2 = fb.iconst(Ty::I64, 0);
    let c2 = fb.icmp(ICmpOp::Ne, Ty::I64, p2, zero2);
    fb.condbr(c2, bl2, vec![], bl3, vec![]);

    for (bb, callee) in [(bl0, l0), (bl1, l1), (bl2, l2), (bl3, l3)] {
        fb.switch_to_block(bb);
        let r = fb.call(callee, vec![a, b, c, d]);
        fb.br(merge, vec![r]);
    }

    fb.switch_to_block(merge);
    fb.ret(vec![m_r]);
    fb.build();
    mb.build()
}

fn ref_pred(salt: i64, a: i64, b: i64, c: i64, d: i64) -> i64 {
    let t = a
        .wrapping_add(b)
        .wrapping_add(c)
        .wrapping_add(d)
        .wrapping_add(salt);
    if t & 1 != 0 { 1 } else { 0 }
}
fn ref_cleaf(j: i64, a: i64, b: i64, c: i64, d: i64) -> i64 {
    let kc = (j + 1).wrapping_mul(0x0001_2345);
    let t = a.wrapping_mul(kc).wrapping_sub(b).wrapping_add(c);
    t ^ d
}
fn ref_condbr_call_predicates(r: &[i64; 4]) -> i64 {
    let (a, b, c, d) = (r[0], r[1], r[2], r[3]);
    let p0 = ref_pred(0, a, b, c, d);
    let j = if p0 != 0 {
        if ref_pred(1, a, b, c, d) != 0 { 0 } else { 1 }
    } else if ref_pred(2, a, b, c, d) != 0 {
        2
    } else {
        3
    };
    ref_cleaf(j, a, b, c, d)
}

#[test]
fn condbr_call_predicates() {
    let m = build_condbr_call_predicates();
    diff_module("condbr_call_predicates", &m, ref_condbr_call_predicates);
}

// ---------------------------------------------------------------------------
// Shape 11: SELECT chains choosing CALL ARGUMENTS feeding a single call.
//   Two selects pick which of (a,b) and (c,d) to pass into a callee, with the
//   selectors derived from comparisons. Exercises select results being consumed
//   as call arguments (live into the call's arg-setup), not as call results.
//   x = (a<b) ? a : b ; y = (c<d) ? d : c
//   r = combine(x, y, a^b, c^d)
//   then r2 = (r<0) ? combine2(...) : r  (select of a call result vs scalar)
// ---------------------------------------------------------------------------

fn build_select_call_args() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    let combine = {
        let mut fb = mb.function("combine", cty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        let seven = fb.iconst(Ty::I64, 7);
        let t = fb.binop(BinOp::Mul, Ty::I64, p[0], seven);
        let t = fb.binop(BinOp::Add, Ty::I64, t, p[1]);
        let t = fb.binop(BinOp::Xor, Ty::I64, t, p[2]);
        let t = fb.binop(BinOp::Sub, Ty::I64, t, p[3]);
        fb.ret(vec![t]);
        fb.build()
    };
    let combine2 = {
        let mut fb = mb.function("combine2", cty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..4).map(|_| fb.add_block_param(blk, Ty::I64)).collect();
        fb.switch_to_block(blk);
        let three = fb.iconst(Ty::I64, 3);
        let t = fb.binop(BinOp::Mul, Ty::I64, p[1], three);
        let t = fb.binop(BinOp::Sub, Ty::I64, t, p[0]);
        let t = fb.binop(BinOp::Add, Ty::I64, t, p[2]);
        let t = fb.binop(BinOp::Xor, Ty::I64, t, p[3]);
        fb.ret(vec![t]);
        fb.build()
    };

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    let altb = fb.icmp(ICmpOp::Slt, Ty::I64, a, b);
    let x = fb.select(Ty::I64, altb, a, b); // min(a,b) signed
    let cltd = fb.icmp(ICmpOp::Slt, Ty::I64, c, d);
    let y = fb.select(Ty::I64, cltd, d, c); // max(c,d) signed
    let xab = fb.binop(BinOp::Xor, Ty::I64, a, b);
    let xcd = fb.binop(BinOp::Xor, Ty::I64, c, d);
    let r = fb.call(combine, vec![x, y, xab, xcd]);

    let zero = fb.iconst(Ty::I64, 0);
    let rneg = fb.icmp(ICmpOp::Slt, Ty::I64, r, zero);
    let r2call = fb.call(combine2, vec![x, y, xab, xcd]);
    let out = fb.select(Ty::I64, rneg, r2call, r);
    fb.ret(vec![out]);
    fb.build();
    mb.build()
}

fn ref_select_call_args(r: &[i64; 4]) -> i64 {
    let (a, b, c, d) = (r[0], r[1], r[2], r[3]);
    let x = if a < b { a } else { b };
    let y = if c < d { d } else { c };
    let xab = a ^ b;
    let xcd = c ^ d;
    // combine(p0,p1,p2,p3) = ((p0*7 + p1) ^ p2) - p3
    let rcomb = (x.wrapping_mul(7).wrapping_add(y) ^ xab).wrapping_sub(xcd);
    // combine2(p0,p1,p2,p3) = ((p1*3 - p0) + p2) ^ p3
    let rcomb2 = y.wrapping_mul(3).wrapping_sub(x).wrapping_add(xab) ^ xcd;
    if rcomb < 0 { rcomb2 } else { rcomb }
}

#[test]
fn select_call_args() {
    let m = build_select_call_args();
    diff_module("select_call_args", &m, ref_select_call_args);
}

// ---------------------------------------------------------------------------
// Shape 12: switch-in-loop where the CALL RESULT feeds BOTH the loop-carried
// accumulator AND the next iteration's switch index (data-dependent dispatch).
// This maximizes register pressure: `a`, `acc`, `i`, and the data-dependent
// `state` are all live across the call and the back-edge.
//   state=a&3, acc=0, i=0
//   loop: if i>=N exit
//     switch(state & 3){ k => contrib=step_k(a, acc, i, state) }
//     acc += contrib; state = contrib ^ (state+1); i++; goto loop
//   ret acc
// ---------------------------------------------------------------------------

const DD_LOOP_N: i64 = 7;

fn dd_step(k: i64, a: i64, acc: i64, i: i64, state: i64) -> i64 {
    let kk = (k.wrapping_add(1)).wrapping_mul(0x2545_F491);
    let t = a.wrapping_mul(kk).wrapping_add(acc);
    let t = t ^ i.wrapping_mul(state | 1);
    t.wrapping_sub(k.wrapping_mul(state))
}

fn build_data_dependent_switch_loop() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let cty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    let mut steps = Vec::new();
    for k in 0..4i128 {
        let f = {
            let name = format!("step_{k}");
            let mut fb = mb.function(name, cty);
            let blk = fb.create_block();
            // params: a, acc, i, state
            let pa = fb.add_block_param(blk, Ty::I64);
            let pacc = fb.add_block_param(blk, Ty::I64);
            let pi = fb.add_block_param(blk, Ty::I64);
            let pstate = fb.add_block_param(blk, Ty::I64);
            fb.switch_to_block(blk);
            let kk = fb.iconst(Ty::I64, (k + 1) * 0x2545_F491);
            let t = fb.binop(BinOp::Mul, Ty::I64, pa, kk);
            let t = fb.binop(BinOp::Add, Ty::I64, t, pacc);
            let one = fb.iconst(Ty::I64, 1);
            let st1 = fb.binop(BinOp::Or, Ty::I64, pstate, one);
            let ist = fb.binop(BinOp::Mul, Ty::I64, pi, st1);
            let t = fb.binop(BinOp::Xor, Ty::I64, t, ist);
            let kc = fb.iconst(Ty::I64, k);
            let ks = fb.binop(BinOp::Mul, Ty::I64, kc, pstate);
            let t = fb.binop(BinOp::Sub, Ty::I64, t, ks);
            fb.ret(vec![t]);
            fb.build()
        };
        steps.push(f);
    }

    let ety = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ety);
    let entry = fb.create_block();
    let header = fb.create_block();
    let body = fb.create_block();
    let case0 = fb.create_block();
    let case1 = fb.create_block();
    let case2 = fb.create_block();
    let case3 = fb.create_block();
    let latch = fb.create_block();
    let exit = fb.create_block();

    let a = fb.add_block_param(entry, Ty::I64);
    for _ in 0..3 {
        fb.add_block_param(entry, Ty::I64);
    }
    // header params: i, acc, state
    let h_i = fb.add_block_param(header, Ty::I64);
    let h_acc = fb.add_block_param(header, Ty::I64);
    let h_state = fb.add_block_param(header, Ty::I64);
    // latch params: i, acc, state, contrib
    let l_i = fb.add_block_param(latch, Ty::I64);
    let l_acc = fb.add_block_param(latch, Ty::I64);
    let l_state = fb.add_block_param(latch, Ty::I64);
    let l_contrib = fb.add_block_param(latch, Ty::I64);
    let e_acc = fb.add_block_param(exit, Ty::I64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    let three0 = fb.iconst(Ty::I64, 3);
    let init_state = fb.binop(BinOp::And, Ty::I64, a, three0);
    fb.br(header, vec![zero, zero, init_state]);

    fb.switch_to_block(header);
    let n = fb.iconst(Ty::I64, DD_LOOP_N as i128);
    let done = fb.icmp(ICmpOp::Sge, Ty::I64, h_i, n);
    fb.condbr(done, exit, vec![h_acc], body, vec![]);

    fb.switch_to_block(body);
    let three = fb.iconst(Ty::I64, 3);
    let idx = fb.binop(BinOp::And, Ty::I64, h_state, three);
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

    for (case_bb, step) in [
        (case0, steps[0]),
        (case1, steps[1]),
        (case2, steps[2]),
        (case3, steps[3]),
    ] {
        fb.switch_to_block(case_bb);
        let contrib = fb.call(step, vec![a, h_acc, h_i, h_state]);
        fb.br(latch, vec![h_i, h_acc, h_state, contrib]);
    }

    fb.switch_to_block(latch);
    let new_acc = fb.binop(BinOp::Add, Ty::I64, l_acc, l_contrib);
    let one = fb.iconst(Ty::I64, 1);
    let state_p1 = fb.binop(BinOp::Add, Ty::I64, l_state, one);
    let new_state = fb.binop(BinOp::Xor, Ty::I64, l_contrib, state_p1);
    let new_i = fb.binop(BinOp::Add, Ty::I64, l_i, one);
    fb.br(header, vec![new_i, new_acc, new_state]);

    fb.switch_to_block(exit);
    fb.ret(vec![e_acc]);
    fb.build();
    mb.build()
}

fn ref_data_dependent_switch_loop(r: &[i64; 4]) -> i64 {
    let a = r[0];
    let mut acc: i64 = 0;
    let mut i: i64 = 0;
    let mut state: i64 = a & 3;
    while i < DD_LOOP_N {
        let k = state & 3;
        let contrib = dd_step(k, a, acc, i, state);
        acc = acc.wrapping_add(contrib);
        state = contrib ^ state.wrapping_add(1);
        i = i.wrapping_add(1);
    }
    acc
}

#[test]
fn data_dependent_switch_loop() {
    let m = build_data_dependent_switch_loop();
    diff_module(
        "data_dependent_switch_loop",
        &m,
        ref_data_dependent_switch_loop,
    );
}
