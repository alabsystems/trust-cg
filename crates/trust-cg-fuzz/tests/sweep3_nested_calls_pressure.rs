// trust-cg-fuzz/tests/sweep3_nested_calls_pressure.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sweep3 surface: "nested_calls_pressure".
//
// FOCUS: deep nested / recursive call chains where 12-28 values are LIVE ACROSS
// MULTIPLE in-module calls, with mixed callee arities (including >8 args that
// force stack-passed arguments + SP-16 alignment), and heavy callee-saved
// register pressure. The single-pass `jit_fast` allocator (used by the
// `jit_fast` / `for_host_jit` production profiles) must agree bit-for-bit with
// the precise allocator and with the trust-ir interpreter oracle.
//
// Why the interpreter is a valid oracle here. Every module built below uses
// ONLY wrapping integer arithmetic and bitwise/compare ops at i64 width plus
// in-module Call/CallIndirect and control flow. There are NO casts (no
// Trunc/ZExt/SExt — which the oracle treats as no-ops), NO Alloca / memory, and
// NO division (so no divide-by-zero). All of these the trust_cg interpreter
// models faithfully, so its result is ground truth. We ADDITIONALLY require
// cross-config JIT agreement (O0..O3 x {fast, precise} regalloc) as a second,
// allocator-sensitive signal: a value dropped across a call shows up as either
// an oracle mismatch or a fast-vs-precise divergence.
//
// Anti-false-positive measures:
//   * arithmetic is wrapping (BinOp::{Add,Sub,Mul,Xor,And,Or,Shl} at i64);
//   * shift amounts are masked to < 64 via constants in [1, 13];
//   * recursion depth is bounded to a small constant (<= 12) well under the
//     oracle's max_call_depth = 32 and fuel = 200_000 budget;
//   * no memory, no division, no casts — see the oracle-validity note above.
//
// Any disagreement (oracle vs any JIT, JIT vs JIT, or a compile-error / panic on
// an oracle-accepted module) is a DEFECT.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::panic;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::run_oracle_one;
use trust_ir::{BinOp, FuncId, ICmpOp, Ty, ValueId};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "fuzz_fn";
const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

// Representative argument rows: zeros, units, sign extremes, and dense bit
// patterns. The recursion-controlling argument is masked inside each builder so
// these never blow the depth/fuel budget regardless of the row value.
const ROWS: &[[i64; 4]] = &[
    [0, 0, 0, 0],
    [1, 2, 3, 4],
    [-1, -2, -3, -4],
    [1, -1, 2, -2],
    [i64::MAX, i64::MIN, 7, -7],
    [i64::MIN, i64::MAX, -1, 1],
    [0x1122_3344, 0x5566_7788, 0x0001_2345, 0x0000_9abc],
    [0x7fff_ffff_ffff_ffff, 1, -0x8000_0000, 0x55],
    [0xdead_beef, 0xfeed_face, 0x1000_0001, 0x7fff_ffff],
    [123456789, -987654321, 0x7fff_ffff, -0x8000_0000],
];

#[derive(Clone, Copy)]
enum Run {
    Value(i64),
    CompileErr,
    SymbolMissing,
}

fn jit_run(module: &trust_ir::Module, opt: OptLevel, jit_fast: bool, row: &[i64; 4]) -> Run {
    let externs: HashMap<String, *const u8> = HashMap::new();
    let mut config = if jit_fast {
        CompilerConfig::jit_fast(Target::host())
    } else {
        let mut c = CompilerConfig::for_host_jit();
        c.enable_jit_fast_regalloc = false;
        c
    };
    config.opt_level = opt;
    let compiler = Compiler::new(config);
    let buf = match compiler.compile_module_to_jit(module, &externs) {
        Ok(r) => r.buffer,
        Err(_) => return Run::CompileErr,
    };
    type Fn4 = extern "C" fn(i64, i64, i64, i64) -> i64;
    let fptr = match unsafe { buf.get_fn_bound::<Fn4>(ENTRY) } {
        Some(p) => p.into_inner(),
        None => return Run::SymbolMissing,
    };
    let v = fptr(row[0], row[1], row[2], row[3]);
    drop(buf);
    Run::Value(v)
}

/// Differential driver: compare the interpreter oracle (when defined) against
/// all eight JIT configurations and every pair of JITs against each other.
/// Records each disagreement / compile failure / panic into `defects`.
fn check(label: &str, module: &trust_ir::Module, rows: &[[i64; 4]], defects: &mut Vec<String>) {
    for row in rows {
        let oracle = run_oracle_one(module, row).ok();
        let mut vals: Vec<(OptLevel, bool, i64)> = Vec::new();
        for jit_fast in [true, false] {
            for opt in OPTS {
                let got = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                    jit_run(module, opt, jit_fast, row)
                }));
                match got {
                    Ok(Run::Value(v)) => vals.push((opt, jit_fast, v)),
                    Ok(Run::CompileErr) => {
                        // Compile error only counts as a defect when the oracle
                        // accepted the module (defined value). Otherwise the
                        // module is genuinely unsupported and is skipped.
                        if oracle.is_some() {
                            defects.push(format!(
                                "{label}: COMPILE_ERR row={row:?} opt={opt:?} fast={jit_fast} (oracle={oracle:?})"
                            ));
                        }
                    }
                    Ok(Run::SymbolMissing) => defects.push(format!(
                        "{label}: SYMBOL_MISSING row={row:?} opt={opt:?} fast={jit_fast}"
                    )),
                    Err(_) => defects.push(format!(
                        "{label}: JIT_PANIC row={row:?} opt={opt:?} fast={jit_fast} (oracle={oracle:?})"
                    )),
                }
            }
        }
        // Oracle vs every JIT (only when the oracle produced a defined value).
        if let Some(want) = oracle {
            for (opt, fast, got) in &vals {
                if *got != want {
                    defects.push(format!(
                        "{label}: ORACLE_MISMATCH row={row:?} opt={opt:?} fast={fast}: interp={want} jit={got}"
                    ));
                }
            }
        }
        // Every JIT against every other JIT (catches divergence even when the
        // oracle rejected the module — though here the oracle always accepts).
        for i in 0..vals.len() {
            for j in (i + 1)..vals.len() {
                let (o0, f0, v0) = vals[i];
                let (o1, f1, v1) = vals[j];
                if v0 != v1 {
                    defects.push(format!(
                        "{label}: JIT_DIVERGENCE row={row:?} ({o0:?},fast={f0})={v0} vs ({o1:?},fast={f1})={v1}"
                    ));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Topology 1: linear nested call chain f0 -> f1 -> ... -> f(depth-1).
//
// The entry computes `pressure` independent carry values from the four args and
// then makes a call. Each chain function takes `arity` integer args (mixed,
// including >8 to force stack args), keeps ALL its params live across its own
// nested call to the next link, and folds the returned value back in. Because
// every param is reused AFTER the nested call returns, all of them are live
// across the call and must survive the callee-clobbering of caller-saved regs.
// ---------------------------------------------------------------------------

fn build_chain(name: &str, depth: u32, arity: u32, pressure: u32) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(name);
    let arity = arity.max(1) as usize;
    let depth = depth.max(1);

    // One shared func type for every chain link: `arity` x i64 -> i64.
    let link_ty = mb.add_func_type(vec![Ty::I64; arity], vec![Ty::I64]);

    // Declare chain links FIRST so their FuncIds are 0..depth (stable, and the
    // entry — declared last — can call link 0 by FuncId::new(0)). Each link i
    // (for i < depth-1) calls link i+1; the last link is a pure mixer (leaf).
    for i in 0..depth {
        let is_leaf = i + 1 == depth;
        let mut fb = mb.function(format!("link{i}"), link_ty);
        let blk = fb.create_block();
        let p: Vec<ValueId> = (0..arity)
            .map(|_| fb.add_block_param(blk, Ty::I64))
            .collect();
        fb.switch_to_block(blk);

        // Pre-call mix: derive a hash from all params (keeps them all live).
        let mut acc = p[0];
        for (j, &pj) in p.iter().enumerate() {
            let k = fb.iconst(Ty::I64, 0x9e3779b1_i128 + (j as i128) * 0x1_0001);
            let m = fb.binop(BinOp::Mul, Ty::I64, pj, k);
            acc = fb.binop(BinOp::Add, Ty::I64, acc, m);
            acc = fb.binop(BinOp::Xor, Ty::I64, acc, p[(j + 1) % arity]);
            let s = fb.iconst(Ty::I64, ((j as i128) % 13) + 1);
            let sh = fb.binop(BinOp::Shl, Ty::I64, acc, s);
            acc = fb.binop(BinOp::Sub, Ty::I64, acc, sh);
        }

        if is_leaf {
            fb.ret(vec![acc]);
            fb.build();
            continue;
        }

        // Build args for the nested call from `acc` mixed with each param, so
        // EVERY param feeds a call argument and is then reused below.
        let next_id = FuncId::new(i + 1);
        let mut args = Vec::with_capacity(arity);
        for (j, &pj) in p.iter().enumerate() {
            let t = fb.binop(BinOp::Add, Ty::I64, pj, acc);
            let kk = fb.iconst(Ty::I64, (j as i128) * 0x1357 + 0x2468);
            let t = fb.binop(BinOp::Xor, Ty::I64, t, kk);
            args.push(t);
        }
        let ret = fb.call(next_id, args);

        // Post-call fold: combine the return with EVERY param again (forces all
        // params to be live across the nested call) and with `acc`.
        let mut out = fb.binop(BinOp::Add, Ty::I64, acc, ret);
        for &pj in &p {
            out = fb.binop(BinOp::Xor, Ty::I64, out, pj);
        }
        fb.ret(vec![out]);
        fb.build();
    }

    // Entry: build `pressure` carries from the four args, hold them all live
    // across the call into link0, then fold the carries + return together.
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    let seeds = [a, b, c, d];
    let mut carries: Vec<ValueId> = Vec::new();
    for i in 0..pressure {
        let base = seeds[(i as usize) % 4];
        let k = fb.iconst(Ty::I64, 0x100_0001_i128 * (i as i128 + 1) + 7);
        let m = fb.binop(BinOp::Mul, Ty::I64, base, k);
        let k2 = fb.iconst(Ty::I64, (i as i128) * 0x1357 + 0x9e37);
        let v = fb.binop(BinOp::Xor, Ty::I64, m, k2);
        carries.push(v);
    }

    // First call argument vector: rotate carries (and args) into `arity` slots.
    let mut args = Vec::with_capacity(arity);
    for j in 0..arity {
        let src = if carries.is_empty() {
            seeds[j % 4]
        } else {
            carries[j % carries.len()]
        };
        let mixed = fb.binop(BinOp::Add, Ty::I64, src, seeds[j % 4]);
        args.push(mixed);
    }
    let ret = fb.call(FuncId::new(0), args);

    // Fold: result depends on the return value AND every carry, so every carry
    // is live across the (deeply nested) call.
    let mut out = ret;
    for &v in &carries {
        out = fb.binop(BinOp::Add, Ty::I64, out, v);
        out = fb.binop(BinOp::Xor, Ty::I64, out, v);
    }
    fb.ret(vec![out]);
    fb.build();

    mb.build()
}

// ---------------------------------------------------------------------------
// Topology 2: bounded self-recursion with high cross-call pressure.
//
// `rec(n, s0..s_{k-1})` recurses on `n-1` until n == 0, keeping every state
// value live across the recursive call (each is reused in the post-call fold).
// The arity is `1 + state` so we can push it past 8 to exercise stack args.
// Depth is bounded by masking `n` to a small constant inside the entry.
// ---------------------------------------------------------------------------

fn build_recursive(name: &str, state: u32, depth_mask: i64) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(name);
    let state = state.max(1) as usize;
    let arity = 1 + state; // n + state values

    let rec_ty = mb.add_func_type(vec![Ty::I64; arity], vec![Ty::I64]);

    // rec is FuncId 0.
    {
        let mut fb = mb.function("rec", rec_ty);
        let entry = fb.create_block();
        let n = fb.add_block_param(entry, Ty::I64);
        let s: Vec<ValueId> = (0..state)
            .map(|_| fb.add_block_param(entry, Ty::I64))
            .collect();

        let base = fb.create_block();
        let recurse = fb.create_block();

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        let at_base = fb.icmp(ICmpOp::Sle, Ty::I64, n, zero);
        fb.condbr(at_base, base, vec![], recurse, vec![]);

        // Base case: mix all state values into one result.
        fb.switch_to_block(base);
        let mut bacc = s[0];
        for (j, &sj) in s.iter().enumerate() {
            let k = fb.iconst(Ty::I64, 0xA5A5_i128 + (j as i128) * 7);
            let m = fb.binop(BinOp::Mul, Ty::I64, sj, k);
            bacc = fb.binop(BinOp::Add, Ty::I64, bacc, m);
            bacc = fb.binop(BinOp::Xor, Ty::I64, bacc, sj);
        }
        fb.ret(vec![bacc]);

        // Recursive case: advance each state value, recurse on n-1, then fold
        // the returned value with EVERY original state value (so they are all
        // live across the recursive call).
        fb.switch_to_block(recurse);
        let one = fb.iconst(Ty::I64, 1);
        let n1 = fb.binop(BinOp::Sub, Ty::I64, n, one);
        let mut next_state: Vec<ValueId> = Vec::with_capacity(state);
        for (j, &sj) in s.iter().enumerate() {
            let k = fb.iconst(Ty::I64, 0x1000_0193_i128 + (j as i128) * 0x101);
            let t = fb.binop(BinOp::Mul, Ty::I64, sj, k);
            let t = fb.binop(BinOp::Add, Ty::I64, t, n);
            let sh = fb.iconst(Ty::I64, ((j as i128) % 11) + 1);
            let t = fb.binop(BinOp::Shl, Ty::I64, t, sh);
            next_state.push(t);
        }
        let mut args = Vec::with_capacity(arity);
        args.push(n1);
        args.extend_from_slice(&next_state);
        let ret = fb.call(FuncId::new(0), args);

        // Post-call fold over all ORIGINAL state values.
        let mut out = fb.binop(BinOp::Add, Ty::I64, ret, n);
        for &sj in &s {
            out = fb.binop(BinOp::Xor, Ty::I64, out, sj);
            out = fb.binop(BinOp::Add, Ty::I64, out, sj);
        }
        fb.ret(vec![out]);
        fb.build();
    }

    // Entry: derive a bounded n (masked) and `state` seed values, call rec.
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    // n = (a & depth_mask) -> bounded recursion depth (<= depth_mask).
    let mask = fb.iconst(Ty::I64, depth_mask as i128);
    let n = fb.binop(BinOp::And, Ty::I64, a, mask);

    let seeds = [a, b, c, d];
    let mut args = Vec::with_capacity(arity);
    args.push(n);
    for j in 0..state {
        let base = seeds[j % 4];
        let k = fb.iconst(Ty::I64, 0x9e3779b1_i128 + (j as i128) * 0x1_3001);
        let v = fb.binop(BinOp::Mul, Ty::I64, base, k);
        let v = fb.binop(BinOp::Xor, Ty::I64, v, seeds[(j + 1) % 4]);
        args.push(v);
    }
    let r = fb.call(FuncId::new(0), args);
    fb.ret(vec![r]);
    fb.build();

    mb.build()
}

// ---------------------------------------------------------------------------
// Topology 3: tree recursion (fib-shaped) with multiple values live across TWO
// nested calls. The first recursive return must be held live across the SECOND
// recursive call — the canonical "value live across a call" stressor, now in a
// recursive context with extra carried state.
// ---------------------------------------------------------------------------

fn build_tree(name: &str, state: u32, depth_mask: i64) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(name);
    let state = state.max(1) as usize;
    let arity = 1 + state;

    let ty = mb.add_func_type(vec![Ty::I64; arity], vec![Ty::I64]);

    // tree is FuncId 0.
    {
        let mut fb = mb.function("tree", ty);
        let entry = fb.create_block();
        let n = fb.add_block_param(entry, Ty::I64);
        let s: Vec<ValueId> = (0..state)
            .map(|_| fb.add_block_param(entry, Ty::I64))
            .collect();

        let base = fb.create_block();
        let recurse = fb.create_block();

        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I64, 1);
        let at_base = fb.icmp(ICmpOp::Sle, Ty::I64, n, one);
        fb.condbr(at_base, base, vec![], recurse, vec![]);

        fb.switch_to_block(base);
        let mut bacc = n;
        for &sj in &s {
            bacc = fb.binop(BinOp::Add, Ty::I64, bacc, sj);
        }
        fb.ret(vec![bacc]);

        fb.switch_to_block(recurse);
        let two = fb.iconst(Ty::I64, 2);
        let n1 = fb.binop(BinOp::Sub, Ty::I64, n, one);
        let n2 = fb.binop(BinOp::Sub, Ty::I64, n, two);

        // First nested call. Pass advanced state.
        let mut a1 = Vec::with_capacity(arity);
        a1.push(n1);
        for (j, &sj) in s.iter().enumerate() {
            let k = fb.iconst(Ty::I64, 0x1357_i128 + (j as i128) * 0x11);
            a1.push(fb.binop(BinOp::Add, Ty::I64, sj, k));
        }
        let r1 = fb.call(FuncId::new(0), a1);

        // Second nested call — r1 and all of `s` must stay live across it.
        let mut a2 = Vec::with_capacity(arity);
        a2.push(n2);
        for (j, &sj) in s.iter().enumerate() {
            let k = fb.iconst(Ty::I64, 0x2468_i128 + (j as i128) * 0x13);
            let t = fb.binop(BinOp::Xor, Ty::I64, sj, k);
            // Mix r1 in so the second call's args depend on the first return,
            // and r1 is provably live here.
            a2.push(fb.binop(BinOp::Add, Ty::I64, t, r1));
        }
        let r2 = fb.call(FuncId::new(0), a2);

        // Fold both returns with all carried state.
        let mut out = fb.binop(BinOp::Add, Ty::I64, r1, r2);
        for &sj in &s {
            out = fb.binop(BinOp::Xor, Ty::I64, out, sj);
        }
        fb.ret(vec![out]);
        fb.build();
    }

    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    // n in [0, depth_mask]; tree recursion depth == n, so keep depth_mask small.
    let mask = fb.iconst(Ty::I64, depth_mask as i128);
    let n = fb.binop(BinOp::And, Ty::I64, a, mask);

    let seeds = [a, b, c, d];
    let mut args = Vec::with_capacity(arity);
    args.push(n);
    for j in 0..state {
        let base = seeds[j % 4];
        let k = fb.iconst(Ty::I64, 0xBEEF_i128 + (j as i128) * 0x71);
        args.push(fb.binop(BinOp::Mul, Ty::I64, base, k));
    }
    let r = fb.call(FuncId::new(0), args);
    fb.ret(vec![r]);
    fb.build();

    mb.build()
}

// ---------------------------------------------------------------------------
// Topology 4: mutual recursion between `ping` and `pong`, each carrying a wide
// state vector live across the cross-call, with DIFFERENT arities (one > 8) so
// the two ABIs (register-only vs stack-spilled args) interleave on the stack.
// ---------------------------------------------------------------------------

fn build_mutual(name: &str, ping_state: u32, pong_state: u32, depth_mask: i64) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(name);
    let ps = ping_state.max(1) as usize;
    let qs = pong_state.max(1) as usize;
    let ping_arity = 1 + ps;
    let pong_arity = 1 + qs;

    let ping_ty = mb.add_func_type(vec![Ty::I64; ping_arity], vec![Ty::I64]);
    let pong_ty = mb.add_func_type(vec![Ty::I64; pong_arity], vec![Ty::I64]);

    // ping = FuncId 0, pong = FuncId 1.
    let ping_id = FuncId::new(0);
    let pong_id = FuncId::new(1);

    // ping(n, s...): if n<=0 mix state; else call pong(n-1, advanced state...)
    // then fold with all original state.
    {
        let mut fb = mb.function("ping", ping_ty);
        let entry = fb.create_block();
        let n = fb.add_block_param(entry, Ty::I64);
        let s: Vec<ValueId> = (0..ps)
            .map(|_| fb.add_block_param(entry, Ty::I64))
            .collect();
        let base = fb.create_block();
        let recurse = fb.create_block();
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        let at_base = fb.icmp(ICmpOp::Sle, Ty::I64, n, zero);
        fb.condbr(at_base, base, vec![], recurse, vec![]);

        fb.switch_to_block(base);
        let mut bacc = s[0];
        for &sj in &s {
            bacc = fb.binop(BinOp::Add, Ty::I64, bacc, sj);
            bacc = fb.binop(BinOp::Xor, Ty::I64, bacc, sj);
        }
        fb.ret(vec![bacc]);

        fb.switch_to_block(recurse);
        let one = fb.iconst(Ty::I64, 1);
        let n1 = fb.binop(BinOp::Sub, Ty::I64, n, one);
        // pong takes pong_arity args; derive them from ping's state, cycling.
        let mut args = Vec::with_capacity(pong_arity);
        args.push(n1);
        for j in 0..qs {
            let sj = s[j % ps];
            let k = fb.iconst(Ty::I64, 0x55AA_i128 + (j as i128) * 0x31);
            args.push(fb.binop(BinOp::Add, Ty::I64, sj, k));
        }
        let ret = fb.call(pong_id, args);
        let mut out = fb.binop(BinOp::Add, Ty::I64, ret, n);
        for &sj in &s {
            out = fb.binop(BinOp::Xor, Ty::I64, out, sj);
        }
        fb.ret(vec![out]);
        fb.build();
    }

    // pong(n, q...): if n<=0 mix; else call ping(n-1, advanced...) then fold.
    {
        let mut fb = mb.function("pong", pong_ty);
        let entry = fb.create_block();
        let n = fb.add_block_param(entry, Ty::I64);
        let q: Vec<ValueId> = (0..qs)
            .map(|_| fb.add_block_param(entry, Ty::I64))
            .collect();
        let base = fb.create_block();
        let recurse = fb.create_block();
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        let at_base = fb.icmp(ICmpOp::Sle, Ty::I64, n, zero);
        fb.condbr(at_base, base, vec![], recurse, vec![]);

        fb.switch_to_block(base);
        let mut bacc = q[0];
        for (j, &qj) in q.iter().enumerate() {
            let k = fb.iconst(Ty::I64, 0x33CC_i128 + (j as i128) * 0x17);
            let m = fb.binop(BinOp::Mul, Ty::I64, qj, k);
            bacc = fb.binop(BinOp::Sub, Ty::I64, bacc, m);
        }
        fb.ret(vec![bacc]);

        fb.switch_to_block(recurse);
        let one = fb.iconst(Ty::I64, 1);
        let n1 = fb.binop(BinOp::Sub, Ty::I64, n, one);
        let mut args = Vec::with_capacity(ping_arity);
        args.push(n1);
        for j in 0..ps {
            let qj = q[j % qs];
            let sh = fb.iconst(Ty::I64, ((j as i128) % 9) + 1);
            let t = fb.binop(BinOp::Shl, Ty::I64, qj, sh);
            args.push(fb.binop(BinOp::Xor, Ty::I64, t, qj));
        }
        let ret = fb.call(ping_id, args);
        let mut out = fb.binop(BinOp::Sub, Ty::I64, ret, n);
        for &qj in &q {
            out = fb.binop(BinOp::Add, Ty::I64, out, qj);
        }
        fb.ret(vec![out]);
        fb.build();
    }

    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let mask = fb.iconst(Ty::I64, depth_mask as i128);
    let n = fb.binop(BinOp::And, Ty::I64, b, mask);
    let seeds = [a, b, c, d];
    let mut args = Vec::with_capacity(ping_arity);
    args.push(n);
    for j in 0..ps {
        let base = seeds[j % 4];
        let k = fb.iconst(Ty::I64, 0xCAFE_i128 + (j as i128) * 0x41);
        args.push(fb.binop(BinOp::Mul, Ty::I64, base, k));
    }
    let r = fb.call(ping_id, args);
    fb.ret(vec![r]);
    fb.build();

    mb.build()
}

// ===========================================================================
// Tests
// ===========================================================================

#[test]
fn nested_chain_mixed_arity() {
    let mut defects = Vec::new();
    let mut n = 0usize;
    // depth: how many links deep the call nest goes (bounded, no recursion).
    // arity: callee param count; >8 forces stack args.
    // pressure: 12..28 carries live across the chain entry call.
    for depth in [2u32, 4, 6, 8] {
        for arity in [4u32, 8, 9, 12, 16] {
            for pressure in [12u32, 16, 20, 24, 28] {
                let m = build_chain(
                    &format!("chain_d{depth}_a{arity}_p{pressure}"),
                    depth,
                    arity,
                    pressure,
                );
                check(
                    &format!("chain depth={depth} arity={arity} pressure={pressure}"),
                    &m,
                    ROWS,
                    &mut defects,
                );
                n += 1;
            }
        }
    }
    eprintln!(
        "nested_chain_mixed_arity: {n} modules, {} defects",
        defects.len()
    );
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn self_recursion_cross_call_pressure() {
    let mut defects = Vec::new();
    let mut n = 0usize;
    // state values carried (and live) across each recursive call: 11..27 ->
    // arity 12..28 (always > 8, so stack args every time). depth_mask bounds
    // recursion to <= mask iterations (well under oracle's 32-deep limit).
    for state in [11u32, 15, 19, 23, 27] {
        for depth_mask in [3i64, 7, 0xf] {
            let m = build_recursive(&format!("rec_s{state}_m{depth_mask}"), state, depth_mask);
            check(
                &format!("recursive state={state} depth_mask={depth_mask}"),
                &m,
                ROWS,
                &mut defects,
            );
            n += 1;
        }
    }
    eprintln!(
        "self_recursion_cross_call_pressure: {n} modules, {} defects",
        defects.len()
    );
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn tree_recursion_value_live_across_two_calls() {
    let mut defects = Vec::new();
    let mut n = 0usize;
    // Tree recursion: keep depth small (call count grows ~2^depth). state >= 7
    // pushes arity past 8 for several configs.
    for state in [3u32, 7, 11, 15].iter().copied() {
        for depth_mask in [3i64, 7].iter().copied() {
            let m = build_tree(&format!("tree_s{state}_m{depth_mask}"), state, depth_mask);
            check(
                &format!("tree state={state} depth_mask={depth_mask}"),
                &m,
                ROWS,
                &mut defects,
            );
            n += 1;
        }
    }
    eprintln!(
        "tree_recursion_value_live_across_two_calls: {n} modules, {} defects",
        defects.len()
    );
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn mutual_recursion_mixed_abi_pressure() {
    let mut defects = Vec::new();
    let mut n = 0usize;
    // ping/pong carry different-width state vectors (one side > 8 args), so the
    // register-only and stack-spilled arg ABIs interleave across the stack as
    // recursion unwinds. depth_mask bounds total cross-calls.
    for (ping_state, pong_state) in [(7u32, 11u32), (11, 15), (15, 7), (23, 11)] {
        for depth_mask in [3i64, 7, 0xf] {
            let m = build_mutual(
                &format!("mut_p{ping_state}_q{pong_state}_m{depth_mask}"),
                ping_state,
                pong_state,
                depth_mask,
            );
            check(
                &format!("mutual ping={ping_state} pong={pong_state} depth_mask={depth_mask}"),
                &m,
                ROWS,
                &mut defects,
            );
            n += 1;
        }
    }
    eprintln!(
        "mutual_recursion_mixed_abi_pressure: {n} modules, {} defects",
        defects.len()
    );
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
