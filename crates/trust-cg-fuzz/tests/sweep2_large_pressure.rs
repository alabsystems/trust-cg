// trust-cg-fuzz/tests/sweep2_large_pressure.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sweep2 surface: large straight-line programs (100+ ops) with high register
// pressure. The point is to stress the register allocator / spiller: many
// simultaneously-live values whose final combination depends on every one of
// them, so a single mis-allocated / mis-spilled value changes the result.
//
// Oracle. These programs use only wrapping integer arithmetic and bitwise ops
// (no casts, no memory, no div-by-zero), all of which the trust_cg interpreter
// models faithfully at i64 width, so the interpreter is a valid oracle here.
// We additionally require cross-config JIT agreement (O0..O3 x fast/precise
// regalloc) as a second, allocator-sensitive signal.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::run_oracle_one;
use trust_ir::{BinOp, Ty, ValueId};
use trust_ir_build::ModuleBuilder;

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn jit(module: &trust_ir::Module, opt: OptLevel, fast: bool, row: [i64; 4]) -> Result<i64, String> {
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
        .map_err(|e| format!("compile_err: {e:?}"))?
        .buffer;
    let f = unsafe { buf.get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>("fuzz_fn") }
        .ok_or_else(|| "symbol_not_found".to_string())?
        .into_inner();
    let v = f(row[0], row[1], row[2], row[3]);
    drop(buf);
    Ok(v)
}

/// Compare interpreter oracle (when defined) and all JIT configs.
fn check(label: &str, module: &trust_ir::Module, rows: &[[i64; 4]]) {
    for &row in rows {
        let oracle = run_oracle_one(module, &row).ok();
        let mut jit_vals: Vec<(OptLevel, bool, i64)> = Vec::new();
        for fast in [true, false] {
            for opt in OPTS {
                match jit(module, opt, fast, row) {
                    Ok(v) => jit_vals.push((opt, fast, v)),
                    Err(e) => panic!("{label}: row={row:?} opt={opt:?} fast={fast}: {e}"),
                }
            }
        }
        if let Some(want) = oracle {
            for (opt, fast, got) in &jit_vals {
                assert_eq!(
                    *got, want,
                    "{label}: ORACLE MISMATCH row={row:?} opt={opt:?} fast={fast} got={got} want={want}"
                );
            }
        }
        if let Some((opt0, fast0, v0)) = jit_vals.first().copied() {
            for (opt, fast, got) in &jit_vals[1..] {
                assert_eq!(
                    *got, v0,
                    "{label}: JIT DIVERGENCE row={row:?} \
                     ({opt0:?},fast={fast0})={v0} vs ({opt:?},fast={fast})={got}"
                );
            }
        }
    }
}

const ROWS: &[[i64; 4]] = &[
    [0, 0, 0, 0],
    [1, 1, 1, 1],
    [-1, -1, -1, -1],
    [1, -1, 2, -2],
    [i64::MAX, i64::MIN, 1, -1],
    [i64::MIN, i64::MAX, -1, 1],
    [123456789, -987654321, 0x7fff_ffff, -0x8000_0000],
    [0xdead_beef, 0x1234_5678, 999, -999],
    [i64::MAX, i64::MAX, i64::MAX, i64::MAX],
    [i64::MIN, i64::MIN, i64::MIN, i64::MIN],
];

/// Build a large straight-line program with many simultaneously-live values.
///
/// We keep a "pool" of `pool_size` live values, all seeded from the four args
/// and constants. Each step combines two pool entries with a rotating op and
/// overwrites one slot, but the FINAL result XORs/adds the entire pool together,
/// so every slot stays live until the end — maximizing register pressure and
/// forcing spills. `ops` total combining steps are emitted.
fn build_pressure(name: &str, pool_size: usize, ops: usize) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(name);
    let ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    // Seed the pool deterministically from args + distinct constants.
    let mut pool: Vec<ValueId> = Vec::with_capacity(pool_size);
    let seeds = [a, b, c, d];
    for i in 0..pool_size {
        if i < 4 {
            pool.push(seeds[i]);
        } else {
            let k = fb.iconst(Ty::I64, (i as i128) * 0x9e3779b9 + 1);
            // Mix a constant with an arg so it is not foldable to a pure const.
            pool.push(fb.binop(BinOp::Add, Ty::I64, k, seeds[i % 4]));
        }
    }

    let cycle = [
        BinOp::Add,
        BinOp::Xor,
        BinOp::Mul,
        BinOp::Sub,
        BinOp::Or,
        BinOp::And,
    ];

    // `live` keeps a running list of values that must all feed the final result,
    // so nothing can be dead-code-eliminated and pressure stays high.
    let mut live: Vec<ValueId> = pool.clone();
    let mut state: u64 = 0x1234_5678_9abc_def0;
    for step in 0..ops {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let i = (state >> 33) as usize % pool_size;
        let j = (state >> 17) as usize % pool_size;
        let op = cycle[step % cycle.len()];
        let lhs = pool[i];
        let rhs = pool[j];
        let nv = fb.binop(op, Ty::I64, lhs, rhs);
        // Overwrite slot i, but record the OLD value into `live` so it cannot be
        // eliminated — this keeps the old SSA value alive past the redefine.
        live.push(pool[i]);
        pool[i] = nv;
        live.push(nv);
    }

    // Reduce the whole live set into one value with a rotating combiner.
    let mut acc = live[0];
    for (n, &v) in live.iter().enumerate().skip(1) {
        let op = cycle[n % cycle.len()];
        acc = fb.binop(op, Ty::I64, acc, v);
    }
    fb.ret(vec![acc]);
    fb.build();
    mb.build()
}

#[test]
fn pressure_pool8_ops150() {
    let m = build_pressure("p8_150", 8, 150);
    check("pressure_pool8_ops150", &m, ROWS);
}

#[test]
fn pressure_pool16_ops200() {
    let m = build_pressure("p16_200", 16, 200);
    check("pressure_pool16_ops200", &m, ROWS);
}

#[test]
fn pressure_pool24_ops300() {
    let m = build_pressure("p24_300", 24, 300);
    check("pressure_pool24_ops300", &m, ROWS);
}

#[test]
fn pressure_pool40_ops120() {
    // Wide pool (40 simultaneously-live) but fewer combining steps: stresses the
    // allocator's ability to keep many distinct values live across a long tail.
    let m = build_pressure("p40_120", 40, 120);
    check("pressure_pool40_ops120", &m, ROWS);
}

/// A long dependency chain (each op depends on the previous) plus the four args
/// held live to the end — stresses spilling of the args across a deep chain.
#[test]
fn deep_chain_with_held_args() {
    let mut mb = ModuleBuilder::new("deepchain");
    let ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let cycle = [BinOp::Add, BinOp::Xor, BinOp::Mul, BinOp::Sub, BinOp::Or];
    let mut acc = a;
    let mix = [a, b, c, d];
    for i in 0..180 {
        let op = cycle[i % cycle.len()];
        let operand = mix[i % 4];
        acc = fb.binop(op, Ty::I64, acc, operand);
    }
    // Hold all args live to the very end.
    let t1 = fb.binop(BinOp::Add, Ty::I64, a, b);
    let t2 = fb.binop(BinOp::Xor, Ty::I64, c, d);
    let t3 = fb.binop(BinOp::Mul, Ty::I64, t1, t2);
    let r = fb.binop(BinOp::Sub, Ty::I64, acc, t3);
    fb.ret(vec![r]);
    fb.build();
    let m = mb.build();
    check("deep_chain_with_held_args", &m, ROWS);
}
