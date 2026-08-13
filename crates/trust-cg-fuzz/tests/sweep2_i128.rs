// trust-cg-fuzz/tests/sweep2_i128.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sweep2 surface: 128-bit integer arithmetic / compare / shift.
//
// Oracle choice. The trust_cg interpreter widens every integer to i128 and
// models Trunc/ZExt/SExt as *no-ops*; it is therefore not a faithful oracle for
// programs that flow through i128 casts (an early version of this test showed the
// interpreter producing order-dependent / mathematically-wrong results for i128
// shifts, while every JIT configuration produced the correct value). So this
// sweep uses two oracles, neither of which is the trust_cg interpreter:
//   * a Rust ground-truth computed directly with native `i128` arithmetic, which
//     is the real semantics the backend must implement; and
//   * cross-config JIT agreement — every opt level (O0..O3) crossed with both
//     the fast-regalloc and precise-regalloc profiles must agree.
// A DEFECT is any JIT value disagreeing with the Rust ground truth, any JIT
// disagreeing with another JIT, or any compile error / panic.
//
// The entry signature is the fixed `(i64,i64,i64,i64) -> i64`. Each shape
// sign-extends the i64 args to i128, computes in i128, then truncates the i128
// result back to i64 for the return value (matching `as i64`).
//
// Anti-false-positive: divisors are forced nonzero via `| 1`; shift amounts are
// masked into `0..128`; all arithmetic is wrapping / defined for every row.
//
// ---------------------------------------------------------------------------
// FINDINGS (live defects this sweep uncovered).
//
// DEFECT A — i128 arithmetic/shift/compare fed by an integer extension fails
//   instruction selection. Any `Add/Sub/Mul/UDiv/SDiv/URem/SRem/Shl/LShr/AShr`
//   or `ICmp` at `Ty::I128` whose operand is the result of `SExt`/`ZExt`
//   i64->i128 aborts the pipeline with:
//       Pipeline(ISel("value Value(N) not defined before use"))
//   Bitwise i128 ops (And/Or/Xor) and pure-i128-constant arithmetic compile
//   fine, so `i128_bitwise_chain` passes while the rest fail. The interpreter
//   ACCEPTS these modules (e.g. returns 30 for 10+20), so per the sweep's defect
//   definition this is a real compile-time miscompile.
//   Minimal `build_module` body (single arg, smallest reproduction):
//       let a   = block param i64
//       let wa  = cast SExt  i64 -> i128, a
//       let k   = iconst i128 5
//       let s   = binop Add  i128, wa, k          // <- ISel aborts here
//       let r   = cast Trunc i128 -> i64, s
//       ret [r]
//   ZExt reproduces it identically; `iconst i128 + iconst i128` does NOT.
//
// DEFECT B — see sweep2_chained_casts.rs: `Trunc i128 -> {i64,i32}` of a value
//   produced by `SExt`/`ZExt` i64->i128 returns 0 instead of the low bits, at
//   essentially every opt level / regalloc. (`i128_high_bits_via_shift` here is
//   blocked by DEFECT A before it can also exhibit B.)
//
// The former DEFECT A reproducers and `i128_bitwise_chain` all remain active
// as regression and positive coverage.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{BinOp, CastOp, ICmpOp, Ty};
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

/// Run one module across all opt x regalloc JIT configs, asserting every result
/// equals `truth(row)` and that all configs agree.
fn check<F>(label: &str, module: &trust_ir::Module, rows: &[[i64; 4]], truth: F)
where
    F: Fn([i64; 4]) -> i64,
{
    for &row in rows {
        let want = truth(row);
        let mut jit_vals: Vec<(OptLevel, bool, i64)> = Vec::new();
        for fast in [true, false] {
            for opt in OPTS {
                match jit(module, opt, fast, row) {
                    Ok(v) => jit_vals.push((opt, fast, v)),
                    Err(e) => panic!("{label}: row={row:?} opt={opt:?} fast={fast}: {e}"),
                }
            }
        }
        for (opt, fast, got) in &jit_vals {
            assert_eq!(
                *got, want,
                "{label}: TRUTH MISMATCH row={row:?} opt={opt:?} fast={fast} got={got} want={want}"
            );
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

/// SExt each of the four i64 args to i128.
fn ext_args(
    fb: &mut trust_ir_build::FunctionBuilder,
    args: &[trust_ir::ValueId; 4],
) -> [trust_ir::ValueId; 4] {
    [
        fb.cast(CastOp::SExt, Ty::I64, Ty::I128, args[0]),
        fb.cast(CastOp::SExt, Ty::I64, Ty::I128, args[1]),
        fb.cast(CastOp::SExt, Ty::I64, Ty::I128, args[2]),
        fb.cast(CastOp::SExt, Ty::I64, Ty::I128, args[3]),
    ]
}

/// Build a module whose body is produced by `body`, which receives the builder
/// and the four SExt'd i128 args and returns the i128 result value-id. The
/// result is truncated to i64 and returned.
fn build_i128<F>(name: &str, body: F) -> trust_ir::Module
where
    F: FnOnce(&mut trust_ir_build::FunctionBuilder, &[trust_ir::ValueId; 4]) -> trust_ir::ValueId,
{
    let mut mb = ModuleBuilder::new(name);
    let ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let w = ext_args(&mut fb, &[a, b, c, d]);
    let r128 = body(&mut fb, &w);
    let r = fb.cast(CastOp::Trunc, Ty::I128, Ty::I64, r128);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

const ROWS: &[[i64; 4]] = &[
    [0, 0, 0, 0],
    [1, 1, 1, 1],
    [-1, -1, -1, -1],
    [1, -1, 2, -2],
    [i64::MAX, i64::MIN, 1, -1],
    [i64::MIN, i64::MAX, -1, 1],
    [i64::MAX, i64::MAX, i64::MAX, i64::MAX],
    [i64::MIN, i64::MIN, i64::MIN, i64::MIN],
    [123456789, -987654321, 0x7fff_ffff, -0x8000_0000],
    [0xdead_beef, 0x1234_5678, 64, 65],
    [3, 5, 127, 128],
    [-7, 11, 63, 96],
    [1_000_000_000_000, -1_000_000_000_000, 13, 200],
    [i64::MAX, 2, 0, 127],
    [i64::MIN, 3, 1, 100],
];

// Ground-truth helpers (native i128 semantics, then `as i64`).
fn w(row: [i64; 4]) -> [i128; 4] {
    [
        row[0] as i128,
        row[1] as i128,
        row[2] as i128,
        row[3] as i128,
    ]
}

#[test]
fn i128_add_sub_mul_chain() {
    let m = build_i128("i128_amm", |fb, x| {
        let t = fb.binop(BinOp::Add, Ty::I128, x[0], x[1]);
        let t = fb.binop(BinOp::Mul, Ty::I128, t, x[2]);
        fb.binop(BinOp::Sub, Ty::I128, t, x[3])
    });
    check("i128_add_sub_mul_chain", &m, ROWS, |row| {
        let x = w(row);
        (x[0]
            .wrapping_add(x[1])
            .wrapping_mul(x[2])
            .wrapping_sub(x[3])) as i64
    });
}

#[test]
fn i128_bitwise_chain() {
    let m = build_i128("i128_bit", |fb, x| {
        let t = fb.binop(BinOp::And, Ty::I128, x[0], x[1]);
        let t = fb.binop(BinOp::Or, Ty::I128, t, x[2]);
        fb.binop(BinOp::Xor, Ty::I128, t, x[3])
    });
    check("i128_bitwise_chain", &m, ROWS, |row| {
        let x = w(row);
        (((x[0] & x[1]) | x[2]) ^ x[3]) as i64
    });
}

#[test]
fn i128_shifts() {
    for op in [BinOp::Shl, BinOp::LShr, BinOp::AShr] {
        let m = build_i128(&format!("i128_sh_{op:?}"), |fb, x| {
            let m127 = fb.iconst(Ty::I128, 127);
            let masked = fb.binop(BinOp::And, Ty::I128, x[2], m127);
            fb.binop(op, Ty::I128, x[0], masked)
        });
        check(&format!("i128_shifts_{op:?}"), &m, ROWS, |row| {
            let x = w(row);
            let amt = (x[2] & 127) as u32;
            let r: i128 = match op {
                BinOp::Shl => (x[0] as u128).wrapping_shl(amt) as i128,
                BinOp::LShr => ((x[0] as u128) >> amt) as i128,
                BinOp::AShr => x[0] >> amt,
                _ => unreachable!(),
            };
            r as i64
        });
    }
}

// Regression for two i128 fixes:
//   (a) i128 Srem/Urem were routed to the i64 select_remainder (dropping the
//       high halves); now routed to __modti3/__umodti3 libcalls.
//   (b) the divisor here is an i128 Bor (x[1] | 1); i128 bitwise And/Or/Xor went
//       through the scalar select_logic, which only computed/defined the LOW
//       half — so the div libcall's use_i128_value of the high half hit "value
//       not defined". select_logic now has an i128 register-pair branch.
#[test]
fn i128_div_rem_nonzero() {
    for op in [BinOp::SDiv, BinOp::UDiv, BinOp::SRem, BinOp::URem] {
        let m = build_i128(&format!("i128_dr_{op:?}"), |fb, x| {
            let one = fb.iconst(Ty::I128, 1);
            let divisor = fb.binop(BinOp::Or, Ty::I128, x[1], one);
            fb.binop(op, Ty::I128, x[0], divisor)
        });
        check(&format!("i128_div_rem_{op:?}"), &m, ROWS, |row| {
            let x = w(row);
            let divisor = x[1] | 1; // always nonzero
            let r: i128 = match op {
                BinOp::SDiv => x[0].wrapping_div(divisor),
                BinOp::SRem => x[0].wrapping_rem(divisor),
                BinOp::UDiv => ((x[0] as u128) / (divisor as u128)) as i128,
                BinOp::URem => ((x[0] as u128) % (divisor as u128)) as i128,
                _ => unreachable!(),
            };
            r as i64
        });
    }
}

#[test]
fn i128_compares() {
    use ICmpOp::*;
    for op in [Eq, Ne, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt, Sge] {
        let m = build_i128(&format!("i128_cmp_{op:?}"), |fb, x| {
            let cond = fb.icmp(op, Ty::I128, x[0], x[1]);
            fb.select(Ty::I128, cond, x[2], x[3])
        });
        check(&format!("i128_compares_{op:?}"), &m, ROWS, |row| {
            let x = w(row);
            let (a, b) = (x[0], x[1]);
            let (ua, ub) = (a as u128, b as u128);
            let cond = match op {
                Eq => a == b,
                Ne => a != b,
                Ult => ua < ub,
                Ule => ua <= ub,
                Ugt => ua > ub,
                Uge => ua >= ub,
                Slt => a < b,
                Sle => a <= b,
                Sgt => a > b,
                Sge => a >= b,
            };
            (if cond { x[2] } else { x[3] }) as i64
        });
    }
}

#[test]
fn i128_mixed_arith_compare_shift() {
    let m = build_i128("i128_mix", |fb, x| {
        let t = fb.binop(BinOp::Mul, Ty::I128, x[0], x[1]);
        let m127 = fb.iconst(Ty::I128, 127);
        let amt = fb.binop(BinOp::And, Ty::I128, x[2], m127);
        let u = fb.binop(BinOp::AShr, Ty::I128, t, amt);
        let v = fb.binop(BinOp::Add, Ty::I128, u, x[3]);
        let cond = fb.icmp(ICmpOp::Slt, Ty::I128, v, x[0]);
        let xored = fb.binop(BinOp::Xor, Ty::I128, v, x[0]);
        fb.select(Ty::I128, cond, v, xored)
    });
    check("i128_mixed_arith_compare_shift", &m, ROWS, |row| {
        let x = w(row);
        let t = x[0].wrapping_mul(x[1]);
        let amt = (x[2] & 127) as u32;
        let u = t >> amt; // arithmetic
        let v = u.wrapping_add(x[3]);
        let r = if v < x[0] { v } else { v ^ x[0] };
        r as i64
    });
}

#[test]
fn i128_high_bits_via_shift() {
    // Force the result to depend on the HIGH 64 bits of an i128 product: a
    // backend that incorrectly narrows to i64 internally would diverge here.
    let m = build_i128("i128_hi", |fb, x| {
        let prod = fb.binop(BinOp::Mul, Ty::I128, x[0], x[1]);
        let sh = fb.iconst(Ty::I128, 64);
        fb.binop(BinOp::LShr, Ty::I128, prod, sh)
    });
    check("i128_high_bits_via_shift", &m, ROWS, |row| {
        let x = w(row);
        let prod = (x[0].wrapping_mul(x[1])) as u128;
        (prod >> 64) as i128 as i64
    });
}
