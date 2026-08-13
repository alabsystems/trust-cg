// trust-cg-fuzz/tests/diff_narrow_int.rs
//
// Differential fuzzing for the "narrow_int" surface:
//   - i8/i16/i32/u8/u16/u32 arithmetic
//   - Trunc/ZExt/SExt round-trips
//   - sub-register stores then reloads through alloca of the narrow type
//   - the upper-bits-zeroed / sign-extended invariant
//   - narrow values widened to i64 only at the end
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::panic;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::run_oracle_one;
use trust_ir::{BinOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "fuzz_fn";

// ---------------------------------------------------------------------------
// JIT run plumbing
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Run {
    Value(i64),
    CompileErr,
    SymbolMissing,
    Panic,
}

fn jit_run(m: &trust_ir::Module, opt: OptLevel, fast: bool, row: &[i64; 4]) -> Run {
    let ext: HashMap<String, *const u8> = HashMap::new();
    let mut cfg = if fast {
        CompilerConfig::jit_fast(Target::host())
    } else {
        let mut c = CompilerConfig::for_host_jit();
        c.enable_jit_fast_regalloc = false;
        c
    };
    cfg.opt_level = opt;

    let compiled = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        Compiler::new(cfg)
            .compile_module_to_jit(m, &ext)
            .map_err(Box::new)
    }));
    let buf = match compiled {
        Ok(Ok(r)) => r.buffer,
        Ok(Err(_)) => return Run::CompileErr,
        Err(_) => return Run::Panic,
    };
    let f = match unsafe { buf.get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>(ENTRY) } {
        Some(p) => p.into_inner(),
        None => return Run::SymbolMissing,
    };
    let called = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        f(row[0], row[1], row[2], row[3])
    }));
    let out = match called {
        Ok(v) => Run::Value(v),
        Err(_) => Run::Panic,
    };
    drop(buf);
    out
}

/// Mask of all value bits for the given narrow integer type.
fn int_mask_for(ty: &Ty) -> u64 {
    match ty.bit_width().unwrap() {
        8 => 0xff,
        16 => 0xffff,
        32 => 0xffff_ffff,
        w => (1u64 << w) - 1,
    }
}

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn all_jit_runs(m: &trust_ir::Module, row: &[i64; 4]) -> Vec<(String, Run)> {
    let mut out = Vec::new();
    for &fast in &[false, true] {
        for &opt in &OPTS {
            let tag = format!("{:?}/{}", opt, if fast { "fast" } else { "std" });
            out.push((tag, jit_run(m, opt, fast, row)));
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Module builders for the narrow_int surface
// ---------------------------------------------------------------------------

/// Shape 1: narrow binop in `nty`, operands derived from params via trunc.
/// The result flows through a narrow binop (which normalizes), so the oracle's
/// no-op-cast simplification still agrees: ORACLE-COMPARABLE.
fn build_arith(nty: Ty, op: BinOp, widen_signed: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    // Truncate both operands to the narrow type.
    let na = fb.trunc(Ty::I64, nty.clone(), a);
    let mut nb = fb.trunc(Ty::I64, nty.clone(), b);

    // For div/rem, force nonzero divisor: nb = (nb | 1).
    if matches!(op, BinOp::UDiv | BinOp::SDiv | BinOp::URem | BinOp::SRem) {
        let one = fb.iconst(nty.clone(), 1);
        nb = fb.binop(BinOp::Or, nty.clone(), nb, one);
    }
    // For shifts, mask amount to width-1.
    let nb = if matches!(op, BinOp::Shl | BinOp::LShr | BinOp::AShr) {
        let w = nty.bit_width().unwrap();
        let mask = fb.iconst(nty.clone(), (w - 1) as i128);
        fb.binop(BinOp::And, nty.clone(), nb, mask)
    } else {
        nb
    };

    let r = fb.binop(op, nty.clone(), na, nb);
    // Widen to i64 only at the end.
    let wide = if widen_signed {
        fb.sext(nty.clone(), Ty::I64, r)
    } else {
        fb.zext(nty.clone(), Ty::I64, r)
    };
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

/// Shape 2: trunc -> store to alloca of narrow type -> reload -> normalizing
/// binop in nty -> widen. Uses memory, so the oracle is UNSUPPORTED; rely on
/// cross-opt/cross-allocator JIT agreement.
fn build_alloca_roundtrip(nty: Ty, widen_signed: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    let slot = fb.alloca(nty.clone());
    let na = fb.trunc(Ty::I64, nty.clone(), a);
    fb.store(nty.clone(), slot, na);
    let loaded = fb.load(nty.clone(), slot);

    let nb = fb.trunc(Ty::I64, nty.clone(), b);
    // sum is a normalizing narrow binop.
    let sum = fb.binop(BinOp::Add, nty.clone(), loaded, nb);

    let wide = if widen_signed {
        fb.sext(nty.clone(), Ty::I64, sum)
    } else {
        fb.zext(nty.clone(), Ty::I64, sum)
    };
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

/// Shape 3: pure trunc/zext/sext round-trip with NO normalizing binop after
/// the final cast. The narrow result is widened and returned directly.
/// The oracle treats casts as no-ops, so it is NOT comparable here; rely on
/// JIT-vs-JIT agreement to check the upper-bits invariant (zext zeroes,
/// sext sign-extends).
fn build_pure_roundtrip(nty: Ty, widen_signed: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let _b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    let na = fb.trunc(Ty::I64, nty.clone(), a);
    let wide = if widen_signed {
        fb.sext(nty.clone(), Ty::I64, na)
    } else {
        fb.zext(nty.clone(), Ty::I64, na)
    };
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

/// Shape 4: multi-step narrow ladder: i64 -> trunc to nty -> narrow ops ->
/// trunc to a *narrower* type -> narrow ops -> widen. Stresses repeated
/// truncation and mixed signedness. Result flows through normalizing binops
/// before each widen, so this is ORACLE-COMPARABLE.
fn build_ladder(wide_ty: Ty, narrow_ty: Ty, mix_signed: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    let wa = fb.trunc(Ty::I64, wide_ty.clone(), a);
    let wb = fb.trunc(Ty::I64, wide_ty.clone(), b);
    let wsum = fb.binop(BinOp::Add, wide_ty.clone(), wa, wb);
    let wmul = fb.binop(BinOp::Mul, wide_ty.clone(), wsum, wa);

    // Truncate wide result down to the narrow type.
    let nv = fb.trunc(wide_ty.clone(), narrow_ty.clone(), wmul);
    let wc = fb.trunc(Ty::I64, narrow_ty.clone(), c);
    let nsum = fb.binop(BinOp::Sub, narrow_ty.clone(), nv, wc);
    // XOR keeps it normalizing.
    let nxor = fb.binop(BinOp::Xor, narrow_ty.clone(), nsum, nv);

    let wide = if mix_signed {
        fb.sext(narrow_ty.clone(), Ty::I64, nxor)
    } else {
        fb.zext(narrow_ty.clone(), Ty::I64, nxor)
    };
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

/// Shape 5: zext-narrow then signed compare via icmp, materializing a bool to
/// an i64. Stresses whether the upper bits leak into a comparison. The narrow
/// value flows through a narrow binop (mul) and then an icmp on the narrow
/// type. ORACLE-COMPARABLE (binop normalizes; icmp on normalized values).
fn build_cmp(nty: Ty, signed_cmp: bool) -> trust_ir::Module {
    use trust_ir::ICmpOp;
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    let na = fb.trunc(Ty::I64, nty.clone(), a);
    let nb = fb.trunc(Ty::I64, nty.clone(), b);
    // Normalizing narrow binop before the compare.
    let prod = fb.binop(BinOp::Mul, nty.clone(), na, nb);
    let op = if signed_cmp { ICmpOp::Slt } else { ICmpOp::Ult };
    let cond = fb.icmp(op, nty.clone(), prod, na);
    // Select between two distinct narrow values, then widen. Use non-negative
    // constants so they are valid for unsigned narrow types; for signed types
    // derive a distinct second constant near the top of the range.
    let lo = fb.iconst(nty.clone(), 7);
    let hi_val: i128 = if nty.is_signed() {
        // A value with the narrow sign bit set, expressed in-range as a
        // signed magnitude (e.g. -3) — valid for signed narrow types.
        -3
    } else {
        // Largest value of the unsigned narrow type minus 2.
        (int_mask_for(&nty) - 2) as i128
    };
    let hi = fb.iconst(nty.clone(), hi_val);
    let sel = fb.select(nty.clone(), cond, hi, lo);
    let wide = fb.sext(nty.clone(), Ty::I64, sel);
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

// ---------------------------------------------------------------------------
// Defect collection
// ---------------------------------------------------------------------------

const INPUT_ROWS: &[[i64; 4]] = &[
    [0, 0, 0, 0],
    [1, 1, 1, 1],
    [-1, -1, -1, -1],
    [i64::MIN, i64::MIN, i64::MIN, i64::MIN],
    [i64::MAX, i64::MAX, i64::MAX, i64::MAX],
    [127, 128, 255, 256],
    [-128, -129, 32767, 32768],
    [0x7fff_ffff, 0x8000_0000, -0x8000_0000, 0xffff_ffff],
    [
        0x1234_5678,
        -0x1234_5678,
        0xdead_beef_i64,
        0x00ff_00ffu32 as i64,
    ],
    [42, -42, 100, -100],
    [0xff, 0xffff, 0xffff_ffff, 0x7f],
    [-1, 1, i64::MIN, i64::MAX],
    [256, 257, 258, 259],
    [0x80, 0x8000, 0x8000_0000, 0x40],
];

struct Sweep {
    configs: usize,
    /// NEW findings: cross-JIT disagreements, compile errors, panics, or oracle
    /// mismatches outside the known confirmed-miscompile family. These fail the
    /// sweep.
    defects: Vec<String>,
    /// EXPECTED findings: oracle mismatches that match the already-confirmed
    /// narrow-signed-div/shift miscompile (all 8 JIT configs agree on the wrong
    /// value). Reported but do not fail the sweep — the dedicated
    /// `confirmed_narrow_signed_div_shift_miscompile` test owns that defect.
    expected_known: Vec<String>,
    oracle_used: bool,
}

/// Run one module over all input rows; compare oracle (when comparable+Ok)
/// and all 8 JIT configs against each other.
///
/// `known_signed_family` is true for the `arith[*, {SDiv,SRem,AShr}, *]` shapes
/// where the confirmed narrow-signed-div/shift miscompile lives; oracle-only
/// mismatches there (with full 8-config JIT agreement) are routed to
/// `expected_known` instead of `defects`.
fn check_module(
    sweep: &mut Sweep,
    label: &str,
    m: &trust_ir::Module,
    oracle_comparable: bool,
    known_signed_family: bool,
) {
    for row in INPUT_ROWS {
        let oracle = if oracle_comparable {
            match run_oracle_one(m, row) {
                Ok(v) => {
                    sweep.oracle_used = true;
                    Some(v)
                }
                Err(_) => None,
            }
        } else {
            None
        };

        let runs = all_jit_runs(m, row);
        sweep.configs += runs.len();

        // 1) All JIT configs that produced a Value must agree with each other.
        let mut values: Vec<(String, i64)> = Vec::new();
        for (tag, run) in &runs {
            match run {
                Run::Value(v) => values.push((tag.clone(), *v)),
                Run::CompileErr => sweep.defects.push(format!(
                    "{label} row={row:?} cfg={tag}: COMPILE_ERROR (oracle accepts={})",
                    oracle.is_some()
                )),
                Run::SymbolMissing => sweep
                    .defects
                    .push(format!("{label} row={row:?} cfg={tag}: SYMBOL_MISSING")),
                Run::Panic => sweep
                    .defects
                    .push(format!("{label} row={row:?} cfg={tag}: PANIC")),
            }
        }
        if let Some((first_tag, first_v)) = values.first().cloned() {
            let mut jit_all_agree = true;
            for (tag, v) in &values {
                if *v != first_v {
                    jit_all_agree = false;
                    sweep.defects.push(format!(
                        "{label} row={row:?}: JIT DISAGREE {first_tag}={first_v} vs {tag}={v}"
                    ));
                }
            }
            // 2) Oracle agreement (only when comparable and defined).
            if let Some(ov) = oracle
                && ov != first_v
            {
                let msg = format!("{label} row={row:?}: ORACLE={ov} vs JIT({first_tag})={first_v}");
                // Route to the expected bucket only when this is the known
                // signed-op family AND all 8 JIT configs agreed (the exact
                // signature of the confirmed miscompile). Anything else is a
                // new finding.
                if known_signed_family && jit_all_agree {
                    sweep.expected_known.push(msg);
                } else {
                    sweep.defects.push(msg);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The sweep test
// ---------------------------------------------------------------------------

/// Build the smallest module exercising a single narrow signed op on two
/// params, both pre-truncated to `nty`, result sext to i64. No |1 masking, no
/// extra ops: this is the minimal miscompile witness shape.
fn build_min_signed_op(nty: Ty, op: BinOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let na = fb.trunc(Ty::I64, nty.clone(), a);
    let nb = fb.trunc(Ty::I64, nty.clone(), b);
    let r = fb.binop(op, nty.clone(), na, nb);
    let wide = fb.sext(nty.clone(), Ty::I64, r);
    fb.ret(vec![wide]);
    fb.build();
    mb.build()
}

/// CONFIRMED MISCOMPILE (narrow signed SDiv / SRem / AShr on i8 & i16).
///
/// trust-cg lowers narrow signed division/remainder/arithmetic-shift to a
/// 32-bit SDIV / ASR (see trust-cg-lower::isel `select_binop`, `select_shift`,
/// `select_remainder`) but does NOT sign-extend the i8/i16 operands from their
/// narrow width up to 32 bits first. A negative narrow value (e.g. i8 -41 held
/// as 0x000000D7 after a Trunc) is therefore read as a large positive 32-bit
/// number, so the signed op silently degrades to its UNSIGNED counterpart:
///   SDiv -> udiv,  SRem -> urem,  AShr -> lshr.
/// i32 is unaffected because the value already fills the whole 32-bit lane.
///
/// All 8 JIT configs (O0..O3 x {std, fast} regalloc) agree on the WRONG value,
/// while the interpreter oracle computes the correct two's-complement result.
/// Every input below is a fully-defined narrow signed value (no div-by-zero,
/// no INT_MIN/-1, shift amounts in range), so this is a genuine miscompile,
/// not a UB edge.
#[test]
fn confirmed_narrow_signed_div_shift_miscompile() {
    // (type, op, [a,b,_,_], mathematically-correct i64 result)
    let cases: &[(Ty, BinOp, [i64; 4], i64)] = &[
        (Ty::I8, BinOp::SDiv, [42, -41, 0, 0], -1), //   42 / -41  (sdiv) = -1; udiv 42/215 = 0
        (Ty::I16, BinOp::SDiv, [42, -41, 0, 0], -1),
        (Ty::I8, BinOp::SDiv, [100, -7, 0, 0], -14),
        (Ty::I8, BinOp::SDiv, [-100, 7, 0, 0], -14),
        (Ty::I8, BinOp::SDiv, [-100, -7, 0, 0], 14),
        (Ty::I8, BinOp::SRem, [42, -41, 0, 0], 1), //    42 % -41  (srem) = 1; urem 42%215 = 42
        (Ty::I16, BinOp::SRem, [42, -41, 0, 0], 1),
        (Ty::I8, BinOp::SRem, [100, -7, 0, 0], 2),
        (Ty::I8, BinOp::AShr, [-1, 1, 0, 0], -1), //     -1 >>a 1   (asr) = -1; lsr 0xFF>>1 = 127
        (Ty::I8, BinOp::AShr, [-2, 1, 0, 0], -1),
        (Ty::I16, BinOp::AShr, [-2, 1, 0, 0], -1),
    ];

    let mut wrong = Vec::new();
    for (nty, op, row, expect) in cases {
        let m = build_min_signed_op(nty.clone(), *op);
        let oracle = run_oracle_one(&m, row);
        let runs = all_jit_runs(&m, row);
        let jit0 = match &runs[0].1 {
            Run::Value(v) => *v,
            other => panic!(
                "{:?} {:?} row={:?}: JIT did not run: {:?}",
                nty, op, row, other
            ),
        };
        let all_agree = runs
            .iter()
            .all(|(_, r)| matches!(r, Run::Value(v) if *v == jit0));
        // Oracle must match the hand-computed expected value (sanity on oracle).
        assert_eq!(
            oracle,
            Ok(*expect),
            "oracle disagreed with hand-computed result for {:?} {:?} row={:?}",
            nty,
            op,
            row
        );
        eprintln!(
            "MISCOMPILE {:?} {:?} row={:?}: correct(oracle)={} jit(all8agree={})={}",
            nty, op, row, expect, all_agree, jit0
        );
        if jit0 != *expect {
            wrong.push((nty.clone(), *op, *row, *expect, jit0, all_agree));
        }
    }

    // Regression: narrow (i8/i16) signed div/rem and arithmetic-shift-right are
    // now lowered with the operands extended to the 32-bit op width using the
    // op's signedness (see `extend_narrow_for_width_op` in trust-cg-lower isel),
    // so every case must match the hand-computed / interpreter-oracle result.
    for (nty, op, row, expect, got, agree) in &wrong {
        eprintln!(
            "  STILL WRONG: {:?} {:?} row={:?} correct={} jit={} (8-config agreement={})",
            nty, op, row, expect, got, agree
        );
    }
    assert!(
        wrong.is_empty(),
        "narrow signed div/rem/asr must match the oracle after the sign-extension fix; {} cases still wrong",
        wrong.len()
    );
}

#[test]
fn diff_narrow_int_sweep() {
    let mut sweep = Sweep {
        configs: 0,
        defects: Vec::new(),
        expected_known: Vec::new(),
        oracle_used: false,
    };

    let narrow_tys = [Ty::I8, Ty::I16, Ty::I32, Ty::U8, Ty::U16, Ty::U32];
    let arith_ops = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::UDiv,
        BinOp::SDiv,
        BinOp::URem,
        BinOp::SRem,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
    ];

    // The oracle interpreter models narrow *binops* exactly (it normalizes the
    // result to the type width) but treats Trunc/ZExt/SExt as NO-OPS on its
    // i128 registers (see trust-cg-codegen interpreter::eval_cast). So an
    // oracle comparison is only valid when the *final* widening cast coincides
    // with the oracle's no-op:
    //   - zext of an UNSIGNED-narrow value: oracle holds it in [0, 2^w), zext
    //     is a no-op, JIT zext agrees.
    //   - sext of a SIGNED-narrow value: oracle holds the signed value, sext to
    //     i64 reproduces it, JIT sext agrees.
    // The mismatched pairs (zext+signed, sext+unsigned) are oracle-modeling
    // artifacts, NOT codegen defects, so we fall back to JIT-vs-JIT agreement
    // (all 8 configs must match) there.
    let oracle_ok = |nty: &Ty, widen_signed: bool| -> bool {
        (widen_signed && nty.is_signed()) || (!widen_signed && nty.is_unsigned())
    };

    // The confirmed miscompile family: narrow signed SDiv/SRem/AShr.
    let is_known_signed_op = |op: &BinOp| matches!(op, BinOp::SDiv | BinOp::SRem | BinOp::AShr);

    // Shape 1: narrow arithmetic, both widen modes.
    for nty in &narrow_tys {
        for op in &arith_ops {
            for &ws in &[false, true] {
                let label = format!("arith[{:?},{:?},sext={}]", nty, op, ws);
                let m = build_arith(nty.clone(), *op, ws);
                check_module(
                    &mut sweep,
                    &label,
                    &m,
                    oracle_ok(nty, ws),
                    is_known_signed_op(op),
                );
            }
        }
    }

    // Shape 2: alloca round-trip (oracle unsupported -> JIT agreement only).
    for nty in &narrow_tys {
        for &ws in &[false, true] {
            let label = format!("alloca[{:?},sext={}]", nty, ws);
            let m = build_alloca_roundtrip(nty.clone(), ws);
            check_module(&mut sweep, &label, &m, false, false);
        }
    }

    // Shape 3: pure cast round-trip (oracle not comparable -> JIT agreement).
    for nty in &narrow_tys {
        for &ws in &[false, true] {
            let label = format!("pure[{:?},sext={}]", nty, ws);
            let m = build_pure_roundtrip(nty.clone(), ws);
            check_module(&mut sweep, &label, &m, false, false);
        }
    }

    // Shape 4: narrowing ladders (oracle-comparable).
    let ladders = [
        (Ty::I32, Ty::I8),
        (Ty::I32, Ty::I16),
        (Ty::U32, Ty::U8),
        (Ty::U32, Ty::U16),
        (Ty::I16, Ty::I8),
        (Ty::U16, Ty::U8),
    ];
    for (wt, nt) in &ladders {
        for &ms in &[false, true] {
            let label = format!("ladder[{:?}->{:?},sext={}]", wt, nt, ms);
            let m = build_ladder(wt.clone(), nt.clone(), ms);
            // Final widen is over the narrow type `nt`; same comparability rule.
            // Ladder uses only Add/Sub/Mul/Xor, none of the signed-div family.
            check_module(&mut sweep, &label, &m, oracle_ok(nt, ms), false);
        }
    }

    // Shape 5: narrow compare/select. The icmp's operands include a bare
    // trunc result (`na`), which the oracle keeps un-truncated (no-op cast),
    // so the oracle can pick the wrong select arm. Rely on JIT-vs-JIT
    // agreement (all 8 configs) instead of the oracle here.
    for nty in &narrow_tys {
        for &sc in &[false, true] {
            let label = format!("cmp[{:?},signed={}]", nty, sc);
            let m = build_cmp(nty.clone(), sc);
            check_module(&mut sweep, &label, &m, false, false);
        }
    }

    eprintln!(
        "narrow_int: {} configs, {} new defects, {} expected-known (oracle_used={})",
        sweep.configs,
        sweep.defects.len(),
        sweep.expected_known.len(),
        sweep.oracle_used
    );
    for d in &sweep.expected_known {
        eprintln!("  KNOWN (narrow signed div/shift miscompile): {d}");
    }
    for d in &sweep.defects {
        eprintln!("  DEFECT: {d}");
    }
    assert!(
        sweep.defects.is_empty(),
        "narrow_int found {} defects",
        sweep.defects.len()
    );
}
