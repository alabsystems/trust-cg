// trust-cg-fuzz/tests/diff_cmp_overflow.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential reproduction harness for the "cmp_overflow" surface:
//   * every ICmpOp (Eq Ne Ult Ule Ugt Uge Slt Sle Sgt Sge) at i32 AND i64
//   * boolean materialization to i64 (zext / sext of the icmp Bool result)
//   * ctpop on the comparison-derived word
//   * select driven by a comparison
//   * comparison results stored to memory and reloaded
//   * chained comparisons (cmp of two cmp results)
//   * equality / ordering of extreme values (INT_MIN/MAX/0/-1)
//
// ANTI-FALSE-POSITIVE NOTE (load-bearing — verified against the interpreter
// source `trust-cg-codegen/src/interpreter.rs`):
//   The interpreter keeps ALL integers as i128 and its `eval_icmp` compares the
//   FULL i128 values (signed via `<`, unsigned via `as u128`). It never masks
//   to the operand bit width, and ZExt/SExt/Trunc are no-ops at the i128 level,
//   except `sext Bool`, which makes true `-1` (trust-ir's meaning, LLVM's
//   `sext i1`; the interpreter returned `1` before `1d65e8e64`).
//   Consequences that drive how this test compares against the oracle:
//     - SIGNED compares: oracle is valid iff every operand's stored i128 already
//       equals its canonical signed value at the compare width. We guarantee
//       this by only feeding signed compares (a) i32/i64 constants in range and
//       (b) dynamic operands masked to a small non-negative window (& 0xffff),
//       which are identical in i32, i64 and i128.
//     - UNSIGNED compares: `(x as u128)` only matches the hardware's width-w
//       unsigned interpretation when the stored i128 is non-negative AND fits
//       in w bits. So for unsigned oracle comparison we ONLY use operands whose
//       stored value is in [0, 2^w). HIGH-BIT-SET unsigned operands (e.g. an
//       i64 0x8000…) are not interpreter-comparable. A separate width-aware
//       Rust scalar reference checks those shapes as well as every other shape.
//       All eight JIT configurations also remain cross-compared.
//
// The interpreter is an additional required reference where its model applies;
// an unexpected error is a defect. For the private immediate store/reload shape,
// its reference uses the equivalent bool zext because Alloca is unsupported.
// The tested JIT module retains the actual memory operations. Each module is
// compiled once per configuration and executed on every original input row.
//
// Every module's entry is `fuzz_fn` : (i64,i64,i64,i64) -> i64, and every
// narrow / boolean result is explicitly widened to i64 before `ret`, so the
// compared value is always fully defined.

#![cfg(target_arch = "aarch64")]

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::{bool_sext_i64_oracle_result, run_oracle_one};
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "fuzz_fn";

#[path = "common/jit_matrix.rs"]
mod jit_matrix;

const ALL_CMPS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
];

fn is_unsigned(op: ICmpOp) -> bool {
    matches!(op, ICmpOp::Ult | ICmpOp::Ule | ICmpOp::Ugt | ICmpOp::Uge)
}

// --- how the comparison Bool result is consumed / widened to i64 ---
#[derive(Clone, Copy, Debug)]
enum Materialize {
    /// zext(Bool -> i64): 0 / 1
    ZextI64,
    /// sext(Bool -> i64): 0 / -1
    SextI64,
    /// select(cmp, a, b) over i64, then returned
    SelectI64,
    /// store the zext'd bool to an i64 slot, reload, return
    StoreReloadI64,
    /// ctpop of the zext'd bool widened to i64 (0 or 1) — exercises popcount
    /// on a value derived from a comparison
    CtpopI64,
}

const ALL_MAT: [Materialize; 5] = [
    Materialize::ZextI64,
    Materialize::SextI64,
    Materialize::SelectI64,
    Materialize::StoreReloadI64,
    Materialize::CtpopI64,
];

// --- operand source for one compare ---
#[derive(Clone, Copy, Debug)]
enum Width {
    I32,
    I64,
}

/// A single-compare shape. `width` selects i32 vs i64; `op` the predicate;
/// `mat` how the boolean is widened. Operands come from masked block params
/// (always canonical & non-negative) plus optional extreme constants.
#[derive(Clone, Copy, Debug)]
struct CmpShape {
    width: Width,
    op: ICmpOp,
    mat: Materialize,
    /// If Some, the LHS is this extreme constant (canonical for the width).
    lhs_const: Option<i128>,
    /// If Some, the RHS is this extreme constant (canonical for the width).
    rhs_const: Option<i128>,
    /// Whether this shape only uses operands whose stored i128 is a faithful
    /// width-`w` unsigned value (non-negative & in range). Determines whether
    /// the interpreter may be consulted for unsigned predicates. The scalar
    /// reference always applies, including when this flag is false.
    oracle_ok: bool,
}

fn ty_of(w: Width) -> Ty {
    match w {
        Width::I32 => Ty::I32,
        Width::I64 => Ty::I64,
    }
}

/// Build a module whose entry computes one comparison shape and returns the
/// materialized i64. Dynamic operands derive from the 4 i64 params masked to a
/// small non-negative window so they are identical across i32/i64/i128.
fn build_cmp_module(shape: CmpShape) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("cmp_overflow");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    let cty = ty_of(shape.width);

    // Derive a canonical operand from an i64 param: mask to 0xffff (a small
    // non-negative value that is bit-identical in i32, i64 and i128, hence
    // safe for BOTH signed and unsigned compares against the oracle).
    let mask = fb.iconst(Ty::I64, 0xffff);
    let mk_dyn =
        |fb: &mut trust_ir_build::FunctionBuilder, p: trust_ir::ValueId| -> trust_ir::ValueId {
            let masked = fb.binop(BinOp::And, Ty::I64, p, mask);
            match shape.width {
                Width::I64 => masked,
                // trunc i64 -> i32: value already < 2^16 so the bit pattern is the
                // same; this just gives the compare its i32-typed operand.
                Width::I32 => fb.trunc(Ty::I64, Ty::I32, masked),
            }
        };

    let lhs = match shape.lhs_const {
        Some(k) => fb.iconst(cty.clone(), k),
        None => mk_dyn(&mut fb, a),
    };
    let rhs = match shape.rhs_const {
        Some(k) => fb.iconst(cty.clone(), k),
        None => mk_dyn(&mut fb, b),
    };

    let cmp = fb.icmp(shape.op, cty.clone(), lhs, rhs);

    let out = match shape.mat {
        Materialize::ZextI64 => fb.zext(Ty::Bool, Ty::I64, cmp),
        Materialize::SextI64 => fb.sext(Ty::Bool, Ty::I64, cmp),
        Materialize::SelectI64 => {
            // select(cmp, c, d) over i64 — drive a real value selection.
            fb.select(Ty::I64, cmp, c, d)
        }
        Materialize::StoreReloadI64 => {
            let slot = fb.alloca(Ty::I64);
            let w = fb.zext(Ty::Bool, Ty::I64, cmp);
            fb.store(Ty::I64, slot, w);
            fb.load(Ty::I64, slot)
        }
        Materialize::CtpopI64 => {
            let w = fb.zext(Ty::Bool, Ty::I64, cmp);
            fb.ctpop(Ty::I64, w)
        }
    };
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A "chained comparison" module: r = (a<op1>b) <op2> (c<op3>d), all bool
/// results compared as i64-extended 0/1 words. Exercises comparing the result
/// of comparisons (boolean algebra via icmp), then ctpop of the combined word.
fn build_chain_module(op1: ICmpOp, op2: ICmpOp, op3: ICmpOp, width: Width) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("cmp_chain");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);

    let cty = ty_of(width);
    let mask = fb.iconst(Ty::I64, 0xffff);
    let canon = |fb: &mut trust_ir_build::FunctionBuilder, p: trust_ir::ValueId| {
        let m = fb.binop(BinOp::And, Ty::I64, p, mask);
        match width {
            Width::I64 => m,
            Width::I32 => fb.trunc(Ty::I64, Ty::I32, m),
        }
    };
    let av = canon(&mut fb, a);
    let bv = canon(&mut fb, b);
    let cv = canon(&mut fb, c);
    let dv = canon(&mut fb, d);

    let c1 = fb.icmp(op1, cty.clone(), av, bv);
    let c2 = fb.icmp(op3, cty.clone(), cv, dv);
    // widen the two bools to i64 0/1 then compare those with op2.
    let w1 = fb.zext(Ty::Bool, Ty::I64, c1);
    let w2 = fb.zext(Ty::Bool, Ty::I64, c2);
    let chained = fb.icmp(op2, Ty::I64, w1, w2);
    // combine: out = zext(chained) + ctpop(w1<<1 | w2)
    let combined = fb.zext(Ty::Bool, Ty::I64, chained);
    let one = fb.iconst(Ty::I64, 1);
    let w1s = fb.binop(BinOp::Shl, Ty::I64, w1, one);
    let packed = fb.binop(BinOp::Or, Ty::I64, w1s, w2);
    let pc = fb.ctpop(Ty::I64, packed);
    let out = fb.binop(BinOp::Add, Ty::I64, combined, pc);
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The domain an interpreter result must lie in before it is compared with
/// the scalar reference. Every shape's result is the interpreter's own value;
/// `sext Bool -> i64` must in addition be a one-bit sign extension, `0` or
/// `-1` ([`bool_sext_i64_oracle_result`]), so the widthless `1` the
/// interpreter returned before `1d65e8e64` is a named defect, never a value.
#[derive(Clone, Copy, Debug)]
enum OracleResultDomain {
    Integer,
    BoolSextI64,
}

fn oracle_result_domain(mat: Materialize) -> OracleResultDomain {
    match mat {
        Materialize::SextI64 => OracleResultDomain::BoolSextI64,
        Materialize::ZextI64
        | Materialize::SelectI64
        | Materialize::StoreReloadI64
        | Materialize::CtpopI64 => OracleResultDomain::Integer,
    }
}

fn oracle_result_in_domain(raw: i64, domain: OracleResultDomain) -> Option<i64> {
    match domain {
        OracleResultDomain::Integer => Some(raw),
        OracleResultDomain::BoolSextI64 => bool_sext_i64_oracle_result(raw),
    }
}

fn rows() -> Vec<[i64; 4]> {
    vec![
        [0, 0, 0, 0],
        [1, 1, 1, 1],
        [1, 2, 3, 4],
        [4, 3, 2, 1],
        [0, 1, 0, 1],
        [1, 0, 1, 0],
        [0xffff, 0, 0xffff, 0],
        [0x1234, 0x4321, 0x7fff, 0x8000],
        [-1, -1, -1, -1],
        [i64::MAX, i64::MIN, 0, -1],
        [i64::MIN, i64::MAX, -1, 0],
        [0x7fff_ffff, 0x8000_0000, 0xffff_ffff, 0],
        [0xdead_beef, 0xfeed_face, 0x1000_0001, 0x7fff_ffff],
    ]
}

/// Single-row convenience for the armed harness controls.
fn run_all_jit(
    module: &trust_ir::Module,
    row: &[i64; 4],
    label: &str,
    defects: &mut Vec<String>,
) -> Vec<((bool, OptLevel), i64)> {
    jit_matrix::run_jit_matrix(module, ENTRY, std::slice::from_ref(row), label, defects)
        .into_iter()
        .map(|(config, values)| (config, values[0]))
        .collect()
}

/// Compare every row/configuration with an independent scalar reference. The
/// interpreter is an additional required check when its width model applies.
fn check(
    module: &trust_ir::Module,
    rows: &[[i64; 4]],
    label: &str,
    expected: impl Fn(&[i64; 4]) -> i64,
    interpreter: Option<(&trust_ir::Module, OracleResultDomain)>,
    defects: &mut Vec<String>,
) {
    let jits = jit_matrix::run_jit_matrix(module, ENTRY, rows, label, defects);
    for (index, row) in rows.iter().enumerate() {
        let expected = expected(row);
        if let Some((reference, domain)) = interpreter {
            match run_oracle_one(reference, row) {
                Err(error) => {
                    defects.push(format!("ORACLE_UNAVAILABLE {label} row={row:?}: {error:?}"))
                }
                Ok(raw) => match oracle_result_in_domain(raw, domain) {
                    None => defects.push(format!(
                        "ORACLE_RESULT_OUT_OF_DOMAIN {label} row={row:?}: {raw}"
                    )),
                    Some(value) if value != expected => defects.push(format!(
                        "ORACLE_DISAGREE {label} row={row:?}: scalar={expected} interpreter={value}"
                    )),
                    Some(_) => {}
                },
            }
        }
        for (key, values) in &jits {
            let value = values[index];
            if value != expected {
                defects.push(format!(
                    "MISCOMPILE {label} row={row:?} {key:?}: jit={value} scalar={expected}"
                ));
            }
            if let Some((reference_key, reference_values)) = jits.first()
                && value != reference_values[index]
            {
                defects.push(format!(
                    "JIT_DISAGREE {label} row={row:?}: {reference_key:?}={} vs {key:?}={value}",
                    reference_values[index]
                ));
            }
        }
    }
}

fn scalar_compare(width: Width, op: ICmpOp, lhs: i128, rhs: i128) -> bool {
    let (signed_lhs, signed_rhs, unsigned_lhs, unsigned_rhs) = match width {
        Width::I32 => (
            lhs as i32 as i64,
            rhs as i32 as i64,
            lhs as u32 as u64,
            rhs as u32 as u64,
        ),
        Width::I64 => (lhs as i64, rhs as i64, lhs as u64, rhs as u64),
    };
    match op {
        ICmpOp::Eq => unsigned_lhs == unsigned_rhs,
        ICmpOp::Ne => unsigned_lhs != unsigned_rhs,
        ICmpOp::Ult => unsigned_lhs < unsigned_rhs,
        ICmpOp::Ule => unsigned_lhs <= unsigned_rhs,
        ICmpOp::Ugt => unsigned_lhs > unsigned_rhs,
        ICmpOp::Uge => unsigned_lhs >= unsigned_rhs,
        ICmpOp::Slt => signed_lhs < signed_rhs,
        ICmpOp::Sle => signed_lhs <= signed_rhs,
        ICmpOp::Sgt => signed_lhs > signed_rhs,
        ICmpOp::Sge => signed_lhs >= signed_rhs,
    }
}

fn scalar_cmp(shape: CmpShape, row: &[i64; 4]) -> i64 {
    let lhs = shape.lhs_const.unwrap_or((row[0] & 0xffff) as i128);
    let rhs = shape.rhs_const.unwrap_or((row[1] & 0xffff) as i128);
    let comparison = scalar_compare(shape.width, shape.op, lhs, rhs);
    match shape.mat {
        Materialize::ZextI64 | Materialize::StoreReloadI64 | Materialize::CtpopI64 => {
            i64::from(comparison)
        }
        Materialize::SextI64 => -i64::from(comparison),
        Materialize::SelectI64 => {
            if comparison {
                row[2]
            } else {
                row[3]
            }
        }
    }
}

fn check_shape(shape: CmpShape, rows: &[[i64; 4]], label: &str, defects: &mut Vec<String>) {
    let module = build_cmp_module(shape);
    // The tested JIT module retains its private immediate i64 store/reload.
    // The widthless interpreter cannot allocate memory, so its additional
    // reference uses the equivalent bool zext. The independent scalar model
    // checks every shape, including memory and wide unsigned comparisons.
    let memory_reference = matches!(shape.mat, Materialize::StoreReloadI64).then(|| {
        build_cmp_module(CmpShape {
            mat: Materialize::ZextI64,
            ..shape
        })
    });
    let interpreter = (!is_unsigned(shape.op) || shape.oracle_ok).then_some((
        memory_reference.as_ref().unwrap_or(&module),
        oracle_result_domain(shape.mat),
    ));
    check(
        &module,
        rows,
        label,
        |row| scalar_cmp(shape, row),
        interpreter,
        defects,
    );
}

/// Canonical extreme constants per width. For i32 they fit the i32 range; for
/// i64 the full range. Each value's stored i128 equals its signed canonical
/// value, so SIGNED compares are oracle-comparable. The `unsigned_ok` flag is
/// true only when the value is non-negative and < 2^w (so UNSIGNED compares
/// are oracle-comparable too).
fn extremes(w: Width) -> Vec<(i128, bool /* unsigned_ok */)> {
    match w {
        Width::I32 => vec![
            (0, true),
            (1, true),
            (0x7fff_ffff, true),       // i32::MAX, < 2^32
            (-1, false),               // 0xffff_ffff unsigned -> wide
            (i32::MIN as i128, false), // 0x8000_0000 unsigned -> wide
            (0x1234_5678, true),
        ],
        Width::I64 => vec![
            (0, true),
            (1, true),
            (i64::MAX as i128, true),  // < 2^64
            (-1, false),               // wide unsigned
            (i64::MIN as i128, false), // wide unsigned
            (0x0123_4567_89ab_cdef, true),
        ],
    }
}

#[test]
fn requested_oracle_failure_is_a_defect() {
    let module = build_cmp_module(CmpShape {
        width: Width::I64,
        op: ICmpOp::Slt,
        mat: Materialize::StoreReloadI64,
        lhs_const: None,
        rhs_const: None,
        oracle_ok: true,
    });
    let row = [1, 2, 0, 0];
    assert!(
        run_oracle_one(&module, &row).is_err(),
        "control requires the interpreter's unsupported Alloca path"
    );
    let mut defects = Vec::new();
    check(
        &module,
        &[row],
        "required interpreter",
        |_| 1,
        Some((&module, OracleResultDomain::Integer)),
        &mut defects,
    );
    assert!(
        defects
            .iter()
            .any(|defect| defect.contains("ORACLE_UNAVAILABLE")),
        "missing oracle result was silently discarded: {defects:?}"
    );
}

#[test]
fn scalar_reference_checks_wide_unsigned_and_memory_shapes() {
    let rows = [[0, 0, 11, 22], [-1, 7, i64::MIN, i64::MAX]];
    let mut defects = Vec::new();
    for width in [Width::I32, Width::I64] {
        for mat in ALL_MAT {
            for (op, truth) in [(ICmpOp::Ugt, true), (ICmpOp::Ult, false)] {
                let shape = CmpShape {
                    width,
                    op,
                    mat,
                    lhs_const: Some(-1),
                    rhs_const: Some(0),
                    oracle_ok: false,
                };
                for row in rows {
                    let expected = match mat {
                        Materialize::SextI64 => {
                            if truth {
                                -1
                            } else {
                                0
                            }
                        }
                        Materialize::SelectI64 => {
                            if truth {
                                row[2]
                            } else {
                                row[3]
                            }
                        }
                        _ => i64::from(truth),
                    };
                    assert_eq!(scalar_cmp(shape, &row), expected);
                }
                check_shape(shape, &rows, "wide unsigned control", &mut defects);
            }
        }
    }
    assert!(defects.is_empty(), "{defects:?}");
}

#[test]
fn an_armed_scalar_mismatch_is_reported_for_every_jit_configuration() {
    let module = build_cmp_module(CmpShape {
        width: Width::I64,
        op: ICmpOp::Slt,
        mat: Materialize::ZextI64,
        lhs_const: None,
        rhs_const: None,
        oracle_ok: true,
    });
    let mut defects = Vec::new();
    check(
        &module,
        &[[1, 2, 0, 0]],
        "armed mismatch",
        |_| 0,
        None,
        &mut defects,
    );
    assert_eq!(defects.len(), 8, "{defects:?}");
    assert!(defects.iter().all(|defect| defect.contains("MISCOMPILE")));
}

#[test]
fn jit_matrix_rejects_empty_rows_and_incompatible_entry_abi() {
    let mut module = build_cmp_module(CmpShape {
        width: Width::I64,
        op: ICmpOp::Slt,
        mat: Materialize::ZextI64,
        lhs_const: None,
        rhs_const: None,
        oracle_ok: true,
    });
    let mut defects = Vec::new();
    assert!(jit_matrix::run_jit_matrix(&module, ENTRY, &[], "empty rows", &mut defects).is_empty());
    assert_eq!(defects.len(), 8);
    assert!(defects.iter().all(|defect| defect.contains("NO_ROWS")));
    module.func_types[0].params[0] = Ty::I32;
    defects.clear();
    assert!(
        jit_matrix::run_jit_matrix(&module, ENTRY, &[[0; 4]], "wrong ABI", &mut defects).is_empty()
    );
    assert_eq!(defects.len(), 8);
    assert!(
        defects
            .iter()
            .all(|defect| defect.contains("ENTRY_ABI_MISMATCH"))
    );
}

#[test]
fn harness_selfcheck_oracle_live_and_sensitive() {
    // Prove (a) the oracle ACCEPTS a representative cmp module (so oracle
    // comparison is actually happening, not silently skipped), (b) it returns
    // the semantically-correct value, and (c) the JITs match it. This guards
    // against vacuous passes.
    let m = build_cmp_module(CmpShape {
        width: Width::I64,
        op: ICmpOp::Slt,
        mat: Materialize::ZextI64,
        lhs_const: None,
        rhs_const: None,
        oracle_ok: true,
    });
    // a=1 (masked->1), b=2 (masked->2): 1 < 2 signed -> true -> zext -> 1.
    let row = [1i64, 2, 0, 0];
    let ov = run_oracle_one(&m, &row).expect("oracle must accept cmp module");
    assert_eq!(ov, 1, "1<2 signed zext should be 1, got {ov}");
    let jits = run_all_jit(&m, &row, "selfcheck", &mut Vec::new());
    assert_eq!(jits.len(), 8, "all 8 JIT configs should produce a value");
    for (k, v) in &jits {
        assert_eq!(*v, 1, "JIT {k:?} should agree with oracle (1), got {v}");
    }
    // Sensitivity: a wrong oracle would be caught — flip inputs so result is 0.
    let row0 = [5i64, 2, 0, 0];
    assert_eq!(run_oracle_one(&m, &row0).unwrap(), 0, "5<2 should be 0");

    // Extreme-edge oracle sanity: i64 Slt with i64::MIN const vs dyn.
    let me = build_cmp_module(CmpShape {
        width: Width::I64,
        op: ICmpOp::Slt,
        mat: Materialize::ZextI64,
        lhs_const: Some(i64::MIN as i128),
        rhs_const: None,
        oracle_ok: true,
    });
    // MIN < (anything non-negative) -> true -> 1.
    assert_eq!(run_oracle_one(&me, &[0, 7, 0, 0]).unwrap(), 1);

    // `sext Bool` true is all ones: trust-ir widens `as_signed()` of the
    // 1-bit value (its reference interpreter's `eval_cast`) and LLVM's
    // `sext i1 true` is -1. The interpreter computes that directly since
    // `1d65e8e64`; before, it returned the raw Bool `1` and this harness
    // projected it. Prove the interpreter's true and false results, that the
    // domain check passes them and refuses the retired `1`, and that every JIT
    // configuration agrees. This is an armed guard against a return of the
    // widthless model in the interpreter or a harness that normalizes it.
    let ms = build_cmp_module(CmpShape {
        width: Width::I64,
        op: ICmpOp::Slt,
        mat: Materialize::SextI64,
        lhs_const: None,
        rhs_const: None,
        oracle_ok: true,
    });
    let raw = run_oracle_one(&ms, &row).expect("oracle must accept Bool SExt module");
    assert_eq!(
        raw, -1,
        "the interpreter's Bool SExt of true must be all ones"
    );
    assert_eq!(
        oracle_result_in_domain(raw, OracleResultDomain::BoolSextI64),
        Some(-1),
        "Bool true sign-extends from one bit to i64 -1"
    );
    assert_eq!(
        oracle_result_in_domain(1, OracleResultDomain::BoolSextI64),
        None,
        "the retired widthless `1` is outside the Bool SExt domain"
    );
    let sext_jits = run_all_jit(&ms, &row, "selfcheck-bool-sext", &mut Vec::new());
    assert_eq!(
        sext_jits.len(),
        8,
        "all 8 Bool SExt JIT configs should produce a value"
    );
    for (k, v) in &sext_jits {
        assert_eq!(*v, -1, "Bool SExt JIT {k:?} should produce -1, got {v}");
    }
    let false_row = [2i64, 1, 0, 0];
    let raw_false =
        run_oracle_one(&ms, &false_row).expect("oracle must accept false Bool SExt case");
    assert_eq!(
        raw_false, 0,
        "false Bool SExt oracle result must remain zero"
    );
    assert_eq!(
        oracle_result_in_domain(raw_false, OracleResultDomain::BoolSextI64),
        Some(0),
        "false Bool must sign-extend to native i64 zero"
    );
    let false_jits = run_all_jit(
        &ms,
        &false_row,
        "selfcheck-bool-sext-false",
        &mut Vec::new(),
    );
    assert_eq!(
        false_jits.len(),
        8,
        "all 8 false Bool SExt JIT configs should produce a value"
    );
    for (k, v) in &false_jits {
        assert_eq!(*v, 0, "false Bool SExt JIT {k:?} should produce 0, got {v}");
    }
}

#[test]
fn cmp_single_shapes() {
    let rows = rows();
    let mut defects = Vec::new();
    let mut configs = 0usize;

    for &width in &[Width::I32, Width::I64] {
        for &op in &ALL_CMPS {
            for &mat in &ALL_MAT {
                // (1) fully-dynamic operands (both masked params): always
                //     oracle-comparable (small non-negative window).
                let shape = CmpShape {
                    width,
                    op,
                    mat,
                    lhs_const: None,
                    rhs_const: None,
                    oracle_ok: true,
                };
                let label = format!("dyn {width:?} {op:?} {mat:?}");
                configs += 1;
                check_shape(shape, &rows, &label, &mut defects);

                // (2) extreme-constant LHS vs dynamic RHS and vice-versa, plus
                //     const-vs-const, sweeping the INT_MIN/MAX/0/-1 edges.
                let exs = extremes(width);
                for &(k, uok) in &exs {
                    // const LHS, dynamic RHS
                    let s1 = CmpShape {
                        width,
                        op,
                        mat,
                        lhs_const: Some(k),
                        rhs_const: None,
                        oracle_ok: uok,
                    };
                    // dynamic LHS, const RHS
                    let s2 = CmpShape {
                        width,
                        op,
                        mat,
                        lhs_const: None,
                        rhs_const: Some(k),
                        oracle_ok: uok,
                    };
                    for (tag, s) in [("cL", s1), ("cR", s2)] {
                        let label = format!("{tag} {width:?} {op:?} {mat:?} k={k:#x}");
                        configs += 1;
                        check_shape(s, &rows, &label, &mut defects);
                    }
                }
            }
        }
    }

    // (3) const-vs-const extreme equality / ordering matrix — pure constant
    //     folding of comparisons over INT_MIN/MAX/0/-1.
    for &width in &[Width::I32, Width::I64] {
        let exs = extremes(width);
        for &op in &ALL_CMPS {
            for &(kl, ulok) in &exs {
                for &(kr, urok) in &exs {
                    let s = CmpShape {
                        width,
                        op,
                        mat: Materialize::ZextI64,
                        lhs_const: Some(kl),
                        rhs_const: Some(kr),
                        oracle_ok: ulok && urok,
                    };
                    let label = format!("cc {width:?} {op:?} l={kl:#x} r={kr:#x}");
                    configs += 1;
                    check_shape(s, &rows, &label, &mut defects);
                }
            }
        }
    }

    assert_eq!(
        configs, 2020,
        "reviewed single-comparison shape census changed"
    );
    assert_eq!(rows.len(), 13, "reviewed input-row census changed");
    eprintln!(
        "cmp_single: {configs} shapes x 8 JIT configurations x {} rows, {} defects",
        rows.len(),
        defects.len()
    );
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(50)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn cmp_chains() {
    let rows = rows();
    let mut defects = Vec::new();
    let mut configs = 0usize;
    // Sweep a representative chain set: outer op2 over the i64 0/1 words is
    // always oracle-comparable (operands are 0/1, faithful). Inner ops over
    // masked small operands are also faithful, so the WHOLE chain is
    // oracle-comparable regardless of signedness.
    for &width in &[Width::I32, Width::I64] {
        for &op1 in &ALL_CMPS {
            for &op2 in &[
                ICmpOp::Eq,
                ICmpOp::Ne,
                ICmpOp::Ult,
                ICmpOp::Slt,
                ICmpOp::Sge,
            ] {
                for &op3 in &[ICmpOp::Slt, ICmpOp::Ugt, ICmpOp::Eq] {
                    let m = build_chain_module(op1, op2, op3, width);
                    let label = format!("chain {width:?} {op1:?}/{op2:?}/{op3:?}");
                    configs += 1;
                    check(
                        &m,
                        &rows,
                        &label,
                        |row| {
                            let first = scalar_compare(
                                width,
                                op1,
                                (row[0] & 0xffff) as i128,
                                (row[1] & 0xffff) as i128,
                            );
                            let second = scalar_compare(
                                width,
                                op3,
                                (row[2] & 0xffff) as i128,
                                (row[3] & 0xffff) as i128,
                            );
                            let outer = scalar_compare(
                                Width::I64,
                                op2,
                                i128::from(first),
                                i128::from(second),
                            );
                            i64::from(outer) + i64::from(first) + i64::from(second)
                        },
                        Some((&m, OracleResultDomain::Integer)),
                        &mut defects,
                    );
                }
            }
        }
    }
    assert_eq!(
        configs, 300,
        "reviewed chained-comparison shape census changed"
    );
    assert_eq!(rows.len(), 13, "reviewed input-row census changed");
    eprintln!(
        "cmp_chains: {configs} shapes x 8 JIT configurations x {} rows, {} defects",
        rows.len(),
        defects.len()
    );
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(50)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// Dedicated wide-unsigned probe: i64 / i32 unsigned compares where operands
/// have the high bit set (INT_MIN, -1). These are NOT oracle-comparable (the
/// interpreter's i128 `as u128` diverges from width-w hardware unsigned). The
/// independent width-aware scalar model still checks all eight JIT configurations.
#[test]
fn cmp_wide_unsigned_jit_agreement() {
    let rows = rows();
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for &width in &[Width::I32, Width::I64] {
        for &op in &[ICmpOp::Ult, ICmpOp::Ule, ICmpOp::Ugt, ICmpOp::Uge] {
            for &mat in &ALL_MAT {
                for &(k, _) in extremes(width).iter().filter(|(_, uok)| !*uok) {
                    for (tag, lc, rc) in [("cL", Some(k), None), ("cR", None, Some(k))] {
                        let s = CmpShape {
                            width,
                            op,
                            mat,
                            lhs_const: lc,
                            rhs_const: rc,
                            oracle_ok: false,
                        };
                        let label = format!("wideU {tag} {width:?} {op:?} {mat:?} k={k:#x}");
                        configs += 1;
                        check_shape(s, &rows, &label, &mut defects);
                    }
                }
            }
        }
    }
    assert_eq!(configs, 160, "reviewed wide-unsigned shape census changed");
    assert_eq!(rows.len(), 13, "reviewed input-row census changed");
    eprintln!(
        "cmp_wide_unsigned: {configs} shapes (scalar reference and JIT agreement), {} defects",
        defects.len()
    );
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(50)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
