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
//   to the operand bit width, and ZExt/SExt/Trunc are no-ops at the i128 level.
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
//       i64 0x8000…) are NOT oracle-comparable; those shapes are checked by
//       cross-opt / cross-allocator JIT agreement (all 8 JIT configs must
//       agree) and are explicitly flagged oracle_comparable=false.
//
// Every module's entry is `fuzz_fn` : (i64,i64,i64,i64) -> i64, and every
// narrow / boolean result is explicitly widened to i64 before `ret`, so the
// compared value is always fully defined.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::panic;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::{project_widthless_bool_sext_i64, run_oracle_one};
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "fuzz_fn";

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
    /// the oracle may be consulted for unsigned predicates.
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
    mb.build()
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
    mb.build()
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Run {
    Value(i64),
    CompileErr,
    SymbolMissing,
    Panic,
}

fn jit_run(module: &trust_ir::Module, opt: OptLevel, jit_fast: bool, row: &[i64; 4]) -> Run {
    let res = panic::catch_unwind(panic::AssertUnwindSafe(|| {
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
    }));
    res.unwrap_or(Run::Panic)
}

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Projection from the interpreter's deliberately widthless integer model to
/// the result semantics exercised by the native JIT. Most result shapes are
/// already represented exactly. `sext Bool -> i64` is the one exception: the
/// interpreter leaves the raw Bool `1` unchanged, while a one-bit signed `1`
/// sign-extends to the native i64 value `-1`.
#[derive(Clone, Copy, Debug)]
enum OracleResultProjection {
    Exact,
    BoolSextI64,
}

fn oracle_result_projection(mat: Materialize) -> OracleResultProjection {
    match mat {
        Materialize::SextI64 => OracleResultProjection::BoolSextI64,
        Materialize::ZextI64
        | Materialize::SelectI64
        | Materialize::StoreReloadI64
        | Materialize::CtpopI64 => OracleResultProjection::Exact,
    }
}

fn project_oracle_result(raw: i64, projection: OracleResultProjection) -> Option<i64> {
    match projection {
        OracleResultProjection::Exact => Some(raw),
        OracleResultProjection::BoolSextI64 => project_widthless_bool_sext_i64(raw),
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

/// Run a module across all 8 JIT configs. Returns (jit_values, defects-from-
/// compile/panic). Each entry is keyed by (jit_fast, opt).
fn run_all_jit(
    module: &trust_ir::Module,
    row: &[i64; 4],
    label: &str,
    defects: &mut Vec<String>,
) -> Vec<((bool, OptLevel), i64)> {
    let mut out = Vec::new();
    for jit_fast in [true, false] {
        for opt in OPTS {
            match jit_run(module, opt, jit_fast, row) {
                Run::Value(v) => out.push(((jit_fast, opt), v)),
                Run::CompileErr => defects.push(format!(
                    "COMPILE_ERR {label} row={row:?} fast={jit_fast} opt={opt:?}"
                )),
                Run::SymbolMissing => defects.push(format!(
                    "SYMBOL_MISSING {label} row={row:?} fast={jit_fast} opt={opt:?}"
                )),
                Run::Panic => defects.push(format!(
                    "PANIC {label} row={row:?} fast={jit_fast} opt={opt:?}"
                )),
            }
        }
    }
    out
}

/// Compare all JIT results against each other and (when allowed) the oracle.
/// `consult_oracle` gates oracle comparison for unsigned-with-wide-operands.
fn check(
    module: &trust_ir::Module,
    row: &[i64; 4],
    label: &str,
    consult_oracle: bool,
    oracle_projection: OracleResultProjection,
    defects: &mut Vec<String>,
) {
    let jits = run_all_jit(module, row, label, defects);
    if jits.is_empty() {
        return;
    }
    // cross-JIT agreement (oracle-free): every config must agree.
    let (ref_key, ref_val) = jits[0];
    for &(key, val) in &jits[1..] {
        if val != ref_val {
            defects.push(format!(
                "JIT_DISAGREE {label} row={row:?}: {:?}={} vs {:?}={}",
                ref_key, ref_val, key, val
            ));
        }
    }
    // oracle agreement (only when provably comparable).
    if consult_oracle && let Ok(raw_ov) = run_oracle_one(module, row) {
        let Some(ov) = project_oracle_result(raw_ov, oracle_projection) else {
            defects.push(format!(
                    "ORACLE_RESULT_OUT_OF_DOMAIN {label} row={row:?}: raw={raw_ov} projection={oracle_projection:?}"
                ));
            return;
        };
        for &(key, val) in &jits {
            if val != ov {
                defects.push(format!(
                    "MISCOMPILE {label} row={row:?} {:?}: jit={} oracle={}",
                    key, val, ov
                ));
            }
        }
    }
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

    // The interpreter's documented widthless cast model leaves `sext Bool`
    // true as raw `1`. Prove that assumption remains live, then prove the
    // harness projects it to the native one-bit sign extension `-1` and that
    // every JIT configuration agrees. This is an armed guard against either
    // silently reintroducing the false-positive oracle comparison or masking
    // a future interpreter change.
    let ms = build_cmp_module(CmpShape {
        width: Width::I64,
        op: ICmpOp::Slt,
        mat: Materialize::SextI64,
        lhs_const: None,
        rhs_const: None,
        oracle_ok: true,
    });
    let raw = run_oracle_one(&ms, &row).expect("oracle must accept Bool SExt module");
    assert_eq!(raw, 1, "widthless interpreter Bool SExt model changed");
    assert_eq!(
        project_oracle_result(raw, OracleResultProjection::BoolSextI64),
        Some(-1),
        "Bool true must sign-extend from one bit to native i64 -1"
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
        project_oracle_result(raw_false, OracleResultProjection::BoolSextI64),
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
                let m = build_cmp_module(shape);
                let label = format!("dyn {width:?} {op:?} {mat:?}");
                configs += 1;
                for row in &rows {
                    check(
                        &m,
                        row,
                        &label,
                        true,
                        oracle_result_projection(mat),
                        &mut defects,
                    );
                }

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
                        let m = build_cmp_module(s);
                        let label = format!("{tag} {width:?} {op:?} {mat:?} k={k:#x}");
                        configs += 1;
                        // For unsigned ops, only consult the oracle when the
                        // constant operand is a faithful width-w unsigned value
                        // (dynamic side is always faithful). Signed ops are
                        // always faithful here.
                        let consult = if is_unsigned(op) { s.oracle_ok } else { true };
                        for row in &rows {
                            check(
                                &m,
                                row,
                                &label,
                                consult,
                                oracle_result_projection(mat),
                                &mut defects,
                            );
                        }
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
                    let m = build_cmp_module(s);
                    let label = format!("cc {width:?} {op:?} l={kl:#x} r={kr:#x}");
                    configs += 1;
                    let consult = if is_unsigned(op) { ulok && urok } else { true };
                    for row in &rows {
                        check(
                            &m,
                            row,
                            &label,
                            consult,
                            OracleResultProjection::Exact,
                            &mut defects,
                        );
                    }
                }
            }
        }
    }

    eprintln!("cmp_single: {configs} configs, {} defects", defects.len());
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
                    for row in &rows {
                        // Fully faithful operands -> oracle always valid.
                        check(
                            &m,
                            row,
                            &label,
                            true,
                            OracleResultProjection::Exact,
                            &mut defects,
                        );
                    }
                }
            }
        }
    }
    eprintln!("cmp_chains: {configs} configs, {} defects", defects.len());
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
/// interpreter's i128 `as u128` diverges from width-w hardware unsigned), so we
/// rely purely on cross-opt / cross-allocator JIT AGREEMENT (all 8 must match).
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
                        let m = build_cmp_module(s);
                        let label = format!("wideU {tag} {width:?} {op:?} {mat:?} k={k:#x}");
                        configs += 1;
                        for row in &rows {
                            // oracle-free: JIT agreement only.
                            check(
                                &m,
                                row,
                                &label,
                                false,
                                oracle_result_projection(mat),
                                &mut defects,
                            );
                        }
                    }
                }
            }
        }
    }
    eprintln!(
        "cmp_wide_unsigned: {configs} configs (oracle-free JIT-agreement), {} defects",
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
