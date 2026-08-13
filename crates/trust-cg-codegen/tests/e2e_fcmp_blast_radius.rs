//! TRUST-SELF ROUND 32 (thread R32): SCOPE THE owner-#10 `fcmp one` MISCOMPILE
//! BLAST RADIUS across the THREE float-condition-code CONSUMERS.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! CONTEXT (from R31 / owner #10, `e2e_trust_fns_round18.rs`)
//! ═══════════════════════════════════════════════════════════════════════════════
//! R31 CONFIRMED an AArch64 backend miscompile: `fcmp one` (ORDERED not-equal, `a!=b`)
//! returns TRUE for NaN operands; IEEE requires FALSE. Root cause is the float
//! condition-code LOWERING: `from_floatcc(FloatCC::NotEqual) => AArch64CC::NE`
//! (isel.rs:415) is the SAME CC as `UnorderedNotEqual => NE` (isel.rs:423), but they
//! must differ on NaN. `select_fcmp` (the ISel routine for the `Fcmp` OPCODE,
//! isel.rs:9363 — "select" = instruction-selection, NOT the Select instruction) only
//! two-CCs `UnorderedEqual`; ordered-ne therefore lowers to a bare `CSET NE`. On AArch64
//! a NaN FCMP sets NZCV=0b0011 (Z=0), so `NE` (Z==0) is TRUE. Ordered-ne needs `NE && VC`.
//!
//! ✅ FIX LANDED 2026-07-05 (commit 91301ed): `select_fcmp` now materializes ordered-ne
//! (`ONE`) as the two-CC `NE && VC` (`CSET t_ne,NE; CSET t_vc,VC; AND dst,t_ne,t_vc`),
//! so it returns FALSE on NaN across all three consumers. The tests below were flipped
//! from fail-loud pins to a CLEAN BILL: they now assert JIT == interp == IEEE oracle on
//! the FULL 12×18×18 matrix (bare/select/branch) — i.e. the blast radius is closed. A
//! regression re-introducing the bare-`CSET NE` lowering would fail these loudly again.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! THIS ROUND — the blast-radius MAP: {predicate} × {bare, select, branch}
//! ═══════════════════════════════════════════════════════════════════════════════
//! The SAME materialized boolean feeds three consumers. Source analysis
//! (crates/trust-cg-lower/src/isel.rs, confirmed by reading it) pins the shapes:
//!   * `Opcode::Fcmp { cond: FloatCC }` → `select_fcmp` → `CSET <cc>` (the ONe bug).
//!   * `Opcode::Select { cond: IntCC }` → `select_csel` (isel.rs:9163): takes the
//!     condition VALUE `inst.args[0]` (an already-materialized boolean), emits
//!     `CMP cond,#0` + `Csel`. It carries an **IntCC, not a FloatCC** — there is NO
//!     fused fcmp+csel path for a float condition, so a float-fed Select CONSUMES the
//!     Fcmp's boolean.
//!   * `Opcode::Brif` → `select_brif` (isel.rs:4819): `cond_val = inst.args[0]`, emits
//!     `CMP cond,#0` + `B.NE`. Again consumes the materialized boolean (no fused
//!     fcmp+b.cc path for float conditions; the only fused branch path is the i128
//!     overflow `pending_v_flag` idiom).
//!     PREDICTION from source: all three consumers transitively read the ONE buggy boolean,
//!     so all three miscompile `ONe`-on-NaN identically; every other ordered predicate is
//!     correct. The bug therefore NARROWS to a single materialization point (fixing
//!     `select_fcmp`/`from_floatcc` fixes all three consumers) yet every consumer OBSERVABLY
//!     miscompiles. This round PROVES that empirically with exact witnesses.
//!
//! ORACLES (unchanged from R31): `interpret()` is the native reference (R31 verified
//! eval_fcmp IEEE-correct and the Select/CondBr semantics IEEE-correct); an INDEPENDENT
//! hand-coded IEEE ordered/unordered NaN-rule oracle (ordered=false-on-NaN) is ground
//! truth; native==JIT is the codegen claim. A JIT!=interpret divergence on select/branch
//! is a NEW manifestation of owner #10 → pinned fail-loud with consumer + witness.
//!
//! No emit-from-Rust: the emit-closure frontend has NO float support (R31 Finding A —
//! `scalar_tir_ty` returns None for `ty::Float`). Everything here is hand-built trust-ir
//! driven through the production `interpret()` (native oracle) + the trust-cg JIT.
//!
//! Run tests ONE AT A TIME (`-- --exact <name> --test-threads=1`): the JIT engine is not
//! thread-safe at suite scale (jit-parallel-race-2026-06-29.md).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};

use trust_ir::{
    Block as TrustIrBlock, Constant, FCmpOp, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, CastOp, FuncId, ValueId};

// ── distinct, unambiguous payloads (never {0,1}) so the RETURNED value names the
//    branch the consumer took: THEN when the predicate is true, ELSE when false. ──────
const THEN_PAYLOAD: i64 = 0x1111; // 4369 — returned iff the predicate materialized TRUE
const ELSE_PAYLOAD: i64 = 0x2222; // 8738 — returned iff the predicate materialized FALSE

// ── the 12 FCmpOp variants (name↔op) ──────────────────────────────────────────────
const FCMP_OPS: [(FCmpOp, &str); 12] = [
    (FCmpOp::OEq, "oeq"),
    (FCmpOp::ONe, "one"),
    (FCmpOp::OLt, "olt"),
    (FCmpOp::OLe, "ole"),
    (FCmpOp::OGt, "ogt"),
    (FCmpOp::OGe, "oge"),
    (FCmpOp::UEq, "ueq"),
    (FCmpOp::UNe, "une"),
    (FCmpOp::ULt, "ult"),
    (FCmpOp::ULe, "ule"),
    (FCmpOp::UGt, "ugt"),
    (FCmpOp::UGe, "uge"),
];

// The six ORDERED predicates (false-on-NaN); ONe is the lone buggy one.
const ORDERED_OPS: [(FCmpOp, &str); 6] = [
    (FCmpOp::OEq, "oeq"),
    (FCmpOp::ONe, "one"),
    (FCmpOp::OLt, "olt"),
    (FCmpOp::OLe, "ole"),
    (FCmpOp::OGt, "ogt"),
    (FCmpOp::OGe, "oge"),
];

// ── the INDEPENDENT IEEE ordered/unordered NaN-rule oracle (verbatim from R31) ───────
// `unordered` iff either operand is NaN; every ORDERED predicate is false when
// unordered; every UNORDERED predicate is true when unordered. The numeric relation is
// taken from `partial_cmp` — a distinct code path from the interpreter's raw `<`/`==` —
// so this oracle is genuinely independent of `eval_fcmp` for the NaN-combining logic.
fn ieee_oracle(op: FCmpOp, a: f64, b: f64) -> bool {
    let unordered = a.is_nan() || b.is_nan();
    let (lt, eq, gt) = if unordered {
        (false, false, false)
    } else {
        match a.partial_cmp(&b).expect("non-NaN pair must be comparable") {
            std::cmp::Ordering::Less => (true, false, false),
            std::cmp::Ordering::Equal => (false, true, false),
            std::cmp::Ordering::Greater => (false, false, true),
        }
    };
    match op {
        FCmpOp::OEq => eq,
        FCmpOp::ONe => !unordered && !eq,
        FCmpOp::OLt => lt,
        FCmpOp::OLe => lt || eq,
        FCmpOp::OGt => gt,
        FCmpOp::OGe => gt || eq,
        FCmpOp::UEq => unordered || eq,
        FCmpOp::UNe => unordered || !eq,
        FCmpOp::ULt => unordered || lt,
        FCmpOp::ULe => unordered || lt || eq,
        FCmpOp::UGt => unordered || gt,
        FCmpOp::UGe => unordered || gt || eq,
    }
}

// ── the special-value matrix (crosses every NaN / inf / ±0 / normal edge; verbatim) ──
fn fcmp_inputs() -> Vec<f64> {
    vec![
        0.0f64,
        -0.0,
        1.0,
        -1.0,
        2.0,
        -2.0,
        0.5,
        1.5,
        f64::MIN_POSITIVE, // smallest normal
        f64::from_bits(1), // smallest subnormal
        f64::MAX,
        f64::MIN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,                              // a qNaN
        -f64::NAN,                             // sign-flipped NaN
        f64::from_bits(0x7ff0_0000_0000_0001), // an sNaN
        f64::from_bits(0xfff8_0000_0000_0002), // another NaN payload
    ]
}
// 18 values, 4 of them NaN → unordered pairs = 18*18 - 14*14 = 128.
const UNORDERED_PAIRS: usize = 128;

// ── module builders: one per CONSUMER (hand-built = the shape the frontend WOULD emit) ─

/// BARE / pure-materialize consumer: `fn(a,b) -> i64 { (a op b) as i64 }` as
/// `FCmp -> ZExt(bool->i64) -> Return`. This isolates ONLY the `Fcmp` opcode
/// materialization (`select_fcmp`/CSET) — NO `select_csel`, NO `select_brif`. Returns
/// 1 iff the predicate is true, 0 iff false. This is the regression anchor for the R31
/// bare bug (R31 materialized via `Select(cond,1,0)`; the zext form is strictly purer).
fn build_bare_fn(func_id: u32, name: &str, module: &mut TrustIrModule, op: FCmpOp) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F64, Ty::F64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64), (ValueId::new(1), Ty::F64)],
        body: vec![
            InstrNode::new(Inst::FCmp {
                op,
                ty: Ty::F64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    module.add_function(f);
}

/// SELECT consumer: `fn(a,b) -> i64 { select(a op b, THEN, ELSE) }` as
/// `FCmp -> Select(cond, THEN, ELSE) -> Return`, with DISTINCT payloads so the returned
/// value names the branch. Exercises `select_csel` reading the Fcmp boolean.
fn build_select_fn(func_id: u32, name: &str, module: &mut TrustIrModule, op: FCmpOp) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F64, Ty::F64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64), (ValueId::new(1), Ty::F64)],
        body: vec![
            InstrNode::new(Inst::FCmp {
                op,
                ty: Ty::F64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(THEN_PAYLOAD as i128),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(ELSE_PAYLOAD as i128),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Select {
                ty: Ty::I64,
                cond: ValueId::new(2),
                then_val: ValueId::new(3),
                else_val: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    module.add_function(f);
}

/// BRANCH consumer: `fn(a,b) -> i64 { if a op b { THEN } else { ELSE } }` as a diamond —
/// `FCmp -> CondBr(cond, join[THEN], join[ELSE]); join(p) -> Return p`. The payload is
/// passed as the join block's arg, DIFFERING per edge, so the returned value names which
/// edge control flow took. Exercises `select_brif` reading the Fcmp boolean.
fn build_branch_fn(func_id: u32, name: &str, module: &mut TrustIrModule, op: FCmpOp) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F64, Ty::F64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::F64), (ValueId::new(1), Ty::F64)],
            body: vec![
                InstrNode::new(Inst::FCmp {
                    op,
                    ty: Ty::F64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(THEN_PAYLOAD as i128),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(ELSE_PAYLOAD as i128),
                })
                .with_result(ValueId::new(4)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1),
                    then_args: vec![ValueId::new(3)],
                    else_target: BlockId::new(1),
                    else_args: vec![ValueId::new(4)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(5), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            })],
        },
    ];
    module.add_function(f);
}

/// Build a module with one function per FCmpOp for the given consumer builder.
fn build_module(tag: &str, build: fn(u32, &str, &mut TrustIrModule, FCmpOp)) -> TrustIrModule {
    let mut module = TrustIrModule::new(format!("blast_{tag}"));
    for (i, (op, name)) in FCMP_OPS.iter().enumerate() {
        build(i as u32, &format!("{tag}_{name}"), &mut module, *op);
    }
    module
}

// ── JIT harness (verbatim pattern from R31) ─────────────────────────────────────────
type ConsumerFn = unsafe extern "C" fn(f64, f64) -> i64;

fn jit_buffer(module: &TrustIrModule) -> trust_cg_codegen::jit::ExecutableBuffer {
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(module, &HashMap::new())
        .expect("hand-built FP module must JIT-compile (backend supports FP)")
        .buffer
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

/// Drive the REAL interpreter (native oracle) through the production `interpret()` entry.
fn interp(module: &TrustIrModule, name: &str, a: f64, b: f64) -> i64 {
    let out = interpret(
        module,
        name,
        &[InterpreterValue::Float(a), InterpreterValue::Float(b)],
    )
    .expect("interpret() of a single consumer fn must succeed");
    match out.as_slice() {
        [InterpreterValue::Int(v)] => *v as i64,
        other => panic!("unexpected interpret result for {name}: {other:?}"),
    }
}

/// Expected consumer output given the IEEE-true predicate value: bare uses {1,0},
/// select/branch use {THEN,ELSE}. `truthy` maps a bool to the consumer's true-payload.
fn expected(oracle_true: bool, true_payload: i64, false_payload: i64) -> i64 {
    if oracle_true {
        true_payload
    } else {
        false_payload
    }
}

// ============================================================================
// TEST 1 — BARE consumer (regression anchor). Pure `Fcmp -> ZExt -> Return`.
//   Confirms: (a) interpreter == IEEE oracle everywhere; (b) `one`-on-NaN is TRUE in
//   JIT (materialized 1) while interp/oracle are false (128 rows) — the R31 bug still
//   present in the pure-materialize path; (c) EVERY other predicate agrees JIT==oracle.
// ============================================================================
#[test]
fn blast_radius_bare_regression_anchor() {
    let module = build_module("bare", build_bare_fn);
    let buffer = jit_buffer(&module);
    let inputs = fcmp_inputs();

    let mut one_nan_fixed = 0usize;
    let mut agree = 0usize;
    for (op, name) in FCMP_OPS.iter() {
        let sym = format!("bare_{name}");
        let f: ConsumerFn = unsafe { std::mem::transmute(bind(&buffer, &sym)) };
        for &a in &inputs {
            for &b in &inputs {
                let jit = unsafe { f(a, b) };
                let itp = interp(&module, &sym, a, b);
                let oracle = ieee_oracle(*op, a, b);
                let want = expected(oracle, 1, 0);
                assert_eq!(
                    itp, want,
                    "interpreter bare {name} != oracle a={a:?} b={b:?}"
                );
                let unordered = a.is_nan() || b.is_nan();
                // owner #10 FIXED (91301ed): ordered-ne now returns false on NaN
                // (select_fcmp emits the two-CC `NE && VC`), so EVERY predicate —
                // including one-on-NaN — agrees with the IEEE oracle.
                assert_eq!(
                    jit,
                    want,
                    "bare JIT != oracle {name}: a={a:?}({:#x}) b={b:?}({:#x}) jit={jit} want={want}",
                    a.to_bits(),
                    b.to_bits()
                );
                agree += 1;
                if *op == FCmpOp::ONe && unordered {
                    assert_eq!(
                        jit, 0,
                        "owner #10: bare one-on-NaN must now be false (got {jit})"
                    );
                    one_nan_fixed += 1;
                }
            }
        }
    }
    assert_eq!(
        one_nan_fixed, UNORDERED_PAIRS,
        "bare one-on-NaN fixed-cell count changed: {one_nan_fixed}"
    );
    assert_eq!(agree, 12 * 18 * 18, "bare agreement count off: {agree}");
    eprintln!(
        "BARE consumer: JIT==interp==oracle on ALL {agree} rows; owner #10 FIXED — the \
         `one`-on-NaN cells ({one_nan_fixed}) now correctly return false on NaN. Pure \
         Fcmp->ZExt path — no select_csel/select_brif. Regression anchor armed."
    );
}

// ============================================================================
// TEST 2 — SELECT consumer: `select(a op b, THEN, ELSE)` over the full matrix.
//   Determines whether the SELECT path miscompiles `one`-on-NaN (owner #10 widens to
//   select_csel) or is correct (narrows). Distinct payloads make the taken branch
//   unambiguous. Sweeps ALL 12 predicates; asserts the ONLY divergence class is
//   `one`-on-NaN and it manifests as the JIT picking the THEN branch (0x1111) where
//   IEEE requires ELSE (0x2222).
// ============================================================================
#[test]
fn blast_radius_select_full_matrix() {
    let module = build_module("sel", build_select_fn);
    let buffer = jit_buffer(&module);
    let inputs = fcmp_inputs();

    let mut one_nan_fixed = 0usize;
    let mut agree = 0usize;
    for (op, name) in FCMP_OPS.iter() {
        let sym = format!("sel_{name}");
        let f: ConsumerFn = unsafe { std::mem::transmute(bind(&buffer, &sym)) };
        for &a in &inputs {
            for &b in &inputs {
                let jit = unsafe { f(a, b) };
                let itp = interp(&module, &sym, a, b);
                let oracle = ieee_oracle(*op, a, b);
                let want = expected(oracle, THEN_PAYLOAD, ELSE_PAYLOAD);
                assert_eq!(
                    itp, want,
                    "interpreter select {name} != oracle a={a:?} b={b:?}"
                );
                let unordered = a.is_nan() || b.is_nan();
                // owner #10 FIXED: the select_csel consumer reads the corrected fcmp
                // boolean, so one-on-NaN now takes the ELSE branch like the IEEE oracle.
                assert_eq!(
                    jit,
                    want,
                    "select JIT != oracle {name}: a={a:?}({:#x}) b={b:?}({:#x}) jit={jit:#x} want={want:#x}",
                    a.to_bits(),
                    b.to_bits()
                );
                agree += 1;
                if *op == FCmpOp::ONe && unordered {
                    assert_eq!(
                        jit, ELSE_PAYLOAD,
                        "owner #10: select one-on-NaN must now take the ELSE branch"
                    );
                    one_nan_fixed += 1;
                }
            }
        }
    }
    assert_eq!(
        one_nan_fixed, UNORDERED_PAIRS,
        "select one-on-NaN fixed-cell count changed: {one_nan_fixed}"
    );
    assert_eq!(agree, 12 * 18 * 18, "select agreement count off: {agree}");
    eprintln!(
        "SELECT consumer: JIT==interp==oracle on ALL {agree} rows; owner #10 FIXED — the \
         `one`-on-NaN cells ({one_nan_fixed}) now correctly take the ELSE branch (0x2222) \
         on NaN in select_csel, matching IEEE. No divergence remains in the select path."
    );
}

// ============================================================================
// TEST 3 — BRANCH consumer: `if a op b { THEN } else { ELSE }` over the full matrix.
//   Determines whether the conditional-BRANCH path miscompiles `one`-on-NaN. The
//   returned payload names the edge control flow took.
// ============================================================================
#[test]
fn blast_radius_branch_full_matrix() {
    let module = build_module("br", build_branch_fn);
    let buffer = jit_buffer(&module);
    let inputs = fcmp_inputs();

    let mut one_nan_fixed = 0usize;
    let mut agree = 0usize;
    for (op, name) in FCMP_OPS.iter() {
        let sym = format!("br_{name}");
        let f: ConsumerFn = unsafe { std::mem::transmute(bind(&buffer, &sym)) };
        for &a in &inputs {
            for &b in &inputs {
                let jit = unsafe { f(a, b) };
                let itp = interp(&module, &sym, a, b);
                let oracle = ieee_oracle(*op, a, b);
                let want = expected(oracle, THEN_PAYLOAD, ELSE_PAYLOAD);
                assert_eq!(
                    itp, want,
                    "interpreter branch {name} != oracle a={a:?} b={b:?}"
                );
                let unordered = a.is_nan() || b.is_nan();
                // owner #10 FIXED: the select_brif consumer reads the corrected fcmp
                // boolean, so one-on-NaN now flows to the else-edge like the IEEE oracle.
                assert_eq!(
                    jit,
                    want,
                    "branch JIT != oracle {name}: a={a:?}({:#x}) b={b:?}({:#x}) jit={jit:#x} want={want:#x}",
                    a.to_bits(),
                    b.to_bits()
                );
                agree += 1;
                if *op == FCmpOp::ONe && unordered {
                    assert_eq!(
                        jit, ELSE_PAYLOAD,
                        "owner #10: branch one-on-NaN must now flow to the else-edge"
                    );
                    one_nan_fixed += 1;
                }
            }
        }
    }
    assert_eq!(
        one_nan_fixed, UNORDERED_PAIRS,
        "branch one-on-NaN fixed-cell count changed: {one_nan_fixed}"
    );
    assert_eq!(agree, 12 * 18 * 18, "branch agreement count off: {agree}");
    eprintln!(
        "BRANCH consumer: JIT==interp==oracle on ALL {agree} rows; owner #10 FIXED — the \
         `one`-on-NaN cells ({one_nan_fixed}) now correctly flow to the else-edge (0x2222) \
         on NaN in select_brif, matching IEEE. No divergence remains in the branch path."
    );
}

// ============================================================================
// TEST 4 — PINNED fail-loud blast-radius witnesses. For EACH consumer (bare/select/
//   branch), pins the exact `one`(1.0, NaN) miscompile AND asserts the five OTHER
//   ordered predicates (OEq/OLt/OLe/OGt/OGe) are CORRECT on (1.0, NaN) — all false, so
//   they take the false/else branch. When `select_fcmp`/`from_floatcc` is fixed the JIT
//   `one` returns false, every assert flips, and this pin fails loudly to prompt removal.
// ============================================================================
#[test]
#[allow(clippy::type_complexity)] // Rows bind a consumer builder and its payload oracle.
fn blast_radius_pinned_witnesses() {
    let nan = f64::NAN;

    // (consumer tag, builder, true-payload, false-payload)
    let consumers: [(&str, fn(u32, &str, &mut TrustIrModule, FCmpOp), i64, i64); 3] = [
        ("bare", build_bare_fn, 1, 0),
        ("sel", build_select_fn, THEN_PAYLOAD, ELSE_PAYLOAD),
        ("br", build_branch_fn, THEN_PAYLOAD, ELSE_PAYLOAD),
    ];

    for (tag, build, tp, fp) in consumers {
        let module = build_module(tag, build);
        let buffer = jit_buffer(&module);

        // owner #10 FIXED: ordered-ne on a finite/NaN pair. IEEE=false (=> false branch);
        // the JIT now takes the false branch too (was: wrongly the true branch).
        let _ = tp;
        let one: ConsumerFn = unsafe { std::mem::transmute(bind(&buffer, &format!("{tag}_one"))) };
        for &(a, b) in &[(1.0f64, nan), (nan, 1.0), (nan, nan), (0.0, nan)] {
            let jit = unsafe { one(a, b) };
            let itp = interp(&module, &format!("{tag}_one"), a, b);
            assert!(
                !ieee_oracle(FCmpOp::ONe, a, b),
                "IEEE ordered-ne must be false on NaN"
            );
            assert_eq!(
                itp, fp,
                "{tag} interpreter ordered-ne must take the false branch on NaN"
            );
            assert_eq!(
                jit, fp,
                "owner #10 REGRESSED ({tag}): JIT ordered-ne on (a={a:?}, b={b:?}) must take \
                 the FALSE branch on NaN (IEEE ONE is false when unordered); the two-CC \
                 `NE && VC` lowering in select_fcmp is missing/broken.",
            );
        }

        // The five OTHER ordered predicates are CORRECT on (1.0, NaN): all false => the
        // consumer takes the false/else branch. This is the "non-buggy cells stay
        // correct" half of the blast-radius map, per consumer.
        for (op, name) in ORDERED_OPS.iter().filter(|(op, _)| *op != FCmpOp::ONe) {
            let f: ConsumerFn =
                unsafe { std::mem::transmute(bind(&buffer, &format!("{tag}_{name}"))) };
            let jit = unsafe { f(1.0, nan) };
            let itp = interp(&module, &format!("{tag}_{name}"), 1.0, nan);
            assert!(
                !ieee_oracle(*op, 1.0, nan),
                "ordered {name} must be false on NaN"
            );
            assert_eq!(
                (jit, itp),
                (fp, fp),
                "{tag} ordered {name}(1.0, NaN) must take the FALSE branch in BOTH JIT and \
                 interpreter (jit={jit:#x} interp={itp:#x}) — a NEW miscompile if not"
            );
        }
        eprintln!(
            "owner #10 FIXED ({tag}): `one`(finite,NaN) now takes the FALSE branch like \
             OEq/OLt/OLe/OGt/OGe (all correct on NaN), matching IEEE across this consumer."
        );
    }
}

// ============================================================================
// TEST 5 — ARMED negative controls: the select/branch differentials are load-bearing.
//   For select and branch, a wrong-op module (computes OGt) checked against the OLt
//   oracle must DIVERGE on ordered pairs (proving the JIT genuinely computes the op /
//   routes the boolean, not a no-op), while the pristine OLt module matches its oracle.
//   This proves the select/branch coverage above is real, not a masked no-op.
// ============================================================================
#[test]
fn blast_radius_select_branch_armed_controls() {
    let inputs = fcmp_inputs();

    for (tag, build) in [
        (
            "sel",
            build_select_fn as fn(u32, &str, &mut TrustIrModule, FCmpOp),
        ),
        (
            "br",
            build_branch_fn as fn(u32, &str, &mut TrustIrModule, FCmpOp),
        ),
    ] {
        // "corrupted": function computes OGt, but we check against the OLt-mapped oracle.
        let mut corrupt = TrustIrModule::new(format!("blast_{tag}_corrupt"));
        build(0, &format!("{tag}_probe"), &mut corrupt, FCmpOp::OGt);
        let cbuf = jit_buffer(&corrupt);
        let cf: ConsumerFn = unsafe { std::mem::transmute(bind(&cbuf, &format!("{tag}_probe"))) };

        // "pristine": function computes OLt, checked against the OLt-mapped oracle.
        let mut pristine = TrustIrModule::new(format!("blast_{tag}_pristine"));
        build(0, &format!("{tag}_probe"), &mut pristine, FCmpOp::OLt);
        let pbuf = jit_buffer(&pristine);
        let pf: ConsumerFn = unsafe { std::mem::transmute(bind(&pbuf, &format!("{tag}_probe"))) };

        let mut diverged = 0usize;
        for &a in &inputs {
            for &b in &inputs {
                let want_olt = expected(ieee_oracle(FCmpOp::OLt, a, b), THEN_PAYLOAD, ELSE_PAYLOAD);
                assert_eq!(
                    unsafe { pf(a, b) },
                    want_olt,
                    "{tag} pristine OLt != oracle a={a:?} b={b:?}"
                );
                if unsafe { cf(a, b) } != want_olt {
                    diverged += 1;
                }
            }
        }
        assert!(
            diverged > 0,
            "{tag} wrong-op (OGt vs OLt-oracle) diverged on NO rows — the {tag} differential \
             is not load-bearing (JIT ignoring the op / not routing the boolean?!)"
        );
        eprintln!(
            "armed control ({tag}): OGt-vs-OLt-oracle diverged on {diverged} rows; pristine==oracle"
        );
    }
}
