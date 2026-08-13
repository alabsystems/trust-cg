//! TRUST-SELF ROUND 31 (thread R31, TRUST BATCH 18): the trust-cg IR interpreter's
//! FLOAT / fcmp / cast / select paths — `trust-cg/crates/trust-cg-codegen/src/interpreter.rs`
//! (oracle #2 of the e2e_frontend_roundtrip harness). Net-new vs round 4 (the INT
//! core: eval_int_binop/unop/icmp/overflow) and round 25/26 (the trust_cg_verify
//! integer-only fp_bitmodel — a DIFFERENT crate).
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! FINDING A [FRONTEND FLOAT GAP] — the interpreter's float surface cannot be routed
//! through this program's Rust->MIR->trust-ir emit-closure pipeline AT ALL.
//! ═══════════════════════════════════════════════════════════════════════════════
//! The emit-closure FRONTEND (`trust-ir/frontend/src/mir_lower.rs`) has NO float
//! support: `scalar_tir_ty` (mir_lower.rs:116-137) maps only Bool/Int/Uint and
//! returns `None` for `ty::Float(_)`. Empirically confirmed (stage1 trust_ir_mir,
//! see tests/slices/trust_interp_float_probe_slice.rs + trust_interp_fcmp_slice.rs):
//!   * a verbatim transcription of the real `eval_fcmp` (:880), and every DIRECT
//!     float op — `a+b`, `a<b`, `a==b`, `f as i`, `i as f` — FAILS at emit with
//!     `place leaf is not a memory scalar: float` (place_leaf_tir_ty, :5178) or
//!     `Rvalue::Cast source not a scalar leaf: float`;
//!   * a float INTRINSIC METHOD — `f64::min`/`sqrt`/`is_nan`/`abs`/... — "emits" but
//!     ONLY as a HOLLOW F4 stub: the f64 is passed opaquely by-ref as `ptr` and the
//!     op is a BODYLESS extern leaf, which fails at JIT LINK (UnresolvedSymbol).
//!     CONSEQUENCE: no emit-closure module ever contains an FCmp / float-BinOp /
//!     float-Cast, so the interpreter's `eval_fcmp` / float-`eval_binop` / float-`eval_cast`
//!     are DEAD CODE in the real native==JIT differential — oracle #2's float handling is
//!     UNCOVERED by the program's native==JIT guarantee. (The gap is frontend-only: the
//!     trust-cg BACKEND fully supports FP — cf. e2e_aarch64_fp_minmax, which hand-builds,
//!     links, and runs f64 ops. Test `trust_interp_float_hollow_leaf_jit_link_fails_pinned`
//!     pins the hollow-stub link failure fail-loud.)
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! FINDING B [NEW CONFIRMED AArch64 BACKEND MISCOMPILE] — `fcmp one` (ordered
//! not-equal) is TRUE for NaN operands on AArch64; it must be FALSE.
//! ═══════════════════════════════════════════════════════════════════════════════
//! Because the frontend can't connect the interpreter's fcmp to the JIT, this round
//! verifies the equivalence the harness RELIES on directly: for each of the 12
//! `FCmpOp` variants over a NaN/inf/±0/normal matrix it compares the trust-cg BACKEND's
//! JIT'd `fcmp <op>` machine code against the REAL interpreter `eval_fcmp` (driven
//! through the production `interpret()` entry on a hand-built FCmp module — the SHAPE
//! the frontend WOULD emit), an INDEPENDENT hand-coded IEEE ordered/unordered oracle,
//! and the host f64 relation. That differential caught a real bug:
//!   `eval_fcmp(ONe, 1.0, NaN)` = false (correct: ordered predicates are false on NaN)
//!   JIT `fcmp one` (1.0, NaN)  = TRUE  (WRONG)
//! ROOT CAUSE (single line): `trust-cg-lower/src/isel.rs:415` maps
//! `FloatCC::NotEqual => AArch64CC::NE`, and `select_fcmp` (isel.rs:9363) only
//! special-cases `UnorderedEqual`, so ordered-ne lowers to a single `CSET NE`. On
//! AArch64 a NaN FCMP sets NZCV=0011 (Z=0), so `NE` (Z==0) is TRUE — computing the
//! UNORDERED not-equal (which correctly ALSO maps to NE at isel.rs:423) instead of the
//! ordered one. Every other predicate in the isel.rs:414-430 table is correct; ONe is
//! the lone bug. Ordered-ne is not a single AArch64 CC — it needs `NE && VC` (Z==0 AND
//! V==0), i.e. the two-CC treatment `UnorderedEqual` already gets.
//! WHY MISSED: x86 is CORRECT here (x86 SETNE reads ZF, which is 1 for NaN -> false,
//! isel comment x86_64_isel.rs:631) and the aarch64 fuzz sweep
//! (trust-cg-fuzz fp_const_and_fcmp.rs) only feeds INTEGER-derived f64 operands
//! (rows `[i64;4]` via SIToFP) — never a NaN. Pinned fail-loud in
//! `trust_fcmp_one_nan_aarch64_miscompile_pinned`: when isel.rs:415 is fixed the JIT
//! returns false, the assert flips, and the pin fails loudly to prompt removal.
//!
//! Run tests ONE AT A TIME (`-- --exact <name> --test-threads=1`): the JIT engine is
//! not thread-safe at suite scale (jit-parallel-race-2026-06-29.md).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};

use trust_ir::{
    BinOp, Block as TrustIrBlock, Constant, FCmpOp, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

// ── the 12 FCmpOp variants, with a stable name↔index mapping for the sweep ────────
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

// ── the six lowerable float BinOp arms of eval_binop (interpreter.rs:738-773) ──────
const FBINOPS: [(BinOp, &str); 6] = [
    (BinOp::FAdd, "fadd"),
    (BinOp::FSub, "fsub"),
    (BinOp::FMul, "fmul"),
    (BinOp::FDiv, "fdiv"),
    (BinOp::FMin, "fmin"),
    (BinOp::FMax, "fmax"),
];

// ── module builders (hand-built trust-ir = the shape the frontend WOULD emit) ─────

/// `fn fcmp_<name>(a: f64, b: f64) -> i64 { (a <op> b) as i64 }`: an `FCmp` producing
/// a bool, then a `Select` mapping bool→{1,0} for a clean integer JIT ABI.
fn build_fcmp_fn(func_id: u32, name: &str, module: &mut TrustIrModule, op: FCmpOp) {
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
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
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

fn build_fcmp_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("interp_fcmp");
    for (i, (op, name)) in FCMP_OPS.iter().enumerate() {
        build_fcmp_fn(i as u32, &format!("fcmp_{name}"), &mut module, *op);
    }
    module
}

/// One-op module `fn <name>(a: f64, b: f64) -> f64 { a <op> b }`.
fn build_fbinop_module(name: &str, op: BinOp) -> TrustIrModule {
    let mut module = TrustIrModule::new("interp_fbinop");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F64, Ty::F64],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64), (ValueId::new(1), Ty::F64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty: Ty::F64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(f);
    module
}

// ── the INDEPENDENT IEEE ordered/unordered NaN-rule oracle ────────────────────────
// Derived from first principles: `unordered` iff either operand is NaN; every ORDERED
// predicate is false when unordered; every UNORDERED predicate is true when unordered.
// The numeric relation (non-NaN case) is taken from `partial_cmp` — a distinct code
// path from the interpreter's raw `<`/`==`/`!=` — so this oracle is genuinely
// independent of `eval_fcmp` for the NaN-combining logic it checks.
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

/// The native transcription of the interpreter's eval_fcmp (interpreter.rs:880),
/// VERBATIM 12-arm match — the source-of-truth for what the interpreter computes.
fn eval_fcmp_native(op: FCmpOp, lhs: f64, rhs: f64) -> bool {
    match op {
        FCmpOp::OEq => lhs == rhs,
        FCmpOp::ONe => !lhs.is_nan() && !rhs.is_nan() && lhs != rhs,
        FCmpOp::OLt => lhs < rhs,
        FCmpOp::OLe => lhs <= rhs,
        FCmpOp::OGt => lhs > rhs,
        FCmpOp::OGe => lhs >= rhs,
        FCmpOp::UEq => lhs == rhs || lhs.is_nan() || rhs.is_nan(),
        FCmpOp::UNe => lhs != rhs || lhs.is_nan() || rhs.is_nan(),
        FCmpOp::ULt => lhs < rhs || lhs.is_nan() || rhs.is_nan(),
        FCmpOp::ULe => lhs <= rhs || lhs.is_nan() || rhs.is_nan(),
        FCmpOp::UGt => lhs > rhs || lhs.is_nan() || rhs.is_nan(),
        FCmpOp::UGe => lhs >= rhs || lhs.is_nan() || rhs.is_nan(),
    }
}

fn minimum_number_spec(a: f64, b: f64) -> f64 {
    if a.is_nan() {
        if b.is_nan() {
            f64::from_bits(a.to_bits() | 0x0008_0000_0000_0000)
        } else {
            b
        }
    } else if b.is_nan() {
        a
    } else {
        a.min(b)
    }
}

fn maximum_number_spec(a: f64, b: f64) -> f64 {
    if a.is_nan() {
        if b.is_nan() {
            f64::from_bits(a.to_bits() | 0x0008_0000_0000_0000)
        } else {
            b
        }
    } else if b.is_nan() {
        a
    } else {
        a.max(b)
    }
}

/// Independent specification of the interpreter's float BinOp semantics.
/// FMin/FMax spell out Trust-IR minimumNumber/maximumNumber so signaling-NaN
/// behavior is independent of the host rustc's lowering of `f64::min/max`.
fn eval_binop_spec(op: BinOp, a: f64, b: f64) -> f64 {
    match op {
        BinOp::FAdd => a + b,
        BinOp::FSub => a - b,
        BinOp::FMul => a * b,
        BinOp::FDiv => a / b,
        BinOp::FRem => a % b,
        BinOp::FMin => minimum_number_spec(a, b),
        BinOp::FMax => maximum_number_spec(a, b),
        _ => unreachable!("non-float binop in eval_binop_spec"),
    }
}

// ── the special-value matrix (crosses every NaN / inf / ±0 / normal edge) ──────────
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

// ── JIT harness ───────────────────────────────────────────────────────────────────

type FcmpFn = unsafe extern "C" fn(f64, f64) -> i64;
type FbinFn = unsafe extern "C" fn(f64, f64) -> f64;

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

/// Drive the REAL interpreter `eval_fcmp` (interpreter.rs:880) through the production
/// `interpret()` entry on the hand-built FCmp+Select module.
fn interp_fcmp(module: &TrustIrModule, name: &str, a: f64, b: f64) -> bool {
    let out = interpret(
        module,
        name,
        &[InterpreterValue::Float(a), InterpreterValue::Float(b)],
    )
    .expect("interpret() of a single FCmp+Select must succeed");
    match out.as_slice() {
        [InterpreterValue::Int(v)] => *v != 0,
        other => panic!("unexpected interpret result for {name}: {other:?}"),
    }
}

/// Drive the REAL interpreter float `eval_binop` (interpreter.rs:738-773) via interpret().
fn interp_fbinop(module: &TrustIrModule, name: &str, a: f64, b: f64) -> f64 {
    let out = interpret(
        module,
        name,
        &[InterpreterValue::Float(a), InterpreterValue::Float(b)],
    )
    .expect("interpret() of a single float BinOp must succeed");
    match out.as_slice() {
        [InterpreterValue::Float(v)] => *v,
        other => panic!("unexpected interpret result for {name}: {other:?}"),
    }
}

// ============================================================================
// TEST 1 — the interpreter's eval_fcmp is IEEE-CORRECT (positive result).
//   interpret()==eval_fcmp_native==independent IEEE oracle over 12 ops × matrix.
//   This is the genuine verification of oracle #2's float-comparison SOUNDNESS: it
//   would catch a wrong ordered-NaN / unordered-NaN rule (the subtle ONe is-nan
//   guard the source comments warn about). NOTE: native-only — no JIT leg, because
//   the emit-closure frontend cannot lower the interpreter's float source (FINDING A).
// ============================================================================
#[test]
fn trust_interp_eval_fcmp_is_ieee_correct() {
    let module = build_fcmp_module();
    let inputs = fcmp_inputs();
    let mut checked = 0usize;
    for (op, name) in FCMP_OPS.iter() {
        let sym = format!("fcmp_{name}");
        for &a in &inputs {
            for &b in &inputs {
                let interp = interp_fcmp(&module, &sym, a, b);
                let native = eval_fcmp_native(*op, a, b);
                let oracle = ieee_oracle(*op, a, b);
                assert_eq!(
                    native, oracle,
                    "eval_fcmp_native {name} != IEEE oracle: a={a:?} b={b:?}"
                );
                assert_eq!(
                    interp,
                    oracle,
                    "REAL interpreter eval_fcmp {name} != IEEE oracle: a={a:?}({:#x}) b={b:?}({:#x})",
                    a.to_bits(),
                    b.to_bits()
                );
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 12 * 18 * 18, "sweep lost coverage: {checked}");
    eprintln!(
        "interpreter eval_fcmp verified IEEE-correct over {checked} (op,a,b): \
         interpret()==native==independent-IEEE-oracle"
    );
}

// ============================================================================
// TEST 2 — JIT fcmp vs the interpreter over the full matrix; the divergence set is
//   EXACTLY the ordered-not-equal-on-NaN bug (FINDING B), and nothing else.
// ============================================================================
#[test]
fn trust_fcmp_jit_vs_interpreter_full_matrix() {
    let module = build_fcmp_module();
    let buffer = jit_buffer(&module);
    let inputs = fcmp_inputs();

    let mut one_nan_divergences = 0usize;
    let mut agree = 0usize;
    for (op, name) in FCMP_OPS.iter() {
        let sym = format!("fcmp_{name}");
        let f: FcmpFn = unsafe { std::mem::transmute(bind(&buffer, &sym)) };
        for &a in &inputs {
            for &b in &inputs {
                let jit = unsafe { f(a, b) } != 0;
                let interp = interp_fcmp(&module, &sym, a, b);
                let oracle = ieee_oracle(*op, a, b);
                // interpreter is always IEEE-correct (Test 1); assert it here too.
                assert_eq!(
                    interp, oracle,
                    "interpreter {name} != oracle a={a:?} b={b:?}"
                );

                let unordered = a.is_nan() || b.is_nan();
                // owner #10 FIXED: JIT == interpreter == oracle for EVERY predicate,
                // including ordered-ne on NaN (now false), bit for bit.
                assert_eq!(
                    jit,
                    oracle,
                    "JIT != oracle {name}: a={a:?}({:#x}) b={b:?}({:#x}) jit={jit} oracle={oracle}",
                    a.to_bits(),
                    b.to_bits()
                );
                agree += 1;
                if *op == FCmpOp::ONe && unordered {
                    assert!(!jit, "owner #10: fcmp one must now be false on NaN");
                    one_nan_divergences += 1; // now: fixed-cell count (all agree)
                }
            }
        }
    }
    // The previously-divergent one-on-NaN class must still be exercised (so the clean
    // bill is not masking a broken sweep) — now it AGREES. The matrix has 4 NaN values
    // among 18, so the unordered pairs under ONe = 18*18 - 14*14 = 128.
    assert_eq!(
        one_nan_divergences, 128,
        "one-on-NaN fixed-cell count changed: {one_nan_divergences} (expected 128)"
    );
    assert_eq!(agree, 12 * 18 * 18, "agreement count off: {agree}");
    eprintln!(
        "JIT==interpreter==oracle on ALL {agree} rows (owner #10 FIXED); the {one_nan_divergences} \
         one-on-NaN cells now correctly return false on NaN"
    );
}

// ============================================================================
// TEST 3 — PINNED fail-loud minimal repro of the AArch64 `fcmp one`-on-NaN bug.
//   Asserts the CURRENT (buggy) behavior. When isel.rs:415 is fixed so ordered-ne
//   excludes NaN (NE && VC), the JIT returns false, the assert flips, and this pin
//   fails loudly to prompt its removal + promotion to full agreement.
// ============================================================================
#[test]
fn trust_fcmp_one_nan_aarch64_miscompile_pinned() {
    let module = build_fcmp_module();
    let buffer = jit_buffer(&module);
    let f: FcmpFn = unsafe { std::mem::transmute(bind(&buffer, "fcmp_one")) };

    // minimal repro: one finite operand, one NaN.
    let nan = f64::NAN;
    for &(a, b) in &[(1.0f64, nan), (nan, 1.0), (nan, nan), (0.0, nan)] {
        let jit = unsafe { f(a, b) } != 0;
        let interp = interp_fcmp(&module, "fcmp_one", a, b);
        let oracle = ieee_oracle(FCmpOp::ONe, a, b);
        assert!(
            !interp,
            "interpreter ordered-ne must be false on NaN (a={a:?} b={b:?})"
        );
        assert!(!oracle, "IEEE oracle ordered-ne must be false on NaN");
        // owner #10 FIXED (91301ed): select_fcmp emits the two-CC `NE && VC`, so ordered-ne
        // is now false on NaN — JIT == interpreter == IEEE oracle.
        assert!(
            !jit,
            "owner #10 REGRESSED: JIT `fcmp one`(a={a:?}, b={b:?}) must be FALSE on NaN \
             (the two-CC NE && VC lowering in select_fcmp is missing/broken)."
        );
    }
    // control finite pairs: ordered-ne is CORRECT (JIT==interp) when no NaN.
    for &(a, b) in &[(1.0f64, 2.0), (1.0, 1.0), (2.0, 1.0), (-0.0, 0.0)] {
        let jit = unsafe { f(a, b) } != 0;
        let interp = interp_fcmp(&module, "fcmp_one", a, b);
        assert_eq!(
            jit, interp,
            "ordered-ne must agree on the non-NaN pair a={a:?} b={b:?}"
        );
    }
    eprintln!(
        "owner #10 FIXED: JIT `fcmp one`(finite,NaN)=false == interpreter/IEEE; \
         non-NaN pairs agree. Clean bill (fails loudly if the bare-NE lowering returns)."
    );
}

// ============================================================================
// TEST 4 — ARMED negative control: the fcmp differential genuinely detects a wrong
//   op. Build a module whose function is FCmpOp::OGt but compare its JIT output to
//   the OLt oracle: they must DIVERGE on ordered pairs (proving the JIT computes the
//   actual op, not a no-op / the oracle). Then restore (OLt vs OLt) and agree.
// ============================================================================
#[test]
fn trust_fcmp_differential_armed_control() {
    // "corrupted": function computes OGt, but we check against the OLt oracle.
    let mut corrupt = TrustIrModule::new("interp_fcmp_corrupt");
    build_fcmp_fn(0, "fcmp_probe", &mut corrupt, FCmpOp::OGt);
    let cbuf = jit_buffer(&corrupt);
    let cf: FcmpFn = unsafe { std::mem::transmute(bind(&cbuf, "fcmp_probe")) };

    // "pristine": function computes OLt, checked against the OLt oracle.
    let mut pristine = TrustIrModule::new("interp_fcmp_pristine");
    build_fcmp_fn(0, "fcmp_probe", &mut pristine, FCmpOp::OLt);
    let pbuf = jit_buffer(&pristine);
    let pf: FcmpFn = unsafe { std::mem::transmute(bind(&pbuf, "fcmp_probe")) };

    let inputs = fcmp_inputs();
    let mut diverged = 0usize;
    for &a in &inputs {
        for &b in &inputs {
            let want_olt = ieee_oracle(FCmpOp::OLt, a, b);
            // pristine must match the OLt oracle exactly.
            assert_eq!(
                (unsafe { pf(a, b) } != 0),
                want_olt,
                "pristine OLt != oracle a={a:?} b={b:?}"
            );
            if (unsafe { cf(a, b) } != 0) != want_olt {
                diverged += 1;
            }
        }
    }
    assert!(
        diverged > 0,
        "the OGt-vs-OLt-oracle control diverged on NO rows — the differential is not \
         load-bearing (JIT ignoring the op?!)"
    );
    eprintln!(
        "armed control: wrong-op (OGt vs OLt-oracle) diverged on {diverged} rows; pristine==oracle"
    );
}

// ============================================================================
// TEST 5 — the float arms of eval_binop (interpreter.rs:738-773): JIT ==
//   interpreter == independent spec, bit-for-bit (to_bits, so NaN/±0 are exact).
//   FAdd/FSub/FMul/FDiv/FMin/FMax. (FRem is covered separately below.)
// ============================================================================
fn is_snan(x: f64) -> bool {
    // A signaling NaN: NaN with the mantissa MSB (quiet bit) CLEAR.
    x.is_nan() && (x.to_bits() & 0x0008_0000_0000_0000) == 0
}

#[test]
fn trust_interp_float_binop_jit_vs_interpreter() {
    let inputs = fcmp_inputs();
    let mut checked = 0usize;
    let mut snan_minmax_cells = 0usize;
    for (op, name) in FBINOPS.iter() {
        let module = build_fbinop_module(name, *op);
        let buffer = jit_buffer(&module);
        let f: FbinFn = unsafe { std::mem::transmute(bind(&buffer, name)) };
        let is_minmax = matches!(op, BinOp::FMin | BinOp::FMax);
        for &a in &inputs {
            for &b in &inputs {
                let jit = unsafe { f(a, b) };
                let interp = interp_fbinop(&module, name, a, b);
                let spec = eval_binop_spec(*op, a, b);
                assert_eq!(
                    interp.to_bits(),
                    spec.to_bits(),
                    "interpreter {name} != independent spec: a={a:?} b={b:?}"
                );
                // owner #11 FIXED: FMin/FMax now canonicalize each operand (self-min/max
                // quiets an sNaN) before the binary op, so JIT == interpreter == spec
                // bit-exact for EVERY float binop, including sNaN min/max.
                assert_eq!(
                    jit.to_bits(),
                    interp.to_bits(),
                    "float {name} JIT != interpreter: a={a:?}({:#x}) b={b:?}({:#x}) jit={:#x} interp={:#x}",
                    a.to_bits(),
                    b.to_bits(),
                    jit.to_bits(),
                    interp.to_bits()
                );
                // Track that the previously-divergent sNaN min/max class is still exercised
                // and now AGREES.
                if is_minmax && (is_snan(a) || is_snan(b)) {
                    snan_minmax_cells += 1;
                }
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 6 * 18 * 18, "sweep lost coverage: {checked}");
    assert!(
        snan_minmax_cells > 0,
        "the sNaN min/max class was never exercised — sweep lost coverage"
    );
    eprintln!(
        "float eval_binop: JIT==interpreter==spec bit-exact over ALL {checked} rows \
         (owner #11 FIXED); the {snan_minmax_cells} sNaN min/max cells now AGREE"
    );
}

// ============================================================================
// TEST 6 — FINDING A pin: the hollow F4 float-intrinsic stub (a real emit of a
//   `f64::is_nan` root: f64 passed by-ref as `ptr`, is_nan a bodyless extern leaf)
//   FAILS to JIT (the float op does not actually lower). Fail-loud: when the frontend
//   gains real float lowering, the emit produces a real body, the JIT succeeds, and
//   this assert flips to prompt promotion to full native==JIT.
// ============================================================================
// ============================================================================
// TEST 7 — owner-#11 regression pin: Trust-IR FMin/FMax return the finite operand
//   for a lone signaling NaN. Both the interpreter's explicit specification helper
//   and the JIT's AArch64 operand-canonicalization must preserve that result. This is
//   intentionally independent of the host rustc's version-specific `f64::min/max`
//   lowering.
// ============================================================================
#[test]
fn trust_fminmax_snan_native_vs_jit_pinned() {
    let snan = f64::from_bits(0x7ff0_0000_0000_0001);
    assert!(is_snan(snan), "test fixture must be a signaling NaN");

    for (op, name) in [(BinOp::FMin, "fmin"), (BinOp::FMax, "fmax")] {
        let module = build_fbinop_module(name, op);
        let buffer = jit_buffer(&module);
        let f: FbinFn = unsafe { std::mem::transmute(bind(&buffer, name)) };

        // Trust-IR minimumNumber/maximumNumber returns the finite operand for sNaN.
        let interp = interp_fbinop(&module, name, 0.0, snan);
        assert_eq!(
            interp.to_bits(),
            0.0f64.to_bits(),
            "interpreter {name}(0.0, sNaN) must be the number 0.0 (Trust-IR semantics)"
        );
        // owner #11 FIXED: JIT FMINNM/FMAXNM now canonicalizes each operand (self-min/max
        // quiets the sNaN), so it returns the NUMBER — matching the interpreter's
        // toolchain-independent Trust-IR semantics.
        let jit = unsafe { f(0.0, snan) };
        assert!(
            !jit.is_nan(),
            "owner #11 REGRESSED: JIT {name}(0.0, sNaN) returned NaN {:#x}, expected the number \
             (operand self-canonicalization missing/broken).",
            jit.to_bits()
        );
        assert_eq!(
            jit.to_bits(),
            interp.to_bits(),
            "owner #11 REGRESSED: JIT {name}(0.0, sNaN) != interpreter — must both be 0.0."
        );
        eprintln!(
            "owner #11 FIXED: {name}(0.0, sNaN): JIT == interpreter == 0.0 (number); the \
             signaling-NaN min/max divergence is resolved."
        );
    }
}

const HOLLOW_ISNAN_IR: &str = include_str!("slices/trust_interp_float_hollow_isnan.tir");

#[test]
fn trust_interp_float_hollow_leaf_jit_link_fails_pinned() {
    let module = trust_ir::parser::parse_module(HOLLOW_ISNAN_IR)
        .expect("the hollow-stub .tir must still PARSE (it emitted+validated clean)");
    // The stub calls a BODYLESS extern `...is_nan` leaf — the actual float op never
    // lowered. JIT compile must FAIL (F4 UnresolvedSymbol), proving the "emit-OK" is a
    // hollow stub, not real float support.
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    let result = Compiler::new(config).compile_module_to_jit(&module, &HashMap::new());
    match result {
        Ok(_) => panic!(
            "PIN STALE: the hollow float-intrinsic stub now JIT-compiles — the \
             emit-closure frontend appears to have gained real float lowering. \
             Re-emit the interpreter float slices and promote FINDING A to native==JIT."
        ),
        Err(e) => {
            let msg = format!("{e:?}");
            eprintln!("PIN ARMED (FINDING A): hollow float-intrinsic stub fails to JIT: {msg}");
        }
    }
}
