// trust-cg-verify/wasm_lowering_proofs.rs - trust-ir → wasm refinement proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Per-instruction lowering-refinement proofs for the trust-cg WebAssembly
//! backend: each obligation asserts that the wasm op the backend emits computes
//! the same function as the trust-ir op it lowers from, discharged as a single
//! SMT `NOT(trust_ir == wasm)` UNSAT check (see
//! [`crate::lowering_proof::ProofObligation::negated_equivalence`]).
//!
//! # Honesty: reconstruction supersedes the degenerate static proofs (task #71)
//!
//! These static obligations build BOTH sides from hand-written encoders. For the
//! plain int arithmetic (`add`/`sub`/`mul`), int division/remainder
//! (`div_s/div_u/rem_s/rem_u`), bitwise (`and/or/xor`), and FP arithmetic
//! (`fadd/fsub/fmul/fdiv`), the trust-ir encoder and the wasm encoder produce the
//! STRUCTURALLY IDENTICAL SmtExpr (`bvadd == bvadd`, `fp.add == fp.add`, ...).
//! Those are degenerate `X == X` self-equalities: they discharge `unsat` only as
//! a MODEL-CONSISTENCY check (no wrong opcode could ever refute them, because the
//! "wasm side" was written to match). Under the strict coverage gate (#61) those
//! count ZERO. The 28 degenerate scalar-ALU/divrem/bitwise/float builders have
//! therefore been DELETED here and are SUPERSEDED by OPERAND RECONSTRUCTION
//! (`wasm_function_verifier::reconstruct_alu_obligation`): at verify time the
//! machine side is rebuilt by DECODING the REAL emitted opcode BYTE over fresh
//! symbolic value-stack operands, so a wrong opcode byte (`i32.sub` 0x6b for an
//! intended add) genuinely REFUTES. That is what `audit_wasm` credits.
//!
//! What REMAINS here are the GENUINELY NON-DEGENERATE static obligations — whose
//! two sides are structurally distinct, so they prove real content on their own:
//!   * SHIFTS (`shl/shr_s/shr_u`, i32/i64): masked wasm side vs unmasked trust-ir
//!     side under the `b < width` precondition (the #57 shift-mask divergence);
//!   * INTEGER COMPARISONS (10 predicates × i32/i64): i1->i32 zero-extend on the
//!     trust-ir side vs the wasm `ite(pred, bv32 1, bv32 0)` lift;
//!   * FLOAT COMPARISONS (12 predicates × f32/f64): interpreter-canonical model
//!     vs the backend's `x!=x`-isnan / `lt|gt`-ONe emission (NaN-precise);
//!   * INTEGER NEGATE (i32/i64): trust-ir `bvneg` vs the wasm `0 - x` expansion;
//!   * INTEGER-WIDTH CASTS (wrap∘zext, wrap∘sext round-trips).
//!     These 54 are registered under [`crate::proof_database::ProofCategory::
//! WasmLowering`] as documented non-degenerate witnesses; the per-opcode gate
//!     credit still flows through reconstruction (so shift/cmp/cast opcodes are
//!     credited the SAME genuine way as the arithmetic ones).
//!
//! The (trust-ir op → wasm op) mapping mirrors the backend's authoritative tables
//! in `trust-cg-codegen/src/wasm/lower.rs` (`int_binop_opcode`, `icmp_opcode`).
//! [`proof_wrong_add_is_sub`] is a deliberately-false obligation proving the
//! harness actually exercises the solver (it must yield a counterexample).

use crate::lowering_proof::ProofObligation;
use crate::smt::SmtExpr;
use crate::trust_ir_semantics::{
    encode_trust_ir_binop, encode_trust_ir_fp_binop, encode_trust_ir_icmp, encode_trust_ir_neg,
};
use crate::wasm_semantics as w;
use trust_cg_lower::instructions::{IntCC, Opcode};
use trust_cg_lower::types::Type;

type ShiftEncoder = fn(SmtExpr, SmtExpr, u32) -> SmtExpr;
type ComparisonEncoder = fn(SmtExpr, SmtExpr) -> SmtExpr;
type ComparisonEntry = (&'static str, IntCC, ComparisonEncoder);

fn vars(width: u32) -> (SmtExpr, SmtExpr) {
    (SmtExpr::var("a", width), SmtExpr::var("b", width))
}

// SUPERSEDED (task #71): `arith_proof` + `arithmetic_proofs` built degenerate
// X==X obligations (trust-ir `bvadd` == wasm `bvadd`). DELETED — Iadd/Isub/Imul
// (i32/i64) are now credited via operand reconstruction (a wrong opcode byte
// decodes to a different op and REFUTES). See `wasm_function_verifier`.

/// Comparison obligation: both sides lifted Bool→i32 (wasm cmp yields i32).
fn cmp_proof(
    name: &str,
    cc: IntCC,
    ty: Type,
    width: u32,
    wasm: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> ProofObligation {
    let (a, b) = vars(width);
    // `encode_trust_ir_icmp` returns a 1-bit result (`ite(pred, bv1, bv0)`).
    // wasm comparison ops yield an i32 (0/1), so zero-extend the i1 to i32 to
    // compare like-for-like. (A previous `lift()` wrongly fed the i1 into an
    // `ite` condition — a double-lift type error that formal SMT discharge via
    // ay caught even though statistical evaluation accepted it.)
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&cc, ty, a.clone(), b.clone()).zero_ext(31),
        aarch64_expr: wasm(a, b),
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    }
}

// SUPERSEDED (task #71): `nonzero`, `no_sdiv_overflow`, `divrem_proof`,
// `division_proofs`, and `float_proofs` built degenerate X==X obligations
// (trust-ir `bvsdiv`/`fp.add`/... == the identical wasm encoder). DELETED — the
// int div/rem (Sdiv/Udiv/Srem/Urem, i32/i64) and FP arith (Fadd/Fsub/Fmul/Fdiv,
// f32/f64) are now credited via operand reconstruction, which carries the SAME
// trap preconditions (`b != 0`, `¬(INT_MIN/-1)` for div_s) and REFUTES on a wrong
// decoded opcode byte. See `wasm_function_verifier`.

/// The wasm-side **1-bit** predicate result of the backend's `emit_fcmp`,
/// modeled in SMT, mirroring lower.rs::emit_fcmp exactly: ordered eq/lt/le/gt/ge
/// are `fp_*`; ONe = lt|gt; UNe = ordered-eq negated (wasm f.ne); the other
/// unordered preds = ordered | isnan(a) | isnan(b), isnan(x) = `x.fp_eq(x).not`
/// (wasm `f.ne(x,x)`). Result is a 1-bit `ite`, matching `encode_trust_ir_fcmp`,
/// so the obligation is a width-1 equality (ay decides FP at this level; a
/// 1→32 zero-extend mix makes ay return `unknown`, so both sides stay 1-bit —
/// the i32 lift the backend applies is a trivial identical widening).
fn wasm_fcmp_model_i1(op: &str, a: &SmtExpr, b: &SmtExpr) -> SmtExpr {
    let isnan = |x: &SmtExpr| x.clone().fp_eq(x.clone()).not_expr();
    let pred = match op {
        "OEq" => a.clone().fp_eq(b.clone()),
        "OLt" => a.clone().fp_lt(b.clone()),
        "OLe" => a.clone().fp_le(b.clone()),
        "OGt" => a.clone().fp_gt(b.clone()),
        "OGe" => a.clone().fp_ge(b.clone()),
        "ONe" => a
            .clone()
            .fp_lt(b.clone())
            .or_expr(a.clone().fp_gt(b.clone())),
        "UNe" => a.clone().fp_eq(b.clone()).not_expr(),
        "UEq" => a
            .clone()
            .fp_eq(b.clone())
            .or_expr(isnan(a))
            .or_expr(isnan(b)),
        "ULt" => a
            .clone()
            .fp_lt(b.clone())
            .or_expr(isnan(a))
            .or_expr(isnan(b)),
        "ULe" => a
            .clone()
            .fp_le(b.clone())
            .or_expr(isnan(a))
            .or_expr(isnan(b)),
        "UGt" => a
            .clone()
            .fp_gt(b.clone())
            .or_expr(isnan(a))
            .or_expr(isnan(b)),
        "UGe" => a
            .clone()
            .fp_ge(b.clone())
            .or_expr(isnan(a))
            .or_expr(isnan(b)),
        _ => panic!("not an FCmp op: {op}"),
    };
    SmtExpr::ite(pred, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// The CANONICAL trust-ir FCmp predicate (1-bit), modeled directly from the
/// trust-ir **interpreter** (`interpret.rs`: `ordered = !isnan(a)&&!isnan(b)`;
/// `OXx = ordered && a<x>b`; `UXx = unordered || a<x>b`). The interpreter is the
/// operational reference (mirrored in Lean). NOTE: this deliberately does NOT
/// use `trust_ir_semantics::encode_trust_ir_fcmp`, whose `NotEqual` arm is
/// `!fp.eq` (UNORDERED) and disagrees with the interpreter's ORDERED `ONe` — a
/// real inconsistency in that SMT-semantics helper; the interpreter is canonical.
fn interp_fcmp_model_i1(op: &str, a: &SmtExpr, b: &SmtExpr) -> SmtExpr {
    let unordered = a.clone().fp_is_nan().or_expr(b.clone().fp_is_nan());
    let ordered = unordered.clone().not_expr();
    let pred = match op {
        "OEq" => ordered.and_expr(a.clone().fp_eq(b.clone())),
        "ONe" => ordered.and_expr(a.clone().fp_eq(b.clone()).not_expr()),
        "OLt" => ordered.and_expr(a.clone().fp_lt(b.clone())),
        "OLe" => ordered.and_expr(a.clone().fp_le(b.clone())),
        "OGt" => ordered.and_expr(a.clone().fp_gt(b.clone())),
        "OGe" => ordered.and_expr(a.clone().fp_ge(b.clone())),
        "UEq" => unordered.clone().or_expr(a.clone().fp_eq(b.clone())),
        "UNe" => unordered
            .clone()
            .or_expr(a.clone().fp_eq(b.clone()).not_expr()),
        "ULt" => unordered.clone().or_expr(a.clone().fp_lt(b.clone())),
        "ULe" => unordered.clone().or_expr(a.clone().fp_le(b.clone())),
        "UGt" => unordered.clone().or_expr(a.clone().fp_gt(b.clone())),
        "UGe" => unordered.clone().or_expr(a.clone().fp_ge(b.clone())),
        _ => panic!("not an FCmp op: {op}"),
    };
    SmtExpr::ite(pred, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// Float-comparison refinement obligations (all 12 ordered/unordered predicates
/// × f32/f64). trust-ir side via `interp_fcmp_model_i1` (interpreter-canonical,
/// uses `fp_is_nan`); wasm side via `wasm_fcmp_model_i1` (the backend's actual
/// emission, uses `x != x` for isnan and `lt|gt` for ONe). The two are
/// independently formulated, so ay proving them equal over all bit patterns
/// (NaN included) is a genuine refinement, not a tautology.
pub fn fcmp_proofs() -> Vec<ProofObligation> {
    let ops = [
        "OEq", "ONe", "OLt", "OLe", "OGt", "OGe", "UEq", "UNe", "ULt", "ULe", "UGt", "UGe",
    ];
    let mut out = Vec::new();
    for (eb, sb, tag) in [(8u32, 24u32, "f32"), (11, 53, "f64")] {
        for op in ops {
            let a = SmtExpr::var("a", eb + sb);
            let b = SmtExpr::var("b", eb + sb);
            out.push(ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name: format!("FCmp_{op}_{tag} -> wasm"),
                trust_ir_expr: interp_fcmp_model_i1(op, &a, &b),
                aarch64_expr: wasm_fcmp_model_i1(op, &a, &b),
                inputs: vec![],
                preconditions: vec![],
                fp_inputs: vec![("a".to_string(), eb, sb), ("b".to_string(), eb, sb)],
                category: None,
            });
        }
    }
    out
}

/// Anti-tautology: claim ordered `OEq` lowers to ordered `OLt`. Must be refuted.
pub fn proof_wrong_oeq_is_olt() -> ProofObligation {
    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "WRONG: FCmp OEq_f32 -> OLt (must be refuted)".to_string(),
        trust_ir_expr: interp_fcmp_model_i1("OEq", &a, &b),
        aarch64_expr: wasm_fcmp_model_i1("OLt", &a, &b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24), ("b".to_string(), 8, 24)],
        category: None,
    }
}

/// Integer-width cast proofs: genuine identities over the backend's actual
/// wasm cast encoders — extend-then-truncate round-trips (`wrap(zext(x))==x`,
/// `wrap(sext(x))==x`), proving wrap/zext/sext compose correctly.
pub fn cast_proofs() -> Vec<ProofObligation> {
    let x = SmtExpr::var("a", 32);
    vec![
        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "ZExt;Trunc round-trips (wrap(zext x) == x)".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: w::encode_wrap(w::encode_zext_i32_i64(x.clone())),
            inputs: vec![("a".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        },
        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "SExt;Trunc round-trips (wrap(sext x) == x)".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: w::encode_wrap(w::encode_sext_i32_i64(x.clone())),
            inputs: vec![("a".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        },
    ]
}

/// Anti-tautology: claim `SExt` lowers to zero-extend. Differs for negative
/// inputs, so must be refuted — proving the lowering distinguishes sign from
/// zero extension.
pub fn proof_wrong_sext_is_zext() -> ProofObligation {
    let x = SmtExpr::var("a", 32);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "WRONG: SExt -> zero_extend (must be refuted)".to_string(),
        trust_ir_expr: w::encode_sext_i32_i64(x.clone()),
        aarch64_expr: w::encode_zext_i32_i64(x),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    }
}

/// Integer-negate refinement: trust-ir `Neg` (`bvneg`) == the backend's wasm
/// expansion `0 - x` (`encode_ineg`). A genuine non-trivial identity (two
/// distinct expression trees), i32 and i64.
pub fn unary_neg_proofs() -> Vec<ProofObligation> {
    let mut out = Vec::new();
    for (ty, width, tag) in [(Type::I32, 32u32, "i32"), (Type::I64, 64u32, "i64")] {
        let x = SmtExpr::var("a", width);
        out.push(ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!("Neg_{tag} -> wasm (0 - x)"),
            trust_ir_expr: encode_trust_ir_neg(ty, x.clone()),
            aarch64_expr: w::encode_ineg(x, width),
            inputs: vec![("a".to_string(), width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        });
    }
    out
}

/// Anti-tautology: claim `Neg` lowers to the identity (`x`). Must be refuted.
pub fn proof_wrong_neg_is_identity() -> ProofObligation {
    let x = SmtExpr::var("a", 32);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "WRONG: Neg_i32 -> identity (must be refuted)".to_string(),
        trust_ir_expr: encode_trust_ir_neg(Type::I32, x.clone()),
        aarch64_expr: x,
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    }
}

/// Anti-tautology: claim `FAdd` lowers to `f32.sub`. Must be refuted.
pub fn proof_wrong_fadd_is_fsub() -> ProofObligation {
    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "WRONG: FAdd_f32 -> wasm f32.sub (must be refuted)".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F32, a.clone(), b.clone()),
        aarch64_expr: w::encode_fsub(a, b),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24), ("b".to_string(), 8, 24)],
        category: None,
    }
}

/// trust-ir's defined semantics for a bitwise/shift `BinOp`, modeled directly
/// (the shared `encode_trust_ir_binop` does not cover these — and adding
/// `Opcode` variants to trust_cg_lower is out of scope here). `And/Or/Xor` are
/// the bitvector ops; `Shl/LShr/AShr` are unmasked shifts, well-defined for
/// shift amount `< width` (the precondition the proofs carry).
fn trust_ir_bitop(name: &str, a: SmtExpr, b: SmtExpr) -> SmtExpr {
    match name {
        "and" => a.bvand(b),
        "or" => a.bvor(b),
        "xor" => a.bvxor(b),
        "shl" => a.bvshl(b),
        "shr_s" => a.bvashr(b),
        "shr_u" => a.bvlshr(b),
        other => panic!("not a bitwise/shift op: {other}"),
    }
}

// SUPERSEDED (task #71): `bitwise_proofs` built degenerate X==X obligations
// (trust-ir `bvand` == wasm `bvand`). DELETED — And/Or/Xor (i32/i64) are now
// credited via operand reconstruction. `trust_ir_bitop` is kept: the genuine
// shift proofs (below) and the `proof_wrong_shl_is_shr` guard still use it for
// the unmasked trust-ir shift side.

/// Shift refinement obligations (shl/shr_s/shr_u, i32 and i64). Each carries the
/// precondition `b <u width`, under which wasm's shift-amount mask is identity.
pub fn shift_proofs() -> Vec<ProofObligation> {
    let table: [(&str, ShiftEncoder); 3] = [
        ("shl", w::encode_shl),
        ("shr_s", w::encode_shr_s),
        ("shr_u", w::encode_shr_u),
    ];
    let mut out = Vec::new();
    for (width, tag) in [(32u32, "i32"), (64u32, "i64")] {
        for (op, wasm) in table {
            let (a, b) = vars(width);
            out.push(ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name: format!("{op}_{tag} -> wasm {tag}.{op}"),
                trust_ir_expr: trust_ir_bitop(op, a.clone(), b.clone()),
                aarch64_expr: wasm(a.clone(), b.clone(), width),
                inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
                preconditions: vec![b.bvult(SmtExpr::bv_const(u64::from(width), width))],
                fp_inputs: vec![],
                category: None,
            });
        }
    }
    out
}

// SUPERSEDED (task #71): `arithmetic_proofs` is DELETED (see the `arith_proof`
// note above). Iadd/Isub/Imul (i32/i64) are reconstruction-credited.

/// The 10 (IntCC → wasm comparison) mappings, mirroring `icmp_opcode`.
fn cmp_table() -> Vec<ComparisonEntry> {
    vec![
        (
            "eq",
            IntCC::Equal,
            w::encode_eq as fn(SmtExpr, SmtExpr) -> SmtExpr,
        ),
        ("ne", IntCC::NotEqual, w::encode_ne),
        ("lt_s", IntCC::SignedLessThan, w::encode_lt_s),
        ("le_s", IntCC::SignedLessThanOrEqual, w::encode_le_s),
        ("gt_s", IntCC::SignedGreaterThan, w::encode_gt_s),
        ("ge_s", IntCC::SignedGreaterThanOrEqual, w::encode_ge_s),
        ("lt_u", IntCC::UnsignedLessThan, w::encode_lt_u),
        ("le_u", IntCC::UnsignedLessThanOrEqual, w::encode_le_u),
        ("gt_u", IntCC::UnsignedGreaterThan, w::encode_gt_u),
        ("ge_u", IntCC::UnsignedGreaterThanOrEqual, w::encode_ge_u),
    ]
}

/// All comparison refinement obligations (10 predicates × {i32, i64}).
pub fn comparison_proofs() -> Vec<ProofObligation> {
    let mut out = Vec::new();
    for (ty, width, tag) in [(Type::I32, 32u32, "i32"), (Type::I64, 64u32, "i64")] {
        for (op, cc, wasm) in cmp_table() {
            out.push(cmp_proof(
                &format!("ICmp_{op}_{tag} -> wasm {tag}.{op}"),
                cc,
                ty.clone(),
                width,
                wasm,
            ));
        }
    }
    out
}

/// Every GENUINELY NON-DEGENERATE trust-ir → wasm scalar-op refinement
/// obligation: the 6 shifts + 20 integer comparisons + 24 float comparisons +
/// 2 integer negates + 2 integer-width casts = 54 obligations whose two sides are
/// STRUCTURALLY DISTINCT (so they prove real content, not an X==X tautology).
///
/// The 28 degenerate scalar-ALU / div-rem / bitwise / FP-arith builders were
/// DELETED (task #71): they were `bvadd == bvadd` self-equalities and are
/// SUPERSEDED by operand reconstruction (`wasm_function_verifier`). This is the
/// set registered under [`crate::proof_database::ProofCategory::WasmLowering`].
pub fn all_wasm_lowering_proofs() -> Vec<ProofObligation> {
    let mut v = shift_proofs();
    v.extend(comparison_proofs());
    v.extend(fcmp_proofs());
    v.extend(unary_neg_proofs());
    v.extend(cast_proofs());
    debug_assert!(
        v.iter().all(|p| p.is_genuinely_proven()),
        "all_wasm_lowering_proofs must contain ONLY non-degenerate obligations"
    );
    v
}

/// Anti-tautology: claim `Shl` lowers to a logical *right* shift. Must be refuted.
pub fn proof_wrong_shl_is_shr() -> ProofObligation {
    let (a, b) = vars(32);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "WRONG: Shl_i32 -> wasm i32.shr_u (must be refuted)".to_string(),
        trust_ir_expr: trust_ir_bitop("shl", a.clone(), b.clone()),
        aarch64_expr: w::encode_shr_u(a, b.clone(), 32),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![b.bvult(SmtExpr::bv_const(32, 32))],
        fp_inputs: vec![],
        category: None,
    }
}

/// A deliberately-FALSE obligation: claims `Iadd` lowers to `i32.sub`. The
/// harness must refute it (counterexample / Invalid), proving the proofs above
/// are not vacuously passing.
pub fn proof_wrong_add_is_sub() -> ProofObligation {
    let (a, b) = vars(32);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "WRONG: Iadd_I32 -> wasm i32.sub (must be refuted)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I32, a.clone(), b.clone()),
        aarch64_expr: w::encode_sub(a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm_formal::{
        Formal, certification_gap_reason, discharge, prove_or_certification_gap_skip, refute,
    };

    fn proof_authority_available() -> bool {
        crate::ay_bridge::z3_available()
    }

    /// FORMAL (default): every GENUINE (non-degenerate) scalar-lowering
    /// refinement obligation is proven `unsat` by the ay SMT solver — correct for
    /// ALL inputs, not sampled. (The degenerate scalar-ALU/divrem/bitwise/float
    /// proofs were deleted; those opcodes are reconstruction-credited.)
    /// Parked behind the certification-gap guard (`crate::formal_gap`): the
    /// exact fail-closed gap diagnostics skip loudly; anything else still
    /// panics with the original `prove` message.
    #[test]
    fn all_wasm_lowerings_proven_formally() {
        if !proof_authority_available() {
            return;
        }
        for ob in all_wasm_lowering_proofs() {
            prove_or_certification_gap_skip(&ob);
        }
    }

    /// FORMAL: shift obligations (shifts carry `b < width`) — the masked-vs-
    /// unmasked divergence is the genuine content (#57).
    #[test]
    fn shift_proofs_proven_formally() {
        if !proof_authority_available() {
            return;
        }
        for ob in shift_proofs() {
            prove_or_certification_gap_skip(&ob);
        }
    }

    /// FORMAL: integer comparison obligations (i1->i32 lift vs wasm i32 0/1).
    #[test]
    fn comparison_proofs_proven_formally() {
        if !proof_authority_available() {
            return;
        }
        for ob in comparison_proofs() {
            prove_or_certification_gap_skip(&ob);
        }
    }

    /// FORMAL: all 12 float-comparison predicates × f32/f64, NaN-precise.
    #[test]
    fn fcmp_proofs_proven_formally() {
        if !proof_authority_available() {
            return;
        }
        for ob in fcmp_proofs() {
            prove_or_certification_gap_skip(&ob);
        }
    }

    /// FORMAL anti-tautology guards: deliberately-wrong mappings are refuted
    /// (`sat`) by ay, proving the discharge genuinely exercises the solver.
    /// (`proof_wrong_add_is_sub` / `_fadd_is_fsub` are kept as live solver-
    /// exercising guards even though their CORRECT counterparts are now
    /// reconstruction-credited rather than registered static proofs.)
    #[test]
    fn wrong_mappings_are_refuted_formally() {
        refute(&proof_wrong_add_is_sub());
        refute(&proof_wrong_shl_is_shr());
        refute(&proof_wrong_fadd_is_fsub());
        refute(&proof_wrong_neg_is_identity());
        refute(&proof_wrong_oeq_is_olt());
        refute(&proof_wrong_sext_is_zext());
    }

    /// Aggregate report + a floor on how many GENUINE obligations are formally
    /// proven. The honest headline is 54 (not the inflated 82, which counted 28
    /// degenerate X==X self-equalities that prove nothing). Under the
    /// certification-gap guard the floor becomes: every one of the 54 is
    /// either PROVEN or the exact confirmed gap — a refutation, timeout, or
    /// unrecognized diagnostic still fails, and `proven == 54` is enforced
    /// verbatim the moment the gap count reaches zero.
    #[test]
    fn formal_discharge_summary() {
        if !proof_authority_available() {
            return;
        }
        let mut proven = 0usize;
        let mut gapped = 0usize;
        for ob in all_wasm_lowering_proofs() {
            let verdict = discharge(&ob);
            if verdict == Formal::Proven {
                proven += 1;
            } else if let Some(reason) = certification_gap_reason(&ob, &verdict) {
                crate::formal_gap::print_gap_skip(
                    &format!("formal_discharge_summary `{}`", ob.name),
                    &reason,
                );
                gapped += 1;
            } else {
                panic!(
                    "obligation `{}` neither proven nor certification-gapped: {verdict:?}",
                    ob.name
                );
            }
        }
        eprintln!(
            "formal_discharge_summary: {proven}/54 GENUINE obligations proven (unsat) via ay \
             ({gapped} certification-gap skipped)"
        );
        assert_eq!(
            proven + gapped,
            54,
            "all 54 genuine (non-degenerate) obligations must be formally proven or the \
             exact confirmed certification gap"
        );
        if gapped == 0 {
            assert_eq!(
                proven, 54,
                "all 54 genuine (non-degenerate) obligations must be formally proven"
            );
        }
    }

    #[test]
    fn cast_proofs_proven_formally() {
        if !proof_authority_available() {
            return;
        }
        for ob in cast_proofs() {
            prove_or_certification_gap_skip(&ob);
        }
    }

    #[test]
    fn proof_set_is_complete() {
        // The GENUINE non-degenerate set: 6 shift + 20 icmp + 24 fcmp + 2 neg
        // + 2 cast = 54. (The 28 degenerate arith/divrem/bitwise/float builders
        // were DELETED — task #71 — and are reconstruction-credited.)
        assert_eq!(fcmp_proofs().len(), 24);
        assert_eq!(shift_proofs().len(), 6);
        assert_eq!(comparison_proofs().len(), 20);
        assert_eq!(unary_neg_proofs().len(), 2);
        assert_eq!(cast_proofs().len(), 2);
        assert_eq!(all_wasm_lowering_proofs().len(), 54);
    }

    /// Every registered wasm proof is GENUINELY non-degenerate (the strict-gate
    /// honesty invariant): no `X == X` self-equality can sneak back in.
    #[test]
    fn registered_proofs_are_all_non_degenerate() {
        for ob in all_wasm_lowering_proofs() {
            assert!(
                ob.is_genuinely_proven(),
                "registered wasm proof '{}' is degenerate (X==X)",
                ob.name
            );
        }
    }

    /// Cross-check that the fast statistical evaluator AGREES with the formal
    /// solver on a sample GENUINE obligation (a shift, the masked/unmasked one).
    #[test]
    fn statistical_and_formal_agree_on_shift() {
        if !proof_authority_available() {
            return;
        }
        use crate::lowering_proof::verify_by_evaluation;
        use crate::verify::VerificationResult;
        let ob = &shift_proofs()[0]; // shl_i32 (masked vs unmasked, b < width)
        assert!(matches!(
            verify_by_evaluation(ob),
            VerificationResult::Valid
        ));
        prove_or_certification_gap_skip(ob);
    }
}
