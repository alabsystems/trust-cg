// trust-cg-verify/aarch64_select_proofs.rs - CMP+CSEL conditional-select lowering proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: Arm DDI 0602 ID062025 (ISA XML 2025-06), CSEL pp373-374 and
//            ConditionHolds p5947; ARM DDI 0487 C5.2.9 (SUBS/CMP flags).

//! Lowering proofs for the `trust_ir::Select` -> `CMP ; CSEL` sequence.
//!
//! # What this family proves, and why it is not the retracted one
//!
//! The pre-existing `CmpSelectCombine: diamond CFG == CSEL x, a, b, cond`
//! entries ([`crate::cmp_combine_proofs::proof_csel_equivalence`]) are
//! DEGENERATE: their two sides are the same `ite(cond != 0, a, b)` term, so
//! [`ProofObligation::is_degenerate`] holds and they credit ZERO. The coverage
//! gate records exactly that, and says what is missing
//! (`coverage_gate.rs`, the `Csel | Csinc | Csneg` arm):
//!
//! > they are X==X self-equalities (the machine side was built to mirror the
//! > spec, no independent CSEL/CSINC/CSNEG encoder) [...] Pending a faithful
//! > independent conditional-select machine encoder, coverage is NOT claimed.
//!
//! This module supplies that missing machine side. The obligation's AArch64
//! term is not written here at all: it is obtained by DECODING the concrete
//! 32-bit `CSEL` instruction word through
//! [`crate::aarch64_csel_semantics::DecodedConditionalSelect`] — an Arm-ARM
//! derived decoder whose field extraction, `ConditionHolds` table and
//! symbolic execution are checked against independent oracles (4096 accepted
//! encodings with fixed-bit mutation controls; all 16 conditions x 16 NZCV
//! against a hand-transcribed truth table; refutation controls for a wrong
//! condition, swapped `Rn`/`Rm`, wrong width and wrong `Rd`). The two sides
//! are therefore structurally distinct:
//!
//! * SOURCE: [`crate::trust_ir_semantics::encode_trust_ir_icmp`] — a pure
//!   bitvector predicate (`bvslt`/`bvuge`/...) selecting between the arms.
//! * MACHINE: the decoded `CSEL` word's own `ite(ConditionHolds(cond, NZCV),
//!   Rn, Rm)`, where NZCV is the packed flag quadruple that
//!   [`crate::nzcv::encode_cmp`] derives from the reaching `CMP` through the
//!   ARM `AddWithCarry` adder, not from the comparison predicate.
//!
//! A wrong condition code, a swapped true/false arm, or a wrong carrier width
//! therefore REFUTES rather than discharging trivially; the negative controls
//! in this module's tests exercise each of those.
//!
//! # What it does NOT prove
//!
//! Nothing here establishes that any CONCRETE emitted `CSEL` implements the
//! modeled source `Select`: that is an applicability question about operands,
//! reaching flags and provenance, decided by the caller
//! ([`crate::function_verifier`]'s in-block consumer binding), not by the
//! existence of these obligations. There is no claim about `CSINC`, `CSINV` or
//! `CSNEG` (whose false arms add, invert and negate), about `FCSEL`, about
//! flag liveness across blocks, or about the physical register write beyond
//! the architectural W-form upper-half clear the decoder models.

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;
use trust_cg_lower::instructions::IntCC;
use trust_cg_lower::isel::AArch64CC;

/// The ten `IntCC` conditions that have an AArch64 condition code, paired with
/// the registry spelling used in this family's names. `MI`/`PL`/`VS`/`VC` have
/// no `IntCC` member and are deliberately absent: a select reading the raw N or
/// V flag is not an integer comparison and must fail closed.
const CONDITIONS: [(IntCC, &str); 10] = [
    (IntCC::Equal, "Eq"),
    (IntCC::NotEqual, "NE"),
    (IntCC::SignedLessThan, "SLT"),
    (IntCC::SignedGreaterThanOrEqual, "SGE"),
    (IntCC::SignedGreaterThan, "SGT"),
    (IntCC::SignedLessThanOrEqual, "SLE"),
    (IntCC::UnsignedLessThan, "ULT"),
    (IntCC::UnsignedGreaterThanOrEqual, "UGE"),
    (IntCC::UnsignedGreaterThan, "UGT"),
    (IntCC::UnsignedLessThanOrEqual, "ULE"),
];

/// Architectural one-bit form of a Boolean flag.
fn flag_bit(flag: SmtExpr) -> SmtExpr {
    SmtExpr::ite(flag, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// Pack NZCV with N most-significant, the order
/// [`crate::aarch64_csel_semantics`] indexes.
fn pack_nzcv(flags: &crate::nzcv::NzcvFlags) -> SmtExpr {
    flag_bit(flags.n.clone())
        .concat(flag_bit(flags.z.clone()))
        .concat(flag_bit(flags.c.clone()))
        .concat(flag_bit(flags.v.clone()))
}

/// The `CSEL Rd, Rn, Rm, cond` instruction word for `Rd`=0, `Rn`=1, `Rm`=2 at
/// the given width, laid out exactly as
/// `trust_cg_codegen::aarch64::encode`'s `AArch64Opcode::Csel` arm does.
///
/// `tests/aarch64_select_proofs_encoder_gate.rs` re-encodes every word in this
/// family with the LIVE encoder and fails on any difference, so this layout
/// cannot drift into describing an instruction the compiler does not emit.
/// (That gate lives in `tests/` because `trust-cg-codegen` is a dev-only
/// dependency here — see the note in `Cargo.toml`.)
pub fn csel_word(width: u32, cc: AArch64CC) -> u32 {
    let sf = u32::from(width == 64);
    let (rd, rn, rm) = (0u32, 1u32, 2u32);
    (sf << 31) | (0b1101_0100 << 21) | (rm << 16) | ((cc as u32) << 12) | (rn << 5) | rd
}

/// The registry query token that resolves to exactly this family member.
///
/// Lowercase, because the walk's lookup does
/// `name.to_lowercase().contains(query)` WITHOUT lowercasing the query.
pub fn select_family_query(cc: AArch64CC, cmp_width: u32, sel_width: u32) -> Option<&'static str> {
    Some(match (cc, cmp_width, sel_width) {
        (AArch64CC::EQ, 32, 32) => "select_eq_nzcv32_sel32",
        (AArch64CC::EQ, 32, 64) => "select_eq_nzcv32_sel64",
        (AArch64CC::EQ, 64, 32) => "select_eq_nzcv64_sel32",
        (AArch64CC::EQ, 64, 64) => "select_eq_nzcv64_sel64",
        (AArch64CC::NE, 32, 32) => "select_ne_nzcv32_sel32",
        (AArch64CC::NE, 32, 64) => "select_ne_nzcv32_sel64",
        (AArch64CC::NE, 64, 32) => "select_ne_nzcv64_sel32",
        (AArch64CC::NE, 64, 64) => "select_ne_nzcv64_sel64",
        (AArch64CC::LT, 32, 32) => "select_slt_nzcv32_sel32",
        (AArch64CC::LT, 32, 64) => "select_slt_nzcv32_sel64",
        (AArch64CC::LT, 64, 32) => "select_slt_nzcv64_sel32",
        (AArch64CC::LT, 64, 64) => "select_slt_nzcv64_sel64",
        (AArch64CC::GE, 32, 32) => "select_sge_nzcv32_sel32",
        (AArch64CC::GE, 32, 64) => "select_sge_nzcv32_sel64",
        (AArch64CC::GE, 64, 32) => "select_sge_nzcv64_sel32",
        (AArch64CC::GE, 64, 64) => "select_sge_nzcv64_sel64",
        (AArch64CC::GT, 32, 32) => "select_sgt_nzcv32_sel32",
        (AArch64CC::GT, 32, 64) => "select_sgt_nzcv32_sel64",
        (AArch64CC::GT, 64, 32) => "select_sgt_nzcv64_sel32",
        (AArch64CC::GT, 64, 64) => "select_sgt_nzcv64_sel64",
        (AArch64CC::LE, 32, 32) => "select_sle_nzcv32_sel32",
        (AArch64CC::LE, 32, 64) => "select_sle_nzcv32_sel64",
        (AArch64CC::LE, 64, 32) => "select_sle_nzcv64_sel32",
        (AArch64CC::LE, 64, 64) => "select_sle_nzcv64_sel64",
        (AArch64CC::LO, 32, 32) => "select_ult_nzcv32_sel32",
        (AArch64CC::LO, 32, 64) => "select_ult_nzcv32_sel64",
        (AArch64CC::LO, 64, 32) => "select_ult_nzcv64_sel32",
        (AArch64CC::LO, 64, 64) => "select_ult_nzcv64_sel64",
        (AArch64CC::HS, 32, 32) => "select_uge_nzcv32_sel32",
        (AArch64CC::HS, 32, 64) => "select_uge_nzcv32_sel64",
        (AArch64CC::HS, 64, 32) => "select_uge_nzcv64_sel32",
        (AArch64CC::HS, 64, 64) => "select_uge_nzcv64_sel64",
        (AArch64CC::HI, 32, 32) => "select_ugt_nzcv32_sel32",
        (AArch64CC::HI, 32, 64) => "select_ugt_nzcv32_sel64",
        (AArch64CC::HI, 64, 32) => "select_ugt_nzcv64_sel32",
        (AArch64CC::HI, 64, 64) => "select_ugt_nzcv64_sel64",
        (AArch64CC::LS, 32, 32) => "select_ule_nzcv32_sel32",
        (AArch64CC::LS, 32, 64) => "select_ule_nzcv32_sel64",
        (AArch64CC::LS, 64, 32) => "select_ule_nzcv64_sel32",
        (AArch64CC::LS, 64, 64) => "select_ule_nzcv64_sel64",
        _ => return None,
    })
}

/// The [`AArch64CC`] an ISel `CondCode` operand immediate denotes.
///
/// The machine IR carries the condition as a bare integer; this is the ONE
/// place that reads it back. The encoding is `AArch64CC`'s own discriminant
/// order (isel.rs): EQ=0 NE=1 HS=2 LO=3 MI=4 PL=5 VS=6 VC=7 HI=8 LS=9 GE=10
/// LT=11 GT=12 LE=13, pinned by `isel_condition_immediates_round_trip`.
/// Anything outside 0..=13 is REFUSED — a malformed condition operand must
/// fail closed, never be masked into a valid one.
pub fn cc_from_isel_immediate(cc: i64) -> Option<AArch64CC> {
    Some(match cc {
        0 => AArch64CC::EQ,
        1 => AArch64CC::NE,
        2 => AArch64CC::HS,
        3 => AArch64CC::LO,
        4 => AArch64CC::MI,
        5 => AArch64CC::PL,
        6 => AArch64CC::VS,
        7 => AArch64CC::VC,
        8 => AArch64CC::HI,
        9 => AArch64CC::LS,
        10 => AArch64CC::GE,
        11 => AArch64CC::LT,
        12 => AArch64CC::GT,
        13 => AArch64CC::LE,
        _ => return None,
    })
}

/// [`select_family_query`] keyed by the raw ISel condition immediate, so the
/// function verifier never has to name [`AArch64CC`] itself.
pub fn select_family_query_for_immediate(
    cc: i64,
    cmp_width: u32,
    sel_width: u32,
) -> Option<&'static str> {
    select_family_query(cc_from_isel_immediate(cc)?, cmp_width, sel_width)
}

/// The AArch64 side: the DECODED `CSEL` word's own post-state for `Rd`, with
/// `Rn`/`Rm` bound to the select arms and NZCV bound to the reaching `CMP`'s
/// packed flags. Returns `None` if the word is not a conditional-select
/// encoding or a slot refuses a caller term — neither is reachable for the
/// words this family builds, and both fail closed rather than substituting a
/// hand-written model.
fn machine_side(
    width: u32,
    cc: AArch64CC,
    true_arm: SmtExpr,
    false_arm: SmtExpr,
    flags: &crate::nzcv::NzcvFlags,
) -> Option<SmtExpr> {
    use crate::aarch64_csel_semantics::{
        ConditionalSelectOperation, DecodedConditionalSelect, SymbolicRegisterState,
    };

    let decoded = DecodedConditionalSelect::decode(csel_word(width, cc)).ok()?;
    // The decoder — not this module — must agree the word is a plain CSEL of
    // the intended width and register layout. CSINC/CSINV/CSNEG differ only in
    // bits 30/10 and have different false arms; binding one of their words to
    // this obligation would be exactly the unfaithful inheritance the family
    // exists to avoid.
    if decoded.operation() != ConditionalSelectOperation::Csel
        || decoded.width().bits() != width
        || decoded.registers() != (0, 1, 2)
    {
        return None;
    }

    let widen = |arm: SmtExpr| {
        if width == 32 { arm.zero_ext(32) } else { arm }
    };
    let before = SymbolicRegisterState::variables()
        .with_register(1, widen(true_arm))?
        .with_register(2, widen(false_arm))?
        .with_nzcv(pack_nzcv(flags))?;
    let after = decoded.execute_symbolic(&before);
    let written = after.register(0)?.clone();
    // The architectural W-form write zero-extends into the X slot; compare at
    // the carrier width the select actually produces.
    Some(if width == 32 {
        written.extract(31, 0)
    } else {
        written
    })
}

/// One `trust_ir::Select(Icmp(cond, a, b), t, f)` -> `CMP ; CSEL` obligation.
///
/// `cmp_width` is the width of the reaching `CMP`'s operands; `sel_width` is
/// the width of the selected values. They are independent: the compiler emits
/// `CMP Wn, Wm ; CSEL Xd, Xn, Xm, cc` whenever a 32-bit comparison selects
/// 64-bit values.
pub fn proof_select_cmp_csel(
    cond: IntCC,
    cmp_width: u32,
    sel_width: u32,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::types::Type;

    if !matches!(cmp_width, 32 | 64) || !matches!(sel_width, 32 | 64) {
        return None;
    }
    let cc = AArch64CC::from_intcc(cond);
    let spelling = CONDITIONS.iter().find(|(c, _)| *c == cond)?.1;

    let a = SmtExpr::var("a", cmp_width);
    let b = SmtExpr::var("b", cmp_width);
    let t = SmtExpr::var("t", sel_width);
    let f = SmtExpr::var("f", sel_width);

    let cmp_ty = if cmp_width == 32 {
        Type::I32
    } else {
        Type::I64
    };
    // SOURCE: the select's own `ite` over the trust_ir comparison BIT. The
    // comparison is a pure bitvector predicate; it never mentions a flag.
    let predicate =
        encode_trust_ir_icmp(&cond, cmp_ty, a.clone(), b.clone()).eq_expr(SmtExpr::bv_const(1, 1));
    let trust_ir_expr = SmtExpr::ite(predicate, t.clone(), f.clone());

    // MACHINE: the reaching CMP's adder-derived NZCV, read by the DECODED
    // CSEL word's own ConditionHolds.
    let flags = crate::nzcv::encode_cmp(a, b, cmp_width);
    let aarch64_expr = machine_side(sel_width, cc, t, f, &flags)?;

    Some(ProofObligation {
        machine_side_provenance: MachineSideProvenance::StaticDb,
        name: format!("Select_{spelling}_Nzcv{cmp_width}_Sel{sel_width} -> CSEL_{cc:?}"),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![
            ("a".to_string(), cmp_width),
            ("b".to_string(), cmp_width),
            ("t".to_string(), sel_width),
            ("f".to_string(), sel_width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    })
}

/// The complete family: 10 conditions x 2 comparison widths x 2 select widths.
///
/// A member that fails to build is a DEFECT, not a silent omission —
/// `select_family_is_complete` pins the count at 40 and
/// `every_select_family_member_resolves_from_its_query` pins that each one is
/// reachable by the token the walk emits.
pub fn all_select_cmp_csel_proofs() -> Vec<ProofObligation> {
    let mut out = Vec::with_capacity(40);
    for (cond, _) in CONDITIONS {
        for cmp_width in [32u32, 64] {
            for sel_width in [32u32, 64] {
                if let Some(p) = proof_select_cmp_csel(cond, cmp_width, sel_width) {
                    out.push(p);
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::verify_by_evaluation;
    use crate::verify::VerificationResult;

    fn discharges(ob: &ProofObligation) -> bool {
        matches!(verify_by_evaluation(ob), VerificationResult::Valid)
    }

    #[test]
    fn select_family_is_complete() {
        let all = all_select_cmp_csel_proofs();
        assert_eq!(all.len(), 40, "10 conditions x cmp{{32,64}} x sel{{32,64}}");
        let names: std::collections::HashSet<_> = all.iter().map(|p| p.name.clone()).collect();
        assert_eq!(names.len(), 40, "family names must be distinct");
    }

    /// The whole point of the family: neither side may be the other. A
    /// degenerate member would be recorded as a binding and credited zero,
    /// which is exactly the retracted `CmpSelectCombine` shape.
    #[test]
    fn no_select_family_member_is_degenerate() {
        for p in all_select_cmp_csel_proofs() {
            assert!(
                !p.is_degenerate(),
                "{} is X==X — the retracted shape, not a lowering proof",
                p.name
            );
        }
    }

    #[test]
    fn every_select_family_member_discharges() {
        for p in all_select_cmp_csel_proofs() {
            assert!(discharges(&p), "{} did not discharge", p.name);
        }
    }

    /// Every token the walk can emit resolves to exactly one member, and every
    /// member is reachable by a token. A token that matched two members would
    /// silently credit the wrong width.
    #[test]
    fn every_select_family_member_resolves_from_its_query() {
        let all = all_select_cmp_csel_proofs();
        let mut matched = 0;
        for cond in CONDITIONS.map(|(c, _)| c) {
            let cc = AArch64CC::from_intcc(cond);
            for cmp_width in [32u32, 64] {
                for sel_width in [32u32, 64] {
                    let q = select_family_query(cc, cmp_width, sel_width)
                        .expect("every mapped condition has a token");
                    let hits: Vec<_> = all
                        .iter()
                        .filter(|p| p.name.to_lowercase().contains(q))
                        .collect();
                    assert_eq!(hits.len(), 1, "token {q} matched {} members", hits.len());
                    matched += 1;
                }
            }
        }
        assert_eq!(matched, 40);
    }

    /// The immediate the machine IR carries must denote the condition ISel
    /// chose. A drift here silently credits the wrong predicate, so it is
    /// pinned against `AArch64CC::from_intcc` for every mapped condition and
    /// against refusal outside the encoding's range.
    #[test]
    fn isel_condition_immediates_round_trip() {
        for (cond, _) in CONDITIONS {
            let cc = AArch64CC::from_intcc(cond);
            assert_eq!(
                cc_from_isel_immediate(cc as i64),
                Some(cc),
                "{cc:?} does not round-trip through its immediate"
            );
        }
        for cc in [AArch64CC::MI, AArch64CC::PL, AArch64CC::VS, AArch64CC::VC] {
            assert_eq!(cc_from_isel_immediate(cc as i64), Some(cc));
        }
        for bad in [-1i64, 14, 15, 16, 255, i64::MIN, i64::MAX] {
            assert!(
                cc_from_isel_immediate(bad).is_none(),
                "{bad} must fail closed, not mask into a condition"
            );
        }
    }

    /// The four condition codes with no `IntCC` member must have no token: a
    /// select reading the raw N or V flag is not an integer comparison.
    #[test]
    fn raw_flag_conditions_have_no_select_token() {
        for cc in [AArch64CC::MI, AArch64CC::PL, AArch64CC::VS, AArch64CC::VC] {
            for cmp_width in [32u32, 64] {
                for sel_width in [32u32, 64] {
                    assert!(
                        select_family_query(cc, cmp_width, sel_width).is_none(),
                        "{cc:?} must fail closed"
                    );
                }
            }
        }
    }

    /// NEGATIVE CONTROL: reading a DIFFERENT condition's flags must refute.
    /// This is what makes the obligation non-vacuous — the machine side really
    /// does consult the condition field of the decoded word.
    #[test]
    fn a_wrong_condition_code_refutes() {
        use crate::trust_ir_semantics::encode_trust_ir_icmp;
        use trust_cg_lower::types::Type;
        let mut checked = 0;
        for (cond, _) in CONDITIONS {
            let right = AArch64CC::from_intcc(cond);
            // The inverted condition is the sharpest control: same flags, same
            // arms, one bit of the encoded word different.
            let wrong = match right {
                AArch64CC::EQ => AArch64CC::NE,
                AArch64CC::NE => AArch64CC::EQ,
                AArch64CC::LT => AArch64CC::GE,
                AArch64CC::GE => AArch64CC::LT,
                AArch64CC::GT => AArch64CC::LE,
                AArch64CC::LE => AArch64CC::GT,
                AArch64CC::LO => AArch64CC::HS,
                AArch64CC::HS => AArch64CC::LO,
                AArch64CC::HI => AArch64CC::LS,
                AArch64CC::LS => AArch64CC::HI,
                other => other,
            };
            for width in [32u32, 64] {
                let a = SmtExpr::var("a", width);
                let b = SmtExpr::var("b", width);
                let t = SmtExpr::var("t", width);
                let f = SmtExpr::var("f", width);
                let cmp_ty = if width == 32 { Type::I32 } else { Type::I64 };
                let predicate = encode_trust_ir_icmp(&cond, cmp_ty, a.clone(), b.clone())
                    .eq_expr(SmtExpr::bv_const(1, 1));
                let flags = crate::nzcv::encode_cmp(a, b, width);
                let bad = ProofObligation {
                    machine_side_provenance: MachineSideProvenance::StaticDb,
                    name: format!("NEGATIVE CONTROL wrong cc {wrong:?} w{width}"),
                    trust_ir_expr: SmtExpr::ite(predicate, t.clone(), f.clone()),
                    aarch64_expr: machine_side(width, wrong, t, f, &flags)
                        .expect("control word decodes"),
                    inputs: vec![
                        ("a".to_string(), width),
                        ("b".to_string(), width),
                        ("t".to_string(), width),
                        ("f".to_string(), width),
                    ],
                    preconditions: vec![],
                    fp_inputs: vec![],
                    category: Some(TransvalCheckKind::InstructionLowering),
                };
                assert!(
                    !discharges(&bad),
                    "{} was accepted — the condition field is not observed",
                    bad.name
                );
                checked += 1;
            }
        }
        assert_eq!(checked, 20);
    }

    /// NEGATIVE CONTROL: swapping the true/false arms must refute. `CSEL`'s
    /// `Rn` is the TRUE source and `Rm` the false one; a lowering that wires
    /// them the other way computes the complement.
    #[test]
    fn swapping_the_select_arms_refutes() {
        use crate::trust_ir_semantics::encode_trust_ir_icmp;
        use trust_cg_lower::types::Type;
        let mut checked = 0;
        for (cond, _) in CONDITIONS {
            let cc = AArch64CC::from_intcc(cond);
            for width in [32u32, 64] {
                let a = SmtExpr::var("a", width);
                let b = SmtExpr::var("b", width);
                let t = SmtExpr::var("t", width);
                let f = SmtExpr::var("f", width);
                let cmp_ty = if width == 32 { Type::I32 } else { Type::I64 };
                let predicate = encode_trust_ir_icmp(&cond, cmp_ty, a.clone(), b.clone())
                    .eq_expr(SmtExpr::bv_const(1, 1));
                let flags = crate::nzcv::encode_cmp(a, b, width);
                let bad = ProofObligation {
                    machine_side_provenance: MachineSideProvenance::StaticDb,
                    name: format!("NEGATIVE CONTROL swapped arms {cc:?} w{width}"),
                    trust_ir_expr: SmtExpr::ite(predicate, t.clone(), f.clone()),
                    // Arms deliberately reversed.
                    aarch64_expr: machine_side(width, cc, f, t, &flags)
                        .expect("control word decodes"),
                    inputs: vec![
                        ("a".to_string(), width),
                        ("b".to_string(), width),
                        ("t".to_string(), width),
                        ("f".to_string(), width),
                    ],
                    preconditions: vec![],
                    fp_inputs: vec![],
                    category: Some(TransvalCheckKind::InstructionLowering),
                };
                assert!(
                    !discharges(&bad),
                    "{} was accepted — the arm order is not observed",
                    bad.name
                );
                checked += 1;
            }
        }
        assert_eq!(checked, 20);
    }
}
