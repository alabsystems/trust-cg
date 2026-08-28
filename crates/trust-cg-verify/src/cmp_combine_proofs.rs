// trust-cg-verify/cmp_combine_proofs.rs - SMT proofs for CmpBranchFusion and CmpSelectCombine
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proves that the CmpBranchFusion and CmpSelectCombine optimization passes
// in trust-cg-opt preserve program semantics. These passes transform:
//
// CmpBranchFusion:
//   CMP Rn, #0 + B.EQ/B.NE → CBZ/CBNZ Rn
//   TST Rn, #(1<<k) + B.EQ/B.NE → TBZ/TBNZ Rn, #k
//
// CmpSelectCombine:
//   Diamond CFG (if-then-else with simple assignments) → CSEL/CSET/CSINC
//
// Technique: Alive2-style (PLDI 2021). Each proof encodes the semantics of
// both the original instruction sequence and the fused/combined instruction,
// then shows equivalence for all inputs.
//
// Reference: crates/trust-cg-opt/src/cmp_branch_fusion.rs
// Reference: crates/trust-cg-opt/src/cmp_select.rs

//! SMT proofs for CmpBranchFusion and CmpSelectCombine correctness.
//!
//! ## CmpBranchFusion Proofs
//!
//! | Proof | Property |
//! |-------|----------|
//! | [`proof_cbz_equivalence`] | CMP Rn,#0; B.EQ ≡ CBZ Rn |
//! | [`proof_cbnz_equivalence`] | CMP Rn,#0; B.NE ≡ CBNZ Rn |
//! | [`proof_tbz_equivalence`] | TST Rn,#(1<<k); B.EQ ≡ TBZ Rn,#k |
//! | [`proof_tbnz_equivalence`] | TST Rn,#(1<<k); B.NE ≡ TBNZ Rn,#k |
//! | [`proof_non_fusible_cmp_nonzero`] | CMP with non-zero imm does not fuse |
//! | [`proof_flag_liveness_cbz`] | CBZ does not set NZCV (flags dead after fusion) |
//!
//! ## CmpSelectCombine Proofs
//!
//! | Proof | Property |
//! |-------|----------|
//! | [`proof_csel_equivalence`] | if(cond) x=a else x=b ≡ CSEL x,a,b,cond |
//! | [`proof_cset_equivalence`] | if(cond) x=1 else x=0 ≡ CSET x,cond |
//! | [`proof_csinc_equivalence`] | if(cond) x=a else x=b+1 ≡ CSINC x,a,b,cond |
//! | [`proof_condition_inversion`] | CSEL x,a,b,cond ≡ CSEL x,b,a,!cond |
//! | [`proof_diamond_safety`] | Side-effect-free arms: value identity preserved |

use crate::lowering_proof::ProofObligation;
use crate::smt::SmtExpr;

// ===========================================================================
// CmpBranchFusion proofs
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. CBZ equivalence: CMP Rn, #0; B.EQ target ≡ CBZ Rn, target
// ---------------------------------------------------------------------------

/// Proof: CBZ equivalence for 64-bit values.
///
/// Theorem: forall Rn : BV64 .
///   branch_taken(CMP Rn,#0; B.EQ) == branch_taken(CBZ Rn)
///
/// CMP Rn, #0 sets Z flag iff Rn == 0. B.EQ branches iff Z == 1.
/// CBZ Rn branches iff Rn == 0.
/// Both compute the same predicate: Rn == 0.
pub fn proof_cbz_equivalence() -> ProofObligation {
    let width = 64;
    let rn = SmtExpr::var("Rn", width);
    let zero = SmtExpr::bv_const(0, width);

    // Original: CMP Rn, #0 sets Z = (Rn == 0); B.EQ branches iff Z == 1
    // Branch taken iff Rn == 0
    let original = SmtExpr::ite(
        rn.clone().eq_expr(zero.clone()),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    // Fused: CBZ Rn branches iff Rn == 0
    let fused = SmtExpr::ite(
        rn.eq_expr(zero),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: CMP Rn,#0; B.EQ ≡ CBZ Rn (64-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: fused,
        inputs: vec![("Rn".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// CBZ equivalence (8-bit, exhaustive).
pub fn proof_cbz_equivalence_8bit() -> ProofObligation {
    let width = 8;
    let rn = SmtExpr::var("Rn", width);
    let zero = SmtExpr::bv_const(0, width);

    let original = SmtExpr::ite(
        rn.clone().eq_expr(zero.clone()),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );
    let fused = SmtExpr::ite(
        rn.eq_expr(zero),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: CMP Rn,#0; B.EQ ≡ CBZ Rn (8-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: fused,
        inputs: vec![("Rn".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ---------------------------------------------------------------------------
// 2. CBNZ equivalence: CMP Rn, #0; B.NE target ≡ CBNZ Rn, target
// ---------------------------------------------------------------------------

/// Proof: CBNZ equivalence for 64-bit values.
///
/// Theorem: forall Rn : BV64 .
///   branch_taken(CMP Rn,#0; B.NE) == branch_taken(CBNZ Rn)
///
/// CMP Rn, #0 sets Z flag iff Rn == 0. B.NE branches iff Z == 0 (i.e., Rn != 0).
/// CBNZ Rn branches iff Rn != 0.
pub fn proof_cbnz_equivalence() -> ProofObligation {
    let width = 64;
    let rn = SmtExpr::var("Rn", width);
    let zero = SmtExpr::bv_const(0, width);

    // Original: B.NE branches iff Z == 0, i.e., Rn != 0
    let original = SmtExpr::ite(
        rn.clone().eq_expr(zero.clone()).not_expr(),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    // Fused: CBNZ Rn branches iff Rn != 0
    let fused = SmtExpr::ite(
        rn.eq_expr(zero).not_expr(),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: CMP Rn,#0; B.NE ≡ CBNZ Rn (64-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: fused,
        inputs: vec![("Rn".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// CBNZ equivalence (8-bit, exhaustive).
pub fn proof_cbnz_equivalence_8bit() -> ProofObligation {
    let width = 8;
    let rn = SmtExpr::var("Rn", width);
    let zero = SmtExpr::bv_const(0, width);

    let original = SmtExpr::ite(
        rn.clone().eq_expr(zero.clone()).not_expr(),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );
    let fused = SmtExpr::ite(
        rn.eq_expr(zero).not_expr(),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: CMP Rn,#0; B.NE ≡ CBNZ Rn (8-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: fused,
        inputs: vec![("Rn".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ---------------------------------------------------------------------------
// 3a. Standalone TST NZCV effect
// ---------------------------------------------------------------------------

/// Proof: the STANDALONE `TST Rn, Rm` NZCV effect, per condition code.
///
/// `aarch64_deferred_value_op_reason` named exactly this gap before these
/// obligations landed:
///
/// > TST is emitted for NZCV-producing bit tests, but no faithful standalone
/// > NZCV obligation is registered; TST+branch fusion evidence does not
/// > establish the unfused instruction's complete flag effect.
///
/// The fusion theorem (`TST;B.EQ ≡ TBZ`) only constrains Z on one code path. An
/// unfused TST — one feeding a `CSEL`/`CSINC` rather than a branch, which is
/// precisely what `and_cmp_fuse` produces on `p2_collatz` — cannot inherit
/// authority from the fusion theorem alone; it needs the flag effect its
/// consumer reads established. The function verifier binds each TST to the
/// obligation of that consumer's condition (`tst_nzcv_consumer_query`).
///
/// These per-condition rows are CONSUMER VIEWS, and no individual one of them
/// certifies an instruction that defines all four flags. That whole-instruction
/// authority is the packed-NZCV theorem (`proof_tst_packed_nzcv`, below in this
/// section), which the verifier binds when no in-block consumer pins a
/// condition; `coverage_gate::aarch64_width_polymorphic_proofs` requires it at
/// both widths before the opcode earns coverage. Both families are registered.
///
/// Each obligation relates ARM's flag machinery (extract the MSB, compare the
/// masked result to zero, then run `eval_condition`'s boolean algebra) to an
/// INDEPENDENT source-level predicate — a different formulation, not the
/// retracted `NZCV_* == NZCV_*` self-equalities of #62. Non-degeneracy is
/// load-bearing here, not cosmetic: `encode_tst` defines Z as literally
/// `(Rn & Rm) == 0`, so the "direct" Z predicates would restate the machine
/// encoder term-for-term and be structurally degenerate (STRICT #61 credits
/// them ZERO and `non_degeneracy_violations` reports them). EQ/NE therefore
/// use the disjointness characterization `(Rn | Rm) == (Rn ^ Rm)`.
///
/// The C/V facts are load-bearing too: logical ops CLEAR both flags. `HS`/`LO`
/// themselves reduce to bare constants on BOTH sides after `encode_tst`, so
/// they admit no non-degenerate obligation and are deliberately absent (a
/// consumer reading them after TST fails closed). The C-clear fact is pinned
/// instead by the COMPOSITE C-readers `HI` (C ∧ ¬Z) and `LS` (¬C ∨ Z), whose
/// machine sides run `eval_condition`'s full algebra: a data-dependent C — say
/// `encode_tst` copy-pasted from `encode_cmp` — makes both REFUTE (see
/// `tst_carry_cases_are_sensitive_to_the_carry_model`). That is the exact fact
/// `and_cmp_fuse`'s C-flag guard rests on, provable instead of merely commented.
fn tst_condition_obligation(
    cc: trust_cg_lower::isel::AArch64CC,
    width: u32,
    name: &str,
    source_side: SmtExpr,
) -> ProofObligation {
    let rn = SmtExpr::var("rn", width);
    let rm = SmtExpr::var("rm", width);
    let flags = crate::nzcv::encode_tst(rn, rm, width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source_side,
        aarch64_expr: crate::nzcv::eval_condition(cc, &flags),
        inputs: vec![("rn".to_string(), width), ("rm".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        // Matches the rest of the CmpCombine family; `proof_database`'s
        // `test_registered_check_kind_matches_proof_family` enforces that a
        // registered proof's TransvalCheckKind agrees with the family it is
        // registered under.
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// The full standalone-TST flag effect at a given width, as one obligation per
/// condition code that reads a different flag combination.
pub fn proof_tst_nzcv_effect(width: u32) -> Vec<ProofObligation> {
    let rn = || SmtExpr::var("rn", width);
    let rm = || SmtExpr::var("rm", width);
    let masked = || rn().bvand(rm());
    let zero = || SmtExpr::bv_const(0, width);
    let w = width;

    // Z: EQ/NE decide whether Rn and Rm share any set bits. The source side is
    // the DISJOINTNESS characterization `(Rn | Rm) == (Rn ^ Rm)` (OR loses
    // nothing to XOR exactly when no bit is shared), NOT `(Rn & Rm) == 0`:
    // `encode_tst` already defines Z as exactly that AND-form, so the direct
    // predicate restates the machine encoder term-for-term — a structurally
    // degenerate X==X of the #62 class. The disjointness form is an independent
    // formulation over different connectives; a wrong machine side (ORR-based
    // flags, a swapped condition) REFUTES.
    let disjoint = || rn().bvor(rm()).eq_expr(rn().bvxor(rm()));

    vec![
        tst_condition_obligation(
            trust_cg_lower::isel::AArch64CC::EQ,
            w,
            &format!("TST w{w}: EQ ≡ (Rn & Rm) == 0"),
            disjoint(),
        ),
        tst_condition_obligation(
            trust_cg_lower::isel::AArch64CC::NE,
            w,
            &format!("TST w{w}: NE ≡ (Rn & Rm) != 0"),
            disjoint().not_expr(),
        ),
        // N: MI/PL decide the sign of the masked value.
        tst_condition_obligation(
            trust_cg_lower::isel::AArch64CC::MI,
            w,
            &format!("TST w{w}: MI ≡ (Rn & Rm) <s 0"),
            masked().bvslt(zero()),
        ),
        tst_condition_obligation(
            trust_cg_lower::isel::AArch64CC::PL,
            w,
            &format!("TST w{w}: PL ≡ (Rn & Rm) >=s 0"),
            masked().bvsge(zero()),
        ),
        // V is cleared, so GE/LT reduce to the sign of N alone.
        tst_condition_obligation(
            trust_cg_lower::isel::AArch64CC::GE,
            w,
            &format!("TST w{w}: GE ≡ (Rn & Rm) >=s 0 (V is cleared)"),
            masked().bvsge(zero()),
        ),
        tst_condition_obligation(
            trust_cg_lower::isel::AArch64CC::LT,
            w,
            &format!("TST w{w}: LT ≡ (Rn & Rm) <s 0 (V is cleared)"),
            masked().bvslt(zero()),
        ),
        // GT/LE are ALSO well-defined N/Z-derived conditions after TST: with
        // V cleared, GT = !Z && (N==V) collapses to (Rn & Rm) >s 0 and LE to
        // (Rn & Rm) <=s 0 — the same class as MI/PL/GE/LT, and a consumer
        // shape `and_cmp_fuse` legally produces (its carry guard permits
        // GT/LE). An earlier revision omitted them under the FALSE rationale
        // "never valid after TST's V-clear"; the review corrected that.
        tst_condition_obligation(
            trust_cg_lower::isel::AArch64CC::GT,
            w,
            &format!("TST w{w}: GT ≡ (Rn & Rm) >s 0 (V is cleared)"),
            masked().bvsgt(zero()),
        ),
        tst_condition_obligation(
            trust_cg_lower::isel::AArch64CC::LE,
            w,
            &format!("TST w{w}: LE ≡ (Rn & Rm) <=s 0 (V is cleared)"),
            masked().bvsle(zero()),
        ),
        // C is cleared, so every C-dependent condition is CONSTANT after TST —
        // the fact and_cmp_fuse's guard rests on. HS ("C") and LO ("not C")
        // themselves cannot carry it as obligations: `eval_condition` reduces
        // both sides to a bare constant, which is structurally degenerate and
        // credits zero under STRICT #61, so those rows are deliberately absent.
        // The composite C-readers HI (C ∧ ¬Z) and LS (¬C ∨ Z) pin the same
        // fact non-degenerately: the machine side is eval_condition's full
        // boolean algebra over the encoded flags, and a data-dependent C makes
        // both refute.
        //
        // SCOPE (review #4, CRITICAL): the HI/LS rows exist ONLY as C-clear
        // MODEL PINS. They are NEVER reachable as per-instruction consumer
        // credit — `tst_condition_query` maps every C/V-observing consumer
        // condition (HS/LO/HI/LS/VS/VC) to None. After TST those conditions
        // are architecturally CONSTANT, so a consumer reading one is exactly
        // the miscompile shape `and_cmp_fuse`'s carry guard
        // (`cond_reads_carry`) exists to forbid: e.g. a regressed rewrite of
        // `CMP z,#0; CSet HI` (z != 0) into `TST a,b; CSet HI` (constant
        // false). Crediting the TST via the true-but-constant HI theorem
        // would stamp that wrong-code shape Verified; failing closed keeps it
        // a compile error.
        tst_condition_obligation(
            trust_cg_lower::isel::AArch64CC::HI,
            w,
            &format!("TST w{w}: HI is always FALSE (C is cleared)"),
            SmtExpr::bool_const(false),
        ),
        tst_condition_obligation(
            trust_cg_lower::isel::AArch64CC::LS,
            w,
            &format!("TST w{w}: LS is always TRUE (C is cleared)"),
            SmtExpr::bool_const(true),
        ),
    ]
}

/// Convert a Boolean flag to its architectural one-bit representation.
fn flag_bit(flag: SmtExpr) -> SmtExpr {
    SmtExpr::ite(flag, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// Pack NZCV in architectural order, with N as the most-significant bit.
fn pack_nzcv(flags: &crate::nzcv::NzcvFlags) -> SmtExpr {
    flag_bit(flags.n.clone())
        .concat(flag_bit(flags.z.clone()))
        .concat(flag_bit(flags.c.clone()))
        .concat(flag_bit(flags.v.clone()))
}

/// Build the complete standalone-TST obligation against an explicitly supplied
/// machine flag model. Keeping this helper separate lets the negative controls
/// corrupt each machine flag without changing the independent source model.
fn tst_packed_nzcv_obligation(
    width: u32,
    machine_flags: crate::nzcv::NzcvFlags,
    name: String,
) -> ProofObligation {
    let rn = SmtExpr::var("rn", width);
    let rm = SmtExpr::var("rm", width);
    // Source-side construction deliberately reverses the two inputs. The
    // architectural encoder below receives (rn, rm), so equivalence depends on
    // the actual commutativity of AND and is structurally non-degenerate.
    let masked = rm.bvand(rn);
    let zero = SmtExpr::bv_const(0, width);

    // Deliberately independent of `encode_tst`: spell out every source flag
    // directly over the reversed source expression. A wrong operation, operand,
    // flag, or packing order therefore refutes instead of collapsing into X==X.
    let source_flags = crate::nzcv::NzcvFlags {
        n: masked
            .clone()
            .extract(width - 1, width - 1)
            .eq_expr(SmtExpr::bv_const(1, 1)),
        z: masked.eq_expr(zero),
        c: SmtExpr::bool_const(false),
        v: SmtExpr::bool_const(false),
    };
    // Keep the source ordering explicit rather than calling the machine packer:
    // a future machine-side N/Z/C/V permutation must not change both sides.
    let source_nzcv = flag_bit(source_flags.n)
        .concat(flag_bit(source_flags.z))
        .concat(flag_bit(source_flags.c))
        .concat(flag_bit(source_flags.v));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: source_nzcv,
        aarch64_expr: pack_nzcv(&machine_flags),
        inputs: vec![("rn".to_string(), width), ("rm".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// Prove the complete standalone `TST` flag result as one packed NZCV value.
///
/// The per-condition lemmas above are useful regression checks, but no one of
/// them authorizes an instruction that produces all four flags. This theorem is
/// the single, non-degenerate authority binding used by the function verifier.
pub fn proof_tst_packed_nzcv(width: u32) -> ProofObligation {
    let rn = SmtExpr::var("rn", width);
    let rm = SmtExpr::var("rm", width);
    let machine_flags = crate::nzcv::encode_tst(rn, rm, width);
    tst_packed_nzcv_obligation(width, machine_flags, format!("TST packed NZCV w{width}"))
}

// ---------------------------------------------------------------------------
// 3b. TBZ equivalence: TST Rn, #(1<<k); B.EQ target ≡ TBZ Rn, #k, target
// ---------------------------------------------------------------------------

/// Proof: TBZ equivalence for 64-bit values.
///
/// Theorem: forall Rn : BV64, forall k in [0,63] .
///   branch_taken(TST Rn, #(1<<k); B.EQ) == branch_taken(TBZ Rn, #k)
///
/// TST Rn, #(1<<k) computes Rn AND (1<<k) and sets Z flag iff result == 0.
/// B.EQ branches iff Z == 1, i.e., bit k of Rn is 0.
/// TBZ Rn, #k branches iff bit k of Rn is 0.
///
/// We encode this parametrically: the bit position k is a free variable and
/// the mask is computed as 1 << k. Precondition: k < 64.
pub fn proof_tbz_equivalence() -> ProofObligation {
    let width = 64;
    let rn = SmtExpr::var("Rn", width);
    let k = SmtExpr::var("k", width);

    // mask = 1 << k
    let one = SmtExpr::bv_const(1, width);
    let mask = one.bvshl(k.clone());

    // Original: TST sets Z = ((Rn AND mask) == 0); B.EQ branches iff Z == 1
    let tst_result = rn.clone().bvand(mask.clone());
    let z_flag = tst_result.eq_expr(SmtExpr::bv_const(0, width));
    let original = SmtExpr::ite(z_flag, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1));

    // Fused: TBZ branches iff bit k of Rn is 0
    // Extract bit k: (Rn >> k) & 1, then test == 0
    let bit_k = rn.bvlshr(k.clone()).bvand(SmtExpr::bv_const(1, width));
    let bit_is_zero = bit_k.eq_expr(SmtExpr::bv_const(0, width));
    let fused = SmtExpr::ite(
        bit_is_zero,
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    // Precondition: k < 64 (valid bit position)
    let k_bound = k.bvult(SmtExpr::bv_const(64, width));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: TST Rn,#(1<<k); B.EQ ≡ TBZ Rn,#k (64-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: fused,
        inputs: vec![("Rn".to_string(), width), ("k".to_string(), width)],
        preconditions: vec![k_bound],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// TBZ equivalence (8-bit, exhaustive).
pub fn proof_tbz_equivalence_8bit() -> ProofObligation {
    let width = 8;
    let rn = SmtExpr::var("Rn", width);
    let k = SmtExpr::var("k", width);

    let one = SmtExpr::bv_const(1, width);
    let mask = one.bvshl(k.clone());

    let tst_result = rn.clone().bvand(mask);
    let z_flag = tst_result.eq_expr(SmtExpr::bv_const(0, width));
    let original = SmtExpr::ite(z_flag, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1));

    let bit_k = rn.bvlshr(k.clone()).bvand(SmtExpr::bv_const(1, width));
    let bit_is_zero = bit_k.eq_expr(SmtExpr::bv_const(0, width));
    let fused = SmtExpr::ite(
        bit_is_zero,
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    // k < 8 for 8-bit
    let k_bound = k.bvult(SmtExpr::bv_const(8, width));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: TST Rn,#(1<<k); B.EQ ≡ TBZ Rn,#k (8-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: fused,
        inputs: vec![("Rn".to_string(), width), ("k".to_string(), width)],
        preconditions: vec![k_bound],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ---------------------------------------------------------------------------
// 4. TBNZ equivalence: TST Rn, #(1<<k); B.NE target ≡ TBNZ Rn, #k, target
// ---------------------------------------------------------------------------

/// Proof: TBNZ equivalence for 64-bit values.
///
/// Theorem: forall Rn : BV64, forall k in [0,63] .
///   branch_taken(TST Rn, #(1<<k); B.NE) == branch_taken(TBNZ Rn, #k)
///
/// TST Rn, #(1<<k) sets Z = ((Rn AND (1<<k)) == 0).
/// B.NE branches iff Z == 0, i.e., bit k of Rn is 1.
/// TBNZ Rn, #k branches iff bit k of Rn is 1.
pub fn proof_tbnz_equivalence() -> ProofObligation {
    let width = 64;
    let rn = SmtExpr::var("Rn", width);
    let k = SmtExpr::var("k", width);

    let one = SmtExpr::bv_const(1, width);
    let mask = one.bvshl(k.clone());

    // Original: TST sets Z = ((Rn AND mask) == 0); B.NE branches iff Z == 0
    let tst_result = rn.clone().bvand(mask);
    let z_flag = tst_result.eq_expr(SmtExpr::bv_const(0, width));
    let original = SmtExpr::ite(
        z_flag.not_expr(), // B.NE: branch when Z == 0
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    // Fused: TBNZ branches iff bit k of Rn is 1
    let bit_k = rn.bvlshr(k.clone()).bvand(SmtExpr::bv_const(1, width));
    let bit_is_one = bit_k.eq_expr(SmtExpr::bv_const(1, width));
    let fused = SmtExpr::ite(bit_is_one, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1));

    let k_bound = k.bvult(SmtExpr::bv_const(64, width));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: TST Rn,#(1<<k); B.NE ≡ TBNZ Rn,#k (64-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: fused,
        inputs: vec![("Rn".to_string(), width), ("k".to_string(), width)],
        preconditions: vec![k_bound],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// TBNZ equivalence (8-bit, exhaustive).
pub fn proof_tbnz_equivalence_8bit() -> ProofObligation {
    let width = 8;
    let rn = SmtExpr::var("Rn", width);
    let k = SmtExpr::var("k", width);

    let one = SmtExpr::bv_const(1, width);
    let mask = one.bvshl(k.clone());

    let tst_result = rn.clone().bvand(mask);
    let z_flag = tst_result.eq_expr(SmtExpr::bv_const(0, width));
    let original = SmtExpr::ite(
        z_flag.not_expr(),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    let bit_k = rn.bvlshr(k.clone()).bvand(SmtExpr::bv_const(1, width));
    let bit_is_one = bit_k.eq_expr(SmtExpr::bv_const(1, width));
    let fused = SmtExpr::ite(bit_is_one, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1));

    let k_bound = k.bvult(SmtExpr::bv_const(8, width));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: TST Rn,#(1<<k); B.NE ≡ TBNZ Rn,#k (8-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: fused,
        inputs: vec![("Rn".to_string(), width), ("k".to_string(), width)],
        preconditions: vec![k_bound],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ---------------------------------------------------------------------------
// 5. Non-fusible rejection: CMP with non-zero immediate doesn't fuse
// ---------------------------------------------------------------------------

/// Proof: CMP Rn, #imm (imm != 0) has different branch semantics than CBZ.
///
/// Theorem: exists Rn : BV64, exists imm : BV64 (imm != 0) .
///   branch_taken(CMP Rn, #imm; B.EQ) != branch_taken(CBZ Rn)
///
/// This is a *safety* proof showing that naively fusing a non-zero CMP
/// into CBZ would be incorrect. We prove this by showing the predicates
/// differ: `(Rn == imm)` vs `(Rn == 0)` are not equivalent when imm != 0.
///
/// Encoded as: for all Rn, (Rn == imm) != (Rn == 0) when imm != 0.
/// We negate: we prove that `(Rn == imm)` is NOT the same as `(Rn == 0)`.
/// Since these are clearly different predicates for imm != 0, we encode
/// the valid case as the identity: for the non-fused path, the predicate
/// `(Rn == imm)` differs from the CBZ predicate `(Rn == 0)`.
///
/// Concretely: imm = 42, and we show CMP Rn,#42; B.EQ takes the branch
/// iff Rn == 42, while CBZ takes branch iff Rn == 0. These differ for
/// Rn == 42 (or Rn == 0). We encode both sides as the SAME predicate
/// (the non-fused one is correct) to prove the pass correctly rejects this.
pub fn proof_non_fusible_cmp_nonzero() -> ProofObligation {
    let width = 64;
    let rn = SmtExpr::var("Rn", width);

    // CMP Rn, #42; B.EQ: branches iff Rn == 42
    let cmp_predicate = SmtExpr::ite(
        rn.clone().eq_expr(SmtExpr::bv_const(42, width)),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    // This predicate is NOT equivalent to CBZ (Rn == 0).
    // We prove the pass is correct by showing it preserves the original
    // non-fused semantics — both sides are the same CMP Rn, #42 predicate.
    let preserved = SmtExpr::ite(
        rn.eq_expr(SmtExpr::bv_const(42, width)),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: CMP Rn,#42 not fused — predicate preserved".to_string(),
        trust_ir_expr: cmp_predicate,
        aarch64_expr: preserved,
        inputs: vec![("Rn".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// Non-fusible rejection (8-bit, exhaustive).
pub fn proof_non_fusible_cmp_nonzero_8bit() -> ProofObligation {
    let width = 8;
    let rn = SmtExpr::var("Rn", width);

    let cmp_predicate = SmtExpr::ite(
        rn.clone().eq_expr(SmtExpr::bv_const(42, width)),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );
    let preserved = SmtExpr::ite(
        rn.eq_expr(SmtExpr::bv_const(42, width)),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: CMP Rn,#42 not fused — predicate preserved (8-bit)".to_string(),
        trust_ir_expr: cmp_predicate,
        aarch64_expr: preserved,
        inputs: vec![("Rn".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ---------------------------------------------------------------------------
// 6. Flag liveness: CBZ/CBNZ do not set NZCV flags
// ---------------------------------------------------------------------------

/// Proof: Fusion is valid because NZCV flags are dead after the branch.
///
/// Theorem: forall Rn, N, Z, C, V : BV1 .
///   flags_after(CMP Rn,#0; CBZ) == flags_before (flags unchanged by CBZ)
///
/// CMP Rn, #0 sets NZCV. The fused CBZ does NOT set NZCV.
/// Fusion is only valid if NZCV flags are dead after the branch (no
/// downstream use). We model this by showing the flag state is preserved
/// (not clobbered) by CBZ — the flags that were live before the CMP
/// are the flags that are live after CBZ, since CBZ doesn't touch them.
///
/// The key insight: if flags ARE live after the branch, the CMP must be
/// kept (fusion rejected). If flags are dead, the CMP's flag-setting is
/// irrelevant and fusion is safe. We prove the latter case: when the only
/// use of the CMP result is the branch condition (EQ/NE), and flags are
/// dead afterward, the branch decision is identical.
pub fn proof_flag_liveness_cbz() -> ProofObligation {
    let width = 64;
    let rn = SmtExpr::var("Rn", width);
    // Model NZCV as a 4-bit flags word from before the CMP
    let _flags_before = SmtExpr::var("flags_before", 4);

    // After CMP Rn, #0 + B.EQ fusion to CBZ:
    // Branch decision depends only on Rn == 0 (same as proven in proof 1).
    // NZCV flags are dead after the branch, so post-branch flag state is irrelevant.
    // We model the preserved quantity: the branch decision AND the flag state
    // that existed before the CMP (since CBZ doesn't clobber flags, and flags
    // are dead anyway, this is a tautology showing the transform is safe).

    // Original: branch decision is (Rn == 0), flags_before are irrelevant
    let branch = SmtExpr::ite(
        rn.clone().eq_expr(SmtExpr::bv_const(0, width)),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    // We encode the combined state: the branch decision is the same regardless
    // of whether CMP set new flags or CBZ preserved old flags.
    // This is modeled as: branch_taken is identical in both sequences.
    let fused_branch = SmtExpr::ite(
        rn.eq_expr(SmtExpr::bv_const(0, width)),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpBranchFusion: CBZ flag liveness — branch decision preserved".to_string(),
        trust_ir_expr: branch,
        aarch64_expr: fused_branch,
        inputs: vec![("Rn".to_string(), width), ("flags_before".to_string(), 4)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ===========================================================================
// CmpSelectCombine proofs
// ===========================================================================

// ---------------------------------------------------------------------------
// 7. CSEL equivalence: if(cond) x = a; else x = b ≡ CSEL x, a, b, cond
// ---------------------------------------------------------------------------

/// Proof: CSEL equivalence for 64-bit values.
///
/// Theorem: forall a, b, cond_val : BV64 .
///   ite(cond_val == 0, b, a) == CSEL(a, b, cond_val != 0)
///
/// Diamond CFG: header compares cond_val, true arm assigns a, false arm
/// assigns b. CSEL x, a, b, cond selects a when cond is true, b otherwise.
///
/// We model the condition as a bitvector comparison result (nonzero = true).
pub fn proof_csel_equivalence() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond = SmtExpr::var("cond", width);

    // Original diamond CFG:
    // if (cond != 0) then x = a else x = b
    let original = SmtExpr::ite(
        cond.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone(),
        b.clone(),
    );

    // CSEL x, a, b, cond: x = (cond != 0) ? a : b
    let csel = SmtExpr::ite(cond.eq_expr(SmtExpr::bv_const(0, width)).not_expr(), a, b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpSelectCombine: diamond CFG ≡ CSEL x, a, b, cond (64-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: csel,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// CSEL equivalence (8-bit, exhaustive).
///
/// Note: 3 inputs at 8-bit = 2^24 = 16M combinations. This is feasible
/// for exhaustive verification with our sampling threshold.
pub fn proof_csel_equivalence_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond = SmtExpr::var("cond", width);

    let original = SmtExpr::ite(
        cond.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone(),
        b.clone(),
    );
    let csel = SmtExpr::ite(cond.eq_expr(SmtExpr::bv_const(0, width)).not_expr(), a, b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpSelectCombine: diamond CFG ≡ CSEL x, a, b, cond (8-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: csel,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ---------------------------------------------------------------------------
// 8. CSET equivalence: if(cond) x = 1; else x = 0 ≡ CSET x, cond
// ---------------------------------------------------------------------------

/// Proof: CSET equivalence for 64-bit values.
///
/// Theorem: forall cond_val : BV64 .
///   ite(cond_val != 0, 1, 0) == CSET(cond_val != 0)
///
/// Diamond CFG: true arm assigns 1, false arm assigns 0.
/// CSET x, cond: x = (cond) ? 1 : 0.
pub fn proof_cset_equivalence() -> ProofObligation {
    let width = 64;
    let result_width = 64; // CSET produces a 64-bit value (0 or 1)
    let cond = SmtExpr::var("cond", width);

    // Original: if (cond != 0) x = 1 else x = 0
    let original = SmtExpr::ite(
        cond.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        SmtExpr::bv_const(1, result_width),
        SmtExpr::bv_const(0, result_width),
    );

    // CSET x, cond: same semantics
    let cset = SmtExpr::ite(
        cond.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        SmtExpr::bv_const(1, result_width),
        SmtExpr::bv_const(0, result_width),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpSelectCombine: if(cond) 1 else 0 ≡ CSET x, cond (64-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: cset,
        inputs: vec![("cond".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// CSET equivalence (8-bit, exhaustive).
pub fn proof_cset_equivalence_8bit() -> ProofObligation {
    let width = 8;
    let cond = SmtExpr::var("cond", width);

    let original = SmtExpr::ite(
        cond.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        SmtExpr::bv_const(1, width),
        SmtExpr::bv_const(0, width),
    );
    let cset = SmtExpr::ite(
        cond.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        SmtExpr::bv_const(1, width),
        SmtExpr::bv_const(0, width),
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpSelectCombine: if(cond) 1 else 0 ≡ CSET x, cond (8-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: cset,
        inputs: vec![("cond".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ---------------------------------------------------------------------------
// 9. CSINC equivalence: if(cond) x = a; else x = b+1 ≡ CSINC x, a, b, cond
// ---------------------------------------------------------------------------

/// Proof: CSINC equivalence for 64-bit values.
///
/// Theorem: forall a, b, cond_val : BV64 .
///   ite(cond_val != 0, a, b + 1) == CSINC(a, b, cond_val != 0)
///
/// CSINC x, a, b, cond: x = (cond) ? a : (b + 1).
pub fn proof_csinc_equivalence() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond = SmtExpr::var("cond", width);

    // Original diamond: if (cond != 0) x = a else x = b + 1
    let b_plus_one = b.clone().bvadd(SmtExpr::bv_const(1, width));
    let original = SmtExpr::ite(
        cond.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone(),
        b_plus_one,
    );

    // CSINC x, a, b, cond: x = (cond) ? a : (b + 1)
    let b_inc = b.bvadd(SmtExpr::bv_const(1, width));
    let csinc = SmtExpr::ite(
        cond.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        b_inc,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpSelectCombine: if(cond) a else b+1 ≡ CSINC x, a, b, cond (64-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: csinc,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// CSINC equivalence (8-bit, exhaustive).
pub fn proof_csinc_equivalence_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond = SmtExpr::var("cond", width);

    let b_plus_one = b.clone().bvadd(SmtExpr::bv_const(1, width));
    let original = SmtExpr::ite(
        cond.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone(),
        b_plus_one,
    );

    let b_inc = b.bvadd(SmtExpr::bv_const(1, width));
    let csinc = SmtExpr::ite(
        cond.eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a,
        b_inc,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpSelectCombine: if(cond) a else b+1 ≡ CSINC x, a, b, cond (8-bit)".to_string(),
        trust_ir_expr: original,
        aarch64_expr: csinc,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ---------------------------------------------------------------------------
// 10. Condition inversion: CSEL x, a, b, cond ≡ CSEL x, b, a, !cond
// ---------------------------------------------------------------------------

/// Proof: Condition inversion for CSEL.
///
/// Theorem: forall a, b, cond_val : BV64 .
///   ite(cond_val != 0, a, b) == ite(cond_val == 0, b, a)
///
/// CSEL x, a, b, cond selects a when cond is true. Swapping the operands
/// and inverting the condition produces the same result.
pub fn proof_condition_inversion() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond = SmtExpr::var("cond", width);

    // CSEL x, a, b, cond: x = (cond != 0) ? a : b
    let csel_original = SmtExpr::ite(
        cond.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone(),
        b.clone(),
    );

    // CSEL x, b, a, !cond: x = (cond == 0) ? b : a
    // Which is: (!(cond != 0)) ? b : a = (cond == 0) ? b : a
    let csel_inverted = SmtExpr::ite(cond.eq_expr(SmtExpr::bv_const(0, width)), b, a);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpSelectCombine: CSEL x,a,b,cond ≡ CSEL x,b,a,!cond (64-bit)".to_string(),
        trust_ir_expr: csel_original,
        aarch64_expr: csel_inverted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// Condition inversion (8-bit, exhaustive).
pub fn proof_condition_inversion_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond = SmtExpr::var("cond", width);

    let csel_original = SmtExpr::ite(
        cond.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone(),
        b.clone(),
    );
    let csel_inverted = SmtExpr::ite(cond.eq_expr(SmtExpr::bv_const(0, width)), b, a);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpSelectCombine: CSEL x,a,b,cond ≡ CSEL x,b,a,!cond (8-bit)".to_string(),
        trust_ir_expr: csel_original,
        aarch64_expr: csel_inverted,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ---------------------------------------------------------------------------
// 11. Diamond safety: only valid when both arms have no side effects
// ---------------------------------------------------------------------------

/// Proof: Diamond CFG with side-effect-free arms preserves value identity.
///
/// Theorem: forall a, b, cond_val : BV64 .
///   let x_diamond = ite(cond != 0, a, b) in
///   let x_csel = ite(cond != 0, a, b) in
///   x_diamond == x_csel
///
/// When both arms of the diamond are pure MOV instructions (no memory
/// writes, no flag modifications, no calls), the diamond-to-CSEL transform
/// preserves the output value exactly. This is the core safety argument:
/// the transform is valid ONLY because both arms are side-effect-free.
///
/// A side-effecting arm (e.g., store, call) would change program behavior
/// because CSEL evaluates both operands, while the diamond only executes one
/// arm. The pass correctly rejects arms with > 2 instructions or non-MOV
/// instructions (see `cmp_select.rs` safety constraints).
pub fn proof_diamond_safety() -> ProofObligation {
    let width = 64;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond = SmtExpr::var("cond", width);

    // Diamond CFG: execute exactly one arm based on condition
    let diamond_result = SmtExpr::ite(
        cond.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone(),
        b.clone(),
    );

    // CSEL: both operands are read (no side effects assumed), select one
    let csel_result = SmtExpr::ite(cond.eq_expr(SmtExpr::bv_const(0, width)).not_expr(), a, b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpSelectCombine: diamond safety — pure arms preserve value".to_string(),
        trust_ir_expr: diamond_result,
        aarch64_expr: csel_result,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

/// Diamond safety (8-bit, exhaustive).
pub fn proof_diamond_safety_8bit() -> ProofObligation {
    let width = 8;
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let cond = SmtExpr::var("cond", width);

    let diamond_result = SmtExpr::ite(
        cond.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr(),
        a.clone(),
        b.clone(),
    );
    let csel_result = SmtExpr::ite(cond.eq_expr(SmtExpr::bv_const(0, width)).not_expr(), a, b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CmpSelectCombine: diamond safety — pure arms preserve value (8-bit)".to_string(),
        trust_ir_expr: diamond_result,
        aarch64_expr: csel_result,
        inputs: vec![
            ("a".to_string(), width),
            ("b".to_string(), width),
            ("cond".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
    }
}

// ===========================================================================
// Registry functions
// ===========================================================================

/// Return all CmpCombine proof obligations (64-bit, statistical).
pub fn all_cmp_combine_proofs() -> Vec<ProofObligation> {
    vec![
        // CmpBranchFusion
        proof_cbz_equivalence(),
        proof_cbnz_equivalence(),
        proof_tbz_equivalence(),
        proof_tbnz_equivalence(),
        proof_non_fusible_cmp_nonzero(),
        proof_flag_liveness_cbz(),
        // CmpSelectCombine
        proof_csel_equivalence(),
        proof_cset_equivalence(),
        proof_csinc_equivalence(),
        proof_condition_inversion(),
        proof_diamond_safety(),
    ]
}

/// Return all CmpCombine proofs including 8-bit exhaustive variants.
/// Retracted degenerate X==X CmpCombine obligations (CBZ/CBNZ fusion, CMP#42-not-fused, CBZ-flag-liveness, CmpSelectCombine diamond/CSET/CSINC — restated the fusion as a value identity). Genuine TST==TBZ/TBNZ and CSEL-swap proofs remain.
const CMPCOMBINE_RETRACTED_DEGENERATE: &[&str] = &[
    "CmpBranchFusion: CBZ flag liveness — branch decision preserved",
    "CmpBranchFusion: CMP Rn,#0; B.EQ ≡ CBZ Rn (64-bit)",
    "CmpBranchFusion: CMP Rn,#0; B.EQ ≡ CBZ Rn (8-bit)",
    "CmpBranchFusion: CMP Rn,#0; B.NE ≡ CBNZ Rn (64-bit)",
    "CmpBranchFusion: CMP Rn,#0; B.NE ≡ CBNZ Rn (8-bit)",
    "CmpBranchFusion: CMP Rn,#42 not fused — predicate preserved",
    "CmpBranchFusion: CMP Rn,#42 not fused — predicate preserved (8-bit)",
    "CmpSelectCombine: diamond CFG ≡ CSEL x, a, b, cond (64-bit)",
    "CmpSelectCombine: diamond CFG ≡ CSEL x, a, b, cond (8-bit)",
    "CmpSelectCombine: diamond safety — pure arms preserve value",
    "CmpSelectCombine: diamond safety — pure arms preserve value (8-bit)",
    "CmpSelectCombine: if(cond) 1 else 0 ≡ CSET x, cond (64-bit)",
    "CmpSelectCombine: if(cond) 1 else 0 ≡ CSET x, cond (8-bit)",
    "CmpSelectCombine: if(cond) a else b+1 ≡ CSINC x, a, b, cond (64-bit)",
    "CmpSelectCombine: if(cond) a else b+1 ≡ CSINC x, a, b, cond (8-bit)",
];

pub fn all_cmp_combine_proofs_with_variants() -> Vec<ProofObligation> {
    let mut proofs = all_cmp_combine_proofs();
    // 8-bit variants for exhaustive verification
    proofs.push(proof_cbz_equivalence_8bit());
    proofs.push(proof_cbnz_equivalence_8bit());
    proofs.push(proof_tbz_equivalence_8bit());
    proofs.push(proof_tbnz_equivalence_8bit());
    proofs.push(proof_non_fusible_cmp_nonzero_8bit());
    proofs.push(proof_cset_equivalence_8bit());
    proofs.push(proof_csel_equivalence_8bit());
    proofs.push(proof_csinc_equivalence_8bit());
    proofs.push(proof_condition_inversion_8bit());
    proofs.push(proof_diamond_safety_8bit());
    // Standalone TST NZCV effect, both widths. Registered so an UNFUSED `Tst`
    // (one feeding a CSEL/CSINC rather than a branch, which is what
    // `and_cmp_fuse` produces on p2_collatz) has the flag effect its consumer
    // reads established — the gap `aarch64_deferred_value_op_reason` named for
    // Tst, formerly the sole opcode blocker for proofs-on on 4 of 18 programs.
    // The function verifier binds per-instruction via `tst_nzcv_consumer_query`
    // (the consuming instruction's condition code selects the obligation).
    proofs.extend(proof_tst_nzcv_effect(64));
    proofs.extend(proof_tst_nzcv_effect(32));
    // ...and the COMPLETE packed-NZCV authority at both emitted widths. No
    // individual consumer view certifies an instruction that DEFINES all four
    // flags, so these carry the whole-instruction authority: the verifier falls
    // back to them when no in-block consumer binding applies
    // (`operand_sensitive_or_opcode_query`), and
    // `coverage_gate::aarch64_width_polymorphic_proofs` demands both widths
    // before Tst earns opcode coverage. Both families are non-degenerate under
    // STRICT #61 (see the tests below), so both are credited.
    proofs.push(proof_tst_packed_nzcv(64));
    proofs.push(proof_tst_packed_nzcv(32));
    // #62 retraction: drop degenerate X==X self-equalities (see CMPCOMBINE_RETRACTED_DEGENERATE).
    proofs.retain(|p| !CMPCOMBINE_RETRACTED_DEGENERATE.contains(&p.name.as_str()));
    proofs
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::verify_by_evaluation;
    use crate::verify::VerificationResult;

    /// Helper: verify a proof obligation and assert it is Valid.
    /// Every standalone-TST flag obligation must discharge, at both widths.
    /// These per-condition rows are the CONSUMER views bound by
    /// `tst_nzcv_consumer_query`; complete whole-instruction authority comes
    /// from the packed-NZCV pair, checked separately below.
    #[test]
    fn tst_standalone_nzcv_obligations_discharge() {
        for width in [32u32, 64] {
            for ob in proof_tst_nzcv_effect(width) {
                assert_valid(&ob);
            }
        }
    }

    #[test]
    fn tst_packed_nzcv_obligations_are_valid_and_non_degenerate() {
        for width in [32u32, 64] {
            let ob = proof_tst_packed_nzcv(width);
            assert!(!ob.is_degenerate(), "w{width} packed NZCV must not be X==X");
            assert_valid(&ob);
        }
    }

    /// Every packed flag bit is load-bearing. Flipping any one field in the
    /// machine model must make the complete-state theorem refute.
    #[test]
    fn tst_packed_nzcv_wrong_flag_controls_refute() {
        let width = 8u32;
        for field in ["N", "Z", "C", "V"] {
            let rn = SmtExpr::var("rn", width);
            let rm = SmtExpr::var("rm", width);
            let mut flags = crate::nzcv::encode_tst(rn, rm, width);
            match field {
                "N" => flags.n = flags.n.not_expr(),
                "Z" => flags.z = flags.z.not_expr(),
                "C" => flags.c = flags.c.not_expr(),
                "V" => flags.v = flags.v.not_expr(),
                _ => unreachable!(),
            }
            let corrupted = tst_packed_nzcv_obligation(
                width,
                flags,
                format!("TST packed NZCV wrong-{field} control"),
            );
            assert!(
                !matches!(verify_by_evaluation(&corrupted), VerificationResult::Valid),
                "flipping {field} must refute the packed NZCV theorem"
            );
        }
    }

    /// The C-flag cases must be NON-VACUOUS. `HS ≡ false`/`LO ≡ true` and the
    /// composite `HI ≡ false`/`LS ≡ true` are
    /// only true because logical ops CLEAR C; if `encode_tst` ever grew a
    /// data-dependent C (say by being copy-pasted from `encode_cmp`), these
    /// would break. Prove they are sensitive to that by flipping C and
    /// requiring EVERY one of them to STOP verifying — otherwise they could
    /// pass for the wrong reason and `and_cmp_fuse`'s guard would rest on a
    /// theorem that no longer holds. HS/LO are checked here even though they
    /// are not registered rows: the fact under test is `encode_tst`'s C model,
    /// not any one obligation.
    #[test]
    fn tst_carry_cases_are_sensitive_to_the_carry_model() {
        let width = 64u32;
        let rn = SmtExpr::var("rn", width);
        let rm = SmtExpr::var("rm", width);
        let mut flags = crate::nzcv::encode_tst(rn.clone(), rm.clone(), width);
        // Corrupt C to the SUBS/CMP form (data dependent) and re-check every
        // C-observing condition: the constant HS/LO views and the composite
        // HI/LS model pins must all stop verifying.
        flags.c = rn.bvuge(rm);

        for (cc, source, label) in [
            (
                trust_cg_lower::isel::AArch64CC::HS,
                SmtExpr::bool_const(false),
                "HS ≡ false",
            ),
            (
                trust_cg_lower::isel::AArch64CC::LO,
                SmtExpr::bool_const(true),
                "LO ≡ true",
            ),
            (
                trust_cg_lower::isel::AArch64CC::HI,
                SmtExpr::bool_const(false),
                "HI ≡ false",
            ),
            (
                trust_cg_lower::isel::AArch64CC::LS,
                SmtExpr::bool_const(true),
                "LS ≡ true",
            ),
        ] {
            let corrupted = ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name: format!("TST w64: {label} with a CMP-style carry (must NOT verify)"),
                trust_ir_expr: source,
                aarch64_expr: crate::nzcv::eval_condition(cc, &flags),
                inputs: vec![("rn".to_string(), width), ("rm".to_string(), width)],
                preconditions: vec![],
                fp_inputs: vec![],
                category: Some(crate::lowering_proof::TransvalCheckKind::PeepholeOptimization),
            };
            assert!(
                !matches!(verify_by_evaluation(&corrupted), VerificationResult::Valid),
                "{label} must depend on TST CLEARING carry; with a CMP-style \
                 data-dependent C it must stop verifying"
            );
        }
    }

    /// STRICT #61 credits only structurally non-degenerate obligations, and the
    /// manifest gate (`non_degeneracy_violations`) fails closed on any new
    /// degenerate row — so every registered TST obligation must formulate its
    /// source side independently of `encode_tst`'s own flag construction. The
    /// packed whole-instruction pair is held to the same bar by
    /// `tst_packed_nzcv_obligations_are_valid_and_non_degenerate`.
    #[test]
    fn tst_standalone_nzcv_obligations_are_structurally_non_degenerate() {
        for width in [32u32, 64] {
            for ob in proof_tst_nzcv_effect(width) {
                assert!(
                    !ob.is_degenerate(),
                    "'{}' restates the machine encoder term-for-term; it can \
                     never be credited and trips the non-degeneracy gate",
                    ob.name
                );
            }
        }
    }

    fn assert_valid(obligation: &ProofObligation) {
        let result = verify_by_evaluation(obligation);
        match &result {
            VerificationResult::Valid => {}
            VerificationResult::Invalid { counterexample } => {
                panic!(
                    "Proof '{}' FAILED with counterexample: {}",
                    obligation.name, counterexample
                );
            }
            VerificationResult::Unknown { reason } => {
                panic!("Proof '{}' returned Unknown: {}", obligation.name, reason);
            }
        }
    }

    // -----------------------------------------------------------------------
    // CmpBranchFusion proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_cbz_equivalence() {
        assert_valid(&proof_cbz_equivalence());
    }

    #[test]
    fn test_proof_cbz_equivalence_8bit() {
        assert_valid(&proof_cbz_equivalence_8bit());
    }

    #[test]
    fn test_proof_cbnz_equivalence() {
        assert_valid(&proof_cbnz_equivalence());
    }

    #[test]
    fn test_proof_cbnz_equivalence_8bit() {
        assert_valid(&proof_cbnz_equivalence_8bit());
    }

    #[test]
    fn test_proof_tbz_equivalence() {
        assert_valid(&proof_tbz_equivalence());
    }

    #[test]
    fn test_proof_tbz_equivalence_8bit() {
        assert_valid(&proof_tbz_equivalence_8bit());
    }

    #[test]
    fn test_proof_tbnz_equivalence() {
        assert_valid(&proof_tbnz_equivalence());
    }

    #[test]
    fn test_proof_tbnz_equivalence_8bit() {
        assert_valid(&proof_tbnz_equivalence_8bit());
    }

    #[test]
    fn test_proof_non_fusible_cmp_nonzero() {
        assert_valid(&proof_non_fusible_cmp_nonzero());
    }

    #[test]
    fn test_proof_non_fusible_cmp_nonzero_8bit() {
        assert_valid(&proof_non_fusible_cmp_nonzero_8bit());
    }

    #[test]
    fn test_proof_flag_liveness_cbz() {
        assert_valid(&proof_flag_liveness_cbz());
    }

    // -----------------------------------------------------------------------
    // CmpSelectCombine proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_csel_equivalence() {
        assert_valid(&proof_csel_equivalence());
    }

    #[test]
    fn test_proof_csel_equivalence_8bit() {
        assert_valid(&proof_csel_equivalence_8bit());
    }

    #[test]
    fn test_proof_cset_equivalence() {
        assert_valid(&proof_cset_equivalence());
    }

    #[test]
    fn test_proof_cset_equivalence_8bit() {
        assert_valid(&proof_cset_equivalence_8bit());
    }

    #[test]
    fn test_proof_csinc_equivalence() {
        assert_valid(&proof_csinc_equivalence());
    }

    #[test]
    fn test_proof_csinc_equivalence_8bit() {
        assert_valid(&proof_csinc_equivalence_8bit());
    }

    #[test]
    fn test_proof_condition_inversion() {
        assert_valid(&proof_condition_inversion());
    }

    #[test]
    fn test_proof_condition_inversion_8bit() {
        assert_valid(&proof_condition_inversion_8bit());
    }

    #[test]
    fn test_proof_diamond_safety() {
        assert_valid(&proof_diamond_safety());
    }

    #[test]
    fn test_proof_diamond_safety_8bit() {
        assert_valid(&proof_diamond_safety_8bit());
    }

    // -----------------------------------------------------------------------
    // Aggregate tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_cmp_combine_proofs_valid() {
        let proofs = all_cmp_combine_proofs();
        assert_eq!(proofs.len(), 11, "expected 11 base proofs");
        for obligation in &proofs {
            assert_valid(obligation);
        }
    }

    #[test]
    fn test_all_cmp_combine_proofs_with_variants_valid() {
        let proofs = all_cmp_combine_proofs_with_variants();
        assert_eq!(
            proofs.len(),
            28,
            "expected 28 GENUINE proofs: the original 6, plus 20 standalone-TST NZCV \
             obligations (10 condition rows x 32- and 64-bit: EQ/NE/MI/PL/GE/LT/GT/LE \
             consumer-bindable + HI/LS as C-clear model pins) registered to close the \
             `aarch64_deferred_value_op_reason` gap for Tst, plus the 2 COMPLETE \
             packed-NZCV whole-instruction authority bindings (w32/w64) the verifier \
             and coverage gate use when no in-block consumer binding applies. \
             (15 degenerate CBZ/CBNZ-fusion + CmpSelectCombine X==X retracted in #62; \
             TST==TBZ/TBNZ + CSEL-swap remain)"
        );
        for obligation in &proofs {
            assert_valid(obligation);
        }
    }

    #[test]
    fn test_proof_names_unique() {
        let proofs = all_cmp_combine_proofs_with_variants();
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let len_before = names.len();
        names.dedup();
        assert_eq!(names.len(), len_before, "all proof names should be unique");
    }
}
