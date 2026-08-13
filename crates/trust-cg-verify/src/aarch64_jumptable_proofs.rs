// trust-cg-verify/aarch64_jumptable_proofs.rs - SMT proofs for the AArch64
// dense-`match` / fieldless-enum JUMP-TABLE dispatch sequence.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// A dense contiguous integer `match` (>= 4 arms) and a >= 6-variant fieldless
// enum lower to a JumpTable. The AArch64 emitter materializes the dispatch as
//
//     ADR   X1, <jumptable>          ; X1 = table base T
//     LDRSW X2, [X1, X0, LSL #2]     ; X2 = sext32( mem[ T + 4*selector ] )
//     ADD   X3, X1, X2               ; X3 = T + entry  (entry = target - T)
//     BR    X3                       ; jump to target
//
// where the table, appended after the function body, holds one signed 32-bit
// `(target - T)` delta per arm (`jit.rs` block-splice: `entry = new_target -
// new_table_base`). This module discharges the TWO address-computation opcodes
// that the per-compile coverage gate previously fail-closed:
//
//   (1) ADR  — the PC-relative jump-table BASE. The pipeline writes the ADR
//       imm21 = `T - P` (an internal __text PC-relative byte delta; `jit.rs`:
//       `pc_relative = new_table_base - new_adr`). At runtime ADR computes
//           Xd = P + sext21(imm21) = P + (T - P) = T.
//       This is the SAME ring identity `p + (t - p) == t` already discharged for
//       BRANCH26 (`proof_branch26_call_target`) and PAGE21 — byte-granular (ADR
//       has no `>>2<<2` instruction-alignment step, unlike BRANCH26's branch
//       immediate). FAITHFUL: spec = `T`, machine = `P + (T - P)`; structurally
//       distinct, so an ABSOLUTE encoder that drops the `- P` REFUTES
//       (`proof_adr_jumptable_absolute_refutes`).
//
//   (2) LDRSW [Xn, Xm, LSL #2] — the scaled signed-word table-entry load. This
//       module proves ONLY the EFFECTIVE-ADDRESS scaling, which is the
//       non-degenerate part this opcode contributes: the intended addressing for
//       a 4-byte-entry table is `base + 4*index`, and the emitted `[Xn, Xm, LSL
//       #2]` addressing mode computes `base + (index << 2)`
//       (`encoding_mem.rs`: option=011 LSL, S=1 => shift by 2). FAITHFUL: spec =
//       `base + 4*index` (bvmul), machine = `base + (index << 2)` (bvshl) — EQUAL
//       (4 == 1<<2) but STRUCTURALLY DISTINCT, so a WRONG scale (LSL #3, i.e.
//       `index << 3`) REFUTES (`proof_ldrsw_ro_wrong_scale_refutes`).
//
//       HONEST SCOPE: this is an ADDRESS-MODE credit, strictly STRONGER than the
//       degenerate `("load", Memory)` query (which is on the
//       KNOWN_DEGENERATE_PENDING_FIX debt and proves nothing), but it is NOT a
//       full memory-load proof. The loaded VALUE itself — the memory dereference
//       `mem[addr]` plus the i32 -> i64 sign-extend that produces the table entry
//       — is the SAME unfaithful-load debt the whole `Ldr*` family carries (the
//       SMT model has no faithful independent dereference encoder), and is NOT
//       separately proven here. We credit exactly the scaled effective-address
//       arithmetic, nothing more.
//
// Technique mirrors the sibling relocation proofs (`aarch64_macho_*_reloc_proofs`):
// the `aarch64_expr` is the emitted/runtime computation and the `trust_ir_expr`
// is the intended spec; each obligation is NON-DEGENERATE (the two sides are
// structurally distinct), so a wrong encoding REFUTES — exercised by the
// `*_refutes` negative controls and the unit tests.
//
// Reference: ARM ARM C6.2 (ADR; LDRSW register-offset, the option/S scaling
// field); `crates/trust-cg-codegen/src/jit.rs` (block-splice jump-table tail);
// `crates/trust-cg-codegen/src/aarch64/encoding_mem.rs` (`encode_ldrsw_ro`).

//! SMT proofs for the AArch64 jump-table dispatch base (ADR) + scaled
//! table-entry effective address (LDRSW [Xn,Xm,LSL#2]).

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on AArch64.
const W: u32 = 64;

// ===========================================================================
// (1) ADR — PC-relative jump-table base
// ===========================================================================

/// Proof: the jump-table `ADR Xd, <table>` lands `Xd` on the table base `T`.
///
/// Theorem: forall P, T : BV64 .  (P + (T - P)) == T
///
/// `P` is the runtime address of the ADR instruction; `T` is the (appended)
/// jump-table base address. The pipeline encodes the ADR imm21 as the internal
/// PC-relative byte delta `T - P` (`jit.rs`: `pc_relative = new_table_base -
/// new_adr`), and the CPU adds the instruction PC `P` at execution:
/// `Xd = P + sext21(imm21) = P + (T - P) = T`.
///
/// The spec side (`trust_ir_expr`) is the intended base `T`; the emitted side
/// (`aarch64_expr`) is `P + (T - P)`. The equality requires the ring identity
/// `p + (t - p) == t`, so it is a genuine equivalence (non-degenerate), NOT an
/// `X == X`. This is the byte-granular analogue of `proof_branch26_call_target`
/// (ADR has no `>>2<<2` alignment step, so no masking is modeled).
pub fn proof_adr_jumptable_pcrel() -> ProofObligation {
    let p = SmtExpr::var("P", W);
    let t = SmtExpr::var("T", W);

    // Spec: the ADR result should be the jump-table base T.
    let intended = t.clone();
    // Emitted/runtime: PC + the encoded PC-relative displacement (T - P).
    let displacement = t.bvsub(p.clone());
    let reconstructed = p.bvadd(displacement);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AArch64 jump-table: ADR Xd == table_base (PC-relative base, P + (table_base - P))"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![("P".to_string(), W), ("T".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control for [`proof_adr_jumptable_pcrel`]: an ABSOLUTE encoder that
/// (incorrectly) writes the absolute base `T` into imm21 instead of the
/// PC-relative delta `T - P`. The CPU still adds the instruction PC, landing on
/// `P + T`, which differs from the intended `T` whenever `P != 0`.
///
/// Intentionally REFUTABLE; the unit tests / AY lane assert it is Invalid (a
/// counterexample exists), demonstrating the positive ADR proof is a real
/// equivalence and not a tautology.
pub fn proof_adr_jumptable_absolute_refutes() -> ProofObligation {
    let p = SmtExpr::var("P", W);
    let t = SmtExpr::var("T", W);

    let intended = t.clone();
    // WRONG: drops the `- P`, so the absolute base is encoded and the CPU still
    // adds the instruction PC: P + T.
    let wrong = p.bvadd(t);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AArch64 jump-table: ADR with ABSOLUTE imm (drops -P) must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![("P".to_string(), W), ("T".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// (2) LDRSW [Xn, Xm, LSL #2] — scaled table-entry effective address
// ===========================================================================

/// Proof: the `LDRSW Xt, [Xn, Xm, LSL #2]` table-entry load addresses
/// `base + 4*index` (the intended 4-byte-entry indexing).
///
/// Theorem: forall base, index : BV64 .
///   (base + (index << 2)) == (base + 4*index)
///
/// The spec side (`trust_ir_expr`) is the intended addressing for a 4-byte-entry
/// table: `base + 4*index` (a multiply). The emitted side (`aarch64_expr`) is the
/// `[Xn, Xm, LSL #2]` addressing-mode effective address `base + (index << 2)`
/// (`encoding_mem.rs::encode_ldrsw_ro`: option=011 LSL, S=1 => shift amount 2).
/// The two sides use STRUCTURALLY DISTINCT operators (bvmul vs bvshl) yet are
/// EQUAL for all values (`4 == 1 << 2`), so this is a genuine equivalence
/// (non-degenerate); a WRONG scale REFUTES (see
/// [`proof_ldrsw_ro_wrong_scale_refutes`]).
///
/// SCOPE (honest): this certifies the scaled EFFECTIVE-ADDRESS arithmetic only —
/// strictly stronger than the degenerate `("load", Memory)` query. It does NOT
/// prove the loaded VALUE: the `mem[addr]` dereference and the i32 -> i64
/// sign-extend remain the shared unfaithful-load debt of the whole `Ldr*` family
/// (no faithful independent dereference encoder in the SMT model) and are not
/// proven here.
pub fn proof_ldrsw_ro_scaled_addr() -> ProofObligation {
    let base = SmtExpr::var("base", W);
    let index = SmtExpr::var("index", W);

    // Spec: 4-byte-entry indexing — base + 4*index (a multiply by the entry size).
    let intended = base
        .clone()
        .bvadd(index.clone().bvmul(SmtExpr::bv_const(4, W)));
    // Emitted: the [Xn, Xm, LSL #2] addressing mode — base + (index << 2).
    let effective = base.bvadd(index.bvshl(SmtExpr::bv_const(2, W)));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AddrMode: jump-table LDRSW [Xn,Xm,LSL#2] scaled effective addr \
               base+(index<<2) == base+4*index"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: effective,
        inputs: vec![("base".to_string(), W), ("index".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control for [`proof_ldrsw_ro_scaled_addr`]: a WRONG scale `LSL #3`
/// (`index << 3`, i.e. 8-byte stride) computes `base + 8*index`, which differs
/// from the intended `base + 4*index` whenever `index != 0`.
///
/// Intentionally REFUTABLE; the unit tests / AY lane assert it is Invalid,
/// demonstrating the positive scaled-address proof is a real equivalence (the
/// scale is load-bearing) and not a tautology.
pub fn proof_ldrsw_ro_wrong_scale_refutes() -> ProofObligation {
    let base = SmtExpr::var("base", W);
    let index = SmtExpr::var("index", W);

    let intended = base
        .clone()
        .bvadd(index.clone().bvmul(SmtExpr::bv_const(4, W)));
    // WRONG: LSL #3 (shift by 3) scales by 8, not 4.
    let wrong = base.bvadd(index.bvshl(SmtExpr::bv_const(3, W)));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AddrMode: jump-table LDRSW WRONG scale (index<<3, 8-byte stride) must REFUTE"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![("base".to_string(), W), ("index".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// The jump-table PC-relative BASE proof (ADR), registered under
/// `ProofCategory::MachOEmission` (the code-emission family that already holds
/// the sibling PC-relative relocation/address proofs).
pub fn aarch64_jumptable_pcrel_proofs() -> Vec<ProofObligation> {
    vec![proof_adr_jumptable_pcrel()]
}

/// The jump-table scaled table-entry EFFECTIVE-ADDRESS proof (LDRSW
/// [Xn,Xm,LSL#2]), registered under `ProofCategory::AddressMode` (the addressing
/// family that holds the other scaled/base+reg effective-address proofs).
pub fn aarch64_jumptable_addr_proofs() -> Vec<ProofObligation> {
    vec![proof_ldrsw_ro_scaled_addr()]
}

/// Negative-control obligations (each is REFUTABLE — a wrong encoding).
///
/// NOT registered as proofs; used by tests to demonstrate the positive proofs
/// are real equivalences (the absolute ADR / wrong LDRSW scale are rejected).
pub fn aarch64_jumptable_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_adr_jumptable_absolute_refutes(),
        proof_ldrsw_ro_wrong_scale_refutes(),
    ]
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::verify_by_evaluation;
    use crate::verify::VerificationResult;

    fn all_positive() -> Vec<ProofObligation> {
        let mut v = aarch64_jumptable_pcrel_proofs();
        v.extend(aarch64_jumptable_addr_proofs());
        v
    }

    #[test]
    fn all_jumptable_proofs_verify() {
        for obligation in all_positive() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "AArch64 jump-table proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_jumptable_negative_controls_refute() {
        for obligation in aarch64_jumptable_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "AArch64 jump-table NEGATIVE control '{}' should be Invalid \
                 (a wrong encoding must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn jumptable_proofs_are_non_degenerate() {
        for obligation in all_positive() {
            assert!(
                obligation.is_genuinely_proven(),
                "AArch64 jump-table proof '{}' is DEGENERATE (X==X); it proves nothing",
                obligation.name
            );
        }
    }

    #[test]
    fn jumptable_proof_count_and_names_unique() {
        let proofs = all_positive();
        assert_eq!(proofs.len(), 2, "expected 2 jump-table positive proofs");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate jump-table proof names");
    }
}
