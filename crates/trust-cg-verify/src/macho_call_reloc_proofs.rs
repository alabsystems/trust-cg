// trust-cg-verify/macho_call_reloc_proofs.rs - SMT proofs for x86-64 Mach-O
// CALL (X86_64_RELOC_BRANCH) relocation selection/encoding correctness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sibling of `macho_data_reloc_proofs.rs` (the x86-64 Mach-O DATA rows) and the
// x86 analogue of `aarch64_macho_call_reloc_proofs.rs` (BRANCH26). This proves
// the x86-64 Mach-O direct-CALL relocation row — `X86_64_RELOC_BRANCH`
// (r_pcrel=1, r_length=2) on a `CALL rel32` / `JMP rel32` — emits the UNIQUE
// correct PC-relative encoding of its intended call target.
//
// Linker + runtime formula (canonical Mach-O x86-64 semantics; Apple `ld`,
// LLVM `X86MachObjectWriter`):
//
//   BRANCH (r_pcrel=1, r_length=2), on the CALL/JMP rel32:
//       The linker writes `rel32 = (S + A) - P` into the 4-byte immediate,
//       where `P` is the address of the byte AFTER the rel32 field (the next
//       instruction — x86 PC-relative displacements are relative to the end
//       of the instruction). At runtime the CPU computes
//           branch_target = P + sext(rel32)
//                         = P + ((S + A) - P)
//                         = S + A.
//       The spec side is the intended target `T = S + A`; the emitted side is
//       `P + (T - P)`. The equality needs the ring identity `p + (t - p) == t`,
//       so it is a real equivalence, not `x == x` (the same non-degeneracy
//       shape as BRANCH26 and the PAGE21 page-delta proof). An encoder that
//       drops the PC subtraction (`r_pcrel=0`, an ABSOLUTE row) makes the
//       linker write `T` and the CPU still add `P`, branching to `P + T != T`
//       for `P != 0` — see `proof_branch_wrong_pcrel_refutes`.
//
// The signed-32-bit range limit of rel32 is an encoding detail (a too-far
// target is a LINK error, never a miscompile), so — exactly as BRANCH26 models
// the displacement semantics rather than the imm26 bit layout — this models
// the PC-relative displacement semantics `T - P`, which is where a wrong
// (absolute / wrong-sign / wrong-anchor) call relocation would refute.
//
// This is solver-backed formal evidence. Its production authority in the
// object-relocation inventory gate additionally requires the per-object
// ENC-9 Mach-O reparse gate (see `object_inventory.rs`): the formula proves
// the KIND's value semantics; the reparse gate independently re-parses the
// exact emitted record set of each object.
//
// Reference: <mach-o/x86_64/reloc.h> (`X86_64_RELOC_BRANCH`),
// LLVM `X86MachObjectWriter.cpp`, `RuntimeDyldMachOX86_64.h`.

//! SMT proofs for x86-64 Mach-O CALL (BRANCH) relocation correctness.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on x86-64.
const W: u32 = 64;

/// Proof: `X86_64_RELOC_BRANCH` (pcrel=1) makes the `CALL rel32` reach `S + A`.
///
/// Theorem: forall S, A, P : BV64 .
///   (P + ((S + A) - P)) == (S + A)
///
/// The spec side (`trust_ir_expr`) is the intended call target `T = S + A`.
/// The emitted side is the runtime computation: the linker encodes the
/// PC-relative displacement `T - P` into the rel32 immediate, and the CPU
/// adds the next-instruction address `P` at execution.
pub fn proof_branch_call_target() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);

    // Spec: the call should land on the target T = S + A.
    let intended = target.clone();
    // Emitted/runtime: next-instruction PC + the encoded displacement (T - P).
    let displacement = target.bvsub(p.clone());
    let reconstructed = p.bvadd(displacement);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: X86_64_RELOC_BRANCH CALL == S+A (PC-relative call)".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("S".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a BRANCH row that (incorrectly) sets `r_pcrel=0` would
/// make the linker write the absolute target `S + A` into the immediate, so
/// the CPU computes `P + (S + A)` — wrong whenever `P != 0`.
///
/// Intentionally REFUTABLE; the tests assert it is Invalid, demonstrating the
/// positive BRANCH proof is a real equivalence and not a tautology.
pub fn proof_branch_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);

    let intended = target.clone();
    // WRONG: pcrel=0 drops the `- P`; the CPU still adds P.
    let wrong = p.bvadd(target);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: BRANCH with wrong r_pcrel=0 must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![
            ("S".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a BRANCH row anchored at the START of the rel32 field
/// instead of its end (`P' = P - 4`) reaches `T + 4`, not `T` — the classic
/// off-by-instruction-length anchor bug.
pub fn proof_branch_wrong_anchor_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);

    let intended = target.clone();
    // WRONG: displacement computed against P, applied by hardware at P+4
    // (equivalently: displacement anchored 4 bytes early).
    let four = SmtExpr::bv_const(4, W);
    let displacement = target.bvsub(p.clone());
    let wrong = p.bvadd(four).bvadd(displacement);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: BRANCH with rel32 anchored at field start must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![
            ("S".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// Collect the x86-64 Mach-O CALL relocation selection/encoding proofs.
///
/// Returns the 1 positive obligation covering the direct-call relocation row
/// the x86-64 Mach-O emitter produces for `CALL symbol` (`X86_64_RELOC_BRANCH`).
/// It must verify.
pub fn x86_64_macho_call_relocation_proofs() -> Vec<ProofObligation> {
    vec![proof_branch_call_target()]
}

/// Negative-control obligations (each is REFUTABLE — a wrong encoding).
pub fn x86_64_macho_call_relocation_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_branch_wrong_pcrel_refutes(),
        proof_branch_wrong_anchor_refutes(),
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

    #[test]
    fn all_x86_call_reloc_proofs_verify() {
        for obligation in x86_64_macho_call_relocation_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "x86-64 Mach-O call relocation proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_x86_call_reloc_negative_controls_refute() {
        for obligation in x86_64_macho_call_relocation_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "x86-64 Mach-O call relocation NEGATIVE control '{}' should be Invalid \
                 (a wrong encoding must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn x86_call_reloc_proofs_are_non_degenerate() {
        for obligation in x86_64_macho_call_relocation_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "x86-64 Mach-O call relocation proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
        }
    }

    #[test]
    fn x86_call_reloc_proof_count_and_names_unique() {
        let proofs = x86_64_macho_call_relocation_proofs();
        assert_eq!(proofs.len(), 1, "expected 1 call relocation proof");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate call reloc proof names");
    }
}
