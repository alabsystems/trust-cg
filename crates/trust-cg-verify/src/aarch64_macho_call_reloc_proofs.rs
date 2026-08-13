// trust-cg-verify/aarch64_macho_call_reloc_proofs.rs - SMT proofs for AArch64
// Mach-O CALL (BRANCH26) relocation selection/encoding correctness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sibling of `aarch64_macho_data_reloc_proofs.rs` (PAGE21/PAGEOFF12 data rows).
// This proves the AArch64 Mach-O direct-CALL relocation row — `ARM64_RELOC_BRANCH26`
// on a `B`/`BL` — emits the UNIQUE correct PC-relative encoding of its intended
// call target. This is solver-backed formal evidence only: it does not promote
// the row through the production Certified inventory gate. Production lacks an
// independently checked authority report bound to the exact emitted object.
//
// Linker + runtime formula (canonical Mach-O ARM64 semantics; Apple `ld`,
// LLVM `AArch64MachObjectWriter`):
//
//   BRANCH26 (r_pcrel=1, r_length=2), on the B/BL:
//       The linker writes `imm26 = ((S + A) - P) >> 2` into bits [25:0]. At
//       runtime the CPU computes
//           branch_target = P + sext(imm26 << 2)
//                         = P + ((S + A) - P)      [low 2 bits of the
//                                                   instruction-aligned delta
//                                                   are 0, so >>2<<2 is exact]
//                         = S + A.
//       The selection proof certifies the branch lands on `T = S + A`: the spec
//       side is `T`; the emitted side is `P + (T - P)`. The equality needs the
//       ring identity `p + (t - p) == t`, so it is a real equivalence, not
//       `x == x` (same shape as the PAGE21 page-delta proof). An encoder that
//       drops the PC subtraction (`r_pcrel=0`, an ABSOLUTE row) makes the linker
//       write `T` and the CPU still add `P`, branching to `P + T != T` for
//       `P != 0` — see `proof_branch26_wrong_pcrel_refutes`.
//
// The `>>2<<2` instruction-alignment step and the 26-bit range limit are
// encoding details (a too-far target is a LINK error, never a miscompile), so —
// exactly as PAGE21 models page-masking rather than the immhi/immlo bit layout —
// this models the PC-relative displacement semantics `T - P`, which is where a
// wrong (absolute / wrong-sign) call relocation would refute.
//
// Reference: <mach-o/arm64/reloc.h> (`ARM64_RELOC_BRANCH26`),
// LLVM `AArch64MachObjectWriter.cpp`, `RuntimeDyldMachOAArch64.h`.

//! SMT proofs for AArch64 Mach-O CALL (BRANCH26) relocation correctness.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on AArch64.
const W: u32 = 64;

/// Proof: `ARM64_RELOC_BRANCH26` (pcrel=1) makes the `B`/`BL` branch to `S + A`.
///
/// Theorem: forall S, A, P : BV64 .
///   (P + ((S + A) - P)) == (S + A)
///
/// The spec side (`trust_ir_expr`) is the intended call target `T = S + A`. The
/// emitted side (`aarch64_expr`) is the runtime computation: the linker encodes
/// the PC-relative displacement `T - P` into the branch immediate, and the CPU
/// adds the instruction PC `P` at execution. The equality requires
/// `p + (t - p) == t`, so it is a genuine equivalence (non-degenerate).
pub fn proof_branch26_call_target() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);

    // Spec: the branch should land on the call target T = S + A.
    let intended = target.clone();
    // Emitted/runtime: PC + the encoded PC-relative displacement (T - P).
    let displacement = target.bvsub(p.clone());
    let reconstructed = p.bvadd(displacement);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: ARM64_RELOC_BRANCH26 BL == S+A (PC-relative call)".to_string(),
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

/// Negative control: a BRANCH26 row that (incorrectly) sets `r_pcrel=0` would make
/// the linker write the absolute target `S + A` into the immediate instead of the
/// PC-relative delta, so the CPU branches to `P + (S + A)` — which differs from
/// the intended `S + A` whenever `P != 0`.
///
/// This obligation is intentionally REFUTABLE; the unit tests / AY lane assert it
/// is Invalid (a counterexample exists), demonstrating the positive BRANCH26 proof
/// is a real equivalence and not a tautology.
pub fn proof_branch26_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);

    let intended = target.clone();
    // WRONG: pcrel=0 drops the `- P`, so the linker writes the absolute target and
    // the CPU still adds the instruction PC: P + (S + A).
    let wrong = p.bvadd(target);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: BRANCH26 with wrong r_pcrel=0 must REFUTE".to_string(),
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

/// Collect the AArch64 Mach-O CALL relocation selection/encoding proofs.
///
/// Returns the 1 positive obligation covering the direct-call relocation row the
/// AArch64 Mach-O emitter produces for a `BL symbol` (`ARM64_RELOC_BRANCH26`).
/// It must verify. GOT_LOAD / TLVP / UNSIGNED / SUBTRACTOR rows are NOT covered
/// here — they stay fail-closed in the inventory gate until both an emission path
/// and a selection proof exist.
pub fn aarch64_macho_call_relocation_proofs() -> Vec<ProofObligation> {
    vec![proof_branch26_call_target()]
}

/// Negative-control obligations (each is REFUTABLE — a wrong encoding).
///
/// NOT registered as proofs; used by tests to demonstrate the positive proof is a
/// real equivalence (a malformed, absolute call row is rejected).
pub fn aarch64_macho_call_relocation_negative_controls() -> Vec<ProofObligation> {
    vec![proof_branch26_wrong_pcrel_refutes()]
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
    fn all_aarch64_call_reloc_proofs_verify() {
        for obligation in aarch64_macho_call_relocation_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "AArch64 Mach-O call relocation proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_aarch64_call_reloc_negative_controls_refute() {
        for obligation in aarch64_macho_call_relocation_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "AArch64 Mach-O call relocation NEGATIVE control '{}' should be Invalid \
                 (a wrong encoding must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn aarch64_call_reloc_proofs_are_non_degenerate() {
        for obligation in aarch64_macho_call_relocation_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "AArch64 Mach-O call relocation proof '{}' is DEGENERATE (X==X); it proves nothing",
                obligation.name
            );
        }
    }

    #[test]
    fn aarch64_call_reloc_proof_count_and_names_unique() {
        let proofs = aarch64_macho_call_relocation_proofs();
        assert_eq!(proofs.len(), 1, "expected 1 call relocation proof");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate call reloc proof names");
    }
}
