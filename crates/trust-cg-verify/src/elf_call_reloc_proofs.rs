// trust-cg-verify/elf_call_reloc_proofs.rs - SMT proofs for x86-64 ELF
// CALL (R_X86_64_PLT32) relocation selection/encoding correctness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sibling of `elf_data_reloc_proofs.rs` (the x86-64 ELF DATA rows) and the
// ELF analogue of `macho_call_reloc_proofs.rs` (X86_64_RELOC_BRANCH). This
// proves the x86-64 ELF direct-CALL relocation row — `R_X86_64_PLT32` with
// the emitter-baked `r_addend = -4` on a `CALL rel32` / `JMP rel32` — emits
// the UNIQUE correct PC-relative encoding of its intended call target.
//
// Linker + runtime formula (System V AMD64 psABI; GNU ld / LLD semantics):
//
//   PLT32 (word32): *field = L + A - P
//       `L` is the address the linker chooses for reaching the callee — the
//       callee's PLT entry, or the resolved symbol address itself when the
//       call binds locally (ld/LLD treat PLT32 against a defined local symbol
//       exactly like PC32). `P` is the address of the relocated FIELD ITSELF
//       (`r_offset` position — the field START, NOT the Mach-O field END).
//       At runtime the CPU computes
//           branch_target = RIP + sext(rel32),   RIP = P + 4
//                         = (P + 4) + (L + A - P)
//                         = L + A + 4,
//       which equals the intended `L` exactly when the emitter bakes
//       `A = -4` — the explicit-addend bridge between ELF's field-START `P`
//       convention and the CPU's field-END RIP. The spec side is the
//       intended target `L`; the emitted side is `(P + 4) + ((L - 4) - P)`.
//       The equality needs the ring identity `(p + 4) + ((l - 4) - p) == l`,
//       so it is a real equivalence, not `x == x` (the same non-degeneracy
//       shape as the Mach-O BRANCH proof). An encoder that omits the `-4`
//       addend calls `L + 4` (into the middle of the target's first
//       instruction); one that drops the PC subtraction calls `P + L` — both
//       refuted below.
//
// The signed-32-bit range limit of rel32 is an encoding detail (a too-far
// target is a LINK error, never a miscompile), so — exactly as the Mach-O
// BRANCH proof models the displacement semantics rather than the imm bit
// layout — this models the PC-relative displacement semantics, which is
// where a wrong (absolute / unbias-ed / wrong-anchor) call relocation would
// refute.
//
// This is solver-backed formal evidence. Its production authority in the
// object-relocation inventory gate additionally requires the per-object ELF
// reparse gate (see `object_inventory.rs`): the formula proves the KIND's
// value semantics; the reparse gate independently re-parses the exact
// emitted record set of each object.
//
// Reference: System V AMD64 ABI ("Relocation Types", "Procedure Linkage
// Table"), LLVM `X86ELFObjectWriter.cpp`, GNU ld `elf_x86_64_relocate_section`.

//! SMT proofs for x86-64 ELF CALL (PLT32) relocation correctness.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on x86-64.
const W: u32 = 64;

/// Proof: `R_X86_64_PLT32` with baked `A = -4` makes the `CALL rel32` reach `L`.
///
/// Theorem: forall L, P : BV64 .
///   ((P + 4) + ((L - 4) - P)) == L
///
/// The spec side (`trust_ir_expr`) is the intended call target `L` (PLT entry
/// or locally-resolved callee). The emitted side is the runtime computation:
/// the linker encodes `L + A - P` into the 4-byte rel32 field with the
/// explicit `r_addend = -4` and `P` = the field-START address, and the CPU
/// adds RIP = `P + 4` at execution.
pub fn proof_plt32_call_target() -> ProofObligation {
    let l = SmtExpr::var("L", W);
    let p = SmtExpr::var("P", W);
    let four = SmtExpr::bv_const(4, W);

    // Spec: the call should land on the target L.
    let intended = l.clone();
    // Linker: L + (-4) - P into the field; CPU: RIP (= P + 4) + field.
    let field = l.bvsub(four.clone()).bvsub(p.clone());
    let runtime = p.bvadd(four).bvadd(field);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: R_X86_64_PLT32 CALL == L (baked -4 bridges field-start P to RIP)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: runtime,
        inputs: vec![("L".to_string(), W), ("P".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a PLT32 row emitted WITHOUT the `-4` bias addend
/// (`A = 0`) makes the CPU call `L + 4` — into the middle of the callee's
/// first instruction; differs from `L` always.
///
/// Intentionally REFUTABLE; the tests assert it is Invalid, demonstrating the
/// positive PLT32 proof is a real equivalence and not a tautology.
pub fn proof_plt32_missing_bias_addend_refutes() -> ProofObligation {
    let l = SmtExpr::var("L", W);
    let p = SmtExpr::var("P", W);
    let four = SmtExpr::bv_const(4, W);

    let intended = l.clone();
    // WRONG: A = 0 — the field-start/field-end anchor mismatch is unbridged.
    let field_wrong = l.bvsub(p.clone());
    let runtime_wrong = p.bvadd(four).bvadd(field_wrong);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: PLT32 without baked -4 addend must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: runtime_wrong,
        inputs: vec![("L".to_string(), W), ("P".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a PLT32 row with the PC subtraction dropped (a would-be
/// absolute row: the linker writes `L + A` and the CPU still adds RIP) calls
/// `P + L`; wrong whenever `P != 0`. Must REFUTE.
pub fn proof_plt32_wrong_pcrel_refutes() -> ProofObligation {
    let l = SmtExpr::var("L", W);
    let p = SmtExpr::var("P", W);
    let four = SmtExpr::bv_const(4, W);

    let intended = l.clone();
    // WRONG: no `- P`; the CPU still adds RIP = P + 4.
    let field_wrong = l.bvsub(four.clone());
    let runtime_wrong = p.bvadd(four).bvadd(field_wrong);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: PLT32 with pc-relativity dropped must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: runtime_wrong,
        inputs: vec![("L".to_string(), W), ("P".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// Collect the x86-64 ELF CALL relocation selection/encoding proofs.
///
/// Returns the 1 positive obligation covering the direct-call relocation row
/// the x86-64 ELF emitter produces for `CALL symbol` (`R_X86_64_PLT32`,
/// baked `r_addend = -4`). It must verify.
pub fn x86_64_elf_call_relocation_proofs() -> Vec<ProofObligation> {
    vec![proof_plt32_call_target()]
}

/// Negative-control obligations (each is REFUTABLE — a wrong encoding).
pub fn x86_64_elf_call_relocation_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_plt32_missing_bias_addend_refutes(),
        proof_plt32_wrong_pcrel_refutes(),
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
    fn all_elf_call_reloc_proofs_verify() {
        for obligation in x86_64_elf_call_relocation_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "x86-64 ELF call relocation proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_elf_call_reloc_negative_controls_refute() {
        for obligation in x86_64_elf_call_relocation_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "x86-64 ELF call relocation NEGATIVE control '{}' should be Invalid \
                 (a wrong encoding must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn elf_call_reloc_proofs_are_non_degenerate() {
        for obligation in x86_64_elf_call_relocation_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "x86-64 ELF call relocation proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
        }
    }

    #[test]
    fn elf_call_reloc_proof_count_and_names_unique() {
        let proofs = x86_64_elf_call_relocation_proofs();
        assert_eq!(proofs.len(), 1, "expected 1 call relocation proof");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate call reloc proof names");
    }
}
