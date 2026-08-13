// trust-cg-verify/elf_data_reloc_proofs.rs - SMT proofs for x86-64 ELF
// DATA relocation selection/encoding correctness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The ELF mirror of `macho_data_reloc_proofs.rs`: every DATA relocation row
// the x86-64 ELF emitter produces (`R_X86_64_64`, `R_X86_64_PC32` in both its
// emitted forms, `R_X86_64_GOTPCREL`) is here proven to be the UNIQUE correct
// encoding of its intended address reference, by showing that the value the
// LINKER applies from the emitted `Elf64_Rela` (`r_offset`, `r_info` type,
// explicit `r_addend`) — composed with the consumer that reads the patched
// field (the CPU's RIP-relative addressing, or the `DW_EH_PE_pcrel` DWARF
// reader) — equals the intended address expression for that reference, for
// all symbol/section/PC values.
//
// Technique mirrors `macho_data_reloc_proofs.rs` (Alive2-style, PLDI 2021):
// encode the linker+consumer-applied formula as the `aarch64_expr` (the
// "emitted" side) and the intended address expression as the `trust_ir_expr`
// (the "spec" side), then prove equivalence. A row with the WRONG
// addend/anchor/pc-relativity REFUTES — exercised by the negative-control
// builders (`*_wrong_*` / `*_missing_*`) and the unit tests.
//
// Linker formulas (System V AMD64 psABI, "Relocation Types"; matching GNU ld,
// LLD, and LLVM `X86ELFObjectWriter`). The load-bearing ELF-vs-Mach-O
// difference: ELF `Rela` addends are EXPLICIT (`r_addend`, the in-place field
// is dead), and `P` is the address of the relocated FIELD ITSELF (`r_offset`
// position, the field START) — NOT the Mach-O field END. An x86 RIP-relative
// operand is nevertheless evaluated by the CPU against the END of the 4-byte
// field (RIP = P + 4), so every instruction-operand PC32-family row must bake
// `A = -4` to bridge the two anchors. Dropping that bias is a real 4-byte
// miscompile, proven refutable below.
//
//   R_X86_64_64 (word64): *field = S + A
//       Absolute 64-bit pointer slot. The linker adds the resolved symbol
//       address `S` to the explicit addend `A`. Emitted for every
//       `GlobalSymbolRef` pointer slot inside a data global (vtable method
//       slots, `static FNS: [fn(); N]`), with `A` = the slot's addend.
//
//   R_X86_64_PC32 (word32), instruction-operand form: *field = S + A - P,
//       with emitter-baked `A = -4`. The CPU computes the operand address as
//       RIP + field = (P + 4) + (S - 4 - P) = S. Emitted for a same-module
//       `GlobalRef` RIP-relative materialization (`lea reg, [rip + disp]`).
//
//   R_X86_64_PC32 (word32), `.eh_frame` DW_EH_PE_pcrel form: *field =
//       S + A - P with `A = 0`. The DWARF reader computes field_addr + *field
//       = P + (S - P) = S — reader and linker share the field-START anchor,
//       so no bias addend exists in this form. Emitted for the FDE pc-begin
//       pointer of a dynamic-alloc frame. Applying the instruction-form `-4`
//       bias here lands the unwinder 4 bytes short — refuted below.
//
//   R_X86_64_GOTPCREL (word32): *field = G + GOT + A - P, with `A = -4`.
//       `G + GOT` is the address of the GOT slot the linker fills with `&S`;
//       the RIP-relative load `mov reg, [rip + disp]` reads that slot:
//       RIP + field = (P + 4) + (Gs - 4 - P) = Gs. Emitted for an
//       `ExternRefGot` materialization.
//
// This is solver-backed formal evidence. Its production authority in the
// object-relocation inventory gate additionally requires the per-object ELF
// reparse gate (see `object_inventory.rs`): the formula proves the KIND's
// value semantics; the reparse gate independently re-parses the exact emitted
// record set (`r_offset`, `r_info`, `r_addend`) of each object.
//
// Reference: System V AMD64 ABI ("Relocation Types" table), LSB `.eh_frame`
// encoding (`DW_EH_PE_pcrel|sdata4`), LLVM `X86ELFObjectWriter.cpp`.

//! SMT proofs for x86-64 ELF DATA relocation selection/encoding correctness.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on x86-64.
const W: u32 = 64;

/// Helper: the CPU's RIP anchor for a 4-byte displacement field at `P`
/// (ELF `r_offset` = field START): `RIP = P + 4`.
fn rip_after_field(field_addr: SmtExpr) -> SmtExpr {
    field_addr.bvadd(SmtExpr::bv_const(4, W))
}

// ===========================================================================
// 1. R_X86_64_64 — absolute 64-bit pointer slot
// ===========================================================================

/// Proof: `R_X86_64_64` writes the intended absolute pointer `S + A`.
///
/// Theorem: forall S, A : BV64 .   (A + S) == (S + A)
///
/// The emitted side models the linker's word64 application: it takes the
/// explicit `r_addend` `A` and adds the resolved symbol address `S`. The spec
/// side is the intended reference "the slot holds the address of S plus
/// addend A".
pub fn proof_abs64() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);

    // Intended: address-of-S plus addend.
    let intended = s.clone().bvadd(a.clone());
    // Linker (word64, non-pcrel): explicit addend + resolved symbol address.
    let linker = a.bvadd(s);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: R_X86_64_64 == S + A (abs64 pointer slot)".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker,
        inputs: vec![("S".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: an abs64 slot (incorrectly) emitted pc-relative would
/// make the linker subtract the field address `P`, producing `S + A - P`,
/// which is NOT the intended absolute `S + A` whenever `P != 0`.
///
/// Intentionally REFUTABLE; the tests assert it is Invalid, demonstrating the
/// positive proof is a real equivalence and not a tautology.
pub fn proof_abs64_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let intended = s.clone().bvadd(a.clone());
    // WRONG: a pc-relative type makes the linker compute S + A - P.
    let linker_wrong = a.bvadd(s).bvsub(p);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: R_X86_64_64 emitted pc-relative must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker_wrong,
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
// 2. R_X86_64_PC32 — instruction-operand form (baked A = -4)
// ===========================================================================

/// Proof: `R_X86_64_PC32` with the emitter-baked `A = -4` makes a
/// RIP-relative operand (`lea reg, [rip + disp]`) address exactly `S`.
///
/// Theorem: forall S, P : BV64 .
///   ((P + 4) + ((S - 4) - P)) == S
///
/// Spec side: the intended operand address — the symbol `S`. Emitted side:
/// the linker writes `S + A - P` into the 4-byte field with the explicit
/// `r_addend = -4` and `P` = the field-START address (`r_offset`); the CPU
/// then adds RIP = `P + 4` (x86 RIP-relative displacements are relative to
/// the END of the instruction / field). The equality needs the ring identity
/// `(p + 4) + ((s - 4) - p) == s`, so it is a real equivalence, not `x == x`.
/// The baked `-4` is load-bearing: it bridges ELF's field-START `P`
/// convention to the CPU's field-END RIP — omitting it lands 4 bytes past
/// the symbol ([`proof_pc32_missing_bias_addend_refutes`]).
pub fn proof_pc32_riprel_operand() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let p = SmtExpr::var("P", W);
    let four = SmtExpr::bv_const(4, W);

    // Spec: the intended operand address.
    let intended = s.clone();
    // Linker: S + (-4) - P into the field; CPU: RIP (= P + 4) + field.
    let field = s.bvsub(four).bvsub(p.clone());
    let runtime = rip_after_field(p).bvadd(field);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: R_X86_64_PC32 RIP-relative operand == S \
               (baked -4 bridges field-start P to RIP)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: runtime,
        inputs: vec![("S".to_string(), W), ("P".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a PC32 instruction-operand row emitted WITHOUT the `-4`
/// bias addend (`A = 0`) makes the CPU address `S + 4` — 4 bytes past the
/// symbol; differs from `S` always. Must REFUTE.
pub fn proof_pc32_missing_bias_addend_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let p = SmtExpr::var("P", W);

    let intended = s.clone();
    // WRONG: A = 0 — the field-start/field-end anchor mismatch is unbridged.
    let field_wrong = s.bvsub(p.clone());
    let runtime_wrong = rip_after_field(p).bvadd(field_wrong);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: PC32 operand without baked -4 addend must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: runtime_wrong,
        inputs: vec![("S".to_string(), W), ("P".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a would-be absolute row in the PC32 slot (pc-relativity
/// dropped: the linker writes `S + A` with no `- P`) makes the CPU compute
/// `P + 4 + S - 4 = P + S`; wrong whenever `P != 0`. Must REFUTE.
pub fn proof_pc32_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let p = SmtExpr::var("P", W);
    let four = SmtExpr::bv_const(4, W);

    let intended = s.clone();
    // WRONG: no PC subtraction; the CPU still adds RIP.
    let field_wrong = s.bvsub(four);
    let runtime_wrong = rip_after_field(p).bvadd(field_wrong);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: PC32 with pc-relativity dropped must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: runtime_wrong,
        inputs: vec![("S".to_string(), W), ("P".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 2b. R_X86_64_PC32 — `.eh_frame` DW_EH_PE_pcrel data form (A = 0)
// ===========================================================================

/// Proof: `R_X86_64_PC32` on an `.eh_frame` FDE pc-begin slot (`A = 0`)
/// resolves, per `DW_EH_PE_pcrel`, to exactly `S + A`.
///
/// Theorem: forall S, A, P : BV64 .
///   (((S + A) - P) + P) == (S + A)
///
/// Spec side: the intended pointer target `S + A` (the function's address;
/// the emitter carries the FDE's intra-section offset in `A`). Emitted side:
/// the linker writes `S + A - P` into the 4-byte data slot, and the DWARF
/// reader computes `*field + field_addr` — `DW_EH_PE_pcrel` is field-START
/// relative, the SAME anchor ELF's `P` uses, so this form correctly bakes NO
/// bias addend. The equality requires the ring identity `(x - p) + p == x`,
/// a real equivalence. The instruction-operand proof does NOT cover this
/// form: its consumer anchor is RIP = `P + 4`, this one's is `P` — mixing
/// them up is a 4-byte unwinder miscompile
/// ([`proof_pc32_ehframe_wrong_bias_refutes`]).
pub fn proof_pc32_ehframe_pcrel() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    // Spec: the intended target address.
    let intended = s.clone().bvadd(a.clone());
    // Linker writes S + A - P; the DW_EH_PE_pcrel reader adds the field
    // START address back.
    let field = s.bvadd(a).bvsub(p.clone());
    let reader = field.bvadd(p);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: R_X86_64_PC32 .eh_frame pc-begin (field + field_addr == S + A, \
               shared field-start anchor)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reader,
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

/// Negative control: applying the instruction-operand `-4` bias to the
/// `.eh_frame` data form (whose reader anchors at field START, not RIP)
/// lands the unwinder at `S - 4`; differs from `S` always. Must REFUTE.
pub fn proof_pc32_ehframe_wrong_bias_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let p = SmtExpr::var("P", W);
    let four = SmtExpr::bv_const(4, W);

    let intended = s.clone();
    // WRONG: the -4 instruction bias applied where the reader anchors at P.
    let field_wrong = s.bvsub(four).bvsub(p.clone());
    let reader_wrong = field_wrong.bvadd(p);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: .eh_frame PC32 with spurious -4 bias must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reader_wrong,
        inputs: vec![("S".to_string(), W), ("P".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 3. R_X86_64_GOTPCREL — RIP-relative load of &S from the GOT
// ===========================================================================

/// Proof: `R_X86_64_GOTPCREL` with the emitter-baked `A = -4` makes the
/// RIP-relative load `mov reg, [rip + disp]` address exactly the GOT slot
/// `Gs` (which the linker fills with `&S`).
///
/// Theorem: forall Gs, P : BV64 .
///   ((P + 4) + ((Gs - 4) - P)) == Gs
///
/// Spec side: the intended GOT-slot address `Gs` (= `G + GOT` in psABI
/// terms — the slot's absolute address). Emitted side: the linker writes
/// `Gs + A - P` with `r_addend = -4` and `P` = field START; the CPU adds
/// RIP = `P + 4`. The RIP-relative load thus addresses exactly the GOT entry
/// `Gs`, out of which it loads `&S` (the GOT contract established by the
/// linker populating the slot). Same ring-identity shape as the PC32 operand
/// proof; dropping the bias or the PC subtraction refutes
/// ([`proof_gotpcrel_missing_bias_addend_refutes`],
/// [`proof_gotpcrel_wrong_pcrel_refutes`]).
pub fn proof_gotpcrel_riprel() -> ProofObligation {
    let gs = SmtExpr::var("Gs", W);
    let p = SmtExpr::var("P", W);
    let four = SmtExpr::bv_const(4, W);

    let intended = gs.clone();
    let field = gs.bvsub(four).bvsub(p.clone());
    let runtime = rip_after_field(p).bvadd(field);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: R_X86_64_GOTPCREL addresses the GOT slot (RIP + field == Gs, \
               baked -4 bridges field-start P to RIP)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: runtime,
        inputs: vec![("Gs".to_string(), W), ("P".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a GOTPCREL row without the `-4` bias addend loads from
/// `Gs + 4` — 4 bytes past the GOT slot. Must REFUTE.
pub fn proof_gotpcrel_missing_bias_addend_refutes() -> ProofObligation {
    let gs = SmtExpr::var("Gs", W);
    let p = SmtExpr::var("P", W);

    let intended = gs.clone();
    let field_wrong = gs.bvsub(p.clone());
    let runtime_wrong = rip_after_field(p).bvadd(field_wrong);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: GOTPCREL without baked -4 addend must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: runtime_wrong,
        inputs: vec![("Gs".to_string(), W), ("P".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a GOTPCREL row with the PC subtraction dropped (the
/// absolute slot address written into the field) makes the CPU address
/// `P + Gs`; wrong whenever `P != 0`. Must REFUTE.
pub fn proof_gotpcrel_wrong_pcrel_refutes() -> ProofObligation {
    let gs = SmtExpr::var("Gs", W);
    let p = SmtExpr::var("P", W);
    let four = SmtExpr::bv_const(4, W);

    let intended = gs.clone();
    let field_wrong = gs.bvsub(four);
    let runtime_wrong = rip_after_field(p).bvadd(field_wrong);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF x86-64: GOTPCREL with pc-relativity dropped must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: runtime_wrong,
        inputs: vec![("Gs".to_string(), W), ("P".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// Collect the x86-64 ELF DATA relocation selection/encoding proofs.
///
/// Returns the 4 positive obligations covering every data relocation row the
/// x86-64 ELF emitter produces:
/// - `R_X86_64_64` (abs64 pointer slot `S + A`),
/// - `R_X86_64_PC32`, instruction-operand form (RIP-relative operand,
///   baked `-4` bridging ELF's field-start `P` to the CPU's field-end RIP),
/// - `R_X86_64_PC32`, `.eh_frame` `DW_EH_PE_pcrel` form (shared field-start
///   anchor, no bias addend),
/// - `R_X86_64_GOTPCREL` (RIP-relative GOT-slot load, baked `-4`).
///   All must verify.
pub fn x86_64_elf_data_relocation_proofs() -> Vec<ProofObligation> {
    vec![
        proof_abs64(),
        proof_pc32_riprel_operand(),
        proof_pc32_ehframe_pcrel(),
        proof_gotpcrel_riprel(),
    ]
}

/// Negative-control obligations (each is REFUTABLE — a wrong encoding).
///
/// These are NOT registered as proofs; they are used by tests to demonstrate
/// the positive proofs are real equivalences (a malformed row is rejected).
pub fn x86_64_elf_data_relocation_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_abs64_wrong_pcrel_refutes(),
        proof_pc32_missing_bias_addend_refutes(),
        proof_pc32_wrong_pcrel_refutes(),
        proof_pc32_ehframe_wrong_bias_refutes(),
        proof_gotpcrel_missing_bias_addend_refutes(),
        proof_gotpcrel_wrong_pcrel_refutes(),
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
    fn all_elf_data_reloc_proofs_verify() {
        for obligation in x86_64_elf_data_relocation_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "x86-64 ELF data relocation proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_elf_data_reloc_negative_controls_refute() {
        for obligation in x86_64_elf_data_relocation_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "x86-64 ELF data relocation NEGATIVE control '{}' should be Invalid \
                 (a wrong encoding must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn elf_data_reloc_proofs_are_non_degenerate() {
        for obligation in x86_64_elf_data_relocation_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "x86-64 ELF data relocation proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
        }
    }

    #[test]
    fn elf_data_reloc_proof_count_and_names_unique() {
        let proofs = x86_64_elf_data_relocation_proofs();
        assert_eq!(proofs.len(), 4, "expected 4 data relocation proofs");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate data reloc proof names");
    }
}
