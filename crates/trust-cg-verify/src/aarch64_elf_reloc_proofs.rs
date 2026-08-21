// trust-cg-verify/aarch64_elf_reloc_proofs.rs - SMT proofs for AArch64 ELF
// data/call relocation value correctness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The AArch64 *ELF* sibling of the Mach-O relocation proof lanes
// (`aarch64_macho_call_reloc_proofs.rs` — BRANCH26;
// `aarch64_macho_data_reloc_proofs.rs` — PAGE21/PAGEOFF12 and their GOT rows)
// and of the x86-64 ELF lanes (`elf_call_reloc_proofs.rs` /
// `elf_data_reloc_proofs.rs`). It proves the VALUE each AArch64 ELF psABI
// relocation kind our emitter produces computes, modeled on the Rela
// convention: explicit `r_addend` `A`, place `P` = `r_offset` (the address of
// the relocated instruction or data word), and the linker-resolved inputs `S`
// (symbol address) or `G` (the symbol's GOT-slot address). Resolving `S`/`G`
// is the static linker's job — exactly the scoping of every registered
// relocation lane — and the RECORD half (that the object's `.rela.*` entries
// and skeleton fields were laid down faithfully) is the per-object ELF
// reparse gate's job (`trust-cg-codegen/src/elf/reparse.rs`), never this
// lane's. Together they form the object-relocation inventory's Certified
// composition (`ObjectProofBinding::ElfReparseEnforced`; see
// `object_inventory.rs`).
//
// Covered kinds (AArch64 ELF psABI, IHI0056):
//
//   * `R_AARCH64_CALL26`  — BL: patched imm26 branches to `S + A`.
//   * `R_AARCH64_JUMP26`  — B: same value semantics as CALL26.
//   * `R_AARCH64_PREL32`  — 32-bit signed PC-relative data word `S + A - P`.
//   * `R_AARCH64_ABS64`   — absolute 64-bit pointer slot `S + A`.
//   * `R_AARCH64_ADR_PREL_PG_HI21` — ADRP lands on `page(S + A)`.
//   * `R_AARCH64_ADD_ABS_LO12_NC`  — paired ADD recomposes `S + A`.
//   * `R_AARCH64_ADR_GOT_PAGE`     — ADRP lands on the GOT slot's page.
//   * `R_AARCH64_LD64_GOT_LO12_NC` — paired LDR addresses the GOT slot.
//
// G-row addend scope: the psABI operation is `Page(G(GDAT(S+A))) - Page(P)`
// — the addend selects WHICH GOT entry (one holding `S+A`); it never offsets
// the slot's own address. Our emitter pins `A = 0` on every GOT fixup, so
// these rows model the slot address as the single linker-resolved input `G`
// with the (emitter-guaranteed) zero addend folded in; a nonzero-addend GOT
// fixup would need a new obligation, not this one.
//
// Every positive obligation is a genuine ring/mask identity (never `x == x`).
// Six negative controls each flip exactly one linker-formula property
// (pc-relativity, the page mask, or the low-12 recomposition) and must
// REFUTE — asserted by this module's own `verify_by_evaluation` tests (the
// controls are deliberately NOT registered in the proof database, matching
// every precedent lane). The GOT page row shares the ADR_PREL_PG_HI21
// control (identical page-delta formula shape).
//
// Formula-level scope (matching the registered precedent lanes): imm26
// branch scaling (`>>2` into the field, `<<2` at decode) is exact because
// AArch64 instruction addresses and admitted branch targets are 4-aligned —
// `S + A - P ≡ 0 (mod 4)` — and out-of-range displacements are LINK errors,
// not value errors; the LD64 GOT field is bits [11:3] of the offset with a
// psABI-mandated 8-alignment check on the slot, so the modeled
// `(target & 0xFFF)` equals the scaled-field reading exactly when the
// linker's own alignment check passes. Field-width/overflow enforcement is
// the fixup validator's and reparse gate's job, never this lane's.
//
// Reference: ELF for the Arm 64-bit Architecture (AArch64), IHI0056,
// "Relocation types"; LLVM `AArch64ELFObjectWriter.cpp`.

//! SMT proofs for AArch64 ELF relocation value correctness.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on AArch64.
const W: u32 = 64;

/// 4 KiB page base: `x & ~0xFFF`.
fn page(x: SmtExpr) -> SmtExpr {
    let mask = SmtExpr::bv_const(!0xFFFu64, W);
    x.bvand(mask)
}

/// Low-12-bit page offset mask.
fn mask12() -> SmtExpr {
    SmtExpr::bv_const(0xFFF, W)
}

// ===========================================================================
// 1. R_AARCH64_CALL26 / R_AARCH64_JUMP26 — PC-relative branch targets
// ===========================================================================

/// Shared positive body for the two 26-bit branch relocations.
fn branch26_obligation(name: &str) -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);

    // Spec: the branch lands on `S + A`.
    let intended = target.clone();
    // Emitted/runtime: the linker patches the PC-relative displacement
    // `S + A - P` into imm26 (as a scaled word offset); the CPU adds the
    // branch instruction's own PC `P` at execution.
    let displacement = target.bvsub(p.clone());
    let reconstructed = p.bvadd(displacement);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
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

/// Proof: `R_AARCH64_CALL26` makes the `BL` branch to `S + A`.
///
/// Theorem: forall S, A, P : BV64 . (P + ((S + A) - P)) == (S + A) — the ring
/// identity that makes pc-relativity load-bearing (drop the `- P` and it
/// refutes; see [`proof_call26_wrong_pcrel_refutes`]).
pub fn proof_call26_bl_target() -> ProofObligation {
    branch26_obligation("ELF AArch64: R_AARCH64_CALL26 BL == S+A (PC-relative call)")
}

/// Proof: `R_AARCH64_JUMP26` makes the tail-call `B` branch to `S + A`.
///
/// Same value theorem as [`proof_call26_bl_target`]; a separate named row so
/// each emitted relocation kind cites an obligation naming ITS kind.
pub fn proof_jump26_b_target() -> ProofObligation {
    branch26_obligation("ELF AArch64: R_AARCH64_JUMP26 B == S+A (PC-relative tail jump)")
}

/// Negative control: a 26-bit branch row emitted NON-pc-relative would make
/// the linker write the absolute target, and the CPU still adds `P`:
/// `P + (S + A) != S + A` whenever `P != 0`. REFUTABLE by design.
pub fn proof_call26_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);
    let intended = target.clone();
    let wrong = p.bvadd(target);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: CALL26/JUMP26 with dropped pc-relativity must REFUTE".to_string(),
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
// 2. R_AARCH64_PREL32 — 32-bit signed PC-relative data word
// ===========================================================================

/// Proof: an `R_AARCH64_PREL32` word decoded at `P` reaches `S + A`.
///
/// Theorem: forall S, A, P : BV64 . (P + ((S + A) - P)) == (S + A)
///
/// The linker writes `S + A - P` into the 32-bit word (psABI overflow check:
/// `-2^31 <= X < 2^32`); a consumer (EH tables, relative jump tables) adds
/// back the word's own address `P`. Same ring identity as the branch rows —
/// the field is data, not an instruction immediate, so there is no field-end
/// bias to bridge (unlike x86 `PC32`'s baked `-4`).
pub fn proof_prel32_word() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);
    let intended = target.clone();
    let reconstructed = p.clone().bvadd(target.bvsub(p));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_PREL32 word + P == S+A (PC-relative data)".to_string(),
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

/// Negative control: a PREL32 word consumed WITHOUT adding back its own
/// address yields the raw displacement `S + A - P != S + A` whenever
/// `P != 0`. REFUTABLE by design.
pub fn proof_prel32_missing_anchor_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);
    let intended = target.clone();
    let wrong = target.bvsub(p);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: PREL32 without the P anchor must REFUTE".to_string(),
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
// 3. R_AARCH64_ABS64 — absolute 64-bit pointer slot
// ===========================================================================

/// Proof: `R_AARCH64_ABS64` writes the intended absolute pointer `S + A`.
///
/// Theorem: forall S, A : BV64 . (A + S) == (S + A) — the same commutation
/// non-degeneracy as x86-64's `R_X86_64_64` lane: the emitted side is the
/// linker's word64 application order (explicit addend + resolved symbol).
pub fn proof_elf_aarch64_abs64() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);

    let intended = s.clone().bvadd(a.clone());
    let linker = a.bvadd(s);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_ABS64 == S + A (abs64 pointer slot)".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker,
        inputs: vec![("S".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: an abs64 slot emitted pc-relative computes `S + A - P`,
/// which differs from the intended absolute whenever `P != 0`. REFUTABLE.
pub fn proof_elf_aarch64_abs64_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let intended = s.clone().bvadd(a.clone());
    let wrong = a.bvadd(s).bvsub(p);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_ABS64 emitted pc-relative must REFUTE".to_string(),
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
// 4. R_AARCH64_ADR_PREL_PG_HI21 + R_AARCH64_ADD_ABS_LO12_NC — ADRP/ADD pair
// ===========================================================================

/// Proof: `R_AARCH64_ADR_PREL_PG_HI21` makes the ADRP land on `page(S + A)`.
///
/// Theorem: forall S, A, P : BV64 .
///   (page(P) + (page(S + A) - page(P))) == page(S + A)
///
/// The linker encodes the PAGE delta; the CPU adds its own page base. The
/// ELF twin of the Mach-O PAGE21 lane, with the Rela explicit addend.
pub fn proof_adr_prel_pg_hi21() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);
    let page_target = page(target);
    let page_p = page(p);

    let intended = page_target.clone();
    let reconstructed = page_p.clone().bvadd(page_target.bvsub(page_p));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_ADR_PREL_PG_HI21 ADRP == page(S+A)".to_string(),
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

/// Negative control: dropping the PAGE pc-relativity leaves
/// `page(P) + page(S+A) != page(S+A)` whenever `page(P) != 0`. REFUTABLE.
pub fn proof_adr_prel_pg_hi21_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);
    let page_target = page(target);

    let intended = page_target.clone();
    let wrong = page(p).bvadd(page_target);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: ADR_PREL_PG_HI21 with dropped pc-relativity must REFUTE".to_string(),
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

/// Proof: `R_AARCH64_ADD_ABS_LO12_NC` completes the ADRP/ADD pair: the ADD
/// contributes the low-12 page offset, recomposing the full `S + A`.
///
/// Theorem: forall S, A : BV64 .
///   (page(S + A) + ((S + A) & 0xFFF)) == (S + A)
///
/// A genuine mask-recomposition identity (the page mask and the low-12 mask
/// partition the address bits); a wrong mask on either side refutes
/// ([`proof_add_abs_lo12_wrong_mask_refutes`]).
pub fn proof_add_abs_lo12_pair() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);

    let target = s.bvadd(a);
    let intended = target.clone();
    let reconstructed = page(target.clone()).bvadd(target.bvand(mask12()));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_ADD_ABS_LO12_NC ADRP+ADD == S+A".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![("S".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: an 11-bit low mask loses address bit 11:
/// `page(S+A) + ((S+A) & 0x7FF) != S+A` whenever bit 11 of `S+A` is set.
/// REFUTABLE by design.
pub fn proof_add_abs_lo12_wrong_mask_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);

    let target = s.bvadd(a);
    let intended = target.clone();
    let wrong_mask = SmtExpr::bv_const(0x7FF, W);
    let wrong = page(target.clone()).bvadd(target.bvand(wrong_mask));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: ADD_ABS_LO12 with an 11-bit mask must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![("S".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 5. R_AARCH64_ADR_GOT_PAGE + R_AARCH64_LD64_GOT_LO12_NC — GOT-indirect pair
// ===========================================================================

/// Proof: `R_AARCH64_ADR_GOT_PAGE` makes the ADRP land on the GOT slot's
/// page, where `G` is the symbol's linker-resolved GOT-slot address (an
/// input, exactly as `S` is for the direct rows) and the addend is the
/// emitter-pinned zero (see the module header's G-row addend scope).
pub fn proof_adr_got_page() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = g.bvadd(a);
    let page_target = page(target);
    let page_p = page(p);

    let intended = page_target.clone();
    let reconstructed = page_p.clone().bvadd(page_target.bvsub(page_p));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_ADR_GOT_PAGE ADRP == page(G+A) (GOT slot page)".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("G".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `R_AARCH64_LD64_GOT_LO12_NC` completes the GOT pair: the LDR's
/// scaled page-offset field addresses exactly the GOT slot (bits [11:3] of
/// the offset; exact under the psABI's own 8-alignment check on the slot —
/// see the module header's formula-level scope).
///
/// Theorem: forall G, A : BV64 .
///   (page(G + A) + ((G + A) & 0xFFF)) == (G + A)
pub fn proof_ld64_got_lo12_pair() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);

    let target = g.bvadd(a);
    let intended = target.clone();
    let reconstructed = page(target.clone()).bvadd(target.bvand(mask12()));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_LD64_GOT_LO12_NC ADRP+LDR == G+A (GOT slot address)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![("G".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control for the GOT pair: masking the pc-relative delta instead
/// of the target (`(G+A-P) & 0xFFF`) breaks the recomposition whenever the
/// low 12 bits of `P` are nonzero. REFUTABLE by design.
pub fn proof_got_pair_wrong_pcrel_refutes() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = g.bvadd(a);
    let intended = target.clone();
    let wrong = page(target.clone()).bvadd(target.bvsub(p).bvand(mask12()));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: GOT LO12 masking a pc-relative delta must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![
            ("G".to_string(), W),
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

/// The 8 positive obligations covering every AArch64 ELF relocation kind the
/// emitter produces. Each must verify.
pub fn aarch64_elf_relocation_proofs() -> Vec<ProofObligation> {
    vec![
        proof_call26_bl_target(),
        proof_jump26_b_target(),
        proof_prel32_word(),
        proof_elf_aarch64_abs64(),
        proof_adr_prel_pg_hi21(),
        proof_add_abs_lo12_pair(),
        proof_adr_got_page(),
        proof_ld64_got_lo12_pair(),
    ]
}

/// Negative-control obligations (each is REFUTABLE — a wrong linker formula).
///
/// NOT registered as proofs (matching every precedent lane); this module's
/// `verify_by_evaluation` tests assert each is Invalid, demonstrating the
/// positive proofs are real equivalences.
pub fn aarch64_elf_relocation_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_call26_wrong_pcrel_refutes(),
        proof_prel32_missing_anchor_refutes(),
        proof_elf_aarch64_abs64_wrong_pcrel_refutes(),
        proof_adr_prel_pg_hi21_wrong_pcrel_refutes(),
        proof_add_abs_lo12_wrong_mask_refutes(),
        proof_got_pair_wrong_pcrel_refutes(),
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
    fn all_aarch64_elf_reloc_proofs_verify() {
        for obligation in aarch64_elf_relocation_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "AArch64 ELF relocation proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_aarch64_elf_reloc_negative_controls_refute() {
        for obligation in aarch64_elf_relocation_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "AArch64 ELF relocation NEGATIVE control '{}' should be Invalid \
                 (a wrong linker formula must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn aarch64_elf_reloc_proofs_are_non_degenerate() {
        for obligation in aarch64_elf_relocation_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "AArch64 ELF relocation proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
        }
    }

    #[test]
    fn aarch64_elf_reloc_proof_names_unique() {
        let mut names: Vec<String> = aarch64_elf_relocation_proofs()
            .iter()
            .chain(aarch64_elf_relocation_negative_controls().iter())
            .map(|p| p.name.clone())
            .collect();
        let before = names.len();
        names.sort();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate obligation names");
    }

    /// Every positive obligation must be structurally non-degenerate: the two
    /// sides must not be the identical expression (the #62 X==X class).
    #[test]
    fn positives_are_structurally_distinct() {
        for p in aarch64_elf_relocation_proofs() {
            assert_ne!(
                format!("{:?}", p.trust_ir_expr),
                format!("{:?}", p.aarch64_expr),
                "degenerate obligation: {}",
                p.name
            );
        }
    }

    /// Registry shape pins: 8 positives (one per emitted kind) and 6 negative
    /// controls, all named under the "ELF AArch64:" lane prefix.
    #[test]
    fn registry_shape() {
        let pos = aarch64_elf_relocation_proofs();
        let neg = aarch64_elf_relocation_negative_controls();
        assert_eq!(pos.len(), 8);
        assert_eq!(neg.len(), 6);
        for p in pos.iter().chain(neg.iter()) {
            assert!(
                p.name.starts_with("ELF AArch64:"),
                "lane prefix: {}",
                p.name
            );
        }
    }
}
