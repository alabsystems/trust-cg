// trust-cg-verify/aarch64_macho_tlvp_reloc_proofs.rs - SMT proofs for AArch64
// Mach-O TLVP (thread-local-variable descriptor) relocation selection/encoding.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sibling of `aarch64_macho_data_reloc_proofs.rs` (PAGE21/PAGEOFF12 data rows)
// and `aarch64_macho_call_reloc_proofs.rs` (BRANCH26 call row). This proves the
// AArch64 Mach-O Darwin TLV-descriptor access relocation rows — the
// `ARM64_RELOC_TLVP_LOAD_PAGE21` on the ADRP and `ARM64_RELOC_TLVP_LOAD_PAGEOFF12`
// on the LDR — emit the UNIQUE correct address reference to the thread-local
// variable's `tlv_descriptor` slot, mirroring the non-TLV PAGE21/PAGEOFF12 data
// proofs.
//
// What the relocations address. On Darwin/arm64 a `#[thread_local]` read lowers
// to (`isel.rs::select_tls_ref`, `TlsModel::Tlv`):
//
//     ADRP Xd, var@TLVPPAGE        ; ARM64_RELOC_TLVP_LOAD_PAGE21    (pcrel=1)
//     LDR  Xd, [Xd, var@TLVPPAGEOFF] ; ARM64_RELOC_TLVP_LOAD_PAGEOFF12 (pcrel=0)
//     ; (the loaded thunk fn-ptr is then called indirectly; that BLR semantics
//     ;  is modeled by a separate lane and is not a relocation row here.)
//
// The symbol `var` resolves (after the linker synthesizes the `__thread_vars`
// `tlv_descriptor`) to the runtime address `D` of that 3-pointer descriptor slot
// `{thunk, key, offset}`. The ADRP+LDR pair must reconstruct exactly `D` so the
// LDR loads the descriptor's first word (the thunk pointer). This is the SAME
// page+pageoff address arithmetic as a plain global read (`proof_page21_adrp_page`
// / `proof_pageoff12_add_full`); the ONLY difference is the relocation *type*
// number (`8`/`9` instead of `3`/`4`), which directs the linker to the
// TLV-descriptor symbol rather than the data symbol. The linker-applied bit
// arithmetic (PC-page subtraction on the pcrel=1 ADRP, raw low-12 mask on the
// pcrel=0 LDR) is byte-for-byte the PAGE21/PAGEOFF12 arithmetic.
//
// Technique mirrors `aarch64_macho_data_reloc_proofs.rs` (Alive2-style,
// PLDI 2021): encode the linker-applied + runtime-reconstructed formula as the
// `aarch64_expr` (the "emitted" side) and the intended descriptor-slot address as
// the `trust_ir_expr` (the "spec" side), then prove equivalence. Each obligation
// is NON-DEGENERATE (the two sides are structurally distinct), so a row with the
// WRONG `r_pcrel` REFUTES — exercised by the `*_wrong_*` negative controls and
// the unit tests.
//
// Linker + runtime formulas (canonical Mach-O ARM64 semantics, matching Apple
// `ld64` and LLVM `AArch64MachObjectWriter` / `RuntimeDyldMachOAArch64`).
// `page(x) = x & ~0xFFF` is the 4 KiB-page base. `D` is the resolved
// tlv_descriptor slot address, `A` the addend (0 for the descriptor read),
// `P` the runtime address of the ADRP (resp. LDR) instruction being relocated.
// The reference target is the descriptor slot `T = D + A`.
//
//   TLVP_LOAD_PAGE21 (r_pcrel=1, r_length=2), on the ADRP:
//       The linker writes the 21-bit field `imm = (page(T) - page(P)) >> 12`
//       into the ADRP immhi/immlo. At runtime ADRP computes
//           adrp_reg = page(P) + (imm << 12)
//                    = page(P) + (page(T) - page(P))
//                    = page(T).
//       The selection proof certifies the ADRP reconstructs `page(T)` (the
//       descriptor slot's page). Spec side: `page(T)`; emitted side:
//       `page(P) + (page(T) - page(P))`. The equality needs the ring identity
//       `p + (t - p) == t`, so it is a real equivalence, not `x == x`. A TLVP
//       PAGE21 row that drops the PC-page subtraction (`r_pcrel=0`) computes
//       `page(P) + page(T) != page(T)` for `page(P) != 0` — see
//       `proof_tlvp_page21_wrong_pcrel_refutes`.
//
//   TLVP_LOAD_PAGEOFF12 (r_pcrel=0, r_length=2), on the LDR:
//       The linker writes `imm12 = T & 0xFFF` (scaled into the LDR's unsigned
//       immediate field). The LDR's effective address is the ADRP base plus that
//       page offset:
//           full = adrp_reg + (T & 0xFFF)
//                = page(T) + (T & 0xFFF)
//                = T.
//       The selection proof certifies the ADRP+LDR pair addresses the full
//       descriptor slot `T = D + A`. Spec side: `T`; emitted side:
//       `page(T) + (T & 0xFFF)`. A TLVP PAGEOFF12 row that wrongly sets
//       `r_pcrel=1` would make the linker subtract the field PC `P` before
//       masking, yielding `page(T) + ((T - P) & 0xFFF) != T` in general — see
//       `proof_tlvp_pageoff12_wrong_pcrel_refutes`.
//
// Scope/soundness boundary. This lane proves the *relocation address
// arithmetic* of the TLVP descriptor access — the part that is identical in form
// to a verified global read and is therefore genuinely closeable today. It does
// does NOT certify the full Darwin TLV access. The backend now emits descriptor
// and initial-value sections plus the indirect thunk call, with an end-to-end
// link/run regression, but those facts do not turn this AY-backed arithmetic
// obligation into production Certified authority. The TLVP inventory rows stay
// fail-closed until an independently checked gate report is bound to the exact
// emitted object.
//
// Reference: <mach-o/arm64/reloc.h> (`ARM64_RELOC_TLVP_LOAD_PAGE21` = 8,
// `ARM64_RELOC_TLVP_LOAD_PAGEOFF12` = 9), LLVM `AArch64MachObjectWriter.cpp`,
// `RuntimeDyldMachOAArch64.h`.

//! SMT proofs for AArch64 Mach-O TLVP (thread-local descriptor) relocation
//! selection/encoding correctness.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on AArch64.
const W: u32 = 64;

/// Low-12-bit page offset mask `0xFFF`.
fn mask12() -> SmtExpr {
    SmtExpr::bv_const(0xFFF, W)
}

/// Page base mask `~0xFFF` (clears the low 12 bits).
fn not_mask12() -> SmtExpr {
    SmtExpr::bv_const(!0xFFFu64, W)
}

/// `page(x) = x & ~0xFFF`.
fn page(x: SmtExpr) -> SmtExpr {
    x.bvand(not_mask12())
}

// ===========================================================================
// 1. ARM64_RELOC_TLVP_LOAD_PAGE21 — ADRP page reconstruction (descriptor slot)
// ===========================================================================

/// Proof: `ARM64_RELOC_TLVP_LOAD_PAGE21` (pcrel=1) makes the ADRP reconstruct
/// `page(D+A)`, the page base of the thread-local `tlv_descriptor` slot.
///
/// Theorem: forall D, A, P : BV64 .
///   (page(P) + (page(D+A) - page(P))) == page(D+A)
///
/// The spec side (`trust_ir_expr`) is the intended ADRP result `page(D+A)` (the
/// descriptor slot's page). The emitted side (`aarch64_expr`) is the runtime
/// computation: the linker encodes the page delta `page(D+A) - page(P)` into the
/// ADRP immediate, and the CPU adds `page(P)` at execution. The equality requires
/// `p + (t - p) == t`, so it is a genuine equivalence (non-degenerate). Same form
/// as the non-TLV `proof_page21_adrp_page`; what differs is only the relocation
/// type the linker keys on (TLVP descriptor symbol vs. data symbol).
pub fn proof_tlvp_page21_adrp_page() -> ProofObligation {
    let d = SmtExpr::var("D", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = d.bvadd(a);
    let page_target = page(target);
    let page_p = page(p);

    // Spec: ADRP should land on the descriptor slot's page base.
    let intended = page_target.clone();
    // Emitted/runtime: page(P) + encoded page delta.
    let page_delta = page_target.bvsub(page_p.clone());
    let reconstructed = page_p.bvadd(page_delta);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: ARM64_RELOC_TLVP_LOAD_PAGE21 ADRP == page(D+A) (TLV descriptor page)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("D".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a TLVP_LOAD_PAGE21 row that (incorrectly) sets `r_pcrel=0`
/// would make the linker omit the PC-page subtraction, so the ADRP would land on
/// `page(P) + page(D+A)` instead of `page(D+A)`. That differs from the intended
/// descriptor-slot page base whenever `page(P) != 0`.
///
/// This obligation is intentionally REFUTABLE; the unit tests / AY lane assert it
/// is Invalid (a counterexample exists), demonstrating the positive TLVP PAGE21
/// proof is a real equivalence and not a tautology.
pub fn proof_tlvp_page21_wrong_pcrel_refutes() -> ProofObligation {
    let d = SmtExpr::var("D", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = d.bvadd(a);
    let page_target = page(target);
    let page_p = page(p);

    let intended = page_target.clone();
    // WRONG: pcrel=0 drops the `- page(P)` term, so the linker writes
    // `page(D+A) >> 12` and the CPU still adds page(P): page(P) + page(D+A).
    let wrong = page_p.bvadd(page_target);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: TLVP_LOAD_PAGE21 with wrong r_pcrel=0 must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![
            ("D".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 2. ARM64_RELOC_TLVP_LOAD_PAGEOFF12 — ADRP+LDR full descriptor-slot address
// ===========================================================================

/// Proof: `ARM64_RELOC_TLVP_LOAD_PAGEOFF12` (pcrel=0) on the LDR completes the
/// ADRP+LDR pair to address the full `tlv_descriptor` slot `D + A`.
///
/// Theorem: forall D, A : BV64 .
///   (page(D+A) + ((D+A) & 0xFFF)) == (D+A)
///
/// The spec side (`trust_ir_expr`) is the intended full descriptor-slot address
/// `D + A`. The emitted side (`aarch64_expr`) is the runtime computation: the
/// ADRP base holds `page(D+A)` (proven by `proof_tlvp_page21_adrp_page`), and the
/// linker writes `(D+A) & 0xFFF` into the LDR's unsigned-offset imm12, which the
/// CPU adds to form the load's effective address. The equality requires
/// `page(t) + (t & 0xFFF) == t` (a bit-decomposition identity), so it is a
/// genuine equivalence (non-degenerate).
pub fn proof_tlvp_pageoff12_ldr_full() -> ProofObligation {
    let d = SmtExpr::var("D", W);
    let a = SmtExpr::var("A", W);

    let target = d.bvadd(a);

    // Spec: the intended full descriptor-slot address.
    let intended = target.clone();
    // Emitted/runtime: ADRP base page(T) + LDR's page offset (T & 0xFFF).
    let page_target = page(target.clone());
    let page_offset = target.bvand(mask12());
    let reconstructed = page_target.bvadd(page_offset);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name:
            "MachO AArch64: ARM64_RELOC_TLVP_LOAD_PAGEOFF12 ADRP+LDR == D+A (TLV descriptor slot)"
                .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![("D".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a TLVP_LOAD_PAGEOFF12 row that (incorrectly) sets
/// `r_pcrel=1` would make the linker subtract the field PC `P` before masking, so
/// the LDR would offset the ADRP base by `(D+A-P) & 0xFFF` instead of
/// `(D+A) & 0xFFF`. The reconstructed address `page(D+A) + ((D+A-P) & 0xFFF)`
/// differs from the intended `D+A` in general (whenever the low 12 bits of `P`
/// are nonzero).
///
/// This obligation is intentionally REFUTABLE.
pub fn proof_tlvp_pageoff12_wrong_pcrel_refutes() -> ProofObligation {
    let d = SmtExpr::var("D", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = d.bvadd(a);

    let intended = target.clone();
    let page_target = page(target.clone());
    // WRONG: pcrel=1 masks `(T - P)` instead of `T`.
    let wrong_offset = target.bvsub(p).bvand(mask12());
    let wrong = page_target.bvadd(wrong_offset);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: TLVP_LOAD_PAGEOFF12 with wrong r_pcrel=1 must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![
            ("D".to_string(), W),
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

/// Collect the AArch64 Mach-O TLVP relocation selection/encoding proofs.
///
/// Returns the 2 positive obligations covering the TLV-descriptor access
/// relocation rows the AArch64 Mach-O emitter produces for a Darwin
/// `#[thread_local]` read (`ADRP`/`LDR` page+pageoff pair against the
/// `tlv_descriptor` symbol):
/// - TLVP_LOAD_PAGE21 (ADRP reconstructs `page(D+A)`),
/// - TLVP_LOAD_PAGEOFF12 (ADRP+LDR addresses the full descriptor slot `D+A`).
///
/// All must verify. These are page-arithmetic obligations only. The full Darwin
/// TLV path is emitted and regression-tested, but this AY-backed evidence is not
/// production Certified authority. The TLVP inventory rows remain fail-closed
/// until an independently checked gate report is bound to the exact object.
pub fn aarch64_macho_tlvp_relocation_proofs() -> Vec<ProofObligation> {
    vec![
        proof_tlvp_page21_adrp_page(),
        proof_tlvp_pageoff12_ldr_full(),
    ]
}

/// Negative-control obligations (each is REFUTABLE — a wrong encoding).
///
/// These are NOT registered as proofs; they are used by tests to demonstrate the
/// positive proofs are real equivalences (a malformed row is rejected).
pub fn aarch64_macho_tlvp_relocation_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_tlvp_page21_wrong_pcrel_refutes(),
        proof_tlvp_pageoff12_wrong_pcrel_refutes(),
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
    fn all_aarch64_tlvp_reloc_proofs_verify() {
        for obligation in aarch64_macho_tlvp_relocation_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "AArch64 Mach-O TLVP relocation proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_aarch64_tlvp_reloc_negative_controls_refute() {
        for obligation in aarch64_macho_tlvp_relocation_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "AArch64 Mach-O TLVP relocation NEGATIVE control '{}' should be Invalid \
                 (a wrong encoding must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn aarch64_tlvp_reloc_proofs_are_non_degenerate() {
        for obligation in aarch64_macho_tlvp_relocation_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "AArch64 Mach-O TLVP relocation proof '{}' is DEGENERATE (X==X); it proves nothing",
                obligation.name
            );
        }
    }

    #[test]
    fn aarch64_tlvp_reloc_proof_count_and_names_unique() {
        let proofs = aarch64_macho_tlvp_relocation_proofs();
        assert_eq!(proofs.len(), 2, "expected 2 TLVP relocation proofs");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate TLVP reloc proof names");
    }
}
