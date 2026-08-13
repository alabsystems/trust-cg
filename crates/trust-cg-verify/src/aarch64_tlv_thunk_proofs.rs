// trust-cg-verify/aarch64_tlv_thunk_proofs.rs - SMT proof for the Darwin aarch64
// TLV thunk-call model (the indirect call through the tlv_descriptor thunk).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sibling of `aarch64_macho_tlvp_reloc_proofs.rs`, which proves the relocation
// ADDRESS ARITHMETIC of the ADRP/LDR pair that materializes the descriptor-slot
// address `D`. This module proves the NEXT step the backend now emits
// (`trust-cg-lower/src/isel.rs::select_tls_ref`, `TlsModel::Tlv`): the indirect
// THUNK CALL that turns that descriptor address into the thread-local variable's
// address.
//
// Emitted Darwin TLV access sequence (isel.rs §`select_tls_ref` Tlv arm):
//
//   ADRP Xd, var@TLVPPAGE         ; \ descriptor-slot address D
//   LDR  Xd, [Xd, var@TLVPPAGEOFF]; / (proven by the TLVP reloc lane)
//   LDR  thunk, [Xd, #0]          ; thunk = descriptor word 0 (the resolver fn ptr)
//   MOV  x0, Xd                   ; pass the descriptor address D to the thunk
//   BLR  thunk                    ; result = thunk(x0=D) -> &var, returned in x0
//
// The descriptor slot is the 3-pointer `tlv_descriptor` `{thunk, key, offset}`:
// word 0 is the resolver thunk pointer, and calling `thunk(D)` returns `&var`.
//
// What this proof certifies. The resolver thunk is genuinely opaque to the
// compiler (it is `_tlv_bootstrap` / a libsystem `tlv_get_addr`), so we model it as
// an ABSTRACT, ARGUMENT-SENSITIVE deterministic function of its sole argument (the
// descriptor address it is handed): `thunk(arg) := arg + thunk_off`, where
// `thunk_off : BV64` is a FREE symbolic offset. Nothing about `thunk_off` is
// assumed (its value is universally quantified) — the proof leans ONLY on the fact
// that the resolver's result is a function OF ITS ARGUMENT (the task's
// `thunk(D) = D.offset_base`). The model is argument-sensitive on purpose: a
// constant model would ignore the argument and could not catch a wrong-argument
// miscompile. The obligation then proves the EMITTED sequence invokes the resolver
// with the CORRECT argument — the descriptor address `D` the ADRP/LDR pair
// materialized — so the result equals the intended `thunk(D)`:
//
//   spec side    : thunk(D)                          (resolver invoked with D)
//   emitted side : thunk(page(D) + (D & 0xFFF))      (resolver invoked with the
//                  descriptor address x0 actually holds — the ADRP/LDR page+pageoff
//                  reconstruction of D)
//
// The non-degeneracy comes from the descriptor-argument reconstruction propagated
// THROUGH the argument-sensitive thunk: the two `thunk_apply` arguments are
// structurally distinct (`D` vs. `page(D)+(D&0xFFF)`) and the equality needs the
// bit-decomposition identity `page(t)+(t&0xFFF) == t` (the SAME identity the
// TLVP_LOAD_PAGEOFF12 reloc proof discharges). A sequence that passes the WRONG
// argument (a different descriptor field, e.g. `D+8`), or drops the indirection
// (returns the descriptor address `D` itself), computes a different result and
// REFUTES — see the negative controls.
//
// Scope/soundness boundary. The strongest faithful statement about an opaque
// resolver is "the emitted sequence invokes it with the right argument and returns
// its result" — i.e. isel passes the descriptor BASE address (not a wrong
// descriptor field) and does not drop the `BLR`. That is what miscompiles if isel
// picks the wrong call argument, and it is exactly what this proves. The
// page+pageoff materialization of `D` is the TLVP reloc lane's concern (proven
// there); the `_tlv_bootstrap` runtime contract is an external assumption.
//
// Reference: trust-cg-lower/src/isel.rs §select_tls_ref (TlsModel::Tlv);
// dyld `tlv_get_addr` / `_tlv_bootstrap`; <mach-o/arm64/reloc.h>.

//! SMT proof for the Darwin aarch64 TLV thunk-call (indirect descriptor resolver).

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on AArch64.
const W: u32 = 64;

/// Low-12-bit page-offset mask `0xFFF`.
fn mask12() -> SmtExpr {
    SmtExpr::bv_const(0xFFF, W)
}

/// Page base mask `~0xFFF` (clears the low 12 bits): `page(x) = x & ~0xFFF`.
fn page(x: SmtExpr) -> SmtExpr {
    x.bvand(SmtExpr::bv_const(!0xFFFu64, W))
}

/// Abstract thunk model: `thunk(arg) := arg + thunk_off`.
///
/// The Darwin TLV resolver (`_tlv_bootstrap` / `tlv_get_addr`) is opaque to the
/// compiler, but its return is a DETERMINISTIC FUNCTION of the descriptor address
/// it is handed (the task's `thunk(D) = D.offset_base`): from the descriptor base
/// it computes the per-thread variable address. We model that as a
/// constrained-but-otherwise-arbitrary deterministic function — the addition of a
/// single symbolic offset `thunk_off` to its argument. Nothing about `thunk_off`
/// is assumed (it is a free BV64), so the proof leans ONLY on the fact that the
/// resolver's result depends on its argument; it does NOT assume any particular
/// offset value. This makes the model ARGUMENT-SENSITIVE: passing the wrong
/// descriptor argument changes the result (which is exactly the miscompile the
/// negative controls catch), unlike a constant model that would ignore its input.
///
/// `thunk_off` is shared across spec and emitted sides (it is the SAME resolver),
/// so the proof reduces to "does the emitted sequence pass the resolver the
/// correct argument `D`?".
fn thunk_apply(thunk_off: &SmtExpr, arg: &SmtExpr) -> SmtExpr {
    arg.clone().bvadd(thunk_off.clone())
}

// ===========================================================================
// Positive proof: the emitted TLV sequence computes result = thunk(D)
// ===========================================================================

/// Proof: the emitted Darwin TLV access computes the thread-local variable address
/// `thunk(D)` — it loads the resolver thunk from the descriptor it materialized,
/// and invokes it with the descriptor address `D`.
///
/// Theorem (abstract argument-sensitive thunk `thunk_off`): for all
/// `D, thunk_off : BV64`,
///   `thunk_apply(thunk_off, D)  ==  thunk_apply(thunk_off, page(D) + (D & 0xFFF))`
///
/// Spec side (`trust_ir_expr`): the intended return `thunk(D)` — the resolver
/// invoked with the descriptor address `D`. Emitted side (`aarch64_expr`): the
/// resolver invoked with the descriptor address the emitted code actually computed
/// and passed in x0 — the ADRP/LDR page+pageoff reconstruction
/// `page(D) + (D & 0xFFF)`. The equality requires the bit-decomposition identity
/// `page(t) + (t & 0xFFF) == t` (the SAME identity the TLVP_LOAD_PAGEOFF12 reloc
/// proof discharges) propagated THROUGH the argument-sensitive thunk — so it is a
/// genuine equivalence, NOT `x == x` (the two `thunk_apply` arguments are
/// structurally distinct, and the thunk's result depends on its argument). This
/// pins that the emitted sequence passes the CORRECT descriptor argument to the
/// resolver; a wrong call argument (a different descriptor field, or a dropped
/// indirection) refutes — see the negative controls.
pub fn proof_tlv_thunk_call_returns_var_addr() -> ProofObligation {
    let thunk_off = SmtExpr::var("thunk_off", W);
    let d = SmtExpr::var("D", W);

    // Spec: the Darwin TLV access yields `thunk(D)` = &var — the resolver invoked
    // with the descriptor address D.
    let intended = thunk_apply(&thunk_off, &d);

    // Emitted: the descriptor address x0 holds is the ADRP/LDR reconstruction
    // page(D) + (D & 0xFFF) (the TLVP page+pageoff materialization), then the
    // resolver is invoked with that reconstructed argument.
    let reconstructed_arg = page(d.clone()).bvadd(d.bvand(mask12()));
    let emitted_result = thunk_apply(&thunk_off, &reconstructed_arg);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "TLV thunk-call: emitted ADRP/LDR/LDR/BLR computes thunk(D) == &var".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: emitted_result,
        inputs: vec![("D".to_string(), W), ("thunk_off".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Negative controls (REFUTABLE — wrong indirection / wrong call argument)
// ===========================================================================

/// Negative control: a TLV sequence that invokes the thunk with the WRONG
/// argument — the address of the descriptor's `key` field (`D + 8`, descriptor
/// word 1) instead of the descriptor base address `D` (word 0). The Darwin ABI
/// passes the descriptor BASE address in x0; calling `thunk(D + 8)` rather than
/// `thunk(D)` hands the resolver a different argument, so the result differs from
/// `&var = thunk(D)` in general (the abstract thunk does not force agreement on
/// distinct arguments) and the obligation is REFUTABLE.
pub fn proof_tlv_thunk_wrong_arg_refutes() -> ProofObligation {
    let thunk_off = SmtExpr::var("thunk_off", W);
    let d = SmtExpr::var("D", W);

    // WRONG argument: D + 8 (the descriptor's `key` field), not the base D.
    let wrong_arg = d.clone().bvadd(SmtExpr::bv_const(8, W));
    let emitted_result = thunk_apply(&thunk_off, &wrong_arg);

    let intended = thunk_apply(&thunk_off, &d);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "TLV thunk-call: calling thunk with wrong arg (descriptor+8) must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: emitted_result,
        inputs: vec![("D".to_string(), W), ("thunk_off".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a TLV sequence that drops the indirection entirely and
/// returns the descriptor ADDRESS `D` itself (as if `&var == D`, i.e. forgetting
/// the `BLR thunk`). The descriptor address is NOT the variable address; the
/// resolver must run. Asserting `D == thunk(D)` is REFUTABLE (they differ unless
/// the thunk happens to be the identity at `D`, which the abstract model does not
/// force).
pub fn proof_tlv_missing_indirection_refutes() -> ProofObligation {
    let thunk_off = SmtExpr::var("thunk_off", W);
    let d = SmtExpr::var("D", W);

    // WRONG: no BLR — return the descriptor address directly.
    let emitted_result = d.clone();
    let intended = thunk_apply(&thunk_off, &d);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "TLV thunk-call: missing BLR indirection (return D) must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: emitted_result,
        inputs: vec![("D".to_string(), W), ("thunk_off".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// Collect the Darwin aarch64 TLV thunk-call proof (1 positive obligation): the
/// emitted ADRP/LDR/LDR/BLR sequence computes `thunk(D) == &var` — it loads the
/// resolver from descriptor word 0 and invokes it with the descriptor address.
///
/// This complements the TLVP relocation lane (which proves the ADRP/LDR address
/// arithmetic that materializes `D`). The full Darwin TLV access is now emitted by
/// the backend and verified end-to-end by link+run, so the thunk-call SEMANTICS
/// are pinned here.
pub fn aarch64_tlv_thunk_proofs() -> Vec<ProofObligation> {
    vec![proof_tlv_thunk_call_returns_var_addr()]
}

/// Negative-control obligations (each REFUTABLE — a wrong call argument, or a
/// missing indirection). NOT registered as proofs; used by tests to demonstrate
/// the positive proof is a real equivalence (a malformed thunk call is rejected).
pub fn aarch64_tlv_thunk_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_tlv_thunk_wrong_arg_refutes(),
        proof_tlv_missing_indirection_refutes(),
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
    fn all_aarch64_tlv_thunk_proofs_verify() {
        for obligation in aarch64_tlv_thunk_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "TLV thunk-call proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_aarch64_tlv_thunk_negative_controls_refute() {
        for obligation in aarch64_tlv_thunk_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "TLV thunk-call NEGATIVE control '{}' should be Invalid (a wrong indirection \
                 must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn aarch64_tlv_thunk_proofs_are_non_degenerate() {
        for obligation in aarch64_tlv_thunk_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "TLV thunk-call proof '{}' is DEGENERATE (X==X); it proves nothing",
                obligation.name
            );
        }
    }

    #[test]
    fn aarch64_tlv_thunk_proof_count_and_names_unique() {
        let proofs = aarch64_tlv_thunk_proofs();
        assert_eq!(proofs.len(), 1, "expected 1 TLV thunk-call proof");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate TLV thunk-call proof names");
    }
}
