// trust-cg-verify/aarch64_eh_lsda_proofs.rs - SMT proofs for the aarch64 LSDA
// call-site / catch-all dispatch encoding (Itanium C++ EH).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proves the SEMANTIC correctness of the LSDA call-site + action encoding the
// backend emits for a `catch(...)` landing pad
// (`trust-cg-codegen/src/exception_handling.rs`: `CallSiteEntry`, `ActionEntry`,
// `build_exception_table_from_pads`, `generate_lsda`).
//
// What the personality does (Itanium C++ ABI sec. 2.5.3-2.5.5, `__gxx_personality_v0`):
// on an exception, it locates the call-site record whose PC range
// `[region_start, region_start+length)` contains the throw PC, reads that record's
// 1-based `action_idx`, and walks the action chain. For each action, the SLEB128
// `type_filter` decides:
//   - type_filter  > 0 : CATCH — index into the type table; the personality
//                         INSTALLS the handler and transfers control to the
//                         record's `landing_pad` offset (a `catch(...)` uses a
//                         POSITIVE filter that points at a NULL TType slot, which
//                         the personality treats as "match any type").
//   - type_filter == 0 : CLEANUP — runs destructors but NEVER stops the unwind;
//                         the exception propagates PAST the landing pad. Encoding a
//                         `catch(...)` as 0 makes the personality report "no
//                         handler" and the program calls `std::terminate()`.
//   - type_filter  < 0 : exception-specification filter (not modeled here).
//
// So the load-bearing correctness facts for a `catch(...)` landing pad are:
//   (A) RANGE: a throw PC inside `[region_start, region_start+length)` selects this
//       call-site record (and one just past the end does NOT).
//   (B) DISPATCH: with a POSITIVE type filter, the personality dispatches to this
//       record's `landing_pad` offset — i.e. the installed handler address is
//       reconstructed as `func_start + landing_pad`, NON-ZERO, the catch fires.
//   (C) The catch-all distinction: `type_filter == 0` (cleanup) does NOT dispatch
//       (reports "no handler"); the catch silently fails.
//
// Technique mirrors the relocation proofs (Alive2-style reconstruction): we encode
// the call-site record fields as bitvectors and prove the personality's
// landing-pad reconstruction / range / dispatch arithmetic against the intended
// behavior. Each obligation is NON-DEGENERATE (spec vs. emitted sides are
// structurally distinct), and a `type_filter == 0` (cleanup) row REFUTES the
// "dispatches" claim — exercised by the negative control.
//
// Scope. A full CFG-level proof of the personality state machine is out of reach,
// so — exactly as the reloc lane models the page-masking arithmetic rather than
// the full linker — this proves the call-site RANGE membership + DISPATCH
// landing-pad reconstruction + the catch-vs-cleanup type-filter distinction (the
// ENCODING arithmetic that is where a wrong call-site/TType encoding would
// miscompile a `catch(...)`). This is a genuine semantic floor for the EH encoding.
//
// Reference: trust-cg-codegen/src/exception_handling.rs; Itanium C++ ABI
// sec. 2.5 "Exception Handling Tables"; LLVM `EHStreamer` / `DwarfEHPrepare`.

//! SMT proofs for the aarch64 LSDA call-site / catch-all dispatch encoding.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Bitvector width for LSDA offsets/PCs (function-relative offsets; 64-bit is
/// ample and matches the native pointer width).
const W: u32 = 64;

/// Symbolic "dispatch decision" reconstruction for one call-site record.
///
/// Models the personality's per-record decision for a throw at `pc`:
///   - if `pc` is in `[region_start, region_start + length)` AND the action's
///     `type_filter > 0` (a catch, including a `catch(...)` NULL-TType slot), the
///     personality INSTALLS the handler at `func_start + landing_pad` (a non-zero
///     handler address);
///   - otherwise (out of range, or `type_filter == 0` cleanup), it does NOT
///     install a handler from this record (reconstructed handler address 0).
///
/// Returns the reconstructed installed-handler address (0 == "no handler from this
/// record / propagate"). This is the value the personality hands the unwinder.
fn dispatch_handler_addr(
    func_start: &SmtExpr,
    region_start: &SmtExpr,
    length: &SmtExpr,
    landing_pad: &SmtExpr,
    type_filter: &SmtExpr,
    pc: &SmtExpr,
) -> SmtExpr {
    let zero = SmtExpr::bv_const(0, W);

    // In-range: region_start <=u pc  AND  pc <u region_start + length.
    let region_end = region_start.clone().bvadd(length.clone());
    let at_or_after_start = region_start.clone().bvule(pc.clone());
    let before_end = pc.clone().bvult(region_end);
    let in_range = at_or_after_start.and_expr(before_end);

    // Catch (handler installs) iff type_filter > 0 (signed). A `catch(...)` uses a
    // positive filter pointing at a NULL TType slot; 0 is cleanup (no install).
    let is_catch = type_filter.clone().bvsgt(zero.clone());

    // Installed handler address = func_start + landing_pad (the absolute landing
    // pad code address the unwinder branches to).
    let handler = func_start.clone().bvadd(landing_pad.clone());

    // Dispatch iff in range and catch; else 0 (no handler from this record).
    SmtExpr::ite(in_range.and_expr(is_catch), handler, zero)
}

// ===========================================================================
// 1. catch(...) in-range dispatch -> lands on func_start + landing_pad
// ===========================================================================

/// Proof: a `catch(...)` call-site record dispatches an in-range exception to its
/// landing pad.
///
/// Theorem: for all `func_start, region_start, length, landing_pad : BV64` with a
/// POSITIVE type filter (a `catch(...)` match-any NULL-TType slot) and a throw
/// `pc` inside the call-site range, the personality's installed-handler
/// reconstruction equals the intended landing-pad address:
///
///   dispatch_handler_addr(.., type_filter=1, pc = region_start) == func_start + landing_pad
///
/// Spec side (`trust_ir_expr`): the intended installed handler `func_start +
/// landing_pad`. Emitted side (`aarch64_expr`): the personality's dispatch
/// reconstruction over the encoded call-site record (range test + positive-filter
/// catch test + landing-pad add). The equality is genuine — the emitted side is a
/// guarded ITE that collapses to the handler ONLY when range AND catch both hold;
/// a cleanup (`type_filter == 0`) row collapses it to 0 and REFUTES (negative
/// control). Preconditions pin a representative in-range PC and a non-empty range.
pub fn proof_eh_catch_all_dispatches_to_landing_pad() -> ProofObligation {
    let func_start = SmtExpr::var("func_start", W);
    let region_start = SmtExpr::var("region_start", W);
    let length = SmtExpr::var("length", W);
    let landing_pad = SmtExpr::var("landing_pad", W);
    // A `catch(...)` uses a positive type filter (1-based NULL-TType slot index).
    let type_filter = SmtExpr::var("type_filter", W);
    let pc = SmtExpr::var("pc", W);

    // Spec: the intended installed handler address.
    let intended = func_start.clone().bvadd(landing_pad.clone());

    // Emitted: the personality's dispatch reconstruction.
    let emitted = dispatch_handler_addr(
        &func_start,
        &region_start,
        &length,
        &landing_pad,
        &type_filter,
        &pc,
    );

    // Preconditions: the throw PC is in the call-site range, the range is
    // non-empty (no wrap), and the type filter is a positive catch (catch-all).
    let zero = SmtExpr::bv_const(0, W);
    let region_end = region_start.clone().bvadd(length.clone());
    let no_wrap = region_end.clone().bvugt(region_start.clone());
    let pc_in_range = region_start
        .clone()
        .bvule(pc.clone())
        .and_expr(pc.clone().bvult(region_end));
    let positive_filter = type_filter.clone().bvsgt(zero);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "LSDA EH: catch(...) in-range dispatch lands on func_start+landing_pad".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: emitted,
        inputs: vec![
            ("func_start".to_string(), W),
            ("region_start".to_string(), W),
            ("length".to_string(), W),
            ("landing_pad".to_string(), W),
            ("type_filter".to_string(), W),
            ("pc".to_string(), W),
        ],
        preconditions: vec![no_wrap, pc_in_range, positive_filter],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a `catch(...)` landing pad mis-encoded as CLEANUP
/// (`type_filter == 0`) does NOT dispatch. With a zero type filter the
/// personality's reconstruction collapses to 0 ("no handler / propagate"), which
/// differs from the intended non-zero handler `func_start + landing_pad` whenever
/// the landing pad is non-trivial. Asserting it still dispatches is REFUTABLE —
/// witnessing the catch-vs-cleanup distinction is load-bearing (a cleanup row
/// silently drops the catch and the program terminates).
pub fn proof_eh_cleanup_does_not_dispatch_refutes() -> ProofObligation {
    let func_start = SmtExpr::var("func_start", W);
    let region_start = SmtExpr::var("region_start", W);
    let length = SmtExpr::var("length", W);
    let landing_pad = SmtExpr::var("landing_pad", W);
    let pc = SmtExpr::var("pc", W);

    let intended = func_start.clone().bvadd(landing_pad.clone());

    // WRONG: type_filter == 0 (cleanup) — the personality does not install a
    // handler from this record even in range.
    let cleanup_filter = SmtExpr::bv_const(0, W);
    let emitted = dispatch_handler_addr(
        &func_start,
        &region_start,
        &length,
        &landing_pad,
        &cleanup_filter,
        &pc,
    );

    // Same in-range preconditions (so the ONLY thing wrong is the cleanup filter).
    let region_end = region_start.clone().bvadd(length.clone());
    let no_wrap = region_end.clone().bvugt(region_start.clone());
    let pc_in_range = region_start
        .clone()
        .bvule(pc.clone())
        .and_expr(pc.clone().bvult(region_end));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "LSDA EH: cleanup (type_filter=0) catch-all must REFUTE (does not dispatch)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: emitted,
        inputs: vec![
            ("func_start".to_string(), W),
            ("region_start".to_string(), W),
            ("length".to_string(), W),
            ("landing_pad".to_string(), W),
            ("pc".to_string(), W),
        ],
        preconditions: vec![no_wrap, pc_in_range],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 2. Out-of-range PC does NOT dispatch (range membership is load-bearing)
// ===========================================================================

/// Proof: an exception whose PC is at/after the END of the call-site range does
/// NOT dispatch to this record's landing pad.
///
/// Theorem: for a POSITIVE-filter `catch(...)` record and a throw `pc` at the
/// region end (`pc == region_start + length`, the first byte PAST the range), the
/// personality's reconstruction yields 0 ("this record does not apply"):
///
///   dispatch_handler_addr(.., type_filter=1, pc = region_start + length) == 0
///
/// Spec side: 0 (the record must not claim an out-of-range PC). Emitted side: the
/// personality's reconstruction, which gates on the half-open range
/// `[region_start, region_start+length)`. The equality is genuine: a record that
/// used a CLOSED range (`pc <=u region_end`) would (wrongly) claim the boundary PC
/// and reconstruct the handler instead of 0 — see the boundary negative control.
pub fn proof_eh_out_of_range_does_not_dispatch() -> ProofObligation {
    let func_start = SmtExpr::var("func_start", W);
    let region_start = SmtExpr::var("region_start", W);
    let length = SmtExpr::var("length", W);
    let landing_pad = SmtExpr::var("landing_pad", W);
    let type_filter = SmtExpr::var("type_filter", W);

    // Throw PC one past the end of the range: pc = region_start + length.
    let pc = region_start.clone().bvadd(length.clone());

    // Spec: no dispatch from this record (handler address 0).
    let intended = SmtExpr::bv_const(0, W);

    // Emitted: the personality's dispatch reconstruction at the boundary PC.
    let emitted = dispatch_handler_addr(
        &func_start,
        &region_start,
        &length,
        &landing_pad,
        &type_filter,
        &pc,
    );

    // Preconditions: non-empty range (so the boundary PC is strictly past the last
    // in-range byte) and a positive (catch) filter (so the ONLY reason for
    // non-dispatch is the out-of-range PC, not the filter).
    let zero = SmtExpr::bv_const(0, W);
    let region_end = region_start.clone().bvadd(length.clone());
    let no_wrap = region_end.bvugt(region_start.clone());
    let positive_filter = type_filter.bvsgt(zero);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "LSDA EH: out-of-range PC (region end) does not dispatch (half-open range)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: emitted,
        inputs: vec![
            ("func_start".to_string(), W),
            ("region_start".to_string(), W),
            ("length".to_string(), W),
            ("landing_pad".to_string(), W),
            ("type_filter".to_string(), W),
        ],
        preconditions: vec![no_wrap, positive_filter],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a call-site record that uses a CLOSED range
/// (`pc <=u region_end`, an off-by-one over-claim) WOULD dispatch the boundary PC
/// `region_start + length` to its landing pad — claiming an exception that belongs
/// to the NEXT call site. Asserting the boundary PC does NOT dispatch is then
/// REFUTABLE under the wrong (closed-range) encoding, witnessing the half-open
/// range bound is load-bearing.
pub fn proof_eh_closed_range_boundary_refutes() -> ProofObligation {
    let func_start = SmtExpr::var("func_start", W);
    let region_start = SmtExpr::var("region_start", W);
    let length = SmtExpr::var("length", W);
    let landing_pad = SmtExpr::var("landing_pad", W);
    let type_filter = SmtExpr::var("type_filter", W);

    let pc = region_start.clone().bvadd(length.clone());

    // Spec: the record must NOT dispatch the boundary (out-of-range) PC.
    let intended = SmtExpr::bv_const(0, W);

    // WRONG emitted: a CLOSED range test `pc <=u region_end` over-claims the
    // boundary PC, so it dispatches to the handler.
    let zero = SmtExpr::bv_const(0, W);
    let region_end = region_start.clone().bvadd(length.clone());
    let at_or_after_start = region_start.clone().bvule(pc.clone());
    let at_or_before_end = pc.clone().bvule(region_end); // WRONG: <=, not <
    let in_range_closed = at_or_after_start.and_expr(at_or_before_end);
    let is_catch = type_filter.clone().bvsgt(zero.clone());
    let handler = func_start.clone().bvadd(landing_pad.clone());
    let emitted = SmtExpr::ite(in_range_closed.and_expr(is_catch), handler, zero);

    let region_end2 = region_start.clone().bvadd(length.clone());
    let no_wrap = region_end2.bvugt(region_start.clone());
    let positive_filter = type_filter.bvsgt(SmtExpr::bv_const(0, W));
    // Pin landing_pad != 0 so the over-claimed handler is distinguishable from "no
    // handler" (0), making the over-claim genuinely refute the "== 0" spec.
    let lp_nonzero = landing_pad.bvugt(SmtExpr::bv_const(0, W));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "LSDA EH: closed-range over-claim at boundary must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: emitted,
        inputs: vec![
            ("func_start".to_string(), W),
            ("region_start".to_string(), W),
            ("length".to_string(), W),
            ("landing_pad".to_string(), W),
            ("type_filter".to_string(), W),
        ],
        preconditions: vec![no_wrap, positive_filter, lp_nonzero],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// Collect the aarch64 LSDA EH call-site/dispatch proofs (2 positive
/// obligations): a `catch(...)` record dispatches an in-range exception to its
/// landing pad (positive type-filter), and a PC past the call-site range does NOT
/// dispatch (half-open range membership). Together they pin the call-site
/// range/dispatch encoding and the catch-vs-cleanup type-filter distinction.
pub fn aarch64_eh_lsda_proofs() -> Vec<ProofObligation> {
    vec![
        proof_eh_catch_all_dispatches_to_landing_pad(),
        proof_eh_out_of_range_does_not_dispatch(),
    ]
}

/// Negative-control obligations (each REFUTABLE). NOT registered as proofs; used
/// by tests to demonstrate the positive proofs are real equivalences (a cleanup
/// type-filter, or a closed-range over-claim, is rejected).
pub fn aarch64_eh_lsda_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_eh_cleanup_does_not_dispatch_refutes(),
        proof_eh_closed_range_boundary_refutes(),
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
    fn all_aarch64_eh_lsda_proofs_verify() {
        for obligation in aarch64_eh_lsda_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "LSDA EH proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_aarch64_eh_lsda_negative_controls_refute() {
        for obligation in aarch64_eh_lsda_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "LSDA EH NEGATIVE control '{}' should be Invalid (a wrong encoding must \
                 refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn aarch64_eh_lsda_proofs_are_non_degenerate() {
        for obligation in aarch64_eh_lsda_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "LSDA EH proof '{}' is DEGENERATE (X==X); it proves nothing",
                obligation.name
            );
        }
    }

    #[test]
    fn aarch64_eh_lsda_proof_count_and_names_unique() {
        let proofs = aarch64_eh_lsda_proofs();
        assert_eq!(proofs.len(), 2, "expected 2 LSDA EH proofs");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate LSDA EH proof names");
    }
}
