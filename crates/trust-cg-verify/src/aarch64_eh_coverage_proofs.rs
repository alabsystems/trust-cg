// trust-cg-verify/aarch64_eh_coverage_proofs.rs - SMT proofs for the aarch64 LSDA
// call-site TABLE COVERAGE / PARTITION property (Itanium C++ EH).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// What this proves, and WHY the abstract dispatch proof needs it
// ===========================================================================
// The sibling module `aarch64_eh_lsda_proofs.rs` proves the personality's
// per-record dispatch over SYMBOLIC `region_start / length / landing_pad`: given
// a record whose half-open range contains the throw PC, the catch dispatches to
// `func_start + landing_pad`. That proof ASSUMES a record EXISTS for the PC —
// it never proves the call-site TABLE actually covers the PC.
//
// That coverage assumption is load-bearing and was the root cause of a real
// backend bug during development: a cleanup / `_Unwind_Resume` PC fell in an
// UNCOVERED call-site region, so the Itanium personality
// (`__gxx_personality_v0`, libcxxabi `scan_eh_table`) found no matching record,
// did NOT continue unwinding, and called `std::terminate()`
// (cxa_personality.cpp lines 908-913 / 918-920). The fix
// (`trust-cg-codegen/src/pipeline.rs::resolve_eh_offsets`) binds the semantic
// Invoke to its exact final four-byte BL/BLR instruction and synthesizes
// clang-style filler "continue-unwind"
// (`landing_pad == 0`, `action_idx == 0`) call-site entries that cover every
// gap in `[0, code_len)` and the tail, then re-sorts by `start_offset`.
//
// This module certifies the INVARIANT that filler synthesis establishes — the
// invariant the dispatch proof assumes:
//
//   (1) TOTAL COVERAGE / PARTITION. For the resolved call-site table over a
//       function of length `code_len`, every `pc` in `[0, code_len)` falls in
//       EXACTLY ONE half-open call-site region `[start_i, start_i + len_i)` —
//       the regions are contiguous, with no gap and no overlap. (No gap =>
//       the personality never terminates on an in-flight PC; no overlap =>
//       `scan_eh_table` selects a single record.)
//
//   (2) INVOKE -> PAD MAPPING. The region containing an Invoke call's PC has the
//       Invoke's own landing-pad offset (non-zero), NOT 0 / "no handler". A
//       filler `landing_pad == 0` over an Invoke PC is exactly the
//       cleanup-PC-terminate bug; the explicit throwing region must win.
//
// ===========================================================================
// Grounding: this mirrors the REAL `resolve_eh_offsets` output shape
// ===========================================================================
// `resolve_eh_offsets` produces, for a function with a single protected Invoke
// instruction at byte range `[r, r + 4)`:
//
//   * the explicit throwing region `[r, r + 4)` with `landing_pad == pad`,
//     derived from the arena-stable final BL/BLR `InstId` and the encoder's
//     executable fixed-width (one instruction == one 4-byte word) contract;
//   * a HEAD filler `[0, r)` for the gap before the first explicit region
//     (`start > cursor` => filler `[cursor, start)`, cursor initially 0);
//   * a TAIL filler `[r + 4, code_len)` after the exact call, both fillers
//     carrying `landing_pad_block = None` (=> `lp_offset == 0`, so no action
//     chain is derived);
//   * the canonical table emitted in monotonically increasing start order.
//
// The model below keeps `r` and `pad` symbolic but constrains `L == 4`, matching
// the production encoder's exact fixed-width call range. This constraint is
// deliberately part of every positive obligation: a merely in-bounds symbolic
// `L` would also admit the old, unsound whole-block protection. The half-open
// `[start, start+len)` membership and filler `landing_pad == 0` semantics are
// exactly what the personality and dispatch proof consume. The executable
// codegen tests additionally bind `r` to the final call's InstId and reject
// whole-block, missing, ambiguous, stale, overlapping, or sentinel-zero
// metadata.
//
// Negative controls (REFUTE): dropping the tail filler (a GAP `[r+L, code_len)`)
// leaves the PCs in that gap uncovered — refutes TOTAL COVERAGE (the literal
// terminate bug); and a filler `landing_pad == 0` placed over the Invoke PC
// refutes INVOKE->PAD (the cleanup-PC-terminate bug). Each is a genuine AY
// CounterExample, witnessing the positive proofs are real.
//
// Reference: trust-cg-codegen/src/pipeline.rs::resolve_eh_offsets;
// trust-cg-codegen/src/exception_handling.rs
// (`CallSiteEntry`, `build_exception_table_from_pads`); Itanium C++ ABI
// sec. 2.5 "Exception Handling Tables"; libcxxabi `scan_eh_table`.

//! SMT proofs for the aarch64 LSDA call-site table coverage / partition property.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Bitvector width for LSDA offsets / PCs. `resolve_eh_offsets` works in
/// `u32` byte offsets (`EhCallSiteEntry.start_offset` / `length`); 32 bits
/// models that exactly while keeping the bounded `forall pc` query tractable.
const W: u32 = 32;

/// Concrete function length used to bound the `forall pc in [0, code_len)`
/// unrolling. AArch64 instructions are 4 bytes, so a 24-byte body is six
/// instructions — a small, representative single-Invoke function whose
/// coverage the bounded quantifier can enumerate exactly (well under the
/// 256-iteration unroll limit). The region start and pad remain symbolic while
/// the proof preconditions pin the production call width to `L = 4`.
const CODE_LEN: u64 = 24;

/// One reconstructed call-site table entry: a half-open byte range
/// `[start, start + len)` and its landing-pad offset (0 == filler /
/// "continue unwinding"). This mirrors the `(start_offset, length, lp_offset)`
/// triple `generate_lsda_for_function` feeds the personality.
struct Entry {
    start: SmtExpr,
    len: SmtExpr,
    /// Landing-pad offset; 0 for a filler (`landing_pad_block == None`).
    landing_pad: SmtExpr,
}

impl Entry {
    /// `start <=u pc  AND  pc <u start + len` — the half-open membership test the
    /// Itanium personality uses (`scan_eh_table`), identical to
    /// `aarch64_eh_lsda_proofs::dispatch_handler_addr`'s in-range gate.
    fn covers(&self, pc: &SmtExpr) -> SmtExpr {
        let end = self.start.clone().bvadd(self.len.clone());
        let at_or_after_start = self.start.clone().bvule(pc.clone());
        let before_end = pc.clone().bvult(end);
        at_or_after_start.and_expr(before_end)
    }

    /// `ite(covers(pc), 1, 0)` as a `W`-bit count contribution.
    fn cover_indicator(&self, pc: &SmtExpr) -> SmtExpr {
        SmtExpr::ite(
            self.covers(pc),
            SmtExpr::bv_const(1, W),
            SmtExpr::bv_const(0, W),
        )
    }
}

/// Reconstruct the three-entry table shape `resolve_eh_offsets` emits for a
/// single-Invoke function: HEAD filler `[0, r)`, explicit throwing
/// region `[r, r + L)` (landing pad `pad`), TAIL filler `[r + L, code_len)`.
///
/// `r`, `L`, `pad` are symbolic; production derives `r` from the final call's
/// arena-stable InstId and fixes `L = 4`. `code_len` is the concrete total code
/// length. The head/tail fillers carry `landing_pad = 0`.
fn resolved_table(r: &SmtExpr, l: &SmtExpr, pad: &SmtExpr, code_len: &SmtExpr) -> [Entry; 3] {
    let zero = SmtExpr::bv_const(0, W);
    let region_end = r.clone().bvadd(l.clone());
    [
        // HEAD filler: [0, r) (empty when r == 0).
        Entry {
            start: zero.clone(),
            len: r.clone(),
            landing_pad: zero.clone(),
        },
        // Explicit throwing region: [r, r + L) (production L = 4).
        Entry {
            start: r.clone(),
            len: l.clone(),
            landing_pad: pad.clone(),
        },
        // TAIL filler: [r + L, code_len) (empty when r + L == code_len).
        Entry {
            start: region_end.clone(),
            len: code_len.clone().bvsub(region_end),
            landing_pad: zero,
        },
    ]
}

/// The production invariant `resolve_eh_offsets` maintains: the explicit range
/// is exactly one four-byte AArch64 call at `[r, r + 4)`, lies inside
/// `[0, code_len)` (no wrap, ordered), and the head/tail fillers exactly fill its
/// complement. Pinning `L` here prevents the proof from silently accepting the
/// old whole-block call-site range.
fn layout_invariant(r: &SmtExpr, l: &SmtExpr, code_len: &SmtExpr) -> Vec<SmtExpr> {
    let region_end = r.clone().bvadd(l.clone());
    vec![
        // The protected region is exactly one final AArch64 BL/BLR word.
        l.clone().eq_expr(SmtExpr::bv_const(4, W)),
        // r + L does not wrap (length is non-negative in the byte-offset domain).
        region_end.clone().bvuge(r.clone()),
        // The throwing region ends at or before the function end.
        region_end.bvule(code_len.clone()),
    ]
}

// ===========================================================================
// 1. TOTAL COVERAGE / PARTITION: every pc in [0, code_len) is covered EXACTLY ONCE
// ===========================================================================

/// Proof: the resolved call-site table covers `[0, code_len)` with no gap and no
/// overlap — every `pc` in `[0, code_len)` lies in EXACTLY ONE call-site region.
///
/// Theorem (for the reconstructed HEAD/explicit/TAIL table, with symbolic
/// `r, L, pad` satisfying the exact-call `resolve_eh_offsets` invariant,
/// including `L == 4`):
///
///   forall pc in [0, code_len):
///       (covers_head(pc) ? 1 : 0)
///     + (covers_explicit(pc) ? 1 : 0)
///     + (covers_tail(pc) ? 1 : 0)   ==  1
///
/// "== 1" is BOTH halves of the partition at once: `>= 1` is total coverage (no
/// gap => the personality never terminates on an in-flight PC), and `<= 1` is
/// disjointness (no overlap => `scan_eh_table` selects a single record). The
/// `forall pc` is a bounded quantifier unrolled over `[0, code_len)`; the region
/// start stays symbolic, so AY proves coverage for every exact-call placement
/// the block allocator could produce. NON-DEGENERATE: the spec side is the
/// constant cover count `1`, the machine side is the table's reconstructed
/// per-pc cover count — a table with a gap or overlap (see negative control)
/// makes the count 0 or 2 for some pc and REFUTES.
pub fn proof_eh_callsite_table_total_coverage() -> ProofObligation {
    let r = SmtExpr::var("region_start", W);
    let l = SmtExpr::var("region_len", W);
    let pad = SmtExpr::var("landing_pad", W);
    let code_len = SmtExpr::bv_const(CODE_LEN, W);

    let table = resolved_table(&r, &l, &pad, &code_len);

    // Per-pc cover count = sum of the three entries' indicators.
    let pc = SmtExpr::var("pc", W);
    let cover_count = table[0]
        .cover_indicator(&pc)
        .bvadd(table[1].cover_indicator(&pc))
        .bvadd(table[2].cover_indicator(&pc));

    // forall pc in [0, code_len): cover_count(pc) == 1.
    let one = SmtExpr::bv_const(1, W);
    let body = cover_count.eq_expr(one);
    let quantified = SmtExpr::forall(
        "pc",
        W,
        SmtExpr::bv_const(0, W),
        SmtExpr::bv_const(CODE_LEN, W),
        body,
    );

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "LSDA EH: resolved call-site table covers [0,code_len) exactly once (partition)"
            .to_string(),
        // Spec: every pc is covered by exactly one region (cover count == 1).
        trust_ir_expr: SmtExpr::bool_const(true),
        // Emitted: the reconstructed table's per-pc cover count equals 1 for all pc.
        aarch64_expr: quantified,
        inputs: vec![
            ("region_start".to_string(), W),
            ("region_len".to_string(), W),
            ("landing_pad".to_string(), W),
        ],
        preconditions: layout_invariant(&r, &l, &code_len),
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control (must REFUTE): DROP the tail filler. Without the
/// `[r + L, code_len)` filler `resolve_eh_offsets` synthesizes, the PCs in
/// `[r + L, code_len)` are covered by NO entry — cover count 0 — so the
/// "covered exactly once" claim is FALSE. This is the literal bug: an
/// uncovered `_Unwind_Resume` PC makes the personality `std::terminate()`.
/// AY must produce a CounterExample (a pc in the gap), witnessing the tail
/// filler is load-bearing.
pub fn proof_eh_missing_tail_filler_leaves_gap_refutes() -> ProofObligation {
    let r = SmtExpr::var("region_start", W);
    let l = SmtExpr::var("region_len", W);
    let pad = SmtExpr::var("landing_pad", W);
    let code_len = SmtExpr::bv_const(CODE_LEN, W);

    // WRONG table: HEAD filler + explicit region ONLY (tail filler dropped).
    let table = resolved_table(&r, &l, &pad, &code_len);
    let pc = SmtExpr::var("pc", W);
    let cover_count = table[0]
        .cover_indicator(&pc)
        .bvadd(table[1].cover_indicator(&pc)); // tail entry OMITTED

    let one = SmtExpr::bv_const(1, W);
    let body = cover_count.eq_expr(one);
    let quantified = SmtExpr::forall(
        "pc",
        W,
        SmtExpr::bv_const(0, W),
        SmtExpr::bv_const(CODE_LEN, W),
        body,
    );

    // Pin a NON-EMPTY tail gap (r + L <u code_len) so the dropped filler
    // genuinely leaves an uncovered pc — making the over-claim refutable rather
    // than vacuously holding when the region already reaches code_len.
    let region_end = r.clone().bvadd(l.clone());
    let mut pre = layout_invariant(&r, &l, &code_len);
    pre.push(region_end.bvult(code_len));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "LSDA EH: dropped tail filler leaves a gap must REFUTE (uncovered PC terminates)"
            .to_string(),
        trust_ir_expr: SmtExpr::bool_const(true),
        aarch64_expr: quantified,
        inputs: vec![
            ("region_start".to_string(), W),
            ("region_len".to_string(), W),
            ("landing_pad".to_string(), W),
        ],
        preconditions: pre,
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 2. INVOKE -> PAD MAPPING: an Invoke's PC maps to a region with the Invoke's pad
// ===========================================================================

/// Proof: an Invoke call's PC maps to the explicit throwing region, whose
/// landing pad is the Invoke's own pad — NOT 0 / "no handler".
///
/// Theorem: for any `pc` inside the explicit throwing region `[r, r + L)` (where
/// the Invoke's `Bl` sits), the landing pad SELECTED by the resolved table — the
/// landing pad of the unique covering region — equals the Invoke's pad `pad`
/// (constrained non-zero, as a real landing-pad offset is). Because the
/// partition (proof 1) makes the explicit region the SOLE cover of such a pc, the
/// selected pad is well defined: it is `pad`, never a filler's 0.
///
/// Modeled as the personality's pad selection over the three reconstructed
/// entries: `selected_pad(pc) = sum_i covers_i(pc) ? landing_pad_i : 0`. Under
/// the partition only the explicit entry fires for an in-region pc, so the sum
/// collapses to `pad`. NON-DEGENERATE: spec side is `pad`; machine side is the
/// table-selected pad — a table that (wrongly) covered the Invoke PC with a
/// `landing_pad == 0` filler would select 0 and REFUTE (negative control).
pub fn proof_eh_invoke_pc_maps_to_invoke_pad() -> ProofObligation {
    let r = SmtExpr::var("region_start", W);
    let l = SmtExpr::var("region_len", W);
    let pad = SmtExpr::var("landing_pad", W);
    let code_len = SmtExpr::bv_const(CODE_LEN, W);
    let pc = SmtExpr::var("pc", W);

    let table = resolved_table(&r, &l, &pad, &code_len);

    // Personality pad selection: sum over entries of (covers(pc) ? pad_i : 0).
    let zero = SmtExpr::bv_const(0, W);
    let selected_pad = table.iter().fold(zero.clone(), |acc, e| {
        acc.bvadd(SmtExpr::ite(
            e.covers(&pc),
            e.landing_pad.clone(),
            zero.clone(),
        ))
    });

    // Spec: the Invoke PC's region carries the Invoke's own landing pad.
    let intended = pad.clone();

    // Preconditions: the cursor-walk invariant, the Invoke PC is inside the
    // explicit throwing region `[r, r + L)` (non-empty: r <u r + L), and the pad
    // is a real (non-zero) landing-pad offset — so "selects pad" is genuinely
    // distinct from a filler's "selects 0".
    let region_end = r.clone().bvadd(l.clone());
    let pc_in_region = r
        .clone()
        .bvule(pc.clone())
        .and_expr(pc.clone().bvult(region_end.clone()));
    let pad_nonzero = pad.bvugt(zero);
    let mut pre = layout_invariant(&r, &l, &code_len);
    pre.push(pc_in_region);
    pre.push(pad_nonzero);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "LSDA EH: Invoke PC maps to region with the Invoke's landing pad (not 0)".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: selected_pad,
        inputs: vec![
            ("region_start".to_string(), W),
            ("region_len".to_string(), W),
            ("landing_pad".to_string(), W),
            ("pc".to_string(), W),
        ],
        preconditions: pre,
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control (must REFUTE): a filler `landing_pad == 0` placed OVER the
/// Invoke PC. If the explicit throwing region were dropped and a
/// `landing_pad == 0` filler covered the whole `[0, code_len)` (so the Invoke
/// PC's region has pad 0), the table-selected pad would be 0 — "no handler" —
/// even though the Invoke has a real pad. This is the cleanup-PC-terminate bug:
/// the exception unwinds past the handler. Asserting the selected pad still
/// equals the (non-zero) Invoke pad is then REFUTABLE, witnessing the explicit
/// region's pad must win over a filler.
pub fn proof_eh_zero_pad_filler_over_invoke_refutes() -> ProofObligation {
    let r = SmtExpr::var("region_start", W);
    let l = SmtExpr::var("region_len", W);
    let pad = SmtExpr::var("landing_pad", W);
    let code_len = SmtExpr::bv_const(CODE_LEN, W);
    let pc = SmtExpr::var("pc", W);
    let zero = SmtExpr::bv_const(0, W);

    // WRONG table: a single filler `landing_pad == 0` over all of [0, code_len)
    // (the explicit throwing region dropped / never given a pad).
    let wrong = Entry {
        start: zero.clone(),
        len: code_len.clone(),
        landing_pad: zero.clone(),
    };
    let selected_pad = SmtExpr::ite(wrong.covers(&pc), wrong.landing_pad.clone(), zero.clone());

    // Spec: the Invoke PC must still select the Invoke's non-zero pad.
    let intended = pad.clone();

    // Same in-region / non-zero-pad preconditions, so the ONLY thing wrong is the
    // filler's zero pad covering the Invoke PC.
    let region_end = r.clone().bvadd(l.clone());
    let pc_in_region = r
        .clone()
        .bvule(pc.clone())
        .and_expr(pc.clone().bvult(region_end.clone()));
    let pad_nonzero = pad.bvugt(zero);
    let mut pre = layout_invariant(&r, &l, &code_len);
    pre.push(pc_in_region);
    pre.push(pad_nonzero);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "LSDA EH: zero-pad filler over Invoke PC must REFUTE (selects 0 / no handler)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: selected_pad,
        inputs: vec![
            ("region_start".to_string(), W),
            ("region_len".to_string(), W),
            ("landing_pad".to_string(), W),
            ("pc".to_string(), W),
        ],
        preconditions: pre,
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// Collect the aarch64 LSDA EH call-site COVERAGE / PARTITION proofs (2 positive
/// obligations): the resolved call-site table covers `[0, code_len)` exactly once
/// (no gap, no overlap), and an Invoke PC maps to a region carrying the Invoke's
/// landing pad. Together they certify the coverage invariant the abstract
/// dispatch proof (`aarch64_eh_lsda_proofs`) ASSUMES — the invariant filler
/// synthesis in `resolve_eh_offsets` establishes.
pub fn aarch64_eh_coverage_proofs() -> Vec<ProofObligation> {
    vec![
        proof_eh_callsite_table_total_coverage(),
        proof_eh_invoke_pc_maps_to_invoke_pad(),
    ]
}

/// Negative-control obligations (each REFUTABLE). NOT registered as proofs; used
/// by tests to demonstrate the positive proofs are real (a dropped tail filler
/// leaves a gap; a zero-pad filler over the Invoke PC selects "no handler").
pub fn aarch64_eh_coverage_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_eh_missing_tail_filler_leaves_gap_refutes(),
        proof_eh_zero_pad_filler_over_invoke_refutes(),
    ]
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::verify_by_evaluation;
    use crate::smt::EvalEnv;
    use crate::verify::VerificationResult;

    #[test]
    fn all_aarch64_eh_coverage_proofs_verify() {
        for obligation in aarch64_eh_coverage_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "LSDA EH coverage proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    /// Evaluate an obligation's two sides at an explicit witness env where the
    /// (wrong) table is mis-built, asserting the precondition holds AND the two
    /// sides DIFFER — i.e. the obligation is refuted at that point. The bounded
    /// `forall pc` over `[0, code_len)` plus the exact `L == 4` and tight
    /// `r + L <u code_len` preconditions make the gap counterexample one the
    /// random sampler rarely lands on, so we pin the witness directly here; the
    /// formal authority is the AY CLI in
    /// `proof_gate_strict::aarch64_eh_coverage_proofs_are_formally_verified`.
    fn refutes_at(obligation: &ProofObligation, bindings: &[(&str, u64)]) {
        let mut env = EvalEnv::default();
        for (name, val) in bindings {
            env.insert((*name).to_string(), *val);
        }
        // Every declared input (and the bound `pc`, if listed) must be present.
        for (name, _) in &obligation.inputs {
            assert!(
                env.contains_key(name),
                "witness env missing input '{}' for '{}'",
                name,
                obligation.name
            );
        }
        for pre in &obligation.preconditions {
            assert!(
                pre.eval(&env).as_bool(),
                "witness for '{}' must satisfy every precondition",
                obligation.name
            );
        }
        let spec = obligation.trust_ir_expr.eval(&env);
        let emitted = obligation.aarch64_expr.eval(&env);
        assert!(
            !spec.semantically_equal(&emitted),
            "LSDA EH coverage NEGATIVE control '{}' did NOT refute at the witness \
             (spec={:?}, emitted={:?}); a wrong table must produce a counterexample",
            obligation.name,
            spec,
            emitted
        );
    }

    #[test]
    fn all_aarch64_eh_coverage_negative_controls_refute() {
        // (1) Dropped tail filler: region_start = 0, region_len = 4 leaves the
        //     gap [4, code_len) uncovered (cover count 0 at every pc in the gap),
        //     so the "covered exactly once" forall is FALSE.
        refutes_at(
            &proof_eh_missing_tail_filler_leaves_gap_refutes(),
            &[("region_start", 0), ("region_len", 4), ("landing_pad", 0)],
        );
        // (2) Zero-pad filler over the Invoke PC: the filler covers pc = 4 with
        //     pad 0, so the selected pad is 0 != the Invoke's pad 8.
        refutes_at(
            &proof_eh_zero_pad_filler_over_invoke_refutes(),
            &[
                ("region_start", 4),
                ("region_len", 4),
                ("landing_pad", 8),
                ("pc", 4),
            ],
        );
    }

    #[test]
    fn positive_proofs_bind_region_to_exact_aarch64_call_width() {
        for obligation in aarch64_eh_coverage_proofs() {
            let mut exact_call = EvalEnv::default();
            exact_call.insert("region_start".to_string(), 4);
            exact_call.insert("region_len".to_string(), 4);
            exact_call.insert("landing_pad".to_string(), 8);
            exact_call.insert("pc".to_string(), 4);
            assert!(
                obligation
                    .preconditions
                    .iter()
                    .all(|pre| pre.eval(&exact_call).as_bool()),
                "exact four-byte call witness must satisfy '{}'",
                obligation.name
            );

            let mut old_whole_block = exact_call.clone();
            old_whole_block.insert("region_len".to_string(), 8);
            assert!(
                !obligation
                    .preconditions
                    .iter()
                    .all(|pre| pre.eval(&old_whole_block).as_bool()),
                "whole-block width must not satisfy exact-call proof '{}'",
                obligation.name
            );
        }
    }

    #[test]
    fn aarch64_eh_coverage_proofs_are_non_degenerate() {
        for obligation in aarch64_eh_coverage_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "LSDA EH coverage proof '{}' is DEGENERATE (X==X); it proves nothing",
                obligation.name
            );
        }
    }

    #[test]
    fn aarch64_eh_coverage_proof_count_and_names_unique() {
        let proofs = aarch64_eh_coverage_proofs();
        assert_eq!(proofs.len(), 2, "expected 2 LSDA EH coverage proofs");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(
            before,
            names.len(),
            "duplicate LSDA EH coverage proof names"
        );
    }
}
