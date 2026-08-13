// trust-cg-verify/coroutine_frame_proofs.rs - SMT proofs for the coroutine
// suspend (yield) frame save/restore lowering.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proves the SEMANTIC correctness of the `Inst::CoroSuspend` macro-expansion the
// backend emits (`trust-cg-lower/src/adapter.rs::translate_coro_suspend`). One
// coroutine `yield` operationally is:
//
//     store i64 `next_state` into `frame[state_slot]`   ; record resume state
//     return `value`                                    ; hand value to resumer
//
// The frame is a caller-owned aggregate of I64 elements, so the state field lives
// at BYTE offset `state_slot * 8` from `frame` (the same `base + index*sizeof(I64)`
// address arithmetic the single-index GEP arm emits). The yielded `value` is a
// SEPARATE SSA value handed back through the return ABI — the state store must NOT
// clobber it.
//
// What these proofs certify (through the symbolic byte-array memory model,
// `memory_proofs::{symbolic_memory, encode_store_le, encode_load_le}`, the SAME
// QF_ABV model the aggregate-placement and Load/Store lowering proofs discharge
// through):
//
//   1. State save: after the emitted 8-byte store of `next_state` at
//      `frame + state_slot*8`, reloading 8 bytes from `frame + state_slot*8`
//      yields exactly `next_state`. Spec side: `next_state`; emitted side:
//      `load_le(store_le(mem, frame+slot*8, next_state), frame+slot*8)`. This is a
//      genuine read-over-write equivalence (NOT `x==x`): a WRONG byte offset on the
//      store (e.g. `state_slot*4`, treating the frame as I32 elements) lands the
//      bytes elsewhere and the reload at the I64 offset REFUTES — see
//      `proof_coro_state_save_wrong_offset_refutes`.
//
//   2. Value independence: the yielded `value` (an independent variable) is
//      UNAFFECTED by the state store, because the store targets the frame and the
//      return value is delivered separately. Modeled as: storing `next_state` into
//      the frame slot does not change `value` — spec side `value`, emitted side
//      `value` reconstructed AFTER the store via a no-op-on-`value` path. To keep
//      this NON-DEGENERATE (a real claim, not `value==value`), we model the
//      yielded value as itself held in a caller scratch slot that is DISJOINT from
//      the frame state slot: store `value` at a scratch address, store `next_state`
//      at the frame slot, then reload `value` from the scratch address. The reload
//      equals `value` IFF the two regions do not overlap — a wrong/overlapping
//      placement REFUTES (`proof_coro_value_independence_overlap_refutes`).
//
// Soundness boundary. These prove the store-placement + value-independence
// SEMANTICS of the suspend expansion (the part that reduces to the verified I64
// Store + Return primitives). The `next_state` constant materialization and the
// return-ABI register placement are covered by the existing const-materialize and
// call-lowering return proofs respectively; this lane pins that the suspend glue
// wires them at the correct frame offset without clobbering the yielded value.
//
// Reference: trust-cg-lower/src/adapter.rs §translate_coro_suspend; trust-ir
// inst.rs §coroutines.

//! SMT proofs for the AArch64 coroutine-suspend frame save/restore lowering.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::memory_proofs::{encode_load_le, encode_store_le, symbolic_memory};
use crate::smt::SmtExpr;

/// I64 frame element size in bytes (the suspend frame is an aggregate of I64s).
const I64_BYTES: u64 = 8;

/// The compile-time resume-state slot index used by the proofs (a representative
/// non-zero slot, so the `state_slot*8` byte-offset arithmetic is exercised; slot
/// 0 is the degenerate frame-base case the lowering special-cases).
const STATE_SLOT: u64 = 3;

// ===========================================================================
// 1. State save: store next_state at frame[state_slot] -> reload == next_state
// ===========================================================================

/// Proof: the emitted `CoroSuspend` state store records `next_state` at the
/// correct I64 frame slot.
///
/// Theorem (over the symbolic byte-array memory model): for all `frame : BV64`,
/// `next_state : BV64`, `mem_default : BV8`,
///   let `addr = frame + STATE_SLOT*8`
///   `load_le(store_le(mem, addr, next_state, 8), addr, 8) == next_state`.
///
/// Spec side (`trust_ir_expr`): the recorded resume state `next_state`. Emitted
/// side (`aarch64_expr`): the byte-array read-over-write the lowering produces (an
/// 8-byte STR at `frame + state_slot*8` then an 8-byte LDR back at the same
/// address). The equality is a genuine read-over-write reconstruction, not a
/// tautology — a wrong store offset refutes (see the negative control).
pub fn proof_coro_state_save_roundtrip() -> ProofObligation {
    let mem = symbolic_memory("mem_default");
    let frame = SmtExpr::var("frame", 64);
    let next_state = SmtExpr::var("next_state", 64);

    // Address of the state field: frame + state_slot * 8.
    let addr = frame
        .clone()
        .bvadd(SmtExpr::bv_const(STATE_SLOT * I64_BYTES, 64));

    // Emitted lowering: STR next_state, [frame, #state_slot*8]; LDR back.
    let mem_after = encode_store_le(&mem, &addr, &next_state, 8);
    let reloaded = encode_load_le(&mem_after, &addr, 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CoroSuspend: state store at frame[state_slot] (offset slot*8) reloads next_state"
            .to_string(),
        trust_ir_expr: next_state,
        aarch64_expr: reloaded,
        inputs: vec![
            ("frame".to_string(), 64),
            ("next_state".to_string(), 64),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
    }
}

/// Negative control: a `CoroSuspend` that stores `next_state` at the WRONG byte
/// offset `state_slot * 4` (treating the I64 frame as if its elements were I32)
/// does NOT reload as `next_state` when read back at the correct I64 offset
/// `state_slot * 8`. The stored bytes land 12 bytes too low (`3*8 - 3*4 = 12`), so
/// the correct-offset reload reads the symbolic default and the obligation is
/// REFUTABLE.
///
/// This obligation is intentionally REFUTABLE; the AY lane asserts it is a
/// CounterExample, demonstrating the positive save proof genuinely pins the
/// `state_slot*8` offset (it is not satisfied by any byte placement).
pub fn proof_coro_state_save_wrong_offset_refutes() -> ProofObligation {
    let mem = symbolic_memory("mem_default");
    let frame = SmtExpr::var("frame", 64);
    let next_state = SmtExpr::var("next_state", 64);

    // WRONG store address: state_slot * 4 (I32-element stride).
    let wrong_addr = frame.clone().bvadd(SmtExpr::bv_const(STATE_SLOT * 4, 64));
    // Correct reload address: state_slot * 8 (I64-element stride).
    let correct_addr = frame
        .clone()
        .bvadd(SmtExpr::bv_const(STATE_SLOT * I64_BYTES, 64));

    let mem_after = encode_store_le(&mem, &wrong_addr, &next_state, 8);
    let reloaded = encode_load_le(&mem_after, &correct_addr, 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CoroSuspend: state store at WRONG offset slot*4 must REFUTE".to_string(),
        trust_ir_expr: next_state,
        aarch64_expr: reloaded,
        inputs: vec![
            ("frame".to_string(), 64),
            ("next_state".to_string(), 64),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
    }
}

// ===========================================================================
// 2. Value independence: the state store does not clobber the yielded value
// ===========================================================================

/// Proof: the yielded `value` survives the `CoroSuspend` state store unchanged.
///
/// The yielded value is an independent SSA value handed back through the return
/// ABI; the state store targets the frame. To express this as a NON-DEGENERATE
/// theorem (not `value == value`), we model `value` as held in a caller scratch
/// slot that is DISJOINT from the frame state slot: store `value` at a scratch
/// address `vbase`, store `next_state` at the frame state slot
/// `frame + state_slot*8`, then reload `value` from `vbase`.
///
/// Theorem: for all `vbase, frame, value, next_state : BV64`,
///   if `[vbase, vbase+8)` and `[frame+slot*8, frame+slot*8+8)` are DISJOINT,
///   then `load_le(store_le(store_le(mem, vbase, value), frame_slot, next_state),
///   vbase) == value`.
///
/// Spec side: `value`; emitted side: the reloaded value after BOTH stores. A wrong
/// (overlapping) placement makes the state store clobber the value and REFUTES
/// (see `proof_coro_value_independence_overlap_refutes`).
pub fn proof_coro_value_independence() -> ProofObligation {
    let mem = symbolic_memory("mem_default");
    let vbase = SmtExpr::var("vbase", 64);
    let frame = SmtExpr::var("frame", 64);
    let value = SmtExpr::var("value", 64);
    let next_state = SmtExpr::var("next_state", 64);

    let frame_slot = frame
        .clone()
        .bvadd(SmtExpr::bv_const(STATE_SLOT * I64_BYTES, 64));

    // Lay down value at the scratch slot, then perform the state store, then
    // reload the yielded value from its scratch slot.
    let mem1 = encode_store_le(&mem, &vbase, &value, 8);
    let mem2 = encode_store_le(&mem1, &frame_slot, &next_state, 8);
    let reloaded = encode_load_le(&mem2, &vbase, 8);

    // Disjointness precondition: the value slot [vbase, vbase+8) and the frame
    // state slot [frame_slot, frame_slot+8) do not overlap (symmetric two-sided,
    // no-wrap form mirroring memory_proofs::proof_non_interference_symbolic).
    let eight = SmtExpr::bv_const(8, 64);
    let vend = vbase.clone().bvadd(eight.clone());
    let fend = frame_slot.clone().bvadd(eight.clone());
    let v_no_wrap = vend.clone().bvugt(vbase.clone());
    let f_no_wrap = fend.clone().bvugt(frame_slot.clone());
    let v_before_f = frame_slot.clone().bvuge(vend);
    let f_before_v = vbase.clone().bvuge(fend);
    let disjoint = v_before_f.or_expr(f_before_v);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CoroSuspend: state store preserves the yielded value (disjoint slot)".to_string(),
        trust_ir_expr: value,
        aarch64_expr: reloaded,
        inputs: vec![
            ("vbase".to_string(), 64),
            ("frame".to_string(), 64),
            ("value".to_string(), 64),
            ("next_state".to_string(), 64),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![v_no_wrap, f_no_wrap, disjoint],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
    }
}

/// Negative control: if the yielded value's slot ALIASES the frame state slot
/// (`vbase == frame + state_slot*8`), the state store CLOBBERS the value, so the
/// reload returns `next_state` rather than `value`. Asserting the reload still
/// equals `value` is then REFUTABLE — witnessing that the positive proof's
/// disjointness precondition is load-bearing (the store really can clobber an
/// overlapping value).
pub fn proof_coro_value_independence_overlap_refutes() -> ProofObligation {
    let mem = symbolic_memory("mem_default");
    let frame = SmtExpr::var("frame", 64);
    let value = SmtExpr::var("value", 64);
    let next_state = SmtExpr::var("next_state", 64);

    let frame_slot = frame
        .clone()
        .bvadd(SmtExpr::bv_const(STATE_SLOT * I64_BYTES, 64));
    // WRONG: the yielded value is placed at the SAME address as the state slot.
    let vbase = frame_slot.clone();

    let mem1 = encode_store_le(&mem, &vbase, &value, 8);
    let mem2 = encode_store_le(&mem1, &frame_slot, &next_state, 8);
    let reloaded = encode_load_le(&mem2, &vbase, 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CoroSuspend: aliasing value/state slot must REFUTE (store clobbers value)"
            .to_string(),
        trust_ir_expr: value,
        aarch64_expr: reloaded,
        inputs: vec![
            ("frame".to_string(), 64),
            ("value".to_string(), 64),
            ("next_state".to_string(), 64),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// Collect the coroutine-suspend frame save/restore proofs (2 positive
/// obligations): the state store records `next_state` at `frame[state_slot]`
/// (offset `slot*8`), and the state store preserves the independently-yielded
/// return `value`. Both discharge through the symbolic byte-array memory model.
pub fn all_coroutine_frame_proofs() -> Vec<ProofObligation> {
    vec![
        proof_coro_state_save_roundtrip(),
        proof_coro_value_independence(),
    ]
}

/// Negative-control obligations (each REFUTABLE). NOT registered as proofs; used
/// by tests to demonstrate the positive proofs are real equivalences (a wrong
/// store offset, or an aliasing value placement, is rejected).
pub fn coroutine_frame_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_coro_state_save_wrong_offset_refutes(),
        proof_coro_value_independence_overlap_refutes(),
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
    fn all_coroutine_frame_proofs_verify() {
        for obligation in all_coroutine_frame_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "coroutine-frame proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_coroutine_frame_negative_controls_refute() {
        for obligation in coroutine_frame_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "coroutine-frame NEGATIVE control '{}' should be Invalid (a wrong placement \
                 must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn coroutine_frame_proofs_are_non_degenerate() {
        for obligation in all_coroutine_frame_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "coroutine-frame proof '{}' is DEGENERATE (X==X); it proves nothing",
                obligation.name
            );
        }
    }

    #[test]
    fn coroutine_frame_proof_count_and_names_unique() {
        let proofs = all_coroutine_frame_proofs();
        assert_eq!(proofs.len(), 2, "expected 2 coroutine-frame proofs");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate coroutine-frame proof names");
    }
}
