// trust-cg-verify/wasm_memory_proofs.rs - wasm linear-memory refinement proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Memory-correctness proofs for the trust-cg WebAssembly backend (Slice 5),
//! over the byte-addressed linear-memory model in [`crate::wasm_semantics`].
//! Discharged FORMALLY (`unsat`) by the `ay` SMT solver via
//! [`crate::wasm_formal`] (QF_ABV array theory). The base memory is a
//! `const_array`, so the only symbolic inputs are bitvectors — no free
//! array variable, which `ProofObligation::to_smt2` cannot yet declare.
//!
//! Two distinct kinds of obligation here, honestly labeled:
//!
//! 1. **Memory-model self-consistency** ([`all_model_consistency_proofs`]):
//!    a little-endian `iN.store` followed by an `iN.load` at the same address
//!    round-trips, and a store does not touch the adjacent word. Both sides are
//!    built from the same `wasm_semantics` byte model, so these validate that
//!    *model* (the `extract` byte split, `p+i` addressing, `concat` reassembly,
//!    little-endianness) — NOT a refinement of `lower.rs`. They are guarded
//!    against vacuity by the anti-tautology tests.
//!
//! 2. **Backend-anchored address arithmetic** ([`proof_gep_elements_disjoint`]):
//!    distinct in-bounds elements of an `i32` array, addressed by the backend's
//!    GEP formula (`base + index*elem_size`, mirrored from `lower.rs`), occupy
//!    **disjoint** byte ranges — i.e. the emitted stride equals the element
//!    size. A wrong stride (e.g. 1 instead of 4) makes elements overlap and the
//!    proof fails (see [`proof_wrong_stride_overlaps`]). This catches a real
//!    lowering bug class.
//!
//! NOT yet covered (documented next slice): refinement against a trust-ir memory
//! SMT encoder (none exists in `trust_ir_semantics` yet), aliasing against a
//! symbolic prior memory (needs a free array-sort input), and the shadow-stack
//! frame offset arithmetic.

use crate::lowering_proof::ProofObligation;
use crate::smt::SmtExpr;
use crate::wasm_semantics as w;

fn obligation(
    name: &str,
    trust_ir_expr: SmtExpr,
    target: SmtExpr,
    inputs: Vec<(String, u32)>,
) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr: target, // "target slot", reused for the wasm memory model
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    }
}

/// `i32.load(i32.store(mem0, p, v), p) == v` — same-address round-trip.
pub fn proof_load_after_store_i32() -> ProofObligation {
    let p = SmtExpr::var("p", 32);
    let v = SmtExpr::var("v", 32);
    let stored = w::encode_store_i32(w::zero_memory(), p.clone(), v.clone());
    let loaded = w::encode_load_i32(stored, p);
    obligation(
        "i32 load-after-store round-trip",
        v,
        loaded,
        vec![("p".to_string(), 32), ("v".to_string(), 32)],
    )
}

/// `i64.load(i64.store(mem0, p, v), p) == v` — same-address round-trip (8 bytes).
pub fn proof_load_after_store_i64() -> ProofObligation {
    let p = SmtExpr::var("p", 32);
    let v = SmtExpr::var("v", 64);
    let stored = w::encode_store_i64(w::zero_memory(), p.clone(), v.clone());
    let loaded = w::encode_load_i64(stored, p);
    obligation(
        "i64 load-after-store round-trip",
        v,
        loaded,
        vec![("p".to_string(), 32), ("v".to_string(), 64)],
    )
}

/// Storing an i32 at `p` leaves the adjacent word at `p+4` untouched (still 0).
pub fn proof_store_non_aliasing_i32() -> ProofObligation {
    let p = SmtExpr::var("p", 32);
    let v = SmtExpr::var("v", 32);
    let stored = w::encode_store_i32(w::zero_memory(), p.clone(), v);
    let next = p.bvadd(SmtExpr::bv_const(4, 32));
    let loaded = w::encode_load_i32(stored, next);
    obligation(
        "i32 store does not alias the adjacent word",
        SmtExpr::bv_const(0, 32),
        loaded,
        vec![("p".to_string(), 32), ("v".to_string(), 32)],
    )
}

/// Memory-model self-consistency obligations (must verify).
pub fn all_model_consistency_proofs() -> Vec<ProofObligation> {
    vec![
        proof_load_after_store_i32(),
        proof_load_after_store_i64(),
        proof_store_non_aliasing_i32(),
    ]
}

/// Backend-anchored: distinct in-bounds elements of an `i32` array (addressed by
/// the GEP formula `base + index*4`) occupy disjoint 4-byte ranges. Validated as
/// `i <u j  ⟹  gep(i)+4 <=u gep(j)` over a bounded, no-wrap address window.
/// A wrong stride makes this fail — see [`proof_wrong_stride_overlaps`].
pub fn proof_gep_elements_disjoint() -> ProofObligation {
    gep_disjoint_obligation("i32-array GEP elements are disjoint (stride == size)", 4)
}

/// Anti-tautology: claim the SAME disjointness with a wrong stride of 1 byte for
/// an i32 (4-byte) element. Elements then overlap, so it must be refuted.
pub fn proof_wrong_stride_overlaps() -> ProofObligation {
    gep_disjoint_obligation(
        "WRONG: i32-array with stride 1 stays disjoint (must be refuted)",
        1,
    )
}

/// Shared builder: element size 4 bytes (i32) but a configurable emitted
/// `stride`. Asserts the two **adjacent** elements (indices 0 and 1 — the
/// tightest non-overlap case) occupy disjoint 4-byte ranges:
/// `gep(0)+4 <=u gep(1)`. Indices are concrete so the obligation has a single
/// symbolic input (`base`) that random sampling actually exercises (a symbolic
/// `j <u 8` precondition would be satisfied by ~0 of the 2^32 samples, vacuously
/// passing). `base` is range-limited so the addresses cannot wrap.
fn gep_disjoint_obligation(name: &str, stride: u32) -> ProofObligation {
    const ELEM_SIZE: u64 = 4; // i32
    let base = SmtExpr::var("base", 32);
    let a0 = w::encode_gep_element(base.clone(), SmtExpr::bv_const(0, 32), stride);
    let a1 = w::encode_gep_element(base.clone(), SmtExpr::bv_const(1, 32), stride);
    // Element 0's range [a0, a0+4) lies entirely below element 1's start.
    let disjoint = a0.bvadd(SmtExpr::bv_const(ELEM_SIZE, 32)).bvule(a1);
    // No-wrap window: base <=u 2^32 - 2*stride - 4, so both ranges fit.
    let max_base = SmtExpr::bv_const((1u64 << 32) - 2 * u64::from(stride) - 4, 32);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: SmtExpr::bool_const(true),
        aarch64_expr: disjoint,
        inputs: vec![("base".to_string(), 32)],
        preconditions: vec![base.bvule(max_base)], // no address wrap
        fp_inputs: vec![],
        category: None,
    }
}

/// Anti-tautology: claims the round-trip yields `v+1`. Must be refuted.
pub fn proof_wrong_value() -> ProofObligation {
    let p = SmtExpr::var("p", 32);
    let v = SmtExpr::var("v", 32);
    let stored = w::encode_store_i32(w::zero_memory(), p.clone(), v.clone());
    let loaded = w::encode_load_i32(stored, p);
    obligation(
        "WRONG: round-trip yields v+1 (must be refuted)",
        v.bvadd(SmtExpr::bv_const(1, 32)),
        loaded,
        vec![("p".to_string(), 32), ("v".to_string(), 32)],
    )
}

/// Anti-tautology (memory-specific): claims a load one byte off (`p+1`) still
/// equals `v`. It does not (it reads `v>>8` with a zero top byte). Must be refuted.
pub fn proof_wrong_address() -> ProofObligation {
    let p = SmtExpr::var("p", 32);
    let v = SmtExpr::var("v", 32);
    let stored = w::encode_store_i32(w::zero_memory(), p.clone(), v.clone());
    let off = p.bvadd(SmtExpr::bv_const(1, 32));
    let loaded = w::encode_load_i32(stored, off);
    obligation(
        "WRONG: load at p+1 equals v (must be refuted)",
        v,
        loaded,
        vec![("p".to_string(), 32), ("v".to_string(), 32)],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm_formal::{prove, refute};

    /// FORMAL (default): memory-model self-consistency obligations are proven
    /// `unsat` by ay (QF_ABV array theory) — load-after-store round-trips and
    /// stores don't alias the adjacent word, for all addresses/values.
    #[test]
    fn model_consistency_proven_formally() {
        if !crate::ay_bridge::z3_available() {
            return;
        }
        for ob in all_model_consistency_proofs() {
            prove(&ob);
        }
    }

    /// FORMAL: the backend-anchored GEP element-disjointness obligation.
    #[test]
    fn gep_elements_disjoint_proven_formally() {
        if !crate::ay_bridge::z3_available() {
            return;
        }
        prove(&proof_gep_elements_disjoint());
    }

    /// FORMAL anti-tautology guards: a wrong stride, a wrong value, and a
    /// wrong (off-by-one) load address are each refuted (`sat`) by ay.
    #[test]
    fn memory_anti_tautologies_refuted_formally() {
        refute(&proof_wrong_stride_overlaps());
        refute(&proof_wrong_value());
        refute(&proof_wrong_address());
    }
}
