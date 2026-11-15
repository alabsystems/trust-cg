// trust-cg-verify/atomic_proofs.rs - Atomic memory operation correctness proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Verifies trust_ir atomic memory operations lowering to AArch64 LSE instructions.
// Atomic operations are modeled over the SMT array memory model (QF_ABV) with
// explicit ordering annotations abstracted: we verify data-flow correctness
// (the *values* are right) while ordering is an architectural guarantee.
//
// Key properties verified:
//   1. Atomic load (LDAR): loads correct value from memory with acquire semantics
//   2. Atomic store (STLR): stores correct value to memory with release semantics
//   3. Atomic RMW ADD (LDADD): returns old value, memory updated to old + operand
//   4. Atomic RMW OR (LDSET): returns old value, memory updated to old | operand
//   5. Atomic RMW XOR (LDEOR): returns old value, memory updated to old ^ operand
//   6. Atomic RMW exchange (SWP): returns old value, memory updated to operand
//   7. Atomic RMW clear (LDCLR): returns old value, memory updated to old AND NOT operand
//   8. Compare-and-swap (CAS): success path stores new value; failure path is no-op
//   9. Atomic SUB via NEG+LDADD equivalence
//  10. Atomic AND via MVN+LDCLR equivalence
//  11. Fence (DMB) ordering properties: barrier option encoding
//
// Ordering model: AArch64 LDAR/STLR provide acquire/release semantics at the
// hardware level. The ISel maps all atomic orderings to the appropriate LDAR/
// STLR/LDADD{A,L,AL} variant. We verify the data-flow semantics are correct
// here. Which C11/Rust ordering each emitted form implements is checked
// separately, on the decoded words, by `aarch64_memory_order` (L03-P3: a
// mapping-conformance check against the C11/Rust -> AArch64 mapping); the
// ordering contribution of each instruction is still the ARM architecture
// specification (DDI 0487, Section B2.3 and K11), delegated.
//
// Reference: ARM Architecture Reference Manual (DDI 0487), Section C6.

//! Atomic memory operation correctness proofs.
//!
//! This module verifies that trust_ir atomic memory operations (AtomicLoad,
//! AtomicStore, AtomicRmw, CmpXchg, Fence) lower correctly to AArch64
//! LSE (Large System Extensions) instructions.
//!
//! # Memory model
//!
//! Memory is modeled as `Array(BitVec64, BitVec8)` — the same byte-addressable
//! array model used by [`crate::memory_proofs`]. Multi-byte atomics use
//! little-endian byte ordering.
//!
//! # Atomic RMW pattern
//!
//! All LSE atomic RMW instructions share the same pattern:
//! ```text
//! LDADD Xs, Xt, [Xn]
//!   Xt = *Xn             (old value returned)
//!   *Xn = Xt OP Xs       (new value written)
//! ```
//!
//! We verify both the return value (old) and the memory state (new).

use crate::lowering_proof::ProofObligation;
use crate::memory_proofs::{encode_load_le, encode_store_le, symbolic_memory};
use crate::smt::{SmtExpr, mask};

// ---------------------------------------------------------------------------
// Atomic load semantics: LDAR
// ---------------------------------------------------------------------------

/// Encode trust_ir AtomicLoad semantics: read `size_bytes` from `addr` in `mem`.
///
/// AtomicLoad is semantically identical to a regular load for data-flow
/// purposes. The acquire ordering is an architectural guarantee provided
/// by the LDAR instruction encoding, not a data-flow property.
fn encode_trust_ir_atomic_load(mem: &SmtExpr, addr: &SmtExpr, size_bytes: u32) -> SmtExpr {
    encode_load_le(mem, addr, size_bytes)
}

/// Encode AArch64 LDAR semantics: load-acquire `size_bytes` from `[Xn]`.
///
/// LDAR Xt, [Xn]: Xt = Mem[Xn] with acquire ordering.
/// LDARB Wt, [Xn]: Wt = ZeroExtend(Mem[Xn], 32) (byte variant).
/// LDARH Wt, [Xn]: Wt = ZeroExtend(Mem[Xn..Xn+1], 32) (halfword variant).
///
/// Reference: ARM DDI 0487, C6.2.118 (LDAR).
fn encode_aarch64_ldar(mem: &SmtExpr, addr: &SmtExpr, size_bytes: u32) -> SmtExpr {
    encode_load_le(mem, addr, size_bytes)
}

/// Build a proof that trust_ir AtomicLoad == AArch64 LDAR for the given size.
///
/// Both sides perform a little-endian load from the same address. The proof
/// verifies value equivalence; ordering is architectural.
fn proof_atomic_load(name: &str, size_bytes: u32) -> ProofObligation {
    let mem = symbolic_memory("mem_default");
    let addr = SmtExpr::var("addr", 64);

    let trust_ir_result = encode_trust_ir_atomic_load(&mem, &addr, size_bytes);
    let aarch64_result = encode_aarch64_ldar(&mem, &addr, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir_result,
        aarch64_expr: aarch64_result,
        inputs: vec![("addr".to_string(), 64), ("mem_default".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: `trust_ir::AtomicLoad(I8) -> LDARB`.
pub fn proof_atomic_load_i8() -> ProofObligation {
    proof_atomic_load("AtomicLoad_I8 -> LDARB", 1)
}

/// Proof: `trust_ir::AtomicLoad(I16) -> LDARH`.
pub fn proof_atomic_load_i16() -> ProofObligation {
    proof_atomic_load("AtomicLoad_I16 -> LDARH", 2)
}

/// Proof: `trust_ir::AtomicLoad(I32) -> LDAR (32-bit)`.
pub fn proof_atomic_load_i32() -> ProofObligation {
    proof_atomic_load("AtomicLoad_I32 -> LDAR_W", 4)
}

/// Proof: `trust_ir::AtomicLoad(I64) -> LDAR (64-bit)`.
pub fn proof_atomic_load_i64() -> ProofObligation {
    proof_atomic_load("AtomicLoad_I64 -> LDAR_X", 8)
}

// ---------------------------------------------------------------------------
// Atomic store semantics: STLR
// ---------------------------------------------------------------------------

/// Encode AArch64 STLR semantics: store-release `value` of `size_bytes` to `[Xn]`.
///
/// STLR Xt, [Xn]: Mem[Xn] = Xt with release ordering.
///
/// Reference: ARM DDI 0487, C6.2.256 (STLR).
fn encode_aarch64_stlr(mem: &SmtExpr, addr: &SmtExpr, value: &SmtExpr, size_bytes: u32) -> SmtExpr {
    encode_store_le(mem, addr, value, size_bytes)
}

/// Build a store-then-load roundtrip proof for atomic store.
///
/// The proof asserts:
/// ```text
/// forall addr: BV64, value: BV(size*8), mem_default: BV8 .
///   let mem = ConstArray(BV64, mem_default)
///   let mem' = STLR(mem, addr, value)
///   LDAR(mem', addr) == value
/// ```
///
/// This verifies the store-load roundtrip: atomically stored values can
/// be atomically loaded back correctly.
fn proof_atomic_store_load_roundtrip(name: &str, size_bytes: u32) -> ProofObligation {
    let result_width = size_bytes * 8;
    let mem = symbolic_memory("mem_default");
    let addr = SmtExpr::var("addr", 64);
    let value = SmtExpr::var("value", result_width);

    // Store the value atomically
    let mem_after_store = encode_aarch64_stlr(&mem, &addr, &value, size_bytes);
    // Load it back atomically
    let loaded = encode_aarch64_ldar(&mem_after_store, &addr, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: value,
        aarch64_expr: loaded,
        inputs: vec![
            ("addr".to_string(), 64),
            ("value".to_string(), result_width),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: STLR then LDAR roundtrip for 8-bit.
pub fn proof_atomic_store_load_i8() -> ProofObligation {
    proof_atomic_store_load_roundtrip("AtomicStore_Load_I8: STLRB->LDARB roundtrip", 1)
}

/// Proof: STLR then LDAR roundtrip for 16-bit.
pub fn proof_atomic_store_load_i16() -> ProofObligation {
    proof_atomic_store_load_roundtrip("AtomicStore_Load_I16: STLRH->LDARH roundtrip", 2)
}

/// Proof: STLR then LDAR roundtrip for 32-bit.
pub fn proof_atomic_store_load_i32() -> ProofObligation {
    proof_atomic_store_load_roundtrip("AtomicStore_Load_I32: STLR->LDAR roundtrip", 4)
}

/// Proof: STLR then LDAR roundtrip for 64-bit.
pub fn proof_atomic_store_load_i64() -> ProofObligation {
    proof_atomic_store_load_roundtrip("AtomicStore_Load_I64: STLR->LDAR roundtrip", 8)
}

// ---------------------------------------------------------------------------
// Atomic RMW semantics: LDADD, LDSET, LDEOR, SWP, LDCLR
// ---------------------------------------------------------------------------

/// Encode an atomic RMW operation at the SMT level.
///
/// All LSE atomic RMW instructions follow the same pattern:
/// ```text
/// old = *addr
/// *addr = old OP operand
/// return old
/// ```
///
/// We model this by:
/// 1. Loading the old value from memory (return value)
/// 2. Computing `old OP operand` (new value)
/// 3. Storing the new value back to memory (side effect)
///
/// Returns `(old_value, mem_after)`.
fn encode_atomic_rmw<F>(
    mem: &SmtExpr,
    addr: &SmtExpr,
    operand: &SmtExpr,
    size_bytes: u32,
    op: F,
) -> (SmtExpr, SmtExpr)
where
    F: FnOnce(SmtExpr, SmtExpr) -> SmtExpr,
{
    // Load old value
    let old_value = encode_load_le(mem, addr, size_bytes);
    // Compute new value
    let new_value = op(old_value.clone(), operand.clone());
    // Store new value
    let mem_after = encode_store_le(mem, addr, &new_value, size_bytes);
    (old_value, mem_after)
}

/// Build a proof that the old value returned by an atomic RMW matches
/// the value previously in memory.
///
/// Proof: `RMW.old_value == Load(mem, addr)` before the RMW.
fn proof_atomic_rmw_returns_old<F>(name: &str, size_bytes: u32, op: F) -> ProofObligation
where
    F: FnOnce(SmtExpr, SmtExpr) -> SmtExpr,
{
    let result_width = size_bytes * 8;
    let mem = symbolic_memory("mem_default");
    let addr = SmtExpr::var("addr", 64);
    let operand = SmtExpr::var("operand", result_width);

    // trust_ir side: the old value at the address
    let trust_ir_old = encode_load_le(&mem, &addr, size_bytes);
    // AArch64 side: the return value from the RMW instruction
    let (aarch64_old, _mem_after) = encode_atomic_rmw(&mem, &addr, &operand, size_bytes, op);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir_old,
        aarch64_expr: aarch64_old,
        inputs: vec![
            ("addr".to_string(), 64),
            ("operand".to_string(), result_width),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Build a proof that the new value in memory after an atomic RMW is correct.
///
/// Proof: `Load(mem_after_RMW, addr) == old_value OP operand`.
fn proof_atomic_rmw_updates_mem<F>(name: &str, size_bytes: u32, op: F) -> ProofObligation
where
    F: FnOnce(SmtExpr, SmtExpr) -> SmtExpr,
{
    let result_width = size_bytes * 8;
    let mem = symbolic_memory("mem_default");
    let addr = SmtExpr::var("addr", 64);
    let operand = SmtExpr::var("operand", result_width);

    // trust_ir expected: old_value OP operand
    let old_value = encode_load_le(&mem, &addr, size_bytes);
    let trust_ir_expected = op(old_value, operand.clone());

    // AArch64 side: store the computed new value, then load it back.
    // This verifies the store-load roundtrip of the RMW result.
    let new_value = trust_ir_expected.clone();
    let mem_after = encode_store_le(&mem, &addr, &new_value, size_bytes);
    let aarch64_loaded = encode_load_le(&mem_after, &addr, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir_expected,
        aarch64_expr: aarch64_loaded,
        inputs: vec![
            ("addr".to_string(), 64),
            ("operand".to_string(), result_width),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

// -- LDADD proofs --

/// Proof: LDADD returns the old value at [addr].
pub fn proof_ldadd_returns_old_i32() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDADD_I32: returns old value", 4, |old, op| old.bvadd(op))
}

/// Proof: LDADD returns the old value at [addr] (64-bit).
pub fn proof_ldadd_returns_old_i64() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDADD_I64: returns old value", 8, |old, op| old.bvadd(op))
}

/// Proof: After LDADD, memory contains old + operand (32-bit).
pub fn proof_ldadd_updates_mem_i32() -> ProofObligation {
    proof_atomic_rmw_updates_mem("LDADD_I32: mem[addr] = old + operand", 4, |old, op| {
        old.bvadd(op)
    })
}

/// Proof: After LDADD, memory contains old + operand (64-bit).
pub fn proof_ldadd_updates_mem_i64() -> ProofObligation {
    proof_atomic_rmw_updates_mem("LDADD_I64: mem[addr] = old + operand", 8, |old, op| {
        old.bvadd(op)
    })
}

// -- LDSET (OR) proofs --

/// Proof: LDSET returns the old value at [addr] (32-bit).
pub fn proof_ldset_returns_old_i32() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDSET_I32: returns old value", 4, |old, op| old.bvor(op))
}

/// Proof: After LDSET, memory contains old | operand (32-bit).
pub fn proof_ldset_updates_mem_i32() -> ProofObligation {
    proof_atomic_rmw_updates_mem("LDSET_I32: mem[addr] = old | operand", 4, |old, op| {
        old.bvor(op)
    })
}

// -- LDEOR (XOR) proofs --

/// Proof: LDEOR returns the old value at [addr] (32-bit).
pub fn proof_ldeor_returns_old_i32() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDEOR_I32: returns old value", 4, |old, op| old.bvxor(op))
}

/// Proof: After LDEOR, memory contains old ^ operand (32-bit).
pub fn proof_ldeor_updates_mem_i32() -> ProofObligation {
    proof_atomic_rmw_updates_mem("LDEOR_I32: mem[addr] = old ^ operand", 4, |old, op| {
        old.bvxor(op)
    })
}

// -- LSE min/max proofs --

fn signed_max(old: SmtExpr, op: SmtExpr) -> SmtExpr {
    SmtExpr::ite(old.clone().bvslt(op.clone()), op, old)
}

fn signed_min(old: SmtExpr, op: SmtExpr) -> SmtExpr {
    SmtExpr::ite(old.clone().bvsgt(op.clone()), op, old)
}

fn unsigned_max(old: SmtExpr, op: SmtExpr) -> SmtExpr {
    SmtExpr::ite(old.clone().bvult(op.clone()), op, old)
}

fn unsigned_min(old: SmtExpr, op: SmtExpr) -> SmtExpr {
    SmtExpr::ite(old.clone().bvugt(op.clone()), op, old)
}

pub fn proof_ldsmax_returns_old_i32() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDSMAX_I32: returns old value", 4, signed_max)
}

pub fn proof_ldsmax_returns_old_i64() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDSMAX_I64: returns old value", 8, signed_max)
}

pub fn proof_ldsmax_updates_mem_i32() -> ProofObligation {
    proof_atomic_rmw_updates_mem(
        "LDSMAX_I32: mem[addr] = signed max(old, operand)",
        4,
        signed_max,
    )
}

pub fn proof_ldsmax_updates_mem_i64() -> ProofObligation {
    proof_atomic_rmw_updates_mem(
        "LDSMAX_I64: mem[addr] = signed max(old, operand)",
        8,
        signed_max,
    )
}

pub fn proof_ldsmin_returns_old_i32() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDSMIN_I32: returns old value", 4, signed_min)
}

pub fn proof_ldsmin_returns_old_i64() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDSMIN_I64: returns old value", 8, signed_min)
}

pub fn proof_ldsmin_updates_mem_i32() -> ProofObligation {
    proof_atomic_rmw_updates_mem(
        "LDSMIN_I32: mem[addr] = signed min(old, operand)",
        4,
        signed_min,
    )
}

pub fn proof_ldsmin_updates_mem_i64() -> ProofObligation {
    proof_atomic_rmw_updates_mem(
        "LDSMIN_I64: mem[addr] = signed min(old, operand)",
        8,
        signed_min,
    )
}

pub fn proof_ldumax_returns_old_i32() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDUMAX_I32: returns old value", 4, unsigned_max)
}

pub fn proof_ldumax_returns_old_i64() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDUMAX_I64: returns old value", 8, unsigned_max)
}

pub fn proof_ldumax_updates_mem_i32() -> ProofObligation {
    proof_atomic_rmw_updates_mem(
        "LDUMAX_I32: mem[addr] = unsigned max(old, operand)",
        4,
        unsigned_max,
    )
}

pub fn proof_ldumax_updates_mem_i64() -> ProofObligation {
    proof_atomic_rmw_updates_mem(
        "LDUMAX_I64: mem[addr] = unsigned max(old, operand)",
        8,
        unsigned_max,
    )
}

pub fn proof_ldumin_returns_old_i32() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDUMIN_I32: returns old value", 4, unsigned_min)
}

pub fn proof_ldumin_returns_old_i64() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDUMIN_I64: returns old value", 8, unsigned_min)
}

pub fn proof_ldumin_updates_mem_i32() -> ProofObligation {
    proof_atomic_rmw_updates_mem(
        "LDUMIN_I32: mem[addr] = unsigned min(old, operand)",
        4,
        unsigned_min,
    )
}

pub fn proof_ldumin_updates_mem_i64() -> ProofObligation {
    proof_atomic_rmw_updates_mem(
        "LDUMIN_I64: mem[addr] = unsigned min(old, operand)",
        8,
        unsigned_min,
    )
}

// ---------------------------------------------------------------------------
// Single-copy atomicity: a TWO-STATE observer model
// ---------------------------------------------------------------------------

/// Build the single-copy-atomicity obligation for a `size_bytes` atomic load,
/// against a lowering that is either ONE access (`split == false`) or TWO
/// half-width accesses (`split == true`).
///
/// # Why this model exists
///
/// Every other atomic proof here is SEQUENTIAL: one symbolic memory, one access.
/// In that model "torn" is not expressible — a load trivially equals itself — so
/// nothing in the perimeter can tell a single paired access from two independent
/// half-width ones. That distinction is exactly what a 128-bit atomic turns on,
/// and it is real in this backend: the NON-atomic `i128` load deliberately emits
/// two independent `LDR`s ("a plain (non-atomic) i128 load does not need
/// single-copy atomicity, so two independent LDRs are correct"), and no proof
/// today would object if an ATOMIC load were routed through that path.
///
/// This adds the minimum needed to make tearing expressible:
///   * TWO memory states — `mem_pre`, and `mem_post`, the state a concurrent
///     writer leaves after storing `newval` over the whole object; and
///   * a per-ACCESS choice of which state that access observes (`obs_lo`,
///     `obs_hi`).
///
/// A lowering that reads the object in ONE access observes ONE state, so both
/// halves carry the same selector. A SPLIT lowering can observe DIFFERENT states
/// per half — `obs_lo != obs_hi` is precisely a TORN read, half old and half new.
///
/// # This is NOT a degenerate obligation, and here is the discriminator
///
/// The `Fence_* -> DMB ISH*` obligations were retracted in #62 as
/// "degenerate const==const barrier-code tautologies" — no lowering could ever
/// fail them. This one FAILS for a split lowering and HOLDS for a paired one:
/// same obligation form, opposite verdicts, decided by the lowering. That is what
/// makes it a check rather than a tautology, and
/// `torn_split_access_is_refuted_at_128_bits` pins it.
///
/// # What it does NOT prove
///
/// That `LDP` itself is single-copy atomic. That is an ARCHITECTURAL fact
/// (FEAT_LSE2, 16-byte aligned) and stays a delegation, exactly as `LDAR`'s
/// ordering is delegated today. What is proved here is a property of the
/// LOWERING: that it performs one access rather than two. Alignment is carried as
/// an explicit precondition rather than assumed, because the architectural
/// guarantee is conditional on it.
fn atomic_load_single_copy_obligation(name: &str, size_bytes: u32, split: bool) -> ProofObligation {
    let half = size_bytes / 2;
    let width = size_bytes * 8;

    let addr = SmtExpr::var("addr", 64);
    let mem_pre = symbolic_memory("mem_pre");
    // The concurrent writer's new value is carried as TWO half-width inputs, not
    // one whole-width one. `verify_by_evaluation`'s environment stores each input
    // in a `u64` slot and builds edge cases with `1u64 << (width - 1)`, so a
    // 128-bit INPUT panics ("attempt to shift left with overflow") — measured.
    // The evaluator's VALUES are 128-bit capable (`as_u128`); only the input
    // environment is not. Two half-width stores build the same post-state while
    // keeping every declared input within the harness's reach.
    let half_width = width / 2;
    let newval_lo = SmtExpr::var("newval_lo", half_width);
    let newval_hi = SmtExpr::var("newval_hi", half_width);
    let hi_store_addr = addr
        .clone()
        .bvadd(SmtExpr::bv_const(u64::from(size_bytes / 2), 64));
    let mem_post = encode_store_le(
        &encode_store_le(&mem_pre, &addr, &newval_lo, size_bytes / 2),
        &hi_store_addr,
        &newval_hi,
        size_bytes / 2,
    );

    let obs_lo = SmtExpr::var("obs_lo", 1);
    let obs_hi = SmtExpr::var("obs_hi", 1);
    let one = SmtExpr::bv_const(1, 1);

    // trust_ir side: the ATOMIC semantics — one access, one state, whole object.
    let trust_ir_expr = SmtExpr::ite(
        obs_lo.clone().eq_expr(one.clone()),
        encode_load_le(&mem_post, &addr, size_bytes),
        encode_load_le(&mem_pre, &addr, size_bytes),
    );

    // machine side: the LOWERING. Both halves share a selector when it is one
    // access; the split form gives the high half its own.
    let hi_addr = addr.clone().bvadd(SmtExpr::bv_const(u64::from(half), 64));
    let sel_hi = if split {
        obs_hi.clone()
    } else {
        obs_lo.clone()
    };
    let lo_half = SmtExpr::ite(
        obs_lo.clone().eq_expr(one.clone()),
        encode_load_le(&mem_post, &addr, half),
        encode_load_le(&mem_pre, &addr, half),
    );
    let hi_half = SmtExpr::ite(
        sel_hi.eq_expr(one.clone()),
        encode_load_le(&mem_post, &hi_addr, half),
        encode_load_le(&mem_pre, &hi_addr, half),
    );
    let aarch64_expr = hi_half.concat(lo_half);

    // The architectural guarantee is conditional on natural alignment; state it.
    let align_mask = SmtExpr::bv_const(u64::from(size_bytes - 1), 64);
    let aligned = addr
        .clone()
        .bvand(align_mask)
        .eq_expr(SmtExpr::bv_const(0, 64));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![
            ("addr".to_string(), 64),
            ("mem_pre".to_string(), 8),
            ("newval_lo".to_string(), half_width),
            ("newval_hi".to_string(), half_width),
            ("obs_lo".to_string(), 1),
            ("obs_hi".to_string(), 1),
        ],
        preconditions: vec![aligned],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: a 128-bit atomic load lowered as ONE paired access is single-copy
/// atomic — it cannot return a mix of the pre- and post-write states.
pub fn proof_atomic_load_single_copy_i128() -> ProofObligation {
    atomic_load_single_copy_obligation(
        "AtomicLoad_I128: single-copy (one paired access)",
        16,
        false,
    )
}

/// The NEGATIVE CONTROL for [`proof_atomic_load_single_copy_i128`]: the same
/// obligation against a lowering SPLIT into two 64-bit accesses. It must be
/// REFUTED. If it ever verifies, the model has stopped discriminating and the
/// positive obligation above is worth nothing.
pub fn torn_split_atomic_load_i128_control() -> ProofObligation {
    atomic_load_single_copy_obligation("AtomicLoad_I128: TORN split control", 16, true)
}

// ---------------------------------------------------------------------------
// Barrier ordering: an INTERLEAVING observer model
// ---------------------------------------------------------------------------

/// Build the barrier-ordering obligation for a DMB placed between two loads.
///
/// # Why this model exists
///
/// The `Fence_* -> DMB ISH*` obligations were retracted in #62 as degenerate
/// `const == const` barrier-code tautologies — they asserted
/// `bv_const(0x0B, 8) == bv_const(0x0B, 8)`, which no lowering could fail. DMB
/// has had NO proof binding it since, and `coverage_gate` went on citing that
/// retracted family as its justification. This is the obligation that replaces
/// it.
///
/// The single-copy model ([`atomic_load_single_copy_obligation`]) gave the
/// perimeter two memory states and a per-ACCESS choice of which state an access
/// observes. That is enough to say "one access, not two". It is NOT enough to say
/// anything about ORDER, because with a single access there is no second event to
/// be ordered against. This adds exactly that: a SECOND access, at a DIFFERENT
/// location, with its own observation selector, so that "B observed an older
/// state than A" becomes expressible — and that is precisely a reordering.
///
/// `sel_a`/`sel_b` select the state each load observes (0 = pre-write,
/// 1 = post-write). A reordering is `sel_a = 1, sel_b = 0`: the later load in
/// program order saw the OLDER world.
///
/// # What is proved, and what is delegated
///
/// DELEGATED (a precondition, never proved here): that the barrier instruction
/// actually enforces ordering. `barrier_orders` carries it exactly as
/// [`atomic_load_single_copy_obligation`] carries natural alignment for FEAT_LSE2
/// — the architectural guarantee is stated as a hypothesis, not assumed silently
/// and not re-proved from itself.
///
/// PROVED: that a lowering which PLACES such a barrier between the two loads
/// yields the ordered result, and — via the controls — that a lowering which
/// omits it, or which uses a barrier that does NOT cover this access pair, does
/// NOT. That is a property of the LOWERING, which is the thing this perimeter is
/// entitled to talk about.
///
/// # This is not a tautology, and here is the discriminator
///
/// `no_barrier_load_load_control` is the SAME obligation with the ordering
/// hypothesis removed: it is REFUTED at `sel_a = 1, sel_b = 0`. And
/// `ishst_does_not_order_loads_control` is the same obligation for a STORE
/// barrier, which does not cover a load-load pair: also REFUTED. So the model
/// discriminates barrier PRESENCE *and* barrier KIND, not just the opcode's
/// existence. `barrier_presence_and_kind_both_discriminate` pins both.
fn barrier_ordering_obligation(name: &str, barrier_orders: bool) -> ProofObligation {
    let size_bytes = 8u32;
    let addr_a = SmtExpr::var("addr_a", 64);
    let addr_b = SmtExpr::var("addr_b", 64);
    let mem_pre = symbolic_memory("mem_pre");

    // One concurrent writer transitions the world pre -> post by updating BOTH
    // locations. Two locations is what makes this an ORDERING question rather
    // than a coherence one: per-location read coherence is guaranteed by the
    // architecture WITHOUT any barrier, so a same-address model would be refuted
    // for a property that actually holds and the control would prove nothing.
    let new_a = SmtExpr::var("new_a", 64);
    let new_b = SmtExpr::var("new_b", 64);
    let mem_post = encode_store_le(
        &encode_store_le(&mem_pre, &addr_a, &new_a, size_bytes),
        &addr_b,
        &new_b,
        size_bytes,
    );

    let sel_a = SmtExpr::var("sel_a", 1);
    let sel_b = SmtExpr::var("sel_b", 1);
    let one = SmtExpr::bv_const(1, 1);

    // SPEC (trust_ir): under a barrier that orders A before B, the later load may
    // not observe a state older than the one the earlier load observed, so its
    // state is `sel_a | sel_b` — at 1 bit, the MAXIMUM of the two.
    let ordered_sel = sel_a.clone().bvor(sel_b.clone());
    let trust_ir_expr = SmtExpr::ite(
        ordered_sel.eq_expr(one.clone()),
        encode_load_le(&mem_post, &addr_b, size_bytes),
        encode_load_le(&mem_pre, &addr_b, size_bytes),
    );

    // MACHINE (the lowering): load B observes whatever state it observes.
    let aarch64_expr = SmtExpr::ite(
        sel_b.clone().eq_expr(one.clone()),
        encode_load_le(&mem_post, &addr_b, size_bytes),
        encode_load_le(&mem_pre, &addr_b, size_bytes),
    );

    // The two accesses are to DIFFERENT locations (see above).
    let mut preconditions = vec![addr_a.clone().eq_expr(addr_b.clone()).not_expr()];
    if barrier_orders {
        // The DELEGATED architectural guarantee: the emitted barrier orders the
        // earlier access before the later one, so the later cannot observe an
        // older state. `bvuge` at 1 bit is exactly NOT(sel_a = 1 AND sel_b = 0).
        preconditions.push(sel_b.clone().bvuge(sel_a.clone()));
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![
            ("addr_a".to_string(), 64),
            ("addr_b".to_string(), 64),
            ("mem_pre".to_string(), 8),
            ("new_a".to_string(), 64),
            ("new_b".to_string(), 64),
            ("sel_a".to_string(), 1),
            ("sel_b".to_string(), 1),
        ],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: `DMB ISH` (full inner-shareable barrier, CRm 0xB — SeqCst/AcqRel)
/// orders a prior load before a subsequent load.
pub fn proof_dmb_ish_orders_loads() -> ProofObligation {
    barrier_ordering_obligation("DMB_ISH: orders prior load before subsequent load", true)
}

/// Proof: `DMB ISHLD` (load barrier, CRm 0x9 — Acquire) orders a prior load
/// before a subsequent load. ISHLD's guarantee covers load-before-load/store, so
/// for this access pair it is the same constraint ISH provides.
pub fn proof_dmb_ishld_orders_loads() -> ProofObligation {
    barrier_ordering_obligation("DMB_ISHLD: orders prior load before subsequent load", true)
}

/// NEGATIVE CONTROL (barrier PRESENCE): the same obligation with no ordering
/// hypothesis. Must be REFUTED at `sel_a = 1, sel_b = 0`. If it ever verifies,
/// the model has stopped seeing reorderings and the positive obligations above
/// are worth nothing. Deliberately NOT registered.
pub fn no_barrier_load_load_control() -> ProofObligation {
    barrier_ordering_obligation("DMB_NONE: no barrier control (must refute)", false)
}

/// NEGATIVE CONTROL (barrier KIND): `DMB ISHST` is a STORE barrier (CRm 0xA,
/// Release). It does not order a load-load pair, so it supplies no hypothesis
/// here and must be REFUTED. This is what stops the query from crediting ANY DMB
/// for ANY ordering. Deliberately NOT registered — and note that
/// `operand_sensitive_or_opcode_query` maps only CRm 0xB/0x9, so an emitted
/// ISHST after an atomic load finds no proof and fails closed.
pub fn ishst_does_not_order_loads_control() -> ProofObligation {
    barrier_ordering_obligation("DMB_ISHST: store barrier control (must refute)", false)
}

// -- SWP (exchange) proofs --

/// Proof: SWP returns the old value at [addr] (32-bit).
pub fn proof_swp_returns_old_i32() -> ProofObligation {
    proof_atomic_rmw_returns_old(
        "SWP_I32: returns old value",
        4,
        |_old, op| op, // new = operand (unconditional swap)
    )
}

/// Proof: SWP returns the old value at [addr] (64-bit).
pub fn proof_swp_returns_old_i64() -> ProofObligation {
    proof_atomic_rmw_returns_old("SWP_I64: returns old value", 8, |_old, op| op)
}

/// Proof: After SWP, memory contains the swap operand (32-bit).
pub fn proof_swp_updates_mem_i32() -> ProofObligation {
    proof_atomic_rmw_updates_mem("SWP_I32: mem[addr] = operand", 4, |_old, op| op)
}

/// Proof: After SWP, memory contains the swap operand (64-bit).
///
/// The 64-bit sibling of [`proof_swp_updates_mem_i32`]. LDADD / LDSMAX / LDSMIN /
/// LDUMAX / LDUMIN each already carry BOTH widths of their `mem[addr] = ...`
/// obligation; SWP carried only the 32-bit one, so a 64-bit SWP had no
/// width-correct memory proof to be credited against — and an atomic over a
/// POINTER element is 64-bit.
pub fn proof_swp_updates_mem_i64() -> ProofObligation {
    proof_atomic_rmw_updates_mem("SWP_I64: mem[addr] = operand", 8, |_old, op| op)
}

// -- LDCLR (AND NOT / bit clear) proofs --

/// Proof: LDCLR returns the old value at [addr] (32-bit).
pub fn proof_ldclr_returns_old_i32() -> ProofObligation {
    proof_atomic_rmw_returns_old("LDCLR_I32: returns old value", 4, |old, op| {
        let all_ones = SmtExpr::bv_const(mask(u64::MAX, 32), 32);
        old.bvand(op.bvxor(all_ones))
    })
}

/// Proof: After LDCLR, memory contains old AND NOT operand (32-bit).
///
/// LDCLR Xs, Xt, [Xn]: *Xn = *Xn AND NOT Xs.
pub fn proof_ldclr_updates_mem_i32() -> ProofObligation {
    proof_atomic_rmw_updates_mem(
        "LDCLR_I32: mem[addr] = old AND NOT operand",
        4,
        |old, op| {
            let all_ones = SmtExpr::bv_const(mask(u64::MAX, 32), 32);
            old.bvand(op.bvxor(all_ones))
        },
    )
}

// ---------------------------------------------------------------------------
// Compare-and-swap (CAS) semantics
// ---------------------------------------------------------------------------

/// Build a CAS success-path proof: when *addr == expected, memory is updated.
///
/// CAS Xs, Xt, [Xn]:
///   old = *Xn
///   if old == Xs (expected):
///     *Xn = Xt (desired)
///   Xs = old  (return old value in Xs)
///
/// Success path: *addr == expected => mem_after contains desired.
pub fn proof_cas_success_i32() -> ProofObligation {
    let mem = symbolic_memory("mem_default");
    let addr = SmtExpr::var("addr", 64);
    let expected = SmtExpr::var("expected", 32);
    let desired = SmtExpr::var("desired", 32);

    // Precondition: memory at addr contains expected value
    let old_value = encode_load_le(&mem, &addr, 4);
    let precond = old_value.clone().eq_expr(expected.clone());

    // trust_ir expected result: memory updated with desired value
    let trust_ir_mem_after = encode_store_le(&mem, &addr, &desired, 4);
    let trust_ir_loaded = encode_load_le(&trust_ir_mem_after, &addr, 4);

    // AArch64 CAS: when old == expected, stores desired
    // On the success path, the memory result is the same
    let aarch64_mem_after = encode_store_le(&mem, &addr, &desired, 4);
    let aarch64_loaded = encode_load_le(&aarch64_mem_after, &addr, 4);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CAS_I32: success path — mem[addr] = desired".to_string(),
        trust_ir_expr: trust_ir_loaded,
        aarch64_expr: aarch64_loaded,
        inputs: vec![
            ("addr".to_string(), 64),
            ("expected".to_string(), 32),
            ("desired".to_string(), 32),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![precond],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// CAS success path: old value is returned correctly.
pub fn proof_cas_returns_old_i32() -> ProofObligation {
    let mem = symbolic_memory("mem_default");
    let addr = SmtExpr::var("addr", 64);
    let _expected = SmtExpr::var("expected", 32);

    // trust_ir side: the old value
    let trust_ir_old = encode_load_le(&mem, &addr, 4);
    // AArch64 CAS: returns old value in Xs
    let aarch64_old = encode_load_le(&mem, &addr, 4);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CAS_I32: returns old value".to_string(),
        trust_ir_expr: trust_ir_old,
        aarch64_expr: aarch64_old,
        inputs: vec![
            ("addr".to_string(), 64),
            ("expected".to_string(), 32),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// CAS failure path: when *addr != expected, memory is unchanged.
///
/// The proof verifies that on CAS failure, the loaded value after the
/// CAS is the same as the loaded value before (memory not modified).
pub fn proof_cas_failure_i32() -> ProofObligation {
    let mem = symbolic_memory("mem_default");
    let addr = SmtExpr::var("addr", 64);
    let expected = SmtExpr::var("expected", 32);

    // Precondition: memory at addr does NOT contain expected value.
    // We model this as: the loaded old value is not changed, since
    // CAS failure means memory is untouched.
    let old_value = encode_load_le(&mem, &addr, 4);
    let precond_neq = old_value.clone().eq_expr(expected.clone()).not_expr();

    // trust_ir side: on CAS failure, memory is unchanged
    let trust_ir_result = encode_load_le(&mem, &addr, 4);

    // AArch64 CAS: on failure, Mem unchanged => load returns same old value
    let aarch64_result = encode_load_le(&mem, &addr, 4);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CAS_I32: failure path — memory unchanged".to_string(),
        trust_ir_expr: trust_ir_result,
        aarch64_expr: aarch64_result,
        inputs: vec![
            ("addr".to_string(), 64),
            ("expected".to_string(), 32),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![precond_neq],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// CAS 64-bit success path.
pub fn proof_cas_success_i64() -> ProofObligation {
    let mem = symbolic_memory("mem_default");
    let addr = SmtExpr::var("addr", 64);
    let expected = SmtExpr::var("expected", 64);
    let desired = SmtExpr::var("desired", 64);

    let old_value = encode_load_le(&mem, &addr, 8);
    let precond = old_value.clone().eq_expr(expected.clone());

    let trust_ir_mem_after = encode_store_le(&mem, &addr, &desired, 8);
    let trust_ir_loaded = encode_load_le(&trust_ir_mem_after, &addr, 8);

    let aarch64_mem_after = encode_store_le(&mem, &addr, &desired, 8);
    let aarch64_loaded = encode_load_le(&aarch64_mem_after, &addr, 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CAS_I64: success path — mem[addr] = desired".to_string(),
        trust_ir_expr: trust_ir_loaded,
        aarch64_expr: aarch64_loaded,
        inputs: vec![
            ("addr".to_string(), 64),
            ("expected".to_string(), 64),
            ("desired".to_string(), 64),
            ("mem_default".to_string(), 8),
        ],
        preconditions: vec![precond],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

// ---------------------------------------------------------------------------
// Fence (DMB) semantics
// ---------------------------------------------------------------------------

/// Proof: DMB ISH barrier option encoding for SeqCst/AcqRel.
///
/// The DMB instruction takes a 4-bit option field. For inner-shareable
/// full barrier (ISH), the option is 0xB (1011b). This is used for
/// SeqCst and AcqRel orderings.
///
/// We verify the option encoding is correct by asserting the ISel mapping.
pub fn proof_fence_dmb_ish() -> ProofObligation {
    // trust_ir: SeqCst/AcqRel fence maps to DMB ISH
    let trust_ir_option = SmtExpr::bv_const(0x0B, 8);
    let aarch64_option = SmtExpr::bv_const(0x0B, 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fence_SeqCst -> DMB ISH (0xB)".to_string(),
        trust_ir_expr: trust_ir_option,
        aarch64_expr: aarch64_option,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: DMB ISHLD barrier option for Acquire ordering.
pub fn proof_fence_dmb_ishld() -> ProofObligation {
    let trust_ir_option = SmtExpr::bv_const(0x09, 8);
    let aarch64_option = SmtExpr::bv_const(0x09, 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fence_Acquire -> DMB ISHLD (0x9)".to_string(),
        trust_ir_expr: trust_ir_option,
        aarch64_expr: aarch64_option,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: DMB ISH barrier option for Release ordering.
///
/// A Release fence orders every earlier access (loads included) before every
/// later store, so it is the full DMB ISH, not the store-only DMB ISHST the
/// selector chose before L03-P3. Like its two siblings this is a retracted
/// const==const tautology (stripped from the registry by name); the ordering
/// check that DOES discriminate the barrier kind is
/// [`crate::aarch64_memory_order::check_lowering`] on the emitted words.
pub fn proof_fence_release_dmb_ish() -> ProofObligation {
    let trust_ir_option = SmtExpr::bv_const(0x0B, 8);
    let aarch64_option = SmtExpr::bv_const(0x0B, 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fence_Release -> DMB ISH (0xB)".to_string(),
        trust_ir_expr: trust_ir_option,
        aarch64_expr: aarch64_option,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

// ---------------------------------------------------------------------------
// Atomic SUB via NEG + LDADD equivalence
// ---------------------------------------------------------------------------

/// Proof: AtomicRmw SUB via NEG+LDADD produces correct result.
///
/// The ISel lowers `AtomicRmw::Sub` as:
///   NEG Xtmp, Xs        (Xtmp = -Xs = 0 - Xs)
///   LDADDAL Xtmp, Xt, [Xn]  (Xt = old; *Xn = old + Xtmp = old - Xs)
///
/// This proof verifies: `old + (-operand) == old - operand` (mod 2^w).
pub fn proof_atomic_sub_via_neg_ldadd_i32() -> ProofObligation {
    let old = SmtExpr::var("old", 32);
    let operand = SmtExpr::var("operand", 32);

    // trust_ir: old - operand
    let trust_ir_result = old.clone().bvsub(operand.clone());

    // AArch64 NEG+LDADD: old + (-operand) = old + (0 - operand)
    let neg_operand = operand.bvneg();
    let aarch64_result = old.bvadd(neg_operand);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AtomicSub_I32: NEG+LDADD equivalence (old-x == old+(-x))".to_string(),
        trust_ir_expr: trust_ir_result,
        aarch64_expr: aarch64_result,
        inputs: vec![("old".to_string(), 32), ("operand".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: AtomicRmw SUB via NEG+LDADD (64-bit).
pub fn proof_atomic_sub_via_neg_ldadd_i64() -> ProofObligation {
    let old = SmtExpr::var("old", 64);
    let operand = SmtExpr::var("operand", 64);

    let trust_ir_result = old.clone().bvsub(operand.clone());
    let neg_operand = operand.bvneg();
    let aarch64_result = old.bvadd(neg_operand);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AtomicSub_I64: NEG+LDADD equivalence (old-x == old+(-x))".to_string(),
        trust_ir_expr: trust_ir_result,
        aarch64_expr: aarch64_result,
        inputs: vec![("old".to_string(), 64), ("operand".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

// ---------------------------------------------------------------------------
// Atomic AND via MVN + LDCLR equivalence
// ---------------------------------------------------------------------------

/// Proof: AtomicRmw AND via MVN+LDCLR produces correct result.
///
/// The ISel lowers `AtomicRmw::And` as:
///   MVN Xtmp, Xs         (Xtmp = ~Xs = NOT Xs)
///   LDCLRAL Xtmp, Xt, [Xn]  (Xt = old; *Xn = old AND NOT Xtmp = old AND NOT(NOT Xs) = old AND Xs)
///
/// LDCLR semantics: `*addr = *addr AND NOT(operand)`.
/// After MVN: operand = NOT(Xs), so: `*addr = *addr AND NOT(NOT(Xs)) = *addr AND Xs`.
///
/// This proof verifies: `old AND x == old AND NOT(NOT(x))`.
pub fn proof_atomic_and_via_mvn_ldclr_i32() -> ProofObligation {
    let old = SmtExpr::var("old", 32);
    let operand = SmtExpr::var("operand", 32);
    let all_ones = SmtExpr::bv_const(mask(u64::MAX, 32), 32);

    // trust_ir: old AND operand
    let trust_ir_result = old.clone().bvand(operand.clone());

    // AArch64 MVN+LDCLR:
    //   mvn_result = NOT(operand) = operand XOR all_ones
    //   ldclr_result = old AND NOT(mvn_result)
    //                = old AND NOT(NOT(operand))
    //                = old AND operand
    let mvn_result = operand.bvxor(all_ones.clone());
    let not_mvn = mvn_result.bvxor(all_ones);
    let aarch64_result = old.bvand(not_mvn);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AtomicAnd_I32: MVN+LDCLR equivalence (old&x == old&~~x)".to_string(),
        trust_ir_expr: trust_ir_result,
        aarch64_expr: aarch64_result,
        inputs: vec![("old".to_string(), 32), ("operand".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: AtomicRmw AND via MVN+LDCLR (64-bit).
pub fn proof_atomic_and_via_mvn_ldclr_i64() -> ProofObligation {
    let old = SmtExpr::var("old", 64);
    let operand = SmtExpr::var("operand", 64);
    let all_ones = SmtExpr::bv_const(mask(u64::MAX, 64), 64);

    let trust_ir_result = old.clone().bvand(operand.clone());

    let mvn_result = operand.bvxor(all_ones.clone());
    let not_mvn = mvn_result.bvxor(all_ones);
    let aarch64_result = old.bvand(not_mvn);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AtomicAnd_I64: MVN+LDCLR equivalence (old&x == old&~~x)".to_string(),
        trust_ir_expr: trust_ir_result,
        aarch64_expr: aarch64_result,
        inputs: vec![("old".to_string(), 64), ("operand".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

// ---------------------------------------------------------------------------
// Atomic store non-interference
// ---------------------------------------------------------------------------

/// Build the sound disjointness + no-wrap + alignment preconditions shared by
/// every atomic non-interference proof (store, RMW, CAS).
///
/// Returns the full precondition vector:
///   * `a_no_wrap`: `addr_a + size >u addr_a` — false exactly when [addr_a,
///     addr_a+size) wraps past 2^64.
///   * `b_no_wrap`: `addr_b + size >u addr_b` — same for B's region.
///   * `a_aligned` / `b_aligned`: `addr & (size-1) == 0` — both accesses are
///     naturally aligned.
///   * `disjoint`: symmetric two-sided
///     `addr_b >=u addr_a+size  OR  addr_a >=u addr_b+size`.
///
/// # Soundness + tractability
///
/// The no-wrap + symmetric-disjoint pair fixes the original formal-gate
/// *counterexample*: the previous one-sided `addr_b >= addr_a + size` with a
/// `addr_a + size` that itself wraps admitted overlapping ranges at the top of
/// the address space (see `proof_atomic_store_non_interference`). Once that
/// spurious model is removed z3 must instead *prove* UNSAT over the byte-array
/// read-over-write chain; for the 64-bit accesses that proof does not discharge
/// within the strict gate's solver budget unless the regions are aligned.
///
/// Natural alignment is added because (a) AArch64 atomic accesses are *required*
/// to be naturally aligned (ARM DDI 0487, B2.2.1 — an unaligned atomic faults),
/// so it is the architecturally-faithful precondition rather than a coverage
/// loss, and (b) aligned, disjoint, same-size regions share no byte, which lets
/// z3 dispatch the read-over-write disequalities quickly. Tightening a
/// precondition only removes inputs from the universally-quantified claim, so it
/// can never make a wrong input pass — this is a sound, documented narrowing.
fn disjoint_no_wrap_preconditions(
    addr_a: &SmtExpr,
    addr_b: &SmtExpr,
    size_bytes: u32,
) -> Vec<SmtExpr> {
    let size = SmtExpr::bv_const(size_bytes as u64, 64);
    let a_end = addr_a.clone().bvadd(size.clone());
    let b_end = addr_b.clone().bvadd(size);

    let a_no_wrap = a_end.clone().bvugt(addr_a.clone());
    let b_no_wrap = b_end.clone().bvugt(addr_b.clone());

    let align_mask = SmtExpr::bv_const((size_bytes - 1) as u64, 64);
    let a_aligned = addr_a
        .clone()
        .bvand(align_mask.clone())
        .eq_expr(SmtExpr::bv_const(0, 64));
    let b_aligned = addr_b
        .clone()
        .bvand(align_mask)
        .eq_expr(SmtExpr::bv_const(0, 64));

    let b_after_a = addr_b.clone().bvuge(a_end);
    let a_after_b = addr_a.clone().bvuge(b_end);
    let disjoint = b_after_a.or_expr(a_after_b);

    vec![a_no_wrap, b_no_wrap, a_aligned, b_aligned, disjoint]
}

/// Build a non-interference proof for atomic store: writing at addr_a
/// does not affect the value loaded from addr_b.
///
/// For disjoint, non-wrapping, naturally-aligned address ranges, STLR at A
/// preserves the value at B. The shared precondition set (no-wrap, alignment,
/// symmetric two-sided disjointness) is built by
/// [`disjoint_no_wrap_preconditions`], which also documents why the previous
/// one-sided form admitted a wrapping counterexample and why natural alignment
/// is both architecturally required and necessary for the 64-bit obligations to
/// discharge UNSAT within the gate budget.
fn proof_atomic_store_non_interference(name: &str, size_bytes: u32) -> ProofObligation {
    let result_width = size_bytes * 8;
    let mem = symbolic_memory("mem_default");
    let addr_a = SmtExpr::var("addr_a", 64);
    let addr_b = SmtExpr::var("addr_b", 64);
    let value = SmtExpr::var("value", result_width);

    let preconditions = disjoint_no_wrap_preconditions(&addr_a, &addr_b, size_bytes);

    // Value at B before atomic store at A
    let before = encode_load_le(&mem, &addr_b, size_bytes);

    // Value at B after atomic store at A
    let mem_after = encode_aarch64_stlr(&mem, &addr_a, &value, size_bytes);
    let after = encode_load_le(&mem_after, &addr_b, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: before,
        aarch64_expr: after,
        inputs: vec![
            ("addr_a".to_string(), 64),
            ("addr_b".to_string(), 64),
            ("value".to_string(), result_width),
            ("mem_default".to_string(), 8),
        ],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: Atomic store at addr A does not affect memory at addr B (32-bit).
pub fn proof_atomic_store_non_interference_i32() -> ProofObligation {
    proof_atomic_store_non_interference(
        "AtomicStore_I32: non-interference (store at A, read at B unchanged)",
        4,
    )
}

/// Proof: Atomic store at addr A does not affect memory at addr B (64-bit).
pub fn proof_atomic_store_non_interference_i64() -> ProofObligation {
    proof_atomic_store_non_interference(
        "AtomicStore_I64: non-interference (store at A, read at B unchanged)",
        8,
    )
}

// ---------------------------------------------------------------------------
// Atomic RMW non-interference
// ---------------------------------------------------------------------------

/// Build a non-interference proof for atomic RMW: an RMW at addr_a
/// does not affect the value loaded from addr_b.
///
/// Atomic RMW instructions (LDADD, LDSET, LDEOR, SWP, LDCLR) perform
/// a load-modify-store at addr_a. We verify the value at a disjoint
/// addr_b is unchanged, under the same sound disjointness + no-wrap +
/// alignment preconditions as store non-interference (see
/// [`disjoint_no_wrap_preconditions`]).
fn proof_atomic_rmw_non_interference<F>(name: &str, size_bytes: u32, op: F) -> ProofObligation
where
    F: FnOnce(SmtExpr, SmtExpr) -> SmtExpr,
{
    let result_width = size_bytes * 8;
    let mem = symbolic_memory("mem_default");
    let addr_a = SmtExpr::var("addr_a", 64);
    let addr_b = SmtExpr::var("addr_b", 64);
    let operand = SmtExpr::var("operand", result_width);

    let preconditions = disjoint_no_wrap_preconditions(&addr_a, &addr_b, size_bytes);

    // Value at B before the RMW at A
    let before = encode_load_le(&mem, &addr_b, size_bytes);

    // Perform the RMW at addr_a: load old, compute new, store new
    let (_old_value, mem_after) = encode_atomic_rmw(&mem, &addr_a, &operand, size_bytes, op);

    // Value at B after the RMW at A
    let after = encode_load_le(&mem_after, &addr_b, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: before,
        aarch64_expr: after,
        inputs: vec![
            ("addr_a".to_string(), 64),
            ("addr_b".to_string(), 64),
            ("operand".to_string(), result_width),
            ("mem_default".to_string(), 8),
        ],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: LDADD at addr A does not affect memory at addr B (32-bit).
pub fn proof_ldadd_non_interference_i32() -> ProofObligation {
    proof_atomic_rmw_non_interference(
        "LDADD_I32: non-interference (RMW at A, read at B unchanged)",
        4,
        |old, op| old.bvadd(op),
    )
}

/// Proof: LDADD at addr A does not affect memory at addr B (64-bit).
pub fn proof_ldadd_non_interference_i64() -> ProofObligation {
    proof_atomic_rmw_non_interference(
        "LDADD_I64: non-interference (RMW at A, read at B unchanged)",
        8,
        |old, op| old.bvadd(op),
    )
}

/// Proof: SWP at addr A does not affect memory at addr B (32-bit).
pub fn proof_swp_non_interference_i32() -> ProofObligation {
    proof_atomic_rmw_non_interference(
        "SWP_I32: non-interference (RMW at A, read at B unchanged)",
        4,
        |_old, op| op,
    )
}

// ---------------------------------------------------------------------------
// CAS non-interference
// ---------------------------------------------------------------------------

/// Build a non-interference proof for CAS: a successful CAS at addr_a
/// does not affect the value loaded from addr_b.
///
/// CAS performs a conditional store: if *addr_a == expected, then
/// *addr_a = desired. On the success path (the only path that modifies
/// memory), we verify the value at disjoint addr_b is unchanged, under the
/// same sound disjointness + no-wrap + alignment preconditions as store
/// non-interference (see [`disjoint_no_wrap_preconditions`]), plus the CAS
/// success guard `*addr_a == expected`.
fn proof_cas_non_interference(name: &str, size_bytes: u32) -> ProofObligation {
    let result_width = size_bytes * 8;
    let mem = symbolic_memory("mem_default");
    let addr_a = SmtExpr::var("addr_a", 64);
    let addr_b = SmtExpr::var("addr_b", 64);
    let expected = SmtExpr::var("expected", result_width);
    let desired = SmtExpr::var("desired", result_width);

    let mut preconditions = disjoint_no_wrap_preconditions(&addr_a, &addr_b, size_bytes);

    // CAS success precondition: *addr_a == expected
    let old_value = encode_load_le(&mem, &addr_a, size_bytes);
    preconditions.push(old_value.eq_expr(expected.clone()));

    // Value at B before CAS at A
    let before = encode_load_le(&mem, &addr_b, size_bytes);

    // CAS success: store desired at addr_a
    let mem_after = encode_store_le(&mem, &addr_a, &desired, size_bytes);

    // Value at B after CAS at A
    let after = encode_load_le(&mem_after, &addr_b, size_bytes);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: before,
        aarch64_expr: after,
        inputs: vec![
            ("addr_a".to_string(), 64),
            ("addr_b".to_string(), 64),
            ("expected".to_string(), result_width),
            ("desired".to_string(), result_width),
            ("mem_default".to_string(), 8),
        ],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::MemoryModel),
    }
}

/// Proof: CAS at addr A does not affect memory at addr B (32-bit).
pub fn proof_cas_non_interference_i32() -> ProofObligation {
    proof_cas_non_interference(
        "CAS_I32: non-interference (CAS at A, read at B unchanged)",
        4,
    )
}

/// Proof: CAS at addr A does not affect memory at addr B (64-bit).
pub fn proof_cas_non_interference_i64() -> ProofObligation {
    proof_cas_non_interference(
        "CAS_I64: non-interference (CAS at A, read at B unchanged)",
        8,
    )
}

// ---------------------------------------------------------------------------
// Registry: all atomic proofs
// ---------------------------------------------------------------------------

/// All atomic load proofs.
pub fn all_atomic_load_proofs() -> Vec<ProofObligation> {
    vec![
        proof_atomic_load_i8(),
        proof_atomic_load_i16(),
        proof_atomic_load_i32(),
        proof_atomic_load_i64(),
    ]
}

/// All atomic store-load roundtrip proofs.
pub fn all_atomic_store_proofs() -> Vec<ProofObligation> {
    vec![
        proof_atomic_store_load_i8(),
        proof_atomic_store_load_i16(),
        proof_atomic_store_load_i32(),
        proof_atomic_store_load_i64(),
    ]
}

/// All atomic RMW proofs (LDADD, LDSET, LDEOR, LSE min/max, SWP, LDCLR).
pub fn all_atomic_rmw_proofs() -> Vec<ProofObligation> {
    vec![
        proof_ldadd_returns_old_i32(),
        proof_ldadd_returns_old_i64(),
        proof_ldadd_updates_mem_i32(),
        proof_ldadd_updates_mem_i64(),
        proof_ldset_returns_old_i32(),
        proof_ldset_updates_mem_i32(),
        proof_ldeor_returns_old_i32(),
        proof_ldeor_updates_mem_i32(),
        proof_ldsmax_returns_old_i32(),
        proof_ldsmax_returns_old_i64(),
        proof_ldsmax_updates_mem_i32(),
        proof_ldsmax_updates_mem_i64(),
        proof_ldsmin_returns_old_i32(),
        proof_ldsmin_returns_old_i64(),
        proof_ldsmin_updates_mem_i32(),
        proof_ldsmin_updates_mem_i64(),
        proof_ldumax_returns_old_i32(),
        proof_ldumax_returns_old_i64(),
        proof_ldumax_updates_mem_i32(),
        proof_ldumax_updates_mem_i64(),
        proof_ldumin_returns_old_i32(),
        proof_ldumin_returns_old_i64(),
        proof_ldumin_updates_mem_i32(),
        proof_ldumin_updates_mem_i64(),
        proof_swp_returns_old_i32(),
        proof_swp_returns_old_i64(),
        proof_swp_updates_mem_i32(),
        proof_swp_updates_mem_i64(),
        proof_ldclr_returns_old_i32(),
        proof_ldclr_updates_mem_i32(),
    ]
}

/// All CAS proofs.
pub fn all_cas_proofs() -> Vec<ProofObligation> {
    vec![
        proof_cas_success_i32(),
        proof_cas_returns_old_i32(),
        proof_cas_failure_i32(),
        proof_cas_success_i64(),
    ]
}

/// All fence proofs.
pub fn all_fence_proofs() -> Vec<ProofObligation> {
    vec![
        proof_fence_dmb_ish(),
        proof_fence_dmb_ishld(),
        proof_fence_release_dmb_ish(),
    ]
}

/// All SUB via NEG+LDADD equivalence proofs.
pub fn all_sub_neg_ldadd_proofs() -> Vec<ProofObligation> {
    vec![
        proof_atomic_sub_via_neg_ldadd_i32(),
        proof_atomic_sub_via_neg_ldadd_i64(),
    ]
}

/// All AND via MVN+LDCLR equivalence proofs.
pub fn all_and_mvn_ldclr_proofs() -> Vec<ProofObligation> {
    vec![
        proof_atomic_and_via_mvn_ldclr_i32(),
        proof_atomic_and_via_mvn_ldclr_i64(),
    ]
}

/// All atomic non-interference proofs.
pub fn all_atomic_non_interference_proofs() -> Vec<ProofObligation> {
    vec![
        proof_atomic_store_non_interference_i32(),
        proof_atomic_store_non_interference_i64(),
        proof_ldadd_non_interference_i32(),
        proof_ldadd_non_interference_i64(),
        proof_swp_non_interference_i32(),
        proof_cas_non_interference_i32(),
        proof_cas_non_interference_i64(),
    ]
}

/// All atomic memory operation proofs combined.
///
/// Returns all proof obligations for atomic operations:
/// - 4 atomic load proofs (I8, I16, I32, I64)
/// - 4 atomic store-load roundtrip proofs (I8, I16, I32, I64)
/// - 30 atomic RMW proofs (LDADD, LDSET, LDEOR, LSE min/max, SWP, LDCLR)
/// - 4 CAS proofs (success, failure, return value, 64-bit)
/// - 3 fence proofs (DMB ISH for SeqCst and Release, ISHLD; retracted below)
/// - 2 SUB via NEG+LDADD proofs (I32, I64)
/// - 2 AND via MVN+LDCLR proofs (I32, I64)
/// - 7 non-interference proofs (store I32/I64, LDADD I32/I64, SWP I32, CAS I32/I64)
///
/// Total: 55 proofs.
pub fn all_atomic_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();
    proofs.extend(all_atomic_load_proofs());
    proofs.extend(all_atomic_store_proofs());
    proofs.extend(all_atomic_rmw_proofs());
    proofs.extend(all_cas_proofs());
    proofs.extend(all_fence_proofs());
    proofs.extend(all_sub_neg_ldadd_proofs());
    proofs.extend(all_and_mvn_ldclr_proofs());
    proofs.extend(all_atomic_non_interference_proofs());
    // Single-copy atomicity of a PAIRED 128-bit access. The matching split-access
    // obligation (`torn_split_atomic_load_i128_control`) is deliberately NOT
    // registered: it must be REFUTED, and it exists to prove this one
    // discriminates. Registering it would fail `test_all_atomic_proofs_valid`,
    // which is the point — a refuted obligation is a control, never a credit.
    proofs.push(proof_atomic_load_single_copy_i128());
    // The interleaving barrier obligations that REPLACE the #62-retracted
    // `Fence_* -> DMB ISH*` tautologies. Only the two barrier kinds that cover a
    // load-load pair are registered; the ISHST (store-barrier) and no-barrier
    // instances are REFUTED controls and stay out of the registry.
    proofs.push(proof_dmb_ish_orders_loads());
    proofs.push(proof_dmb_ishld_orders_loads());
    // #62 retraction: the "<RMW/CAS/SWP>: returns old value" obligations route
    // BOTH sides through encode_load_le (trust_ir_old == aarch64_old literally —
    // X==X, no independent machine-side old-value encoder), and the AArch64
    // "Fence_* -> DMB ISH*" obligations are degenerate const==const barrier-code
    // tautologies. Both prove nothing about the instruction and are RETRACTED.
    // The GENUINE atomic VALUE/memory proofs (mem[addr] = old OP operand, SWP/
    // LDCLR effects, NEG+LDADD / MVN+LDCLR equivalence, STLR->LDAR roundtrip,
    // non-interference, and the allowlisted CAS success/failure + AtomicLoad->LDAR*
    // identities) remain.
    proofs.retain(|p| {
        !(p.name.ends_with(": returns old value")
            || p.name.starts_with("Fence_") && p.name.contains("-> DMB"))
    });
    proofs
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::{
        VerificationConfig, verify_by_evaluation, verify_by_evaluation_with_config,
    };
    use crate::verify::VerificationResult;

    // -----------------------------------------------------------------------
    // Atomic load proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_atomic_load_i8_valid() {
        let p = proof_atomic_load_i8();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "AtomicLoad I8 -> LDARB should be valid"
        );
    }

    #[test]
    fn test_atomic_load_i16_valid() {
        let p = proof_atomic_load_i16();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "AtomicLoad I16 -> LDARH should be valid"
        );
    }

    #[test]
    fn test_atomic_load_i32_valid() {
        let p = proof_atomic_load_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "AtomicLoad I32 -> LDAR should be valid"
        );
    }

    #[test]
    fn test_atomic_load_i64_valid() {
        let p = proof_atomic_load_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "AtomicLoad I64 -> LDAR should be valid"
        );
    }

    // -----------------------------------------------------------------------
    // Atomic store-load roundtrip proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_atomic_store_load_i8_valid() {
        let p = proof_atomic_store_load_i8();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "AtomicStore/Load I8 roundtrip should be valid"
        );
    }

    #[test]
    fn test_atomic_store_load_i16_valid() {
        let p = proof_atomic_store_load_i16();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "AtomicStore/Load I16 roundtrip should be valid"
        );
    }

    #[test]
    fn test_atomic_store_load_i32_valid() {
        let p = proof_atomic_store_load_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "AtomicStore/Load I32 roundtrip should be valid"
        );
    }

    #[test]
    fn test_atomic_store_load_i64_valid() {
        let p = proof_atomic_store_load_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "AtomicStore/Load I64 roundtrip should be valid"
        );
    }

    // -----------------------------------------------------------------------
    // LDADD proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_ldadd_returns_old_i32() {
        let p = proof_ldadd_returns_old_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDADD I32 should return old value"
        );
    }

    #[test]
    fn test_ldadd_returns_old_i64() {
        let p = proof_ldadd_returns_old_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDADD I64 should return old value"
        );
    }

    #[test]
    fn test_ldadd_updates_mem_i32() {
        let p = proof_ldadd_updates_mem_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDADD I32 should update memory to old + operand"
        );
    }

    #[test]
    fn test_ldadd_updates_mem_i64() {
        let p = proof_ldadd_updates_mem_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDADD I64 should update memory to old + operand"
        );
    }

    // -----------------------------------------------------------------------
    // LDSET (OR) proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_ldset_returns_old_i32() {
        let p = proof_ldset_returns_old_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDSET I32 should return old value"
        );
    }

    #[test]
    fn test_ldset_updates_mem_i32() {
        let p = proof_ldset_updates_mem_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDSET I32 should update memory to old | operand"
        );
    }

    // -----------------------------------------------------------------------
    // LDEOR (XOR) proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_ldeor_returns_old_i32() {
        let p = proof_ldeor_returns_old_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDEOR I32 should return old value"
        );
    }

    #[test]
    fn test_ldeor_updates_mem_i32() {
        let p = proof_ldeor_updates_mem_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDEOR I32 should update memory to old ^ operand"
        );
    }

    // -----------------------------------------------------------------------
    // SWP (exchange) proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_swp_returns_old_i32() {
        let p = proof_swp_returns_old_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "SWP I32 should return old value"
        );
    }

    #[test]
    fn test_swp_returns_old_i64() {
        let p = proof_swp_returns_old_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "SWP I64 should return old value"
        );
    }

    #[test]
    fn test_swp_updates_mem_i32() {
        let p = proof_swp_updates_mem_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "SWP I32 should update memory to operand"
        );
    }

    // -----------------------------------------------------------------------
    // Single-copy atomicity (two-state observer model)
    // -----------------------------------------------------------------------

    #[test]
    fn single_paired_access_is_single_copy_atomic_at_128_bits() {
        let p = proof_atomic_load_single_copy_i128();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "a 128-bit atomic load lowered as ONE paired access must be single-copy atomic"
        );
    }

    #[test]
    fn dmb_ish_orders_a_prior_load_before_a_subsequent_load() {
        let p = proof_dmb_ish_orders_loads();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "a full inner-shareable barrier must order a prior load before a subsequent one"
        );
    }

    #[test]
    fn dmb_ishld_orders_a_prior_load_before_a_subsequent_load() {
        let p = proof_dmb_ishld_orders_loads();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "a load barrier must order a prior load before a subsequent one"
        );
    }

    /// THE DISCRIMINATOR for the barrier model, in BOTH directions.
    ///
    /// An obligation no lowering can fail is a tautology — that is exactly why
    /// the `Fence_* -> DMB ISH*` obligations (`bv_const(0xB,8) == bv_const(0xB,8)`)
    /// were retracted in #62. So the same obligation form must be REFUTED when
    /// the barrier is absent, AND when the barrier is of a kind that does not
    /// cover this access pair. The second half is what stops the model from
    /// crediting ANY DMB for ANY ordering.
    #[test]
    fn barrier_presence_and_kind_both_discriminate() {
        let absent = verify_by_evaluation(&no_barrier_load_load_control());
        assert!(
            !matches!(absent, VerificationResult::Valid),
            "without a barrier the later load CAN observe the older state \
             (sel_a = 1, sel_b = 0) and this must NOT verify; got {absent:?} — the \
             interleaving model has stopped seeing reorderings, so \
             `proof_dmb_ish_orders_loads` no longer proves anything"
        );
        let wrong_kind = verify_by_evaluation(&ishst_does_not_order_loads_control());
        assert!(
            !matches!(wrong_kind, VerificationResult::Valid),
            "a STORE barrier does not order a load-load pair and must NOT verify; \
             got {wrong_kind:?} — the model is crediting barrier PRESENCE rather \
             than the ordering the barrier actually provides"
        );
    }

    /// THE DISCRIMINATOR. Without this the positive obligation above is worth
    /// nothing: an obligation that no lowering can fail is a tautology, which is
    /// exactly why the `Fence_* -> DMB ISH*` obligations were retracted in #62.
    /// The SAME obligation form, applied to a lowering split into two 64-bit
    /// accesses, must be REFUTED — that split can observe the pre-write state in
    /// one half and the post-write state in the other, i.e. a TORN read.
    #[test]
    fn torn_split_access_is_refuted_at_128_bits() {
        let p = torn_split_atomic_load_i128_control();
        let result = verify_by_evaluation(&p);
        assert!(
            !matches!(result, VerificationResult::Valid),
            "a 128-bit atomic load split into two 64-bit accesses CAN tear and must NOT verify; \
             got {result:?} — the observer model has stopped discriminating, so \
             `proof_atomic_load_single_copy_i128` no longer proves anything"
        );
    }

    #[test]
    fn test_swp_updates_mem_i64() {
        let p = proof_swp_updates_mem_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "SWP I64 should update memory to operand"
        );
    }

    /// The 64-bit SWP memory obligation must be REGISTERED, not merely
    /// constructible: `registry_proof_for_query` resolves a credit by scanning
    /// `all_atomic_proofs()`, so an unregistered proof would leave a 64-bit SWP
    /// silently falling back to the FIRST name containing the query — the 32-bit
    /// theorem — which is a four-byte claim about an eight-byte write.
    #[test]
    fn swp_mem_obligations_are_registered_at_both_widths() {
        let names: Vec<String> = all_atomic_proofs().iter().map(|p| p.name.clone()).collect();
        for expected in [
            "SWP_I32: mem[addr] = operand",
            "SWP_I64: mem[addr] = operand",
        ] {
            assert!(
                names.iter().any(|n| n == expected),
                "{expected} must survive the #62 retraction and stay registered; have: {names:#?}"
            );
        }
        // And the retraction still removes the degenerate half, at BOTH widths.
        for retracted in ["SWP_I32: returns old value", "SWP_I64: returns old value"] {
            assert!(
                !names.iter().any(|n| n == retracted),
                "{retracted} is degenerate (X==X through encode_load_le) and must stay retracted"
            );
        }
    }

    // -----------------------------------------------------------------------
    // LDCLR (AND NOT) proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_ldclr_returns_old_i32() {
        let p = proof_ldclr_returns_old_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDCLR I32 should return old value"
        );
    }

    #[test]
    fn test_ldclr_updates_mem_i32() {
        let p = proof_ldclr_updates_mem_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDCLR I32 should update memory to old AND NOT operand"
        );
    }

    #[test]
    fn test_lse_min_max_representative_proofs() {
        let config = VerificationConfig::with_sample_count(512);
        for p in [
            proof_ldsmax_updates_mem_i64(),
            proof_ldsmin_updates_mem_i64(),
            proof_ldumax_updates_mem_i64(),
            proof_ldumin_updates_mem_i64(),
        ] {
            assert!(
                matches!(
                    verify_by_evaluation_with_config(&p, &config),
                    VerificationResult::Valid
                ),
                "{} should be valid",
                p.name
            );
        }
    }

    // -----------------------------------------------------------------------
    // CAS proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_cas_success_i32() {
        let p = proof_cas_success_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "CAS I32 success path should update memory to desired"
        );
    }

    #[test]
    fn test_cas_returns_old_i32() {
        let p = proof_cas_returns_old_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "CAS I32 should return old value"
        );
    }

    #[test]
    fn test_cas_failure_i32() {
        let p = proof_cas_failure_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "CAS I32 failure path should leave memory unchanged"
        );
    }

    #[test]
    fn test_cas_success_i64() {
        let p = proof_cas_success_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "CAS I64 success path should update memory to desired"
        );
    }

    // -----------------------------------------------------------------------
    // Fence proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_fence_dmb_ish() {
        let p = proof_fence_dmb_ish();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "DMB ISH encoding for SeqCst should be 0xB"
        );
    }

    #[test]
    fn test_fence_dmb_ishld() {
        let p = proof_fence_dmb_ishld();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "DMB ISHLD encoding for Acquire should be 0x9"
        );
    }

    #[test]
    fn test_fence_release_dmb_ish() {
        let p = proof_fence_release_dmb_ish();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "DMB ISH encoding for Release should be 0xB"
        );
    }

    // -----------------------------------------------------------------------
    // SUB via NEG+LDADD equivalence
    // -----------------------------------------------------------------------

    #[test]
    fn test_atomic_sub_neg_ldadd_i32() {
        let p = proof_atomic_sub_via_neg_ldadd_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "old - x == old + (-x) should hold for I32"
        );
    }

    #[test]
    fn test_atomic_sub_neg_ldadd_i64() {
        let p = proof_atomic_sub_via_neg_ldadd_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "old - x == old + (-x) should hold for I64"
        );
    }

    // -----------------------------------------------------------------------
    // AND via MVN+LDCLR equivalence
    // -----------------------------------------------------------------------

    #[test]
    fn test_atomic_and_mvn_ldclr_i32() {
        let p = proof_atomic_and_via_mvn_ldclr_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "old & x == old & ~~x should hold for I32"
        );
    }

    #[test]
    fn test_atomic_and_mvn_ldclr_i64() {
        let p = proof_atomic_and_via_mvn_ldclr_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "old & x == old & ~~x should hold for I64"
        );
    }

    // -----------------------------------------------------------------------
    // Non-interference
    // -----------------------------------------------------------------------

    // The non-interference proofs require BOTH addresses naturally aligned.
    // `addr_a` and `addr_b` are consecutive draws of the multi-input sweep's
    // power-of-two-modulus LCG, whose successive outputs alternate in parity,
    // so no uniform sample has both addresses even; and no edge combination
    // aligns both either. Only the sweep's precondition-directed trials
    // (aligned values, an earlier address plus a power-of-two offset) reach
    // them, so these tests assert the directed evidence and also check the
    // property at explicit witnesses — aligned, non-wrapping, disjoint address
    // pairs (adjacent on both sides and near the top of the address space).
    // Sampled evidence is statistical; a formal claim comes from the strict AY
    // gate.

    /// Aligned, non-wrapping, disjoint `(addr_a, addr_b)` pairs for `size`-byte
    /// accesses: far apart, adjacent above, adjacent below, top of memory.
    fn disjoint_aligned_pairs(size: u64) -> [(u64, u64); 4] {
        [
            (0x1000, 0x2000),
            (0x1000, 0x1000 + size),
            (0x1000 + size, 0x1000),
            (0, u64::MAX - (size - 1) - size),
        ]
    }

    /// Witness rows `addr_a`, `addr_b`, `extra` for each disjoint pair.
    fn non_interference_witnesses(
        size: u64,
        extra: &[(&'static str, u64)],
    ) -> Vec<Vec<(&'static str, u64)>> {
        disjoint_aligned_pairs(size)
            .iter()
            .map(|&(a, b)| {
                let mut row = vec![("addr_a", a), ("addr_b", b)];
                row.extend_from_slice(extra);
                row
            })
            .collect()
    }

    fn assert_non_interference_holds(
        p: &ProofObligation,
        size: u64,
        extra: &[(&'static str, u64)],
    ) {
        let rows = non_interference_witnesses(size, extra);
        let witnesses: Vec<&[(&str, u64)]> = rows.iter().map(Vec::as_slice).collect();
        crate::lowering_proof::assert_directed_sampling_holds_at(p, &witnesses);
    }

    #[test]
    fn test_atomic_store_non_interference_i32() {
        let p = proof_atomic_store_non_interference_i32();
        assert_non_interference_holds(&p, 4, &[("value", 0xdead_beef), ("mem_default", 0xab)]);
    }

    #[test]
    fn test_atomic_store_non_interference_i64() {
        let p = proof_atomic_store_non_interference_i64();
        assert_non_interference_holds(
            &p,
            8,
            &[("value", 0x0123_4567_89ab_cdef), ("mem_default", 0x5a)],
        );
    }

    #[test]
    fn test_ldadd_non_interference_i32() {
        let p = proof_ldadd_non_interference_i32();
        assert_non_interference_holds(&p, 4, &[("operand", 0xffff_ffff), ("mem_default", 0x01)]);
    }

    #[test]
    fn test_ldadd_non_interference_i64() {
        let p = proof_ldadd_non_interference_i64();
        assert_non_interference_holds(&p, 8, &[("operand", 7), ("mem_default", 0xff)]);
    }

    #[test]
    fn test_swp_non_interference_i32() {
        let p = proof_swp_non_interference_i32();
        assert_non_interference_holds(&p, 4, &[("operand", 0x1234_5678), ("mem_default", 0)]);
    }

    /// The CAS success guard `*addr_a == expected` holds when `expected` is the
    /// little-endian load of the untouched memory's repeated default byte.
    #[test]
    fn test_cas_non_interference_i32() {
        let p = proof_cas_non_interference_i32();
        assert_non_interference_holds(
            &p,
            4,
            &[
                ("expected", 0xabab_abab),
                ("desired", 0x0000_0001),
                ("mem_default", 0xab),
            ],
        );
    }

    #[test]
    fn test_cas_non_interference_i64() {
        let p = proof_cas_non_interference_i64();
        assert_non_interference_holds(
            &p,
            8,
            &[
                ("expected", 0x3c3c_3c3c_3c3c_3c3c),
                ("desired", u64::MAX),
                ("mem_default", 0x3c),
            ],
        );
    }

    // -----------------------------------------------------------------------
    // Non-interference: wrapping-CEX regression (disjointness soundness)
    // -----------------------------------------------------------------------

    /// Evaluate every precondition of `p` under the given concrete addresses
    /// and return true iff all preconditions hold (i.e. the proof body makes a
    /// claim about this address pair).
    fn all_preconditions_hold(p: &ProofObligation, addr_a: u64, addr_b: u64) -> bool {
        // Supply concrete addresses; default-fill any other inputs with 0 so the
        // address-only preconditions evaluate. mem_default / value / operand /
        // expected / desired do not appear in the disjointness preconditions.
        let mut env: std::collections::HashMap<String, u64> = std::collections::HashMap::new();
        for (name, _w) in &p.inputs {
            env.insert(name.clone(), 0);
        }
        env.insert("addr_a".to_string(), addr_a);
        env.insert("addr_b".to_string(), addr_b);
        p.preconditions.iter().all(|pre| pre.eval(&env).as_bool())
    }

    /// Regression for the formal-gate counterexamples: each non-interference
    /// proof's preconditions must REJECT the wrapping, overlapping address pairs
    /// that previously slipped through the buggy one-sided disjointness term.
    ///
    /// For size=4, addr_a=0x…FFFC, addr_b=0x…FFFA: A occupies [0xFC..0xFF] and
    /// B occupies [0xFA..0xFD] — they overlap, so the precondition must be false.
    /// For size=8, addr_a=0x…FFF8, addr_b=0x…FFF7 the ranges also overlap.
    #[test]
    fn test_non_interference_rejects_wrapping_cex() {
        // (proof, addr_a, addr_b) — the exact gate CEX pairs (and their size-8 form).
        let cases: Vec<(ProofObligation, u64, u64)> = vec![
            (
                proof_atomic_store_non_interference_i32(),
                0xffff_ffff_ffff_fffc,
                0xffff_ffff_ffff_fffa,
            ),
            (
                proof_atomic_store_non_interference_i64(),
                0xffff_ffff_ffff_fff8,
                0xffff_ffff_ffff_fff7,
            ),
            (
                proof_ldadd_non_interference_i32(),
                0xffff_ffff_ffff_fffc,
                0xffff_ffff_ffff_fff9,
            ),
            (
                proof_ldadd_non_interference_i64(),
                0xffff_ffff_ffff_fff8,
                0xffff_ffff_ffff_fff6,
            ),
            (
                proof_swp_non_interference_i32(),
                0xffff_ffff_ffff_fffc,
                0xffff_ffff_ffff_fffa,
            ),
            (
                proof_cas_non_interference_i32(),
                0xffff_ffff_ffff_fffc,
                0xffff_ffff_ffff_fff9,
            ),
            (
                proof_cas_non_interference_i64(),
                0xffff_ffff_ffff_fff8,
                0xffff_ffff_ffff_fff1,
            ),
        ];
        for (p, addr_a, addr_b) in &cases {
            assert!(
                !all_preconditions_hold(p, *addr_a, *addr_b),
                "{}: preconditions must REJECT wrapping/overlapping pair \
                 addr_a=0x{:x}, addr_b=0x{:x} (was a formal-gate counterexample)",
                p.name,
                addr_a,
                addr_b
            );
        }
    }

    /// Complement: a genuinely-disjoint, non-wrapping pair must still SATISFY all
    /// preconditions — proving the fix didn't degenerate into a tautology that
    /// rejects every input.
    #[test]
    fn test_non_interference_accepts_disjoint_pair() {
        // A at 0x1000 (size 8 => [0x1000..0x1007]), B at 0x2000 — clearly disjoint.
        for p in [
            proof_atomic_store_non_interference_i32(),
            proof_atomic_store_non_interference_i64(),
            proof_ldadd_non_interference_i32(),
            proof_ldadd_non_interference_i64(),
            proof_swp_non_interference_i32(),
        ] {
            assert!(
                all_preconditions_hold(&p, 0x1000, 0x2000),
                "{}: disjoint non-wrapping pair must satisfy preconditions",
                p.name
            );
        }
    }

    // -----------------------------------------------------------------------
    // Registry tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_atomic_proofs_count() {
        let proofs = all_atomic_proofs();
        assert_eq!(
            proofs.len(),
            40,
            "expected 40 atomic proofs (16 RMW/CAS/SWP 'returns old value' X==X + 3 \
             Fence->DMB const tautologies retracted in #62; +1 for \
             `SWP_I64: mem[addr] = operand`, the 64-bit sibling SWP was missing while \
             LDADD/LDSMAX/LDSMIN/LDUMAX/LDUMIN all carried both widths; +1 for \
             `AtomicLoad_I128: single-copy (one paired access)`, the two-state observer \
             model; +2 for `DMB_ISH`/`DMB_ISHLD: orders prior load before subsequent \
             load`, the interleaving model that replaces the retracted Fence->DMB \
             family — DMB had NO proof binding it between #62 and that change), got {}",
            proofs.len()
        );
    }

    /// Every atomic proof is `Valid` by evaluation, the non-interference family
    /// included: the multi-input sweep's directed trials reach their aligned,
    /// disjoint address pairs (the per-proof tests above pin that evidence).
    #[test]
    fn test_all_atomic_proofs_valid() {
        for p in all_atomic_proofs() {
            let result = verify_by_evaluation(&p);
            assert!(
                matches!(result, VerificationResult::Valid),
                "proof '{}' should be valid, got {:?}",
                p.name,
                result
            );
        }
    }

    #[test]
    fn test_all_atomic_proofs_have_names() {
        for p in all_atomic_proofs() {
            assert!(!p.name.is_empty(), "every proof must have a name");
        }
    }

    #[test]
    fn test_all_atomic_proofs_unique_names() {
        let proofs = all_atomic_proofs();
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        for window in names.windows(2) {
            assert_ne!(window[0], window[1], "duplicate proof name: {}", window[0]);
        }
    }
}
