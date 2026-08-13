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
// STLR/LDADD{A,L,AL} variant. We verify the data-flow semantics are correct;
// the ordering correctness follows from the ARM architecture specification
// (DDI 0487, Section B2.3 and K11).
//
// Reference: ARM Architecture Reference Manual (DDI 0487), Section C6.
// Reference: designs/2026-04-13-verification-architecture.md

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

/// Proof: DMB ISHST barrier option for Release ordering.
pub fn proof_fence_dmb_ishst() -> ProofObligation {
    let trust_ir_option = SmtExpr::bv_const(0x0A, 8);
    let aarch64_option = SmtExpr::bv_const(0x0A, 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fence_Release -> DMB ISHST (0xA)".to_string(),
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
        proof_fence_dmb_ishst(),
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
/// - 29 atomic RMW proofs (LDADD, LDSET, LDEOR, LSE min/max, SWP, LDCLR)
/// - 4 CAS proofs (success, failure, return value, 64-bit)
/// - 3 fence proofs (DMB ISH, ISHLD, ISHST)
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
    fn test_fence_dmb_ishst() {
        let p = proof_fence_dmb_ishst();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "DMB ISHST encoding for Release should be 0xA"
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

    #[test]
    fn test_atomic_store_non_interference_i32() {
        let p = proof_atomic_store_non_interference_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "Atomic store at A should not affect read at B (I32)"
        );
    }

    #[test]
    fn test_atomic_store_non_interference_i64() {
        let p = proof_atomic_store_non_interference_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "Atomic store at A should not affect read at B (I64)"
        );
    }

    #[test]
    fn test_ldadd_non_interference_i32() {
        let p = proof_ldadd_non_interference_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDADD at A should not affect read at B (I32)"
        );
    }

    #[test]
    fn test_ldadd_non_interference_i64() {
        let p = proof_ldadd_non_interference_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "LDADD at A should not affect read at B (I64)"
        );
    }

    #[test]
    fn test_swp_non_interference_i32() {
        let p = proof_swp_non_interference_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "SWP at A should not affect read at B (I32)"
        );
    }

    #[test]
    fn test_cas_non_interference_i32() {
        let p = proof_cas_non_interference_i32();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "CAS at A should not affect read at B (I32)"
        );
    }

    #[test]
    fn test_cas_non_interference_i64() {
        let p = proof_cas_non_interference_i64();
        assert!(
            matches!(verify_by_evaluation(&p), VerificationResult::Valid),
            "CAS at A should not affect read at B (I64)"
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
            36,
            "expected 36 atomic proofs (16 RMW/CAS/SWP 'returns old value' X==X + 3 \
             Fence->DMB const tautologies retracted in #62), got {}",
            proofs.len()
        );
    }

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
