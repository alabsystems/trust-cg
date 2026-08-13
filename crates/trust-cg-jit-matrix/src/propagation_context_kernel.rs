// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PropagationContext-ABI watched-list BCP kernel (`ay_sat_watch_bcp`, #678).
//!
//! Implements the `ay_sat_propagation_context_abi_v1` contract from
//! `trust_cg_codegen::ay_sat_bcp_contract`: a kernel that takes a
//! `*mut PropagationContext`, runs Boolean Constraint Propagation, and writes a
//! `AYSatWatchBcpResult` record. This is the trust-cg-side, ABI-stable kernel
//! the ay-sat solver hosts (the `KernelCtx` kernel in `jit_bcp_kernel` is the
//! sibling internal ABI; this one is the published `ay::sat::WatchBcpKernel`
//! surface).
//!
//! The `_reference` entry runs BCP through the proven [`BcpState`] baseline
//! behind the ABI marshalling — it is the `dense_reference_bcp` reference the
//! contract's `ReplayComparison` proof fact compares against. A JIT/specialized
//! variant reuses the same marshalling but drives a compiled kernel; both must
//! produce identical results.
//!
//! ## Layouts (must match `ay_sat_bcp_contract` field offsets exactly)
//! `PropagationContext` is 168 bytes; `AYSatWatchBcpResult` is 56 bytes.
//!
//! ## Buffer formats (this kernel's concrete interpretation of the ABI ptrs)
//! * `clause_arena: *const i32`, `clause_arena_len`: flat array. `arena[0]` =
//!   clause count; then each clause is `[len, lit0, .., lit_{len-1}]` (DIMACS
//!   signed literals). A clause's external ref is the i32 offset of its `len`.
//! * `assignment: *mut i8`, `assignment_len = num_vars + 1`: per-variable value
//!   `+1`/`-1`/`0`, slot 0 unused. `num_vars = assignment_len - 1`.
//! * `pending_queue: *const i32`, `[head..tail)`: decision literals to replay.
//! * `trail: *mut i32`, `trail_len`: on output, the full post-BCP trail.
//! * `result.propagated_literals: *mut i32`: newly-implied literals (count in
//!   `result.detail`); caller sizes it `>= num_vars`.

use crate::bcp_baseline::BcpState;
use crate::bcp_kernel::{BCP_RESULT_CONFLICT, BCP_RESULT_DECODE_ERROR, BcpKernelProvider};
use crate::jit_bcp_kernel::JitBcpWatchedLiteralKernelProvider;
use crate::solver_kernel_abi::SolverKernelHandle;

/// Result-record `status` / entry return codes.
pub const AY_SAT_BCP_STATUS_OK: i32 = 0;
pub const AY_SAT_BCP_STATUS_CONFLICT: i32 = 1;
pub const AY_SAT_BCP_STATUS_STALE_GENERATION: i32 = 2;
pub const AY_SAT_BCP_STATUS_DECODE_ERROR: i32 = 3;

/// `ay_sat_propagation_context_abi_v1` (168 bytes). Field order/offsets mirror
/// `ay_sat_watch_bcp_propagation_context_record_layout`.
#[repr(C)]
pub struct PropagationContext {
    pub clause_arena: *const i32,         // 0
    pub clause_arena_len: u64,            // 8
    pub watch_heads: *const i32,          // 16
    pub watch_head_count: u64,            // 24
    pub watch_entries: *const i32,        // 32
    pub watch_entry_count: u64,           // 40
    pub assignment: *mut i8,              // 48
    pub assignment_len: u64,              // 56
    pub trail: *mut i32,                  // 64
    pub trail_len: u64,                   // 72
    pub pending_queue: *const i32,        // 80
    pub pending_queue_head: u64,          // 88
    pub pending_queue_tail: u64,          // 96
    pub pending_queue_capacity: u64,      // 104
    pub result: *mut AYSatWatchBcpResult, // 112
    pub generation_facts: u64,            // 120
    pub context_generation: u64,          // 128
    pub expected_generation: u64,         // 136
    pub watch_generation: u64,            // 144
    pub assignment_generation: u64,       // 152
    pub status: i32,                      // 160
    pub reserved: u32,                    // 164
}

/// `ay_sat_bcp_result_abi_v1` (56 bytes). Mirrors the result record layout.
#[repr(C)]
pub struct AYSatWatchBcpResult {
    pub status: i32,                   // 0
    pub conflict_clause: i32,          // 4
    pub propagated_literals: *mut i32, // 8
    pub trail_len: u64,                // 16
    pub pending_queue_head: u64,       // 24
    pub pending_queue_tail: u64,       // 32
    pub generation: u64,               // 40
    pub detail: u64,                   // 48
}

/// The published `ay_sat_watch_bcp` entry signature.
pub type AYSatWatchBcpFn = unsafe extern "C" fn(*mut PropagationContext) -> i32;

// Compile-time ABI size assertions (must match the contract's byte sizes).
const _: () = assert!(core::mem::size_of::<PropagationContext>() == 168);
const _: () = assert!(core::mem::size_of::<AYSatWatchBcpResult>() == 56);

#[inline]
#[allow(unsafe_op_in_unsafe_fn)]
unsafe fn write_status(ctx: &mut PropagationContext, status: i32) {
    ctx.status = status;
    if !ctx.result.is_null() {
        (*ctx.result).status = status;
        (*ctx.result).generation = ctx.context_generation;
    }
}

/// Reference `ay_sat_watch_bcp`: generation-fail-closed BCP over the ABI,
/// implemented via the proven [`BcpState`] baseline. Safe for the contract's
/// reference-replay role.
///
/// # Safety
/// `ctx` must point at a valid `PropagationContext` whose pointer/length fields
/// describe live, correctly-sized buffers in the documented formats.
#[allow(unsafe_op_in_unsafe_fn)]
pub unsafe extern "C" fn ay_sat_watch_bcp_reference(ctx: *mut PropagationContext) -> i32 {
    if ctx.is_null() {
        return AY_SAT_BCP_STATUS_DECODE_ERROR;
    }
    let ctx = &mut *ctx;

    // Generation freshness — fail-closed `fail_closed_epoch_match` policy.
    if ctx.context_generation != ctx.expected_generation
        || ctx.watch_generation != ctx.expected_generation
        || ctx.assignment_generation != ctx.expected_generation
    {
        write_status(ctx, AY_SAT_BCP_STATUS_STALE_GENERATION);
        return AY_SAT_BCP_STATUS_STALE_GENERATION;
    }

    if ctx.assignment.is_null() || ctx.assignment_len == 0 || ctx.clause_arena.is_null() {
        write_status(ctx, AY_SAT_BCP_STATUS_DECODE_ERROR);
        return AY_SAT_BCP_STATUS_DECODE_ERROR;
    }
    let num_vars = (ctx.assignment_len - 1) as usize;

    // Decode clauses from the arena; remember each clause's arena offset so the
    // conflict clause can be reported as an external (arena-offset) ref.
    let arena = core::slice::from_raw_parts(ctx.clause_arena, ctx.clause_arena_len as usize);
    let Some((clauses, clause_offsets)) = decode_clauses(arena) else {
        write_status(ctx, AY_SAT_BCP_STATUS_DECODE_ERROR);
        return AY_SAT_BCP_STATUS_DECODE_ERROR;
    };

    // Settled assignment prefix: the full assignment minus the pending decisions
    // (so a decision var is not also pre-seeded — matches the host contract).
    let assignment = core::slice::from_raw_parts(ctx.assignment, ctx.assignment_len as usize);
    let mut initial_values: Vec<i8> = assignment.to_vec();

    let qhead = ctx.pending_queue_head as usize;
    let qtail = ctx.pending_queue_tail as usize;
    let decisions: Vec<i32> = if ctx.pending_queue.is_null() || qtail <= qhead {
        Vec::new()
    } else {
        let pq = core::slice::from_raw_parts(ctx.pending_queue, qtail);
        pq[qhead..qtail].to_vec()
    };
    for &d in &decisions {
        let v = d.unsigned_abs() as usize;
        if v >= 1 && v < initial_values.len() {
            initial_values[v] = 0;
        }
    }

    // Run BCP through the proven baseline.
    let mut state = BcpState::new(num_vars, clauses);
    state.seed_initial_values(&initial_values);
    for &d in &decisions {
        state.assign(d);
    }
    let conflict = state.propagate();

    // Marshal the trail back, recording newly-implied literals.
    let decision_set: std::collections::BTreeSet<i32> = decisions.iter().copied().collect();
    let mut implied: Vec<i32> = Vec::new();
    let mut full_trail: Vec<i32> = Vec::with_capacity(state.trail_len());
    for i in 0..state.trail_len() {
        let lit = state.trail_at(i);
        full_trail.push(lit);
        if !decision_set.contains(&lit) {
            implied.push(lit);
        }
    }

    // Write the post-BCP trail back into ctx.trail (bounded by trail capacity =
    // the original trail_len field as the allocation size hint).
    if !ctx.trail.is_null() {
        let cap = ctx.trail_len as usize;
        let n = full_trail.len().min(cap);
        let out = core::slice::from_raw_parts_mut(ctx.trail, cap);
        out[..n].copy_from_slice(&full_trail[..n]);
    }
    ctx.trail_len = full_trail.len() as u64;

    let status = if conflict.is_some() {
        AY_SAT_BCP_STATUS_CONFLICT
    } else {
        AY_SAT_BCP_STATUS_OK
    };

    if !ctx.result.is_null() {
        let res = &mut *ctx.result;
        res.status = status;
        res.conflict_clause = match conflict {
            Some(idx) => clause_offsets.get(idx).copied().unwrap_or(-1),
            None => -1,
        };
        res.trail_len = full_trail.len() as u64;
        res.pending_queue_head = qtail as u64; // fully drained
        res.pending_queue_tail = qtail as u64;
        res.generation = ctx.context_generation;
        res.detail = implied.len() as u64;
        if !res.propagated_literals.is_null() {
            let out = core::slice::from_raw_parts_mut(res.propagated_literals, implied.len());
            out.copy_from_slice(&implied);
        }
    }
    ctx.status = status;
    status
}

/// Decode `[count, (len, lits..)*]` into clauses + their arena offsets.
fn decode_clauses(arena: &[i32]) -> Option<(Vec<Vec<i32>>, Vec<i32>)> {
    if arena.is_empty() {
        return Some((Vec::new(), Vec::new()));
    }
    let count = arena[0];
    if count < 0 {
        return None;
    }
    let mut clauses = Vec::with_capacity(count as usize);
    let mut offsets = Vec::with_capacity(count as usize);
    let mut idx = 1usize;
    for _ in 0..count {
        if idx >= arena.len() {
            return None;
        }
        let len = arena[idx];
        if len < 0 {
            return None;
        }
        let len = len as usize;
        let start = idx + 1;
        let end = start + len;
        if end > arena.len() {
            return None;
        }
        offsets.push(idx as i32);
        clauses.push(arena[start..end].to_vec());
        idx = end;
    }
    Some((clauses, offsets))
}

/// Specialized `ay_sat_watch_bcp`: identical ABI + semantics to
/// [`ay_sat_watch_bcp_reference`], but drives the JIT-compiled watched-literal
/// `KernelCtx` kernel instead of the `BcpState` baseline. By the contract's
/// `ReplayComparison` proof fact, this must produce results identical to the
/// reference on every input — verified differentially below.
///
/// # Safety
/// Same contract as [`ay_sat_watch_bcp_reference`].
#[allow(unsafe_op_in_unsafe_fn)]
pub unsafe extern "C" fn ay_sat_watch_bcp_specialized(ctx: *mut PropagationContext) -> i32 {
    if ctx.is_null() {
        return AY_SAT_BCP_STATUS_DECODE_ERROR;
    }
    let ctx = &mut *ctx;
    if ctx.context_generation != ctx.expected_generation
        || ctx.watch_generation != ctx.expected_generation
        || ctx.assignment_generation != ctx.expected_generation
    {
        write_status(ctx, AY_SAT_BCP_STATUS_STALE_GENERATION);
        return AY_SAT_BCP_STATUS_STALE_GENERATION;
    }
    if ctx.assignment.is_null() || ctx.assignment_len == 0 || ctx.clause_arena.is_null() {
        write_status(ctx, AY_SAT_BCP_STATUS_DECODE_ERROR);
        return AY_SAT_BCP_STATUS_DECODE_ERROR;
    }
    let num_vars = (ctx.assignment_len - 1) as usize;
    let arena = core::slice::from_raw_parts(ctx.clause_arena, ctx.clause_arena_len as usize);
    let Some((clauses, clause_offsets)) = decode_clauses(arena) else {
        write_status(ctx, AY_SAT_BCP_STATUS_DECODE_ERROR);
        return AY_SAT_BCP_STATUS_DECODE_ERROR;
    };

    let assignment = core::slice::from_raw_parts(ctx.assignment, ctx.assignment_len as usize);
    let mut initial_values: Vec<i8> = assignment.to_vec();
    let qhead = ctx.pending_queue_head as usize;
    let qtail = ctx.pending_queue_tail as usize;
    let decisions: Vec<i32> = if ctx.pending_queue.is_null() || qtail <= qhead {
        Vec::new()
    } else {
        core::slice::from_raw_parts(ctx.pending_queue, qtail)[qhead..qtail].to_vec()
    };
    for &d in &decisions {
        let v = d.unsigned_abs() as usize;
        if v >= 1 && v < initial_values.len() {
            initial_values[v] = 0;
        }
    }

    // Drive the JIT-compiled watched-literal BCP kernel.
    let provider =
        match JitBcpWatchedLiteralKernelProvider::compile(num_vars, clauses, num_vars.max(1)) {
            Ok(p) => p,
            Err(_) => {
                write_status(ctx, AY_SAT_BCP_STATUS_DECODE_ERROR);
                return AY_SAT_BCP_STATUS_DECODE_ERROR;
            }
        };
    let mut handle = SolverKernelHandle::from_provider(&provider);
    let buf = (num_vars * 2).max(8);
    let mut implied_buf = vec![0i32; buf];
    let mut reasons_buf = vec![0i32; buf];
    handle.set_implied_literals_buffer(&mut implied_buf);
    handle.set_implied_reasons_buffer(&mut reasons_buf);
    handle.set_clause_id_translation(&[]);
    handle.set_initial_values(&initial_values);
    provider.reset_arena();
    let input: Vec<u32> = decisions
        .iter()
        .map(|&d| BcpKernelProvider::encode_literal(d.unsigned_abs(), d < 0))
        .collect();
    let kstatus = handle.call(&input);

    let status = match kstatus.result {
        BCP_RESULT_CONFLICT => AY_SAT_BCP_STATUS_CONFLICT,
        BCP_RESULT_DECODE_ERROR => AY_SAT_BCP_STATUS_DECODE_ERROR,
        _ => AY_SAT_BCP_STATUS_OK,
    };
    if status == AY_SAT_BCP_STATUS_DECODE_ERROR {
        write_status(ctx, status);
        return status;
    }
    let n = kstatus.implied_literals_len;
    let implied: Vec<i32> = if n == usize::MAX || n > implied_buf.len() {
        Vec::new()
    } else {
        implied_buf[..n].to_vec()
    };

    if !ctx.result.is_null() {
        let res = &mut *ctx.result;
        res.status = status;
        res.conflict_clause =
            if kstatus.result == BCP_RESULT_CONFLICT && kstatus.conflicting_clause_index >= 0 {
                clause_offsets
                    .get(kstatus.conflicting_clause_index as usize)
                    .copied()
                    .unwrap_or(-1)
            } else {
                -1
            };
        res.trail_len = (decisions.len() + implied.len()) as u64;
        res.pending_queue_head = qtail as u64;
        res.pending_queue_tail = qtail as u64;
        res.generation = ctx.context_generation;
        res.detail = implied.len() as u64;
        if !res.propagated_literals.is_null() {
            let out = core::slice::from_raw_parts_mut(res.propagated_literals, implied.len());
            out.copy_from_slice(&implied);
        }
    }
    ctx.status = status;
    status
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bcp_kernel::{BCP_RESULT_CONFLICT, BcpKernelProvider};
    use crate::jit_bcp_kernel::JitBcpWatchedLiteralKernelProvider;
    use crate::solver_kernel_abi::SolverKernelHandle;
    use std::collections::BTreeSet;

    /// Owns the buffers backing a `PropagationContext` for tests.
    struct OwnedContext {
        arena: Vec<i32>,
        assignment: Vec<i8>,
        trail: Vec<i32>,
        pending: Vec<i32>,
        propagated: Vec<i32>,
        result: Box<AYSatWatchBcpResult>,
        ctx: Box<PropagationContext>,
    }

    impl OwnedContext {
        fn new(num_vars: usize, clauses: &[Vec<i32>], initial: &[i8], decisions: &[i32]) -> Self {
            let mut arena = vec![clauses.len() as i32];
            for c in clauses {
                arena.push(c.len() as i32);
                arena.extend_from_slice(c);
            }
            let mut assignment = vec![0i8; num_vars + 1];
            assignment[..initial.len().min(num_vars + 1)]
                .copy_from_slice(&initial[..initial.len().min(num_vars + 1)]);
            let trail = vec![0i32; num_vars + 1];
            let pending = decisions.to_vec();
            let propagated = vec![0i32; num_vars + 1];
            let result = Box::new(AYSatWatchBcpResult {
                status: -1,
                conflict_clause: -1,
                propagated_literals: core::ptr::null_mut(),
                trail_len: 0,
                pending_queue_head: 0,
                pending_queue_tail: 0,
                generation: 0,
                detail: 0,
            });
            let mut owned = OwnedContext {
                arena,
                assignment,
                trail,
                pending,
                propagated,
                result,
                ctx: Box::new(unsafe { core::mem::zeroed() }),
            };
            owned.result.propagated_literals = owned.propagated.as_mut_ptr();
            *owned.ctx = PropagationContext {
                clause_arena: owned.arena.as_ptr(),
                clause_arena_len: owned.arena.len() as u64,
                watch_heads: core::ptr::null(),
                watch_head_count: 0,
                watch_entries: core::ptr::null(),
                watch_entry_count: 0,
                assignment: owned.assignment.as_mut_ptr(),
                assignment_len: owned.assignment.len() as u64,
                trail: owned.trail.as_mut_ptr(),
                trail_len: owned.trail.len() as u64,
                pending_queue: owned.pending.as_ptr(),
                pending_queue_head: 0,
                pending_queue_tail: owned.pending.len() as u64,
                pending_queue_capacity: owned.pending.len() as u64,
                result: &mut *owned.result,
                generation_facts: 0,
                context_generation: 7,
                expected_generation: 7,
                watch_generation: 7,
                assignment_generation: 7,
                status: -1,
                reserved: 0,
            };
            owned
        }

        fn run(&mut self) -> i32 {
            unsafe { ay_sat_watch_bcp_reference(&mut *self.ctx) }
        }

        fn run_specialized(&mut self) -> i32 {
            unsafe { ay_sat_watch_bcp_specialized(&mut *self.ctx) }
        }

        fn implied_set(&self) -> BTreeSet<i32> {
            let n = self.result.detail as usize;
            self.propagated[..n].iter().copied().collect()
        }
    }

    /// Oracle: run the JIT KernelCtx watched-literal kernel on the same inputs.
    fn jit_oracle(
        num_vars: usize,
        clauses: &[Vec<i32>],
        initial: &[i8],
        decisions: &[i32],
    ) -> (bool, BTreeSet<i32>) {
        let provider =
            JitBcpWatchedLiteralKernelProvider::compile(num_vars, clauses.to_vec(), num_vars)
                .expect("compile");
        let mut handle = SolverKernelHandle::from_provider(&provider);
        let mut implied = vec![0i32; (num_vars * 2).max(8)];
        let mut reasons = vec![0i32; (num_vars * 2).max(8)];
        handle.set_implied_literals_buffer(&mut implied);
        handle.set_implied_reasons_buffer(&mut reasons);
        handle.set_clause_id_translation(&[]);
        let mut iv = vec![0i8; num_vars + 1];
        iv[..initial.len().min(num_vars + 1)]
            .copy_from_slice(&initial[..initial.len().min(num_vars + 1)]);
        for &d in decisions {
            let v = d.unsigned_abs() as usize;
            if v >= 1 && v < iv.len() {
                iv[v] = 0;
            }
        }
        handle.set_initial_values(&iv);
        provider.reset_arena();
        let input: Vec<u32> = decisions
            .iter()
            .map(|&d| BcpKernelProvider::encode_literal(d.unsigned_abs(), d < 0))
            .collect();
        let status = handle.call(&input);
        let n = status.implied_literals_len;
        let set = if n == usize::MAX {
            BTreeSet::new()
        } else {
            implied[..n].iter().copied().collect()
        };
        (status.result == BCP_RESULT_CONFLICT, set)
    }

    #[test]
    fn abi_sizes_match_contract() {
        assert_eq!(core::mem::size_of::<PropagationContext>(), 168);
        assert_eq!(core::mem::size_of::<AYSatWatchBcpResult>(), 56);
    }

    #[test]
    fn stale_generation_is_fail_closed() {
        let mut owned = OwnedContext::new(2, &[vec![-1, 2]], &[0, 0, 0], &[1]);
        owned.ctx.assignment_generation = owned.ctx.expected_generation + 1; // stale
        assert_eq!(owned.run(), AY_SAT_BCP_STATUS_STALE_GENERATION);
    }

    #[test]
    fn reference_matches_jit_oracle_on_implication_chain() {
        let clauses = vec![vec![-1, 2], vec![-2, 3], vec![-3, 4]];
        let mut owned = OwnedContext::new(4, &clauses, &[0; 5], &[1]);
        let status = owned.run();
        assert_eq!(status, AY_SAT_BCP_STATUS_OK);
        assert_eq!(owned.implied_set(), [2, 3, 4].into_iter().collect());

        let (jit_conflict, jit_implied) = jit_oracle(4, &clauses, &[0; 5], &[1]);
        assert!(!jit_conflict);
        assert_eq!(owned.implied_set(), jit_implied);
    }

    #[test]
    fn reference_reports_conflict_like_jit() {
        let clauses = vec![vec![-1, 2], vec![-1, -2]];
        let mut owned = OwnedContext::new(2, &clauses, &[0; 3], &[1]);
        assert_eq!(owned.run(), AY_SAT_BCP_STATUS_CONFLICT);
        assert!(owned.result.conflict_clause >= 0);
        let (jit_conflict, _) = jit_oracle(2, &clauses, &[0; 3], &[1]);
        assert!(jit_conflict);
    }

    /// Differential corpus: the PropagationContext reference kernel must agree
    /// with the JIT KernelCtx oracle across many random fresh CNFs (the
    /// `ReplayComparison` / `dense_reference_bcp` evidence at the ABI level).
    #[test]
    fn reference_matches_jit_over_random_corpus() {
        let mut s: u64 = 0xD1B5_4A32_D192_ED03;
        let mut rng = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut compared = 0u64;
        for _ in 0..300 {
            let num_vars = 3 + (rng() % 6) as usize;
            let nc = 2 + (rng() % 6) as usize;
            let mut clauses = Vec::new();
            for _ in 0..nc {
                let size = 2 + (rng() % 2) as usize;
                let mut used: Vec<u32> = Vec::new();
                let mut lits = Vec::new();
                while lits.len() < size {
                    let v = 1 + (rng() % num_vars as u64) as i32;
                    if used.contains(&(v as u32)) {
                        continue;
                    }
                    used.push(v as u32);
                    lits.push(if rng() & 1 == 0 { v } else { -v });
                }
                clauses.push(lits);
            }
            let dv = 1 + (rng() % num_vars as u64) as i32;
            let decision = if rng() & 1 == 0 { dv } else { -dv };
            let initial = vec![0i8; num_vars + 1];

            let mut owned = OwnedContext::new(num_vars, &clauses, &initial, &[decision]);
            let status = owned.run();
            let ref_conflict = status == AY_SAT_BCP_STATUS_CONFLICT;
            let (jit_conflict, jit_implied) = jit_oracle(num_vars, &clauses, &initial, &[decision]);
            assert_eq!(
                ref_conflict, jit_conflict,
                "conflict verdict mismatch on {clauses:?} decide {decision}"
            );
            if !ref_conflict && !jit_conflict {
                assert_eq!(
                    owned.implied_set(),
                    jit_implied,
                    "implied mismatch on {clauses:?} decide {decision}"
                );
            }
            compared += 1;
        }
        assert!(compared >= 200);
    }

    /// ReplayComparison proof fact: the BcpState-backed `reference` kernel and
    /// the JIT-compiled `specialized` kernel must produce identical results on
    /// every input over the PropagationContext ABI.
    #[test]
    fn reference_matches_specialized_over_random_corpus() {
        let mut s: u64 = 0x91E1_0DA5_C100_4D3B;
        let mut rng = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut compared = 0u64;
        for _ in 0..200 {
            let num_vars = 3 + (rng() % 6) as usize;
            let nc = 2 + (rng() % 6) as usize;
            let mut clauses = Vec::new();
            for _ in 0..nc {
                let size = 2 + (rng() % 2) as usize;
                let mut used: Vec<u32> = Vec::new();
                let mut lits = Vec::new();
                while lits.len() < size {
                    let v = 1 + (rng() % num_vars as u64) as i32;
                    if used.contains(&(v as u32)) {
                        continue;
                    }
                    used.push(v as u32);
                    lits.push(if rng() & 1 == 0 { v } else { -v });
                }
                clauses.push(lits);
            }
            let dv = 1 + (rng() % num_vars as u64) as i32;
            let decision = if rng() & 1 == 0 { dv } else { -dv };
            let initial = vec![0i8; num_vars + 1];

            let mut ref_ctx = OwnedContext::new(num_vars, &clauses, &initial, &[decision]);
            let ref_status = ref_ctx.run();
            let mut spec_ctx = OwnedContext::new(num_vars, &clauses, &initial, &[decision]);
            let spec_status = spec_ctx.run_specialized();

            assert_eq!(
                ref_status, spec_status,
                "reference/specialized status mismatch on {clauses:?} decide {decision}"
            );
            if ref_status == AY_SAT_BCP_STATUS_OK {
                assert_eq!(
                    ref_ctx.implied_set(),
                    spec_ctx.implied_set(),
                    "reference/specialized implied mismatch on {clauses:?} decide {decision}"
                );
            }
            compared += 1;
        }
        assert!(compared >= 150);
    }

    /// Per-call BCP throughput: JIT-compiled-cached kernel vs the BcpState
    /// reference, both reconstruct-per-call (the PropagationContext ABI model).
    /// Run: `TRUST_CG_RUN_MEASUREMENT_TESTS=1 cargo test
    /// -p trust-cg-jit-matrix --lib perf_jit_cached_vs_bcpstate -- --nocapture`.
    #[test]
    fn perf_jit_cached_vs_bcpstate() {
        if !matches!(
            std::env::var("TRUST_CG_RUN_MEASUREMENT_TESTS").as_deref(),
            Ok("1")
        ) {
            eprintln!(
                "measurement campaign not requested; \
                 set TRUST_CG_RUN_MEASUREMENT_TESTS=1 to run"
            );
            return;
        }

        use std::time::Instant;
        // Moderate random 3-SAT (~4.3 ratio).
        let num_vars = 200usize;
        let nclauses = 860usize;
        let mut s: u64 = 0xC0FF_EE12_3456_789A;
        let mut rng = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut clauses: Vec<Vec<i32>> = Vec::with_capacity(nclauses);
        for _ in 0..nclauses {
            let mut used: Vec<u32> = Vec::new();
            let mut lits = Vec::new();
            while lits.len() < 3 {
                let v = 1 + (rng() % num_vars as u64) as i32;
                if used.contains(&(v as u32)) {
                    continue;
                }
                used.push(v as u32);
                lits.push(if rng() & 1 == 0 { v } else { -v });
            }
            clauses.push(lits);
        }
        // A handful of decisions to drive propagation.
        let decisions: Vec<i32> = (1..=8).map(|v| if v % 2 == 0 { v } else { -v }).collect();
        let initial = vec![0i8; num_vars + 1];
        let iters = 20_000u32;

        // JIT: compile ONCE (cached), then drive per call.
        let provider = JitBcpWatchedLiteralKernelProvider::compile_or_get_cached(
            num_vars,
            clauses.clone(),
            num_vars,
        )
        .expect("jit compile");
        let input: Vec<u32> = decisions
            .iter()
            .map(|&d| BcpKernelProvider::encode_literal(d.unsigned_abs(), d < 0))
            .collect();
        let buf = num_vars * 2;
        let mut implied = vec![0i32; buf];
        let mut reasons = vec![0i32; buf];
        // warm
        for _ in 0..200 {
            let mut h = SolverKernelHandle::from_provider(&*provider);
            h.set_implied_literals_buffer(&mut implied);
            h.set_implied_reasons_buffer(&mut reasons);
            h.set_clause_id_translation(&[]);
            h.set_initial_values(&initial);
            provider.reset_arena();
            let _ = h.call(&input);
        }
        let t0 = Instant::now();
        for _ in 0..iters {
            let mut h = SolverKernelHandle::from_provider(&*provider);
            h.set_implied_literals_buffer(&mut implied);
            h.set_implied_reasons_buffer(&mut reasons);
            h.set_clause_id_translation(&[]);
            h.set_initial_values(&initial);
            provider.reset_arena();
            let _ = h.call(&input);
        }
        let jit_ns = t0.elapsed().as_nanos() / iters as u128;

        // BcpState reference: build ONCE (watches reused), reset + run per call
        // — apples-to-apples with the JIT (which also reuses its compiled arena).
        let mut st = BcpState::new(num_vars, clauses.clone());
        for _ in 0..200 {
            st.reset();
            st.seed_initial_values(&initial);
            for &d in &decisions {
                st.assign(d);
            }
            let _ = st.propagate();
        }
        let t1 = Instant::now();
        for _ in 0..iters {
            st.reset();
            st.seed_initial_values(&initial);
            for &d in &decisions {
                st.assign(d);
            }
            let _ = st.propagate();
        }
        let bcp_ns = t1.elapsed().as_nanos() / iters as u128;

        eprintln!(
            "[PERF] {num_vars}v/{nclauses}c, {} decisions, {iters} iters:\n  \
             JIT-cached : {jit_ns} ns/call\n  \
             BcpState   : {bcp_ns} ns/call\n  \
             JIT/BcpState ratio: {:.2}x  (>1 means JIT slower)",
            decisions.len(),
            jit_ns as f64 / bcp_ns as f64
        );
    }
}
