// trust-cg-jit-matrix/src/bcp_kernel.rs - BcpState <-> SolverKernel ABI bridge.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use crate::bcp_baseline::BcpState;
use crate::solver_kernel_abi::{
    KERNEL_COUNTER_SHIFT, KernelCtx, KernelEntry, NO_CONFLICTING_CLAUSE, SolverKernelProvider,
};

/// Versioned tag for the literal-encoding contract used by `bcp_native_entry`.
///
/// Each `u32` element in the `input` slice passed to the kernel is one
/// literal-to-assign encoded as `(var << 1) | polarity`:
///
/// - `var` occupies the high 31 bits and is 1-indexed (matching DIMACS).
/// - `polarity` occupies bit 0: `0` selects the positive literal `+var`,
///   `1` selects the negative literal `-var`.
///
/// A `var` field of `0` is reserved (DIMACS uses `0` as the end-of-clause
/// sentinel) and the kernel reports it via the `2 = decode error` result code.
pub const BCP_INPUT_FORMAT_VERSION: u32 = 1;

pub const BCP_RESULT_OK: u32 = 0;
pub const BCP_RESULT_CONFLICT: u32 = 1;
pub const BCP_RESULT_DECODE_ERROR: u32 = 2;

fn pack_status(result: u32, counter: u32) -> u64 {
    (result as u64) | ((counter as u64) << KERNEL_COUNTER_SHIFT)
}

fn decode_literal(encoded: u32) -> Option<i32> {
    let var = encoded >> 1;
    if var == 0 {
        return None;
    }
    if var > i32::MAX as u32 {
        return None;
    }
    let polarity = encoded & 1;
    let signed = var as i32;
    Some(if polarity == 0 { signed } else { -signed })
}

/// Append `lit` (and optionally its reason clause id) to the
/// caller-supplied `implied_literals_out` / `implied_reasons_out`
/// buffers in `ctx`, respecting the overflow contract documented on
/// `KernelCtx`.
///
/// `reason_ci` is the JIT clause index that forced `lit`. The kernel
/// looks it up in `ctx.clause_id_translation` (if non-null) before
/// writing to the reasons buffer; otherwise it writes the raw index
/// (passthrough mode). When `ctx.implied_reasons_out` is null, the
/// reason write is skipped entirely (graceful degradation).
///
/// # Safety
///
/// `ctx` must point to a live, exclusively borrowed `KernelCtx`. When
/// `ctx.implied_literals_len < ctx.implied_literals_cap`, the write
/// targets `ctx.implied_literals_out.add(ctx.implied_literals_len)`,
/// which the ABI contract requires the caller to have provisioned as
/// part of the supplied buffer. The same index is used for the
/// reasons buffer when present; the caller must size it at least as
/// large as the literals buffer.
unsafe fn record_implied_literal(ctx: &mut KernelCtx, lit: i32, reason_ci: usize) {
    if ctx.implied_literals_len == usize::MAX {
        // Sticky overflow: do nothing.
        return;
    }
    if ctx.implied_literals_len >= ctx.implied_literals_cap {
        ctx.implied_literals_len = usize::MAX;
        return;
    }
    let idx = ctx.implied_literals_len;
    // SAFETY: `implied_literals_len < implied_literals_cap` and the caller
    // promises `implied_literals_out` has room for `implied_literals_cap`
    // `i32` writes starting at the base pointer.
    unsafe {
        ctx.implied_literals_out.add(idx).write(lit);
    }
    // Emit the reason clause id when the host installed a reasons
    // buffer. `reason_ci == usize::MAX` (i.e. "decision literal, no
    // reason") would only reach this helper from a non-propagation
    // assignment path; native BCP's `drain_implied_trail` filters
    // those out before calling here, so we don't need a special-case
    // sentinel write here.
    if !ctx.implied_reasons_out.is_null() {
        let id_i32: i32 = if ctx.clause_id_translation.is_null() {
            // Passthrough: emit the JIT clause index directly. Cast is
            // lossy only if `reason_ci` exceeds `i32::MAX`, which the
            // ABI documents as unsupported (clause indices are bounded
            // by `num_clauses <= i32::MAX` per DIMACS).
            reason_ci as i32
        } else {
            // Translation table lookup. The kernel ABI documents the
            // table as a `*const i32` of length `num_clauses`, so this
            // offset is in-bounds whenever `reason_ci < num_clauses`.
            // SAFETY: contract enforced by the host via
            // `set_clause_id_translation`.
            unsafe { ctx.clause_id_translation.add(reason_ci).read() }
        };
        // SAFETY: same provisioning contract as the literals buffer;
        // the host is required to size reasons >= cap when installed.
        unsafe {
            ctx.implied_reasons_out.add(idx).write(id_i32);
        }
    }
    ctx.implied_literals_len += 1;
}

/// Append every literal in `state.trail[snapshot..end]` to the
/// implied-literals output buffer in `ctx`, in order. Used after each
/// `propagate()` step so the host sees the literals BCP newly assigned.
fn drain_implied_trail(state: &BcpState, ctx: &mut KernelCtx, snapshot: usize) {
    let trail_len = state.trail_len();
    for idx in snapshot..trail_len {
        let lit = state.trail_at(idx);
        let reason_ci = state.reason_at(idx);
        // SAFETY: see record_implied_literal docs; the helper itself enforces
        // the bounds check against `ctx.implied_literals_cap`.
        unsafe { record_implied_literal(ctx, lit, reason_ci) };
    }
}

/// # Safety
///
/// Callers must uphold the `KernelEntry` ABI contract:
/// - `ctx` must point to a live, exclusively borrowed `KernelCtx` whose
///   `user_data` field has been set to a `*mut BcpState` referring to a live,
///   exclusively borrowed `BcpState` for the duration of the call.
/// - `input` must point to `len` consecutive valid `u32` values, or be any
///   value when `len == 0`.
pub unsafe extern "C" fn bcp_native_entry(
    ctx: *mut KernelCtx,
    input: *const u32,
    len: usize,
) -> u64 {
    if ctx.is_null() {
        return pack_status(BCP_RESULT_DECODE_ERROR, 0);
    }

    // SAFETY: the caller guarantees `ctx` points to a live, exclusively
    // borrowed `KernelCtx` for the duration of this call (see fn-level docs).
    let ctx_ref = unsafe { &mut *ctx };

    let state_ptr = ctx_ref.user_data as *mut BcpState;
    if state_ptr.is_null() {
        return pack_status(BCP_RESULT_DECODE_ERROR, 0);
    }

    // SAFETY: the caller guarantees `user_data` is a `*mut BcpState` pointing
    // to a live, exclusively borrowed `BcpState` for the duration of this
    // call (see fn-level docs).
    let state = unsafe { &mut *state_ptr };

    // Seed the values array from the host's `initial_values` slice
    // when installed. Mirrors the JIT kernels' Phase 0: the caller
    // communicates the already-settled assignment state without
    // pushing it onto the trail; only the unprocessed suffix arrives
    // as decisions through the `input` slice.
    if !ctx_ref.initial_values.is_null() && ctx_ref.initial_values_len != 0 {
        // SAFETY: the host's `set_initial_values` contract guarantees
        // `initial_values` is valid for `initial_values_len` `i8`
        // reads. The slice is bounded to this call.
        let slice = unsafe {
            core::slice::from_raw_parts(ctx_ref.initial_values, ctx_ref.initial_values_len)
        };
        state.seed_initial_values(slice);
    }

    let starting_trail = state.trail_len();

    let pre_propagate_len = state.trail_len();
    if let Some(conflict_ci) = state.propagate() {
        // Even on conflict, the literals propagated before the conflict
        // are visible on the trail; report them.
        drain_implied_trail(state, ctx_ref, pre_propagate_len);
        ctx_ref.conflicting_clause_index = conflict_ci as i32;
        let counter = (state.trail_len() - starting_trail) as u32;
        return pack_status(BCP_RESULT_CONFLICT, counter);
    }
    drain_implied_trail(state, ctx_ref, pre_propagate_len);

    let input_slice: &[u32] = if len == 0 {
        &[]
    } else {
        // SAFETY: the caller guarantees `input` is valid for `len` consecutive
        // `u32` reads (see fn-level docs); the slice is bounded to this call.
        unsafe { core::slice::from_raw_parts(input, len) }
    };

    for &encoded in input_slice {
        let lit = match decode_literal(encoded) {
            Some(lit) => lit,
            None => {
                let counter = (state.trail_len() - starting_trail) as u32;
                return pack_status(BCP_RESULT_DECODE_ERROR, counter);
            }
        };

        state.assign(lit);

        let pre_inner = state.trail_len();
        if let Some(conflict_ci) = state.propagate() {
            drain_implied_trail(state, ctx_ref, pre_inner);
            ctx_ref.conflicting_clause_index = conflict_ci as i32;
            let counter = (state.trail_len() - starting_trail) as u32;
            return pack_status(BCP_RESULT_CONFLICT, counter);
        }
        drain_implied_trail(state, ctx_ref, pre_inner);
    }

    // Make sure no stale conflict index sticks around from a previous call.
    ctx_ref.conflicting_clause_index = NO_CONFLICTING_CLAUSE;
    let counter = (state.trail_len() - starting_trail) as u32;
    pack_status(BCP_RESULT_OK, counter)
}

pub struct BcpKernelProvider<'a> {
    state: &'a mut BcpState,
}

impl<'a> BcpKernelProvider<'a> {
    pub fn new(state: &'a mut BcpState) -> Self {
        Self { state }
    }

    pub fn encode_literal(var: u32, negated: bool) -> u32 {
        (var << 1) | if negated { 1 } else { 0 }
    }
}

impl<'a> SolverKernelProvider for BcpKernelProvider<'a> {
    fn entry(&self) -> KernelEntry {
        bcp_native_entry
    }

    fn ctx_seed(&self) -> KernelCtx {
        KernelCtx {
            arena_ptr: core::ptr::null_mut(),
            arena_len: 0,
            formula_constants_ptr: core::ptr::null(),
            formula_constants_len: 0,
            user_data: (self.state as *const BcpState as *mut BcpState) as *mut u8,
            status: 0,
            implied_literals_out: core::ptr::NonNull::<i32>::dangling().as_ptr(),
            implied_literals_cap: 0,
            implied_literals_len: 0,
            conflicting_clause_index: NO_CONFLICTING_CLAUSE,
            _reserved_pad: 0,
            implied_reasons_out: core::ptr::null_mut(),
            implied_reasons_cap: 0,
            clause_id_translation: core::ptr::null(),
            initial_values: core::ptr::null(),
            initial_values_len: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver_kernel_abi::SolverKernelHandle;

    #[test]
    fn unit_clause_propagates_through_kernel() {
        let clauses = vec![vec![1i32]];
        let mut state = BcpState::new(3, clauses);
        let provider = BcpKernelProvider::new(&mut state);
        let mut handle = SolverKernelHandle::from_provider(&provider);
        let status = handle.call(&[]);
        assert_eq!(status.result, BCP_RESULT_OK);
        assert!(status.counters > 0);
    }

    #[test]
    fn conflicting_assignment_yields_conflict_result() {
        let clauses = vec![
            vec![1i32, 2i32],
            vec![-1i32, 2i32],
            vec![1i32, -2i32],
            vec![-1i32, -2i32],
        ];
        let mut state = BcpState::new(2, clauses);
        let provider = BcpKernelProvider::new(&mut state);
        let mut handle = SolverKernelHandle::from_provider(&provider);
        let lit_pos1 = BcpKernelProvider::encode_literal(1, false);
        let lit_pos2 = BcpKernelProvider::encode_literal(2, false);
        let status = handle.call(&[lit_pos1, lit_pos2]);
        assert_eq!(status.result, BCP_RESULT_CONFLICT);
    }

    #[test]
    fn zero_var_input_is_decode_error() {
        let mut state = BcpState::new(3, Vec::new());
        let provider = BcpKernelProvider::new(&mut state);
        let mut handle = SolverKernelHandle::from_provider(&provider);
        let status = handle.call(&[0u32]);
        assert_eq!(status.result, BCP_RESULT_DECODE_ERROR);
    }

    #[test]
    fn counter_is_monotone_under_more_assignments() {
        let clauses = vec![vec![-1i32, 2i32], vec![-2i32, 3i32], vec![-3i32, 4i32]];

        let mut state_one = BcpState::new(4, clauses.clone());
        let provider_one = BcpKernelProvider::new(&mut state_one);
        let mut handle_one = SolverKernelHandle::from_provider(&provider_one);
        let lit1 = BcpKernelProvider::encode_literal(1, false);
        let status_one = handle_one.call(&[lit1]);
        assert_eq!(status_one.result, BCP_RESULT_OK);

        let mut state_two = BcpState::new(4, clauses);
        let provider_two = BcpKernelProvider::new(&mut state_two);
        let mut handle_two = SolverKernelHandle::from_provider(&provider_two);
        let lit2 = BcpKernelProvider::encode_literal(2, false);
        let status_two = handle_two.call(&[lit1, lit2]);
        assert_eq!(status_two.result, BCP_RESULT_OK);

        assert!(status_two.counters >= status_one.counters);
    }

    #[test]
    fn native_returns_conflicting_clause_on_conflict() {
        // (x1 v x2 v x3) ^ (-x1) ^ (-x2) ^ (-x3): the chain of unit clauses
        // implies -x1, -x2, -x3 and the first clause is the conflict.
        let clauses = vec![vec![1i32, 2, 3], vec![-1], vec![-2], vec![-3]];
        let mut state = BcpState::new(3, clauses);
        let provider = BcpKernelProvider::new(&mut state);
        let mut handle = SolverKernelHandle::from_provider(&provider);
        let status = handle.call(&[]);
        assert_eq!(status.result, BCP_RESULT_CONFLICT);
        assert_eq!(status.conflicting_clause_index, 0);
    }

    #[test]
    fn native_emits_implied_literals_in_propagation_order() {
        // unit clause `1` followed by binary implications.
        let clauses = vec![vec![1i32], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
        let mut state = BcpState::new(4, clauses);
        let provider = BcpKernelProvider::new(&mut state);
        let mut handle = SolverKernelHandle::from_provider(&provider);

        let mut buf = vec![0i32; 8];
        handle.set_implied_literals_buffer(&mut buf);

        let status = handle.call(&[]);
        assert_eq!(status.result, BCP_RESULT_OK);
        assert_eq!(status.implied_literals_len, 4);
        assert_eq!(&buf[..4], &[1, 2, 3, 4]);
    }

    #[test]
    fn native_implied_literals_overflow_signals() {
        let clauses = vec![vec![1i32], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
        let mut state = BcpState::new(4, clauses);
        let provider = BcpKernelProvider::new(&mut state);
        let mut handle = SolverKernelHandle::from_provider(&provider);

        // Capacity 2 < 4 propagations -> overflow.
        let mut tiny = vec![0i32; 2];
        handle.set_implied_literals_buffer(&mut tiny);

        let status = handle.call(&[]);
        assert_eq!(status.result, BCP_RESULT_OK);
        assert_eq!(status.implied_literals_len, usize::MAX);
    }

    #[test]
    fn native_emits_reasons_in_passthrough_mode() {
        // Unit clause 1 (idx 0), chain via binary clauses 1 (idx 1), 2 (idx 2), 3 (idx 3).
        let clauses = vec![vec![1i32], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
        let mut state = BcpState::new(4, clauses);
        let provider = BcpKernelProvider::new(&mut state);
        let mut handle = SolverKernelHandle::from_provider(&provider);

        let mut lits = vec![0i32; 8];
        let mut reasons = vec![-9i32; 8];
        handle.set_implied_literals_buffer(&mut lits);
        handle.set_implied_reasons_buffer(&mut reasons);

        let status = handle.call(&[]);
        assert_eq!(status.result, BCP_RESULT_OK);
        assert_eq!(status.implied_literals_len, 4);
        assert!(status.implied_reasons_present, "reasons should be present");
        // Each implied literal's reason is the JIT clause index of the
        // clause that forced it (passthrough mode — no translation table).
        assert_eq!(&lits[..4], &[1, 2, 3, 4]);
        assert_eq!(&reasons[..4], &[0, 1, 2, 3]);
    }

    #[test]
    fn native_emits_reasons_via_translation_table() {
        // Same chain as above; install a translation table mapping each
        // clause idx to a fake "DB offset" id of (100 + idx) and verify
        // the kernel emits those ids instead of the raw indices.
        let clauses = vec![vec![1i32], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
        let mut state = BcpState::new(4, clauses);
        let provider = BcpKernelProvider::new(&mut state);
        let mut handle = SolverKernelHandle::from_provider(&provider);

        let translation: Vec<i32> = vec![100, 101, 102, 103];
        let mut lits = vec![0i32; 8];
        let mut reasons = vec![-9i32; 8];
        handle.set_implied_literals_buffer(&mut lits);
        handle.set_implied_reasons_buffer(&mut reasons);
        handle.set_clause_id_translation(&translation);

        let status = handle.call(&[]);
        assert_eq!(status.result, BCP_RESULT_OK);
        assert_eq!(status.implied_literals_len, 4);
        assert!(status.implied_reasons_present);
        assert_eq!(&lits[..4], &[1, 2, 3, 4]);
        assert_eq!(&reasons[..4], &[100, 101, 102, 103]);
    }

    #[test]
    fn native_handles_no_reason_buffer() {
        // Reasons buffer not installed: literals still written, reasons
        // skipped, status snapshot reports reasons absent.
        let clauses = vec![vec![1i32], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
        let mut state = BcpState::new(4, clauses);
        let provider = BcpKernelProvider::new(&mut state);
        let mut handle = SolverKernelHandle::from_provider(&provider);

        let mut lits = vec![0i32; 8];
        handle.set_implied_literals_buffer(&mut lits);
        // Deliberately do NOT call set_implied_reasons_buffer.

        let status = handle.call(&[]);
        assert_eq!(status.result, BCP_RESULT_OK);
        assert_eq!(status.implied_literals_len, 4);
        assert!(!status.implied_reasons_present);
        assert_eq!(&lits[..4], &[1, 2, 3, 4]);
    }
}
