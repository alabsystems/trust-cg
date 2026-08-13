// trust-cg-jit-matrix/tests/bcp_watched_literal_trust_ir.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Integration tests for the watched-literal BCP kernel authored in
// `bcp_module_builder::build_bcp_propagate_watched_literal_module`. The
// kernel implements the classical two-watched-literal algorithm against a
// fixed-capacity per-literal watch table laid out in `BcpWatchedArena`.
//
// Each test compares the JIT'd kernel's `result` code (lo32 of the packed
// status word) against the native watched-literal reference in
// `bcp_baseline::BcpState`, which is the same algorithm with growable
// `Vec<Vec<_>>` watch lists.

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use trust_cg_jit_matrix::bcp_baseline::BcpState;
use trust_cg_jit_matrix::bcp_module_builder::{
    BCP_RESULT_CONFLICT, BCP_RESULT_DECODE_ERROR, BCP_RESULT_OK,
};
use trust_cg_jit_matrix::jit_bcp_kernel::JitBcpWatchedLiteralKernelProvider;
use trust_cg_jit_matrix::solver_kernel_abi::SolverKernelHandle;

fn encode(var: u32, negated: bool) -> u32 {
    (var << 1) | if negated { 1 } else { 0 }
}

fn decode_literal(encoded: u32, num_vars: u32) -> Option<i32> {
    let var = encoded >> 1;
    if var == 0 || var > num_vars {
        return None;
    }
    if var > i32::MAX as u32 {
        return None;
    }
    let polarity = encoded & 1;
    let signed = var as i32;
    Some(if polarity == 0 { signed } else { -signed })
}

/// Run the JIT'd watched-literal kernel and return the result + the
/// final values table (1..=num_vars).
fn run_jit(num_vars: usize, clauses: &[Vec<i32>], input: &[u32]) -> (u32, Vec<(usize, i8)>) {
    let provider =
        JitBcpWatchedLiteralKernelProvider::compile(num_vars, clauses.to_vec(), input.len())
            .expect("JIT compile of watched-literal BCP kernel");
    provider.reset_arena();
    let mut handle = SolverKernelHandle::from_provider(&provider);
    let status = handle.call(input);

    let mut values_out: Vec<(usize, i8)> = Vec::new();
    for v in 1..=num_vars {
        values_out.push((v, provider.arena_values()[v]));
    }
    (status.result, values_out)
}

/// Native reference: same algorithm via `BcpState`. Runs the initial
/// propagate (handles unit clauses), then assigns each decoded input
/// literal and propagates between assignments. This matches the
/// "decode-then-propagate-after-each-assignment" shape of the JIT kernel
/// (which propagates them all at once via the trail/qhead, since
/// watched-literal BCP is order-insensitive for `result`).
fn reference_run(num_vars: usize, clauses: &[Vec<i32>], input: &[u32]) -> (u32, Vec<(usize, i8)>) {
    let mut state = BcpState::new(num_vars, clauses.to_vec());
    let mut result = BCP_RESULT_OK;

    if state.propagate().is_some() {
        result = BCP_RESULT_CONFLICT;
    } else {
        for &enc in input {
            let lit = match decode_literal(enc, num_vars as u32) {
                Some(l) => l,
                None => {
                    result = BCP_RESULT_DECODE_ERROR;
                    break;
                }
            };
            state.assign(lit);
            if state.propagate().is_some() {
                result = BCP_RESULT_CONFLICT;
                break;
            }
        }
    }

    let mut values: Vec<(usize, i8)> = Vec::new();
    for v in 1..=num_vars {
        let val = match state.value_of_lit(v as i32) {
            trust_cg_jit_matrix::bcp_baseline::Value::Unassigned => 0,
            trust_cg_jit_matrix::bcp_baseline::Value::True => 1,
            trust_cg_jit_matrix::bcp_baseline::Value::False => -1,
        };
        values.push((v, val));
    }
    (result, values)
}

#[test]
fn empty_input_round_trips() {
    let num_vars = 3;
    let clauses: Vec<Vec<i32>> = vec![vec![1, 2], vec![-2, 3]];
    let (jit_status, _jit_vals) = run_jit(num_vars, &clauses, &[]);
    let (ref_status, _ref_vals) = reference_run(num_vars, &clauses, &[]);
    assert_eq!(jit_status, BCP_RESULT_OK);
    assert_eq!(jit_status, ref_status);
}

#[test]
fn empty_formula_round_trips() {
    let num_vars = 0;
    let clauses: Vec<Vec<i32>> = vec![];
    let (jit_status, _) = run_jit(num_vars, &clauses, &[]);
    let (ref_status, _) = reference_run(num_vars, &clauses, &[]);
    assert_eq!(jit_status, BCP_RESULT_OK);
    assert_eq!(jit_status, ref_status);
}

#[test]
fn unit_clause_propagates_one_literal() {
    let num_vars = 3;
    let clauses = vec![vec![3]];
    let (jit_status, jit_vals) = run_jit(num_vars, &clauses, &[]);
    let (ref_status, ref_vals) = reference_run(num_vars, &clauses, &[]);
    assert_eq!(jit_status, BCP_RESULT_OK);
    assert_eq!(jit_status, ref_status);
    assert_eq!(jit_vals, ref_vals);
}

#[test]
fn three_variable_unsat_reaches_conflict() {
    let num_vars = 3;
    let clauses = vec![vec![1, 2, 3], vec![-1], vec![-2], vec![-3]];
    let (jit_status, _) = run_jit(num_vars, &clauses, &[]);
    let (ref_status, _) = reference_run(num_vars, &clauses, &[]);
    assert_eq!(jit_status, BCP_RESULT_CONFLICT);
    assert_eq!(jit_status, ref_status);
}

#[test]
fn chain_propagation_three_var() {
    // After deciding x1, the binary implications cascade to x2 and x3.
    let num_vars = 3;
    let clauses = vec![vec![-1, 2], vec![-2, 3]];
    let input = vec![encode(1, false)];
    let (jit_status, jit_vals) = run_jit(num_vars, &clauses, &input);
    let (ref_status, ref_vals) = reference_run(num_vars, &clauses, &input);
    assert_eq!(jit_status, BCP_RESULT_OK);
    assert_eq!(jit_status, ref_status);
    assert_eq!(jit_vals, ref_vals);
    assert_eq!(jit_vals, vec![(1, 1), (2, 1), (3, 1)]);
}

#[test]
fn conflicting_decision_yields_conflict() {
    let num_vars = 3;
    let clauses = vec![vec![1, 2], vec![-1, 3], vec![-1, -3]];
    let input = vec![encode(1, false)];
    let (jit_status, _) = run_jit(num_vars, &clauses, &input);
    let (ref_status, _) = reference_run(num_vars, &clauses, &input);
    assert_eq!(jit_status, BCP_RESULT_CONFLICT);
    assert_eq!(jit_status, ref_status);
}

#[test]
fn multi_decision_sequence_matches_native() {
    let num_vars = 4;
    let clauses = vec![vec![-1, 2], vec![-2, 3], vec![-3, 4], vec![-4, 1]];
    let input = vec![encode(1, false), encode(2, false)];
    let (jit_status, jit_vals) = run_jit(num_vars, &clauses, &input);
    let (ref_status, ref_vals) = reference_run(num_vars, &clauses, &input);
    assert_eq!(jit_status, ref_status);
    assert_eq!(jit_vals, ref_vals);
}

#[test]
fn decode_error_on_zero_var() {
    let num_vars = 3;
    let clauses = vec![vec![1, 2]];
    let input = vec![0u32];
    let (jit_status, _) = run_jit(num_vars, &clauses, &input);
    assert_eq!(jit_status, BCP_RESULT_DECODE_ERROR);
}

#[test]
fn decode_error_on_oob_var() {
    let num_vars = 3;
    let clauses = vec![vec![1, 2]];
    let oob = (num_vars as u32) + 1;
    let input = vec![oob << 1];
    let (jit_status, _) = run_jit(num_vars, &clauses, &input);
    assert_eq!(jit_status, BCP_RESULT_DECODE_ERROR);
}

#[test]
fn binary_conflict_full_assignment() {
    // Same shape as the native baseline's `binary_conflict_detection`:
    // assign +1 and +2; clause (-1, -2) is now all-false -> conflict.
    let num_vars = 2;
    let clauses = vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]];
    let input = vec![encode(1, false), encode(2, false)];
    let (jit_status, _) = run_jit(num_vars, &clauses, &input);
    let (ref_status, _) = reference_run(num_vars, &clauses, &input);
    assert_eq!(jit_status, BCP_RESULT_CONFLICT);
    assert_eq!(jit_status, ref_status);
}

/// Run the watched-literal JIT with a caller-supplied implied-literals
/// buffer and return the resulting `KernelStatus` plus the buffer (so
/// tests can inspect the recorded literals or assert the overflow
/// sentinel).
fn run_jit_with_buffer(
    num_vars: usize,
    clauses: &[Vec<i32>],
    input: &[u32],
    buf: &mut [i32],
) -> trust_cg_jit_matrix::solver_kernel_abi::KernelStatus {
    let provider =
        JitBcpWatchedLiteralKernelProvider::compile(num_vars, clauses.to_vec(), input.len())
            .expect("JIT compile of watched-literal BCP kernel");
    provider.reset_arena();
    let mut handle = SolverKernelHandle::from_provider(&provider);
    handle.set_implied_literals_buffer(buf);
    handle.call(input)
}

#[test]
fn watched_literal_returns_conflicting_clause_on_conflict() {
    // (x1 v x2 v x3) is clause 0; unit clauses (-x1), (-x2), (-x3)
    // propagate to falsify clause 0.
    let num_vars = 3;
    let clauses = vec![vec![1i32, 2, 3], vec![-1], vec![-2], vec![-3]];
    let mut buf = vec![0i32; 16];
    let status = run_jit_with_buffer(num_vars, &clauses, &[], &mut buf);
    assert_eq!(status.result, BCP_RESULT_CONFLICT);
    assert_eq!(
        status.conflicting_clause_index, 0,
        "expected clause 0 to be reported as the falsified clause"
    );
}

#[test]
fn watched_literal_emits_implied_literals_in_propagation_order() {
    // Decide +1; binary chain 2 <- 1, 3 <- 2 fires via the BCP loop.
    let num_vars = 3;
    let clauses = vec![vec![-1i32, 2], vec![-2, 3]];
    let input = vec![encode(1, false)];
    let mut buf = vec![0i32; 16];
    let status = run_jit_with_buffer(num_vars, &clauses, &input, &mut buf);
    assert_eq!(status.result, BCP_RESULT_OK);
    assert_eq!(
        status.implied_literals_len, 2,
        "expected 2 implied literals, got {}",
        status.implied_literals_len
    );
    assert_eq!(&buf[..2], &[2i32, 3], "propagation-order mismatch");
}

#[test]
fn watched_literal_implied_literals_overflow_signals() {
    // Two propagations through a single-slot buffer -> sentinel.
    let num_vars = 3;
    let clauses = vec![vec![-1i32, 2], vec![-2, 3]];
    let input = vec![encode(1, false)];
    let mut tiny = vec![0i32; 1];
    let status = run_jit_with_buffer(num_vars, &clauses, &input, &mut tiny);
    assert_eq!(
        status.implied_literals_len,
        usize::MAX,
        "expected overflow sentinel"
    );
}

/// Sibling of `run_jit_with_buffer` that also installs a reasons buffer
/// (and optionally a clause-id translation table). Returns the final
/// `KernelStatus` so tests can inspect both the literals and reasons
/// streams.
fn run_jit_with_reasons(
    num_vars: usize,
    clauses: &[Vec<i32>],
    input: &[u32],
    lits_buf: &mut [i32],
    reasons_buf: &mut [i32],
    translation: Option<&[i32]>,
) -> trust_cg_jit_matrix::solver_kernel_abi::KernelStatus {
    let provider =
        JitBcpWatchedLiteralKernelProvider::compile(num_vars, clauses.to_vec(), input.len())
            .expect("JIT compile of watched-literal BCP kernel");
    provider.reset_arena();
    let mut handle = SolverKernelHandle::from_provider(&provider);
    handle.set_implied_literals_buffer(lits_buf);
    handle.set_implied_reasons_buffer(reasons_buf);
    if let Some(table) = translation {
        handle.set_clause_id_translation(table);
    }
    handle.call(input)
}

#[test]
fn watched_literal_emits_reasons_in_passthrough_mode() {
    // Unit clause (idx 0) `+1`, then binary chain via clause idx 1
    // (`-1 v 2`) and clause idx 2 (`-2 v 3`) — both implied by the
    // watched-literal BCP loop, NOT by the unit-clause phase.
    let num_vars = 3;
    let clauses = vec![vec![1i32], vec![-1, 2], vec![-2, 3]];
    let mut lits = vec![0i32; 8];
    let mut reasons = vec![-9i32; 8];
    let status = run_jit_with_reasons(num_vars, &clauses, &[], &mut lits, &mut reasons, None);
    assert_eq!(status.result, BCP_RESULT_OK);
    assert_eq!(status.implied_literals_len, 3);
    assert!(status.implied_reasons_present);
    assert_eq!(&lits[..3], &[1i32, 2, 3]);
    // Reason ids match JIT clause indices (passthrough mode).
    assert_eq!(&reasons[..3], &[0i32, 1, 2]);
}

#[test]
fn watched_literal_emits_reasons_via_translation_table() {
    // Same chain; translation table maps idx -> 100+idx.
    let num_vars = 3;
    let clauses = vec![vec![1i32], vec![-1, 2], vec![-2, 3]];
    let mut lits = vec![0i32; 8];
    let mut reasons = vec![-9i32; 8];
    let translation: Vec<i32> = vec![100, 101, 102];
    let status = run_jit_with_reasons(
        num_vars,
        &clauses,
        &[],
        &mut lits,
        &mut reasons,
        Some(&translation),
    );
    assert_eq!(status.result, BCP_RESULT_OK);
    assert_eq!(status.implied_literals_len, 3);
    assert!(status.implied_reasons_present);
    assert_eq!(&lits[..3], &[1i32, 2, 3]);
    assert_eq!(&reasons[..3], &[100, 101, 102]);
}

#[test]
fn watched_literal_handles_no_reason_buffer() {
    // Reasons buffer not installed: literals still written, reasons
    // skipped, status.implied_reasons_present == false.
    let num_vars = 3;
    let clauses = vec![vec![1i32], vec![-1, 2], vec![-2, 3]];
    let mut lits = vec![0i32; 8];
    let status = run_jit_with_buffer(num_vars, &clauses, &[], &mut lits);
    assert_eq!(status.result, BCP_RESULT_OK);
    assert_eq!(status.implied_literals_len, 3);
    assert!(!status.implied_reasons_present);
    assert_eq!(&lits[..3], &[1i32, 2, 3]);
}

#[test]
fn random_3sat_matches_native_on_small_formula() {
    use trust_cg_jit_matrix::bcp_baseline::random_3sat;
    let num_vars = 20;
    let clauses = random_3sat(num_vars, 80, 0xC0FFEE);
    let (jit_status, jit_vals) = run_jit(num_vars, &clauses, &[]);
    let (ref_status, ref_vals) = reference_run(num_vars, &clauses, &[]);
    assert_eq!(jit_status, ref_status);
    assert_eq!(jit_vals, ref_vals);
}

#[test]
fn random_3sat_with_decisions_matches_native() {
    use trust_cg_jit_matrix::bcp_baseline::random_3sat;
    let num_vars = 30;
    let clauses = random_3sat(num_vars, 120, 0xBEEF);
    let input = vec![encode(3, false), encode(7, true), encode(11, false)];
    let (jit_status, jit_vals) = run_jit(num_vars, &clauses, &input);
    let (ref_status, ref_vals) = reference_run(num_vars, &clauses, &input);
    assert_eq!(jit_status, ref_status);
    assert_eq!(jit_vals, ref_vals);
}
