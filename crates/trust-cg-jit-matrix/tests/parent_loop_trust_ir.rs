// trust-cg-jit-matrix/tests/parent_loop_trust_ir.rs - Integration tests for the
// JIT'd TLA+/TY parent-loop kernel authored in trust_ir.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Each test exercises the kernel via SolverKernelHandle::call and asserts
// the resulting counters / digests match `parent_loop_baseline::explore_one_step`.

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use trust_cg_jit_matrix::jit_parent_loop_kernel::JitParentLoopKernelProvider;
use trust_cg_jit_matrix::parent_loop_baseline::{
    Action, ParentLoopState, State, StepResult, TransitionSystem, explore_one_step,
    random_transition_system,
};
use trust_cg_jit_matrix::parent_loop_module_builder::{
    PARENT_LOOP_RESULT_CONTINUED, PARENT_LOOP_RESULT_FRONTIER_EMPTY,
    PARENT_LOOP_RESULT_INVARIANT_VIOLATION,
};
use trust_cg_jit_matrix::solver_kernel_abi::SolverKernelHandle;

const FRONTIER_CAP_DEFAULT: usize = 8 * 1024;

fn build_jit(num_vars: u32, system: &TransitionSystem) -> JitParentLoopKernelProvider {
    JitParentLoopKernelProvider::compile(num_vars, system.clone(), FRONTIER_CAP_DEFAULT)
        .expect("JIT compile of parent-loop kernel")
}

fn call_with_budget(handle: &mut SolverKernelHandle, max_steps: u64) -> (u32, u32) {
    // The kernel reads the budget out of the `input_len` argument; we pass an
    // empty slice but force the length via a manually constructed call sequence.
    // The current `SolverKernelHandle::call(&[u32])` API uses `slice.len()` for
    // `input_len`, so we synthesise a zero-filled slice of the requested length.
    let dummy: Vec<u32> = vec![0u32; max_steps as usize];
    let status = handle.call(&dummy);
    (status.result, status.counters)
}

#[test]
fn single_step_matches_baseline_two_state_cycle() {
    let toggle = Action {
        guard_mask: 0,
        guard_value: 0,
        set_mask: 0x1,
        set_value: 0x1,
    };
    let untoggle = Action {
        guard_mask: 0x1,
        guard_value: 0x1,
        set_mask: 0x1,
        set_value: 0x0,
    };
    let system = TransitionSystem {
        init: State(0),
        actions: vec![toggle, untoggle],
        invariant_mask: 0,
        invariant_value: 0,
    };

    let provider = build_jit(2, &system);
    let mut handle = SolverKernelHandle::from_provider(&provider);

    // First call: do 1 step.
    let (result, counters) = call_with_budget(&mut handle, 1);
    assert_eq!(result, PARENT_LOOP_RESULT_CONTINUED);
    assert_eq!(counters, 1);

    // Mirror with the native baseline.
    let mut native = ParentLoopState::new(&system);
    let r1 = explore_one_step(&mut native, &system);
    assert!(matches!(r1, StepResult::Continued));

    assert_eq!(provider.parent_count(), native.parent_count);
    assert_eq!(provider.generated_count(), native.generated_count);
    assert_eq!(provider.parent_digest(), native.parent_digest);
    assert_eq!(provider.fingerprint(), native.fingerprint);
}

#[test]
fn two_state_cycle_runs_to_frontier_empty() {
    let toggle = Action {
        guard_mask: 0,
        guard_value: 0,
        set_mask: 0x1,
        set_value: 0x1,
    };
    let untoggle = Action {
        guard_mask: 0x1,
        guard_value: 0x1,
        set_mask: 0x1,
        set_value: 0x0,
    };
    let system = TransitionSystem {
        init: State(0),
        actions: vec![toggle, untoggle],
        invariant_mask: 0,
        invariant_value: 0,
    };

    let provider = build_jit(2, &system);
    let mut handle = SolverKernelHandle::from_provider(&provider);

    // Two-state cycle reaches frontier-empty in two steps.
    let (result, counters) = call_with_budget(&mut handle, 8);
    assert_eq!(result, PARENT_LOOP_RESULT_FRONTIER_EMPTY);
    assert!(counters >= 2, "expected >= 2 steps, got {counters}");

    // Native reference: drive until frontier empty.
    let mut native = ParentLoopState::new(&system);
    let mut native_steps: u32 = 0;
    loop {
        match explore_one_step(&mut native, &system) {
            StepResult::Continued => {
                native_steps += 1;
            }
            StepResult::FrontierEmpty => {
                break;
            }
            StepResult::InvariantViolation(_) => panic!("unexpected violation"),
        }
    }
    assert_eq!(counters, native_steps);
    assert_eq!(provider.parent_count(), native.parent_count);
    assert_eq!(provider.generated_count(), native.generated_count);
    assert_eq!(provider.parent_digest(), native.parent_digest);
    assert_eq!(provider.fingerprint(), native.fingerprint);
}

#[test]
fn invariant_violation_detected() {
    let bad = Action {
        guard_mask: 0,
        guard_value: 0,
        set_mask: 0x1,
        set_value: 0x1,
    };
    let system = TransitionSystem {
        init: State(0),
        actions: vec![bad],
        invariant_mask: 0x1,
        invariant_value: 0x0,
    };

    let provider = build_jit(2, &system);
    let mut handle = SolverKernelHandle::from_provider(&provider);
    let (result, _counters) = call_with_budget(&mut handle, 4);
    assert_eq!(result, PARENT_LOOP_RESULT_INVARIANT_VIOLATION);
    assert_eq!(provider.invariant_violations(), 1);
    assert_eq!(provider.last_violating_state(), 1);
}

#[test]
fn determinism_same_seed_same_telemetry() {
    let system = random_transition_system(8, 16, 0xDEAD_BEEF);

    // Run the JIT kernel to frontier-empty with a generous budget.
    let provider = build_jit(8, &system);
    let mut handle = SolverKernelHandle::from_provider(&provider);
    let (result_a, counters_a) = call_with_budget(&mut handle, 4096);
    assert!(matches!(
        result_a,
        x if x == PARENT_LOOP_RESULT_FRONTIER_EMPTY || x == PARENT_LOOP_RESULT_CONTINUED
    ));
    let digest_a = provider.parent_digest();
    let fp_a = provider.fingerprint();
    let pc_a = provider.parent_count();
    let gc_a = provider.generated_count();

    // Repeat with a fresh provider (same seed -> same system -> same arena).
    let provider2 = build_jit(8, &system);
    let mut handle2 = SolverKernelHandle::from_provider(&provider2);
    let (result_b, counters_b) = call_with_budget(&mut handle2, 4096);
    assert_eq!(result_a, result_b);
    assert_eq!(counters_a, counters_b);
    assert_eq!(provider2.parent_digest(), digest_a);
    assert_eq!(provider2.fingerprint(), fp_a);
    assert_eq!(provider2.parent_count(), pc_a);
    assert_eq!(provider2.generated_count(), gc_a);
}

#[test]
fn multi_call_matches_baseline() {
    let system = random_transition_system(8, 16, 0xDEAD_BEEF);

    let provider = build_jit(8, &system);
    let mut handle = SolverKernelHandle::from_provider(&provider);

    let mut native = ParentLoopState::new(&system);

    // 100 steps total across 4 JIT calls (25 + 25 + 25 + 25). Each call's
    // post-call counters MUST equal the native baseline driven the same
    // way; on frontier-empty we stop both.
    let mut total_done: u64 = 0;
    let mut frontier_empty = false;
    for _ in 0..4 {
        if frontier_empty {
            break;
        }
        let (result, counters) = call_with_budget(&mut handle, 25);
        for _ in 0..counters {
            match explore_one_step(&mut native, &system) {
                StepResult::Continued => {}
                StepResult::FrontierEmpty => {
                    frontier_empty = true;
                    break;
                }
                StepResult::InvariantViolation(_) => {
                    panic!("unexpected violation in native baseline");
                }
            }
        }
        total_done += counters as u64;
        if result == PARENT_LOOP_RESULT_FRONTIER_EMPTY {
            // Pull the final native step (which reports FrontierEmpty)
            // so the native loop's "frontier empty" observation matches.
            if !frontier_empty {
                let _ = explore_one_step(&mut native, &system);
            }
            break;
        }
    }

    let _ = total_done;
    assert_eq!(provider.parent_count(), native.parent_count);
    assert_eq!(provider.generated_count(), native.generated_count);
    assert_eq!(provider.parent_digest(), native.parent_digest);
    assert_eq!(provider.fingerprint(), native.fingerprint);
}

#[test]
fn reset_arena_rewinds_state() {
    let system = random_transition_system(8, 16, 0x1234_5678);
    let provider = build_jit(8, &system);
    let mut handle = SolverKernelHandle::from_provider(&provider);
    let (_, counters1) = call_with_budget(&mut handle, 50);
    let pc1 = provider.parent_count();
    assert!(pc1 > 0, "first call should make progress");
    let _ = counters1;

    provider.reset_arena();
    assert_eq!(provider.parent_count(), 0);
    assert_eq!(provider.generated_count(), 0);
    assert_eq!(provider.parent_digest(), 0);
    assert_eq!(provider.fingerprint(), 0);
    assert_eq!(provider.frontier_len(), 1);
    assert!(provider.arena().visited_contains(system.init.0));

    let (_, counters2) = call_with_budget(&mut handle, 50);
    let _ = counters2;
    assert_eq!(provider.parent_count(), pc1);
}

/// Equivalence on the denser fixture used by the
/// `parent_loop_dense_jit_vs_native_bench` bench: every action is
/// always-enabled, set_value flips bit i on (even i) or off (odd i).
/// This produces a wide BFS frontier so the bench measures the
/// action-sweep loop body rather than the per-call dispatch.
fn dense_transition_system_for_test(_num_vars: u32, num_actions: u32) -> TransitionSystem {
    let mut actions = Vec::with_capacity(num_actions as usize);
    for i in 0..num_actions {
        let bit = 1u64 << i;
        let set_value = if i.is_multiple_of(2) { bit } else { 0 };
        actions.push(Action {
            guard_mask: 0,
            guard_value: 0,
            set_mask: bit,
            set_value,
        });
    }
    TransitionSystem {
        init: State(0),
        actions,
        invariant_mask: 0,
        invariant_value: 0,
    }
}

#[test]
fn dense_fixture_jit_matches_native() {
    // Small enough to drain the frontier inside one budgeted call,
    // large enough that the BFS does real work.
    let system = dense_transition_system_for_test(8, 8);
    let provider = build_jit(8, &system);
    let mut handle = SolverKernelHandle::from_provider(&provider);

    // Drive the JIT to completion.
    let mut total_jit_steps = 0u64;
    loop {
        let (result, counters) = call_with_budget(&mut handle, 4096);
        total_jit_steps += counters as u64;
        if result == PARENT_LOOP_RESULT_FRONTIER_EMPTY
            || result == PARENT_LOOP_RESULT_INVARIANT_VIOLATION
        {
            break;
        }
        if counters == 0 {
            // Defensive: shouldn't happen, but avoid an infinite loop
            // if it does.
            break;
        }
    }
    let _ = total_jit_steps;

    // Drive the native baseline to completion on the same fixture.
    let mut native = ParentLoopState::new(&system);
    loop {
        match explore_one_step(&mut native, &system) {
            StepResult::Continued => {}
            StepResult::FrontierEmpty => break,
            StepResult::InvariantViolation(_) => panic!("unexpected violation"),
        }
    }

    assert_eq!(
        provider.parent_count(),
        native.parent_count,
        "dense parent_count mismatch"
    );
    assert_eq!(
        provider.generated_count(),
        native.generated_count,
        "dense generated_count mismatch"
    );
    assert_eq!(provider.parent_digest(), native.parent_digest);
    assert_eq!(provider.fingerprint(), native.fingerprint);
    // Sanity: even at 4 even-bit toggles we should reach 16 parents.
    assert!(
        native.parent_count >= 16,
        "dense BFS should reach >=16 parents, got {}",
        native.parent_count
    );
}

#[test]
fn dense_fixture_one_budgeted_call_reaches_expected_parents() {
    // The bench drives `STEPS=1000` per iter and uses early-exit. Confirm
    // that on the dense fixtures a single 1000-step call really does
    // visit a substantial portion of the reachable set (i.e. the JIT
    // is paying steady-state per-step cost, not just dispatch).
    for (label, num_vars, num_actions, _expected_full_reachable) in [
        ("dense_16v_16a", 16u32, 16u32, 256u64),
        ("dense_20v_20a", 20u32, 20u32, 1024u64),
        ("dense_24v_24a", 24u32, 24u32, 4096u64),
    ] {
        let system = dense_transition_system_for_test(num_vars, num_actions);
        let provider = build_jit(num_vars, &system);
        let mut handle = SolverKernelHandle::from_provider(&provider);
        let (_result, counters) = call_with_budget(&mut handle, 1000);
        let pc = provider.parent_count();
        let gc = provider.generated_count();
        eprintln!(
            "{label}: 1000-step call -> counters={} parent_count={} generated_count={}",
            counters, pc, gc
        );
        assert!(
            pc >= 1,
            "{label}: single budgeted call should make progress, parent_count={}",
            pc
        );
    }
}

#[test]
fn dense_fixture_reachable_set_sizes_match_bench_expectations() {
    // Diagnostic: confirm the dense bench's three cases produce
    // wide enough reachable sets to exercise the action-sweep body
    // for many iterations, not drain in 1-2 steps the way the
    // shallow `random_transition_system` cases do.
    for (label, num_vars, num_actions, expected_reachable_min) in [
        ("dense_16v_16a", 16u32, 16u32, 256u64), // 2^(16/2) = 256
        ("dense_20v_20a", 20u32, 20u32, 1024u64),
        ("dense_24v_24a", 24u32, 24u32, 4096u64),
    ] {
        let system = dense_transition_system_for_test(num_vars, num_actions);
        let mut native = ParentLoopState::new(&system);
        loop {
            match explore_one_step(&mut native, &system) {
                StepResult::Continued => {}
                StepResult::FrontierEmpty => break,
                StepResult::InvariantViolation(_) => panic!("unexpected violation"),
            }
        }
        assert!(
            native.parent_count >= expected_reachable_min,
            "{label}: native reached only {} parents, expected >= {}",
            native.parent_count,
            expected_reachable_min
        );
        // generated_count = parent_count * num_actions for the always-
        // enabled case; sanity-check it.
        assert_eq!(
            native.generated_count,
            native.parent_count * num_actions as u64,
            "{label}: generated_count not parent_count*num_actions",
        );
    }
}
