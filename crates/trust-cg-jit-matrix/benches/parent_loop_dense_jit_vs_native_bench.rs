// trust-cg-jit-matrix/benches/parent_loop_dense_jit_vs_native_bench.rs -
// Denser-workload parent-loop JIT vs native bench.
//
// YYY's existing `parent_loop_jit_vs_native_bench` uses
// `random_transition_system`, which generates actions with random
// guard masks AND random guard values. For any non-empty guard mask,
// the action only fires when the parent state happens to match the
// fixed `guard_value` random bits, so most actions never enable from
// the seeded init and the frontier drains in 1-2 steps. That means
// per-call dispatch (load arena pointer, decode ctx, set up SSA
// entry) dominates over the action-sweep loop body, which is exactly
// what the JIT is supposed to make cheap.
//
// This bench builds a *dense* transition system instead: every action
// has `guard_mask = 0` (always-enabled), with set masks chosen to
// touch a single distinct bit each. With `num_actions = num_vars`
// you get the full `2^num_vars` reachable set; with fewer actions
// you get a wide-but-bounded frontier. Either way every parent in
// the frontier exercises *all* actions, so the per-step inner loop
// runs the full action sweep and is the dominant cost.
//
// This is a fixture-level change, not a kernel change: the JIT
// kernel and the native baseline both consume the same
// `TransitionSystem` shape unchanged. We are NOT modifying the
// production kernel ABI - the dense system is just another input
// the existing kernel handles.
//
// IMPORTANT: criterion's `BatchSize::SmallInput` collects B
// setup-results into a Vec first, then runs the routine B times
// without re-running setup. That is fine for routines that
// read-only consume their setup input (the documented pattern of
// `iter_batched`) but here the routine mutates persistent provider
// state through interior `RefCell`. On a sparse workload that
// drains the frontier in 1-2 steps (YYY's `random_transition_system`
// cases) iter-2-and-beyond observe "frontier already empty" and
// return immediately - same shape as iter 1, so the measurement is
// honest. On a dense workload where BFS reaches hundreds of states,
// iter-2 observes the post-state of iter-1 (visited bits set,
// frontier empty) and exits trivially, drastically understating the
// JIT's per-iter work. To measure honestly we use
// `BatchSize::PerIteration`: setup runs immediately before each
// routine call, paying the reset cost on every iter but giving every
// iter the same starting state.
//
// Workloads:
//   dense_16v_16a   - 16 vars, 16 always-on actions
//                     (every reachable state, frontier saturates fast)
//   dense_20v_20a   - 20 vars, 20 always-on actions
//                     (larger reachable set, more steady-state work)
//   dense_24v_24a   - 24 vars, 24 always-on actions
//                     (matches YYY's large fixture in num_vars; the
//                      visited bitmap is the same 2 MiB)
//
// We cap STEPS the same as YYY (1000) and let frontier-empty terminate
// early in each iter. With dense systems the frontier doesn't drain in
// 1-2 steps; it stays large until you've visited a substantial fraction
// of the reachable set, so the 1000-step budget runs the action sweep
// many times per iter.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use trust_cg_jit_matrix::jit_parent_loop_kernel::JitParentLoopKernelProvider;
use trust_cg_jit_matrix::parent_loop_baseline::{
    Action, ParentLoopState, State, StepResult, TransitionSystem, explore_one_step,
};
use trust_cg_jit_matrix::solver_kernel_abi::SolverKernelHandle;

struct DenseCase {
    label: &'static str,
    num_vars: u32,
    num_actions: u32,
}

const CASES: &[DenseCase] = &[
    DenseCase {
        label: "dense_16v_16a",
        num_vars: 16,
        num_actions: 16,
    },
    DenseCase {
        label: "dense_20v_20a",
        num_vars: 20,
        num_actions: 20,
    },
    DenseCase {
        label: "dense_24v_24a",
        num_vars: 24,
        num_actions: 24,
    },
];

const STEPS: usize = 1000;
const FRONTIER_CAP: usize = 64 * 1024;

/// Build a dense transition system: every action is always-enabled
/// (guard_mask = 0, guard_value = 0) and flips a single distinct bit
/// (set_mask = 1<<i, set_value = 0). From the init state, every
/// action is enabled at every parent, so the action sweep runs to
/// completion every step.
fn dense_transition_system(num_vars: u32, num_actions: u32) -> TransitionSystem {
    assert!(num_vars <= 64);
    assert!(num_actions <= num_vars);
    let mut actions = Vec::with_capacity(num_actions as usize);
    for i in 0..num_actions {
        let bit = 1u64 << i;
        // guard_mask = 0 means the guard is trivially satisfied at
        // every state. The action toggles bit `i` to 0 if currently
        // set, else flips it on via a companion action - but to keep
        // the action set compact and the reachable graph predictable
        // we use set_value = bit so each action is "set bit i to 1".
        // To still get a wide reachable set we use set_value = 0 for
        // odd i and set_value = bit for even i, which gives both
        // directions and produces the full 2^num_actions reachable
        // states.
        let set_mask = bit;
        let set_value = if i.is_multiple_of(2) { bit } else { 0 };
        actions.push(Action {
            guard_mask: 0,
            guard_value: 0,
            set_mask,
            set_value,
        });
    }
    TransitionSystem {
        init: State(0),
        actions,
        // No invariant violation in the dense case - we want the
        // bench to measure the action sweep, not invariant
        // termination.
        invariant_mask: 0,
        invariant_value: 0,
    }
}

fn drive_native(state: &mut ParentLoopState, system: &TransitionSystem) -> u64 {
    for _ in 0..STEPS {
        match explore_one_step(state, system) {
            StepResult::Continued => {}
            StepResult::FrontierEmpty => break,
            StepResult::InvariantViolation(_) => break,
        }
    }
    state.parent_digest ^ state.fingerprint
}

fn drive_jit(provider: &JitParentLoopKernelProvider, handle: &mut SolverKernelHandle) -> u64 {
    let dummy = vec![0u32; STEPS];
    let _status = handle.call(&dummy);
    provider.parent_digest() ^ provider.fingerprint()
}

fn bench_native_dense(c: &mut Criterion) {
    let mut group = c.benchmark_group("parent_loop_native_baseline_dense");
    for case in CASES {
        let system = dense_transition_system(case.num_vars, case.num_actions);
        group.bench_function(case.label, |b| {
            b.iter_batched(
                || ParentLoopState::new(&system),
                |mut state| {
                    black_box(drive_native(&mut state, &system));
                },
                criterion::BatchSize::PerIteration,
            );
        });
    }
    group.finish();
}

fn bench_jit_dense(c: &mut Criterion) {
    let mut group = c.benchmark_group("parent_loop_jit_dense");
    for case in CASES {
        let system = dense_transition_system(case.num_vars, case.num_actions);
        let provider =
            JitParentLoopKernelProvider::compile(case.num_vars, system.clone(), FRONTIER_CAP)
                .expect("JIT compile of parent-loop kernel (dense)");
        group.bench_function(case.label, |b| {
            let mut handle = SolverKernelHandle::from_provider(&provider);
            b.iter_batched(
                || provider.reset_arena(),
                |_| {
                    black_box(drive_jit(&provider, &mut handle));
                },
                criterion::BatchSize::PerIteration,
            );
        });
    }
    group.finish();
}

criterion_group!(benches, bench_native_dense, bench_jit_dense);
criterion_main!(benches);
