// trust-cg-jit-matrix/benches/parent_loop_jit_vs_native_bench.rs - Criterion
// bench comparing the JIT'd parent-loop kernel against the native Rust
// reference at three workload sizes mirroring the existing parent_loop_bench.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Workloads:
//   small  -  8v / 16a   (seed 0xA11CE)
//   medium - 16v / 64a   (seed 0xB0B)
//   large  - 24v / 256a  (seed 0xCAFE)
//
// Each bench iter resets the arena (or rebuilds the native ParentLoopState),
// then drives up to `STEPS` parent steps and black_boxes the resulting digest+
// fingerprint xor so the optimizer cannot hoist the work.

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use trust_cg_jit_matrix::jit_parent_loop_kernel::JitParentLoopKernelProvider;
use trust_cg_jit_matrix::parent_loop_baseline::{
    ParentLoopState, StepResult, TransitionSystem, explore_one_step, random_transition_system,
};
use trust_cg_jit_matrix::solver_kernel_abi::SolverKernelHandle;

struct Case {
    label: &'static str,
    num_vars: u32,
    num_actions: usize,
    seed: u64,
}

const CASES: &[Case] = &[
    Case {
        label: "small_8v_16a",
        num_vars: 8,
        num_actions: 16,
        seed: 0xA11CE,
    },
    Case {
        label: "medium_16v_64a",
        num_vars: 16,
        num_actions: 64,
        seed: 0xB0B,
    },
    Case {
        label: "large_24v_256a",
        num_vars: 24,
        num_actions: 256,
        seed: 0xCAFE,
    },
];

const STEPS: usize = 1000;
const FRONTIER_CAP: usize = 64 * 1024;

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
    // One call runs up to STEPS steps; budget passed via the input slice length.
    let dummy = vec![0u32; STEPS];
    let _status = handle.call(&dummy);
    provider.parent_digest() ^ provider.fingerprint()
}

fn bench_native(c: &mut Criterion) {
    let mut group = c.benchmark_group("parent_loop_native_baseline");
    for case in CASES {
        let system = random_transition_system(case.num_vars, case.num_actions, case.seed);
        group.bench_function(case.label, |b| {
            b.iter_batched(
                || ParentLoopState::new(&system),
                |mut state| {
                    black_box(drive_native(&mut state, &system));
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

fn bench_jit(c: &mut Criterion) {
    let mut group = c.benchmark_group("parent_loop_jit");
    for case in CASES {
        let system = random_transition_system(case.num_vars, case.num_actions, case.seed);
        // The JIT provider amortizes the codegen across iterations; the per-iter
        // setup is a cheap arena reset.
        let provider =
            JitParentLoopKernelProvider::compile(case.num_vars, system.clone(), FRONTIER_CAP)
                .expect("JIT compile of parent-loop kernel");
        group.bench_function(case.label, |b| {
            let mut handle = SolverKernelHandle::from_provider(&provider);
            b.iter_batched(
                || provider.reset_arena(),
                |_| {
                    black_box(drive_jit(&provider, &mut handle));
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

criterion_group!(benches, bench_native, bench_jit);
criterion_main!(benches);
