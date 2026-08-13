// trust-cg-jit-matrix/benches/parent_loop_bench.rs - Criterion bench for the
// native Rust parent-loop baseline. The trust-cg-JIT version of the TY parent
// loop must beat this baseline to validate the JIT strategy for TLA+ workloads.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use trust_cg_jit_matrix::parent_loop_baseline::{
    ParentLoopState, StepResult, TransitionSystem, explore_one_step, random_transition_system,
};

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

fn drive(state: &mut ParentLoopState, system: &TransitionSystem) -> u64 {
    for _ in 0..STEPS {
        match explore_one_step(state, system) {
            StepResult::Continued => {}
            StepResult::FrontierEmpty => break,
            StepResult::InvariantViolation(_) => break,
        }
    }
    state.parent_digest ^ state.fingerprint
}

fn bench_parent_loop(c: &mut Criterion) {
    let mut group = c.benchmark_group("parent_loop_baseline");
    for case in CASES {
        let system = random_transition_system(case.num_vars, case.num_actions, case.seed);
        group.bench_function(case.label, |b| {
            b.iter_batched(
                || ParentLoopState::new(&system),
                |mut state| {
                    black_box(drive(&mut state, &system));
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

criterion_group!(benches, bench_parent_loop);
criterion_main!(benches);
