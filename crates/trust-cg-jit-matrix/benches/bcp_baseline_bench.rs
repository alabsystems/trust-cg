// trust-cg-jit-matrix/benches/bcp_baseline_bench.rs - Criterion bench for the
// native Rust watched-literal BCP baseline. The trust-cg-JIT version of BCP
// must beat this baseline by >=1.3x to validate the JIT strategy.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use trust_cg_jit_matrix::bcp_baseline::{BcpState, random_3sat};

struct Case {
    label: &'static str,
    num_vars: usize,
    num_clauses: usize,
    seed: u64,
}

const CASES: &[Case] = &[
    Case {
        label: "small_50v_200c",
        num_vars: 50,
        num_clauses: 200,
        seed: 0xA11CE,
    },
    Case {
        label: "medium_200v_850c",
        num_vars: 200,
        num_clauses: 850,
        seed: 0xB0B,
    },
    Case {
        label: "large_500v_2125c",
        num_vars: 500,
        num_clauses: 2125,
        seed: 0xCAFE,
    },
];

const DECISIONS: usize = 100;

fn random_walk(state: &mut BcpState, decision_seed: u64) -> usize {
    state.reset();
    let _ = state.propagate();
    let mut rng = if decision_seed == 0 {
        0x9E37_79B9_7F4A_7C15
    } else {
        decision_seed
    };
    let num_vars = state.num_vars();
    let mut propagations: usize = 0;

    for _ in 0..DECISIONS {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        let v = (rng % num_vars as u64) as i32 + 1;
        let lit = if (rng >> 1) & 1 == 0 { v } else { -v };
        let before = state.trail_len();
        state.assign(lit);
        if state.propagate().is_some() {
            propagations += state.trail_len() - before;
            state.reset();
            let _ = state.propagate();
        } else {
            propagations += state.trail_len() - before;
        }
    }

    propagations
}

fn bench_bcp_baseline(c: &mut Criterion) {
    let mut group = c.benchmark_group("bcp_baseline");
    for case in CASES {
        let clauses = random_3sat(case.num_vars, case.num_clauses, case.seed);
        group.bench_function(case.label, |b| {
            b.iter_batched(
                || BcpState::new(case.num_vars, clauses.clone()),
                |mut state| {
                    black_box(random_walk(&mut state, case.seed ^ 0xDEAD_BEEF));
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

criterion_group!(benches, bench_bcp_baseline);
criterion_main!(benches);
