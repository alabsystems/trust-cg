// trust-cg-jit-matrix/benches/jit_vs_native_bcp_bench.rs - Head-to-head
// criterion bench comparing the native watched-literal BCP kernel against the
// trust-cg-JIT'd BCP kernels.
//
// Two bench groups are reported:
//
// 1. `bcp_propagate_throughput`: both providers receive
//    an empty input slice. Workload measured is "given a static clause set,
//    propagate to fixpoint". Kept stable so prior reported numbers remain
//    reproducible. JIT side uses the scan-only kernel.
//
// 2. `bcp_propagate_with_decisions_throughput`: both providers receive the
//    same fixed handful of decision-literal `u32`s (one polarity-tagged
//    `(var << 1) | polarity` slot per element). Workload measured is "given
//    a static clause set + a handful of decisions, decode the decisions,
//    seed the value array, and propagate to fixpoint". JIT side uses the
//    sibling `bcp_propagate_with_decisions` kernel that actually consumes
//    its input slice.
//
// JIT compilation cost is paid once outside the timed loop for both groups.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use trust_cg_jit_matrix::bcp_baseline::{BcpState, random_3sat};
use trust_cg_jit_matrix::bcp_kernel::BcpKernelProvider;
use trust_cg_jit_matrix::jit_bcp_kernel::{
    JitBcpKernelProvider, JitBcpWatchedLiteralChunkedKernelProvider,
    JitBcpWatchedLiteralKernelProvider, JitBcpWithDecisionsProvider,
};
use trust_cg_jit_matrix::solver_kernel_abi::SolverKernelHandle;

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

/// Run native and JIT once on `clauses` and assert they agree on the
/// kernel result. We deliberately do not assert counter equality because the
/// native kernel reports trail-len delta as its counter while the JIT kernel
/// reports its arena trail length; the encodings differ even when the
/// underlying propagation set is identical. A semantic regression at this
/// layer (e.g. JIT no longer detecting a UNSAT formula) will still trip the
/// `result` mismatch and panic the bench before any timings are reported.
fn parity_check(case: &Case, clauses: &[Vec<i32>]) {
    let mut native_state = BcpState::new(case.num_vars, clauses.to_vec());
    let native_provider = BcpKernelProvider::new(&mut native_state);
    let mut native_handle = SolverKernelHandle::from_provider(&native_provider);
    let native_status = native_handle.call(&[]);

    let jit_provider = JitBcpKernelProvider::compile(case.num_vars, clauses.to_vec())
        .expect("JIT compile of BCP propagate kernel for parity prologue");
    let mut jit_handle = SolverKernelHandle::from_provider(&jit_provider);
    let jit_status = jit_handle.call(&[]);

    assert_eq!(
        native_status.result, jit_status.result,
        "JIT and native disagree on case `{}`: native.result = {}, jit.result = {}",
        case.label, native_status.result, jit_status.result,
    );
}

fn bench_jit_vs_native(c: &mut Criterion) {
    let mut group = c.benchmark_group("bcp_propagate_throughput");

    for case in CASES {
        let clauses = random_3sat(case.num_vars, case.num_clauses, case.seed);

        // One-off semantic prologue (not timed). Catches JIT-vs-native
        // divergence before we hand criterion any wall-clock numbers.
        parity_check(case, &clauses);

        // Native provider: re-build the BcpState per iteration via
        // iter_batched so each measured call sees the same initial trail
        // state (matches what JIT does, which has no per-iter mutable state
        // baked into the entry).
        let native_label = format!("{}_native", case.label);
        let native_clauses = clauses.clone();
        let native_num_vars = case.num_vars;
        group.bench_function(&native_label, |b| {
            b.iter_batched(
                || {
                    let state = BcpState::new(native_num_vars, native_clauses.clone());
                    Box::new(state)
                },
                |mut state_box| {
                    let provider = BcpKernelProvider::new(&mut state_box);
                    let mut handle = SolverKernelHandle::from_provider(&provider);
                    black_box(handle.call(black_box(&[])));
                },
                criterion::BatchSize::SmallInput,
            );
        });

        // JIT provider: compile once outside the timed loop, then measure
        // only the call. The provider keeps the executable buffer + arena
        // alive for the whole benchmark.
        let jit_provider = JitBcpKernelProvider::compile(case.num_vars, clauses.clone())
            .expect("JIT compile of BCP propagate kernel for bench");
        let jit_label = format!("{}_jit", case.label);
        group.bench_function(&jit_label, |b| {
            // Fresh handle per measurement: the handle owns its own
            // KernelCtx, so resetting it between calls is equivalent to
            // re-seeding from the provider. The provider itself (the
            // ExecutableBuffer and the arena) is reused.
            b.iter_batched(
                || SolverKernelHandle::from_provider(&jit_provider),
                |mut handle| {
                    black_box(handle.call(black_box(&[])));
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

const DECISION_COUNT: usize = 8;

fn random_decisions(num_vars: usize, count: usize, seed: u64) -> Vec<u32> {
    let mut state = if seed == 0 {
        0xDEAD_BEEF_CAFE_F00D
    } else {
        seed
    };
    let mut out = Vec::with_capacity(count);
    let mut chosen: Vec<u32> = Vec::with_capacity(count);
    while out.len() < count {
        let x1 = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        state = x1;
        let var = ((x1 >> 33) as u32) % (num_vars as u32) + 1;
        if chosen.contains(&var) {
            continue;
        }
        let polarity = (x1 & 1) as u32;
        chosen.push(var);
        out.push((var << 1) | polarity);
    }
    out
}

fn bench_jit_vs_native_with_decisions(c: &mut Criterion) {
    let mut group = c.benchmark_group("bcp_propagate_with_decisions_throughput");

    for case in CASES {
        let clauses = random_3sat(case.num_vars, case.num_clauses, case.seed);
        let decisions = random_decisions(case.num_vars, DECISION_COUNT, case.seed ^ 0xDEC1510D);

        let native_label = format!("{}_native_dec{}", case.label, DECISION_COUNT);
        let native_clauses = clauses.clone();
        let native_num_vars = case.num_vars;
        let native_decisions = decisions.clone();
        group.bench_function(&native_label, |b| {
            b.iter_batched(
                || {
                    let state = BcpState::new(native_num_vars, native_clauses.clone());
                    Box::new(state)
                },
                |mut state_box| {
                    let provider = BcpKernelProvider::new(&mut state_box);
                    let mut handle = SolverKernelHandle::from_provider(&provider);
                    black_box(handle.call(black_box(&native_decisions)));
                },
                criterion::BatchSize::SmallInput,
            );
        });

        let jit_provider =
            JitBcpWithDecisionsProvider::compile(case.num_vars, clauses.clone(), DECISION_COUNT)
                .expect("JIT compile of BCP propagate-with-decisions kernel for bench");
        let jit_label = format!("{}_jit_dec{}", case.label, DECISION_COUNT);
        let jit_decisions = decisions.clone();
        group.bench_function(&jit_label, |b| {
            b.iter(|| {
                jit_provider.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&jit_provider);
                black_box(handle.call(black_box(&jit_decisions)));
            });
        });
    }

    group.finish();
}

/// Apples-to-apples comparison: the JIT'd kernel runs the SAME
/// watched-literal algorithm the native baseline runs, so the only
/// remaining variable is "native Rust" vs "trust-cg JIT'd from trust-ir".
/// Two workloads measured: empty input (propagate-to-fixpoint only) and
/// +8 decision literals. Mirrors the workload shape of
/// `bcp_propagate_throughput` and `bcp_propagate_with_decisions_throughput`.
fn bench_jit_watched_literal_vs_native(c: &mut Criterion) {
    let mut group = c.benchmark_group("bcp_watched_literal_throughput");

    for case in CASES {
        let clauses = random_3sat(case.num_vars, case.num_clauses, case.seed);

        // Empty-input variant.
        let native_label = format!("{}_native_empty", case.label);
        let native_clauses = clauses.clone();
        let native_num_vars = case.num_vars;
        group.bench_function(&native_label, |b| {
            b.iter_batched(
                || {
                    let state = BcpState::new(native_num_vars, native_clauses.clone());
                    Box::new(state)
                },
                |mut state_box| {
                    let provider = BcpKernelProvider::new(&mut state_box);
                    let mut handle = SolverKernelHandle::from_provider(&provider);
                    black_box(handle.call(black_box(&[])));
                },
                criterion::BatchSize::SmallInput,
            );
        });

        let jit_provider =
            JitBcpWatchedLiteralKernelProvider::compile(case.num_vars, clauses.clone(), 0)
                .expect("JIT compile of watched-literal BCP kernel for empty workload");
        let jit_label = format!("{}_jit_empty", case.label);
        group.bench_function(&jit_label, |b| {
            b.iter(|| {
                jit_provider.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&jit_provider);
                black_box(handle.call(black_box(&[])));
            });
        });

        // +8 decision literals variant.
        let decisions = random_decisions(case.num_vars, DECISION_COUNT, case.seed ^ 0xDEC1510D);
        let native_dec_label = format!("{}_native_dec{}", case.label, DECISION_COUNT);
        let native_dec_clauses = clauses.clone();
        let native_dec_decisions = decisions.clone();
        group.bench_function(&native_dec_label, |b| {
            b.iter_batched(
                || {
                    let state = BcpState::new(native_num_vars, native_dec_clauses.clone());
                    Box::new(state)
                },
                |mut state_box| {
                    let provider = BcpKernelProvider::new(&mut state_box);
                    let mut handle = SolverKernelHandle::from_provider(&provider);
                    black_box(handle.call(black_box(&native_dec_decisions)));
                },
                criterion::BatchSize::SmallInput,
            );
        });

        let jit_dec_provider = JitBcpWatchedLiteralKernelProvider::compile(
            case.num_vars,
            clauses.clone(),
            DECISION_COUNT,
        )
        .expect("JIT compile of watched-literal BCP kernel for +decisions workload");
        let jit_dec_label = format!("{}_jit_dec{}", case.label, DECISION_COUNT);
        let jit_dec_decisions = decisions.clone();
        group.bench_function(&jit_dec_label, |b| {
            b.iter(|| {
                jit_dec_provider.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&jit_dec_provider);
                black_box(handle.call(black_box(&jit_dec_decisions)));
            });
        });
    }

    group.finish();
}

/// Chunked-layout watched-literal kernel bench. Same workload shape as
/// `bcp_watched_literal_throughput` (empty / +8 decisions, small /
/// medium / large), but the JIT side uses the new
/// `JitBcpWatchedLiteralChunkedKernelProvider` whose arena replaces the
/// per-literal fixed-capacity row-major watch table with a linked-list
/// (`watch_heads + watch_nodes`) layout of size `O(num_vars +
/// num_clauses)`.
///
/// Honest framing: the JIT chunked kernel runs the SAME watched-literal
/// algorithm the fixed-cap kernel runs, so per-call throughput should
/// be roughly comparable on either layout. The win is MEMORY: this
/// group also prints, once per case, the chunked vs fixed-cap arena
/// byte footprint for the `watch_heads + watch_nodes + (watches +
/// watch_lens)` infrastructure. That memory delta is what makes the
/// data-layout-vs-codegen attribution clean: the chunked kernel uses
/// the same memory shape MicroSAT does, so any remaining speedup over
/// MicroSAT in subsequent benches is codegen-attributable, not
/// data-layout-attributable.
fn bench_jit_watched_literal_chunked_vs_native(c: &mut Criterion) {
    let mut group = c.benchmark_group("bcp_watched_literal_chunked_throughput");

    for case in CASES {
        let clauses = random_3sat(case.num_vars, case.num_clauses, case.seed);

        // Memory delta print: this is the headline number for the
        // chunked variant. Done once per case before the timed loops so
        // it shows up alongside criterion's own output.
        let fixed_provider = JitBcpWatchedLiteralKernelProvider::compile(
            case.num_vars,
            clauses.clone(),
            DECISION_COUNT,
        )
        .expect("JIT compile of fixed-capacity watched-literal kernel for memory print");
        let chunked_provider = JitBcpWatchedLiteralChunkedKernelProvider::compile(
            case.num_vars,
            clauses.clone(),
            DECISION_COUNT,
        )
        .expect("JIT compile of chunked watched-literal kernel for memory print");

        // Fixed-capacity watch infra: 2*(num_vars+1) lit rows of length
        // `max(num_clauses, 1)` (= `watch_cap`), each entry a u32, plus
        // 2*num_vars + 2 `watch_lens` slots (u32).
        let fixed_rows = 2 * case.num_vars + 2;
        let fixed_cap = case.num_clauses.max(1);
        let fixed_watch_bytes = fixed_rows * fixed_cap * std::mem::size_of::<u32>()
            + fixed_rows * std::mem::size_of::<u32>();
        let chunked_watch_bytes = chunked_provider.watch_memory_bytes();
        let ratio = (fixed_watch_bytes as f64) / (chunked_watch_bytes.max(1) as f64);
        eprintln!(
            "[chunked bench] case={} watch_infra_bytes: fixed={} chunked={} ratio={:.2}x",
            case.label, fixed_watch_bytes, chunked_watch_bytes, ratio
        );
        drop(fixed_provider);
        drop(chunked_provider);

        // Empty-input variant.
        let native_label = format!("{}_native_empty", case.label);
        let native_clauses = clauses.clone();
        let native_num_vars = case.num_vars;
        group.bench_function(&native_label, |b| {
            b.iter_batched(
                || {
                    let state = BcpState::new(native_num_vars, native_clauses.clone());
                    Box::new(state)
                },
                |mut state_box| {
                    let provider = BcpKernelProvider::new(&mut state_box);
                    let mut handle = SolverKernelHandle::from_provider(&provider);
                    black_box(handle.call(black_box(&[])));
                },
                criterion::BatchSize::SmallInput,
            );
        });

        let jit_fixed_provider =
            JitBcpWatchedLiteralKernelProvider::compile(case.num_vars, clauses.clone(), 0)
                .expect("JIT compile of fixed-cap watched-literal kernel for empty workload");
        let jit_fixed_label = format!("{}_jit_fixed_empty", case.label);
        group.bench_function(&jit_fixed_label, |b| {
            b.iter(|| {
                jit_fixed_provider.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&jit_fixed_provider);
                black_box(handle.call(black_box(&[])));
            });
        });

        let jit_chunked_provider =
            JitBcpWatchedLiteralChunkedKernelProvider::compile(case.num_vars, clauses.clone(), 0)
                .expect("JIT compile of chunked watched-literal kernel for empty workload");
        let jit_chunked_label = format!("{}_jit_chunked_empty", case.label);
        group.bench_function(&jit_chunked_label, |b| {
            b.iter(|| {
                jit_chunked_provider.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&jit_chunked_provider);
                black_box(handle.call(black_box(&[])));
            });
        });

        // +8 decision literals variant.
        let decisions = random_decisions(case.num_vars, DECISION_COUNT, case.seed ^ 0xDEC1510D);

        let native_dec_label = format!("{}_native_dec{}", case.label, DECISION_COUNT);
        let native_dec_clauses = clauses.clone();
        let native_dec_decisions = decisions.clone();
        group.bench_function(&native_dec_label, |b| {
            b.iter_batched(
                || {
                    let state = BcpState::new(native_num_vars, native_dec_clauses.clone());
                    Box::new(state)
                },
                |mut state_box| {
                    let provider = BcpKernelProvider::new(&mut state_box);
                    let mut handle = SolverKernelHandle::from_provider(&provider);
                    black_box(handle.call(black_box(&native_dec_decisions)));
                },
                criterion::BatchSize::SmallInput,
            );
        });

        let jit_fixed_dec_provider = JitBcpWatchedLiteralKernelProvider::compile(
            case.num_vars,
            clauses.clone(),
            DECISION_COUNT,
        )
        .expect("JIT compile of fixed-cap watched-literal kernel for +decisions workload");
        let jit_fixed_dec_label = format!("{}_jit_fixed_dec{}", case.label, DECISION_COUNT);
        let jit_fixed_decisions = decisions.clone();
        group.bench_function(&jit_fixed_dec_label, |b| {
            b.iter(|| {
                jit_fixed_dec_provider.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&jit_fixed_dec_provider);
                black_box(handle.call(black_box(&jit_fixed_decisions)));
            });
        });

        let jit_chunked_dec_provider = JitBcpWatchedLiteralChunkedKernelProvider::compile(
            case.num_vars,
            clauses.clone(),
            DECISION_COUNT,
        )
        .expect("JIT compile of chunked watched-literal kernel for +decisions workload");
        let jit_chunked_dec_label = format!("{}_jit_chunked_dec{}", case.label, DECISION_COUNT);
        let jit_chunked_decisions = decisions.clone();
        group.bench_function(&jit_chunked_dec_label, |b| {
            b.iter(|| {
                jit_chunked_dec_provider.reset_arena();
                let mut handle = SolverKernelHandle::from_provider(&jit_chunked_dec_provider);
                black_box(handle.call(black_box(&jit_chunked_decisions)));
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_jit_vs_native,
    bench_jit_vs_native_with_decisions,
    bench_jit_watched_literal_vs_native,
    bench_jit_watched_literal_chunked_vs_native,
);
criterion_main!(benches);
