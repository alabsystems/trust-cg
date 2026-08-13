// trust-cg-jit-matrix/benches/parent_loop_compile_breakdown_bench.rs -
// Per-phase compile-cost breakdown for the parent-loop JIT provider,
// mirroring `jit_compile_breakdown_bench.rs` (BCP) so the
// post-JitFast cold-compile speedup can be compared head-to-head.
//
// What this measures:
//
// 1. `module_construction` - `build_parent_loop_module()` alone.
// 2. `compile_module_to_jit_total_jit_fast` - whole
//    `Compiler::compile_module_to_jit` with the production
//    `CompilerConfig::for_host_jit()` (JitFast regalloc enabled).
// 3. `compile_module_to_jit_total_baseline` - same call but with
//    `enable_jit_fast_regalloc = false`, so the ratio against (2) is
//    the parent-loop analogue of C2's 2.78x full-compile speedup on
//    BCP. Both shapes use the host JIT target; only the regalloc
//    strategy differs.
// 4. `arena_build` - `ParentLoopArena::build` for the medium fixture.
// 5. `full_jit_parent_loop_kernel_provider_compile` - end-to-end
//    `JitParentLoopKernelProvider::compile` for cross-reference
//    against the BCP `full_jit_bcp_kernel_provider_compile` figure.
// 6. Per-phase trace (dialect_lower, adapter, prepare_function,
//    compile_raw, isel, optimization, regalloc, frame_lowering,
//    branch_resolution, encoding) on the production JitFast config -
//    same surface as the BCP breakdown bench so the regalloc share of
//    compile is directly readable.
//
// Bench is harness-only; no production source is modified. The
// parent-loop trust-ir module is a single function and does not
// depend on the transition system size, so we use the medium fixture
// (16v/64a, seed 0xB0B) for the compile path - the compile cost is a
// function of the module shape, not the workload.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use std::collections::HashMap;
use std::hint::black_box;
use std::time::Duration;

use criterion::{Criterion, criterion_group, criterion_main};

use trust_cg_codegen::Compiler;
use trust_cg_codegen::compiler::{CompilerConfig, CompilerTraceLevel};
use trust_cg_jit_matrix::jit_parent_loop_kernel::JitParentLoopKernelProvider;
use trust_cg_jit_matrix::parent_loop_baseline::random_transition_system;
use trust_cg_jit_matrix::parent_loop_module_builder::{ParentLoopArena, build_parent_loop_module};

const NUM_VARS: u32 = 16;
const NUM_ACTIONS: usize = 64;
const SEED: u64 = 0xB0B;
const FRONTIER_CAP: usize = 64 * 1024;

fn fixture_system() -> trust_cg_jit_matrix::parent_loop_baseline::TransitionSystem {
    random_transition_system(NUM_VARS, NUM_ACTIONS, SEED)
}

fn bench_module_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("parent_loop_compile_breakdown");
    group.bench_function("module_construction", |b| {
        b.iter(|| {
            let module = build_parent_loop_module();
            black_box(module);
        });
    });
    group.finish();
}

fn bench_compile_module_to_jit_total_jit_fast(c: &mut Criterion) {
    let mut group = c.benchmark_group("parent_loop_compile_breakdown");
    group.bench_function("compile_module_to_jit_total_jit_fast", |b| {
        b.iter_batched(
            build_parent_loop_module,
            |module| {
                let config = CompilerConfig::for_host_jit();
                assert!(config.enable_jit_fast_regalloc);
                let extern_symbols: HashMap<String, *const u8> = HashMap::new();
                let result = Compiler::new(config)
                    .compile_module_to_jit(&module, &extern_symbols)
                    .expect("compile_module_to_jit (jit_fast)");
                black_box(result);
            },
            criterion::BatchSize::SmallInput,
        );
    });
    group.finish();
}

fn bench_compile_module_to_jit_total_baseline(c: &mut Criterion) {
    let mut group = c.benchmark_group("parent_loop_compile_breakdown");
    group.bench_function("compile_module_to_jit_total_baseline_no_jit_fast", |b| {
        b.iter_batched(
            build_parent_loop_module,
            |module| {
                let mut config = CompilerConfig::for_host_jit();
                config.enable_jit_fast_regalloc = false;
                let extern_symbols: HashMap<String, *const u8> = HashMap::new();
                let result = Compiler::new(config)
                    .compile_module_to_jit(&module, &extern_symbols)
                    .expect("compile_module_to_jit (no_jit_fast)");
                black_box(result);
            },
            criterion::BatchSize::SmallInput,
        );
    });
    group.finish();
}

fn bench_arena_build(c: &mut Criterion) {
    let mut group = c.benchmark_group("parent_loop_compile_breakdown");
    let system = fixture_system();
    group.bench_function("arena_build_medium_16v_64a", |b| {
        b.iter_batched(
            || system.clone(),
            |system| {
                let arena = ParentLoopArena::build(NUM_VARS, &system, FRONTIER_CAP);
                black_box(arena);
            },
            criterion::BatchSize::SmallInput,
        );
    });
    group.finish();
}

fn bench_full_jit_parent_loop_kernel_provider_compile(c: &mut Criterion) {
    let mut group = c.benchmark_group("parent_loop_compile_breakdown");
    let system = fixture_system();
    group.bench_function(
        "full_jit_parent_loop_kernel_provider_compile_medium_16v_64a",
        |b| {
            b.iter_batched(
                || system.clone(),
                |system| {
                    let provider =
                        JitParentLoopKernelProvider::compile(NUM_VARS, system, FRONTIER_CAP)
                            .expect("JitParentLoopKernelProvider::compile");
                    black_box(provider);
                },
                criterion::BatchSize::SmallInput,
            );
        },
    );
    group.finish();
}

/// Per-phase trace using `CompilerConfig::for_host_jit()` (JitFast on),
/// matching what `JitParentLoopKernelProvider::compile` actually runs.
fn bench_sub_phases_jit_fast(c: &mut Criterion) {
    // Same set the BCP breakdown bench surfaces, minus `verification`
    // (gated on emit_proofs which `for_host_jit` leaves off).
    let phases = [
        "dialect_lower",
        "adapter",
        "prepare_function",
        "compile_raw",
        "isel",
        "optimization",
        "regalloc",
        "frame_lowering",
        "branch_resolution",
        "encoding",
    ];

    let mut group = c.benchmark_group("parent_loop_compile_breakdown_subphases_jit_fast");
    for phase in phases.iter() {
        let phase_name = (*phase).to_string();
        group.bench_function(*phase, |b| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    let module = build_parent_loop_module();
                    let mut config = CompilerConfig::for_host_jit();
                    config.trace_level = CompilerTraceLevel::Full;
                    let extern_symbols: HashMap<String, *const u8> = HashMap::new();
                    let result = Compiler::new(config)
                        .compile_module_to_jit(&module, &extern_symbols)
                        .expect("compile_module_to_jit (trace, jit_fast)");
                    total += extract_phase(&result, &phase_name);
                    black_box(&result);
                }
                total
            });
        });
    }
    group.finish();
}

/// Companion per-phase trace with JitFast turned off, so the regalloc
/// row drop between the two groups is the parent-loop analogue of
/// C2's reported 5.11x regalloc speedup on BCP.
fn bench_sub_phases_baseline(c: &mut Criterion) {
    let phases = [
        "dialect_lower",
        "adapter",
        "prepare_function",
        "compile_raw",
        "isel",
        "optimization",
        "regalloc",
        "frame_lowering",
        "branch_resolution",
        "encoding",
    ];

    let mut group =
        c.benchmark_group("parent_loop_compile_breakdown_subphases_baseline_no_jit_fast");
    for phase in phases.iter() {
        let phase_name = (*phase).to_string();
        group.bench_function(*phase, |b| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    let module = build_parent_loop_module();
                    let mut config = CompilerConfig::for_host_jit();
                    config.enable_jit_fast_regalloc = false;
                    config.trace_level = CompilerTraceLevel::Full;
                    let extern_symbols: HashMap<String, *const u8> = HashMap::new();
                    let result = Compiler::new(config)
                        .compile_module_to_jit(&module, &extern_symbols)
                        .expect("compile_module_to_jit (trace, no_jit_fast)");
                    total += extract_phase(&result, &phase_name);
                    black_box(&result);
                }
                total
            });
        });
    }
    group.finish();
}

fn extract_phase(
    result: &trust_cg_codegen::compiler::JitCompilationResult,
    phase: &str,
) -> Duration {
    match phase {
        "dialect_lower" | "adapter" | "prepare_function" | "compile_raw" => result
            .trace
            .as_ref()
            .map(|t| {
                t.entries
                    .iter()
                    .filter(|e| e.phase == phase)
                    .map(|e| e.duration)
                    .sum()
            })
            .unwrap_or(Duration::ZERO),
        other => result
            .per_function_metrics
            .iter()
            .map(|m| match other {
                "isel" => m.phase_timings.isel.unwrap_or(Duration::ZERO),
                "optimization" => m.phase_timings.optimization.unwrap_or(Duration::ZERO),
                "verification" => m.phase_timings.verification.unwrap_or(Duration::ZERO),
                "regalloc" => m.phase_timings.regalloc.unwrap_or(Duration::ZERO),
                "frame_lowering" => m.phase_timings.frame_lowering.unwrap_or(Duration::ZERO),
                "branch_resolution" => m.phase_timings.branch_resolution.unwrap_or(Duration::ZERO),
                "encoding" => m.phase_timings.encoding.unwrap_or(Duration::ZERO),
                "unattributed" => m.phase_timings.unattributed.unwrap_or(Duration::ZERO),
                _ => Duration::ZERO,
            })
            .sum(),
    }
}

criterion_group!(
    benches,
    bench_module_construction,
    bench_compile_module_to_jit_total_jit_fast,
    bench_compile_module_to_jit_total_baseline,
    bench_arena_build,
    bench_full_jit_parent_loop_kernel_provider_compile,
    bench_sub_phases_jit_fast,
    bench_sub_phases_baseline,
);
criterion_main!(benches);
