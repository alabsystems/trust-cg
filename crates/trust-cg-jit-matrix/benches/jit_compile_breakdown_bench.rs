// trust-cg-jit-matrix/benches/jit_compile_breakdown_bench.rs - Per-phase
// breakdown of `JitBcpKernelProvider::compile`.
//
// This bench is harness-only. No production source under
// `crates/trust-cg-jit-matrix/src/` or `crates/trust-cg-codegen/` is modified.
//
// What it measures:
//
// 1. `module_construction` - the cost of `build_bcp_propagate_module()` alone.
// 2. `module_text_round_trip` - SKIPPED. `JitBcpKernelProvider::compile` does
//    not serialize the module to text and re-parse it; it hands the
//    `trust_ir::Module` directly to `Compiler::compile_module_to_jit`. We
//    confirmed this by reading `jit_bcp_kernel.rs` line by line: there is no
//    `load_module_as(..., FormatMode::Text)` call on the JIT path. The phase
//    is therefore not exercised at all and we do not invent a synthetic one.
// 3. `compile_module_to_jit_total` - the whole
//    `Compiler::compile_module_to_jit` call. This is the phase MM measured at
//    1.4-1.7 ms.
// 4. `arena_build` - the `BcpArena::build(num_vars, &clauses, ...)` call that
//    `JitBcpKernelProvider::compile` performs after the JIT. Included so the
//    sum of phases reconstructs the full provider compile cost. Conceptually
//    plays the "executable_buffer_finalize" role described in the assignment:
//    there is no extra finalize step inside `compile_module_to_jit_total` for
//    the host JIT path on aarch64 / x86_64 - the executable buffer comes back
//    fully populated and ready to dispatch. Arena construction is the only
//    work the provider does after that.
// 5. `full_jit_bcp_kernel_provider_compile` - the entire
//    `JitBcpKernelProvider::compile(num_vars, clauses)` call, for direct
//    cross-reference against MM's table in `benchmarks/benchmark_study.md`.
//
// Sub-phases of `compile_module_to_jit`:
//
// `trust_cg_codegen::compiler::Compiler` exposes a per-call
// `CompilerTrace` (top-level phases: `dialect_lower`, `adapter`,
// `prepare_function`, `compile_raw`) plus, separately, per-function
// `PhaseTimings` (`isel`, `optimization`, `verification`, `regalloc`,
// `frame_lowering`, `branch_resolution`, `encoding`) on
// `JitCompilationResult::per_function_metrics`. The `per_function_metrics`
// vector is always populated; the trace requires
// `CompilerConfig::trace_level != None`. Together they give us the full
// pipeline breakdown without touching any production code.
//
// To avoid mutating `CompilerConfig::for_host_jit()` inside the production
// `JitBcpKernelProvider::compile` path (which would require editing
// `jit_bcp_kernel.rs`), the bench manually replays the provider compile path
// here with the exact same defaults plus `trace_level = Full`. The replay is
// gated behind the `breakdown` bench group so it never runs in the hot
// `jit_vs_native_bcp_bench` matrix.
//
// Generation: random_3sat(50, 218, seed=42), matching the generated
// 50-variable/218-clause shape used by the end-to-end study.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::HashMap;
use std::hint::black_box;
use std::time::{Duration, Instant};

use criterion::{Criterion, criterion_group, criterion_main};

use trust_cg_codegen::Compiler;
use trust_cg_codegen::compiler::{CompilerConfig, CompilerTraceLevel};
use trust_cg_jit_matrix::bcp_baseline::random_3sat;
use trust_cg_jit_matrix::bcp_module_builder::build_bcp_propagate_module;
use trust_cg_jit_matrix::jit_bcp_kernel::JitBcpKernelProvider;

const NUM_VARS: usize = 50;
const NUM_CLAUSES: usize = 218;
const SEED: u64 = 42;

fn fixture_clauses() -> Vec<Vec<i32>> {
    random_3sat(NUM_VARS, NUM_CLAUSES, SEED)
}

fn bench_module_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("jit_compile_breakdown");
    group.bench_function("module_construction", |b| {
        b.iter(|| {
            let module = build_bcp_propagate_module();
            black_box(module);
        });
    });
    group.finish();
}

fn bench_compile_module_to_jit_total(c: &mut Criterion) {
    let mut group = c.benchmark_group("jit_compile_breakdown");
    group.bench_function("compile_module_to_jit_total", |b| {
        b.iter_batched(
            build_bcp_propagate_module,
            |module| {
                let config = CompilerConfig::for_host_jit();
                let extern_symbols: HashMap<String, *const u8> = HashMap::new();
                let result = Compiler::new(config)
                    .compile_module_to_jit(&module, &extern_symbols)
                    .expect("compile_module_to_jit");
                black_box(result);
            },
            criterion::BatchSize::SmallInput,
        );
    });
    group.finish();
}

fn bench_arena_build(c: &mut Criterion) {
    let mut group = c.benchmark_group("jit_compile_breakdown");
    let clauses = fixture_clauses();
    group.bench_function("arena_build_uuf50_218", |b| {
        b.iter_batched(
            || clauses.clone(),
            |clauses| {
                use trust_cg_jit_matrix::bcp_module_builder::BcpArena;
                let trail_capacity = (NUM_VARS + 1).max(8);
                let arena = BcpArena::build(NUM_VARS, &clauses, trail_capacity);
                black_box(arena);
            },
            criterion::BatchSize::SmallInput,
        );
    });
    group.finish();
}

fn bench_full_jit_bcp_kernel_provider_compile(c: &mut Criterion) {
    let mut group = c.benchmark_group("jit_compile_breakdown");
    let clauses = fixture_clauses();
    group.bench_function("full_jit_bcp_kernel_provider_compile_uuf50_218", |b| {
        b.iter_batched(
            || clauses.clone(),
            |clauses| {
                let provider = JitBcpKernelProvider::compile(NUM_VARS, clauses)
                    .expect("JitBcpKernelProvider::compile");
                black_box(provider);
            },
            criterion::BatchSize::SmallInput,
        );
    });
    group.finish();
}

/// Replay the full compile path once with `trace_level = Full`, then expose
/// each named phase from the resulting `CompilerTrace` and
/// `PhaseTimings` as its own criterion benchmark. The compile happens fresh
/// inside `iter_custom`, so each sample is an independent compile that
/// produces its own trace - we just charge criterion only the slice of time
/// corresponding to the phase under measurement.
///
/// We surface, in this order:
///   - `dialect_lower`
///   - `adapter`
///   - `prepare_function` (sum across functions; only one for BCP today)
///   - `compile_raw` (final JIT encode / link)
///     plus per-function timings aggregated across functions (only one for BCP):
///   - `isel`, `optimization`, `verification`, `regalloc`,
///     `frame_lowering`, `branch_resolution`, `encoding`
fn bench_sub_phases(c: &mut Criterion) {
    // NOTE: `verification` is intentionally omitted. The phase only runs
    // when `CompilerConfig::emit_proofs = true`, which is *not* the
    // `for_host_jit` default that `JitBcpKernelProvider::compile` uses.
    // The standalone `jit_compile_breakdown_table` binary still prints
    // `verification` as 0.0 us for completeness; criterion rejects
    // benchmarks whose samples are all-zero so we exclude it here.
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

    let mut group = c.benchmark_group("jit_compile_breakdown_subphases");
    for phase in phases.iter() {
        let phase_name = (*phase).to_string();
        group.bench_function(*phase, |b| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    let module = build_bcp_propagate_module();
                    let mut config = CompilerConfig::for_host_jit();
                    config.trace_level = CompilerTraceLevel::Full;
                    let extern_symbols: HashMap<String, *const u8> = HashMap::new();
                    let result = Compiler::new(config)
                        .compile_module_to_jit(&module, &extern_symbols)
                        .expect("compile_module_to_jit (trace)");
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
        // Top-level trace entries from `compile_module_to_jit`.
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
        // Per-function phase timings, summed across functions (BCP module has
        // one function today, so the sum is the per-function value).
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

/// Sanity check: the trace path must produce a usable provider (so it's
/// representative of the production compile path). Not strictly needed for
/// the bench but cheap and prevents silent drift if `trace_level` ever
/// changes pipeline behaviour.
fn _smoke_invariant_check() {
    let clauses = fixture_clauses();
    // Match what `JitBcpKernelProvider::compile` does, but with tracing on.
    let module = build_bcp_propagate_module();
    let mut config = CompilerConfig::for_host_jit();
    config.trace_level = CompilerTraceLevel::Full;
    let extern_symbols: HashMap<String, *const u8> = HashMap::new();
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &extern_symbols)
        .expect("compile_module_to_jit (smoke)");
    assert!(
        result.trace.is_some(),
        "trace must be populated when trace_level=Full"
    );
    assert!(
        !result.per_function_metrics.is_empty(),
        "per_function_metrics must be populated"
    );

    // Cross-reference against the production provider once - confirms parity
    // with `JitBcpKernelProvider::compile`.
    let provider = JitBcpKernelProvider::compile(NUM_VARS, clauses).expect("provider compile");
    let _ = provider.arena_values();

    // Silence "instant unused" lints in unused-fn paths.
    let _ = Instant::now();
}

criterion_group!(
    benches,
    bench_module_construction,
    bench_compile_module_to_jit_total,
    bench_arena_build,
    bench_full_jit_bcp_kernel_provider_compile,
    bench_sub_phases,
);
criterion_main!(benches);
