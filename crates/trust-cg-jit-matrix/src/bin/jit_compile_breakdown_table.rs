// jit_compile_breakdown_table.rs - Standalone per-phase breakdown of
// `JitBcpKernelProvider::compile`, emitted as a markdown table on stdout.
//
// Bench harness only - does not modify `jit_bcp_kernel.rs` or
// `bcp_module_builder.rs`. Replays the same compile path via the public
// `Compiler::compile_module_to_jit` API with `trace_level = Full`, sums the
// per-phase durations across `--repetitions` samples, and prints the
// breakdown.
//
// Run with `--features unsafe-unrelocated-buffer-cache-test-hooks`; the binary
// deliberately exercises quarantined same-process executable-buffer replay.
//
// Defaults reproduce the 50-variable/218-clause random-3SAT shape used by the
// `JitBcpKernelProvider::compile` 1.4-1.7 ms measurement in
// `benchmarks/benchmark_study.md`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::HashMap;
use std::process::ExitCode;
use std::time::{Duration, Instant};

use clap::Parser;

use trust_cg_codegen::Compiler;
use trust_cg_codegen::compiler::{CompilerConfig, CompilerTraceLevel, JitCompilationResult};
use trust_cg_jit_matrix::bcp_baseline::random_3sat;
use trust_cg_jit_matrix::bcp_module_builder::{BcpArena, build_bcp_propagate_module};
use trust_cg_jit_matrix::executable_buffer_cache::{
    decode_buffer_payload, publish_decoded_payload, serialize_buffer,
};
use trust_cg_jit_matrix::jit_bcp_kernel::JitBcpKernelProvider;
use trust_cg_jit_matrix::jit_compile_cache::reset_jit_compile_caches_for_tests;
use trust_cg_jit_matrix::jit_disk_cache::clear_disk_cache;

#[derive(Debug, Parser)]
#[command(
    name = "jit_compile_breakdown_table",
    about = "Emit a markdown table of per-phase JitBcpKernelProvider::compile costs"
)]
struct Args {
    #[arg(long, default_value_t = 50)]
    num_vars: usize,

    #[arg(long, default_value_t = 218)]
    num_clauses: usize,

    #[arg(long, default_value_t = 42)]
    seed: u64,

    #[arg(long, default_value_t = 30)]
    repetitions: usize,

    /// Number of warmup iterations executed before timed repetitions.
    #[arg(long, default_value_t = 3)]
    warmup: usize,
}

#[derive(Debug, Default, Clone)]
struct PhaseAccum {
    total: Duration,
    samples: usize,
}

impl PhaseAccum {
    fn record(&mut self, d: Duration) {
        self.total += d;
        self.samples += 1;
    }

    fn mean_us(&self) -> f64 {
        if self.samples == 0 {
            0.0
        } else {
            self.total.as_secs_f64() * 1e6 / self.samples as f64
        }
    }
}

fn main() -> ExitCode {
    let args = Args::parse();

    let clauses = random_3sat(args.num_vars, args.num_clauses, args.seed);

    // Warmup: pre-touch the JIT plumbing so we don't bake one-shot allocator
    // and mmap costs into the first sample.
    for _ in 0..args.warmup {
        let module = build_bcp_propagate_module();
        let mut config = CompilerConfig::for_host_jit();
        config.trace_level = CompilerTraceLevel::Full;
        let extern_symbols: HashMap<String, *const u8> = HashMap::new();
        let _ = Compiler::new(config)
            .compile_module_to_jit(&module, &extern_symbols)
            .expect("warmup compile");
    }

    // Accumulators.
    let mut module_construction = PhaseAccum::default();
    let mut compile_module_to_jit_total = PhaseAccum::default();
    let mut arena_build = PhaseAccum::default();
    let mut full_provider = PhaseAccum::default();
    let mut dialect_lower = PhaseAccum::default();
    let mut adapter = PhaseAccum::default();
    let mut prepare_function = PhaseAccum::default();
    let mut compile_raw = PhaseAccum::default();
    let mut isel = PhaseAccum::default();
    let mut optimization = PhaseAccum::default();
    let mut verification = PhaseAccum::default();
    let mut regalloc = PhaseAccum::default();
    let mut frame_lowering = PhaseAccum::default();
    let mut branch_resolution = PhaseAccum::default();
    let mut encoding = PhaseAccum::default();
    let mut unattributed = PhaseAccum::default();

    for _ in 0..args.repetitions {
        // 1. Time `build_bcp_propagate_module()` alone.
        let t = Instant::now();
        let module = build_bcp_propagate_module();
        module_construction.record(t.elapsed());

        // 2. Time `Compiler::compile_module_to_jit` and capture its trace.
        let mut config = CompilerConfig::for_host_jit();
        config.trace_level = CompilerTraceLevel::Full;
        let extern_symbols: HashMap<String, *const u8> = HashMap::new();
        let t = Instant::now();
        let result = Compiler::new(config)
            .compile_module_to_jit(&module, &extern_symbols)
            .expect("compile_module_to_jit");
        compile_module_to_jit_total.record(t.elapsed());

        // 3. Decompose the compile via the captured trace + per-function
        //    metrics.
        record_sub_phases(
            &result,
            &mut dialect_lower,
            &mut adapter,
            &mut prepare_function,
            &mut compile_raw,
            &mut isel,
            &mut optimization,
            &mut verification,
            &mut regalloc,
            &mut frame_lowering,
            &mut branch_resolution,
            &mut encoding,
            &mut unattributed,
        );

        // 4. Time `BcpArena::build` (the post-JIT work the provider performs).
        let trail_capacity = (args.num_vars + 1).max(8);
        let t = Instant::now();
        let arena = BcpArena::build(args.num_vars, &clauses, trail_capacity);
        arena_build.record(t.elapsed());

        // Keep arena alive until after we've recorded.
        std::hint::black_box(arena);
        std::hint::black_box(&result);

        // 5. Time the full provider end-to-end for cross-reference.
        let t = Instant::now();
        let provider = JitBcpKernelProvider::compile(args.num_vars, clauses.clone())
            .expect("JitBcpKernelProvider::compile");
        full_provider.record(t.elapsed());
        std::hint::black_box(provider);
    }

    let total_us = full_provider.mean_us();
    println!(
        "# JIT compile breakdown (num_vars={}, num_clauses={}, seed={}, repetitions={}, warmup={})",
        args.num_vars, args.num_clauses, args.seed, args.repetitions, args.warmup
    );
    println!();
    println!(
        "Cross-reference: `full_jit_bcp_kernel_provider_compile` mean = {:.1} us",
        total_us
    );
    println!();
    println!("## Outer phases (slices of `JitBcpKernelProvider::compile`)");
    println!();
    println!("| phase | time (us) | % of full |");
    println!("|---|---:|---:|");
    print_row(
        "module_construction",
        module_construction.mean_us(),
        total_us,
    );
    print_row(
        "compile_module_to_jit_total",
        compile_module_to_jit_total.mean_us(),
        total_us,
    );
    print_row("arena_build", arena_build.mean_us(), total_us);
    print_row(
        "full_jit_bcp_kernel_provider_compile",
        full_provider.mean_us(),
        total_us,
    );
    println!();
    println!("## Sub-phases of `compile_module_to_jit`");
    println!();
    let compile_total = compile_module_to_jit_total.mean_us();
    println!("| phase | time (us) | % of compile_module_to_jit |");
    println!("|---|---:|---:|");
    print_row("dialect_lower", dialect_lower.mean_us(), compile_total);
    print_row("adapter", adapter.mean_us(), compile_total);
    print_row(
        "prepare_function (sum across funcs)",
        prepare_function.mean_us(),
        compile_total,
    );
    print_row(
        "compile_raw (JIT encode + link)",
        compile_raw.mean_us(),
        compile_total,
    );
    println!();
    println!("### `prepare_function` sub-phases (from `PhaseTimings`, summed across funcs)");
    println!();
    let prepare_total = prepare_function.mean_us();
    println!("| phase | time (us) | % of prepare_function |");
    println!("|---|---:|---:|");
    print_row("isel", isel.mean_us(), prepare_total);
    print_row("optimization", optimization.mean_us(), prepare_total);
    print_row("verification", verification.mean_us(), prepare_total);
    print_row("regalloc", regalloc.mean_us(), prepare_total);
    print_row("frame_lowering", frame_lowering.mean_us(), prepare_total);
    print_row(
        "branch_resolution",
        branch_resolution.mean_us(),
        prepare_total,
    );
    print_row("encoding", encoding.mean_us(), prepare_total);
    // Non-zero here = time the JIT entry point measures as ONE region
    // (regalloc+frame+branch+encode). Not a phase; not rankable.
    print_row("unattributed", unattributed.mean_us(), prepare_total);

    // -----------------------------------------------------------------
    // L2 ExecutableBuffer disk-cache microbench
    // -----------------------------------------------------------------
    //
    // Compares four service paths for the same `JitBcpKernelProvider`
    // compile:
    //
    //   * cold-compile      — `JitBcpKernelProvider::compile` from
    //                         scratch, every iteration. Equivalent to
    //                         what a single-shot SAT-Comp process did
    //                         before any disk cache existed.
    //   * L3 IR-text cache  — KKK's option (a) disk cache: skips
    //                         module construction + IR encoding but
    //                         still pays ISel + regalloc + encoding.
    //   * L2 disk-cold      — first-ever read of a `.tcg-jit-buf` file
    //                         (cache miss, full compile, fsync write).
    //                         Approximates the "first run after a
    //                         cache wipe" case.
    //   * L2 disk-warm      — buffer already on disk: file read +
    //                         decode + mmap + mprotect; no compile.
    //                         This is the target single-shot path.
    //   * in-memory warm    — Arc clone out of the thread-local LRU;
    //                         the cheapest path we publish.
    //
    // Numbers are reported in microseconds with one decimal place so
    // a reader can read off the wall-clock ratio between tiers
    // directly.
    println!();
    println!("## JIT compile cache: L2 disk-cold vs L2 disk-warm (ExecutableBuffer)");
    println!();

    // Use a per-process tempdir as the cache root for both tiers so
    // this microbench cannot disturb the developer's real
    // `~/.cache/trust-cg/`. `tempfile` is a dev-dep only, so we
    // construct the directory directly under `std::env::temp_dir()`.
    let pid = std::process::id();
    let ts = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let bench_tmp = std::env::temp_dir().join(format!("trust-cg-jit-buf-bench-{pid}-{ts}"));
    std::fs::create_dir_all(&bench_tmp).expect("microbench tempdir");
    trust_cg_jit_matrix::jit_disk_cache::set_disk_cache_root_for_tests(Some(bench_tmp.clone()));
    // SAFETY: the unique tempdir is owned for this process only; this benchmark
    // uses an empty extern map and keeps profiling instrumentation disabled.
    unsafe {
        trust_cg_jit_matrix::executable_buffer_cache::set_buffer_cache_root_for_tests(Some(
            bench_tmp.clone(),
        ));
    }

    let l2_module = build_bcp_propagate_module();
    let l2_config = CompilerConfig::for_host_jit();
    let l2_externs: HashMap<String, *const u8> = HashMap::new();
    // Pre-compute a serialized buffer for the L2-warm path so each
    // iteration measures only the disk + decode + mmap cost.
    let warm_buffer = Compiler::new(l2_config.clone())
        .compile_module_to_jit(&l2_module, &l2_externs)
        .expect("warmup compile")
        .buffer;
    let warm_bytes = serialize_buffer(&warm_buffer);
    drop(warm_buffer); // free the live mapping; we replay from bytes

    let mut cold_compile = PhaseAccum::default();
    let mut l3_ir_text = PhaseAccum::default();
    let mut l2_disk_cold = PhaseAccum::default();
    let mut l2_disk_warm = PhaseAccum::default();
    let mut in_mem_warm = PhaseAccum::default();

    // The root override installed above already enables disk I/O for this
    // microbenchmark; no process-environment mutation is needed.

    for _ in 0..args.repetitions {
        // 1. cold-compile (no cache at all)
        reset_jit_compile_caches_for_tests();
        clear_disk_cache();
        trust_cg_jit_matrix::executable_buffer_cache::clear_buffer_cache();
        let t = Instant::now();
        let provider =
            JitBcpKernelProvider::compile(args.num_vars, clauses.clone()).expect("cold compile");
        cold_compile.record(t.elapsed());
        std::hint::black_box(&provider);

        // 2. L3 IR-text disk-warm: prime IR text on disk, clear L2
        //    and in-memory, then re-enter the cached pathway. The
        //    closure skips `build_bcp_propagate_module()` but still
        //    runs ISel + regalloc + encoding.
        reset_jit_compile_caches_for_tests();
        clear_disk_cache();
        trust_cg_jit_matrix::executable_buffer_cache::clear_buffer_cache();
        // Prime L3 only: invoke `compile_or_get_cached` once so the IR
        // text lands on disk, then clear in-memory + L2 again.
        let _ = JitBcpKernelProvider::compile_or_get_cached(args.num_vars, clauses.clone())
            .expect("prime l3");
        reset_jit_compile_caches_for_tests();
        trust_cg_jit_matrix::executable_buffer_cache::clear_buffer_cache();
        let t = Instant::now();
        let provider = JitBcpKernelProvider::compile_or_get_cached(args.num_vars, clauses.clone())
            .expect("L3 hit");
        l3_ir_text.record(t.elapsed());
        std::hint::black_box(provider);

        // 3. L2 disk-cold: cache wipe + full compile populates L2 +
        //    L3 in passing. Measures "first run after a cache wipe".
        reset_jit_compile_caches_for_tests();
        clear_disk_cache();
        trust_cg_jit_matrix::executable_buffer_cache::clear_buffer_cache();
        let t = Instant::now();
        let provider = JitBcpKernelProvider::compile_or_get_cached(args.num_vars, clauses.clone())
            .expect("L2 cold (writes L2+L3)");
        l2_disk_cold.record(t.elapsed());
        std::hint::black_box(provider);

        // 4. L2 disk-warm: L2 already populated by step (3). Clear
        //    in-memory, leave disk intact, and re-enter the cached
        //    pathway: file read + decode + mmap + mprotect, no
        //    compile.
        reset_jit_compile_caches_for_tests();
        let t = Instant::now();
        let provider = JitBcpKernelProvider::compile_or_get_cached(args.num_vars, clauses.clone())
            .expect("L2 warm");
        l2_disk_warm.record(t.elapsed());
        std::hint::black_box(provider);

        // 5. in-memory warm: same cache, second invocation.
        let t = Instant::now();
        let arc = JitBcpKernelProvider::compile_or_get_cached(args.num_vars, clauses.clone())
            .expect("L1 warm");
        in_mem_warm.record(t.elapsed());
        std::hint::black_box(arc);
    }

    // Reference: pure decode-and-mmap from in-memory bytes (no file
    // I/O, no SHA recompute beyond the deserializer's own check).
    // This isolates the kernel mmap+memcpy+mprotect cost from the
    // disk-read latency for diagnostic interest.
    let mut bytes_replay = PhaseAccum::default();
    for _ in 0..args.repetitions {
        let t = Instant::now();
        let payload = decode_buffer_payload(&warm_bytes).expect("decode");
        let replayed = publish_decoded_payload(payload).expect("publish");
        bytes_replay.record(t.elapsed());
        std::hint::black_box(replayed);
    }

    println!("| tier | time (us) |");
    println!("|---|---:|");
    println!(
        "| cold-compile (no cache) | {:.1} |",
        cold_compile.mean_us()
    );
    println!("| L3 disk-warm (IR text)  | {:.1} |", l3_ir_text.mean_us());
    println!(
        "| L2 disk-cold (full compile + write) | {:.1} |",
        l2_disk_cold.mean_us()
    );
    println!(
        "| L2 disk-warm (.tcg-jit-buf) | {:.1} |",
        l2_disk_warm.mean_us()
    );
    println!(
        "| in-memory warm (Arc clone) | {:.1} |",
        in_mem_warm.mean_us()
    );
    println!(
        "| (reference) bytes-only replay | {:.1} |",
        bytes_replay.mean_us()
    );
    println!();
    let cold_us = cold_compile.mean_us();
    let warm_us = l2_disk_warm.mean_us();
    let l3_us = l3_ir_text.mean_us();
    let speedup = if warm_us > 0.0 {
        cold_us / warm_us
    } else {
        0.0
    };
    let l3_vs_l2 = if warm_us > 0.0 { l3_us / warm_us } else { 0.0 };
    println!(
        "L2 disk-warm speedup over cold compile: {speedup:.1}x ({cold_us:.1} us -> {warm_us:.1} us)"
    );
    println!(
        "L2 disk-warm speedup over L3 IR-text:   {l3_vs_l2:.1}x ({l3_us:.1} us -> {warm_us:.1} us)"
    );

    // Restore the override slots so a subsequent process invocation
    // does not see this run's tempdir leak in.
    trust_cg_jit_matrix::jit_disk_cache::set_disk_cache_root_for_tests(None);
    // SAFETY: clearing the process-private override cannot expose a replay.
    unsafe {
        trust_cg_jit_matrix::executable_buffer_cache::set_buffer_cache_root_for_tests(None);
    }
    let _ = std::fs::remove_dir_all(&bench_tmp);

    ExitCode::SUCCESS
}

fn print_row(name: &str, us: f64, denom_us: f64) {
    let pct = if denom_us > 0.0 {
        us / denom_us * 100.0
    } else {
        0.0
    };
    println!("| {} | {:.1} | {:.1} |", name, us, pct);
}

#[allow(clippy::too_many_arguments)]
fn record_sub_phases(
    result: &JitCompilationResult,
    dialect_lower: &mut PhaseAccum,
    adapter: &mut PhaseAccum,
    prepare_function: &mut PhaseAccum,
    compile_raw: &mut PhaseAccum,
    isel: &mut PhaseAccum,
    optimization: &mut PhaseAccum,
    verification: &mut PhaseAccum,
    regalloc: &mut PhaseAccum,
    frame_lowering: &mut PhaseAccum,
    branch_resolution: &mut PhaseAccum,
    encoding: &mut PhaseAccum,
    unattributed: &mut PhaseAccum,
) {
    if let Some(trace) = result.trace.as_ref() {
        let mut dl = Duration::ZERO;
        let mut ad = Duration::ZERO;
        let mut pf = Duration::ZERO;
        let mut cr = Duration::ZERO;
        for entry in &trace.entries {
            match entry.phase.as_str() {
                "dialect_lower" => dl += entry.duration,
                "adapter" => ad += entry.duration,
                "prepare_function" => pf += entry.duration,
                "compile_raw" => cr += entry.duration,
                _ => {}
            }
        }
        dialect_lower.record(dl);
        adapter.record(ad);
        prepare_function.record(pf);
        compile_raw.record(cr);
    } else {
        // Shouldn't happen with trace_level = Full, but guard anyway.
        dialect_lower.record(Duration::ZERO);
        adapter.record(Duration::ZERO);
        prepare_function.record(Duration::ZERO);
        compile_raw.record(Duration::ZERO);
    }

    let mut isel_sum = Duration::ZERO;
    let mut opt_sum = Duration::ZERO;
    let mut ver_sum = Duration::ZERO;
    let mut reg_sum = Duration::ZERO;
    let mut fl_sum = Duration::ZERO;
    let mut br_sum = Duration::ZERO;
    let mut enc_sum = Duration::ZERO;
    let mut unattr_sum = Duration::ZERO;
    for m in &result.per_function_metrics {
        isel_sum += m.phase_timings.isel.unwrap_or(Duration::ZERO);
        opt_sum += m.phase_timings.optimization.unwrap_or(Duration::ZERO);
        ver_sum += m.phase_timings.verification.unwrap_or(Duration::ZERO);
        reg_sum += m.phase_timings.regalloc.unwrap_or(Duration::ZERO);
        fl_sum += m.phase_timings.frame_lowering.unwrap_or(Duration::ZERO);
        br_sum += m.phase_timings.branch_resolution.unwrap_or(Duration::ZERO);
        enc_sum += m.phase_timings.encoding.unwrap_or(Duration::ZERO);
        unattr_sum += m.phase_timings.unattributed.unwrap_or(Duration::ZERO);
    }
    isel.record(isel_sum);
    optimization.record(opt_sum);
    verification.record(ver_sum);
    regalloc.record(reg_sum);
    frame_lowering.record(fl_sum);
    branch_resolution.record(br_sum);
    encoding.record(enc_sum);
    unattributed.record(unattr_sum);
}
