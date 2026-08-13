// trust-cg-sat-host/src/bin/satlib_bench_table.rs - Standalone CLI
// that wall-clocks MicroSAT-native-only vs MicroSAT-with-JIT-shadow on
// every fixture in `tests/fixtures/sat_corpus/` and prints a markdown
// table to stdout, plus a stderr-side summary that buckets fixtures
// by native solve-time tier and reports whether each fixture shows
// per-call JIT amortization. A fixture "amortizes" when the
// jit-shadow path's overhead is below the native solve time on that
// instance - that is, the JIT bookkeeping has already paid for
// itself on a single call. Anything where native solve is under
// ~100 us is flagged "too-easy-for-jit" because the compile cost
// (~1.5 ms today) cannot be amortized by per-call speedup on such
// short solves regardless of how fast the JIT path runs.
//
// This is not a criterion bench - it is a quick-look summary intended
// to be pasted into `benchmarks/benchmark_study.md`. The criterion bench
// (`benches/satlib_jit_shadow_bench.rs`) provides the proper
// statistical numbers; this binary just turns those numbers into a
// human-skimmable row-per-fixture table on demand.
//
// Usage:
//
//   cargo run -p trust-cg-sat-host --bin satlib_bench_table --release
//   cargo run -p trust-cg-sat-host --bin satlib_bench_table --release -- \
//       --repetitions 10 --warmup
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The executable's legacy `satlib_` name is retained for compatibility. The
// current fixture corpus is generated entirely by this project and contains no
// SATLIB or AIM instance bytes.

use std::error::Error;
use std::ffi::CString;
use std::fmt;
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};

use trust_cg_jit_matrix::dimacs::read_dimacs_cnf_file;
use trust_cg_jit_matrix::jit_bcp_kernel::JitBcpWatchedLiteralKernelProvider;
use trust_cg_jit_matrix::jit_compile_cache::{
    clear_disk_cache, reset_jit_compile_caches_for_tests,
};
use trust_cg_sat_host::propagate::{
    JIT_ANALYZE_DRIVER_FORCE, JIT_DIVERGENCE_COUNT, JIT_INIT_COUNT, JIT_KERNEL_CHOICE,
    JIT_KERNEL_WATCHED_LITERAL, JIT_PRIMARY_RETURNS, PRIMARY_JIT_MODE, PROPAGATE_CALL_COUNT,
    SHADOW_MODE, reset_jit_shadow_for_tests,
};
use trust_cg_sat_host::sys;

/// Name of the JIT kernel this binary times. Pinned to
/// `watched-literal` because that is the default `JIT_KERNEL_CHOICE`
/// since the headline switchover; the table header surfaces it so
/// readers know which kernel produced the `jit-shadow (ms)` and
/// `jit-compile-once (ms)` columns.
const JIT_KERNEL_NAME: &str = "watched-literal";

type AnyError = Box<dyn Error + Send + Sync + 'static>;

#[derive(Debug)]
struct BenchError(String);

impl fmt::Display for BenchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl Error for BenchError {}

fn bench_err<S: Into<String>>(msg: S) -> AnyError {
    Box::new(BenchError(msg.into()))
}

struct CliArgs {
    repetitions: usize,
    warmup: bool,
}

fn parse_args() -> Result<CliArgs, AnyError> {
    let mut repetitions: usize = 5;
    let mut warmup = false;
    let mut iter = std::env::args().skip(1);
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--repetitions" => {
                let val = iter
                    .next()
                    .ok_or_else(|| bench_err("--repetitions requires a positive integer"))?;
                repetitions = val
                    .parse::<usize>()
                    .map_err(|err| bench_err(format!("--repetitions {val:?}: {err}")))?;
                if repetitions == 0 {
                    return Err(bench_err("--repetitions must be at least 1"));
                }
            }
            "--warmup" => warmup = true,
            "--help" | "-h" => {
                println!(
                    "satlib_bench_table - wall-clock project-authored corpus under native vs JIT shadow"
                );
                println!();
                println!("Options:");
                println!("  --repetitions N   number of timed runs per fixture (default 5)");
                println!("  --warmup          run one untimed solve per fixture before timing");
                std::process::exit(0);
            }
            other => {
                return Err(bench_err(format!("unknown argument {other:?}")));
            }
        }
    }
    Ok(CliArgs {
        repetitions,
        warmup,
    })
}

fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("sat_corpus")
}

fn corpus_fixtures() -> Result<Vec<(String, PathBuf)>, AnyError> {
    let dir = corpus_dir();
    let read = std::fs::read_dir(&dir)
        .map_err(|err| bench_err(format!("read corpus dir {}: {err}", dir.display())))?;
    let mut entries: Vec<(String, PathBuf)> = Vec::new();
    for entry in read {
        let entry =
            entry.map_err(|err| bench_err(format!("walk corpus dir {}: {err}", dir.display())))?;
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("cnf") {
            continue;
        }
        let stem = match path.file_stem().and_then(|s| s.to_str()) {
            Some(s) => s.to_owned(),
            None => continue,
        };
        entries.push((stem, path));
    }
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(entries)
}

fn solve_path(cnf_path: &Path) -> Result<i32, AnyError> {
    let path_str = cnf_path.to_string_lossy().into_owned();
    let c_path =
        CString::new(path_str).map_err(|err| bench_err(format!("cnf path contains NUL: {err}")))?;
    let mut solver: MaybeUninit<sys::solver> = MaybeUninit::uninit();
    // SAFETY: matches the upstream MicroSAT `main` pattern (see
    // `sys::parse` + `sys::solve` docs). `parse` runs `initCDCL` and
    // fully populates the solver before any read happens.
    let rc = unsafe {
        let parse_rc = sys::parse(
            solver.as_mut_ptr(),
            c_path.as_ptr() as *mut std::os::raw::c_char,
        );
        if parse_rc == sys::UNSAT {
            sys::UNSAT
        } else {
            sys::solve(solver.as_mut_ptr())
        }
    };
    Ok(rc)
}

fn mean_ms(samples: &[Duration]) -> f64 {
    if samples.is_empty() {
        return f64::NAN;
    }
    let total: f64 = samples.iter().map(|d| d.as_secs_f64() * 1000.0).sum();
    total / samples.len() as f64
}

fn measure_native(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<(Vec<Duration>, i32), AnyError> {
    SHADOW_MODE.store(false, Ordering::SeqCst);
    let mut last_rc = 0;
    if warmup {
        last_rc = solve_path(path)?;
    }
    let mut samples = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        let t0 = Instant::now();
        last_rc = solve_path(path)?;
        samples.push(t0.elapsed());
    }
    Ok((samples, last_rc))
}

fn measure_jit_shadow(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<(Vec<Duration>, i32, u64), AnyError> {
    let divergences_before = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
    let mut last_rc = 0;
    if warmup {
        reset_jit_shadow_for_tests();
        SHADOW_MODE.store(true, Ordering::SeqCst);
        last_rc = solve_path(path)?;
        SHADOW_MODE.store(false, Ordering::SeqCst);
    }
    let mut samples = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        reset_jit_shadow_for_tests();
        SHADOW_MODE.store(true, Ordering::SeqCst);
        let t0 = Instant::now();
        last_rc = solve_path(path)?;
        let elapsed = t0.elapsed();
        SHADOW_MODE.store(false, Ordering::SeqCst);
        samples.push(elapsed);
    }
    let divergences_after = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
    Ok((samples, last_rc, divergences_after - divergences_before))
}

/// Wall-clock PRIMARY_JIT_MODE solve where each repetition pays the
/// JIT compile cost from scratch — the thread-local
/// `JIT_BCP_*_CACHE` is cleared before every iteration so
/// `compile_or_get_cached` always misses. This is the
/// "primary-jit-cold" column; it reflects what a single-shot
/// SAT-Comp invocation would observe (cold cache on every solve).
fn measure_primary_jit_cold(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<(Vec<Duration>, i32), AnyError> {
    let mut last_rc = 0;
    if warmup {
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        last_rc = solve_path(path)?;
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
    }
    let mut samples = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        // Cold path: drop every cached buffer before the solve so
        // the next `compile_or_get_cached` call has to re-JIT from
        // scratch. `reset_jit_shadow_for_tests` clears the per-solve
        // JitProviderCache so the freshly-compiled provider is the
        // one this repetition observes.
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        let t0 = Instant::now();
        last_rc = solve_path(path)?;
        let elapsed = t0.elapsed();
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
        samples.push(elapsed);
    }
    Ok((samples, last_rc))
}

/// Wall-clock PRIMARY_JIT_MODE solve where the thread-local JIT
/// compile cache is pre-populated once and then reused across
/// repetitions. The first (untimed) priming solve pays compile cost;
/// every subsequent timed solve hits the cache and skips the
/// compile. This is the "primary-jit-warm" column.
fn measure_primary_jit_warm(
    path: &Path,
    repetitions: usize,
    _warmup: bool,
) -> Result<(Vec<Duration>, i32), AnyError> {
    // Clear caches once at the start so the priming solve is the
    // only compile this measurement pays for, regardless of what
    // earlier fixtures left behind.
    reset_jit_compile_caches_for_tests();
    reset_jit_shadow_for_tests();
    PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
    let prime_rc = solve_path(path)?;
    PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
    let mut last_rc = prime_rc;
    let mut samples = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        // Reset per-solve state but DO NOT reset the compile cache.
        // The first call inside this solve hits the cache.
        reset_jit_shadow_for_tests();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        let t0 = Instant::now();
        last_rc = solve_path(path)?;
        let elapsed = t0.elapsed();
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
        samples.push(elapsed);
    }
    Ok((samples, last_rc))
}

/// Wall-clock PRIMARY_JIT_MODE solve where each repetition pays the
/// JIT compile cost from scratch AND has no on-disk cache file to
/// short-circuit module construction. This is the "primary-jit-disk-cold"
/// column: it models SAT-Comp's first-ever invocation on a fresh
/// machine, where neither the in-memory cache nor the on-disk cache
/// has anything to offer.
fn measure_primary_jit_disk_cold(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<(Vec<Duration>, i32), AnyError> {
    let mut last_rc = 0;
    if warmup {
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        clear_disk_cache();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        last_rc = solve_path(path)?;
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
    }
    let mut samples = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        // Clear BOTH caches before every repetition so the disk hit
        // path cannot accidentally serve the IR text from a prior
        // iteration. This is the strictest "cold" model.
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        clear_disk_cache();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        let t0 = Instant::now();
        last_rc = solve_path(path)?;
        let elapsed = t0.elapsed();
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
        samples.push(elapsed);
    }
    Ok((samples, last_rc))
}

/// Wall-clock PRIMARY_JIT_MODE solve where the on-disk cache is
/// pre-populated once and the in-memory cache is cleared between
/// repetitions. The first (untimed) priming solve writes the disk
/// file; every subsequent timed solve sees an empty in-memory cache
/// but a populated disk cache, so the compile path takes the
/// disk-hit code branch (parse cached IR, skip module construction,
/// run `compile_module_to_jit`). This is the "primary-jit-disk-warm"
/// column - the cross-process amortization story SAT-Comp cares
/// about.
fn measure_primary_jit_disk_warm(
    path: &Path,
    repetitions: usize,
    _warmup: bool,
) -> Result<(Vec<Duration>, i32), AnyError> {
    // Reset everything once, then run a priming solve so the disk
    // file gets written for the formula under test.
    reset_jit_compile_caches_for_tests();
    reset_jit_shadow_for_tests();
    clear_disk_cache();
    PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
    let prime_rc = solve_path(path)?;
    PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
    let mut last_rc = prime_rc;
    let mut samples = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        // Per-repetition: clear in-memory caches (simulating a new
        // process bootstrap) but leave the disk file alone so each
        // solve exercises the disk-hit code path.
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        let t0 = Instant::now();
        last_rc = solve_path(path)?;
        let elapsed = t0.elapsed();
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
        samples.push(elapsed);
    }
    Ok((samples, last_rc))
}

/// Telemetry snapshot harvested across a `measure_primary_jit_*`
/// run. The counters are process-global so callers diff before/after
/// to attribute the JIT firing behaviour to the just-completed
/// fixture. See `propagate.rs` for the canonical definitions.
#[derive(Default, Clone, Copy, Debug)]
struct PrimaryJitTelemetry {
    propagate_calls: u64,
    jit_inits: u64,
    jit_primary_returns: u64,
    jit_divergences: u64,
}

fn snapshot_primary_jit_telemetry() -> PrimaryJitTelemetry {
    PrimaryJitTelemetry {
        propagate_calls: PROPAGATE_CALL_COUNT.load(Ordering::SeqCst),
        jit_inits: JIT_INIT_COUNT.load(Ordering::SeqCst),
        jit_primary_returns: JIT_PRIMARY_RETURNS.load(Ordering::SeqCst),
        jit_divergences: JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst),
    }
}

fn telemetry_delta(
    before: &PrimaryJitTelemetry,
    after: &PrimaryJitTelemetry,
) -> PrimaryJitTelemetry {
    PrimaryJitTelemetry {
        propagate_calls: after.propagate_calls - before.propagate_calls,
        jit_inits: after.jit_inits - before.jit_inits,
        jit_primary_returns: after.jit_primary_returns - before.jit_primary_returns,
        jit_divergences: after.jit_divergences - before.jit_divergences,
    }
}

/// Wall-clock PRIMARY_JIT_MODE solve with the historical
/// root-authoritative gate engaged (no `JIT_ANALYZE_DRIVER_FORCE`).
/// This is the production single-shot configuration: the JIT only
/// replaces native at the root-forced regime. The JIT compile cache
/// is dropped before every iteration so each repetition pays the cold
/// cost (same accounting as a single-shot SAT-Comp invocation).
fn measure_primary_jit_gate_on(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<(Vec<Duration>, i32, PrimaryJitTelemetry), AnyError> {
    let before = snapshot_primary_jit_telemetry();
    let mut last_rc = 0;
    if warmup {
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        last_rc = solve_path(path)?;
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
    }
    let mut samples = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        let t0 = Instant::now();
        last_rc = solve_path(path)?;
        let elapsed = t0.elapsed();
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
        samples.push(elapsed);
    }
    let after = snapshot_primary_jit_telemetry();
    Ok((samples, last_rc, telemetry_delta(&before, &after)))
}

/// Wall-clock PRIMARY_JIT_MODE solve with `JIT_ANALYZE_DRIVER_FORCE`
/// engaged (the historical root-authoritative gate is bypassed; the
/// JIT runs as the primary verdict on every non-empty propagate
/// call). This corresponds to RRR's "verification works but speed is
/// gated by the DB-arena split" configuration; the verdict must
/// match native (the release-corpus test
/// `non_root_jit_replacement_zero_divergences_on_release_corpus` already
/// asserts zero divergences for this mode). Compile cache cleared
/// per-repetition for cold accounting parity with
/// `measure_primary_jit_gate_on`.
fn measure_primary_jit_analyze_driver_force(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<(Vec<Duration>, i32, PrimaryJitTelemetry), AnyError> {
    let before = snapshot_primary_jit_telemetry();
    let mut last_rc = 0;
    let prior_force = JIT_ANALYZE_DRIVER_FORCE.swap(true, Ordering::SeqCst);
    if warmup {
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        last_rc = solve_path(path)?;
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
    }
    let mut samples = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        PRIMARY_JIT_MODE.store(true, Ordering::SeqCst);
        let t0 = Instant::now();
        last_rc = solve_path(path)?;
        let elapsed = t0.elapsed();
        PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
        samples.push(elapsed);
    }
    JIT_ANALYZE_DRIVER_FORCE.store(prior_force, Ordering::SeqCst);
    let after = snapshot_primary_jit_telemetry();
    Ok((samples, last_rc, telemetry_delta(&before, &after)))
}

fn measure_jit_compile(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<Vec<Duration>, AnyError> {
    let cnf = read_dimacs_cnf_file(path)
        .map_err(|err| bench_err(format!("read {}: {err}", path.display())))?;
    // Match the kernel the JIT-shadow column uses so the
    // `jit-compile-once` column reports the right thing: the default JIT kernel is
    // `JitBcpWatchedLiteralKernelProvider`. Trail capacity hint is
    // `num_vars`: every variable is assigned at most once during a
    // single BCP sweep, so this is a safe upper bound on per-call
    // trail growth.
    let trail_hint = cnf.num_vars;
    if warmup {
        JitBcpWatchedLiteralKernelProvider::compile(cnf.num_vars, cnf.clauses.clone(), trail_hint)
            .map_err(|err| bench_err(format!("JIT compile warmup failed: {err}")))?;
    }
    let mut samples = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        let clauses = cnf.clauses.clone();
        let t0 = Instant::now();
        let provider =
            JitBcpWatchedLiteralKernelProvider::compile(cnf.num_vars, clauses, trail_hint)
                .map_err(|err| bench_err(format!("JIT compile failed: {err}")))?;
        samples.push(t0.elapsed());
        drop(provider);
    }
    Ok(samples)
}

fn run() -> Result<(), AnyError> {
    let args = parse_args()?;
    let fixtures = corpus_fixtures()?;
    if fixtures.is_empty() {
        return Err(bench_err(format!(
            "no .cnf fixtures discovered under {}",
            corpus_dir().display()
        )));
    }

    eprintln!(
        "satlib_bench_table: {} fixtures, {} repetitions/fixture, warmup={}, jit_kernel={}",
        fixtures.len(),
        args.repetitions,
        args.warmup,
        JIT_KERNEL_NAME
    );

    // Pin the JIT kernel both `measure_jit_shadow` and
    // `measure_jit_compile` exercise. The default is already
    // `watched-literal`, but storing explicitly leaves no doubt for
    // a reader who only sees the table.
    JIT_KERNEL_CHOICE.store(JIT_KERNEL_WATCHED_LITERAL, Ordering::SeqCst);

    println!("kernel: {JIT_KERNEL_NAME}");
    println!();
    println!(
        "| fixture | native (ms) | jit-shadow ({JIT_KERNEL_NAME}, ms) | overhead (%) | divergences | jit-compile-once ({JIT_KERNEL_NAME}, ms) | tier | amortization |"
    );
    println!("|---|---:|---:|---:|---:|---:|---|---|");

    // Tier counters drive the post-table summary so the operator can
    // see at a glance how many fixtures actually exercise per-call JIT
    // amortization vs how many are dominated by the compile cost.
    let mut tier_counts: [usize; TIER_LABELS.len()] = [0; TIER_LABELS.len()];
    let mut amortizes = 0usize;
    let mut compile_dominates = 0usize;
    let mut too_easy_for_jit = 0usize;

    for (label, path) in &fixtures {
        eprintln!("  measuring {label}...");
        let (native_samples, native_rc) = measure_native(path, args.repetitions, args.warmup)?;
        let (jit_samples, jit_rc, divergences) =
            measure_jit_shadow(path, args.repetitions, args.warmup)?;
        let compile_samples = measure_jit_compile(path, args.repetitions, args.warmup)?;

        if native_rc != jit_rc {
            return Err(bench_err(format!(
                "result code mismatch on {label}: native={native_rc} jit-shadow={jit_rc}"
            )));
        }

        let native_ms = mean_ms(&native_samples);
        let jit_ms = mean_ms(&jit_samples);
        let compile_ms = mean_ms(&compile_samples);
        let overhead_pct = if native_ms > 0.0 {
            (jit_ms - native_ms) / native_ms * 100.0
        } else {
            f64::NAN
        };

        let tier = solve_tier(native_ms);
        let amort = amortization_verdict(native_ms, jit_ms, compile_ms);
        tier_counts[tier as usize] += 1;
        match amort {
            AmortizationVerdict::Amortizes => amortizes += 1,
            AmortizationVerdict::CompileDominates => compile_dominates += 1,
            AmortizationVerdict::TooEasyForJit => too_easy_for_jit += 1,
        }

        println!(
            "| {label} | {native_ms:.3} | {jit_ms:.3} | {overhead_pct:+.1} | {divergences} | {compile_ms:.3} | {tier} | {amort} |"
        );
    }

    // Post-table summary: tier histogram + amortization verdict
    // breakdown. Printed to stderr so the markdown table on stdout
    // stays clean and pasteable into the benchmark study document.
    eprintln!();
    eprintln!(
        "solve-time tier distribution (native, mean of {} reps):",
        args.repetitions
    );
    for (idx, label) in TIER_LABELS.iter().enumerate() {
        eprintln!("  {:<24}: {}", label, tier_counts[idx]);
    }
    eprintln!();
    eprintln!("amortization verdict:");
    eprintln!("  amortizes (jit-shadow overhead < native solve): {amortizes}");
    eprintln!("  compile-dominates (jit-shadow >= native solve): {compile_dominates}");
    eprintln!("  too-easy-for-jit (native < 100 us)            : {too_easy_for_jit}");

    // JIT-compile-cache cold-vs-warm comparison across the entire
    // corpus. The cold column clears the thread-local
    // `JIT_BCP_*_CACHE` between repetitions so each solve pays the
    // full compile cost. The warm column primes the cache once,
    // then measures the cache-hit path on every subsequent
    // repetition. The delta isolates the JIT compile cost the
    // cache eliminates; DDD-v2's primary_jit on uuf75-01 shows up
    // as the gap between primary-jit-cold and primary-jit-warm.
    println!();
    println!("## JIT compile cache: primary-jit cold (cache miss) vs warm (cache hit)");
    println!();
    println!(
        "| fixture | native (ms) | primary-jit-cold (ms) | primary-jit-warm (ms) | warm-vs-cold delta (ms) | warm speedup (x) |"
    );
    println!("|---|---:|---:|---:|---:|---:|");
    let mut cache_div_total: u64 = 0;
    for (label, path) in &fixtures {
        eprintln!("  cache-comparison: measuring {label}...");
        let div_before = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
        let (native_samples, native_rc) = measure_native(path, args.repetitions, args.warmup)?;
        let (cold_samples, cold_rc) =
            measure_primary_jit_cold(path, args.repetitions, args.warmup)?;
        let (warm_samples, warm_rc) =
            measure_primary_jit_warm(path, args.repetitions, args.warmup)?;
        if native_rc != cold_rc || native_rc != warm_rc {
            return Err(bench_err(format!(
                "rc mismatch on cache comparison for {label}: \
                 native={native_rc} cold={cold_rc} warm={warm_rc}"
            )));
        }
        let div_after = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
        cache_div_total += div_after - div_before;
        let native_ms = mean_ms(&native_samples);
        let cold_ms = mean_ms(&cold_samples);
        let warm_ms = mean_ms(&warm_samples);
        let delta_ms = cold_ms - warm_ms;
        let speedup = if warm_ms > 0.0 {
            cold_ms / warm_ms
        } else {
            f64::NAN
        };
        println!(
            "| {label} | {native_ms:.3} | {cold_ms:.3} | {warm_ms:.3} | {delta_ms:+.3} | {speedup:.2} |"
        );
    }
    eprintln!("cache-comparison: divergences observed across cold+warm runs: {cache_div_total}");

    // -------- Post-QQQ/RRR re-measurement (full corpus) --------
    //
    // Captures the production PRIMARY_JIT_MODE wall-clock numbers on
    // the full 16-fixture corpus now that QQQ has gated the hot-path
    // eprintln spam and RRR has fixed the kernel-decode invariant.
    // Two configurations:
    //
    //   * gate enabled (historical root-authoritative gate; JIT
    //     replaces native only at the root-forced regime). This is
    //     the production single-shot configuration.
    //
    //   * `JIT_ANALYZE_DRIVER_FORCE` engaged (the historical gate is
    //     bypassed; the JIT runs as primary on every non-empty
    //     propagate call, with the conflict branch surrendering back
    //     to native because the analyze-driver's reason-chain story
    //     does not hold cross-call). This is the "verification works
    //     but speed gated by DB-arena split" configuration RRR's
    //     work landed.
    //
    // Cold compile cache per repetition so each timing reflects what
    // a single-shot SAT-Comp invocation would see.
    println!();
    println!(
        "## Post-QQQ/RRR re-measurement: native vs PRIMARY_JIT_MODE (gate on) vs PRIMARY_JIT_MODE (analyze-driver-force)"
    );
    println!();
    println!(
        "| fixture | native (ms) | primary-jit gate-on (ms) | delta gate-on vs native (%) | primary-jit ADF (ms) | delta ADF vs native (%) | gate-on primary returns/solve | gate-on JIT inits/solve | ADF primary returns/solve |"
    );
    println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|");

    // Track whether any fixture's gate-on configuration came in
    // end-to-end faster than native; print the list to stderr at the
    // bottom of the section so the operator can see at a glance which
    // fixtures (if any) flipped after QQQ+RRR. Negative delta means
    // JIT is faster.
    let mut gate_on_wins: Vec<(String, f64, f64, f64)> = Vec::new();
    let mut adf_wins: Vec<(String, f64, f64, f64)> = Vec::new();

    for (label, path) in &fixtures {
        eprintln!("  post-QQQ/RRR: measuring {label}...");
        // Native first so the JIT-shadow cache and analyze-driver
        // flag are not engaged when timing the native baseline.
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        let (native_samples, native_rc) = measure_native(path, args.repetitions, args.warmup)?;

        let (gate_samples, gate_rc, gate_telem) =
            measure_primary_jit_gate_on(path, args.repetitions, args.warmup)?;

        let (adf_samples, adf_rc, adf_telem) =
            measure_primary_jit_analyze_driver_force(path, args.repetitions, args.warmup)?;

        if native_rc != gate_rc {
            return Err(bench_err(format!(
                "rc mismatch on post-QQQ/RRR gate-on column for {label}: \
                 native={native_rc} gate-on={gate_rc}"
            )));
        }
        // ADF column: known latent analyze-driver bug on SAT instances
        // post-learning (see `non_root_jit_replacement_zero_divergences_on_release_corpus`
        // in src/lib.rs for the explicit regression campaign). Demote rc mismatch
        // to a warning so the bench can still complete the whole corpus
        // and the gate-on column (the production configuration) is
        // surfaced. The mismatch is recorded in `adf_rc_mismatches`.
        let adf_rc_warning = native_rc != adf_rc;
        if adf_rc_warning {
            eprintln!(
                "  warning: ADF rc mismatch on {label}: native={native_rc} adf={adf_rc} \
                 (known latent analyze-driver bug post-learning)"
            );
        }

        let native_ms = mean_ms(&native_samples);
        let gate_ms = mean_ms(&gate_samples);
        let adf_ms = mean_ms(&adf_samples);
        let gate_delta_pct = if native_ms > 0.0 {
            (gate_ms - native_ms) / native_ms * 100.0
        } else {
            f64::NAN
        };
        let adf_delta_pct = if native_ms > 0.0 {
            (adf_ms - native_ms) / native_ms * 100.0
        } else {
            f64::NAN
        };

        // Per-repetition averages of the telemetry counters - clearer
        // than raw totals for a reader trying to gauge how active the
        // JIT-replacement pathway was on this fixture.
        // Per-solve averages. Each fixture measurement is `repetitions + 1`
        // solves if warmup is on (the warmup counts toward the
        // telemetry totals too); otherwise just `repetitions`. We
        // divide by repetitions so the figures are comparable across
        // `--warmup` and no-warmup runs.
        let reps = args.repetitions as f64;
        let gate_primary_per_solve = gate_telem.jit_primary_returns as f64 / reps;
        let gate_inits_per_solve = gate_telem.jit_inits as f64 / reps;
        let adf_primary_per_solve = adf_telem.jit_primary_returns as f64 / reps;

        if gate_ms < native_ms {
            gate_on_wins.push((label.clone(), native_ms, gate_ms, gate_delta_pct));
        }
        if !adf_rc_warning && adf_ms < native_ms {
            adf_wins.push((label.clone(), native_ms, adf_ms, adf_delta_pct));
        }

        println!(
            "| {label} | {native_ms:.3} | {gate_ms:.3} | {gate_delta_pct:+.1} | {adf_ms:.3} | {adf_delta_pct:+.1} | {gate_primary_per_solve:.1} | {gate_inits_per_solve:.1} | {adf_primary_per_solve:.1} |"
        );
    }

    eprintln!();
    eprintln!("post-QQQ/RRR summary:");
    eprintln!(
        "  fixtures where primary-jit gate-on beat native end-to-end: {}",
        gate_on_wins.len()
    );
    for (label, native_ms, gate_ms, delta) in &gate_on_wins {
        eprintln!("    {label}: native={native_ms:.3}ms gate-on={gate_ms:.3}ms ({delta:+.1}%)");
    }
    eprintln!(
        "  fixtures where primary-jit ADF beat native end-to-end: {}",
        adf_wins.len()
    );
    for (label, native_ms, adf_ms, delta) in &adf_wins {
        eprintln!("    {label}: native={native_ms:.3}ms ADF={adf_ms:.3}ms ({delta:+.1}%)");
    }

    // Section boundary: drop everything the post-QQQ/RRR section left
    // behind so the disk-cache section starts from a clean slate.
    // The disk-cold helper clears these again per-repetition, but
    // resetting here keeps the section contract self-evident and
    // ensures even the warmup solve below sees an empty cache.
    clear_disk_cache();
    reset_jit_compile_caches_for_tests();
    reset_jit_shadow_for_tests();

    // Disk-cache cold-vs-warm comparison. Pinned to the
    // watched-literal kernel like the in-memory comparison above.
    // The two new columns model the SAT-Comp story explicitly:
    //   primary-jit-disk-cold: SAT-Comp's first ever invocation on
    //   a fresh machine. No in-memory cache, no on-disk cache.
    //   Equivalent to today's behaviour before this change.
    //
    //   primary-jit-disk-warm: SAT-Comp's Nth invocation on the
    //   same instance (or a same-formula instance) after the
    //   first run wrote the IR cache. In-memory cache still
    //   starts empty (it's a fresh process), but the disk cache
    //   short-circuits module construction.
    println!();
    println!("## JIT compile cache: disk-cold (no $XDG file) vs disk-warm (file primed)");
    println!();
    println!(
        "| fixture | native (ms) | primary-jit-disk-cold (ms) | primary-jit-disk-warm (ms) | disk-warm-vs-cold delta (ms) | disk-warm speedup (x) |"
    );
    println!("|---|---:|---:|---:|---:|---:|");
    let mut disk_div_total: u64 = 0;
    for (label, path) in &fixtures {
        eprintln!("  disk-cache-comparison: measuring {label}...");
        let div_before = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
        let (native_samples, native_rc) = measure_native(path, args.repetitions, args.warmup)?;
        let (cold_samples, cold_rc) =
            measure_primary_jit_disk_cold(path, args.repetitions, args.warmup)?;
        let (warm_samples, warm_rc) =
            measure_primary_jit_disk_warm(path, args.repetitions, args.warmup)?;
        if native_rc != cold_rc || native_rc != warm_rc {
            return Err(bench_err(format!(
                "rc mismatch on disk cache comparison for {label}: \
                 native={native_rc} disk-cold={cold_rc} disk-warm={warm_rc}"
            )));
        }
        let div_after = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
        disk_div_total += div_after - div_before;
        let native_ms = mean_ms(&native_samples);
        let cold_ms = mean_ms(&cold_samples);
        let warm_ms = mean_ms(&warm_samples);
        let delta_ms = cold_ms - warm_ms;
        let speedup = if warm_ms > 0.0 {
            cold_ms / warm_ms
        } else {
            f64::NAN
        };
        println!(
            "| {label} | {native_ms:.3} | {cold_ms:.3} | {warm_ms:.3} | {delta_ms:+.3} | {speedup:.2} |"
        );
    }
    eprintln!(
        "disk-cache-comparison: divergences observed across cold+warm runs: {disk_div_total}"
    );

    // Leave the disk cache populated so the operator can inspect the
    // resulting `$XDG_CACHE_HOME/trust-cg/jit/` directory after the
    // run if desired. Tests rely on `clear_disk_cache()` explicitly
    // when they want a fresh slate.

    let total_div = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
    eprintln!("total divergences observed across all fixtures: {total_div}");
    if total_div > 0 {
        return Err(bench_err(format!(
            "shadow divergence > 0 ({total_div}); investigate before quoting these numbers"
        )));
    }
    Ok(())
}

/// Solve-time tier label, used in the markdown table and the
/// post-table histogram. Bucket cut-offs are picked so the existing
/// 50-variable generated smoke corpus falls in the bottom two tiers, the
/// 75-variable generated instances and small PHPs land in the middle tier,
/// and the harder 100-variable generated instances / large PHPs land in the
/// top two tiers. The
/// boundary at 1.5 ms is intentionally aligned with today's measured
/// JIT compile cost so it is easy to see at a glance which fixtures
/// even have a chance of demonstrating per-call amortization.
#[derive(Clone, Copy, Debug)]
enum SolveTier {
    /// Native solve completes in under 100 microseconds. JIT compile
    /// cost is orders of magnitude larger than solve; per-call
    /// amortization is impossible on this fixture.
    Trivial,
    /// 100 us .. 500 us. Still well under the compile cost.
    Easy,
    /// 500 us .. 1.5 ms. Solve and compile are the same order of
    /// magnitude; amortization tips one way or the other.
    Boundary,
    /// 1.5 ms .. 10 ms. Solve dominates compile by a small factor;
    /// per-call JIT speedup should be measurable.
    Moderate,
    /// >= 10 ms. Solve dominates compile by >=10x; per-call JIT
    /// > speedup is clearly visible end-to-end.
    Hard,
}

const TIER_LABELS: [&str; 5] = [
    "trivial    (<100 us)",
    "easy       (.1-.5ms)",
    "boundary   (.5-1.5ms)",
    "moderate   (1.5-10ms)",
    "hard       (>=10 ms)",
];

impl fmt::Display for SolveTier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolveTier::Trivial => f.write_str("trivial"),
            SolveTier::Easy => f.write_str("easy"),
            SolveTier::Boundary => f.write_str("boundary"),
            SolveTier::Moderate => f.write_str("moderate"),
            SolveTier::Hard => f.write_str("hard"),
        }
    }
}

fn solve_tier(native_ms: f64) -> SolveTier {
    if native_ms < 0.1 {
        SolveTier::Trivial
    } else if native_ms < 0.5 {
        SolveTier::Easy
    } else if native_ms < 1.5 {
        SolveTier::Boundary
    } else if native_ms < 10.0 {
        SolveTier::Moderate
    } else {
        SolveTier::Hard
    }
}

/// Three-way verdict on whether a fixture meaningfully exercises the
/// JIT amortization story. The decision is on jit-shadow time vs
/// native: when shadow tracking adds overhead smaller than the
/// native solve itself, the *per-call* JIT path has effectively paid
/// for the bookkeeping; when shadow overhead exceeds native solve we
/// would never want to JIT on this fixture in production.
#[derive(Clone, Copy, Debug)]
enum AmortizationVerdict {
    /// jit-shadow runs at or below native solve - the JIT path has
    /// already amortized its own bookkeeping on this fixture.
    Amortizes,
    /// jit-shadow exceeds native solve - on this fixture the compile
    /// or shadow-tracking cost is larger than just running native.
    CompileDominates,
    /// Native solve is below 100 us; per-call JIT cannot possibly
    /// help, regardless of what jit-shadow measures.
    TooEasyForJit,
}

impl fmt::Display for AmortizationVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AmortizationVerdict::Amortizes => f.write_str("amortizes"),
            AmortizationVerdict::CompileDominates => f.write_str("compile-dominates"),
            AmortizationVerdict::TooEasyForJit => f.write_str("too-easy-for-jit"),
        }
    }
}

fn amortization_verdict(
    native_ms: f64,
    jit_shadow_ms: f64,
    _compile_ms: f64,
) -> AmortizationVerdict {
    if native_ms < 0.1 {
        AmortizationVerdict::TooEasyForJit
    } else if jit_shadow_ms <= native_ms {
        AmortizationVerdict::Amortizes
    } else {
        AmortizationVerdict::CompileDominates
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("satlib_bench_table: {err}");
            ExitCode::FAILURE
        }
    }
}
