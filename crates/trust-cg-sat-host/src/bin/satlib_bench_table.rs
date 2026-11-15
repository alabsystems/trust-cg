// Quick-look native/shadow/primary SAT measurements on the project-authored
// corpus in tests/fixtures/sat_corpus. Tables report observed means and fixed
// native-time buckets. They do not infer amortization, statistical significance,
// or current compile cost from a historical threshold. The memory/disk labels
// describe cleared or primed cache state, not measured cache-hit counts.
// Eligible performance headlines require the repository's measurement contract.
//
// Usage:
//
//   scripts/trust_cargo.sh run -p trust-cg-sat-host --bin satlib_bench_table --release
//   scripts/trust_cargo.sh run -p trust-cg-sat-host --bin satlib_bench_table --release -- \
//       --repetitions 10 --warmup
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The executable's legacy `satlib_` name is retained for compatibility. The
// current fixture corpus is generated entirely by this project and contains no
// SATLIB or AIM instance bytes.

use std::ffi::CString;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};

use trust_cg_jit_matrix::dimacs::read_dimacs_cnf_file;
use trust_cg_jit_matrix::jit_bcp_kernel::JitBcpWatchedLiteralKernelProvider;
use trust_cg_jit_matrix::jit_compile_cache::reset_jit_compile_caches_for_tests;
use trust_cg_sat_host::propagate::{
    JIT_DIVERGENCE_COUNT, JIT_KERNEL_CHOICE, JIT_KERNEL_WATCHED_LITERAL, reset_jit_shadow_for_tests,
};
use trust_cg_sat_host::{OwnedMicroSatSolver, sys};

/// Name of the JIT kernel this binary times. Pinned to
/// `watched-literal` because that is the default `JIT_KERNEL_CHOICE`
/// since the headline switchover; the table header surfaces it so
/// readers know which kernel produced the `jit-shadow (ms)` and
/// `jit-compile-once (ms)` columns.
const JIT_KERNEL_NAME: &str = "watched-literal";

#[path = "common/sat_measurement.rs"]
pub mod sat_measurement;
use sat_measurement::{
    AnyError, DiskBackingGuard, DiskCacheWorkspace, SolveMode, SolveTelemetry, bench_err, measure,
    measure_primary_jit, require_matching_verdict, require_memory_primed,
};

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
    // SAFETY: benchmark inputs are committed, well-formed DIMACS fixtures.
    let (mut solver, parse_rc) = unsafe { OwnedMicroSatSolver::parse(c_path.as_c_str()) };
    let rc = unsafe {
        if parse_rc == sys::UNSAT {
            sys::UNSAT
        } else {
            solver.solve()
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
    let (samples, rc, _) = measure(
        SolveMode::Native,
        repetitions,
        warmup,
        || Ok(()),
        || solve_path(path),
    )?;
    Ok((samples, rc))
}

fn measure_jit_shadow(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<(Vec<Duration>, i32, u64), AnyError> {
    let (samples, rc, telemetry) = measure(
        SolveMode::Shadow,
        repetitions,
        warmup,
        || {
            reset_jit_shadow_for_tests();
            Ok(())
        },
        || solve_path(path),
    )?;
    Ok((samples, rc, telemetry.jit_divergences))
}

/// Clear the in-memory provider caches before every solve. The caller's
/// memory-only guard disables the watched-literal provider's disk tier.
fn measure_primary_jit_cold(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<(Vec<Duration>, i32), AnyError> {
    let (samples, rc, _) =
        measure_primary_jit(true, repetitions, warmup, prepare_primary_jit, || {
            solve_path(path)
        })?;
    Ok((samples, rc))
}

/// Prime the provider cache once, then retain it across measured solves.
/// Require a provider after priming; its presence is not a measured hit count.
fn measure_primary_jit_warm(
    path: &Path,
    repetitions: usize,
    _warmup: bool,
) -> Result<(Vec<Duration>, i32), AnyError> {
    reset_jit_compile_caches_for_tests();
    let mut priming = true;
    let (samples, rc, _) = measure(
        SolveMode::Primary {
            analyze_driver: true,
        },
        repetitions,
        true,
        || {
            reset_jit_shadow_for_tests();
            if priming {
                priming = false;
                Ok(())
            } else {
                require_memory_primed()
            }
        },
        || solve_path(path),
    )?;
    Ok((samples, rc))
}

/// Clear both provider memory and the benchmark-owned IR-text directory before
/// each solve. This clears these caches, not every cache in a fresh process.
fn measure_primary_jit_disk_cold(
    path: &Path,
    repetitions: usize,
    warmup: bool,
    disk: &DiskCacheWorkspace,
) -> Result<(Vec<Duration>, i32), AnyError> {
    let _disk_backing = DiskBackingGuard::enter(true);
    let (samples, rc, _) = measure(
        SolveMode::Primary {
            analyze_driver: true,
        },
        repetitions,
        warmup,
        || {
            prepare_primary_jit();
            disk.clear()
        },
        || solve_path(path),
    )?;
    Ok((samples, rc))
}

/// Prime the isolated IR-text directory, requiring an artifact, then clear
/// provider memory between measured solves while preserving those files.
/// These are same-process measurements; no cache-hit or cross-process claim.
fn measure_primary_jit_disk_warm(
    path: &Path,
    repetitions: usize,
    _warmup: bool,
    disk: &DiskCacheWorkspace,
) -> Result<(Vec<Duration>, i32), AnyError> {
    let _disk_backing = DiskBackingGuard::enter(true);
    disk.clear()?;
    let mut priming = true;
    let (samples, rc, _) = measure(
        SolveMode::Primary {
            analyze_driver: true,
        },
        repetitions,
        true,
        || {
            prepare_primary_jit();
            if priming {
                priming = false;
                Ok(())
            } else {
                disk.require_primed()
            }
        },
        || solve_path(path),
    )?;
    Ok((samples, rc))
}

/// Wall-clock PRIMARY_JIT_MODE solve with the historical
/// root-authoritative gate engaged (no `JIT_ANALYZE_DRIVER_FORCE`).
/// Provider memory is cleared before every iteration. This admission mode is
/// distinct from the default-on analyze driver.
fn measure_primary_jit_gate_on(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<(Vec<Duration>, i32, SolveTelemetry), AnyError> {
    measure_primary_jit(false, repetitions, warmup, prepare_primary_jit, || {
        solve_path(path)
    })
}

/// Wall-clock PRIMARY_JIT_MODE solve with `JIT_ANALYZE_DRIVER_FORCE`
/// engaged (the historical root-authoritative gate is bypassed; the
/// replacement is attempted on nonempty trails, with native continuation where
/// required). Provider memory is cleared per repetition, as in the root-only lane.
fn measure_primary_jit_analyze_driver_force(
    path: &Path,
    repetitions: usize,
    warmup: bool,
) -> Result<(Vec<Duration>, i32, SolveTelemetry), AnyError> {
    measure_primary_jit(true, repetitions, warmup, prepare_primary_jit, || {
        solve_path(path)
    })
}

fn prepare_primary_jit() {
    reset_jit_compile_caches_for_tests();
    reset_jit_shadow_for_tests();
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
    let _memory_only = DiskBackingGuard::enter(false);
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
        "| fixture | native (ms) | jit-shadow ({JIT_KERNEL_NAME}, ms) | overhead (%) | divergences | jit-compile-once ({JIT_KERNEL_NAME}, ms) | native-time bucket |"
    );
    println!("|---|---:|---:|---:|---:|---:|---|");

    // Descriptive histogram of observed native means, not compile-cost buckets.
    let mut tier_counts: [usize; TIER_LABELS.len()] = [0; TIER_LABELS.len()];

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
        tier_counts[tier as usize] += 1;

        println!(
            "| {label} | {native_ms:.3} | {jit_ms:.3} | {overhead_pct:+.1} | {divergences} | {compile_ms:.3} | {tier} |"
        );
    }

    // Report the histogram separately from the table.
    eprintln!();
    eprintln!(
        "solve-time tier distribution (native, mean of {} reps):",
        args.repetitions
    );
    for (idx, label) in TIER_LABELS.iter().enumerate() {
        eprintln!("  {:<24}: {}", label, tier_counts[idx]);
    }

    // Compare cleared and primed provider memory with disk backing disabled.
    // Differences are observed whole-solve means, not isolated compile cost.
    println!();
    println!("## JIT provider cache: memory-cleared vs memory-primed (disk disabled)");
    println!();
    println!(
        "| fixture | native (ms) | memory-cleared (ms) | memory-primed (ms) | warm-vs-cold delta (ms) | warm speedup (x) |"
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

    // Explicitly compare root-only admission with the default analyze-driver
    // configuration. Both use cold compile-cache accounting per repetition.
    println!();
    println!("## Native vs primary JIT: root-only admission vs analyze driver");
    println!(
        "Telemetry excludes warmup; saturation or regression rejects the measurement. Primary events count kernel attempts plus mapped comparisons, not authoritative returns or native calls avoided."
    );
    println!();
    println!(
        "| fixture | native (ms) | primary-jit root-only (ms) | delta root-only vs native (%) | primary-jit ADF (ms) | delta ADF vs native (%) | root-only primary events/solve | root-only JIT inits/solve | ADF primary events/solve |"
    );
    println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|");

    // Track whether any fixture's gate-on configuration came in
    // end-to-end faster than native; print the list to stderr at the
    // bottom of the section so the operator can see at a glance which
    // fixtures (if any) were faster in this run. Negative delta means JIT is faster.
    let mut gate_on_wins: Vec<(String, f64, f64, f64)> = Vec::new();
    let mut adf_wins: Vec<(String, f64, f64, f64)> = Vec::new();

    for (label, path) in &fixtures {
        eprintln!("  primary lanes: measuring {label}...");
        // Native first so the JIT-shadow cache and analyze-driver
        // flag are not engaged when timing the native baseline.
        reset_jit_compile_caches_for_tests();
        reset_jit_shadow_for_tests();
        let (native_samples, native_rc) = measure_native(path, args.repetitions, args.warmup)?;

        let (gate_samples, gate_rc, gate_telem) =
            measure_primary_jit_gate_on(path, args.repetitions, args.warmup)?;

        let (adf_samples, adf_rc, adf_telem) =
            measure_primary_jit_analyze_driver_force(path, args.repetitions, args.warmup)?;

        require_matching_verdict(&format!("{label} root-only vs native"), native_rc, gate_rc)?;
        require_matching_verdict(
            &format!("{label} analyze-driver vs native"),
            native_rc,
            adf_rc,
        )?;

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

        // Warmup is excluded from both timing samples and telemetry snapshots.
        let reps = args.repetitions as f64;
        let gate_primary_per_solve = gate_telem.jit_primary_events as f64 / reps;
        let gate_inits_per_solve = gate_telem.jit_inits as f64 / reps;
        let adf_primary_per_solve = adf_telem.jit_primary_events as f64 / reps;

        if gate_ms < native_ms {
            gate_on_wins.push((label.clone(), native_ms, gate_ms, gate_delta_pct));
        }
        if adf_ms < native_ms {
            adf_wins.push((label.clone(), native_ms, adf_ms, adf_delta_pct));
        }

        println!(
            "| {label} | {native_ms:.3} | {gate_ms:.3} | {gate_delta_pct:+.1} | {adf_ms:.3} | {adf_delta_pct:+.1} | {gate_primary_per_solve:.1} | {gate_inits_per_solve:.1} | {adf_primary_per_solve:.1} |"
        );
    }

    eprintln!();
    eprintln!("primary-admission comparison summary:");
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

    // Isolate disk work from the operator's real cache. A real I/O control must
    // pass before this section can be measured or labeled disk-primed.
    let disk_cache = DiskCacheWorkspace::new()?;
    reset_jit_compile_caches_for_tests();
    reset_jit_shadow_for_tests();

    // Compare cleared and primed IR-text files; provider memory is cleared in
    // both lanes. Priming state is checked but cache hits are not counted.
    println!();
    println!("## JIT IR-text cache: disk-cleared vs disk-primed (isolated temporary directory)");
    println!();
    println!(
        "| fixture | native (ms) | disk-cleared (ms) | disk-primed (ms) | disk-warm-vs-cold delta (ms) | disk-warm speedup (x) |"
    );
    println!("|---|---:|---:|---:|---:|---:|");
    let mut disk_div_total: u64 = 0;
    for (label, path) in &fixtures {
        eprintln!("  disk-cache-comparison: measuring {label}...");
        let div_before = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
        let (native_samples, native_rc) = measure_native(path, args.repetitions, args.warmup)?;
        let (cold_samples, cold_rc) =
            measure_primary_jit_disk_cold(path, args.repetitions, args.warmup, &disk_cache)?;
        let (warm_samples, warm_rc) =
            measure_primary_jit_disk_warm(path, args.repetitions, args.warmup, &disk_cache)?;
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

    // DiskCacheWorkspace removes only this run's temporary artifacts on exit.

    let total_div = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
    eprintln!("total divergences observed across all fixtures: {total_div}");
    if total_div > 0 {
        return Err(bench_err(format!(
            "shadow divergence > 0 ({total_div}); investigate before quoting these numbers"
        )));
    }
    Ok(())
}

/// Fixed descriptive buckets for the observed native mean. Boundaries do not
/// imply anything about current JIT compile cost or achievable speedup.
#[derive(Clone, Copy, Debug)]
enum SolveTier {
    Trivial,
    Easy,
    Boundary,
    Moderate,
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

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("satlib_bench_table: {err}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod real_lane_tests {
    use super::*;
    use sat_measurement::test_support::MODE_LOCK;

    #[test]
    fn all_real_measurement_lanes_execute_on_a_small_sat_formula() {
        use std::io::Write;
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let previous_kernel = JIT_KERNEL_CHOICE.swap(JIT_KERNEL_WATCHED_LITERAL, Ordering::SeqCst);
        let result = std::panic::catch_unwind(|| {
            let _memory_only = DiskBackingGuard::enter(false);
            let disk = DiskCacheWorkspace::new().unwrap();
            let mut cnf = tempfile::NamedTempFile::new().unwrap();
            cnf.write_all(b"p cnf 2 2\n1 2 0\n-1 2 0\n").unwrap();
            cnf.flush().unwrap();
            let path = cnf.path();
            for warmup in [false, true] {
                for (samples, rc) in [
                    measure_native(path, 2, warmup).unwrap(),
                    measure_primary_jit_cold(path, 2, warmup).unwrap(),
                    measure_primary_jit_warm(path, 2, warmup).unwrap(),
                    measure_primary_jit_disk_cold(path, 2, warmup, &disk).unwrap(),
                    measure_primary_jit_disk_warm(path, 2, warmup, &disk).unwrap(),
                ] {
                    assert_eq!(rc, sys::SAT);
                    assert_eq!(samples.len(), 2);
                }
                let (samples, rc, divergences) = measure_jit_shadow(path, 2, warmup).unwrap();
                assert_eq!((samples.len(), rc, divergences), (2, sys::SAT, 0));
                for (samples, rc, telemetry) in [
                    measure_primary_jit_gate_on(path, 2, warmup).unwrap(),
                    measure_primary_jit_analyze_driver_force(path, 2, warmup).unwrap(),
                ] {
                    assert_eq!((samples.len(), rc), (2, sys::SAT));
                    assert!(telemetry.propagate_calls > 0);
                    assert!(telemetry.jit_inits > 0);
                    assert!(telemetry.jit_primary_events > 0);
                    assert_eq!(telemetry.jit_divergences, 0);
                }
            }
        });
        JIT_KERNEL_CHOICE.store(previous_kernel, Ordering::SeqCst);
        result.unwrap();
    }
}
