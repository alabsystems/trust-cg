// adf_quick_bench - Wall-clock comparison of native vs ADF (analyze-
// driver-force) on a configurable subset of the project-authored release
// corpus.
//
// This is purposely a *fast* benchmark for the candidate iteration
// loop: it skips the disk/in-memory-cache columns of `satlib_bench_table`
// and only times native + PRIMARY_JIT_MODE+ADF on the named fixtures.
// It also reports legacy telemetry: clause agreements count shortcut-predicate
// admissions, not independent comparison with the skipped native walk. The
// native-skips counter is reserved and is not incremented by current dispatch.
//
// Usage:
//   scripts/trust_cargo.sh run -p trust-cg-sat-host --bin adf_quick_bench --release -- \
//       --reps 5 php-10-9 uuf100-04
//
// If no fixtures are listed the default pair (php-10-9, uuf100-04) is
// used. Repetitions default to 5.

use std::ffi::CString;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::Ordering;
use std::time::Duration;

use trust_cg_jit_matrix::jit_compile_cache::reset_jit_compile_caches_for_tests;
use trust_cg_sat_host::propagate::{
    JIT_KERNEL_CHOICE, JIT_KERNEL_WATCHED_LITERAL, reset_jit_shadow_for_tests,
};
use trust_cg_sat_host::{OwnedMicroSatSolver, sys};

#[path = "common/sat_measurement.rs"]
pub mod sat_measurement;
use sat_measurement::{AnyError, DiskBackingGuard, SolveMode, SolveTelemetry, bench_err, measure};

fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("sat_corpus")
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

fn measure_native(path: &Path, reps: usize) -> Result<(Vec<Duration>, i32), AnyError> {
    let (samples, rc, _) = measure(
        SolveMode::Native,
        reps,
        false,
        || Ok(()),
        || solve_path(path),
    )?;
    Ok((samples, rc))
}

fn measure_adf(path: &Path, reps: usize) -> Result<(Vec<Duration>, i32, SolveTelemetry), AnyError> {
    measure(
        SolveMode::Primary {
            analyze_driver: true,
        },
        reps,
        false,
        || {
            reset_jit_compile_caches_for_tests();
            reset_jit_shadow_for_tests();
            Ok(())
        },
        || solve_path(path),
    )
}

fn parse_args() -> Result<(usize, Vec<String>), AnyError> {
    let mut reps: usize = 5;
    let mut labels: Vec<String> = Vec::new();
    let mut iter = std::env::args().skip(1);
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--reps" => {
                let val = iter
                    .next()
                    .ok_or_else(|| bench_err("--reps requires a positive integer"))?;
                reps = val
                    .parse::<usize>()
                    .map_err(|err| bench_err(format!("--reps {val:?}: {err}")))?;
                if reps == 0 {
                    return Err(bench_err("--reps must be >= 1"));
                }
            }
            "--help" | "-h" => {
                println!("adf_quick_bench: quick native vs ADF wall-clock");
                println!("Usage: adf_quick_bench [--reps N] FIXTURE ...");
                std::process::exit(0);
            }
            other => labels.push(other.to_string()),
        }
    }
    if labels.is_empty() {
        labels.push("php-10-9".to_string());
        labels.push("uuf100-04".to_string());
    }
    Ok((reps, labels))
}

fn run() -> Result<(), AnyError> {
    let (reps, labels) = parse_args()?;
    let _memory_only = DiskBackingGuard::enter(false);
    let dir = corpus_dir();
    JIT_KERNEL_CHOICE.store(JIT_KERNEL_WATCHED_LITERAL, Ordering::SeqCst);

    eprintln!("adf_quick_bench: {} fixtures x {} reps", labels.len(), reps);
    println!(
        "Saturated or regressing telemetry rejects the measurement. Primary events are kernel attempts plus mapped comparisons, not authoritative returns; clause shortcuts are predicate admissions, not checked agreements. Native skips are reserved and remain zero."
    );
    println!(
        "| fixture | native (ms) | adf (ms) | delta (%) | calls/solve | primary_events/solve | adf_driven/solve | clause_shortcuts/solve | reserved_native_skips/solve | divergences |"
    );
    println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|");

    for label in &labels {
        let path = dir.join(format!("{label}.cnf"));
        if !path.exists() {
            return Err(bench_err(format!(
                "fixture {} not found at {}",
                label,
                path.display()
            )));
        }

        // Native baseline first.
        let (native_samples, native_rc) = measure_native(&path, reps)?;

        let (adf_samples, adf_rc, telemetry) = measure_adf(&path, reps)?;

        if native_rc != adf_rc {
            return Err(bench_err(format!(
                "rc mismatch on {label}: native={native_rc} adf={adf_rc}"
            )));
        }

        let native_ms = mean_ms(&native_samples);
        let adf_ms = mean_ms(&adf_samples);
        let delta_pct = if native_ms > 0.0 {
            (adf_ms - native_ms) / native_ms * 100.0
        } else {
            f64::NAN
        };
        let reps_f = reps as f64;
        let calls_per = telemetry.propagate_calls as f64 / reps_f;
        let prim_per = telemetry.jit_primary_events as f64 / reps_f;
        let driven_per = telemetry.jit_analyze_driven as f64 / reps_f;
        let agree_per = telemetry.jit_clause_shortcuts as f64 / reps_f;
        let skips_per = telemetry.jit_reserved_native_skips as f64 / reps_f;
        let div = telemetry.jit_divergences;

        println!(
            "| {label} | {native_ms:.3} | {adf_ms:.3} | {delta_pct:+.1} | {calls_per:.0} | {prim_per:.0} | {driven_per:.0} | {agree_per:.0} | {skips_per:.0} | {div} |"
        );
    }
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("adf_quick_bench: {err}");
            ExitCode::FAILURE
        }
    }
}
