// adf_quick_bench - Wall-clock comparison of native vs ADF (analyze-
// driver-force) on a configurable subset of the project-authored release
// corpus.
//
// This is purposely a *fast* benchmark for the candidate iteration
// loop: it skips the disk/in-memory-cache columns of `satlib_bench_table`
// and only times native + PRIMARY_JIT_MODE+ADF on the named fixtures.
// It also dumps the JIT_ANALYZE_DRIVER_CLAUSE_AGREEMENTS and
// JIT_ANALYZE_DRIVER_NATIVE_SKIPS counters so the operator can see
// how often each F1-v2 optimization fired.
//
// Usage:
//   cargo run -p trust-cg-sat-host --bin adf_quick_bench --release -- \
//       --reps 5 php-10-9 uuf100-04
//
// If no fixtures are listed the default pair (php-10-9, uuf100-04) is
// used. Repetitions default to 5.

use std::error::Error;
use std::ffi::CString;
use std::fmt;
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};

use trust_cg_jit_matrix::jit_compile_cache::reset_jit_compile_caches_for_tests;
use trust_cg_sat_host::propagate::{
    JIT_ANALYZE_DRIVEN, JIT_ANALYZE_DRIVER_CLAUSE_AGREEMENTS, JIT_ANALYZE_DRIVER_FORCE,
    JIT_ANALYZE_DRIVER_NATIVE_SKIPS, JIT_DIVERGENCE_COUNT, JIT_INIT_COUNT, JIT_KERNEL_CHOICE,
    JIT_KERNEL_WATCHED_LITERAL, JIT_PRIMARY_RETURNS, PRIMARY_JIT_MODE, PROPAGATE_CALL_COUNT,
    SHADOW_MODE, reset_jit_shadow_for_tests,
};
use trust_cg_sat_host::sys;

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
    let mut solver: MaybeUninit<sys::solver> = MaybeUninit::uninit();
    // SAFETY: same pattern as upstream MicroSAT `main`. `parse` runs
    // `initCDCL` and fully populates the solver before any read.
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

fn measure_native(path: &Path, reps: usize) -> Result<(Vec<Duration>, i32), AnyError> {
    SHADOW_MODE.store(false, Ordering::SeqCst);
    PRIMARY_JIT_MODE.store(false, Ordering::SeqCst);
    let mut last_rc = 0;
    let mut samples = Vec::with_capacity(reps);
    for _ in 0..reps {
        let t0 = Instant::now();
        last_rc = solve_path(path)?;
        samples.push(t0.elapsed());
    }
    Ok((samples, last_rc))
}

fn measure_adf(path: &Path, reps: usize) -> Result<(Vec<Duration>, i32), AnyError> {
    let prior_force = JIT_ANALYZE_DRIVER_FORCE.swap(true, Ordering::SeqCst);
    let mut last_rc = 0;
    let mut samples = Vec::with_capacity(reps);
    for _ in 0..reps {
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
    Ok((samples, last_rc))
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
    let dir = corpus_dir();
    JIT_KERNEL_CHOICE.store(JIT_KERNEL_WATCHED_LITERAL, Ordering::SeqCst);

    eprintln!("adf_quick_bench: {} fixtures x {} reps", labels.len(), reps);
    println!(
        "| fixture | native (ms) | adf (ms) | delta (%) | calls/solve | jit_prim/solve | adf_driven/solve | clause_agree/solve | native_skips/solve | divergences |"
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

        // ADF run; snapshot counters before / after to attribute the
        // primary returns and clause-agreement counters to this run.
        let calls_before = PROPAGATE_CALL_COUNT.load(Ordering::SeqCst);
        let prim_before = JIT_PRIMARY_RETURNS.load(Ordering::SeqCst);
        let driven_before = JIT_ANALYZE_DRIVEN.load(Ordering::SeqCst);
        let agree_before = JIT_ANALYZE_DRIVER_CLAUSE_AGREEMENTS.load(Ordering::SeqCst);
        let skips_before = JIT_ANALYZE_DRIVER_NATIVE_SKIPS.load(Ordering::SeqCst);
        let div_before = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
        let _inits_before = JIT_INIT_COUNT.load(Ordering::SeqCst);

        let (adf_samples, adf_rc) = measure_adf(&path, reps)?;

        let calls_after = PROPAGATE_CALL_COUNT.load(Ordering::SeqCst);
        let prim_after = JIT_PRIMARY_RETURNS.load(Ordering::SeqCst);
        let driven_after = JIT_ANALYZE_DRIVEN.load(Ordering::SeqCst);
        let agree_after = JIT_ANALYZE_DRIVER_CLAUSE_AGREEMENTS.load(Ordering::SeqCst);
        let skips_after = JIT_ANALYZE_DRIVER_NATIVE_SKIPS.load(Ordering::SeqCst);
        let div_after = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);

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
        let calls_per = (calls_after - calls_before) as f64 / reps_f;
        let prim_per = (prim_after - prim_before) as f64 / reps_f;
        let driven_per = (driven_after - driven_before) as f64 / reps_f;
        let agree_per = (agree_after - agree_before) as f64 / reps_f;
        let skips_per = (skips_after - skips_before) as f64 / reps_f;
        let div = div_after - div_before;

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
