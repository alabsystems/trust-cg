// trust_cg_sat.rs — SAT-Comp-compliant solver entry point.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Purpose
// -------
// Wraps the trampolined MicroSAT + trust-cg JIT shadow/primary path
// (`trust_cg_sat_host`) into a single executable that conforms to the
// SAT-Competition solver invocation contract:
//
//   * Positional arg 1: path to a DIMACS CNF file.
//   * Positional arg 2 (optional) OR `--proof <path>`: DRAT proof output.
//   * Stdout: `c ...` info lines, `s SATISFIABLE` / `s UNSATISFIABLE` /
//     `s UNKNOWN` result line, plus `v <lit> ... 0` model lines on SAT.
//   * Exit code: 10 on SAT, 20 on UNSAT, 0 on UNKNOWN.
//
// Note that MicroSAT's internal codes are `SAT=1` / `UNSAT=0`; this
// wrapper performs the contract translation. See the comment block in
// `main()` for the exit-code mapping table.
//
// Toggles
// -------
// * `--shadow`        — engage `SHADOW_MODE` (JIT BCP runs as a
//   differential check alongside native propagate; native is still
//   authoritative for the return value).
// * `--primary-jit`   — engage `PRIMARY_JIT_MODE` (JIT BCP's verdict
//   becomes the primary return value where the epoch-0 authority
//   rules permit; mutually exclusive with `--shadow`).
// * `--jit-kernel`    — pick the JIT BCP kernel that both `--shadow`
//   and `--primary-jit` build. Default `watched-literal`; the `scan`
//   and `with-decisions` kernels remain available for
//   differential testing.
// * `--quiet`         — suppress `c ` info lines.
// * `--verbose`       — enable hot-path JIT diagnostic eprintlns
//   (epoch-fallback, buffer-overflow, per-call divergence) that are
//   suppressed by default to avoid drowning stderr on learning-heavy
//   instances. Use only when investigating a JIT regression.
//
// `.cnf.gz` handling is filed as a stretch goal in
// `benchmarks/benchmark_study.md`; this binary accepts only plain `.cnf`.

use std::ffi::CString;
use std::io::{self, Write};
use std::mem::MaybeUninit;
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::atomic::Ordering;

use clap::Parser;

use trust_cg_sat_host::drat_recorder::{
    disable_drat_output, enable_drat_output, flush_drat_output,
};
use trust_cg_sat_host::propagate::{
    JIT_DIVERGENCE_COUNT, JIT_INIT_COUNT, JIT_KERNEL_CHOICE, JIT_KERNEL_SCAN,
    JIT_KERNEL_WATCHED_LITERAL, JIT_KERNEL_WITH_DECISIONS, JIT_PRIMARY_RETURNS,
    JIT_SUCCESSFUL_RUNS, PRIMARY_JIT_MODE, PROPAGATE_CALL_COUNT, SHADOW_MODE,
    TRUST_CG_PROPAGATE_VERBOSE,
};
use trust_cg_sat_host::sys;

/// SAT-Comp exit code convention. Different from MicroSAT's internal
/// `SAT=1` / `UNSAT=0`.
const EXIT_SAT: u8 = 10;
const EXIT_UNSAT: u8 = 20;
const EXIT_UNKNOWN: u8 = 0;

#[derive(Debug, Parser)]
#[command(
    name = "trust_cg_sat",
    version,
    about = "SAT-Competition-compliant solver wrapping trampolined MicroSAT \
             with the trust-cg JIT BCP shadow.",
    long_about = "Run as:\n  \
                  trust_cg_sat <instance.cnf> [proof.drat]\n\
                  trust_cg_sat <instance.cnf> --proof proof.drat\n\n\
                  Exit codes: 10 = SATISFIABLE, 20 = UNSATISFIABLE, \
                  0 = UNKNOWN."
)]
struct Args {
    /// Path to the DIMACS CNF instance.
    cnf: PathBuf,

    /// Optional path for the DRAT UNSAT proof. May also be supplied
    /// via `--proof`. If both are given the explicit `--proof` flag
    /// takes precedence.
    proof_positional: Option<PathBuf>,

    /// DRAT UNSAT proof output path.
    #[arg(long = "proof", value_name = "PATH")]
    proof: Option<PathBuf>,

    /// Engage `SHADOW_MODE`: run the JIT BCP kernel as a differential
    /// check alongside MicroSAT's native propagate. Mutually exclusive
    /// with `--primary-jit`.
    #[arg(long)]
    shadow: bool,

    /// Engage `PRIMARY_JIT_MODE`: surface the JIT BCP kernel's verdict
    /// as the primary propagate return value where epoch-0 authority
    /// rules permit. Mutually exclusive with `--shadow`.
    #[arg(long = "primary-jit")]
    primary_jit: bool,

    /// Which JIT BCP kernel `--shadow` / `--primary-jit` build.
    /// Defaults to `watched-literal`, which uses the same algorithm as
    /// the native baseline. The `scan` and `with-decisions` kernels remain for
    /// differential testing.
    #[arg(
        long = "jit-kernel",
        value_name = "KIND",
        default_value = "watched-literal",
        value_parser = parse_jit_kernel_choice,
    )]
    jit_kernel: u8,

    /// Suppress `c ` informational comment lines on stdout.
    #[arg(long)]
    quiet: bool,

    /// Enable hot-path diagnostic `eprintln!`s in the propagate
    /// dispatcher (epoch-fallback, buffer-overflow, per-call
    /// divergence). Off by default because the per-call messages can
    /// fire thousands of times per learning-heavy solve and drown
    /// stderr; only flip this on when investigating a JIT regression.
    /// One-shot diagnostics (initial JIT compile failure, the first
    /// divergence) are always emitted regardless of this flag.
    #[arg(long)]
    verbose: bool,
}

/// Parse `--jit-kernel <KIND>` into the numeric tag accepted by
/// `JIT_KERNEL_CHOICE`. Mirrors the parser in `bcp_matrix` so the two
/// binaries accept identical spellings.
fn parse_jit_kernel_choice(raw: &str) -> Result<u8, String> {
    match raw {
        "scan" => Ok(JIT_KERNEL_SCAN),
        "with-decisions" => Ok(JIT_KERNEL_WITH_DECISIONS),
        "watched-literal" => Ok(JIT_KERNEL_WATCHED_LITERAL),
        other => Err(format!(
            "unknown --jit-kernel value {other:?}; expected one of \
             scan | with-decisions | watched-literal"
        )),
    }
}

/// Human-readable label for the numeric kernel tag, for the
/// `c mode:` comment line.
fn jit_kernel_label(choice: u8) -> &'static str {
    match choice {
        JIT_KERNEL_SCAN => "scan",
        JIT_KERNEL_WITH_DECISIONS => "with-decisions",
        JIT_KERNEL_WATCHED_LITERAL => "watched-literal",
        _ => "unknown",
    }
}

fn main() -> ExitCode {
    let args = Args::parse();
    match run(args) {
        Ok(code) => ExitCode::from(code),
        Err(err) => {
            // Write the error as a SAT-Comp comment line so a harness
            // that captures stdout still sees it; mirror onto stderr
            // for humans.
            let msg = format!("c trust_cg_sat: error: {err}");
            println!("{msg}");
            eprintln!("{msg}");
            // UNKNOWN exit per SAT-Comp contract: anything other than
            // 10 or 20 means "no answer."
            ExitCode::from(EXIT_UNKNOWN)
        }
    }
}

#[derive(Debug)]
struct CliError(String);

impl std::fmt::Display for CliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<io::Error> for CliError {
    fn from(err: io::Error) -> Self {
        CliError(err.to_string())
    }
}

fn run(args: Args) -> Result<u8, CliError> {
    if args.shadow && args.primary_jit {
        return Err(CliError(
            "--shadow and --primary-jit are mutually exclusive".into(),
        ));
    }

    if !args.cnf.exists() {
        return Err(CliError(format!(
            "CNF file does not exist: {}",
            args.cnf.display()
        )));
    }
    // Reject obviously unsupported gzip inputs early with a clear
    // message so a SAT-Comp harness operator gets actionable output
    // rather than a parse error from MicroSAT (which would `exit(1)`
    // and look like a crash). `.cnf.gz` support is filed as a stretch
    // goal in `benchmarks/benchmark_study.md`.
    if args
        .cnf
        .extension()
        .and_then(|s| s.to_str())
        .map(|s| s.eq_ignore_ascii_case("gz"))
        .unwrap_or(false)
    {
        return Err(CliError(format!(
            "gzip-compressed inputs are not supported in this build: {}",
            args.cnf.display()
        )));
    }

    let proof_path = args.proof.clone().or_else(|| args.proof_positional.clone());

    let mut stdout = io::stdout().lock();
    let comment = |s: &str, stdout: &mut io::StdoutLock<'_>| -> io::Result<()> {
        if !args.quiet {
            writeln!(stdout, "c {s}")?;
        }
        Ok(())
    };

    comment(
        &format!("trust_cg_sat version {}", env!("CARGO_PKG_VERSION")),
        &mut stdout,
    )?;
    comment(&format!("input: {}", args.cnf.display()), &mut stdout)?;
    let kernel_name = jit_kernel_label(args.jit_kernel);
    if args.shadow {
        comment(&format!("mode: shadow-jit ({kernel_name})"), &mut stdout)?;
    } else if args.primary_jit {
        comment(&format!("mode: primary-jit ({kernel_name})"), &mut stdout)?;
    } else {
        comment("mode: native (trampolined MicroSAT, no JIT)", &mut stdout)?;
    }
    if let Some(p) = &proof_path {
        comment(&format!("drat proof: {}", p.display()), &mut stdout)?;
    }

    // Configure mode flags. The propagate module's static atomics are
    // process-global; this binary owns the whole process so we set
    // them once and rely on `disable_drat_output` + atomic restores in
    // the cleanup path below. `JIT_KERNEL_CHOICE` defaults to the
    // watched-literal kernel; we still swap explicitly so a value
    // left over from a previous in-process run (unit-test embedding,
    // hypothetical library use) does not leak in.
    let prior_shadow = SHADOW_MODE.swap(args.shadow, Ordering::SeqCst);
    let prior_primary = PRIMARY_JIT_MODE.swap(args.primary_jit, Ordering::SeqCst);
    let prior_kernel = JIT_KERNEL_CHOICE.swap(args.jit_kernel, Ordering::SeqCst);
    let prior_verbose = TRUST_CG_PROPAGATE_VERBOSE.swap(args.verbose, Ordering::SeqCst);

    if let Some(p) = &proof_path {
        enable_drat_output(p).map_err(|e| {
            CliError(format!(
                "could not open DRAT proof file {}: {e}",
                p.display()
            ))
        })?;
    }

    // Snapshot telemetry counters so we can report deltas attributable
    // to this solve rather than the cumulative process totals (which
    // are 0 on a fresh invocation but matter if this code is ever
    // embedded in a longer-lived host).
    let propagate_calls_before = PROPAGATE_CALL_COUNT.load(Ordering::SeqCst);
    let divergences_before = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst);
    let jit_inits_before = JIT_INIT_COUNT.load(Ordering::SeqCst);
    let jit_primary_before = JIT_PRIMARY_RETURNS.load(Ordering::SeqCst);
    let jit_successful_before = JIT_SUCCESSFUL_RUNS.load(Ordering::SeqCst);

    // SAFETY justification covered at the call site below.
    let mut solver: MaybeUninit<sys::solver> = MaybeUninit::uninit();
    let c_path = CString::new(args.cnf.to_string_lossy().into_owned())
        .map_err(|e| CliError(format!("CNF path has interior NUL: {e}")))?;

    // SAFETY: `parse` itself calls `initCDCL`, which initialises every
    // field of `*solver` it reads before returning. Passing an
    // uninitialised `solver` matches how MicroSAT's own `main` builds
    // it on the stack. The cast on `c_path.as_ptr()` is sound because
    // MicroSAT's `parse` reads the filename via `fopen` and never
    // writes through the pointer despite the non-const signature.
    let parse_rc = unsafe {
        sys::parse(
            solver.as_mut_ptr(),
            c_path.as_ptr() as *mut std::os::raw::c_char,
        )
    };

    let solve_rc = if parse_rc == sys::UNSAT {
        comment("parse short-circuited to UNSAT", &mut stdout)?;
        sys::UNSAT
    } else {
        // SAFETY: `parse` returned without UNSAT, meaning it ran
        // `initCDCL` and populated the solver state. Calling `solve`
        // on that state is exactly the upstream usage in microsat.c's
        // `main`.
        unsafe { sys::solve(solver.as_mut_ptr()) }
    };

    // Flush any buffered DRAT before we read the file or exit.
    if proof_path.is_some()
        && let Err(e) = flush_drat_output()
    {
        comment(&format!("WARNING: drat flush failed: {e}"), &mut stdout)?;
    }
    disable_drat_output();

    // Emit telemetry comments before the result line so a parser that
    // greps `^s ` still works. SAT-Comp parsers ignore unknown `c`
    // lines.
    let propagate_calls_delta =
        PROPAGATE_CALL_COUNT.load(Ordering::SeqCst) - propagate_calls_before;
    comment(
        &format!("propagate_calls={propagate_calls_delta}"),
        &mut stdout,
    )?;
    if args.shadow || args.primary_jit {
        let jit_inits_delta = JIT_INIT_COUNT.load(Ordering::SeqCst) - jit_inits_before;
        let divergences_delta = JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst) - divergences_before;
        let jit_primary_delta = JIT_PRIMARY_RETURNS.load(Ordering::SeqCst) - jit_primary_before;
        let jit_successful_delta =
            JIT_SUCCESSFUL_RUNS.load(Ordering::SeqCst) - jit_successful_before;
        comment(&format!("jit_init_count={jit_inits_delta}"), &mut stdout)?;
        comment(&format!("jit_divergences={divergences_delta}"), &mut stdout)?;
        comment(
            &format!("jit_primary_returns={jit_primary_delta}"),
            &mut stdout,
        )?;
        comment(
            &format!("jit_successful_runs={jit_successful_delta}"),
            &mut stdout,
        )?;
    }

    // Restore prior mode flags so this function leaves no global side
    // effects beyond the result on stdout.
    SHADOW_MODE.store(prior_shadow, Ordering::SeqCst);
    PRIMARY_JIT_MODE.store(prior_primary, Ordering::SeqCst);
    JIT_KERNEL_CHOICE.store(prior_kernel, Ordering::SeqCst);
    TRUST_CG_PROPAGATE_VERBOSE.store(prior_verbose, Ordering::SeqCst);

    // SAT-Comp exit-code translation table:
    //   MicroSAT `sys::SAT (=1)`   -> "s SATISFIABLE",   exit 10
    //   MicroSAT `sys::UNSAT (=0)` -> "s UNSATISFIABLE", exit 20
    //   anything else              -> "s UNKNOWN",       exit 0
    //
    // (This intentionally differs from MicroSAT's own return codes,
    // which a SAT-Comp harness would mis-read as "no answer.")
    let final_code = match solve_rc {
        x if x == sys::SAT => {
            writeln!(stdout, "s SATISFIABLE")?;
            // SAFETY: `parse` did not short-circuit, so `solver` is
            // fully initialised; we hold the only mutable reference to
            // it for the rest of this function.
            let model = unsafe { extract_model(solver.as_mut_ptr()) };
            emit_model_lines(&mut stdout, &model)?;
            EXIT_SAT
        }
        x if x == sys::UNSAT => {
            writeln!(stdout, "s UNSATISFIABLE")?;
            EXIT_UNSAT
        }
        other => {
            comment(
                &format!("unexpected MicroSAT return code {other}; reporting UNKNOWN"),
                &mut stdout,
            )?;
            writeln!(stdout, "s UNKNOWN")?;
            EXIT_UNKNOWN
        }
    };

    stdout.flush()?;
    Ok(final_code)
}

/// Walk MicroSAT's solver state after a SAT verdict and produce a
/// satisfying assignment for every variable in `1..=nVars`.
///
/// MicroSAT does not expose a "print model" function; we mirror the
/// information available in its solver state:
///
///   * `S->false_[v]` non-zero ⇒ literal `+v` is assigned false ⇒
///     variable `v` is `false`.
///   * `S->false_[-v]` non-zero ⇒ literal `-v` is assigned false ⇒
///     variable `v` is `true`.
///   * Otherwise the variable is unassigned at the moment `solve`
///     returned SAT; SAT-Comp accepts any extension, so we fall back
///     to the phase-saved value in `S->model[v]` (true if non-zero,
///     false otherwise). This matches MicroSAT's own phase-saving
///     convention.
///
/// Returns a vector of length `nVars`, indexed by `v - 1`, where each
/// entry is `true` if `v` is satisfied, `false` if it is falsified.
///
/// # Safety
///
/// `s` must point to a fully initialised `sys::solver` produced by
/// `parse` and then `solve` returning `sys::SAT`. The function reads
/// `nVars`, `false_`, and `model`; it performs no writes.
unsafe fn extract_model(s: *mut sys::solver) -> Vec<bool> {
    // SAFETY: precondition - `s` is live and post-solve. Reading the
    // scalar `nVars` and the (`nVars` + 1)-length `false_` / `model`
    // tables is sound under that precondition.
    let solver_ref = unsafe { &*s };
    let nvars = solver_ref.nVars as usize;
    let false_arr = solver_ref.false_;
    let model_arr = solver_ref.model;
    let mut model: Vec<bool> = Vec::with_capacity(nvars);
    for v in 1..=nvars as i32 {
        // SAFETY: `false_` was offset by `n` inside `initCDCL` so it
        // is valid for indices in `[-n, n]`. `model` is allocated
        // `n+1` ints (indices `0..=n`). Both pointers are non-null
        // post-`initCDCL`.
        let pos = unsafe { *false_arr.offset(v as isize) };
        let neg = unsafe { *false_arr.offset(-(v as isize)) };
        let phase = unsafe { *model_arr.offset(v as isize) };
        let value = if neg != 0 {
            // `-v` is false ⇒ `v` is true.
            true
        } else if pos != 0 {
            // `+v` is false ⇒ `v` is false.
            false
        } else {
            // Free variable: report phase-saved value (any extension
            // is a model).
            phase != 0
        };
        model.push(value);
    }
    model
}

/// Print SAT-Comp `v` lines, terminated by ` 0`. Wraps at ~10
/// literals per line to keep individual lines comfortably under any
/// downstream tool's line-buffer limit, while staying within the
/// SAT-Comp spec (multiple `v` lines are concatenated and must end
/// with a `0` after the final literal).
fn emit_model_lines(out: &mut io::StdoutLock<'_>, model: &[bool]) -> io::Result<()> {
    const PER_LINE: usize = 10;
    if model.is_empty() {
        writeln!(out, "v 0")?;
        return Ok(());
    }
    let mut written_on_line: usize = 0;
    for (i, &val) in model.iter().enumerate() {
        if written_on_line == 0 {
            out.write_all(b"v")?;
        }
        let var = (i as i32) + 1;
        let lit = if val { var } else { -var };
        write!(out, " {lit}")?;
        written_on_line += 1;
        let is_last = i + 1 == model.len();
        if is_last {
            // Final literal on the final line: append ` 0` then
            // newline.
            out.write_all(b" 0\n")?;
        } else if written_on_line >= PER_LINE {
            out.write_all(b"\n")?;
            written_on_line = 0;
        }
    }
    Ok(())
}

// End-to-end behaviour is covered by
// `crates/trust-cg-sat-host/tests/trust_cg_sat_cli.rs`, which exercises
// every flag and the SAT-Comp invocation contract as a subprocess
// (stdout / exit-code / DRAT artefacts). `emit_model_lines` is
// awkward to unit-test in isolation because it takes a `StdoutLock`
// that is not constructible without a real stdout; the integration
// tests cover the formatting path directly via the binary's stdout.
