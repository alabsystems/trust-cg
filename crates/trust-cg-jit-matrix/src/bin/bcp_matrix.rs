// bcp_matrix.rs - DIMACS-driven BCP kernel runner.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::PathBuf;
use std::process::ExitCode;
use std::str::FromStr;
use std::time::Instant;

use clap::Parser;
use serde::Serialize;
use serde_json::json;

use trust_cg_jit_matrix::bcp_baseline::BcpState;
use trust_cg_jit_matrix::bcp_kernel::{
    BCP_RESULT_CONFLICT, BCP_RESULT_DECODE_ERROR, BCP_RESULT_OK, BcpKernelProvider,
};
use trust_cg_jit_matrix::dimacs::{DimacsError, read_dimacs_cnf_file};
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
use trust_cg_jit_matrix::jit_bcp_kernel::{
    JitBcpKernelProvider, JitBcpWatchedLiteralKernelProvider, JitBcpWithDecisionsProvider,
};
use trust_cg_jit_matrix::solver_kernel_abi::SolverKernelHandle;

const DEFAULT_DECISIONS: u32 = 100;
const DEFAULT_SEED: u64 = 0xC0FFEE;

/// Which JIT'd BCP kernel `bcp_matrix --jit` engages. The default is
/// `WatchedLiteral` because it uses the same watched-literal algorithm as the
/// native baseline. The older `Scan` (single-shot) and `WithDecisions` kernels
/// remain selectable for differential testing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum JitKernelChoice {
    Scan,
    WithDecisions,
    WatchedLiteral,
}

impl JitKernelChoice {
    fn as_str(self) -> &'static str {
        match self {
            JitKernelChoice::Scan => "scan",
            JitKernelChoice::WithDecisions => "with-decisions",
            JitKernelChoice::WatchedLiteral => "watched-literal",
        }
    }
}

impl FromStr for JitKernelChoice {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "scan" => Ok(JitKernelChoice::Scan),
            "with-decisions" => Ok(JitKernelChoice::WithDecisions),
            "watched-literal" => Ok(JitKernelChoice::WatchedLiteral),
            other => Err(format!(
                "unknown --jit-kernel value {other:?}; expected one of \
                 scan | with-decisions | watched-literal"
            )),
        }
    }
}

#[derive(Debug, Parser)]
#[command(
    name = "bcp_matrix",
    about = "Run BCP against a DIMACS CNF through the SolverKernelProvider ABI",
    long_about = "Loads a DIMACS .cnf file, builds a BcpState, exposes it via the \
SolverKernelProvider ABI, and feeds a pseudo-random sequence of decision literals \
(xorshift-seeded) through one kernel call. Emits a single JSON object on stdout."
)]
struct Args {
    #[arg(long)]
    input: PathBuf,

    #[arg(long, default_value_t = DEFAULT_DECISIONS)]
    decisions: u32,

    #[arg(long, default_value_t = DEFAULT_SEED)]
    seed: u64,

    /// Run the JIT'd BCP kernel rather than the native Rust baseline.
    /// When set without `--jit-kernel`, the watched-literal kernel
    /// is engaged.
    #[arg(long, default_value_t = false)]
    jit: bool,

    /// Which JIT'd BCP kernel to use when `--jit` is set. Defaults to
    /// `watched-literal` (the apples-to-apples headline kernel). The
    /// other choices are kept reachable for differential testing.
    #[arg(
        long = "jit-kernel",
        value_name = "KIND",
        default_value = "watched-literal",
        value_parser = JitKernelChoice::from_str,
    )]
    jit_kernel: JitKernelChoice,
}

#[derive(Debug, Serialize)]
struct BcpReport {
    input: String,
    num_vars: usize,
    num_clauses: usize,
    decisions_fed: u32,
    result_code: u32,
    result_label: &'static str,
    propagation_counter: u32,
    elapsed_us: u128,
    jit: bool,
    /// Name of the JIT kernel used. When `jit == false`, this is
    /// `"native"` to keep the field shape stable across runs (older
    /// readers can still treat `jit` as the on/off knob).
    jit_kernel: &'static str,
}

fn main() -> ExitCode {
    let args = Args::parse();
    match run(&args) {
        Ok(code) => code,
        Err(err) => {
            let payload = json!({
                "input": args.input.display().to_string(),
                "error": err.kind,
                "message": err.message,
            });
            match serde_json::to_string_pretty(&payload) {
                Ok(text) => println!("{text}"),
                Err(_) => println!(
                    "{{\"input\":\"{}\",\"error\":\"{}\",\"message\":\"{}\"}}",
                    args.input.display(),
                    err.kind,
                    err.message.replace('"', "\\\"")
                ),
            }
            ExitCode::from(err.exit_code)
        }
    }
}

struct CliError {
    kind: &'static str,
    message: String,
    exit_code: u8,
}

fn run(args: &Args) -> Result<ExitCode, CliError> {
    let cnf = read_dimacs_cnf_file(&args.input).map_err(|err| match err {
        DimacsError::IoError(io_err) => CliError {
            kind: "io_error",
            message: io_err.to_string(),
            exit_code: 1,
        },
        other => CliError {
            kind: "parse_error",
            message: other.to_string(),
            exit_code: 1,
        },
    })?;

    let num_vars = cnf.num_vars;
    let num_clauses = cnf.clauses.len();

    let input_buf = if num_vars == 0 {
        Vec::new()
    } else {
        generate_decisions(num_vars, args.decisions, args.seed)
    };
    let decisions_fed = input_buf.len() as u32;

    let (status, elapsed_us, kernel_label) = if args.jit {
        let (status, elapsed_us) = run_jit(num_vars, cnf.clauses, &input_buf, args.jit_kernel)?;
        (status, elapsed_us, args.jit_kernel.as_str())
    } else {
        let (status, elapsed_us) = run_native(num_vars, cnf.clauses, &input_buf);
        (status, elapsed_us, "native")
    };

    let (label, exit) = match status.result {
        BCP_RESULT_OK => ("ok", ExitCode::SUCCESS),
        BCP_RESULT_CONFLICT => ("conflict", ExitCode::SUCCESS),
        BCP_RESULT_DECODE_ERROR => ("decode_error", ExitCode::from(2)),
        _ => ("decode_error", ExitCode::from(2)),
    };

    let report = BcpReport {
        input: args.input.display().to_string(),
        num_vars,
        num_clauses,
        decisions_fed,
        result_code: status.result,
        result_label: label,
        propagation_counter: status.counters,
        elapsed_us,
        jit: args.jit,
        jit_kernel: kernel_label,
    };

    let text = serde_json::to_string_pretty(&report).map_err(|err| CliError {
        kind: "serialize_error",
        message: err.to_string(),
        exit_code: 1,
    })?;
    println!("{text}");

    Ok(exit)
}

fn run_native(
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
    input_buf: &[u32],
) -> (trust_cg_jit_matrix::solver_kernel_abi::KernelStatus, u128) {
    let mut state = BcpState::new(num_vars, clauses);
    let provider = BcpKernelProvider::new(&mut state);
    let mut handle = SolverKernelHandle::from_provider(&provider);

    let start = Instant::now();
    let status = handle.call(input_buf);
    let elapsed_us = start.elapsed().as_micros();
    (status, elapsed_us)
}

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
fn run_jit(
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
    input_buf: &[u32],
    kernel: JitKernelChoice,
) -> Result<(trust_cg_jit_matrix::solver_kernel_abi::KernelStatus, u128), CliError> {
    match kernel {
        JitKernelChoice::Scan => {
            let provider =
                JitBcpKernelProvider::compile(num_vars, clauses).map_err(|err| CliError {
                    kind: "jit_compile_error",
                    message: err.to_string(),
                    exit_code: 1,
                })?;
            let mut handle = SolverKernelHandle::from_provider(&provider);

            let start = Instant::now();
            let status = handle.call(input_buf);
            let elapsed_us = start.elapsed().as_micros();
            Ok((status, elapsed_us))
        }
        JitKernelChoice::WithDecisions => {
            let trail_capacity_hint = input_buf.len();
            let provider =
                JitBcpWithDecisionsProvider::compile(num_vars, clauses, trail_capacity_hint)
                    .map_err(|err| CliError {
                        kind: "jit_compile_error",
                        message: err.to_string(),
                        exit_code: 1,
                    })?;
            let mut handle = SolverKernelHandle::from_provider(&provider);

            let start = Instant::now();
            let status = handle.call(input_buf);
            let elapsed_us = start.elapsed().as_micros();
            Ok((status, elapsed_us))
        }
        JitKernelChoice::WatchedLiteral => {
            let trail_capacity_hint = input_buf.len();
            let provider =
                JitBcpWatchedLiteralKernelProvider::compile(num_vars, clauses, trail_capacity_hint)
                    .map_err(|err| CliError {
                        kind: "jit_compile_error",
                        message: err.to_string(),
                        exit_code: 1,
                    })?;
            let mut handle = SolverKernelHandle::from_provider(&provider);

            let start = Instant::now();
            let status = handle.call(input_buf);
            let elapsed_us = start.elapsed().as_micros();
            Ok((status, elapsed_us))
        }
    }
}

#[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
fn run_jit(
    _num_vars: usize,
    _clauses: Vec<Vec<i32>>,
    _input_buf: &[u32],
    _kernel: JitKernelChoice,
) -> Result<(trust_cg_jit_matrix::solver_kernel_abi::KernelStatus, u128), CliError> {
    Err(CliError {
        kind: "jit_compile_error",
        message: "host architecture does not support JIT".to_string(),
        exit_code: 1,
    })
}

fn generate_decisions(num_vars: usize, count: u32, seed: u64) -> Vec<u32> {
    let mut state = if seed == 0 {
        0x9E37_79B9_7F4A_7C15
    } else {
        seed
    };
    let mut out = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let r = xorshift64(&mut state);
        let var = ((r % num_vars as u64) as u32) + 1;
        let polarity = (xorshift64(&mut state) & 1) as u32;
        out.push((var << 1) | polarity);
    }
    out
}

fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decisions_are_in_var_range_and_encoded() {
        let decisions = generate_decisions(4, 32, 0xDEADBEEF);
        assert_eq!(decisions.len(), 32);
        for encoded in decisions {
            let var = encoded >> 1;
            assert!((1..=4).contains(&var));
            assert!(encoded & !1 != 0);
        }
    }

    #[test]
    fn deterministic_sequence_for_fixed_seed() {
        let a = generate_decisions(8, 16, 0xC0FFEE);
        let b = generate_decisions(8, 16, 0xC0FFEE);
        assert_eq!(a, b);
    }

    #[test]
    fn jit_kernel_choice_parses_each_variant() {
        assert_eq!(
            "scan".parse::<JitKernelChoice>().expect("scan"),
            JitKernelChoice::Scan
        );
        assert_eq!(
            "with-decisions"
                .parse::<JitKernelChoice>()
                .expect("with-decisions"),
            JitKernelChoice::WithDecisions
        );
        assert_eq!(
            "watched-literal"
                .parse::<JitKernelChoice>()
                .expect("watched-literal"),
            JitKernelChoice::WatchedLiteral
        );
        assert!("bogus".parse::<JitKernelChoice>().is_err());
    }
}
