// trust-cg-test — unified test and verification CLI entry point.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This binary is the repository entry point for the WS1-WS9 test workstreams.
//
// Design rules enforced here:
//   * One CLI surface; maintained script-backed runners stay behind it.
//   * Implemented subcommands document their command-specific outputs.
//     Planned subcommands fail explicitly without invoking tools or writing.
//   * Exit codes map to `ResultStatus` (sysexits.h aligned). See
//     `results::ResultStatus`.
//
// Keep new subcommands self-describing through `--help` and typed output.

#![deny(missing_docs)]
#![deny(clippy::pedantic)]
#![deny(warnings)]
#![allow(clippy::module_name_repetitions)]
// Doc strings intentionally carry natural prose (subcommand help text).
// Backticking every product name (YARPGen, JUnit, SingleSource, MIR) in
// operator-facing `--help` output is worse UX than the lint suggests.
#![allow(clippy::doc_markdown)]
// `match` expressions with a single arm that binds make the intent clearer
// than `if let` in several of this crate's dispatch sites. Allow both.
#![allow(clippy::single_match_else)]
#![allow(clippy::needless_pass_by_value)]
#![allow(clippy::missing_errors_doc)]
#![allow(clippy::missing_panics_doc)]
#![allow(clippy::format_push_string)]
#![allow(clippy::too_many_lines)]
#![allow(clippy::unnecessary_wraps)]
#![allow(clippy::ref_option)]
#![allow(clippy::map_unwrap_or)]
#![allow(clippy::match_same_arms)]
#![allow(clippy::manual_contains)]
#![allow(clippy::collapsible_if)]
// The skeleton exposes APIs that WS1-WS9 will call in follow-up PRs.
// They appear unused here; allow that explicitly rather than littering
// the code with per-item `#[allow]`.
#![allow(dead_code)]

//! Unified test and verification CLI for Trust Codegen.
//!
//! Run `trust-cg-test --help` for the command tree. Common controls include
//! `--format {human,json,junit}`, `-o/--out`, `--timeout`, `--parallel`,
//! `-q/--quiet`, `-v/--verbose`, `--no-cache`, and `--dry-run`.

use std::process::ExitCode;

use clap::{Parser, Subcommand, ValueEnum};
use tracing_subscriber::EnvFilter;

mod cmd;
mod config;
mod corpus;
mod external;
mod progress;
mod results;
mod shell;

use results::ResultStatus;

/// Output format for result-emitting subcommands.
#[derive(Clone, Copy, Debug, ValueEnum, Default)]
#[value(rename_all = "lower")]
pub enum OutputFormat {
    /// Pretty table + narrative, targeted at humans.
    #[default]
    Human,
    /// Machine-readable JSON.
    Json,
    /// JUnit XML for CI consumers.
    Junit,
}

/// Top-level `trust-cg-test` CLI.
#[derive(Parser, Debug)]
#[command(
    name = "trust-cg-test",
    version,
    about = "Unified test and verification CLI for Trust Codegen",
    long_about = "Repository test, fuzz, and proof workflows behind one CLI. \
                  Implemented commands delegate to maintained script-backed \
                  runners; planned commands return an explicit not-implemented \
                  status. Use each subcommand's `--help` for its current \
                  requirements and examples. Generic JSON building-block \
                  schemas are committed under `evals/schema/`; command-specific \
                  JSON shapes remain unstable in v0.1.0.\n\n\
                  # Examples\n\n  \
                  trust-cg-test matrix --format human\n  \
                  trust-cg-test doctor --for fuzz\n  \
                  trust-cg-test report --out reports/weekly/2026-04-19.md"
)]
pub struct Cli {
    /// Output format (human, json, junit).
    #[arg(short = 'f', long, value_enum, default_value_t = OutputFormat::Human, global = true)]
    pub format: OutputFormat,

    /// Override the command-specific output file or directory.
    ///
    /// See the selected subcommand's help for its output type and default.
    #[arg(short = 'o', long, value_name = "PATH", global = true)]
    pub out: Option<std::path::PathBuf>,

    /// Per-unit timeout in seconds. Subcommands may apply per-unit
    /// defaults when this is unset.
    #[arg(long, value_name = "SECS", global = true)]
    pub timeout: Option<u64>,

    /// Worker count (honors cargo-serialization lock). Default: auto.
    #[arg(long, value_name = "N", global = true)]
    pub parallel: Option<usize>,

    /// Suppress progress bars; errors still go to stderr.
    #[arg(short = 'q', long, global = true)]
    pub quiet: bool,

    /// Show debug-level events. Repeat for more: -vv, -vvv.
    #[arg(short = 'v', long, action = clap::ArgAction::Count, global = true)]
    pub verbose: u8,

    /// Ignore proof / corpus caches.
    #[arg(long, global = true)]
    pub no_cache: bool,

    /// Print what would run without executing external tools.
    #[arg(long, global = true)]
    pub dry_run: bool,

    /// Subcommand.
    #[command(subcommand)]
    pub command: Command,
}

/// Every workstream's entry point; each variant's help states its current scope.
#[derive(Subcommand, Debug)]
pub enum Command {
    /// WS1 — Run the workspace unit/integration test matrix.
    #[command(
        long_about = "Run the workspace unit/integration test matrix (WS1).\n\n\
                      Delegates to the maintained full matrix runner in \
                      `scripts/run_full_test_matrix.sh`. Writes \
                      `evals/results/tests/<iso-date>.json` with per-crate \
                      `{passed, failed, ignored, time_s}`. Regular-test or rustdoc \
                      ignored counts and failed/timeout/incomplete shards make the CLI \
                      return exit 1.\n\n\
                      # Examples\n\n  \
                      trust-cg-test matrix --format human\n  \
                      trust-cg-test matrix --crate trust-cg-codegen --shard integration-jit-runtime --format json\n  \
                      trust-cg-test matrix --compare path/to/tests-baseline.json"
    )]
    Matrix(cmd::matrix::MatrixArgs),

    /// Planned WS2 llvm-test-suite runner (not implemented in v0.1.0).
    #[command(
        long_about = "Planned external llvm-test-suite SingleSource runner (WS2).\n\n\
                      This command is not implemented in trust-cg 0.1.0. It exits \
                      2 without invoking tools, cloning a corpus, or writing a \
                      result artifact. Its options are reserved for a future release."
    )]
    Suite(cmd::suite::SuiteArgs),

    /// Planned WS3 differential-fuzzing dispatcher (not implemented in v0.1.0).
    #[command(long_about = "Planned differential-fuzzing dispatcher (WS3).\n\n\
                      This command is not implemented in trust-cg 0.1.0. It exits \
                      2 without generating programs, invoking tools, filing \
                      issues, or writing a result artifact. Its options are \
                      reserved for a future release.")]
    Fuzz(cmd::fuzz::FuzzArgs),

    /// WS4 — Drive `rustc_codegen_trust_cg` + rustc UI tests.
    #[command(
        long_about = "Drive `rustc_codegen_trust_cg` + rustc UI tests (WS4).\n\n\
                      `rustc smoke` sanity-compiles `hello.rs`. `rustc ui` runs \
                      the full UI harness and writes a per-test JSON record. \
                      `rustc feature-coverage` reports which rustc-MIR opcodes \
                      the adapter currently translates.\n\n\
                      # Examples\n\n  \
                      trust-cg-test rustc smoke\n  \
                      trust-cg-test rustc ui --format json --out evals/results/rustc/2026-04-19.json\n  \
                      trust-cg-test rustc feature-coverage --format human"
    )]
    Rustc(cmd::rustc::RustcArgs),

    /// Planned WS5 rustc bootstrap driver (not implemented in v0.1.0).
    #[command(long_about = "Planned rustc bootstrap driver (WS5).\n\n\
                      This command is not implemented in trust-cg 0.1.0. It exits \
                      2 without invoking `x.py`, reading a rustc checkout, or \
                      writing a result artifact. Its options are reserved for a \
                      future release.")]
    Bootstrap(cmd::bootstrap::BootstrapArgs),

    /// Planned WS6 crates.io smoke runner (not implemented in v0.1.0).
    #[command(long_about = "Planned crates.io smoke runner (WS6).\n\n\
                      This command is not implemented in trust-cg 0.1.0. It exits \
                      2 without fetching crates, invoking Cargo, modifying a \
                      cache, or writing a result artifact. Its options are \
                      reserved for a future release.")]
    Ecosystem(cmd::ecosystem::EcosystemArgs),

    /// Planned WS7 AY proof dispatcher (not implemented in v0.1.0).
    #[command(long_about = "Planned AY lowering-obligation dispatcher (WS7).\n\n\
                      This command is not implemented in trust-cg 0.1.0. It exits \
                      2 without invoking AY, reading a proof cache, or writing a \
                      result artifact. Its options are reserved for a future \
                      release.")]
    Prove(cmd::prove::ProveArgs),

    /// Planned WS8 non-ISel proof dispatcher (not implemented in v0.1.0).
    #[command(long_about = "Planned non-ISel proof dispatcher (WS8).\n\n\
                      The register-allocation, scheduling, and object-emission \
                      stages are not implemented in this CLI in trust-cg 0.1.0. \
                      Every stage exits 2 without invoking tools or writing a \
                      result artifact.")]
    Pipeline(cmd::pipeline::PipelineArgs),

    /// WS9 — Generate weekly report + dashboard.
    #[command(long_about = "Generate the weekly Trust Codegen dashboard (WS9).\n\n\
                      Reads the newest compatible JSON recursively from each \
                      known workstream result directory, renders the north-star \
                      table and per-workstream sections, and marks missing data \
                      with `—`. Writes `reports/weekly/<iso-date>.md` by default.\n\n\
                      # Examples\n\n  \
                      trust-cg-test report\n  \
                      trust-cg-test report --week 2026-04-19 --format human\n  \
                      trust-cg-test report --out /tmp/weekly.md")]
    Report(cmd::report::ReportArgs),

    /// Generate Phase 3 JIT diagnostic dashboard exports from fixtures.
    #[command(
        name = "jit-diagnostic-dashboard",
        long_about = "Generate Phase 3 JIT diagnostic dashboard exports from \
                      checked-in fixtures.\n\n\
                      This is a fixture-only exporter for #711. It reads the \
                      #710 status matrix, #703 replay bundle decisions, #704 \
                      verifier rejection metadata, and #706 proof/TV outcome \
                      rows, then writes deterministic dashboard JSON and \
                      Markdown artifacts without invoking live Phase 6 CI.\n\n\
                      # Examples\n\n  \
                      trust-cg-test jit-diagnostic-dashboard\n  \
                      trust-cg-test jit-diagnostic-dashboard --format json\n  \
                      trust-cg-test jit-diagnostic-dashboard --input-dir tests/fixtures/jit_diagnostic_dashboard"
    )]
    JitDiagnosticDashboard(cmd::jit_diagnostic_dashboard::JitDiagnosticDashboardArgs),

    /// Run ratchet checks (called by CI).
    #[command(long_about = "Run ratchet checks (called by CI). Every ratchet fails \
                      with a non-zero exit code when its invariant is \
                      violated.\n\n\
                      # Examples\n\n  \
                      trust-cg-test ratchet shell-isolation\n  \
                      trust-cg-test ratchet schema --format json\n  \
                      trust-cg-test ratchet tests --baseline path/to/tests-baseline.json\n  \
                      trust-cg-test ratchet warnings\n  \
                      trust-cg-test ratchet unwrap\n  \
                      trust-cg-test ratchet lint-linux")]
    Ratchet(cmd::ratchet::RatchetArgs),

    /// Check environment for required tools.
    #[command(long_about = "Check the local environment for tools and reference \
                      corpora used by `trust-cg-test`. Prints a table for \
                      `--format human`, a structured JSON report for \
                      `--format json`. Exits 0 when every *required* tool \
                      for the given `--for` target is present, 2 otherwise.\n\n\
                      # Examples\n\n  \
                      trust-cg-test doctor\n  \
                      trust-cg-test doctor --for fuzz --format json\n  \
                      trust-cg-test doctor --for matrix")]
    Doctor(cmd::doctor::DoctorArgs),

    /// Cross-compile check for Linux `#[cfg(target_os = "linux")]` paths
    /// in `trust-cg-codegen` (issue #346). Safe on macOS-only boxes — targets
    /// not installed via `rustup target add` are reported as `skipped`.
    #[command(
        long_about = "Cross-compile check for the Linux `#[cfg(target_os = \"linux\")]` \
                      paths in trust-cg-codegen. Runs `cargo check --target <T> -p <P>` \
                      for each installed Linux target. Missing targets are skipped \
                      (they are environmental, not a failure) so this subcommand is \
                      safe to wire into CI on macOS-only developer boxes.\n\n\
                      Installed targets are discovered via `rustup target list \
                      --installed`. Install one with e.g. \
                      `rustup target add x86_64-unknown-linux-gnu`.\n\n\
                      Exit codes:\n  \
                      0 — every installed target compiled (or all targets skipped).\n  \
                      1 — at least one installed target failed to compile.\n  \
                      2 — cargo missing from PATH.\n\n\
                      # Examples\n\n  \
                      trust-cg-test lint-linux\n  \
                      trust-cg-test lint-linux --format json\n  \
                      trust-cg-test lint-linux --target x86_64-unknown-linux-gnu\n  \
                      trust-cg-test lint-linux --package trust-cg-codegen --package trust-cg-ir"
    )]
    LintLinux(cmd::lint_linux::LintLinuxArgs),
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    init_tracing(cli.verbose, cli.quiet);
    match run(cli) {
        Ok(status) => ExitCode::from(status.exit_code()),
        Err(err) => {
            eprintln!("trust-cg-test: error: {err:#}");
            ExitCode::from(ResultStatus::Errored.exit_code())
        }
    }
}

fn init_tracing(verbose: u8, quiet: bool) {
    let filter = match (quiet, verbose) {
        (true, _) => EnvFilter::new("error"),
        (_, 0) => EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info")),
        (_, 1) => EnvFilter::new("debug"),
        _ => EnvFilter::new("trace"),
    };
    // Subscriber init can only fail if one is already installed, which
    // cannot happen here because `main` runs exactly once.
    let _ = tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_env_filter(filter)
        .try_init();
}

fn run(cli: Cli) -> anyhow::Result<ResultStatus> {
    let global = cmd::GlobalArgs {
        format: cli.format,
        out: cli.out,
        timeout: cli.timeout,
        parallel: cli.parallel,
        quiet: cli.quiet,
        verbose: cli.verbose,
        no_cache: cli.no_cache,
        dry_run: cli.dry_run,
    };
    match cli.command {
        Command::Matrix(args) => cmd::matrix::run(&global, &args),
        Command::Suite(args) => cmd::suite::run(&global, &args),
        Command::Fuzz(args) => cmd::fuzz::run(&global, &args),
        Command::Rustc(args) => cmd::rustc::run(&global, &args),
        Command::Bootstrap(args) => cmd::bootstrap::run(&global, &args),
        Command::Ecosystem(args) => cmd::ecosystem::run(&global, &args),
        Command::Prove(args) => cmd::prove::run(&global, &args),
        Command::Pipeline(args) => cmd::pipeline::run(&global, &args),
        Command::Report(args) => cmd::report::run(&global, &args),
        Command::JitDiagnosticDashboard(args) => cmd::jit_diagnostic_dashboard::run(&global, &args),
        Command::Ratchet(args) => cmd::ratchet::run(&global, &args),
        Command::Doctor(args) => cmd::doctor::run(&global, &args),
        Command::LintLinux(args) => cmd::lint_linux::run(&global, &args),
    }
}
