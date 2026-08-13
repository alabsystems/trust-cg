// Subcommand dispatcher for `trust-cg-test`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Per-workstream subcommand modules.
//!
//! Each WS-N workstream's runnable surface lives under `cmd/<ws>.rs`.
//! Stubs here return `ResultStatus::NotImplemented` (exit 2) until the
//! respective workstream fills them in.

use std::path::PathBuf;

use crate::OutputFormat;
use crate::results::ResultStatus;

pub mod bootstrap;
pub mod doctor;
pub mod ecosystem;
pub mod fuzz;
pub mod jit_diagnostic_dashboard;
pub mod lint_linux;
pub mod matrix;
pub mod pipeline;
pub mod prove;
pub mod ratchet;
pub mod report;
pub mod rustc;
pub mod suite;

/// Global arguments present on every subcommand. Built from the
/// top-level `Cli` struct in `main.rs` and passed to each `run()`.
#[derive(Clone, Debug)]
pub struct GlobalArgs {
    /// Output format for the human-facing view and the exit-code story.
    pub format: OutputFormat,
    /// Command-specific output file or directory override.
    pub out: Option<PathBuf>,
    /// Per-unit timeout override, in seconds.
    pub timeout: Option<u64>,
    /// Worker count override.
    pub parallel: Option<usize>,
    /// Suppress progress bars.
    pub quiet: bool,
    /// Verbosity counter (0 = info, 1 = debug, 2+ = trace).
    pub verbose: u8,
    /// Ignore caches for this run.
    pub no_cache: bool,
    /// Print-only; do not invoke external tools.
    pub dry_run: bool,
}

impl GlobalArgs {
    /// Is JSON output requested?
    #[must_use]
    pub fn is_json(&self) -> bool {
        matches!(self.format, OutputFormat::Json | OutputFormat::Junit)
    }
}

/// Default "not yet implemented" path used by WS1-WS9 stubs.
///
/// Prints a self-contained status and returns `ResultStatus::NotImplemented`
/// (exit 2).
pub(crate) fn not_yet_implemented(cmd: &str) -> anyhow::Result<ResultStatus> {
    eprintln!(
        "subcommand `{cmd}` is not implemented in trust-cg 0.1.0; run \
         `trust-cg-test {cmd} --help` for the current scope"
    );
    Ok(ResultStatus::NotImplemented)
}
