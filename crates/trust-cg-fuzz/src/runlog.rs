// trust-cg-fuzz/src/runlog.rs - JSON run log schema
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Shared JSON result schema and publication for the fuzz drivers. The campaign script
// (scripts/fuzz_campaign.sh) and WS9 consume this format.

use serde::{Deserialize, Serialize};
use std::io;
use std::path::Path;
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Repro {
    /// PRNG seed or external-tool seed that reproduces this run.
    pub seed: u64,
    /// Path to the minimized input (trust_ir json for trust-ir-gen, .c file for
    /// csmith/yarpgen). None when we couldn't save it.
    pub minimized_input_path: Option<String>,
    /// One-line summary of the defect for humans browsing the log.
    pub summary: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RunLog {
    /// Driver name, including trust-ir-gen, trust-ir-jit-diff, csmith-driver,
    /// and yarpgen-driver.
    pub driver: String,
    /// "ok" | "unavailable".
    pub status: String,
    /// Human-readable reason when `status == "unavailable"` (e.g. which
    /// external tool is missing and how to install it).
    pub reason: Option<String>,
    /// Campaign duration in seconds (requested).
    pub duration_secs: u64,
    /// Number of iterations that actually ran.
    pub runs: u64,
    /// Runs that timed out (per-iteration timeout).
    pub timeouts: u64,
    /// Runs where the compiler or an external tool crashed (panic, non-zero
    /// exit from a phase that shouldn't fail).
    pub crashes: u64,
    /// Runs where the oracle and Trust Codegen disagreed on the result — actual
    /// miscompiles.
    pub miscompiles: u64,
    /// Detailed repros (up to a cap, to keep JSON manageable).
    pub repros: Vec<Repro>,
    /// ISO8601 start timestamp (UTC).
    pub started_at: String,
    /// ISO8601 end timestamp (UTC).
    pub finished_at: String,
    /// First generated seed, for drivers that walk a seed range.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub seed_start: Option<u64>,
    /// The number of seeds requested with `--runs`; `runs` below it means the
    /// duration expired before the fixed seed range was covered.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub requested_runs: Option<u64>,
    /// A negative-control run: the seed whose result was deliberately
    /// perturbed after execution. Such a log is never campaign evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub planted_miscompile_seed: Option<u64>,
    /// Differential rows (one generated module and one input row, checked at
    /// every JIT level) the driver compared.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rows_checked: Option<u64>,
    /// Rows in which every JIT level executed (a value or a hardware trap).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rows_executed: Option<u64>,
    /// Rows in which at least one JIT level was refused and so compared
    /// nothing at that level.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rows_refused: Option<u64>,
    /// The first distinct refusal reasons, truncated (at most a few).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub refusal_samples: Vec<String>,
    /// Checked rows whose JIT levels were compared against the reference
    /// model's value.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rows_oracle_compared: Option<u64>,
    /// Checked rows for which the reference model produced no value (for
    /// example a division by zero), so the JIT levels were compared only with
    /// each other.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rows_cross_level_only: Option<u64>,
    /// The first distinct reference-model errors, truncated (at most a few).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub oracle_error_samples: Vec<String>,
    /// Scalar rows each seed checks when it completes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scalar_rows_per_seed: Option<u64>,
    /// Seeds that checked fewer scalar rows than `scalar_rows_per_seed` (a
    /// generator panic, or a defect that stopped the seed early).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub seeds_incomplete: Option<u64>,
    /// The first incomplete seeds (at most a few).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub incomplete_seed_samples: Vec<u64>,
}

impl RunLog {
    /// Serialize completely before opening the output. An unavailable tool or
    /// a failed campaign still needs a reliable report; publication failures
    /// are operator diagnostics, not compiler crashes or successful runs.
    pub fn write_to(&self, path: &Path) -> io::Result<()> {
        let json = serde_json::to_vec_pretty(self).map_err(|error| {
            io::Error::other(format!(
                "cannot serialize fuzz run log '{}': {error}",
                path.display()
            ))
        })?;
        std::fs::write(path, json).map_err(|error| {
            io::Error::new(
                error.kind(),
                format!("cannot write fuzz run log '{}': {error}", path.display()),
            )
        })
    }
}

/// Validate the requested duration before creating output or starting tools.
/// `Instant + Duration` can panic for a valid u64 command-line argument.
pub fn campaign_deadline(duration_secs: u64) -> Result<Instant, String> {
    Instant::now()
        .checked_add(Duration::from_secs(duration_secs))
        .ok_or_else(|| "--duration exceeds the platform's monotonic-clock range".to_string())
}
