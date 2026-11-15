// Ratchet checks — shell isolation, schema drift, etc.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust-cg-test ratchet` — invariants CI enforces over the test suite.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::Context;
use clap::{Args, Subcommand};
use schemars::schema_for;
use serde::{Deserialize, Serialize};

use super::GlobalArgs;
use super::lint_linux::LintLinuxArgs;
use crate::OutputFormat;
use crate::config::RepoRoot;
use crate::results::{EmptyRecord, ResultStatus, RunSummary};

// #624: preserve the old integration-jit ratchet floor after #437 split
// the current matrix shard into runtime and observability shards.
const CODEGEN_CRATE: &str = "trust-cg-codegen";
const LEGACY_JIT_SHARD: &str = "integration-jit";
const SPLIT_JIT_SHARDS: [&str; 2] = ["integration-jit-runtime", "integration-jit-observability"];

/// Which ratchet to run.
#[derive(Subcommand, Debug, Clone)]
pub enum RatchetCommand {
    /// Pass-count regression check against a caller-supplied baseline.
    #[command(
        long_about = "Monotonic pass-count ratchet for the workspace test matrix.\n\n\
                  Compares the newest JSON in `evals/results/tests/` against\n\
                  the required `--baseline` JSON. Fails if any `(crate, shard)`\n\
                  pair in the baseline has a lower `passed` count in the\n\
                  current run, or a higher `failed` count, or has disappeared\n\
                  entirely. New shards are OK — the baseline only grows.\n\n\
                  Exit codes:\n  \
                  0 — current run is at or above baseline on every pair.\n  \
                  1 — regression detected.\n  \
                  2 — tooling error (missing files, parse error, etc.).\n\n\
                  # Examples\n\n  \
                  trust-cg-test ratchet tests --baseline path/to/tests-baseline.json\n  \
                  trust-cg-test ratchet tests --current current.json --baseline baseline.json\n  \
                  trust-cg-test ratchet tests --baseline path/to/tests-baseline.json --format json"
    )]
    Tests(TestsArgs),
    /// Enforce `std::process::Command` is only used in `shell.rs` / `external.rs`.
    #[command(
        long_about = "Enforce the process-spawn boundary for `trust-cg-test`.\n\n\
                      Scans `crates/trust-cg-test/src` and fails if \
                      `std::process::Command`, `Command::new`, or \
                      `process::Command` appears outside `shell.rs`, \
                      `external.rs`, or this ratchet implementation.\n\n\
                      # Examples\n\n  \
                      trust-cg-test ratchet shell-isolation\n  \
                      trust-cg-test ratchet shell-isolation --format json"
    )]
    ShellIsolation,
    /// Assert committed `evals/schema/*.json` matches what schemars emits.
    #[command(long_about = "Assert the committed result schemas match the Rust \
                      types.\n\n\
                      Regenerates the expected schemars output for the \
                      initial result-schema types and compares it with the \
                      JSON committed under `evals/schema/`.\n\n\
                      # Examples\n\n  \
                      trust-cg-test ratchet schema\n  \
                      trust-cg-test ratchet schema --format json")]
    Schema(SchemaArgs),
    /// Cross-compile check for `#[cfg(target_os = "linux")]` paths in
    /// `trust-cg-codegen` (issue #346). Safe on macOS-only boxes — targets
    /// whose std the installed Trust package lacks are reported as `skipped`.
    ///
    /// Equivalent to the top-level `trust-cg-test lint-linux`. Registered as
    /// a ratchet so CI can sweep every invariant with
    /// `trust-cg-test ratchet <check>` under a single dispatcher (#446).
    #[command(long_about = "Cross-compile check for Linux-only `trust-cg-codegen` \
                  paths.\n\n\
                  Runs `targo --unverified check --target <linux-triple> -p \
                  trust-cg-codegen` through the shared `trust-cg-test` shell \
                  boundary. Missing Rust targets are reported as `skipped`, \
                  so the command is safe on macOS-only developer boxes.\n\n\
                  Equivalent to top-level `trust-cg-test lint-linux`; kept \
                  under `ratchet` so CI can sweep every invariant through \
                  one dispatcher.\n\n\
                  # Examples\n\n  \
                  trust-cg-test ratchet lint-linux\n  \
                  trust-cg-test ratchet lint-linux --target x86_64-unknown-linux-gnu\n  \
                  trust-cg-test ratchet lint-linux --format json")]
    LintLinux(LintLinuxArgs),
}

/// Arguments for `trust-cg-test ratchet tests`.
#[derive(Args, Debug, Clone)]
#[command(
    long_about = "Monotonic pass-count ratchet for the workspace test matrix.\n\n\
                  Compares the newest JSON in `evals/results/tests/` against\n\
                  the required `--baseline` JSON. Fails if any `(crate, shard)`\n\
                  pair in the baseline has a lower `passed` count in the\n\
                  current run, or a higher `failed` count, or has disappeared\n\
                  entirely. New shards are OK — the baseline only grows.\n\n\
                  Exit codes:\n  \
                  0 — current run is at or above baseline on every pair.\n  \
                  1 — regression detected.\n  \
                  2 — tooling error (missing files, parse error, etc.).\n\n\
                  # Examples\n\n  \
                  trust-cg-test ratchet tests --baseline path/to/tests-baseline.json\n  \
                  trust-cg-test ratchet tests --current current.json --baseline baseline.json\n  \
                  trust-cg-test ratchet tests --baseline path/to/tests-baseline.json --format json"
)]
pub struct TestsArgs {
    /// Override the "current" test-matrix JSON. Default: newest
    /// `*.json` under `evals/results/tests/`.
    #[arg(long, value_name = "PATH")]
    pub current: Option<PathBuf>,
    /// Baseline JSON to compare against. Required because v0.1.0 ships no
    /// universal machine-independent pass-count baseline.
    #[arg(long, value_name = "PATH")]
    pub baseline: PathBuf,
}

/// Arguments for `trust-cg-test ratchet`.
#[derive(Args, Debug, Clone)]
#[command(long_about = "Run ratchet checks (called by CI). Every ratchet fails \
                  with a non-zero exit code when its invariant is \
                  violated.\n\n\
                  # Examples\n\n  \
                  trust-cg-test ratchet shell-isolation\n  \
                  trust-cg-test ratchet schema --format json\n  \
                  trust-cg-test ratchet tests --baseline path/to/tests-baseline.json\n  \
                  trust-cg-test ratchet lint-linux")]
pub struct RatchetArgs {
    /// Which ratchet to run.
    #[command(subcommand)]
    pub cmd: RatchetCommand,
}

/// Arguments for the committed result-schema ratchet.
#[derive(Args, Debug, Clone, Default)]
pub struct SchemaArgs {
    /// Write missing or changed schemas instead of failing the ratchet.
    #[arg(long)]
    pub write: bool,
}

/// Entry point.
pub fn run(global: &GlobalArgs, args: &RatchetArgs) -> anyhow::Result<ResultStatus> {
    match &args.cmd {
        RatchetCommand::Tests(a) => tests(global, a),
        RatchetCommand::ShellIsolation => shell_isolation(global),
        RatchetCommand::Schema(args) => schema(global, args),
        RatchetCommand::LintLinux(a) => super::lint_linux::run(global, a),
    }
}

// ---------------- tests (pass-count ratchet) ----------------
//
// The canonical test-count ratchet (formerly `scripts/check_test_ratchet.sh`,
// deleted once this port was complete; `trust-cg-test matrix --compare`
// delegates here). Compares the newest test-matrix JSON under
// `evals/results/tests/` against a caller-supplied, reviewed baseline.
// Fails (exit 1) on any of:
//   * A `(crate, shard)` pair in the baseline has a lower `passed`
//     count in the current run.
//   * A `(crate, shard)` pair in the baseline has a higher `failed`
//     count in the current run.
//   * A baseline shard is missing from the current run entirely.
// New shards in the current run are accepted silently — the baseline
// grows monotonically on refresh.
//
// Exit semantics (the contract the shell script established):
//   * `ResultStatus::Ok` (0)          — no regressions
//   * `ResultStatus::Failed` (1)      — at least one violation / missing
//   * `ResultStatus::EnvBroken` (2)   — missing / unparseable input files

/// One per-crate/per-shard entry in the test-matrix JSON. Unknown fields
/// are ignored so future matrix runs can add metadata without breaking
/// the ratchet.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
struct ShardEntry {
    #[serde(default, rename = "crate")]
    krate: String,
    #[serde(default)]
    shard: String,
    #[serde(default)]
    passed: u64,
    #[serde(default)]
    failed: u64,
}

/// Top-level test-matrix JSON document. Only the fields the ratchet
/// reads are modeled.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
struct TestMatrixDoc {
    #[serde(default)]
    shards: Vec<ShardEntry>,
    #[serde(default)]
    totals: TotalsEntry,
}

/// `totals` subtree — only `passed` / `failed` are used for the
/// human-readable summary line.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
struct TotalsEntry {
    #[serde(default)]
    passed: u64,
    #[serde(default)]
    failed: u64,
}

/// Why a `(crate, shard)` pair regressed.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
enum RegressionKind {
    /// `passed` decreased.
    PassedDecreased,
    /// `failed` increased.
    FailedIncreased,
}

impl RegressionKind {
    const fn as_str(self) -> &'static str {
        match self {
            Self::PassedDecreased => "passed decreased",
            Self::FailedIncreased => "failed increased",
        }
    }
}

/// One regression finding.
#[derive(Clone, Debug, Serialize)]
struct Regression {
    #[serde(rename = "crate")]
    krate: String,
    shard: String,
    kind: RegressionKind,
    baseline: u64,
    current: u64,
}

impl Regression {
    fn delta(&self) -> i128 {
        i128::from(self.current) - i128::from(self.baseline)
    }
}

/// Machine-readable summary emitted under `--format json` / `--format junit`.
#[derive(Clone, Debug, Serialize)]
struct TestsReport {
    command: &'static str,
    current_path: String,
    baseline_path: String,
    baseline_totals: TotalsSummary,
    current_totals: TotalsSummary,
    regressions: Vec<Regression>,
    missing_shards: Vec<ShardKey>,
    exit: ResultStatus,
}

#[derive(Clone, Debug, Serialize)]
struct TotalsSummary {
    passed: u64,
    failed: u64,
}

#[derive(Clone, Debug, Serialize)]
struct ShardKey {
    #[serde(rename = "crate")]
    krate: String,
    shard: String,
}

fn tests(global: &GlobalArgs, args: &TestsArgs) -> anyhow::Result<ResultStatus> {
    let repo = RepoRoot::locate(Path::new("."))?;
    let results_dir = repo.join("evals").join("results").join("tests");

    // Resolve the current path; the baseline is always caller-supplied.
    let current_path = match args.current.clone() {
        Some(p) => p,
        None => match newest_json(&results_dir) {
            Some(p) => p,
            None => {
                eprintln!(
                    "ratchet tests: no current test-matrix JSON found (looked in {}/)",
                    results_dir.display()
                );
                eprintln!("Run: scripts/run_full_test_matrix.sh");
                return Ok(ResultStatus::EnvBroken);
            }
        },
    };
    let baseline_path = args.baseline.clone();

    if !current_path.is_file() {
        eprintln!(
            "ratchet tests: current file missing: {}",
            current_path.display()
        );
        return Ok(ResultStatus::EnvBroken);
    }
    if !baseline_path.is_file() {
        eprintln!(
            "ratchet tests: baseline file missing: {}",
            baseline_path.display()
        );
        eprintln!("To seed the baseline from the current run:");
        eprintln!(
            "  cp {} {}",
            current_path.display(),
            baseline_path.display()
        );
        return Ok(ResultStatus::EnvBroken);
    }

    let current_doc = load_matrix(&current_path)?;
    let baseline_doc = load_matrix(&baseline_path)?;

    let (regressions, missing) = diff_matrices(&baseline_doc, &current_doc);

    let exit = if regressions.is_empty() && missing.is_empty() {
        ResultStatus::Ok
    } else {
        ResultStatus::Failed
    };

    let report = TestsReport {
        command: "ratchet.tests",
        current_path: current_path.display().to_string(),
        baseline_path: baseline_path.display().to_string(),
        baseline_totals: TotalsSummary {
            passed: baseline_doc.totals.passed,
            failed: baseline_doc.totals.failed,
        },
        current_totals: TotalsSummary {
            passed: current_doc.totals.passed,
            failed: current_doc.totals.failed,
        },
        regressions: regressions.clone(),
        missing_shards: missing.clone(),
        exit,
    };

    match global.format {
        OutputFormat::Json | OutputFormat::Junit => {
            let json = serde_json::to_string_pretty(&report)?;
            println!("{json}");
        }
        OutputFormat::Human => print_tests_human(&report),
    }

    Ok(exit)
}

/// Parse a test-matrix JSON doc. Returns `EnvBroken` exit on failure via
/// the outer error context so callers can surface a clean error instead
/// of a Rust panic string.
fn load_matrix(path: &Path) -> anyhow::Result<TestMatrixDoc> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    let doc: TestMatrixDoc = serde_json::from_str(&text)
        .with_context(|| format!("parsing {} as test-matrix JSON", path.display()))?;
    Ok(doc)
}

/// Pick the newest `*.json` in `dir` by lexicographic filename (matches
/// the shell script's `ls -1 … | sort | tail -n 1`). Returns `None` when
/// the directory is empty or missing. Non-JSON files and the
/// `.trust-cg-verify.all.log` sidecar are ignored.
fn newest_json(dir: &Path) -> Option<PathBuf> {
    let entries = fs::read_dir(dir).ok()?;
    let mut jsons: Vec<PathBuf> = entries
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("json"))
        .collect();
    jsons.sort();
    jsons.pop()
}

/// Return `(regressions, missing_shards)` for `current` vs `baseline`.
/// `missing_shards` lists baseline `(crate, shard)` pairs absent from
/// the current run — disappearance is its own failure mode per the
/// shell script's "can't silently delete" rule.
fn diff_matrices(
    baseline: &TestMatrixDoc,
    current: &TestMatrixDoc,
) -> (Vec<Regression>, Vec<ShardKey>) {
    let current_ix: std::collections::HashMap<(String, String), &ShardEntry> = current
        .shards
        .iter()
        .map(|s| ((s.krate.clone(), s.shard.clone()), s))
        .collect();

    let mut regressions: Vec<Regression> = Vec::new();
    let mut missing: Vec<ShardKey> = Vec::new();

    for base_s in &baseline.shards {
        let Some(cur_s) = current_shard_for_baseline(base_s, &current_ix) else {
            missing.push(ShardKey {
                krate: base_s.krate.clone(),
                shard: base_s.shard.clone(),
            });
            continue;
        };
        if cur_s.passed < base_s.passed {
            regressions.push(Regression {
                krate: base_s.krate.clone(),
                shard: base_s.shard.clone(),
                kind: RegressionKind::PassedDecreased,
                baseline: base_s.passed,
                current: cur_s.passed,
            });
        }
        if cur_s.failed > base_s.failed {
            regressions.push(Regression {
                krate: base_s.krate.clone(),
                shard: base_s.shard.clone(),
                kind: RegressionKind::FailedIncreased,
                baseline: base_s.failed,
                current: cur_s.failed,
            });
        }
    }

    (regressions, missing)
}

fn current_shard_for_baseline(
    base_s: &ShardEntry,
    current_ix: &std::collections::HashMap<(String, String), &ShardEntry>,
) -> Option<ShardEntry> {
    let key = (base_s.krate.clone(), base_s.shard.clone());
    if let Some(cur_s) = current_ix.get(&key) {
        return Some((*cur_s).clone());
    }

    if base_s.krate != CODEGEN_CRATE || base_s.shard != LEGACY_JIT_SHARD {
        return None;
    }

    let mut out = ShardEntry {
        krate: base_s.krate.clone(),
        shard: base_s.shard.clone(),
        ..ShardEntry::default()
    };
    for split_shard in SPLIT_JIT_SHARDS {
        let split_key = (CODEGEN_CRATE.to_string(), split_shard.to_string());
        let split_s = current_ix.get(&split_key)?;
        out.passed += split_s.passed;
        out.failed += split_s.failed;
    }
    Some(out)
}

fn print_tests_human(r: &TestsReport) {
    if !r.missing_shards.is_empty() {
        println!("test ratchet FAILED: baseline shards missing from current run:");
        for k in &r.missing_shards {
            println!("  {}/{}", k.krate, k.shard);
        }
        println!();
    }

    if !r.regressions.is_empty() {
        println!("test ratchet FAILED: regression detected.");
        println!("  current:  {}", r.current_path);
        println!("  baseline: {}", r.baseline_path);
        println!();
        println!(
            "{:<42} {:<20} {:>8} {:>8} {:>8}",
            "crate/shard", "metric", "base", "cur", "delta"
        );
        for v in &r.regressions {
            let label = format!("{}/{}", v.krate, v.shard);
            println!(
                "{:<42} {:<20} {:>8} {:>8} {:>+8}",
                label,
                v.kind.as_str(),
                v.baseline,
                v.current,
                v.delta()
            );
        }
        println!();
        println!("Fix the regression, or refresh the baseline after approval:");
        println!("  cp {} {}", r.current_path, r.baseline_path);
        return;
    }

    if r.exit == ResultStatus::Failed {
        // Only reachable when missing shards but no metric regressions.
        return;
    }

    println!(
        "test ratchet OK: passed {} >= baseline {}; failed {} <= baseline {}.",
        r.current_totals.passed,
        r.baseline_totals.passed,
        r.current_totals.failed,
        r.baseline_totals.failed,
    );
}

// ---------------- shell-isolation ----------------

#[derive(Debug, Serialize)]
struct ShellViolation {
    path: String,
    line: u32,
    text: String,
}

fn shell_isolation(global: &GlobalArgs) -> anyhow::Result<ResultStatus> {
    let repo = RepoRoot::locate(Path::new("."))?;
    let crate_src = repo.join("crates").join("trust-cg-test").join("src");
    let mut violations: Vec<ShellViolation> = Vec::new();
    walk_rs(&crate_src, &mut |path| {
        scan_file(&crate_src, path, &mut violations);
    })?;

    match global.format {
        OutputFormat::Json | OutputFormat::Junit => {
            let json = serde_json::to_string_pretty(&violations)?;
            println!("{json}");
        }
        OutputFormat::Human => {
            if violations.is_empty() {
                println!("ratchet shell-isolation: OK (no offenders)");
            } else {
                println!(
                    "ratchet shell-isolation: {} violation(s):",
                    violations.len()
                );
                for v in &violations {
                    println!("  {}:{}  {}", v.path, v.line, v.text.trim());
                }
            }
        }
    }

    Ok(if violations.is_empty() {
        ResultStatus::Ok
    } else {
        ResultStatus::Failed
    })
}

fn walk_rs(dir: &Path, cb: &mut dyn FnMut(&Path)) -> anyhow::Result<()> {
    for entry in fs::read_dir(dir).with_context(|| format!("reading {}", dir.display()))? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            walk_rs(&path, cb)?;
        } else if path.extension().and_then(|s| s.to_str()) == Some("rs") {
            cb(&path);
        }
    }
    Ok(())
}

fn scan_file(base: &Path, path: &Path, out: &mut Vec<ShellViolation>) {
    // Exempt files: shell.rs, external.rs, and this ratchet itself (the
    // only place we need to refer to the offending symbol as a literal).
    let rel = path.strip_prefix(base).unwrap_or(path);
    let rel_str = rel.to_string_lossy().replace('\\', "/");
    if rel_str == "shell.rs" || rel_str == "external.rs" || rel_str == "cmd/ratchet.rs" {
        return;
    }
    let Ok(text) = fs::read_to_string(path) else {
        return;
    };
    for (i, line) in text.lines().enumerate() {
        // Skip comments/doc lines.
        let trimmed = line.trim_start();
        if trimmed.starts_with("//") || trimmed.starts_with("///") || trimmed.starts_with("//!") {
            continue;
        }
        // Skip lines that are entirely inside a string literal (crude but
        // sufficient — full tokenization is overkill for this check).
        let without_strings = strip_string_literals(line);
        let banned_fragment = "std::proc";
        let banned_symbol = "ess::Command"; // split intentionally to avoid self-trigger
        let full_symbol = format!("{banned_fragment}{banned_symbol}");
        if without_strings.contains(&full_symbol) {
            out.push(ShellViolation {
                path: path.to_string_lossy().into_owned(),
                line: u32::try_from(i + 1).unwrap_or(0),
                text: line.to_string(),
            });
        }
    }
}

fn strip_string_literals(line: &str) -> String {
    // Replace anything between paired `"` with a placeholder. Naive but
    // sufficient for this ratchet's scope (one-line literals only).
    let mut out = String::with_capacity(line.len());
    let mut in_str = false;
    let mut prev_bs = false;
    for ch in line.chars() {
        match ch {
            '"' if !prev_bs => {
                in_str = !in_str;
                out.push(' ');
            }
            _ if in_str => out.push(' '),
            _ => out.push(ch),
        }
        prev_bs = ch == '\\' && !prev_bs;
    }
    out
}

// ---------------- schema ----------------

fn schema(global: &GlobalArgs, args: &SchemaArgs) -> anyhow::Result<ResultStatus> {
    let repo = RepoRoot::locate(Path::new("."))?;
    let schema_dir = repo.join("evals").join("schema");
    fs::create_dir_all(&schema_dir)?;

    let generated = generate_schemas();

    // Compare each schema with the checked-in file.
    let mut drift: Vec<(String, String)> = Vec::new();
    let mut updated: Vec<String> = Vec::new();
    for (name, json) in &generated {
        let target = schema_dir.join(format!("{name}.json"));
        let current = fs::read_to_string(&target).ok();
        if current.as_deref() != Some(json.as_str()) {
            if args.write {
                fs::write(&target, json)?;
                updated.push(name.clone());
            } else {
                drift.push((name.clone(), target.display().to_string()));
            }
        }
    }

    let exit = if drift.is_empty() {
        ResultStatus::Ok
    } else {
        ResultStatus::Failed
    };

    match global.format {
        OutputFormat::Json | OutputFormat::Junit => {
            let report = serde_json::json!({
                "command": "ratchet.schema",
                "drift": drift.iter().map(|(n, p)| serde_json::json!({"name": n, "path": p})).collect::<Vec<_>>(),
                "updated": updated,
                "exit": exit,
            });
            println!("{report:#}");
        }
        OutputFormat::Human => {
            if drift.is_empty() {
                println!("ratchet schema: OK ({} schemas checked)", generated.len());
                if !updated.is_empty() {
                    println!("  schemas written: {}", updated.join(", "));
                }
            } else {
                println!("ratchet schema: drift in {} schema(s):", drift.len());
                for (name, path) in &drift {
                    println!("  {name}  ({path})");
                }
                println!("  regenerate with `trust-cg-test ratchet schema --write`");
            }
        }
    }

    Ok(exit)
}

fn generate_schemas() -> Vec<(String, String)> {
    let s_run = schema_for!(RunSummary<EmptyRecord>);
    let run_summary = serde_json::to_string_pretty(&s_run).unwrap_or_default();
    let s_empty = schema_for!(EmptyRecord);
    let empty = serde_json::to_string_pretty(&s_empty).unwrap_or_default();
    vec![
        ("run_summary".to_string(), run_summary),
        ("empty_record".to_string(), empty),
    ]
}

#[cfg(test)]
mod tests {
    use clap::{Command, Subcommand};

    use super::{
        RatchetCommand, RegressionKind, ShardEntry, TestMatrixDoc, TotalsEntry, diff_matrices,
        newest_json,
    };

    /// Guard against a silent drop of a subcommand from the ratchet tree.
    /// Every ratchet port must appear here so clap can reach it; if the
    /// `RatchetCommand` enum ever loses a variant, this test breaks
    /// loudly instead of the subcommand vanishing from CI (#446).
    #[test]
    fn ratchet_subcommand_tree_is_complete() {
        let cmd = <RatchetCommand as Subcommand>::augment_subcommands(Command::new("ratchet-test"));
        let subs: Vec<String> = cmd
            .get_subcommands()
            .map(|c| c.get_name().to_string())
            .collect();
        for expected in ["tests", "shell-isolation", "schema", "lint-linux"] {
            assert!(
                subs.iter().any(|s| s == expected),
                "ratchet subcommand `{expected}` missing from RatchetCommand tree; \
                 present: {subs:?}"
            );
        }
    }

    // -------- tests (pass-count ratchet) helpers --------

    fn shard(krate: &str, shard: &str, passed: u64, failed: u64) -> ShardEntry {
        ShardEntry {
            krate: krate.to_string(),
            shard: shard.to_string(),
            passed,
            failed,
        }
    }

    fn doc(shards: Vec<ShardEntry>) -> TestMatrixDoc {
        let (tp, tf) = shards
            .iter()
            .fold((0u64, 0u64), |(p, f), s| (p + s.passed, f + s.failed));
        TestMatrixDoc {
            shards,
            totals: TotalsEntry {
                passed: tp,
                failed: tf,
            },
        }
    }

    #[test]
    fn diff_no_change_is_clean() {
        let base = doc(vec![shard("c1", "all", 10, 0), shard("c2", "lib", 5, 1)]);
        let cur = base.clone();
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(regressions.is_empty());
        assert!(missing.is_empty());
    }

    #[test]
    fn diff_catches_passed_decrease() {
        let base = doc(vec![shard("c1", "all", 10, 0)]);
        let cur = doc(vec![shard("c1", "all", 9, 0)]);
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(missing.is_empty());
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].kind, RegressionKind::PassedDecreased);
        assert_eq!(regressions[0].baseline, 10);
        assert_eq!(regressions[0].current, 9);
        assert_eq!(regressions[0].delta(), -1);
    }

    #[test]
    fn diff_catches_failed_increase() {
        let base = doc(vec![shard("c1", "all", 10, 0)]);
        let cur = doc(vec![shard("c1", "all", 10, 3)]);
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(missing.is_empty());
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].kind, RegressionKind::FailedIncreased);
        assert_eq!(regressions[0].baseline, 0);
        assert_eq!(regressions[0].current, 3);
    }

    #[test]
    fn diff_reports_both_metric_breaks() {
        let base = doc(vec![shard("c1", "all", 10, 0)]);
        let cur = doc(vec![shard("c1", "all", 8, 2)]);
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(missing.is_empty());
        assert_eq!(regressions.len(), 2);
        let kinds: Vec<_> = regressions.iter().map(|r| r.kind).collect();
        assert!(kinds.contains(&RegressionKind::PassedDecreased));
        assert!(kinds.contains(&RegressionKind::FailedIncreased));
    }

    #[test]
    fn diff_flags_missing_shards() {
        let base = doc(vec![shard("c1", "all", 10, 0), shard("c2", "lib", 5, 0)]);
        let cur = doc(vec![shard("c1", "all", 10, 0)]);
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(regressions.is_empty());
        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0].krate, "c2");
        assert_eq!(missing[0].shard, "lib");
    }

    #[test]
    fn diff_accepts_new_shards_in_current() {
        // New `(crate, shard)` pairs in `current` that aren't in baseline
        // must not trigger a regression — the baseline grows monotonically.
        let base = doc(vec![shard("c1", "all", 10, 0)]);
        let cur = doc(vec![shard("c1", "all", 10, 0), shard("c2", "new", 3, 0)]);
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(regressions.is_empty());
        assert!(missing.is_empty());
    }

    #[test]
    fn diff_accepts_legacy_jit_baseline_when_split_shards_cover_floor() {
        let base = doc(vec![shard("trust-cg-codegen", "integration-jit", 63, 0)]);
        let cur = doc(vec![
            shard("trust-cg-codegen", "integration-jit-runtime", 40, 0),
            shard("trust-cg-codegen", "integration-jit-observability", 23, 0),
        ]);
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(regressions.is_empty());
        assert!(missing.is_empty());
    }

    #[test]
    fn diff_catches_legacy_jit_split_combined_pass_decrease() {
        let base = doc(vec![shard("trust-cg-codegen", "integration-jit", 63, 0)]);
        let cur = doc(vec![
            shard("trust-cg-codegen", "integration-jit-runtime", 40, 0),
            shard("trust-cg-codegen", "integration-jit-observability", 22, 0),
        ]);
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(missing.is_empty());
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].kind, RegressionKind::PassedDecreased);
        assert_eq!(regressions[0].baseline, 63);
        assert_eq!(regressions[0].current, 62);
    }

    #[test]
    fn diff_catches_legacy_jit_split_combined_failed_increase() {
        let base = doc(vec![shard("trust-cg-codegen", "integration-jit", 63, 0)]);
        let cur = doc(vec![
            shard("trust-cg-codegen", "integration-jit-runtime", 63, 1),
            shard("trust-cg-codegen", "integration-jit-observability", 1, 0),
        ]);
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(missing.is_empty());
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].kind, RegressionKind::FailedIncreased);
        assert_eq!(regressions[0].baseline, 0);
        assert_eq!(regressions[0].current, 1);
    }

    #[test]
    fn diff_requires_both_legacy_jit_split_shards() {
        let base = doc(vec![shard("trust-cg-codegen", "integration-jit", 63, 0)]);
        let cur = doc(vec![shard(
            "trust-cg-codegen",
            "integration-jit-runtime",
            80,
            0,
        )]);
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(regressions.is_empty());
        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0].krate, "trust-cg-codegen");
        assert_eq!(missing[0].shard, "integration-jit");
    }

    #[test]
    fn diff_accepts_increased_passed_and_decreased_failed() {
        let base = doc(vec![shard("c1", "all", 10, 2)]);
        let cur = doc(vec![shard("c1", "all", 12, 1)]);
        let (regressions, missing) = diff_matrices(&base, &cur);
        assert!(regressions.is_empty());
        assert!(missing.is_empty());
    }

    #[test]
    fn newest_json_picks_lexicographically_latest() {
        let tmp = tempdir_unique("ratchet_newest_json_ok");
        let tmp = tmp.path();
        std::fs::write(tmp.join("2026-04-17.json"), "{}").expect("write");
        std::fs::write(tmp.join("2026-04-19.json"), "{}").expect("write");
        std::fs::write(tmp.join("2026-04-18.json"), "{}").expect("write");
        // Sidecar log file — must be ignored.
        std::fs::write(tmp.join("2026-04-19.trust-cg-verify.all.log"), "x").expect("write");
        let pick = newest_json(tmp).expect("some");
        assert_eq!(pick.file_name().unwrap(), "2026-04-19.json");
    }

    #[test]
    fn newest_json_returns_none_for_missing_or_empty_dir() {
        let missing = std::env::temp_dir().join("trust_cg_ratchet_missing_XYZ_does_not_exist");
        assert!(newest_json(&missing).is_none());
        let empty = tempdir_unique("ratchet_newest_json_empty");
        assert!(newest_json(empty.path()).is_none());
    }

    /// A unique scratch directory the test owns: removed when the returned
    /// guard drops, whether the test passed or failed.
    fn tempdir_unique(tag: &str) -> tempfile::TempDir {
        tempfile::Builder::new()
            .prefix(&format!("trust_cg_{tag}_"))
            .tempdir()
            .expect("mkdir tempdir")
    }
}
