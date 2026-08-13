// WS1 — workspace unit/integration test matrix.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust-cg-test matrix` — run the workspace unit-test matrix.
//!
//! The command delegates to the maintained repository matrix runner; use
//! `trust-cg-test matrix --help` for selectors and output details.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use anyhow::Context;
use chrono::Utc;
use clap::Args;
use serde::Deserialize;

use super::GlobalArgs;
use crate::OutputFormat;
use crate::config::RepoRoot;
use crate::results::ResultStatus;
use crate::shell::{Captured, Spawn, which};

/// Arguments for `trust-cg-test matrix`.
#[derive(Args, Debug, Clone)]
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
pub struct MatrixArgs {
    /// Only run the named crate (e.g. `trust-cg-codegen`).
    #[arg(long = "crate", alias = "crate-filter", value_name = "CRATE")]
    pub crate_filter: Option<String>,

    /// Shard of a crate to run (e.g. `aarch64`, `macho`). Requires `--crate`.
    #[arg(long, value_name = "NAME")]
    pub shard: Option<String>,

    /// Only run tests changed since the given git ref.
    #[arg(long, value_name = "REF")]
    pub since: Option<String>,

    /// Caller-supplied baseline JSON file to diff the run against.
    #[arg(long, value_name = "PATH")]
    pub compare: Option<std::path::PathBuf>,
}

#[derive(Debug, Deserialize)]
struct MatrixArtifact {
    totals: MatrixTotals,
}

#[derive(Debug, Deserialize)]
struct MatrixTotals {
    #[serde(default)]
    failed: u64,
    #[serde(default)]
    test_ignored: u64,
    #[serde(default)]
    doc_ignored: u64,
    #[serde(default)]
    outcome_counts: BTreeMap<String, u64>,
}

/// Entry point.
pub fn run(global: &GlobalArgs, args: &MatrixArgs) -> anyhow::Result<ResultStatus> {
    if args.since.is_some() {
        eprintln!("trust-cg-test matrix: --since is not supported by the full matrix runner yet");
        return Ok(ResultStatus::UsageError);
    }

    let selector = match matrix_selector(args) {
        MatrixSelector::All => None,
        MatrixSelector::Only(selector) => Some(selector),
        MatrixSelector::Invalid => {
            eprintln!("trust-cg-test matrix: --shard requires --crate");
            return Ok(ResultStatus::UsageError);
        }
    };

    let repo = RepoRoot::locate(Path::new("."))?;
    let out_path = matrix_output_path(&repo, global.out.as_ref());
    let script_status = run_matrix_script(&repo, global, selector.as_deref(), &out_path)?;
    if script_status != ResultStatus::Ok {
        return Ok(script_status);
    }
    if global.dry_run {
        if let Some(compare) = &args.compare {
            println!(
                "dry-run: would compare matrix artifact {} against {}",
                out_path.display(),
                compare.display()
            );
        }
        return Ok(ResultStatus::Ok);
    }

    let artifact_status = status_from_artifact(&out_path)?;
    if global.is_json() && artifact_status != ResultStatus::Ok {
        print_artifact(&out_path)?;
        return Ok(artifact_status);
    }

    let compare_status = if let Some(compare) = &args.compare {
        run_compare(&repo, global, &out_path, compare)?
    } else {
        ResultStatus::Ok
    };

    if global.is_json() && args.compare.is_none() {
        print_artifact(&out_path)?;
    }

    Ok(if artifact_status != ResultStatus::Ok {
        artifact_status
    } else if compare_status != ResultStatus::Ok {
        compare_status
    } else {
        ResultStatus::Ok
    })
}

#[derive(Debug, Eq, PartialEq)]
enum MatrixSelector {
    All,
    Only(String),
    Invalid,
}

fn matrix_selector(args: &MatrixArgs) -> MatrixSelector {
    match (&args.crate_filter, &args.shard) {
        (None, None) => MatrixSelector::All,
        (Some(krate), None) => MatrixSelector::Only(krate.clone()),
        (Some(krate), Some(shard)) => MatrixSelector::Only(format!("{krate}|{shard}")),
        (None, Some(_)) => MatrixSelector::Invalid,
    }
}

fn matrix_output_path(repo: &RepoRoot, out: Option<&PathBuf>) -> PathBuf {
    match out {
        Some(path) if path.is_absolute() => path.clone(),
        Some(path) => repo.join(path),
        None => repo
            .join("evals")
            .join("results")
            .join("tests")
            .join(format!("{}.json", Utc::now().format("%Y-%m-%d"))),
    }
}

fn run_matrix_script(
    repo: &RepoRoot,
    global: &GlobalArgs,
    selector: Option<&str>,
    out_path: &Path,
) -> anyhow::Result<ResultStatus> {
    let Some(mut spawn) = matrix_script_spawn(repo) else {
        eprintln!(
            "trust-cg-test matrix: bash not found; install MSYS2/Git Bash or put bash on PATH"
        );
        return Ok(ResultStatus::EnvBroken);
    };

    spawn = spawn
        .cwd(repo.0.clone())
        .arg("--out")
        .arg(path_arg_for_bash(out_path));
    if global.dry_run {
        spawn = spawn.arg("--dry-run");
    }
    if let Some(only) = selector {
        spawn = spawn.arg("--only").arg(only.to_string());
    }

    let code = if global.is_json() && !global.dry_run {
        let captured = spawn.capture()?;
        if captured.code != 0 {
            relay_captured_to_stderr(&captured)?;
        }
        captured.code
    } else {
        spawn.run()?
    };
    Ok(status_from_script_exit_code(code))
}

fn matrix_script_spawn(repo: &RepoRoot) -> Option<Spawn> {
    let script = path_arg_for_bash(&repo.join("scripts").join("run_full_test_matrix.sh"));
    let bash = find_bash()?;
    Some(
        Spawn::new(bash)
            .arg("-lc")
            .arg(r#"export PATH="$1:$PATH"; cd "$2" && shift 2 && exec "$@""#)
            .arg("trust-cg-test-matrix")
            .arg(cargo_bin_for_bash())
            .arg(path_arg_for_bash(&repo.0))
            .arg(script),
    )
}

fn path_arg_for_bash(path: &Path) -> OsString {
    let raw = path.display().to_string();
    let without_verbatim = raw.strip_prefix(r"\\?\").unwrap_or(&raw);
    let normalized = without_verbatim.replace('\\', "/");
    let bytes = normalized.as_bytes();
    if bytes.len() > 2 && bytes[1] == b':' && bytes[2] == b'/' && bytes[0].is_ascii_alphabetic() {
        let drive = char::from(bytes[0]).to_ascii_lowercase();
        OsString::from(format!("/{drive}/{}", &normalized[3..]))
    } else {
        OsString::from(normalized)
    }
}

fn cargo_bin_for_bash() -> OsString {
    which("cargo")
        .or_else(|| which("cargo.exe"))
        .and_then(|path| path.parent().map(path_arg_for_bash))
        .or_else(|| {
            std::env::var_os("USERPROFILE").map(|home| {
                let mut path = PathBuf::from(home);
                path.push(".cargo");
                path.push("bin");
                path_arg_for_bash(&path)
            })
        })
        .unwrap_or_else(|| OsString::from("/usr/bin"))
}

fn find_bash() -> Option<OsString> {
    [
        r"C:\msys64\usr\bin\bash.exe",
        r"C:\Program Files\Git\bin\bash.exe",
        r"C:\Program Files\Git\usr\bin\bash.exe",
    ]
    .into_iter()
    .map(PathBuf::from)
    .find(|p| p.is_file())
    .or_else(|| which("bash"))
    .or_else(|| which("bash.exe"))
    .map(|p| p.as_os_str().to_os_string())
}

fn status_from_artifact(path: &Path) -> anyhow::Result<ResultStatus> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    let artifact: MatrixArtifact = serde_json::from_str(&text)
        .with_context(|| format!("parsing {} as test matrix JSON", path.display()))?;
    let bad_outcomes = ["fail", "timeout", "incomplete"].into_iter().any(|name| {
        artifact
            .totals
            .outcome_counts
            .get(name)
            .copied()
            .unwrap_or(0)
            > 0
    });
    if artifact.totals.failed > 0
        || artifact.totals.test_ignored > 0
        || artifact.totals.doc_ignored > 0
        || bad_outcomes
    {
        Ok(ResultStatus::Failed)
    } else {
        Ok(ResultStatus::Ok)
    }
}

fn run_compare(
    repo: &RepoRoot,
    global: &GlobalArgs,
    current: &Path,
    baseline: &Path,
) -> anyhow::Result<ResultStatus> {
    let mut spawn = Spawn::new(std::env::current_exe()?.as_os_str().to_os_string())
        .cwd(repo.0.clone())
        .arg("--format")
        .arg(format_name(global.format))
        .arg("ratchet")
        .arg("tests")
        .arg("--current")
        .arg(current.as_os_str().to_os_string())
        .arg("--baseline")
        .arg(baseline.as_os_str().to_os_string());
    if global.quiet {
        spawn = spawn.arg("--quiet");
    }
    for _ in 0..global.verbose {
        spawn = spawn.arg("--verbose");
    }
    Ok(status_from_exit_code(spawn.run()?))
}

fn format_name(format: OutputFormat) -> &'static str {
    match format {
        OutputFormat::Human => "human",
        OutputFormat::Json => "json",
        OutputFormat::Junit => "junit",
    }
}

fn status_from_exit_code(code: i32) -> ResultStatus {
    match code {
        0 => ResultStatus::Ok,
        1 => ResultStatus::Failed,
        2 => ResultStatus::EnvBroken,
        64 => ResultStatus::UsageError,
        70 => ResultStatus::Errored,
        _ => ResultStatus::Errored,
    }
}

fn status_from_script_exit_code(code: i32) -> ResultStatus {
    match code {
        0 => ResultStatus::Ok,
        1 => ResultStatus::EnvBroken,
        2 => ResultStatus::UsageError,
        64 => ResultStatus::UsageError,
        70 => ResultStatus::Errored,
        _ => ResultStatus::Errored,
    }
}

fn print_artifact(path: &Path) -> anyhow::Result<()> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    print!("{text}");
    io::stdout().flush()?;
    Ok(())
}

fn relay_captured_to_stderr(captured: &Captured) -> anyhow::Result<()> {
    eprint!("{}", captured.stdout);
    eprint!("{}", captured.stderr);
    io::stderr().flush()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(krate: Option<&str>, shard: Option<&str>) -> MatrixArgs {
        MatrixArgs {
            crate_filter: krate.map(str::to_string),
            shard: shard.map(str::to_string),
            since: None,
            compare: None,
        }
    }

    #[test]
    fn selector_rejects_shard_without_crate() {
        assert_eq!(
            matrix_selector(&args(None, Some("integration-jit-runtime"))),
            MatrixSelector::Invalid
        );
    }

    #[test]
    fn selector_combines_crate_and_shard_for_runner_only_filter() {
        assert_eq!(
            matrix_selector(&args(
                Some("trust-cg-codegen"),
                Some("integration-jit-runtime")
            )),
            MatrixSelector::Only("trust-cg-codegen|integration-jit-runtime".to_string())
        );
    }

    #[test]
    fn bash_path_strips_windows_verbatim_prefix() {
        let path = PathBuf::from(r"\\?\C:\build\Trust Codegen\scripts\run_full_test_matrix.sh");
        assert_eq!(
            path_arg_for_bash(&path),
            OsString::from("/c/build/Trust Codegen/scripts/run_full_test_matrix.sh")
        );
    }

    #[test]
    fn script_exit_codes_follow_matrix_runner_contract() {
        assert_eq!(status_from_script_exit_code(0), ResultStatus::Ok);
        assert_eq!(status_from_script_exit_code(1), ResultStatus::EnvBroken);
        assert_eq!(status_from_script_exit_code(2), ResultStatus::UsageError);
        assert_eq!(status_from_script_exit_code(64), ResultStatus::UsageError);
    }

    #[test]
    fn artifact_status_rejects_failed_outcomes() {
        let path = std::env::temp_dir().join(format!(
            "trust-cg-test-matrix-status-{}.json",
            std::process::id()
        ));
        fs::write(
            &path,
            r#"{"totals":{"failed":0,"test_ignored":0,"doc_ignored":0,"outcome_counts":{"pass":1,"timeout":1}}}"#,
        )
        .expect("write temp matrix artifact");
        let status = status_from_artifact(&path).expect("parse temp matrix artifact");
        let _ = fs::remove_file(&path);
        assert_eq!(status, ResultStatus::Failed);
    }

    #[test]
    fn artifact_status_rejects_ignored_rustdocs() {
        let path = std::env::temp_dir().join(format!(
            "trust-cg-test-matrix-doc-ignore-status-{}.json",
            std::process::id()
        ));
        fs::write(
            &path,
            r#"{"totals":{"failed":0,"test_ignored":0,"doc_ignored":1,"outcome_counts":{"pass":1}}}"#,
        )
        .expect("write temp matrix artifact");
        let status = status_from_artifact(&path).expect("parse temp matrix artifact");
        let _ = fs::remove_file(&path);
        assert_eq!(status, ResultStatus::Failed);
    }
}
