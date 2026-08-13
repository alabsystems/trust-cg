// WS9 — weekly report generator.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The template literal in this file is the source of truth for generated
// weekly reports.

//! `trust-cg-test report` — render the weekly Trust Codegen dashboard.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::Context;
use chrono::{NaiveDate, Utc};
use clap::Args;
use serde::Deserialize;

use super::GlobalArgs;
use crate::OutputFormat;
use crate::config::RepoRoot;
use crate::results::ResultStatus;

/// Arguments for `trust-cg-test report`.
#[derive(Args, Debug, Clone)]
#[command(long_about = "Generate the weekly Trust Codegen dashboard (WS9).\n\n\
                  Reads the newest compatible JSON recursively from each \
                  known workstream result directory, renders the north-star \
                  table and per-workstream sections, and marks missing data \
                  with `—`. Writes `reports/weekly/<iso-date>.md` by default.\n\n\
                  # Examples\n\n  \
                  trust-cg-test report\n  \
                  trust-cg-test report --week 2026-04-19 --format human\n  \
                  trust-cg-test report --out /tmp/weekly.md")]
pub struct ReportArgs {
    /// ISO date for the report. Default: today (UTC).
    #[arg(long, value_name = "ISO-DATE")]
    pub week: Option<String>,

    /// Markdown target path (takes precedence over `--out`).
    #[arg(long, value_name = "PATH")]
    pub markdown_out: Option<PathBuf>,

    /// Also copy the report to `reports/weekly/` and write
    /// `reports/dashboard.md`, even when a custom output path is selected.
    #[arg(long)]
    pub publish: bool,
}

#[derive(Debug, Deserialize)]
struct LatestResult {
    #[serde(default)]
    command: String,
    #[serde(default)]
    totals: Option<serde_json::Value>,
    #[serde(default)]
    exit: Option<serde_json::Value>,
}

#[derive(Clone, Copy)]
struct ResultSource {
    key: &'static str,
    directory: &'static str,
    preferred_subdir: Option<&'static str>,
}

const RESULT_SOURCES: [ResultSource; 8] = [
    ResultSource {
        key: "matrix",
        directory: "tests",
        preferred_subdir: None,
    },
    ResultSource {
        key: "suite",
        directory: "suite",
        preferred_subdir: None,
    },
    ResultSource {
        key: "fuzz",
        directory: "fuzz",
        preferred_subdir: None,
    },
    ResultSource {
        key: "rustc",
        directory: "rustc",
        preferred_subdir: Some("ui"),
    },
    ResultSource {
        key: "bootstrap",
        directory: "bootstrap",
        preferred_subdir: None,
    },
    ResultSource {
        key: "ecosystem",
        directory: "ecosystem",
        preferred_subdir: None,
    },
    ResultSource {
        key: "prove",
        directory: "prove",
        preferred_subdir: None,
    },
    ResultSource {
        key: "pipeline",
        directory: "pipeline",
        preferred_subdir: None,
    },
];

fn discover_latest(root: &Path) -> BTreeMap<String, Option<LatestResult>> {
    let base = root.join("evals").join("results");
    let mut out: BTreeMap<String, Option<LatestResult>> = BTreeMap::new();
    for source in RESULT_SOURCES {
        out.insert(source.key.to_string(), discover_source(&base, source));
    }
    out
}

fn discover_source(base: &Path, source: ResultSource) -> Option<LatestResult> {
    let directory = base.join(source.directory);
    let mut candidates = Vec::new();
    collect_json_files(&directory, &mut candidates);
    candidates.sort_by(|left, right| {
        result_sort_key(&directory, right, source.preferred_subdir).cmp(&result_sort_key(
            &directory,
            left,
            source.preferred_subdir,
        ))
    });
    candidates
        .iter()
        .find_map(|path| read_compatible_result(path, source.key))
}

fn collect_json_files(directory: &Path, output: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_json_files(&path, output);
        } else if path.extension().and_then(|value| value.to_str()) == Some("json") {
            output.push(path);
        }
    }
}

fn result_sort_key(
    root: &Path,
    path: &Path,
    preferred_subdir: Option<&str>,
) -> (bool, String, String) {
    let relative = path.strip_prefix(root).unwrap_or(path);
    let preferred = preferred_subdir.is_some_and(|wanted| {
        relative
            .components()
            .any(|component| component.as_os_str() == wanted)
    });
    let stem = path
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or_default()
        .to_string();
    (preferred, stem, relative.to_string_lossy().into_owned())
}

fn read_compatible_result(path: &Path, fallback_command: &str) -> Option<LatestResult> {
    let text = fs::read_to_string(path).ok()?;
    let mut parsed = serde_json::from_str::<LatestResult>(&text).ok()?;
    if parsed.command.trim().is_empty() {
        parsed.command = fallback_command.to_string();
    }
    Some(parsed)
}

fn metric_cell(record: &Option<LatestResult>) -> String {
    let Some(r) = record else {
        return "—".to_string();
    };
    match &r.totals {
        Some(t) => serde_json::to_string(t).unwrap_or_else(|_| "—".to_string()),
        None => {
            let exit = r
                .exit
                .as_ref()
                .and_then(|v| v.as_str())
                .unwrap_or("unknown");
            format!("exit={exit}")
        }
    }
}

fn render_markdown(
    week_iso: &str,
    records: &BTreeMap<String, Option<LatestResult>>,
    sha: &str,
) -> String {
    let row = |ws: &str, layer: &str, metric: &str, rec: &Option<LatestResult>| -> String {
        format!(
            "| {ws} | {layer} | {metric} | {cell} |",
            cell = metric_cell(rec)
        )
    };
    let mut s = String::new();
    s.push_str(&format!("# Trust Codegen weekly report — {week_iso}\n\n"));
    s.push_str(&format!("Git commit: `{sha}`\n\n"));
    s.push_str("> Rendered by `trust-cg-test report`. `—` means not measured yet.\n\n");
    s.push_str("## North-star metrics\n\n");
    s.push_str("| WS | Layer | Metric | Latest |\n");
    s.push_str("|---|---|---|---|\n");
    s.push_str(&row(
        "WS1",
        "L1 Unit",
        "`cargo test` pass-count",
        records.get("matrix").unwrap_or(&None),
    ));
    s.push('\n');
    s.push_str(&row(
        "WS2",
        "L2 E2E",
        "`llvm-test-suite SingleSource` pass-rate",
        records.get("suite").unwrap_or(&None),
    ));
    s.push('\n');
    s.push_str(&row(
        "WS3",
        "L3 Fuzz",
        "miscompiles found/fixed",
        records.get("fuzz").unwrap_or(&None),
    ));
    s.push('\n');
    s.push_str(&row(
        "WS4",
        "L4 rustc",
        "rustc UI pass-rate",
        records.get("rustc").unwrap_or(&None),
    ));
    s.push('\n');
    s.push_str(&row(
        "WS5",
        "L5 Bootstrap",
        "rustc stage reached",
        records.get("bootstrap").unwrap_or(&None),
    ));
    s.push('\n');
    s.push_str(&row(
        "WS6",
        "L6 Ecosystem",
        "top-100 crates.io pass-rate",
        records.get("ecosystem").unwrap_or(&None),
    ));
    s.push('\n');
    s.push_str(&row(
        "WS7",
        "L7 Proof",
        "ay obligations discharged",
        records.get("prove").unwrap_or(&None),
    ));
    s.push('\n');
    s.push_str(&row(
        "WS8",
        "L8 Proof infra",
        "RA/sched/emit stages proven",
        records.get("pipeline").unwrap_or(&None),
    ));
    s.push('\n');
    s.push_str(
        "\n<sup>Cells marked `—` have no compatible artifact in the configured \
         workstream result directory. ",
    );
    s.push_str(
        "Run `trust-cg-test <ws> --help` to see whether that workflow emits \
         results in v0.1.0.</sup>\n\n",
    );
    s.push_str("## Per-workstream notes\n\n");
    for ws in [
        "matrix",
        "suite",
        "fuzz",
        "rustc",
        "bootstrap",
        "ecosystem",
        "prove",
        "pipeline",
    ] {
        s.push_str(&format!(
            "### {}\n\n",
            match ws {
                "matrix" => "WS1 — matrix",
                "suite" => "WS2 — suite",
                "fuzz" => "WS3 — fuzz",
                "rustc" => "WS4 — rustc",
                "bootstrap" => "WS5 — bootstrap",
                "ecosystem" => "WS6 — ecosystem",
                "prove" => "WS7 — prove",
                "pipeline" => "WS8 — pipeline",
                _ => ws,
            }
        ));
        match records.get(ws).unwrap_or(&None) {
            Some(r) => s.push_str(&format!(
                "Command: `{}`. Totals: {}.\n\n",
                r.command,
                metric_cell(&Some(LatestResult {
                    command: r.command.clone(),
                    totals: r.totals.clone(),
                    exit: r.exit.clone(),
                }))
            )),
            None => s.push_str(&format!(
                "No result yet. Run `trust-cg-test {ws} --help` for the current workflow.\n\n"
            )),
        }
    }
    s.push_str("## Source\n\n");
    s.push_str("This report is generated by `trust-cg-test report`. ");
    s.push_str("Do not hand-edit — regenerate via `trust-cg-test report`.\n");
    s
}

fn today_iso() -> String {
    Utc::now().format("%Y-%m-%d").to_string()
}

fn parse_week(input: &str) -> anyhow::Result<String> {
    NaiveDate::parse_from_str(input, "%Y-%m-%d")
        .with_context(|| format!("week must be YYYY-MM-DD, got {input:?}"))?;
    Ok(input.to_string())
}

fn weekly_report_path(repo: &Path, week: &str) -> PathBuf {
    repo.join("reports")
        .join("weekly")
        .join(format!("{week}.md"))
}

fn write_text(path: &Path, contents: &str) -> anyhow::Result<()> {
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, contents)?;
    Ok(())
}

fn write_report_outputs(
    repo: &Path,
    target: &Path,
    week: &str,
    markdown: &str,
    publish: bool,
) -> anyhow::Result<()> {
    write_text(target, markdown)?;
    if !publish {
        return Ok(());
    }

    let weekly = weekly_report_path(repo, week);
    if target != weekly {
        write_text(&weekly, markdown)?;
    }
    let dashboard = repo.join("reports").join("dashboard.md");
    let pointer = format!(
        "# Trust Codegen dashboard\n\nLatest weekly report: \
         [`reports/weekly/{week}.md`](weekly/{week}.md)\n"
    );
    write_text(&dashboard, &pointer)
}

fn repo_sha(root: &Path) -> String {
    // Works for plain repos and for linked worktrees where `.git` is a
    // file containing `gitdir: <path-to-worktree-gitdir>`.
    let git = root.join(".git");
    let git_dir = if git.is_dir() {
        git
    } else if let Ok(text) = fs::read_to_string(&git) {
        text.lines()
            .find_map(|l| l.strip_prefix("gitdir: ").map(str::trim).map(PathBuf::from))
            .unwrap_or_else(|| PathBuf::from(".git"))
    } else {
        return "unknown".to_string();
    };
    let head = git_dir.join("HEAD");
    let Ok(content) = fs::read_to_string(&head) else {
        return "unknown".to_string();
    };
    let content = content.trim();
    if let Some(reference) = content.strip_prefix("ref: ") {
        // For linked worktrees, refs are in the main repo's refs dir.
        // The common dir is captured by `commondir` next to `HEAD`.
        let commondir = git_dir.join("commondir");
        let base = if commondir.is_file() {
            let rel = fs::read_to_string(&commondir).unwrap_or_default();
            let rel = rel.trim();
            git_dir.join(rel)
        } else {
            git_dir.clone()
        };
        let ref_path = base.join(reference);
        return fs::read_to_string(ref_path)
            .ok()
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|| "unknown".to_string());
    }
    content.to_string()
}

/// Entry point.
pub fn run(global: &GlobalArgs, args: &ReportArgs) -> anyhow::Result<ResultStatus> {
    let repo = RepoRoot::locate(Path::new("."))?;
    let week = match &args.week {
        Some(w) => parse_week(w)?,
        None => today_iso(),
    };
    let records = discover_latest(&repo.0);
    let sha = repo_sha(&repo.0);
    let md = render_markdown(&week, &records, &sha);

    let target = if let Some(p) = args.markdown_out.clone() {
        p
    } else if let Some(p) = global.out.clone() {
        p
    } else {
        weekly_report_path(&repo.0, &week)
    };

    write_report_outputs(&repo.0, &target, &week, &md, args.publish)?;

    match global.format {
        OutputFormat::Json | OutputFormat::Junit => {
            let json = serde_json::json!({
                "command": "report",
                "week": week,
                "output": target,
                "bytes": md.len(),
            });
            println!("{json}");
        }
        OutputFormat::Human => {
            println!("trust-cg-test report");
            println!("  week:   {week}");
            println!("  output: {}", target.display());
            println!("  size:   {} bytes", md.len());
        }
    }

    Ok(ResultStatus::Ok)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_fixture(path: &Path, contents: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create fixture directory");
        }
        fs::write(path, contents).expect("write fixture");
    }

    #[test]
    fn discovers_matrix_artifact_from_tests_directory_without_command_field() {
        let temp = tempfile::tempdir().expect("temporary repository");
        write_fixture(
            &temp.path().join("evals/results/tests/2026-07-23.json"),
            r#"{"schema":"trust-cg.test-matrix.v1","totals":{"passed":42,"failed":0}}"#,
        );

        let records = discover_latest(temp.path());
        let matrix = records
            .get("matrix")
            .and_then(Option::as_ref)
            .expect("matrix result");
        assert_eq!(matrix.command, "matrix");
        assert_eq!(
            matrix
                .totals
                .as_ref()
                .and_then(|totals| totals.get("passed"))
                .and_then(serde_json::Value::as_u64),
            Some(42)
        );
    }

    #[test]
    fn discovers_nested_rustc_ui_artifact_before_other_rustc_modes() {
        let temp = tempfile::tempdir().expect("temporary repository");
        write_fixture(
            &temp.path().join("evals/results/rustc/2026-07-23.json"),
            r#"{"command":"rustc-feature-coverage","exit":"ok"}"#,
        );
        write_fixture(
            &temp.path().join("evals/results/rustc/ui/2026-07-22.json"),
            r#"{"command":"rustc-ui","exit":"ok"}"#,
        );

        let records = discover_latest(temp.path());
        let rustc = records
            .get("rustc")
            .and_then(Option::as_ref)
            .expect("rustc result");
        assert_eq!(rustc.command, "rustc-ui");
    }

    #[test]
    fn publish_with_custom_output_also_writes_canonical_weekly_report() {
        let temp = tempfile::tempdir().expect("temporary repository");
        let custom = temp.path().join("custom/report.md");
        write_report_outputs(
            temp.path(),
            &custom,
            "2026-07-23",
            "# generated report\n",
            true,
        )
        .expect("write report outputs");

        let weekly = temp.path().join("reports/weekly/2026-07-23.md");
        let dashboard = temp.path().join("reports/dashboard.md");
        assert_eq!(
            fs::read_to_string(&custom).expect("custom report"),
            "# generated report\n"
        );
        assert_eq!(
            fs::read_to_string(&weekly).expect("weekly report"),
            "# generated report\n"
        );
        assert!(
            fs::read_to_string(dashboard)
                .expect("dashboard pointer")
                .contains("(weekly/2026-07-23.md)")
        );
    }
}
