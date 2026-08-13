// Phase 3 JIT diagnostic dashboard fixture exporter.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust-cg-test jit-diagnostic-dashboard` fixture export generator.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, bail};
use clap::Args;
use serde::{Deserialize, Serialize};

use super::GlobalArgs;
use crate::OutputFormat;
use crate::config::RepoRoot;
use crate::results::ResultStatus;

const FIXTURE_FILES: [(&str, &str); 5] = [
    ("status_matrix", "status-matrix.json"),
    ("replay_bundle", "replay-bundle-decisions.json"),
    ("verifier_rejections", "verifier-rejections.json"),
    ("proof_tv_outcomes", "proof-tv-outcomes.json"),
    (
        "proof_guided_optimization_dispositions",
        "proof-guided-optimization-dispositions.json",
    ),
];

const LEGACY_FIXTURE_ISSUE: &str = "#711";
const PROOF_GUIDED_FIXTURE_ISSUE: &str = "#799";
const NOT_APPLICABLE: &str = "not_applicable";
const USEFUL_NATIVE_PROMOTED: &str = "useful_native_promoted";
const PROOF_DISPOSITIONS: [&str; 8] = [
    NOT_APPLICABLE,
    "proof_missing",
    "proof_unrepresentable",
    "rewrite_rejected",
    "candidate_disabled",
    "proved_profile_only",
    "gate_failed",
    USEFUL_NATIVE_PROMOTED,
];

/// Arguments for `trust-cg-test jit-diagnostic-dashboard`.
#[derive(Args, Debug, Clone)]
#[command(long_about = "Generate Phase 3 JIT diagnostic dashboard exports \
                  from checked-in fixtures.")]
pub struct JitDiagnosticDashboardArgs {
    /// Directory containing the checked-in dashboard fixture inputs.
    #[arg(long, value_name = "DIR")]
    pub input_dir: Option<PathBuf>,

    /// Directory where dashboard exports should be written.
    #[arg(long, value_name = "DIR")]
    pub output_dir: Option<PathBuf>,
}

#[derive(Clone, Debug, Deserialize)]
struct FixtureDocument {
    fixture_issue: String,
    source_issue: String,
    rows: Vec<FixtureRow>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct FixtureRow {
    candidate_id: String,
    consumer: String,
    family: String,
    #[serde(default = "default_not_applicable")]
    kernel_family: String,
    #[serde(default = "default_not_applicable")]
    proof_disposition: String,
    #[serde(default = "default_not_applicable")]
    transform_id: String,
    #[serde(default = "default_not_applicable")]
    transform_version: String,
    #[serde(default = "default_not_applicable")]
    certificate_id: String,
    #[serde(default = "default_not_applicable")]
    certificate_hash: String,
    #[serde(default = "default_not_applicable")]
    manifest_hash: String,
    #[serde(default = "default_not_applicable")]
    proof_validation_hash: String,
    #[serde(default = "default_not_applicable")]
    replay_root: String,
    #[serde(default = "default_not_applicable")]
    useful_native_counter_status: String,
    #[serde(default = "default_not_applicable")]
    raw_rejection_code: String,
    #[serde(default = "default_not_applicable")]
    normalized_reason: String,
    status_kind: String,
    failure_category: String,
    failure_code: String,
    install_disposition: String,
    native_disposition: String,
    promotion_disposition: String,
    dashboard_state: String,
    blocker_kind: String,
    evidence_refs: Vec<String>,
    downstream_blockers: Vec<String>,
    useful_native_eligible: bool,
    useful_native_count: u64,
}

#[derive(Clone, Debug, Serialize)]
struct CandidateRow {
    candidate_id: String,
    consumer: String,
    family: String,
    kernel_family: String,
    source_fixture: String,
    source_issue: String,
    proof_disposition: String,
    transform_id: String,
    transform_version: String,
    certificate_id: String,
    certificate_hash: String,
    manifest_hash: String,
    proof_validation_hash: String,
    replay_root: String,
    useful_native_counter_status: String,
    raw_rejection_code: String,
    normalized_reason: String,
    status_kind: String,
    failure_category: String,
    failure_code: String,
    install_disposition: String,
    native_disposition: String,
    promotion_disposition: String,
    dashboard_state: String,
    blocker_kind: String,
    evidence_refs: Vec<String>,
    downstream_blockers: Vec<String>,
    useful_native_eligible: bool,
    useful_native_count: u64,
}

#[derive(Clone, Debug, Serialize)]
struct CandidateTable {
    schema: &'static str,
    generated_from: Vec<String>,
    rows: Vec<CandidateRow>,
}

#[derive(Clone, Debug, Serialize)]
struct DashboardSummary {
    schema: &'static str,
    issue: &'static str,
    proof_guided_issue: &'static str,
    parent_issue: &'static str,
    source_issues: Vec<String>,
    row_count: usize,
    blocker_count: usize,
    proof_guided_row_count: usize,
    useful_native_count: u64,
    useful_native_eligible_count: usize,
    rows_by_consumer: BTreeMap<String, usize>,
    rows_by_kernel_family: BTreeMap<String, usize>,
    rows_by_proof_disposition: BTreeMap<String, usize>,
    rows_by_state: BTreeMap<String, usize>,
    rows_by_blocker_kind: BTreeMap<String, usize>,
    downstream_blockers: Vec<String>,
    outputs: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct CounterSummary {
    schema: &'static str,
    row_count: usize,
    useful_native_count: u64,
    useful_native_eligible_count: usize,
    non_promoting_count: usize,
    proof_guided_row_count: usize,
    by_install_disposition: BTreeMap<String, usize>,
    by_native_disposition: BTreeMap<String, usize>,
    by_status_kind: BTreeMap<String, usize>,
    by_consumer: BTreeMap<String, usize>,
    by_kernel_family: BTreeMap<String, usize>,
    by_proof_disposition: BTreeMap<String, usize>,
    by_useful_native_counter_status: BTreeMap<String, usize>,
    by_consumer_proof_disposition: BTreeMap<String, BTreeMap<String, usize>>,
}

#[derive(Clone, Debug, Serialize)]
struct BlockerTable {
    schema: &'static str,
    blockers: Vec<BlockerRow>,
}

#[derive(Clone, Debug, Serialize)]
struct BlockerRow {
    candidate_id: String,
    consumer: String,
    kernel_family: String,
    proof_disposition: String,
    transform_id: String,
    transform_version: String,
    certificate_id: String,
    certificate_hash: String,
    manifest_hash: String,
    proof_validation_hash: String,
    replay_root: String,
    useful_native_counter_status: String,
    raw_rejection_code: String,
    normalized_reason: String,
    blocker_kind: String,
    status_kind: String,
    failure_category: String,
    failure_code: String,
    source_issue: String,
    evidence_refs: Vec<String>,
    downstream_blockers: Vec<String>,
}

fn default_not_applicable() -> String {
    NOT_APPLICABLE.to_owned()
}

fn is_known_proof_disposition(disposition: &str) -> bool {
    PROOF_DISPOSITIONS.contains(&disposition)
}

fn is_proof_guided(row: &CandidateRow) -> bool {
    row.proof_disposition != NOT_APPLICABLE
}

fn is_promoting(row: &CandidateRow) -> bool {
    row.proof_disposition == USEFUL_NATIVE_PROMOTED
        || row.promotion_disposition == USEFUL_NATIVE_PROMOTED
}

fn is_blocker(row: &CandidateRow) -> bool {
    !is_promoting(row)
}

fn read_rows(input_dir: &Path) -> anyhow::Result<Vec<CandidateRow>> {
    let mut rows = Vec::new();
    for (source_fixture, file_name) in FIXTURE_FILES {
        let path = input_dir.join(file_name);
        let text = fs::read_to_string(&path)
            .with_context(|| format!("read fixture input {}", path.display()))?;
        let document: FixtureDocument = serde_json::from_str(&text)
            .with_context(|| format!("parse fixture input {}", path.display()))?;
        if document.fixture_issue != LEGACY_FIXTURE_ISSUE
            && document.fixture_issue != PROOF_GUIDED_FIXTURE_ISSUE
        {
            bail!(
                "{} fixture_issue must be {LEGACY_FIXTURE_ISSUE} or {PROOF_GUIDED_FIXTURE_ISSUE}, got {}",
                path.display(),
                document.fixture_issue
            );
        }
        for row in document.rows {
            if !is_known_proof_disposition(&row.proof_disposition) {
                bail!(
                    "{} row {} has unknown proof disposition {}",
                    path.display(),
                    row.candidate_id,
                    row.proof_disposition
                );
            }
            let is_promoted = row.proof_disposition == USEFUL_NATIVE_PROMOTED
                || row.promotion_disposition == USEFUL_NATIVE_PROMOTED;
            if !is_promoted && row.promotion_disposition != "non_promoting" {
                bail!(
                    "{} row {} is not non_promoting or useful-native promoted",
                    path.display(),
                    row.candidate_id
                );
            }
            if is_promoted {
                if !row.useful_native_eligible || row.useful_native_count == 0 {
                    bail!(
                        "{} row {} has promoted disposition without useful-native count",
                        path.display(),
                        row.candidate_id
                    );
                }
            } else if row.useful_native_eligible || row.useful_native_count != 0 {
                bail!(
                    "{} row {} would promote useful-native evidence",
                    path.display(),
                    row.candidate_id
                );
            }
            if !is_promoted && (row.blocker_kind.is_empty() || row.blocker_kind == "none") {
                bail!(
                    "{} row {} has no typed blocker kind",
                    path.display(),
                    row.candidate_id
                );
            }
            rows.push(CandidateRow {
                candidate_id: row.candidate_id,
                consumer: row.consumer,
                family: row.family,
                kernel_family: row.kernel_family,
                source_fixture: source_fixture.to_owned(),
                source_issue: document.source_issue.clone(),
                proof_disposition: row.proof_disposition,
                transform_id: row.transform_id,
                transform_version: row.transform_version,
                certificate_id: row.certificate_id,
                certificate_hash: row.certificate_hash,
                manifest_hash: row.manifest_hash,
                proof_validation_hash: row.proof_validation_hash,
                replay_root: row.replay_root,
                useful_native_counter_status: row.useful_native_counter_status,
                raw_rejection_code: row.raw_rejection_code,
                normalized_reason: row.normalized_reason,
                status_kind: row.status_kind,
                failure_category: row.failure_category,
                failure_code: row.failure_code,
                install_disposition: row.install_disposition,
                native_disposition: row.native_disposition,
                promotion_disposition: row.promotion_disposition,
                dashboard_state: row.dashboard_state,
                blocker_kind: row.blocker_kind,
                evidence_refs: row.evidence_refs,
                downstream_blockers: row.downstream_blockers,
                useful_native_eligible: row.useful_native_eligible,
                useful_native_count: row.useful_native_count,
            });
        }
    }
    rows.sort_by(|left, right| left.candidate_id.cmp(&right.candidate_id));
    Ok(rows)
}

fn count_by(rows: &[CandidateRow], f: impl Fn(&CandidateRow) -> &str) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry(f(row).to_owned()).or_insert(0) += 1;
    }
    counts
}

fn count_by_pair(
    rows: &[CandidateRow],
    outer: impl Fn(&CandidateRow) -> &str,
    inner: impl Fn(&CandidateRow) -> &str,
) -> BTreeMap<String, BTreeMap<String, usize>> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts
            .entry(outer(row).to_owned())
            .or_insert_with(BTreeMap::new)
            .entry(inner(row).to_owned())
            .or_insert(0) += 1;
    }
    counts
}

fn downstream_blockers(rows: &[CandidateRow]) -> Vec<String> {
    let mut blockers = BTreeSet::new();
    for row in rows {
        for issue in &row.downstream_blockers {
            blockers.insert(issue.clone());
        }
    }
    blockers.into_iter().collect()
}

fn source_issues(rows: &[CandidateRow]) -> Vec<String> {
    let mut issues = BTreeSet::new();
    issues.insert("#661".to_owned());
    issues.insert("#704".to_owned());
    issues.insert("#710".to_owned());
    for row in rows {
        issues.insert(row.source_issue.clone());
        for evidence in &row.evidence_refs {
            if evidence.starts_with('#') {
                issues.insert(evidence.clone());
            }
        }
    }
    issues.into_iter().collect()
}

fn build_outputs(
    rows: &[CandidateRow],
) -> (
    DashboardSummary,
    CandidateTable,
    CounterSummary,
    BlockerTable,
) {
    let useful_native_count = rows.iter().map(|row| row.useful_native_count).sum();
    let useful_native_eligible_count = rows.iter().filter(|row| row.useful_native_eligible).count();
    let proof_guided_row_count = rows.iter().filter(|row| is_proof_guided(row)).count();
    let blockers = rows
        .iter()
        .filter(|row| is_blocker(row))
        .map(|row| BlockerRow {
            candidate_id: row.candidate_id.clone(),
            consumer: row.consumer.clone(),
            kernel_family: row.kernel_family.clone(),
            proof_disposition: row.proof_disposition.clone(),
            transform_id: row.transform_id.clone(),
            transform_version: row.transform_version.clone(),
            certificate_id: row.certificate_id.clone(),
            certificate_hash: row.certificate_hash.clone(),
            manifest_hash: row.manifest_hash.clone(),
            proof_validation_hash: row.proof_validation_hash.clone(),
            replay_root: row.replay_root.clone(),
            useful_native_counter_status: row.useful_native_counter_status.clone(),
            raw_rejection_code: row.raw_rejection_code.clone(),
            normalized_reason: row.normalized_reason.clone(),
            blocker_kind: row.blocker_kind.clone(),
            status_kind: row.status_kind.clone(),
            failure_category: row.failure_category.clone(),
            failure_code: row.failure_code.clone(),
            source_issue: row.source_issue.clone(),
            evidence_refs: row.evidence_refs.clone(),
            downstream_blockers: row.downstream_blockers.clone(),
        })
        .collect::<Vec<_>>();
    let summary = DashboardSummary {
        schema: "trust-cg.jit_diagnostic_dashboard.summary/v1",
        issue: LEGACY_FIXTURE_ISSUE,
        proof_guided_issue: PROOF_GUIDED_FIXTURE_ISSUE,
        parent_issue: "#661",
        source_issues: source_issues(rows),
        row_count: rows.len(),
        blocker_count: blockers.len(),
        proof_guided_row_count,
        useful_native_count,
        useful_native_eligible_count,
        rows_by_consumer: count_by(rows, |row| &row.consumer),
        rows_by_kernel_family: count_by(rows, |row| &row.kernel_family),
        rows_by_proof_disposition: count_by(rows, |row| &row.proof_disposition),
        rows_by_state: count_by(rows, |row| &row.dashboard_state),
        rows_by_blocker_kind: count_by(rows, |row| &row.blocker_kind),
        downstream_blockers: downstream_blockers(rows),
        outputs: vec![
            "dashboard-summary.json".to_owned(),
            "candidate-table.json".to_owned(),
            "counter-summary.json".to_owned(),
            "blockers.json".to_owned(),
            "dashboard-summary.md".to_owned(),
        ],
    };
    let table = CandidateTable {
        schema: "trust-cg.jit_diagnostic_dashboard.candidate_table/v1",
        generated_from: FIXTURE_FILES
            .iter()
            .map(|(_, file_name)| format!("tests/fixtures/jit_diagnostic_dashboard/{file_name}"))
            .collect(),
        rows: rows.to_vec(),
    };
    let counters = CounterSummary {
        schema: "trust-cg.jit_diagnostic_dashboard.counter_summary/v1",
        row_count: rows.len(),
        useful_native_count,
        useful_native_eligible_count,
        non_promoting_count: rows
            .iter()
            .filter(|row| row.promotion_disposition == "non_promoting")
            .count(),
        proof_guided_row_count,
        by_install_disposition: count_by(rows, |row| &row.install_disposition),
        by_native_disposition: count_by(rows, |row| &row.native_disposition),
        by_status_kind: count_by(rows, |row| &row.status_kind),
        by_consumer: count_by(rows, |row| &row.consumer),
        by_kernel_family: count_by(rows, |row| &row.kernel_family),
        by_proof_disposition: count_by(rows, |row| &row.proof_disposition),
        by_useful_native_counter_status: count_by(rows, |row| &row.useful_native_counter_status),
        by_consumer_proof_disposition: count_by_pair(
            rows,
            |row| &row.consumer,
            |row| &row.proof_disposition,
        ),
    };
    let blocker_table = BlockerTable {
        schema: "trust-cg.jit_diagnostic_dashboard.blockers/v1",
        blockers,
    };
    (summary, table, counters, blocker_table)
}

fn render_markdown(summary: &DashboardSummary, rows: &[CandidateRow]) -> String {
    let mut out = String::new();
    out.push_str("# JIT diagnostic dashboard\n\n");
    out.push_str(
        "Generated by `trust-cg-test jit-diagnostic-dashboard` from fixture inputs only.\n\n",
    );
    out.push_str("## Summary\n\n");
    out.push_str("| Metric | Value |\n");
    out.push_str("|---|---:|\n");
    out.push_str(&format!("| Candidate rows | {} |\n", summary.row_count));
    out.push_str(&format!("| Typed blockers | {} |\n", summary.blocker_count));
    out.push_str(&format!(
        "| Proof-guided rows | {} |\n",
        summary.proof_guided_row_count
    ));
    out.push_str(&format!(
        "| Useful-native eligible rows | {} |\n",
        summary.useful_native_eligible_count
    ));
    out.push_str(&format!(
        "| Useful-native count | {} |\n\n",
        summary.useful_native_count
    ));
    out.push_str("## Proof Dispositions\n\n");
    out.push_str("| Disposition | Rows |\n");
    out.push_str("|---|---:|\n");
    for (disposition, count) in &summary.rows_by_proof_disposition {
        out.push_str(&format!("| `{disposition}` | {count} |\n"));
    }
    out.push('\n');
    out.push_str("## Candidate Rows\n\n");
    out.push_str(
        "| Candidate | Consumer | Kernel | Proof disposition | Transform | Cert | Manifest | Proof/validation | Replay | Counter | Raw code | Reason | Blocker | Issues |\n",
    );
    out.push_str("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|\n");
    for row in rows {
        let mut issues = row.evidence_refs.clone();
        issues.extend(row.downstream_blockers.clone());
        issues.sort();
        issues.dedup();
        out.push_str(&format!(
            "| `{}` | `{}` | `{}` | `{}` | `{}`@`{}` | `{}` / `{}` | `{}` | `{}` | `{}` | `{}` | `{}` | `{}` | `{}` | {} |\n",
            row.candidate_id,
            row.consumer,
            row.kernel_family,
            row.proof_disposition,
            row.transform_id,
            row.transform_version,
            row.certificate_id,
            row.certificate_hash,
            row.manifest_hash,
            row.proof_validation_hash,
            row.replay_root,
            row.useful_native_counter_status,
            row.raw_rejection_code,
            row.normalized_reason,
            row.blocker_kind,
            issues.join(", ")
        ));
    }
    out.push_str("\n## Non-Promotion Contract\n\n");
    out.push_str(
        "Rows with missing manifests, proof/validation hashes, replay roots, \
         or useful-native counters remain visible as `non_promoting` typed \
         blockers. `useful_native_promoted` rows carry the positive counter \
         evidence needed to keep them out of `blockers.json`.\n",
    );
    out
}

fn write_json<T: Serialize>(path: &Path, value: &T) -> anyhow::Result<()> {
    let json = serde_json::to_string_pretty(value)?;
    fs::write(path, format!("{json}\n"))?;
    Ok(())
}

fn write_outputs(
    output_dir: &Path,
    summary: &DashboardSummary,
    table: &CandidateTable,
    counters: &CounterSummary,
    blockers: &BlockerTable,
    markdown: &str,
) -> anyhow::Result<()> {
    fs::create_dir_all(output_dir)?;
    write_json(&output_dir.join("dashboard-summary.json"), summary)?;
    write_json(&output_dir.join("candidate-table.json"), table)?;
    write_json(&output_dir.join("counter-summary.json"), counters)?;
    write_json(&output_dir.join("blockers.json"), blockers)?;
    fs::write(output_dir.join("dashboard-summary.md"), markdown)?;
    Ok(())
}

/// Entry point.
pub fn run(global: &GlobalArgs, args: &JitDiagnosticDashboardArgs) -> anyhow::Result<ResultStatus> {
    let repo = RepoRoot::locate(Path::new("."))?;
    let input_dir = args.input_dir.clone().unwrap_or_else(|| {
        repo.join("tests")
            .join("fixtures")
            .join("jit_diagnostic_dashboard")
    });
    let output_dir = args
        .output_dir
        .clone()
        .or_else(|| global.out.clone())
        .unwrap_or_else(|| repo.join("reports").join("jit-diagnostic-dashboard"));

    let rows = read_rows(&input_dir)?;
    let (summary, table, counters, blockers) = build_outputs(&rows);
    let markdown = render_markdown(&summary, &rows);
    write_outputs(
        &output_dir,
        &summary,
        &table,
        &counters,
        &blockers,
        &markdown,
    )?;

    match global.format {
        OutputFormat::Json | OutputFormat::Junit => {
            let json = serde_json::json!({
                "command": "jit-diagnostic-dashboard",
                "input_dir": input_dir,
                "output_dir": output_dir,
                "row_count": summary.row_count,
                "blocker_count": summary.blocker_count,
                "proof_guided_row_count": summary.proof_guided_row_count,
                "useful_native_count": summary.useful_native_count,
            });
            println!("{json}");
        }
        OutputFormat::Human => {
            println!("trust-cg-test jit-diagnostic-dashboard");
            println!("  input:  {}", input_dir.display());
            println!("  output: {}", output_dir.display());
            println!("  rows:   {}", summary.row_count);
            println!("  blockers: {}", summary.blocker_count);
            println!("  proof-guided rows: {}", summary.proof_guided_row_count);
        }
    }

    Ok(ResultStatus::Ok)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixture_rows_remain_non_promoting_typed_blockers() {
        let input = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join("tests")
            .join("fixtures")
            .join("jit_diagnostic_dashboard");
        let rows = read_rows(&input).expect("fixture rows should parse");
        let (summary, _table, counters, blockers) = build_outputs(&rows);
        let non_promoting_count = rows
            .iter()
            .filter(|row| row.promotion_disposition == "non_promoting")
            .count();

        assert_eq!(summary.blocker_count, non_promoting_count);
        assert_eq!(counters.non_promoting_count, non_promoting_count);
        assert_eq!(blockers.blockers.len(), non_promoting_count);

        for expected in [
            "unmatched",
            "incomplete",
            "stale",
            "rejected",
            "replay_only",
            "blocked",
        ] {
            assert!(
                summary.rows_by_blocker_kind.contains_key(expected),
                "missing blocker kind {expected}"
            );
        }

        for row in rows
            .iter()
            .filter(|row| row.promotion_disposition == "non_promoting")
        {
            assert_eq!(row.useful_native_count, 0);
            assert!(!row.useful_native_eligible);
            assert_ne!(row.blocker_kind, "none");
        }
    }

    #[test]
    fn proof_guided_rows_expose_normalized_dispositions_and_identity() {
        let input = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join("tests")
            .join("fixtures")
            .join("jit_diagnostic_dashboard");
        let rows = read_rows(&input).expect("fixture rows should parse");
        let (summary, _table, counters, blockers) = build_outputs(&rows);
        let proof_rows = rows
            .iter()
            .filter(|row| row.source_fixture == "proof_guided_optimization_dispositions")
            .collect::<Vec<_>>();

        assert_eq!(proof_rows.len(), 7);
        assert_eq!(summary.proof_guided_row_count, 7);
        assert_eq!(counters.proof_guided_row_count, 7);
        assert_eq!(
            proof_rows.iter().filter(|row| row.consumer == "ay").count(),
            4
        );
        assert_eq!(
            proof_rows.iter().filter(|row| row.consumer == "ty").count(),
            3
        );

        for expected in [
            "proof_missing",
            "proof_unrepresentable",
            "rewrite_rejected",
            "candidate_disabled",
            "proved_profile_only",
            "gate_failed",
            "useful_native_promoted",
        ] {
            assert_eq!(
                counters.by_proof_disposition.get(expected),
                Some(&1),
                "missing proof disposition {expected}"
            );
        }

        let missing = proof_rows
            .iter()
            .find(|row| row.candidate_id == "ay-lra-inline-proof-missing")
            .expect("missing-proof row is present");
        assert_eq!(missing.consumer, "ay");
        assert_eq!(missing.kernel_family, "ay_lra");
        assert_eq!(missing.proof_disposition, "proof_missing");
        assert_eq!(missing.manifest_hash, "missing");
        assert_eq!(missing.proof_validation_hash, "missing");
        assert_eq!(missing.replay_root, "missing");
        assert_eq!(missing.useful_native_counter_status, "missing");
        assert_eq!(missing.promotion_disposition, "non_promoting");

        let promoted = proof_rows
            .iter()
            .find(|row| row.candidate_id == "ay-lra-const-fold-useful-native")
            .expect("promoted-style row is present");
        assert_eq!(promoted.proof_disposition, "useful_native_promoted");
        assert_eq!(promoted.promotion_disposition, "useful_native_promoted");
        assert!(promoted.useful_native_eligible);
        assert!(promoted.useful_native_count > 0);
        assert!(
            blockers
                .blockers
                .iter()
                .all(|row| row.candidate_id != promoted.candidate_id)
        );
    }
}
