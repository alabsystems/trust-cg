use std::process::Command;

use serde_json::Value;
use sha2::{Digest, Sha256};

#[test]
fn phase8_ay_subsumption_cli_binds_counters_to_deterministic_manifest_hash() {
    let first = run_plan_only_matrix("first");
    let second = run_plan_only_matrix("second");

    assert_eq!(first.manifest_hash.len(), 64);
    assert!(first.manifest_hash.chars().all(|ch| ch.is_ascii_hexdigit()));
    assert_eq!(first.manifest_missing_count, 0);
    assert_eq!(first.manifest_hash, second.manifest_hash);
    assert_eq!(first.manifest_hash, first.canonical_manifest_sha256);
    assert_eq!(second.manifest_hash, second.canonical_manifest_sha256);
    assert!(first.final_manifest_artifact_count > 0);
    assert!(second.final_manifest_artifact_count > 0);
    assert!(first.final_manifest_contains_canonical_preimage);
    assert!(second.final_manifest_contains_canonical_preimage);
    assert!(first.canonical_preimage_excludes_final_manifest);
    assert!(first.canonical_preimage_excludes_counters);
    assert_eq!(first.manifest_sha256_file, first.manifest_hash);
    assert_eq!(first.gate_manifest_hash, first.manifest_hash);
    assert_eq!(first.replay_manifest_hash, first.manifest_hash);
    assert_eq!(first.gate_verdict, "non_promoting");
    assert!(first.gate_plan_only);
    assert!(first.gate_missing_no_regression_comparison);
    assert_eq!(first.gate_useful_native_count, 0);
    assert!(first.final_manifest_contains_gate_results);
    assert!(first.final_manifest_contains_command_metadata);
    assert!(first.final_manifest_contains_replay_descriptor);
    assert_eq!(
        first.manifest_source_cases_status.as_deref(),
        Some("present")
    );
    assert_eq!(
        first.manifest_ay_revision_status.as_deref(),
        Some("blocked")
    );
}

struct PlanOnlyRun {
    manifest_hash: String,
    canonical_manifest_sha256: String,
    manifest_sha256_file: String,
    gate_manifest_hash: String,
    replay_manifest_hash: String,
    gate_verdict: String,
    gate_plan_only: bool,
    gate_missing_no_regression_comparison: bool,
    gate_useful_native_count: u64,
    manifest_missing_count: u64,
    final_manifest_artifact_count: usize,
    final_manifest_contains_canonical_preimage: bool,
    final_manifest_contains_gate_results: bool,
    final_manifest_contains_command_metadata: bool,
    final_manifest_contains_replay_descriptor: bool,
    canonical_preimage_excludes_final_manifest: bool,
    canonical_preimage_excludes_counters: bool,
    manifest_source_cases_status: Option<String>,
    manifest_ay_revision_status: Option<String>,
}

fn run_plan_only_matrix(name: &str) -> PlanOnlyRun {
    let temp_dir = tempfile::tempdir().expect("tempdir");
    let out_dir = temp_dir.path().join(name);
    let cases = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/ay_subsumption_cases.json");
    let status = Command::new(env!("CARGO_BIN_EXE_ay_subsumption_matrix"))
        .arg("--cases")
        .arg(cases)
        .arg("--out-dir")
        .arg(&out_dir)
        .arg("--plan-only")
        .status()
        .expect("ay_subsumption_matrix should run");
    assert!(status.success());

    let counters: Value = serde_json::from_slice(
        &std::fs::read(out_dir.join("phase8_native_promotion_counters.json"))
            .expect("counter artifact should exist"),
    )
    .expect("counter artifact should parse");
    let manifest: Value = serde_json::from_slice(
        &std::fs::read(out_dir.join("artifact.manifest.json")).expect("manifest should exist"),
    )
    .expect("manifest should parse");
    let canonical_manifest_bytes = std::fs::read(out_dir.join("artifact.manifest.canonical.json"))
        .expect("canonical manifest preimage should exist");
    let manifest_sha256_file = std::fs::read_to_string(out_dir.join("artifact.manifest.sha256"))
        .expect("manifest sha256 file should exist")
        .trim()
        .to_string();
    let gate_results: Value = serde_json::from_slice(
        &std::fs::read(out_dir.join("gate-results.json")).expect("gate results should exist"),
    )
    .expect("gate results should parse");
    let replay: Value = serde_json::from_slice(
        &std::fs::read(out_dir.join("replay-reproduction.json"))
            .expect("replay descriptor should exist"),
    )
    .expect("replay descriptor should parse");
    let canonical_manifest: Value =
        serde_json::from_slice(&canonical_manifest_bytes).expect("canonical manifest should parse");
    let canonical_manifest_sha256 = sha256_hex(&canonical_manifest_bytes);
    let final_manifest_artifacts = manifest["artifacts"]
        .as_array()
        .expect("manifest artifacts should be an array");
    let canonical_manifest_artifacts = canonical_manifest["artifacts"]
        .as_array()
        .expect("canonical manifest artifacts should be an array");

    PlanOnlyRun {
        manifest_hash: counters["counter_scope"]["manifest_sha256"]
            .as_str()
            .expect("counter manifest hash should be present")
            .to_string(),
        canonical_manifest_sha256,
        manifest_sha256_file,
        gate_manifest_hash: gate_results["canonical_manifest_sha256"]
            .as_str()
            .expect("gate manifest hash should be present")
            .to_string(),
        replay_manifest_hash: replay["canonical_manifest_sha256"]
            .as_str()
            .expect("replay manifest hash should be present")
            .to_string(),
        gate_verdict: gate_results["verdict"]
            .as_str()
            .expect("gate verdict should be present")
            .to_string(),
        gate_plan_only: gate_results["plan_only"]
            .as_bool()
            .expect("gate plan_only should be boolean"),
        gate_missing_no_regression_comparison: gate_results["missing_no_regression_comparison"]
            .as_bool()
            .expect("gate missing_no_regression_comparison should be boolean"),
        gate_useful_native_count: gate_results["counts"]["useful_native"]
            .as_u64()
            .expect("gate useful_native count should be numeric"),
        manifest_missing_count: counters["artifact_gate"]["manifest_missing_count"]
            .as_u64()
            .expect("manifest missing count should be numeric"),
        final_manifest_artifact_count: final_manifest_artifacts.len(),
        final_manifest_contains_canonical_preimage: final_manifest_artifacts.iter().any(
            |artifact| {
                artifact["path"]
                    .as_str()
                    .is_some_and(|path| path.ends_with("artifact.manifest.canonical.json"))
            },
        ),
        final_manifest_contains_gate_results: final_manifest_artifacts.iter().any(|artifact| {
            artifact["path"]
                .as_str()
                .is_some_and(|path| path.ends_with("gate-results.json"))
        }),
        final_manifest_contains_command_metadata: final_manifest_artifacts.iter().any(|artifact| {
            artifact["path"]
                .as_str()
                .is_some_and(|path| path.ends_with("command-metadata.json"))
        }),
        final_manifest_contains_replay_descriptor: final_manifest_artifacts.iter().any(
            |artifact| {
                artifact["path"]
                    .as_str()
                    .is_some_and(|path| path.ends_with("replay-reproduction.json"))
            },
        ),
        canonical_preimage_excludes_final_manifest: !canonical_manifest_artifacts.iter().any(
            |artifact| {
                artifact["path"]
                    .as_str()
                    .is_some_and(|path| path.contains("artifact.manifest.json"))
            },
        ),
        canonical_preimage_excludes_counters: !canonical_manifest_artifacts.iter().any(
            |artifact| {
                artifact["path"]
                    .as_str()
                    .is_some_and(|path| path.contains("phase8_native_promotion_counters.json"))
            },
        ),
        manifest_source_cases_status: manifest["evidence"]["source_cases_input"]["status"]
            .as_str()
            .map(str::to_string),
        manifest_ay_revision_status: manifest["evidence"]["ay_revision"]["status"]
            .as_str()
            .map(str::to_string),
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}
