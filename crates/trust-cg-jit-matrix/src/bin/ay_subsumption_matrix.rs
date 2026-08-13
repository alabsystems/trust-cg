// ay_subsumption_matrix.rs - #571 ay subsumption benchmark runner CLI.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result, bail};
use clap::Parser;
use serde::Serialize;
use sha2::{Digest, Sha256};

use trust_cg_jit_matrix::{
    AYReferenceBackendState, AYReferenceExecutionReport, BackendReadinessReport, CorrectnessReport,
    PHASE8_AY_PROMOTION_PACKET_REQUIRED_ARTIFACTS, PHASE8_AY_SUBSUMPTION_COUNTER_FAMILY,
    PHASE8_AY_SUBSUMPTION_PROOF_POLICY, PHASE8_NATIVE_PROMOTION_CANARY_MODE,
    Phase8NativePromotionCounterScope, ThroughputSummaryReport, TrustCgBackendExecutionReport,
    TrustCgBackendProbeReport, ay_numeric_length_buckets, ay_reference_source_checks,
    ay_subsumption_correctness_with_full_backend_execution,
    ay_subsumption_throughput_csv_with_backend_buckets, load_ay_subsumption_cases,
    phase8_ay_promotion_packet_missing_artifact_blockers,
    phase8_ay_subsumption_native_promotion_counters,
    planned_ay_subsumption_backend_readiness_with_full_backend_execution,
    planned_ay_subsumption_throughput_with_backend_buckets,
    run_ay_reference_execution_with_length_buckets,
    run_trust_cg_backend_execution_with_length_buckets,
    run_trust_cg_backend_probe_with_length_buckets, validate_ay_subsumption_cases,
};

const MAX_JIT_MATRIX_ARTIFACT_BYTES: u64 = 16 * 1024 * 1024;
const MAX_JIT_MATRIX_GIT_OUTPUT_BYTES: u64 = 4 * 1024 * 1024;

#[derive(Debug, Parser)]
#[command(
    name = "ay_subsumption_matrix",
    about = "Validate and plan the #571 ay subsumption JIT benchmark matrix",
    long_about = "Validates benchmarks/jit-matrix/ay-subsumption/cases.json and \
emits the #571 artifact contract. Optional execution switches can populate ay \
reference and Trust Codegen backend rows; a non-plan run exits successfully only when \
the complete artifact gate has no pending rows, no correctness mismatches, no \
gate blockers, and a passing ay-relative throughput gate."
)]
struct Args {
    /// ay subsumption cases JSON.
    #[arg(long)]
    cases: PathBuf,

    /// ay checkout to use for the reference backend.
    #[arg(long)]
    ay_repo: Option<PathBuf>,

    /// ay revision to record.
    #[arg(long, default_value = "origin/main")]
    ay_rev: String,

    /// Target triple for the benchmark run.
    #[arg(long, default_value = "aarch64-apple-darwin")]
    target: String,

    /// Comma-separated variants requested by the runner.
    #[arg(long, value_delimiter = ',')]
    variants: Vec<String>,

    /// Comma-separated length buckets requested by the runner.
    #[arg(long, value_delimiter = ',')]
    length_buckets: Vec<String>,

    /// Warmup iterations requested by the runner.
    #[arg(long)]
    warmup_iterations: Option<u64>,

    /// Measurement repetitions requested by the runner.
    #[arg(long)]
    measurement_repetitions: Option<u64>,

    /// Output directory for plan artifacts.
    #[arg(long)]
    out_dir: PathBuf,

    /// Emit validation artifacts without attempting benchmark execution.
    #[arg(long)]
    plan_only: bool,

    /// Run the bounded Trust Codegen raw-JIT padded scanner backend probe.
    #[arg(long)]
    run_trust_cg_probe: bool,

    /// Populate bounded Trust Codegen mixed-fixture throughput rows from the Trust Codegen probe.
    #[arg(long)]
    run_trust_cg_mixed_rows: bool,

    /// Populate bounded Trust Codegen probe throughput rows for comma-separated numeric length buckets.
    #[arg(long, value_delimiter = ',')]
    run_trust_cg_bucket_rows: Vec<String>,

    /// Populate real Trust Codegen O2/O3 pipeline backend rows for comma-separated numeric length buckets.
    #[arg(long, value_delimiter = ',')]
    run_trust_cg_backend_bucket_rows: Vec<String>,

    /// Populate real Trust Codegen O2/O3 pipeline backend rows for every numeric fixture length bucket.
    #[arg(long)]
    run_trust_cg_all_numeric_backend_bucket_rows: bool,

    /// Run the bounded ay reference scanner execution row.
    #[arg(long)]
    run_ay_reference: bool,

    /// Populate bounded real ay reference rows for comma-separated numeric length buckets.
    #[arg(long, value_delimiter = ',')]
    run_ay_bucket_rows: Vec<String>,

    /// Populate bounded real ay reference rows for every numeric fixture length bucket.
    #[arg(long)]
    run_ay_all_numeric_bucket_rows: bool,
}

#[derive(Clone, Debug, Serialize)]
struct EnvironmentReport {
    schema: &'static str,
    status: &'static str,
    target: String,
    host_arch: String,
    macos_version: String,
    cpu_brand: String,
    rustc_version: String,
    cargo_version: String,
    trust_cg_commit: String,
    trust_cg_dirty: bool,
    ay_repo: Option<String>,
    ay_rev: String,
    ay_resolved_rev: Option<String>,
    ay_dirty: Option<bool>,
    generated_unix_seconds: u64,
}

#[derive(Clone, Debug, Serialize)]
struct Manifest {
    schema: &'static str,
    status: &'static str,
    artifacts: Vec<Artifact>,
    #[serde(skip_serializing_if = "Option::is_none")]
    evidence: Option<ManifestEvidence>,
}

#[derive(Clone, Debug, Serialize)]
struct Artifact {
    path: String,
    sha256: String,
    size_bytes: u64,
}

#[derive(Clone, Debug, Serialize)]
struct ManifestEvidence {
    source_cases_input: EvidenceRef,
    ay_revision: EvidenceRef,
    target_facts: EvidenceRef,
    proof_policy: EvidenceRef,
    proof_reports: Vec<EvidenceRef>,
    telemetry_summary: EvidenceRef,
    replay_inputs: EvidenceRef,
}

#[derive(Clone, Debug, Serialize)]
struct EvidenceRef {
    kind: &'static str,
    status: &'static str,
    path: Option<String>,
    sha256: Option<String>,
    value: Option<String>,
    blocker: Option<TypedBlocker>,
}

#[derive(Clone, Debug, Serialize)]
struct TypedBlocker {
    code: String,
    message: String,
}

#[derive(Clone, Debug, Serialize)]
struct CommandMetadata {
    schema: &'static str,
    status: &'static str,
    argv: Vec<String>,
    out_dir: String,
    plan_only: bool,
    target: String,
    ay_repo: Option<String>,
    ay_rev: String,
    run_ay_all_numeric_bucket_rows: bool,
    run_ay_bucket_rows: Vec<String>,
    run_trust_cg_backend_bucket_rows: Vec<String>,
    run_trust_cg_all_numeric_backend_bucket_rows: bool,
    generated_unix_seconds: u64,
}

#[derive(Clone, Debug, Serialize)]
struct ReplayDescriptor {
    schema: &'static str,
    status: &'static str,
    canonical_manifest_sha256: String,
    reproduction_command: Vec<String>,
    cases: String,
    ay_repo: Option<String>,
    ay_rev: String,
    target: String,
    artifact_manifest_sha256_path: String,
    blockers: Vec<TypedBlocker>,
}

#[derive(Clone, Debug, Serialize)]
struct GateResults {
    schema: &'static str,
    verdict: &'static str,
    can_promote_beyond_canary: bool,
    canonical_manifest_sha256: String,
    counter_scope_manifest_sha256: Option<String>,
    throughput_gate_passed: Option<bool>,
    plan_only: bool,
    missing_downstream_ay_execution: bool,
    missing_proof_evidence: bool,
    missing_useful_native_applications: bool,
    missing_no_regression_comparison: bool,
    counts: GateResultCounts,
    blockers: Vec<GateResultBlocker>,
}

#[derive(Clone, Debug, Serialize)]
struct GateResultCounts {
    baseline: usize,
    native_candidate: usize,
    fallback: usize,
    rejected: usize,
    deopted: usize,
    stale: usize,
    useful_native: usize,
}

#[derive(Clone, Debug, Serialize)]
struct GateResultBlocker {
    code: String,
    count: usize,
    message: String,
}

struct CanonicalManifestInputs<'a> {
    status: &'static str,
    environment: &'a EnvironmentReport,
    correctness: &'a CorrectnessReport,
    backend_readiness: &'a BackendReadinessReport,
    trust_cg_probe: Option<&'a TrustCgBackendProbeReport>,
    trust_cg_backend: Option<&'a TrustCgBackendExecutionReport>,
    ay_execution: Option<&'a AYReferenceExecutionReport>,
    throughput_csv: &'a str,
    throughput: &'a ThroughputSummaryReport,
    summary: &'a str,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let cases = load_ay_subsumption_cases(&args.cases)?;
    let correctness = validate_ay_subsumption_cases(&cases)?;
    validate_requested_matrix(
        &args,
        &correctness.workload.length_buckets,
        &correctness.workload.variants,
    )?;
    let ay_bucket_rows = resolve_ay_bucket_rows(&args, &correctness.workload.length_buckets)?;
    let trust_cg_backend_bucket_rows =
        resolve_trust_cg_backend_bucket_rows(&args, &correctness.workload.length_buckets)?;

    fs::create_dir_all(&args.out_dir)
        .with_context(|| format!("creating output directory {}", args.out_dir.display()))?;

    let ay_reference = ay_reference_backend_state(&args);
    let trust_cg_probe = (args.run_trust_cg_probe
        || args.run_trust_cg_mixed_rows
        || !args.run_trust_cg_bucket_rows.is_empty())
    .then(|| {
        run_trust_cg_backend_probe_with_length_buckets(&cases, &args.run_trust_cg_bucket_rows)
    });
    let trust_cg_backend = (!trust_cg_backend_bucket_rows.is_empty()).then(|| {
        run_trust_cg_backend_execution_with_length_buckets(&cases, &trust_cg_backend_bucket_rows)
    });
    let ay_execution = (args.run_ay_reference || !ay_bucket_rows.is_empty()).then(|| {
        run_ay_reference_execution_with_length_buckets(
            &cases,
            ay_reference.as_ref(),
            &args.out_dir,
            &ay_bucket_rows,
        )
    });
    let environment = collect_environment(&args)?;
    let correctness = ay_subsumption_correctness_with_full_backend_execution(
        &correctness,
        ay_reference.as_ref(),
        trust_cg_probe.as_ref(),
        ay_execution.as_ref(),
        trust_cg_backend.as_ref(),
    );
    let env_path = args.out_dir.join("environment.json");
    let correctness_path = args.out_dir.join("correctness.json");
    let backend_readiness_path = args.out_dir.join("backend_readiness.json");
    let trust_cg_probe_path = args.out_dir.join("trust_cg_backend_probe.json");
    let trust_cg_backend_path = args.out_dir.join("trust_cg_backend_execution.json");
    let ay_execution_path = args.out_dir.join("ay_reference_execution.json");
    let throughput_path = args.out_dir.join("throughput.csv");
    let throughput_summary_path = args.out_dir.join("throughput_summary.json");
    let phase8_counters_path = args.out_dir.join("phase8_native_promotion_counters.json");
    let gate_results_path = args.out_dir.join("gate-results.json");
    let command_metadata_path = args.out_dir.join("command-metadata.json");
    let replay_descriptor_path = args.out_dir.join("replay-reproduction.json");
    let manifest_sha256_path = args.out_dir.join("artifact.manifest.sha256");
    let summary_path = args.out_dir.join("summary.md");
    let canonical_manifest_path = args.out_dir.join("artifact.manifest.canonical.json");
    let backend_readiness = planned_ay_subsumption_backend_readiness_with_full_backend_execution(
        &correctness,
        ay_reference.clone(),
        trust_cg_probe.as_ref(),
        ay_execution.as_ref(),
        trust_cg_backend.as_ref(),
    );
    let throughput = planned_ay_subsumption_throughput_with_backend_buckets(
        &correctness,
        ay_execution.as_ref(),
        trust_cg_probe.as_ref(),
        args.run_trust_cg_mixed_rows,
        &args.run_trust_cg_bucket_rows,
        trust_cg_backend.as_ref(),
        &trust_cg_backend_bucket_rows,
    );
    write_json(&env_path, &environment)?;
    write_json(&correctness_path, &correctness)?;
    write_json(&backend_readiness_path, &backend_readiness)?;
    if let Some(probe) = &trust_cg_probe {
        write_json(&trust_cg_probe_path, probe)?;
    }
    if let Some(backend) = &trust_cg_backend {
        write_json(&trust_cg_backend_path, backend)?;
    }
    if let Some(execution) = &ay_execution {
        write_json(&ay_execution_path, execution)?;
    }
    let throughput_csv = ay_subsumption_throughput_csv_with_backend_buckets(
        ay_execution.as_ref(),
        trust_cg_probe.as_ref(),
        args.run_trust_cg_mixed_rows,
        &args.run_trust_cg_bucket_rows,
        trust_cg_backend.as_ref(),
        &trust_cg_backend_bucket_rows,
    );
    fs::write(&throughput_path, &throughput_csv)
        .with_context(|| format!("writing {}", throughput_path.display()))?;
    write_json(&throughput_summary_path, &throughput)?;
    let summary = summary_markdown(
        &environment,
        correctness.mismatch_count,
        throughput.row_accounting.planned_rows,
        throughput.row_accounting.measured_ay_reference_rows,
        throughput.row_accounting.measured_trust_cg_mixed_probe_rows,
        throughput
            .row_accounting
            .measured_trust_cg_bucket_probe_rows,
        throughput.row_accounting.measured_trust_cg_backend_rows,
        throughput.row_accounting.pending_backend_rows,
        trust_cg_probe.as_ref().map(|probe| probe.status),
        trust_cg_backend.as_ref().map(|backend| backend.status),
        ay_execution.as_ref().map(|execution| execution.status),
        &ay_bucket_rows,
        args.run_trust_cg_mixed_rows,
        &args.run_trust_cg_bucket_rows,
        &trust_cg_backend_bucket_rows,
    );
    fs::write(&summary_path, &summary)
        .with_context(|| format!("writing {}", summary_path.display()))?;

    let manifest_path = args.out_dir.join("artifact.manifest.json");
    let mut artifacts = vec![
        artifact_for(&env_path)?,
        artifact_for(&correctness_path)?,
        artifact_for(&backend_readiness_path)?,
    ];
    if trust_cg_probe.is_some() {
        artifacts.push(artifact_for(&trust_cg_probe_path)?);
    }
    if trust_cg_backend.is_some() {
        artifacts.push(artifact_for(&trust_cg_backend_path)?);
    }
    if ay_execution.is_some() {
        artifacts.push(artifact_for(&ay_execution_path)?);
    }
    artifacts.extend([
        artifact_for(&throughput_path)?,
        artifact_for(&throughput_summary_path)?,
        artifact_for(&summary_path)?,
    ]);
    let manifest_status = artifact_status(
        trust_cg_probe.is_some(),
        trust_cg_backend.is_some(),
        ay_execution.is_some(),
        args.run_trust_cg_mixed_rows,
        !args.run_trust_cg_bucket_rows.is_empty(),
        !trust_cg_backend_bucket_rows.is_empty(),
    );
    let canonical_manifest = canonical_manifest(CanonicalManifestInputs {
        status: manifest_status,
        environment: &environment,
        correctness: &correctness,
        backend_readiness: &backend_readiness,
        trust_cg_probe: trust_cg_probe.as_ref(),
        trust_cg_backend: trust_cg_backend.as_ref(),
        ay_execution: ay_execution.as_ref(),
        throughput_csv: &throughput_csv,
        throughput: &throughput,
        summary: &summary,
    })?;
    write_json(&canonical_manifest_path, &canonical_manifest)?;
    let canonical_manifest_sha256 = canonical_json_sha256(&canonical_manifest)?;
    fs::write(
        &manifest_sha256_path,
        format!("{canonical_manifest_sha256}\n"),
    )
    .with_context(|| format!("writing {}", manifest_sha256_path.display()))?;
    let mut counter_scope = phase8_ay_counter_scope(&args, &environment, &correctness, &throughput);
    counter_scope.manifest_sha256 = Some(canonical_manifest_sha256.clone());
    counter_scope.expected_manifest_sha256 = Some(canonical_manifest_sha256.clone());
    let phase8_counters =
        phase8_ay_subsumption_native_promotion_counters(&correctness, &throughput, counter_scope);
    write_json(&phase8_counters_path, &phase8_counters)?;
    let command_metadata = command_metadata(&args, &environment);
    write_json(&command_metadata_path, &command_metadata)?;
    let replay_descriptor = replay_descriptor(
        &args,
        &canonical_manifest_sha256,
        &manifest_sha256_path,
        &phase8_counters.promotion_verdict.blockers,
    );
    write_json(&replay_descriptor_path, &replay_descriptor)?;
    let gate_results = gate_results(
        &args,
        &canonical_manifest_sha256,
        &throughput,
        &phase8_counters,
    );
    write_json(&gate_results_path, &gate_results)?;
    artifacts.push(artifact_for(&phase8_counters_path)?);
    artifacts.push(artifact_for(&gate_results_path)?);
    artifacts.push(artifact_for(&command_metadata_path)?);
    artifacts.push(artifact_for(&replay_descriptor_path)?);
    artifacts.push(artifact_for(&manifest_sha256_path)?);
    artifacts.push(artifact_for(&canonical_manifest_path)?);

    let manifest = Manifest {
        schema: "trust-cg.ay_subsumption.artifact_manifest.v1",
        status: manifest_status,
        artifacts,
        evidence: Some(manifest_evidence(
            &args,
            &environment,
            &correctness_path,
            &backend_readiness_path,
            &throughput_summary_path,
            &replay_descriptor_path,
        )?),
    };
    write_json(&manifest_path, &manifest)?;

    if !args.plan_only {
        validate_non_plan_acceptance(&correctness, &throughput, &gate_results)
            .with_context(|| format!("artifacts were written under {}", args.out_dir.display()))?;
    }

    println!(
        "validated #571 ay subsumption workload: {} clauses, {} fixture mismatches; artifacts: {}",
        correctness.workload.clause_count,
        correctness.mismatch_count,
        args.out_dir.display()
    );
    Ok(())
}

fn validate_non_plan_acceptance(
    correctness: &CorrectnessReport,
    throughput: &ThroughputSummaryReport,
    gate_results: &GateResults,
) -> Result<()> {
    let blockers = non_plan_acceptance_blockers(correctness, throughput, gate_results);
    if blockers.is_empty() {
        return Ok(());
    }

    bail!(
        "benchmark execution artifacts did not satisfy the non-plan acceptance gate: {}",
        blockers.join("; ")
    )
}

fn non_plan_acceptance_blockers(
    correctness: &CorrectnessReport,
    throughput: &ThroughputSummaryReport,
    gate_results: &GateResults,
) -> Vec<String> {
    let mut blockers = Vec::new();
    if gate_results.plan_only {
        blockers.push("gate-results still mark the run plan_only=true".to_string());
    }
    if throughput.status != "complete_ay_reference_and_trust_cg_backend_rows" {
        blockers.push(format!(
            "throughput_summary.status={} is not complete_ay_reference_and_trust_cg_backend_rows",
            throughput.status
        ));
    }
    if throughput.row_accounting.pending_backend_rows != 0 {
        blockers.push(format!(
            "pending_backend_rows={}",
            throughput.row_accounting.pending_backend_rows
        ));
    }

    let correctness_mismatches = correctness.mismatch_count
        + correctness
            .backend_rows
            .iter()
            .map(|row| row.contains_mismatch_count + row.subsumption_mismatch_count)
            .sum::<usize>();
    if correctness_mismatches != 0 {
        blockers.push(format!("correctness_mismatches={correctness_mismatches}"));
    }
    if throughput.gate.passed != Some(true) {
        blockers.push(format!(
            "throughput_gate_passed={:?} o2_geomean={:?} o3_geomean={:?} required={}",
            throughput.gate.passed,
            throughput.gate.trust_cg_o2_vectorized_geomean,
            throughput.gate.trust_cg_o3_vectorized_geomean,
            throughput.gate.required_ay_relative_geomean
        ));
    }
    if !gate_results.blockers.is_empty() {
        blockers.push(format!(
            "gate_result_blockers={}",
            gate_results
                .blockers
                .iter()
                .map(|blocker| blocker.code.as_str())
                .collect::<Vec<_>>()
                .join(",")
        ));
    }
    if !gate_results.can_promote_beyond_canary {
        blockers.push(format!(
            "can_promote_beyond_canary=false verdict={}",
            gate_results.verdict
        ));
    }
    blockers
}

fn validate_numeric_bucket_row(
    flag: &str,
    bucket: &str,
    expected_buckets: &[String],
) -> Result<()> {
    if bucket == "mixed_2_16" {
        bail!("use mixed rows for mixed_2_16; {flag} is for numeric buckets");
    }
    if !bucket.chars().all(|ch| ch.is_ascii_digit()) {
        bail!("requested {flag} bucket {bucket:?} is not numeric");
    }
    if !expected_buckets.iter().any(|expected| expected == bucket) {
        bail!(
            "requested {flag} bucket {bucket:?} is not in fixture buckets {:?}",
            expected_buckets
        );
    }
    Ok(())
}

fn validate_unique_bucket_rows(flag: &str, buckets: &[String]) -> Result<()> {
    let mut seen = std::collections::BTreeSet::new();
    for bucket in buckets {
        if !seen.insert(bucket) {
            bail!("duplicate {flag} bucket row {bucket:?}");
        }
    }
    Ok(())
}

fn validate_requested_bucket_uniqueness(args: &Args) -> Result<()> {
    validate_unique_bucket_rows("--run-trust-cg-bucket-rows", &args.run_trust_cg_bucket_rows)?;
    validate_unique_bucket_rows(
        "--run-trust-cg-backend-bucket-rows",
        &args.run_trust_cg_backend_bucket_rows,
    )?;
    validate_unique_bucket_rows("--run-ay-bucket-rows", &args.run_ay_bucket_rows)?;
    Ok(())
}

fn resolve_ay_bucket_rows(args: &Args, expected_buckets: &[String]) -> Result<Vec<String>> {
    if !args.run_ay_all_numeric_bucket_rows {
        return Ok(args.run_ay_bucket_rows.clone());
    }
    if !args.run_ay_bucket_rows.is_empty() {
        bail!(
            "--run-ay-all-numeric-bucket-rows cannot be combined with --run-ay-bucket-rows; pass the exact numeric bucket list with --run-ay-bucket-rows when you need a bounded subset"
        );
    }
    let buckets = ay_numeric_length_buckets(expected_buckets);
    if buckets.is_empty() {
        bail!("--run-ay-all-numeric-bucket-rows requested, but the fixture has no numeric buckets");
    }
    Ok(buckets)
}

fn resolve_trust_cg_backend_bucket_rows(
    args: &Args,
    expected_buckets: &[String],
) -> Result<Vec<String>> {
    if !args.run_trust_cg_all_numeric_backend_bucket_rows {
        return Ok(args.run_trust_cg_backend_bucket_rows.clone());
    }
    if !args.run_trust_cg_backend_bucket_rows.is_empty() {
        bail!(
            "--run-trust-cg-all-numeric-backend-bucket-rows cannot be combined with --run-trust-cg-backend-bucket-rows; pass the exact numeric bucket list with --run-trust-cg-backend-bucket-rows when you need a bounded subset"
        );
    }
    let buckets = ay_numeric_length_buckets(expected_buckets);
    if buckets.is_empty() {
        bail!(
            "--run-trust-cg-all-numeric-backend-bucket-rows requested, but the fixture has no numeric buckets"
        );
    }
    Ok(buckets)
}

fn validate_requested_matrix(
    args: &Args,
    expected_buckets: &[String],
    expected_variants: &[String],
) -> Result<()> {
    if !args.variants.is_empty() && args.variants != expected_variants {
        bail!(
            "requested variants {:?} do not match fixture variants {:?}",
            args.variants,
            expected_variants
        );
    }
    if !args.length_buckets.is_empty() && args.length_buckets != expected_buckets {
        bail!(
            "requested length buckets {:?} do not match fixture buckets {:?}",
            args.length_buckets,
            expected_buckets
        );
    }
    validate_requested_bucket_uniqueness(args)?;
    for bucket in &args.run_trust_cg_bucket_rows {
        validate_numeric_bucket_row("--run-trust-cg-bucket-rows", bucket, expected_buckets)?;
    }
    for bucket in &args.run_trust_cg_backend_bucket_rows {
        validate_numeric_bucket_row(
            "--run-trust-cg-backend-bucket-rows",
            bucket,
            expected_buckets,
        )?;
    }
    for bucket in &args.run_ay_bucket_rows {
        validate_numeric_bucket_row("--run-ay-bucket-rows", bucket, expected_buckets)?;
    }
    if args.run_trust_cg_all_numeric_backend_bucket_rows
        && args.run_trust_cg_backend_bucket_rows.is_empty()
    {
        let numeric_buckets = ay_numeric_length_buckets(expected_buckets);
        if numeric_buckets.is_empty() {
            bail!(
                "--run-trust-cg-all-numeric-backend-bucket-rows requested, but the fixture has no numeric buckets"
            );
        }
    }
    Ok(())
}

fn collect_environment(args: &Args) -> Result<EnvironmentReport> {
    let ay_repo = args.ay_repo.as_deref();
    Ok(EnvironmentReport {
        schema: "trust-cg.ay_subsumption.environment.v1",
        status: "plan_only",
        target: args.target.clone(),
        host_arch: command_output("uname", &["-m"]).unwrap_or_else(|| "unknown".to_string()),
        macos_version: command_output("sw_vers", &["-productVersion"])
            .unwrap_or_else(|| "unknown".to_string()),
        cpu_brand: command_output("sysctl", &["-n", "machdep.cpu.brand_string"])
            .unwrap_or_else(|| "unknown".to_string()),
        rustc_version: command_output("rustc", &["-Vv"]).unwrap_or_else(|| "unknown".to_string()),
        cargo_version: command_output("cargo", &["-V"]).unwrap_or_else(|| "unknown".to_string()),
        trust_cg_commit: git_output(Path::new("."), &["rev-parse", "HEAD"])
            .unwrap_or_else(|| "unknown".to_string()),
        trust_cg_dirty: git_dirty(Path::new(".")).unwrap_or(true),
        ay_repo: ay_repo.map(|path| path.display().to_string()),
        ay_rev: args.ay_rev.clone(),
        ay_resolved_rev: ay_repo.and_then(|path| git_output(path, &["rev-parse", &args.ay_rev])),
        ay_dirty: ay_repo.and_then(git_dirty),
        generated_unix_seconds: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .context("system clock is before UNIX epoch")?
            .as_secs(),
    })
}

fn command_metadata(args: &Args, environment: &EnvironmentReport) -> CommandMetadata {
    CommandMetadata {
        schema: "trust-cg.ay_subsumption.command_metadata.v1",
        status: "recorded",
        argv: std::env::args().collect(),
        out_dir: args.out_dir.display().to_string(),
        plan_only: args.plan_only,
        target: args.target.clone(),
        ay_repo: args.ay_repo.as_ref().map(|path| path.display().to_string()),
        ay_rev: args.ay_rev.clone(),
        run_ay_all_numeric_bucket_rows: args.run_ay_all_numeric_bucket_rows,
        run_ay_bucket_rows: args.run_ay_bucket_rows.clone(),
        run_trust_cg_backend_bucket_rows: args.run_trust_cg_backend_bucket_rows.clone(),
        run_trust_cg_all_numeric_backend_bucket_rows: args
            .run_trust_cg_all_numeric_backend_bucket_rows,
        generated_unix_seconds: environment.generated_unix_seconds,
    }
}

fn replay_descriptor(
    args: &Args,
    canonical_manifest_sha256: &str,
    manifest_sha256_path: &Path,
    promotion_blockers: &[trust_cg_jit_matrix::Phase8PromotionBlocker],
) -> ReplayDescriptor {
    ReplayDescriptor {
        schema: "trust-cg.ay_subsumption.replay_reproduction.v1",
        status: "non_promoting_replay_descriptor",
        canonical_manifest_sha256: canonical_manifest_sha256.to_string(),
        reproduction_command: std::env::args().collect(),
        cases: args.cases.display().to_string(),
        ay_repo: args.ay_repo.as_ref().map(|path| path.display().to_string()),
        ay_rev: args.ay_rev.clone(),
        target: args.target.clone(),
        artifact_manifest_sha256_path: manifest_sha256_path.display().to_string(),
        blockers: promotion_blockers
            .iter()
            .map(|blocker| TypedBlocker {
                code: blocker.code.clone(),
                message: blocker.message.clone(),
            })
            .collect(),
    }
}

fn gate_results(
    args: &Args,
    canonical_manifest_sha256: &str,
    throughput: &ThroughputSummaryReport,
    counters: &trust_cg_jit_matrix::Phase8NativePromotionCounters,
) -> GateResults {
    let packet_blockers = phase8_ay_promotion_packet_missing_artifact_blockers(
        &args.out_dir,
        PHASE8_AY_PROMOTION_PACKET_REQUIRED_ARTIFACTS
            .iter()
            .copied()
            .filter(|artifact| {
                *artifact != "artifact.manifest.json" && *artifact != "gate-results.json"
            })
            .collect::<Vec<_>>()
            .as_slice(),
    );
    let mut blockers = counters
        .promotion_verdict
        .blockers
        .iter()
        .chain(packet_blockers.iter())
        .map(|blocker| GateResultBlocker {
            code: blocker.code.clone(),
            count: blocker.count,
            message: blocker.message.clone(),
        })
        .collect::<Vec<_>>();
    if args.plan_only {
        blockers.push(GateResultBlocker {
            code: "plan_only".to_string(),
            count: 1,
            message: "plan-only ay subsumption evidence cannot promote beyond canary".to_string(),
        });
    }
    blockers.sort_by(|a, b| a.code.cmp(&b.code).then(a.message.cmp(&b.message)));
    let can_promote_beyond_canary = !args.plan_only
        && counters.promotion_verdict.can_promote_beyond_canary
        && blockers.is_empty();

    GateResults {
        schema: "trust-cg.ay_subsumption.gate_results.v1",
        verdict: if can_promote_beyond_canary {
            "promoting"
        } else {
            "non_promoting"
        },
        can_promote_beyond_canary,
        canonical_manifest_sha256: canonical_manifest_sha256.to_string(),
        counter_scope_manifest_sha256: counters.counter_scope.manifest_sha256.clone(),
        throughput_gate_passed: throughput.gate.passed,
        plan_only: args.plan_only,
        missing_downstream_ay_execution: throughput.row_accounting.measured_ay_reference_rows == 0,
        missing_proof_evidence: counters.proof_gate.proof_verified_count == 0,
        missing_useful_native_applications: counters.dispatch.useful_native_count == 0,
        missing_no_regression_comparison: throughput.gate.passed.is_none(),
        counts: GateResultCounts {
            baseline: counters.dispatch.baseline_call_count,
            native_candidate: counters.dispatch.native_call_count,
            fallback: counters.dispatch.fallback_count,
            rejected: counters.lifecycle.install_rejected_count,
            deopted: counters.dispatch.deopt_count,
            stale: counters.invalidation_gate.stale_install_reject_count
                + counters.invalidation_gate.stale_call_reject_count
                + counters.proof_gate.proof_stale_count,
            useful_native: counters.dispatch.useful_native_count,
        },
        blockers,
    }
}

fn manifest_evidence(
    args: &Args,
    environment: &EnvironmentReport,
    correctness_path: &Path,
    backend_readiness_path: &Path,
    throughput_summary_path: &Path,
    replay_descriptor_path: &Path,
) -> Result<ManifestEvidence> {
    Ok(ManifestEvidence {
        source_cases_input: file_evidence(
            "source_cases_input",
            &args.cases,
            "cases_input_missing",
        )?,
        ay_revision: ay_revision_evidence(environment),
        target_facts: value_evidence(
            "target_facts",
            format!(
                "target={};host_arch={};cpu={};trust_cg_commit={};trust_cg_dirty={}",
                environment.target,
                environment.host_arch,
                environment.cpu_brand,
                environment.trust_cg_commit,
                environment.trust_cg_dirty
            ),
        ),
        proof_policy: value_evidence(
            "proof_policy",
            PHASE8_AY_SUBSUMPTION_PROOF_POLICY.to_string(),
        ),
        proof_reports: vec![
            file_evidence(
                "correctness_report",
                correctness_path,
                "correctness_report_missing",
            )?,
            file_evidence(
                "backend_readiness_report",
                backend_readiness_path,
                "backend_readiness_report_missing",
            )?,
        ],
        telemetry_summary: file_evidence(
            "telemetry_summary",
            throughput_summary_path,
            "telemetry_summary_missing",
        )?,
        replay_inputs: file_evidence(
            "replay_inputs",
            replay_descriptor_path,
            "replay_descriptor_missing",
        )?,
    })
}

fn file_evidence(
    kind: &'static str,
    path: &Path,
    missing_code: &'static str,
) -> Result<EvidenceRef> {
    if !path.is_file() {
        return Ok(EvidenceRef {
            kind,
            status: "blocked",
            path: Some(path.display().to_string()),
            sha256: None,
            value: None,
            blocker: Some(TypedBlocker {
                code: missing_code.to_string(),
                message: format!("required evidence file is missing: {}", path.display()),
            }),
        });
    }
    Ok(EvidenceRef {
        kind,
        status: "present",
        path: Some(path.display().to_string()),
        sha256: Some(file_sha256(path)?),
        value: None,
        blocker: None,
    })
}

fn value_evidence(kind: &'static str, value: String) -> EvidenceRef {
    EvidenceRef {
        kind,
        status: "present",
        path: None,
        sha256: Some(sha256_hex(&value)),
        value: Some(value),
        blocker: None,
    }
}

fn ay_revision_evidence(environment: &EnvironmentReport) -> EvidenceRef {
    match (
        environment.ay_repo.as_ref(),
        environment.ay_resolved_rev.as_ref(),
    ) {
        (Some(repo), Some(rev)) => value_evidence("ay_revision", format!("repo={repo};rev={rev}")),
        (Some(repo), None) => EvidenceRef {
            kind: "ay_revision",
            status: "blocked",
            path: Some(repo.clone()),
            sha256: None,
            value: Some(environment.ay_rev.clone()),
            blocker: Some(TypedBlocker {
                code: "ay_revision_unresolved".to_string(),
                message: format!(
                    "could not resolve requested ay revision {}",
                    environment.ay_rev
                ),
            }),
        },
        (None, _) => EvidenceRef {
            kind: "ay_revision",
            status: "blocked",
            path: None,
            sha256: None,
            value: Some(environment.ay_rev.clone()),
            blocker: Some(TypedBlocker {
                code: "ay_repo_not_provided".to_string(),
                message: "no ay repository was provided for revision evidence".to_string(),
            }),
        },
    }
}

fn file_sha256(path: &Path) -> Result<String> {
    let (sha256, _) = stream_file_sha256(path, MAX_JIT_MATRIX_ARTIFACT_BYTES)?;
    Ok(sha256)
}

fn ay_reference_backend_state(args: &Args) -> Option<AYReferenceBackendState> {
    let repo = args.ay_repo.as_deref()?;
    let revision_source_path = "crates/ay-jit/src/simd_inprocess.rs";
    let source_path = repo.join("crates/ay-jit/src/simd_inprocess.rs");
    let resolved_rev = git_output(repo, &["rev-parse", &args.ay_rev]);
    let revision_source = git_output(
        repo,
        &["show", &format!("{}:{revision_source_path}", args.ay_rev)],
    );
    let source_checks = revision_source
        .as_deref()
        .map(ay_reference_source_checks)
        .unwrap_or_default();
    let all_expected_symbols_present =
        !source_checks.is_empty() && source_checks.iter().all(|check| check.present);
    let revision_source_sha256 = revision_source.as_deref().map(sha256_hex);
    let revision_source_size_bytes = revision_source.as_ref().map(|source| source.len() as u64);
    Some(AYReferenceBackendState {
        repo: repo.display().to_string(),
        requested_rev: args.ay_rev.clone(),
        resolved_rev,
        dirty: git_dirty(repo),
        source_path: source_path.display().to_string(),
        source_exists: source_path.exists(),
        revision_source_path: revision_source_path.to_string(),
        revision_source_exists: revision_source.is_some(),
        revision_source_sha256,
        revision_source_size_bytes,
        source_checks,
        adapter_ready: all_expected_symbols_present,
    })
}

fn phase8_ay_counter_scope(
    args: &Args,
    environment: &EnvironmentReport,
    correctness: &CorrectnessReport,
    throughput: &ThroughputSummaryReport,
) -> Phase8NativePromotionCounterScope {
    let target_features = format!(
        "target={};host_arch={};cpu={}",
        args.target, environment.host_arch, environment.cpu_brand
    );
    let layout = format!(
        "correctness_schema={};throughput_schema={};workload={};issue={};buckets={};variants={};planned_rows={}",
        correctness.schema,
        throughput.schema,
        correctness.workload.name,
        correctness.workload.issue,
        correctness.workload.length_buckets.join(","),
        correctness.workload.variants.join(","),
        throughput.row_accounting.planned_rows
    );
    let invalidation_key = format!(
        "{}:{}:{}:{}:{}",
        correctness.workload.name,
        correctness.workload.issue,
        args.target,
        environment
            .ay_resolved_rev
            .as_deref()
            .unwrap_or(&environment.ay_rev),
        environment.trust_cg_commit
    );

    Phase8NativePromotionCounterScope {
        consumer: "ay".to_string(),
        family: PHASE8_AY_SUBSUMPTION_COUNTER_FAMILY.to_string(),
        mode: PHASE8_NATIVE_PROMOTION_CANARY_MODE.to_string(),
        target_triple: args.target.clone(),
        target_cpu: environment.cpu_brand.clone(),
        target_features_sha256: sha256_hex(target_features),
        proof_policy_sha256: sha256_hex(PHASE8_AY_SUBSUMPTION_PROOF_POLICY),
        layout_checksum: sha256_hex(layout),
        invalidation_key,
        manifest_sha256: None,
        expected_manifest_sha256: None,
    }
}

fn command_output(program: &str, args: &[&str]) -> Option<String> {
    let output = Command::new(program).args(args).output().ok()?;
    if !output.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn git_output(repo: &Path, args: &[&str]) -> Option<String> {
    let mut child = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .stdout(Stdio::piped())
        .spawn()
        .ok()?;
    let stdout = child.stdout.take()?;
    let mut bytes = Vec::new();
    let mut bounded = stdout.take(MAX_JIT_MATRIX_GIT_OUTPUT_BYTES + 1);
    bounded.read_to_end(&mut bytes).ok()?;
    if bytes.len() as u64 > MAX_JIT_MATRIX_GIT_OUTPUT_BYTES {
        let _ = child.kill();
        let _ = child.wait();
        return None;
    }
    let status = child.wait().ok()?;
    if !status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&bytes).trim().to_string())
}

fn git_dirty(repo: &Path) -> Option<bool> {
    git_output(repo, &["status", "--short"]).map(|status| !status.is_empty())
}

fn write_json<T: Serialize>(path: &Path, value: &T) -> Result<()> {
    let text = serde_json::to_string_pretty(value).context("serializing JSON artifact")?;
    fs::write(path, format!("{text}\n")).with_context(|| format!("writing {}", path.display()))
}

fn artifact_for(path: &Path) -> Result<Artifact> {
    let (sha256, size_bytes) = stream_file_sha256(path, MAX_JIT_MATRIX_ARTIFACT_BYTES)?;
    Ok(Artifact {
        path: path.display().to_string(),
        sha256,
        size_bytes,
    })
}

fn stream_file_sha256(path: &Path, limit: u64) -> Result<(String, u64)> {
    let size = fs::metadata(path)
        .with_context(|| format!("statting {}", path.display()))?
        .len();
    if size > limit {
        bail!(
            "artifact {} is {} byte(s), over limit {}",
            path.display(),
            size,
            limit
        );
    }

    let file = fs::File::open(path).with_context(|| format!("reading {}", path.display()))?;
    let mut reader = file.take(limit + 1);
    let mut hasher = Sha256::new();
    let mut total = 0u64;
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let read = reader
            .read(&mut buffer)
            .with_context(|| format!("reading {}", path.display()))?;
        if read == 0 {
            break;
        }
        total += read as u64;
        if total > limit {
            bail!(
                "artifact {} grew over limit {} while reading",
                path.display(),
                limit
            );
        }
        hasher.update(&buffer[..read]);
    }

    Ok((format!("{:x}", hasher.finalize()), total))
}

fn canonical_manifest(inputs: CanonicalManifestInputs<'_>) -> Result<Manifest> {
    let mut environment = inputs.environment.clone();
    environment.generated_unix_seconds = 0;
    let mut artifacts = vec![
        canonical_json_artifact("environment.json", &environment)?,
        canonical_json_artifact("correctness.json", inputs.correctness)?,
        canonical_json_artifact("backend_readiness.json", inputs.backend_readiness)?,
    ];
    if let Some(probe) = inputs.trust_cg_probe {
        artifacts.push(canonical_json_artifact(
            "trust_cg_backend_probe.json",
            probe,
        )?);
    }
    if let Some(backend) = inputs.trust_cg_backend {
        artifacts.push(canonical_json_artifact(
            "trust_cg_backend_execution.json",
            backend,
        )?);
    }
    if let Some(execution) = inputs.ay_execution {
        artifacts.push(canonical_json_artifact(
            "ay_reference_execution.json",
            execution,
        )?);
    }
    artifacts.extend([
        canonical_bytes_artifact("throughput.csv", inputs.throughput_csv.as_bytes()),
        canonical_json_artifact("throughput_summary.json", inputs.throughput)?,
        canonical_bytes_artifact("summary.md", inputs.summary.as_bytes()),
    ]);
    Ok(Manifest {
        schema: "trust-cg.ay_subsumption.canonical_artifact_manifest.v1",
        status: inputs.status,
        artifacts,
        evidence: None,
    })
}

fn canonical_json_artifact<T: Serialize>(path: &str, value: &T) -> Result<Artifact> {
    let bytes = canonical_json_bytes(value)?;
    Ok(canonical_bytes_artifact(path, &bytes))
}

fn canonical_bytes_artifact(path: &str, bytes: &[u8]) -> Artifact {
    Artifact {
        path: path.to_string(),
        sha256: sha256_hex(bytes),
        size_bytes: bytes.len() as u64,
    }
}

fn canonical_json_sha256<T: Serialize>(value: &T) -> Result<String> {
    canonical_json_bytes(value).map(sha256_hex)
}

fn canonical_json_bytes<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    let text =
        serde_json::to_string_pretty(value).context("serializing canonical JSON artifact")?;
    Ok(format!("{text}\n").into_bytes())
}

fn sha256_hex(bytes: impl AsRef<[u8]>) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes.as_ref());
    format!("{:x}", hasher.finalize())
}

#[allow(clippy::too_many_arguments)] // Inputs enumerate independent report sections and counters.
fn summary_markdown(
    environment: &EnvironmentReport,
    mismatch_count: usize,
    planned_throughput_rows: usize,
    measured_ay_reference_rows: usize,
    measured_trust_cg_mixed_probe_rows: usize,
    measured_trust_cg_bucket_probe_rows: usize,
    measured_trust_cg_backend_rows: usize,
    pending_backend_rows: usize,
    trust_cg_probe_status: Option<&str>,
    trust_cg_backend_status: Option<&str>,
    ay_reference_status: Option<&str>,
    ay_bucket_rows: &[String],
    trust_cg_mixed_rows: bool,
    trust_cg_bucket_rows: &[String],
    trust_cg_backend_bucket_rows: &[String],
) -> String {
    let ay_bucket_rows = if ay_bucket_rows.is_empty() {
        "not_enabled".to_string()
    } else {
        ay_bucket_rows.join(",")
    };
    let bucket_rows = if trust_cg_bucket_rows.is_empty() {
        "not_enabled".to_string()
    } else {
        trust_cg_bucket_rows.join(",")
    };
    let backend_bucket_rows = if trust_cg_backend_bucket_rows.is_empty() {
        "not_enabled".to_string()
    } else {
        trust_cg_backend_bucket_rows.join(",")
    };
    format!(
        "# ay Subsumption Matrix Plan\n\n\
Status: {}; no #571 throughput acceptance claimed.\n\n\
- Target: `{}`\n\
- Host arch: `{}`\n\
- Trust Codegen commit: `{}`\n\
- Trust Codegen dirty: `{}`\n\
- ay revision: `{}`\n\
- Fixture mismatch count: `{}`\n\n\
- ay reference execution: `{}`\n\
- ay numeric bucket rows: `{}`\n\
- Trust Codegen backend probe: `{}`\n\
- Trust Codegen mixed probe rows: `{}`\n\
- Trust Codegen numeric bucket probe rows: `{}`\n\
- Trust Codegen O2/O3 pipeline backend: `{}`\n\
- Trust Codegen O2/O3 backend numeric bucket rows: `{}`\n\
- Planned throughput rows: `{}`\n\
- Measured bounded rows: ay `{}`, Trust Codegen mixed probe `{}`, Trust Codegen numeric probe `{}`, Trust Codegen O2/O3 backend `{}`\n\
- Pending backend rows: `{}`\n\n\
Full acceptance still requires Apple Silicon execution of ay NEON and Trust Codegen \
O2/O3 vectorized/scalar-control variants, with zero correctness mismatches and \
Trust Codegen vectorized geometric-mean throughput at least 0.90x ay NEON.\n",
        summary_status(
            trust_cg_probe_status.is_some(),
            ay_reference_status.is_some(),
            trust_cg_mixed_rows,
            !trust_cg_bucket_rows.is_empty(),
            !trust_cg_backend_bucket_rows.is_empty(),
        ),
        environment.target,
        environment.host_arch,
        environment.trust_cg_commit,
        environment.trust_cg_dirty,
        environment
            .ay_resolved_rev
            .as_deref()
            .unwrap_or(&environment.ay_rev),
        mismatch_count,
        ay_reference_status.unwrap_or("not_run"),
        ay_bucket_rows,
        trust_cg_probe_status.unwrap_or("not_run"),
        if trust_cg_mixed_rows {
            "enabled"
        } else {
            "not_enabled"
        },
        bucket_rows,
        trust_cg_backend_status.unwrap_or("not_run"),
        backend_bucket_rows,
        planned_throughput_rows,
        measured_ay_reference_rows,
        measured_trust_cg_mixed_probe_rows,
        measured_trust_cg_bucket_probe_rows,
        measured_trust_cg_backend_rows,
        pending_backend_rows
    )
}

fn artifact_status(
    trust_cg_probe: bool,
    trust_cg_backend: bool,
    ay_reference: bool,
    trust_cg_mixed_rows: bool,
    trust_cg_bucket_rows: bool,
    trust_cg_backend_rows: bool,
) -> &'static str {
    match (
        ay_reference,
        trust_cg_probe,
        trust_cg_backend,
        trust_cg_mixed_rows,
        trust_cg_bucket_rows,
        trust_cg_backend_rows,
    ) {
        (true, _, true, _, _, true) => "plan_with_ay_reference_and_trust_cg_backend_rows",
        (false, _, true, _, _, true) => "plan_with_trust_cg_backend_rows",
        (true, true, false, true, true, _) => {
            "plan_with_ay_reference_trust_cg_probe_mixed_and_bucket_rows"
        }
        (true, true, false, false, true, _) => {
            "plan_with_ay_reference_trust_cg_probe_and_bucket_rows"
        }
        (true, true, false, true, false, _) => {
            "plan_with_ay_reference_trust_cg_probe_and_mixed_rows"
        }
        (true, true, false, false, false, _) => "plan_with_ay_reference_and_trust_cg_probe",
        (true, false, false, _, _, _) => "plan_with_ay_reference",
        (false, true, false, true, true, _) => "plan_with_trust_cg_probe_mixed_and_bucket_rows",
        (false, true, false, false, true, _) => "plan_with_trust_cg_probe_and_bucket_rows",
        (false, true, false, true, false, _) => "plan_with_trust_cg_probe_and_mixed_rows",
        (false, true, false, false, false, _) => "plan_with_trust_cg_probe",
        (false, false, false, _, _, _) => "plan_only",
        (_, _, true, _, _, false) => "plan_with_empty_trust_cg_backend_rows",
    }
}

fn summary_status(
    trust_cg_probe: bool,
    ay_reference: bool,
    trust_cg_mixed_rows: bool,
    trust_cg_bucket_rows: bool,
    trust_cg_backend_rows: bool,
) -> &'static str {
    match (
        ay_reference,
        trust_cg_probe,
        trust_cg_mixed_rows,
        trust_cg_bucket_rows,
        trust_cg_backend_rows,
    ) {
        (true, _, _, _, true) => "plan-with-ay-reference-and-trust-cg-backend-rows",
        (false, _, _, _, true) => "plan-with-trust-cg-backend-rows",
        (true, true, true, true, false) => {
            "plan-with-ay-reference-trust-cg-probe-mixed-and-bucket-rows"
        }
        (true, true, false, true, false) => "plan-with-ay-reference-trust-cg-probe-and-bucket-rows",
        (true, true, true, false, false) => "plan-with-ay-reference-trust-cg-probe-and-mixed-rows",
        (true, true, false, false, false) => "plan-with-ay-reference-and-trust-cg-probe",
        (true, false, _, _, false) => "plan-with-ay-reference",
        (false, true, true, true, false) => "plan-with-trust-cg-probe-mixed-and-bucket-rows",
        (false, true, false, true, false) => "plan-with-trust-cg-probe-and-bucket-rows",
        (false, true, true, false, false) => "plan-with-trust-cg-probe-and-mixed-rows",
        (false, true, false, false, false) => "plan-with-trust-cg-probe",
        (false, false, _, _, false) => "plan-only",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use trust_cg_jit_matrix::{
        PHASE8_NATIVE_PROMOTION_COUNTERS_SCHEMA, Phase8AYConsumerCounters,
        Phase8AYMutationCounters, Phase8AYResultParityCounters, Phase8AYUsefulnessCounters,
        Phase8ArtifactGateCounters, Phase8ConsumerCounters, Phase8DispatchCounters,
        Phase8InvalidationGateCounters, Phase8LifecycleCounters, Phase8NativePromotionCounters,
        Phase8PerformanceCounters, Phase8PromotionBlocker, Phase8PromotionVerdict,
        Phase8ProofGateCounters, ThroughputGate, ThroughputRowAccounting, WorkloadSummary,
    };

    #[test]
    fn stream_file_sha256_rejects_oversized_artifact_before_hashing() {
        let temp_dir = tempfile::tempdir().expect("tempdir");
        let path = temp_dir.path().join("oversized-artifact.json");
        let file = fs::File::create(&path).expect("create sparse artifact");
        file.set_len(MAX_JIT_MATRIX_ARTIFACT_BYTES + 1)
            .expect("set sparse len");
        drop(file);

        let error = stream_file_sha256(&path, MAX_JIT_MATRIX_ARTIFACT_BYTES).unwrap_err();

        assert!(
            error.to_string().contains("over limit"),
            "unexpected error: {error:?}"
        );
    }

    #[test]
    fn gate_results_plan_only_blocks_otherwise_promotable_counters() {
        let temp_dir = tempfile::tempdir().expect("tempdir");
        write_present_gate_packet_artifacts(temp_dir.path());
        let args = gate_test_args(temp_dir.path().to_path_buf(), true);
        let throughput = promotable_throughput_summary();
        let counters = promotable_phase8_counters();

        assert!(counters.promotion_verdict.can_promote_beyond_canary);
        assert!(counters.promotion_verdict.blockers.is_empty());

        let gate = gate_results(&args, "manifest-hash", &throughput, &counters);

        assert_eq!(gate.verdict, "non_promoting");
        assert!(!gate.can_promote_beyond_canary);
        assert!(gate.plan_only);
        assert_eq!(gate.throughput_gate_passed, Some(true));
        assert_eq!(gate.counts.useful_native, 2);
        assert!(
            gate.blockers
                .iter()
                .any(|blocker| blocker.code == "plan_only")
        );
        assert!(
            !gate
                .blockers
                .iter()
                .any(|blocker| blocker.code == "required_packet_artifact_missing")
        );
    }

    #[test]
    fn non_plan_acceptance_allows_complete_unblocked_gate_artifacts() {
        let temp_dir = tempfile::tempdir().expect("tempdir");
        write_present_gate_packet_artifacts(temp_dir.path());
        let args = gate_test_args(temp_dir.path().to_path_buf(), false);
        let correctness = promotable_correctness_report();
        let throughput = promotable_throughput_summary();
        let counters = promotable_phase8_counters();

        let gate = gate_results(&args, "manifest-hash", &throughput, &counters);

        assert_eq!(gate.verdict, "promoting");
        assert!(gate.can_promote_beyond_canary);
        assert!(!gate.plan_only);
        assert!(gate.blockers.is_empty());
        assert!(non_plan_acceptance_blockers(&correctness, &throughput, &gate).is_empty());
        validate_non_plan_acceptance(&correctness, &throughput, &gate)
            .expect("complete unblocked gate artifacts should be accepted");
    }

    #[test]
    fn non_plan_acceptance_reports_exact_artifact_blockers() {
        let temp_dir = tempfile::tempdir().expect("tempdir");
        write_present_gate_packet_artifacts(temp_dir.path());
        let args = gate_test_args(temp_dir.path().to_path_buf(), false);
        let mut correctness = promotable_correctness_report();
        correctness.mismatch_count = 1;
        let mut throughput = promotable_throughput_summary();
        throughput.status = "partial_trust_cg_backend_rows";
        throughput.row_accounting.pending_backend_rows = 3;
        throughput.gate.passed = Some(false);
        let mut counters = promotable_phase8_counters();
        counters.promotion_verdict.can_promote_beyond_canary = false;
        counters
            .promotion_verdict
            .blockers
            .push(Phase8PromotionBlocker {
                code: "native_status_error".to_string(),
                count: 1,
                message: "test blocker".to_string(),
            });

        let gate = gate_results(&args, "manifest-hash", &throughput, &counters);
        let blockers = non_plan_acceptance_blockers(&correctness, &throughput, &gate);
        let joined = blockers.join("\n");

        assert!(joined.contains("throughput_summary.status=partial_trust_cg_backend_rows"));
        assert!(joined.contains("pending_backend_rows=3"));
        assert!(joined.contains("correctness_mismatches=1"));
        assert!(joined.contains("throughput_gate_passed=Some(false)"));
        assert!(joined.contains("gate_result_blockers=native_status_error"));
        assert!(joined.contains("can_promote_beyond_canary=false verdict=non_promoting"));
    }

    fn write_present_gate_packet_artifacts(out_dir: &Path) {
        for artifact in [
            "artifact.manifest.sha256",
            "phase8_native_promotion_counters.json",
            "command-metadata.json",
            "replay-reproduction.json",
        ] {
            std::fs::write(out_dir.join(artifact), "present\n").expect("write packet artifact");
        }
    }

    fn gate_test_args(out_dir: PathBuf, plan_only: bool) -> Args {
        Args {
            cases: PathBuf::from("cases.json"),
            ay_repo: None,
            ay_rev: "test-ay-rev".to_string(),
            target: "aarch64-apple-darwin".to_string(),
            variants: Vec::new(),
            length_buckets: Vec::new(),
            warmup_iterations: None,
            measurement_repetitions: None,
            out_dir,
            plan_only,
            run_trust_cg_probe: false,
            run_trust_cg_mixed_rows: false,
            run_trust_cg_bucket_rows: Vec::new(),
            run_trust_cg_backend_bucket_rows: Vec::new(),
            run_trust_cg_all_numeric_backend_bucket_rows: false,
            run_ay_reference: false,
            run_ay_bucket_rows: Vec::new(),
            run_ay_all_numeric_bucket_rows: false,
        }
    }

    fn promotable_throughput_summary() -> ThroughputSummaryReport {
        ThroughputSummaryReport {
            schema: "trust-cg.ay_subsumption.throughput_summary.v1",
            status: "complete_ay_reference_and_trust_cg_backend_rows",
            workload: workload_summary(),
            rows: Vec::new(),
            row_accounting: ThroughputRowAccounting {
                planned_rows: 2,
                measured_ay_reference_rows: 2,
                measured_trust_cg_mixed_probe_rows: 0,
                measured_trust_cg_bucket_probe_rows: 0,
                measured_trust_cg_backend_rows: 2,
                pending_backend_rows: 0,
            },
            gate: ThroughputGate {
                required_ay_relative_geomean: 0.9,
                trust_cg_o2_vectorized_geomean: Some(1.2),
                trust_cg_o3_vectorized_geomean: Some(1.3),
                passed: Some(true),
            },
            note: "test throughput evidence",
        }
    }

    fn promotable_correctness_report() -> CorrectnessReport {
        CorrectnessReport {
            schema: "trust-cg.ay_subsumption.correctness.v1",
            workload: workload_summary(),
            contains: Vec::new(),
            subsumption: Vec::new(),
            backend_rows: Vec::new(),
            mismatch_count: 0,
            status: "validated",
            note: "test correctness evidence",
        }
    }

    fn promotable_phase8_counters() -> Phase8NativePromotionCounters {
        Phase8NativePromotionCounters {
            schema: PHASE8_NATIVE_PROMOTION_COUNTERS_SCHEMA,
            counter_scope: Phase8NativePromotionCounterScope {
                consumer: "ay".to_string(),
                family: PHASE8_AY_SUBSUMPTION_COUNTER_FAMILY.to_string(),
                mode: PHASE8_NATIVE_PROMOTION_CANARY_MODE.to_string(),
                target_triple: "aarch64-apple-darwin".to_string(),
                target_cpu: "test-cpu".to_string(),
                target_features_sha256: "features".to_string(),
                proof_policy_sha256: "proof-policy".to_string(),
                layout_checksum: "layout".to_string(),
                invalidation_key: "invalidation".to_string(),
                manifest_sha256: Some("manifest-hash".to_string()),
                expected_manifest_sha256: Some("manifest-hash".to_string()),
            },
            lifecycle: Phase8LifecycleCounters {
                observed_count: 2,
                nominated_count: 2,
                profile_only_compiled_count: 0,
                shadow_dispatch_count: 0,
                canary_install_count: 2,
                active_promotion_count: 1,
                install_rejected_count: 0,
                invalidated_count: 0,
                rolled_back_count: 0,
                revoked_count: 0,
            },
            artifact_gate: Phase8ArtifactGateCounters {
                manifest_missing_count: 0,
                manifest_hash_mismatch_count: 0,
                abi_mismatch_count: 0,
                layout_mismatch_count: 0,
                target_mismatch_count: 0,
                replay_missing_count: 0,
                telemetry_missing_count: 0,
            },
            proof_gate: Phase8ProofGateCounters {
                proof_verified_count: 2,
                proof_missing_count: 0,
                proof_failed_count: 0,
                proof_timeout_count: 0,
                proof_unknown_count: 0,
                proof_unsupported_target_count: 0,
                proof_stale_count: 0,
            },
            invalidation_gate: Phase8InvalidationGateCounters {
                fresh_install_count: 2,
                stale_install_reject_count: 0,
                stale_call_reject_count: 0,
                kill_switch_reject_count: 0,
                revoked_artifact_reject_count: 0,
                generation_mismatch_count: 0,
            },
            dispatch: Phase8DispatchCounters {
                eligible_call_count: 2,
                native_call_count: 2,
                baseline_call_count: 2,
                useful_native_count: 2,
                fallback_count: 0,
                deopt_count: 0,
                native_status_error_count: 0,
                shadow_mismatch_count: 0,
                crash_count: 0,
                internal_error_count: 0,
            },
            performance: Phase8PerformanceCounters {
                baseline_p50_us: 2.0,
                baseline_p95_us: 2.0,
                baseline_p99_us: 2.0,
                native_p50_us: 1.0,
                native_p95_us: 1.0,
                native_p99_us: 1.0,
                compile_p50_ms: 0.0,
                proof_p50_ms: 0.0,
                code_size_bytes: 0,
                cache_hit_count: 0,
                cache_miss_count: 0,
            },
            consumer: Phase8ConsumerCounters {
                ay: Phase8AYConsumerCounters {
                    solver_program_sha256: None,
                    solver_semantic_generation: "test-generation".to_string(),
                    solver_state_hash: None,
                    basis_epoch: "679".to_string(),
                    kernel_family: "other_allowlisted".to_string(),
                    row_region_sha256: None,
                    result_parity: Phase8AYResultParityCounters {
                        solver_result_mismatch_count: 0,
                        witness_mismatch_count: 0,
                        proof_regression_count: 0,
                        wrong_answer_count: 0,
                        score_regression_count: 0,
                        unknown_timeout_regression_count: 0,
                    },
                    mutation: Phase8AYMutationCounters {
                        mutation_attempt_count: 0,
                        mutation_commit_count: 0,
                        rollback_count: 0,
                        partial_row_deopt_count: 0,
                        bounds_reject_count: 0,
                        overflow_reject_count: 0,
                        alias_reject_count: 0,
                        stale_generation_reject_count: 0,
                    },
                    usefulness: Phase8AYUsefulnessCounters {
                        competition_instance_count: 2,
                        native_useful_application_count: 2,
                        fallback_application_count: 0,
                        profile_only_application_count: 0,
                    },
                },
            },
            promotion_verdict: Phase8PromotionVerdict {
                can_promote_beyond_canary: true,
                blockers: Vec::new(),
            },
        }
    }

    fn workload_summary() -> WorkloadSummary {
        WorkloadSummary {
            name: "test-ay-subsumption".to_string(),
            issue: 679,
            clause_count: 2,
            real_literal_lanes: 4,
            padded_literal_lanes: 8,
            contains_query_count: 1,
            subsumption_pair_count: 1,
            length_buckets: vec!["2".to_string()],
            variants: vec![
                "ay_neon_reference".to_string(),
                "trust_cg_o2_vectorized".to_string(),
            ],
            warmup_iterations: 1,
            measurement_repetitions: 1,
        }
    }
}
