// trust-cg-jit-matrix/lib.rs - Shared helpers for JIT matrix runners.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

pub mod bcp_baseline;
pub use trust_cg_process_env as env_lock;
pub mod parent_loop_baseline;

pub mod dimacs;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::Command;
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
use std::time::Instant;

use anyhow::{Context, Result, bail};
use serde::{Deserialize, Serialize};

pub mod solver_kernel_abi;

pub mod bcp_kernel;

pub mod bcp_module_builder;

pub mod parent_loop_module_builder;

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
pub mod jit_bcp_kernel;
/// PropagationContext-ABI (`ay_sat_watch_bcp`) verified BCP kernel (#678).
pub mod propagation_context_kernel;

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
pub mod jit_parent_loop_kernel;

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
pub mod jit_compile_cache;

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
pub mod jit_disk_cache;

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
pub mod executable_buffer_cache;

/// Stable aggregate counter schema for Phase 8 native promotion evidence.
pub const PHASE8_NATIVE_PROMOTION_COUNTERS_SCHEMA: &str =
    "trust-cg.phase8.native_promotion_counters.v1";
/// Stable ay subsumption counter family emitted by the ay matrix runner.
pub const PHASE8_AY_SUBSUMPTION_COUNTER_FAMILY: &str = "ay_subsumption";
/// Stable TY parent-loop counter family emitted by downstream smoke evidence.
pub const PHASE8_TY_PARENT_LOOP_COUNTER_FAMILY: &str = "ty_parent_loop";
/// Phase 8 mode for correctness-gated candidate evidence.
pub const PHASE8_NATIVE_PROMOTION_CANARY_MODE: &str = "canary";
/// Stable proof-policy token for ay subsumption correctness/throughput gating.
pub const PHASE8_AY_SUBSUMPTION_PROOF_POLICY: &str =
    "ay_subsumption_correctness_and_backend_gate_v1";
/// Maximum ay subsumption cases JSON size accepted by the matrix loader.
pub const MAX_AY_SUBSUMPTION_CASES_BYTES: u64 = 8 * 1024 * 1024;
/// Required artifact set for a ay Phase 8 promotion packet.
pub const PHASE8_AY_PROMOTION_PACKET_REQUIRED_ARTIFACTS: &[&str] = &[
    "artifact.manifest.json",
    "artifact.manifest.sha256",
    "phase8_native_promotion_counters.json",
    "gate-results.json",
    "command-metadata.json",
    "replay-reproduction.json",
];

/// Deterministic ay subsumption benchmark workload.
#[derive(Clone, Debug, Deserialize)]
pub struct AYSubsumptionCases {
    /// Workload name.
    pub name: String,
    /// GitHub issue that owns the workload.
    pub issue: u64,
    /// ay reference source path.
    pub source_reference: String,
    /// Padding literal that must never match real-lane queries.
    pub sentinel: i32,
    /// Human-readable literal encoding note.
    pub literal_encoding: String,
    /// Clause lengths covered by this fixture.
    pub clause_lengths: Vec<usize>,
    /// Clause arena entries.
    pub clauses: Vec<ClauseCase>,
    /// Literal containment checks.
    pub contains_queries: Vec<ContainsQuery>,
    /// Batch subsumption checks.
    pub subsumption_pairs: Vec<SubsumptionPair>,
    /// Required throughput matrix shape.
    pub benchmark_matrix: BenchmarkMatrix,
}

/// One clause fixture row.
#[derive(Clone, Debug, Deserialize)]
pub struct ClauseCase {
    /// Stable clause id.
    pub id: usize,
    /// Number of real literal lanes.
    pub length: usize,
    /// Padded length, divisible by four.
    pub padded_length: usize,
    /// Real literals.
    pub lits: Vec<i32>,
}

/// Literal containment expectation.
#[derive(Clone, Debug, Deserialize)]
pub struct ContainsQuery {
    /// Literal to search.
    pub literal: i32,
    /// Expected matching clause ids.
    pub expected_clause_ids: Vec<usize>,
    /// Coverage note.
    pub covers: String,
}

/// Batch subsumption expectation.
#[derive(Clone, Debug, Deserialize)]
pub struct SubsumptionPair {
    /// Candidate subset clause id.
    pub a: usize,
    /// Candidate superset clause id.
    pub b: usize,
    /// Expected subsumption result.
    pub expected: bool,
    /// Coverage note.
    pub covers: String,
}

/// Required benchmark shape from `cases.json`.
#[derive(Clone, Debug, Deserialize)]
pub struct BenchmarkMatrix {
    /// Clause length buckets to measure.
    pub length_buckets: Vec<String>,
    /// Required implementation variants.
    pub variants: Vec<String>,
    /// Warmup iterations per row.
    pub warmup_iterations: u64,
    /// Measurement repetitions per row.
    pub measurement_repetitions: u64,
}

/// Validated workload summary emitted by the runner.
#[derive(Clone, Debug, Serialize)]
pub struct WorkloadSummary {
    /// Workload name.
    pub name: String,
    /// GitHub issue number.
    pub issue: u64,
    /// Number of clauses.
    pub clause_count: usize,
    /// Total real lanes.
    pub real_literal_lanes: usize,
    /// Total padded lanes.
    pub padded_literal_lanes: usize,
    /// Containment query count.
    pub contains_query_count: usize,
    /// Subsumption pair count.
    pub subsumption_pair_count: usize,
    /// Clause length buckets.
    pub length_buckets: Vec<String>,
    /// Required variants.
    pub variants: Vec<String>,
    /// Warmup iterations.
    pub warmup_iterations: u64,
    /// Measurement repetitions.
    pub measurement_repetitions: u64,
}

/// Deterministic correctness artifact for the scalar oracle.
#[derive(Clone, Debug, Serialize)]
pub struct CorrectnessReport {
    /// Artifact schema.
    pub schema: &'static str,
    /// Workload summary.
    pub workload: WorkloadSummary,
    /// Containment oracle rows.
    pub contains: Vec<ContainsResult>,
    /// Subsumption oracle rows.
    pub subsumption: Vec<SubsumptionResult>,
    /// Per-backend deterministic correctness adapter rows.
    pub backend_rows: Vec<CorrectnessBackendRow>,
    /// Number of fixture/oracle mismatches.
    pub mismatch_count: usize,
    /// Runner status.
    pub status: &'static str,
    /// Why this is not final #571 acceptance evidence.
    pub note: &'static str,
}

/// Throughput artifact schema emitted before and after backend execution.
#[derive(Clone, Debug, Serialize)]
pub struct ThroughputSummaryReport {
    /// Artifact schema.
    pub schema: &'static str,
    /// Runner status.
    pub status: &'static str,
    /// Workload summary.
    pub workload: WorkloadSummary,
    /// Per operation/bucket/variant summary rows.
    pub rows: Vec<ThroughputSummaryRow>,
    /// Machine-readable accounting for partial row coverage.
    pub row_accounting: ThroughputRowAccounting,
    /// Recommendation gate summary.
    pub gate: ThroughputGate,
    /// Why this is not final #571 acceptance evidence.
    pub note: &'static str,
}

/// Counts of planned and populated rows in the throughput summary.
#[derive(Clone, Debug, Serialize)]
pub struct ThroughputRowAccounting {
    /// Total planned matrix rows.
    pub planned_rows: usize,
    /// ay reference rows populated by bounded execution.
    pub measured_ay_reference_rows: usize,
    /// Trust Codegen mixed probe rows populated by bounded execution.
    pub measured_trust_cg_mixed_probe_rows: usize,
    /// Trust Codegen numeric-bucket probe rows populated by bounded execution.
    pub measured_trust_cg_bucket_probe_rows: usize,
    /// Real Trust Codegen O2/O3 pipeline backend rows populated by bounded execution.
    pub measured_trust_cg_backend_rows: usize,
    /// Rows still waiting for the real backend matrix.
    pub pending_backend_rows: usize,
}

/// One throughput summary row.
#[derive(Clone, Debug, Serialize)]
pub struct ThroughputSummaryRow {
    /// Operation under measurement.
    pub operation: &'static str,
    /// Clause-length bucket.
    pub length_bucket: String,
    /// Backend variant.
    pub variant: String,
    /// Configured warmup iterations.
    pub warmup_iterations: u64,
    /// Configured measurement repetitions.
    pub measurement_repetitions: u64,
    /// Measurement status for this row.
    pub status: &'static str,
    /// Phase 7/8 promotion disposition for this row.
    pub promotion_disposition: &'static str,
    /// Whether this row may contribute product install evidence after packet gates pass.
    pub product_install_evidence: bool,
    /// Mean throughput after execution.
    pub mean_throughput_per_us: Option<f64>,
    /// Standard deviation after execution.
    pub stddev_throughput_per_us: Option<f64>,
    /// Coefficient of variation after execution.
    pub coefficient_of_variation: Option<f64>,
    /// Ratio against ay NEON after execution.
    pub ay_relative_ratio: Option<f64>,
    /// Scalar-control speedup after execution.
    pub scalar_speedup: Option<f64>,
}

/// #571 throughput recommendation gate.
#[derive(Clone, Debug, Serialize)]
pub struct ThroughputGate {
    /// Required geometric-mean ratio against ay NEON.
    pub required_ay_relative_geomean: f64,
    /// O2 vectorized geometric-mean ratio after execution.
    pub trust_cg_o2_vectorized_geomean: Option<f64>,
    /// O3 vectorized geometric-mean ratio after execution.
    pub trust_cg_o3_vectorized_geomean: Option<f64>,
    /// Whether the measured matrix passes the throughput gate.
    pub passed: Option<bool>,
}

/// Phase 8 aggregate native-promotion counter artifact.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8NativePromotionCounters {
    /// Artifact schema.
    pub schema: &'static str,
    /// Exact scope that the counters are allowed to summarize.
    pub counter_scope: Phase8NativePromotionCounterScope,
    /// Candidate lifecycle counters.
    pub lifecycle: Phase8LifecycleCounters,
    /// Artifact identity and replay binding counters.
    pub artifact_gate: Phase8ArtifactGateCounters,
    /// Proof or correctness-gate counters.
    pub proof_gate: Phase8ProofGateCounters,
    /// Runtime invalidation counters.
    pub invalidation_gate: Phase8InvalidationGateCounters,
    /// Native dispatch counters.
    pub dispatch: Phase8DispatchCounters,
    /// Performance summary counters derived from measured throughput rows.
    pub performance: Phase8PerformanceCounters,
    /// Consumer-specific counters.
    pub consumer: Phase8ConsumerCounters,
    /// Machine-readable promotion verdict.
    pub promotion_verdict: Phase8PromotionVerdict,
}

/// Phase 8 aggregate native-promotion counter artifact for TY scopes.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8TyNativePromotionCounters {
    /// Artifact schema.
    pub schema: &'static str,
    /// Exact scope that the counters are allowed to summarize.
    pub counter_scope: Phase8NativePromotionCounterScope,
    /// Candidate lifecycle counters.
    pub lifecycle: Phase8LifecycleCounters,
    /// Artifact identity and replay binding counters.
    pub artifact_gate: Phase8ArtifactGateCounters,
    /// Proof or correctness-gate counters.
    pub proof_gate: Phase8ProofGateCounters,
    /// Runtime invalidation counters.
    pub invalidation_gate: Phase8InvalidationGateCounters,
    /// Native dispatch counters.
    pub dispatch: Phase8DispatchCounters,
    /// Performance summary counters derived from measured throughput rows.
    pub performance: Phase8PerformanceCounters,
    /// Consumer-specific counters.
    pub consumer: Phase8TyConsumerCounterEnvelope,
    /// Machine-readable promotion verdict.
    pub promotion_verdict: Phase8PromotionVerdict,
}

/// Consumer-specific Phase 8 counters for TY-scoped artifacts.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8TyConsumerCounterEnvelope {
    /// TY-specific counters.
    pub ty: Phase8TyConsumerCounters,
}

/// Scope key for Phase 8 aggregate counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8NativePromotionCounterScope {
    /// Consumer name.
    pub consumer: String,
    /// Stable candidate family.
    pub family: String,
    /// Promotion mode.
    pub mode: String,
    /// Target triple under test.
    pub target_triple: String,
    /// Target CPU or host CPU descriptor.
    pub target_cpu: String,
    /// SHA256 of the target feature descriptor used for this run.
    pub target_features_sha256: String,
    /// SHA256 of the proof or correctness-gate policy.
    pub proof_policy_sha256: String,
    /// Layout checksum for the benchmark/report matrix.
    pub layout_checksum: String,
    /// Consumer-visible invalidation key.
    pub invalidation_key: String,
    /// Canonical manifest hash when the caller has one available.
    pub manifest_sha256: Option<String>,
    /// Expected canonical manifest hash, when an independent bundle or gate
    /// reference is available to compare against the caller-provided hash.
    pub expected_manifest_sha256: Option<String>,
}

/// Downstream TY parent-loop evidence used to derive Phase 8 promotion counters.
#[derive(Clone, Debug)]
pub struct Phase8TyParentLoopEvidence {
    /// TY spec under test.
    pub spec_name: String,
    /// Artifact root emitted by the downstream TY smoke, when available.
    pub artifact_root: Option<String>,
    /// Stable digest for the TY state layout, when available.
    pub state_layout_sha256: Option<String>,
    /// Stable digest for the transition/action cluster, when available.
    pub transition_cluster_sha256: Option<String>,
    /// Profile-generate report identity/hash binding for this canary capture.
    pub profile_generate_report: Phase8TyProfileReportBinding,
    /// Profile-use report identity/hash binding for the native parent-loop compile.
    pub profile_use_report: Phase8TyProfileUseReportBinding,
    /// Downstream CLI verdict. `None` means the downstream proof did not run.
    pub downstream_cli_passed: Option<bool>,
    /// Whether the strict native selftest completed.
    pub strict_selftest_completed: bool,
    /// Whether the native-fused dispatch path was active.
    pub native_fused_path_active: bool,
    /// Whether the compiled BFS level-loop marker was observed.
    pub compiled_bfs_level_loop_fused: bool,
    /// Whether native dispatch was actually promoted for the run.
    pub native_dispatch_promoted: bool,
    /// Whether the downstream artifact explicitly marked the run non-promoting.
    pub non_promoting: bool,
    /// Expected action count for the spec.
    pub expected_action_count: usize,
    /// Observed action count from the downstream artifact.
    pub actual_action_count: Option<usize>,
    /// Expected invariant count for the spec.
    pub expected_invariant_count: usize,
    /// Observed invariant count from the downstream artifact.
    pub actual_invariant_count: Option<usize>,
    /// Expected state-constraint count for the spec.
    pub expected_state_constraint_count: usize,
    /// Observed state-constraint count from the downstream artifact.
    pub actual_state_constraint_count: Option<usize>,
    /// Expected serialized state length.
    pub expected_state_len: usize,
    /// Observed serialized state length.
    pub actual_state_len: Option<usize>,
    /// Flat-state bytes copied by the native parent-loop helper.
    pub flat_state_copy_bytes: usize,
    /// Fingerprints computed by the native parent-loop helper.
    pub fingerprint_count: usize,
    /// Fingerprint payload bytes processed by the native parent-loop helper.
    pub fingerprint_bytes: usize,
    /// Helper calls proven inlined in the promoted native path.
    pub helper_inline_count: usize,
    /// Alias/readonly metadata hits observed for helper/state accesses.
    pub alias_readonly_metadata_hit_count: usize,
    /// Compiled BFS levels completed.
    pub compiled_bfs_levels_completed: usize,
    /// Compiled BFS parents processed.
    pub compiled_bfs_parents_processed: usize,
    /// Compiled BFS successors generated.
    pub compiled_bfs_successors_generated: usize,
    /// Compiled BFS new successors.
    pub compiled_bfs_successors_new: usize,
    /// Compiled BFS total states.
    pub compiled_bfs_total_states: usize,
    /// Native-eligible calls observed in the downstream run.
    pub eligible_native_call_count: usize,
    /// Native calls observed in the downstream run.
    pub native_call_count: usize,
    /// Baseline calls observed in the downstream run.
    pub baseline_call_count: usize,
    /// Useful native calls allowed to contribute to promotion.
    pub useful_native_call_count: usize,
    /// Fallback count.
    pub fallback_count: usize,
    /// Deoptimization count.
    pub deopt_count: usize,
    /// Native status error count.
    pub native_status_error_count: usize,
    /// Shadow mismatch count.
    pub shadow_mismatch_count: usize,
    /// Crash count.
    pub crash_count: usize,
    /// Crash packet artifact count.
    pub crash_packet_count: usize,
    /// Internal error count.
    pub internal_error_count: usize,
    /// Replay artifacts captured by the downstream run.
    pub replay_artifact_count: usize,
    /// Telemetry artifacts captured by the downstream run.
    pub telemetry_artifact_count: usize,
    /// Cache hit count.
    pub cache_hit_count: usize,
    /// Cache miss count.
    pub cache_miss_count: usize,
}

/// Stable identity for a TY profile report participating in Phase 8 evidence.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8TyProfileReportBinding {
    /// Caller-visible report identifier, such as an artifact path or event id.
    pub report_identity: Option<String>,
    /// SHA256 of the profile report payload, when captured.
    pub report_sha256: Option<String>,
    /// SHA256 of the `.profdata` artifact referenced by the report.
    pub profile_sha256: Option<String>,
    /// Stable PGO freshness key digest from the report.
    pub profile_key_digest: Option<String>,
}

impl Phase8TyProfileReportBinding {
    fn has_identity_or_hash(&self) -> bool {
        phase8_non_empty_optional(self.report_identity.as_deref()).is_some()
            || phase8_non_empty_optional(self.report_sha256.as_deref()).is_some()
            || phase8_non_empty_optional(self.profile_sha256.as_deref()).is_some()
            || phase8_non_empty_optional(self.profile_key_digest.as_deref()).is_some()
    }

    fn profile_sha256(&self) -> Option<&str> {
        phase8_non_empty_optional(self.profile_sha256.as_deref())
    }

    fn profile_key_digest(&self) -> Option<&str> {
        phase8_non_empty_optional(self.profile_key_digest.as_deref())
    }
}

/// Stable identity and freshness verdict for a TY profile-use report.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8TyProfileUseReportBinding {
    /// Caller-visible report identifier, such as an artifact path or event id.
    pub report_identity: Option<String>,
    /// SHA256 of the profile-use report payload, when captured.
    pub report_sha256: Option<String>,
    /// SHA256 of the `.profdata` artifact consumed by profile-use.
    pub profile_sha256: Option<String>,
    /// Stable PGO freshness key digest from the profile-use report.
    pub profile_key_digest: Option<String>,
    /// Whether the profile-use report explicitly marked the profile fresh.
    pub fresh: Option<bool>,
    /// Profile-use freshness reason emitted by the producer, when available.
    pub freshness_reason: Option<String>,
    /// Whether the profile-use pass was scheduled in the optimizing pipeline.
    pub scheduled: Option<bool>,
}

impl Phase8TyProfileUseReportBinding {
    fn has_identity_or_hash(&self) -> bool {
        phase8_non_empty_optional(self.report_identity.as_deref()).is_some()
            || phase8_non_empty_optional(self.report_sha256.as_deref()).is_some()
            || phase8_non_empty_optional(self.profile_sha256.as_deref()).is_some()
            || phase8_non_empty_optional(self.profile_key_digest.as_deref()).is_some()
    }

    fn profile_sha256(&self) -> Option<&str> {
        phase8_non_empty_optional(self.profile_sha256.as_deref())
    }

    fn profile_key_digest(&self) -> Option<&str> {
        phase8_non_empty_optional(self.profile_key_digest.as_deref())
    }
}

/// Phase 8 candidate lifecycle counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8LifecycleCounters {
    /// Number of rows observed in the scoped matrix.
    pub observed_count: usize,
    /// Number of Trust Codegen vectorized backend rows nominated for promotion.
    pub nominated_count: usize,
    /// Profile-only native compile count.
    pub profile_only_compiled_count: usize,
    /// Shadow dispatch count.
    pub shadow_dispatch_count: usize,
    /// Canary install count.
    pub canary_install_count: usize,
    /// Active promotion count.
    pub active_promotion_count: usize,
    /// Install rejection count.
    pub install_rejected_count: usize,
    /// Invalidated artifact count.
    pub invalidated_count: usize,
    /// Rollback count.
    pub rolled_back_count: usize,
    /// Revoked artifact count.
    pub revoked_count: usize,
}

/// Phase 8 artifact/replay binding counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8ArtifactGateCounters {
    /// Missing manifest count.
    pub manifest_missing_count: usize,
    /// Manifest hash mismatch count.
    pub manifest_hash_mismatch_count: usize,
    /// ABI mismatch count.
    pub abi_mismatch_count: usize,
    /// Layout mismatch count.
    pub layout_mismatch_count: usize,
    /// Target mismatch count.
    pub target_mismatch_count: usize,
    /// Missing replay artifact count.
    pub replay_missing_count: usize,
    /// Missing telemetry artifact count.
    pub telemetry_missing_count: usize,
}

/// Phase 8 proof or correctness gate counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8ProofGateCounters {
    /// Count of rows covered by the correctness gate.
    pub proof_verified_count: usize,
    /// Missing proof/correctness evidence count.
    pub proof_missing_count: usize,
    /// Failed proof/correctness evidence count.
    pub proof_failed_count: usize,
    /// Timed-out proof count.
    pub proof_timeout_count: usize,
    /// Unknown proof result count.
    pub proof_unknown_count: usize,
    /// Unsupported target proof count.
    pub proof_unsupported_target_count: usize,
    /// Stale proof count.
    pub proof_stale_count: usize,
}

/// Phase 8 invalidation counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8InvalidationGateCounters {
    /// Fresh install count.
    pub fresh_install_count: usize,
    /// Stale install rejection count.
    pub stale_install_reject_count: usize,
    /// Stale call rejection count.
    pub stale_call_reject_count: usize,
    /// Kill-switch rejection count.
    pub kill_switch_reject_count: usize,
    /// Revoked artifact rejection count.
    pub revoked_artifact_reject_count: usize,
    /// Generation mismatch count.
    pub generation_mismatch_count: usize,
}

/// Phase 8 dispatch counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8DispatchCounters {
    /// Eligible native call or row count.
    pub eligible_call_count: usize,
    /// Native call or row count.
    pub native_call_count: usize,
    /// Baseline ay reference call or row count.
    pub baseline_call_count: usize,
    /// Useful native call or row count.
    pub useful_native_count: usize,
    /// Fallback count.
    pub fallback_count: usize,
    /// Deoptimization count.
    pub deopt_count: usize,
    /// Native status error count.
    pub native_status_error_count: usize,
    /// Shadow mismatch count.
    pub shadow_mismatch_count: usize,
    /// Crash count.
    pub crash_count: usize,
    /// Internal error count.
    pub internal_error_count: usize,
}

/// Phase 8 performance counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8PerformanceCounters {
    /// Baseline p50 latency estimate in microseconds.
    pub baseline_p50_us: f64,
    /// Baseline p95 latency estimate in microseconds.
    pub baseline_p95_us: f64,
    /// Baseline p99 latency estimate in microseconds.
    pub baseline_p99_us: f64,
    /// Native p50 latency estimate in microseconds.
    pub native_p50_us: f64,
    /// Native p95 latency estimate in microseconds.
    pub native_p95_us: f64,
    /// Native p99 latency estimate in microseconds.
    pub native_p99_us: f64,
    /// Native compile p50 in milliseconds.
    pub compile_p50_ms: f64,
    /// Proof/correctness gate p50 in milliseconds.
    pub proof_p50_ms: f64,
    /// Native code size in bytes.
    pub code_size_bytes: usize,
    /// Cache hit count.
    pub cache_hit_count: usize,
    /// Cache miss count.
    pub cache_miss_count: usize,
}

/// Consumer-specific Phase 8 counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8ConsumerCounters {
    /// ay-specific counters.
    pub ay: Phase8AYConsumerCounters,
}

/// ay-specific Phase 8 counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8AYConsumerCounters {
    /// Stable solver-program digest, when available.
    pub solver_program_sha256: Option<String>,
    /// Solver semantic generation.
    pub solver_semantic_generation: String,
    /// Hash of relevant immutable solver state, when available.
    pub solver_state_hash: Option<String>,
    /// Basis or row-layout epoch.
    pub basis_epoch: String,
    /// ay kernel family.
    pub kernel_family: String,
    /// Hash of the affected row or basis region, when available.
    pub row_region_sha256: Option<String>,
    /// Result parity counters.
    pub result_parity: Phase8AYResultParityCounters,
    /// Mutation counters.
    pub mutation: Phase8AYMutationCounters,
    /// ay usefulness counters.
    pub usefulness: Phase8AYUsefulnessCounters,
}

/// ay result parity counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8AYResultParityCounters {
    /// Solver-result mismatch count.
    pub solver_result_mismatch_count: usize,
    /// Witness mismatch count.
    pub witness_mismatch_count: usize,
    /// Proof regression count.
    pub proof_regression_count: usize,
    /// Wrong-answer count.
    pub wrong_answer_count: usize,
    /// Score regression count.
    pub score_regression_count: usize,
    /// UNKNOWN or timeout regression count.
    pub unknown_timeout_regression_count: usize,
}

/// ay mutation counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8AYMutationCounters {
    /// Mutation attempt count.
    pub mutation_attempt_count: usize,
    /// Mutation commit count.
    pub mutation_commit_count: usize,
    /// Rollback count.
    pub rollback_count: usize,
    /// Partial-row deoptimization count.
    pub partial_row_deopt_count: usize,
    /// Bounds rejection count.
    pub bounds_reject_count: usize,
    /// Overflow rejection count.
    pub overflow_reject_count: usize,
    /// Alias rejection count.
    pub alias_reject_count: usize,
    /// Stale generation rejection count.
    pub stale_generation_reject_count: usize,
}

/// ay useful-native counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8AYUsefulnessCounters {
    /// Competition or fixture instance count.
    pub competition_instance_count: usize,
    /// Useful native application count.
    pub native_useful_application_count: usize,
    /// Fallback application count.
    pub fallback_application_count: usize,
    /// Profile-only application count.
    pub profile_only_application_count: usize,
}

impl Phase8AYConsumerCounters {
    /// Whether this payload is the empty non-ay marker.
    pub fn is_not_applicable(&self) -> bool {
        self.solver_semantic_generation == "not_applicable"
            && self.basis_epoch == "not_applicable"
            && self.kernel_family == "not_applicable"
            && self.solver_program_sha256.is_none()
            && self.solver_state_hash.is_none()
            && self.row_region_sha256.is_none()
            && self.result_parity.solver_result_mismatch_count == 0
            && self.result_parity.witness_mismatch_count == 0
            && self.result_parity.proof_regression_count == 0
            && self.result_parity.wrong_answer_count == 0
            && self.result_parity.score_regression_count == 0
            && self.result_parity.unknown_timeout_regression_count == 0
            && self.mutation.mutation_attempt_count == 0
            && self.mutation.mutation_commit_count == 0
            && self.mutation.rollback_count == 0
            && self.mutation.partial_row_deopt_count == 0
            && self.mutation.bounds_reject_count == 0
            && self.mutation.overflow_reject_count == 0
            && self.mutation.alias_reject_count == 0
            && self.mutation.stale_generation_reject_count == 0
            && self.usefulness.competition_instance_count == 0
            && self.usefulness.native_useful_application_count == 0
            && self.usefulness.fallback_application_count == 0
            && self.usefulness.profile_only_application_count == 0
    }

    /// Empty ay counter payload for non-ay Phase 8 evidence records.
    pub fn not_applicable() -> Self {
        Self {
            solver_program_sha256: None,
            solver_semantic_generation: "not_applicable".to_string(),
            solver_state_hash: None,
            basis_epoch: "not_applicable".to_string(),
            kernel_family: "not_applicable".to_string(),
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
                competition_instance_count: 0,
                native_useful_application_count: 0,
                fallback_application_count: 0,
                profile_only_application_count: 0,
            },
        }
    }
}

/// TY-specific Phase 8 counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8TyConsumerCounters {
    /// TY spec under test.
    pub spec_name: String,
    /// Artifact root emitted by the downstream TY smoke, when available.
    pub artifact_root: Option<String>,
    /// Stable digest for the TY state layout, when available.
    pub state_layout_sha256: Option<String>,
    /// Stable digest for the transition/action cluster, when available.
    pub transition_cluster_sha256: Option<String>,
    /// Profile-generate/profile-use report bindings for TY PGO evidence.
    pub profile_reports: Phase8TyProfileReportCounters,
    /// TY shape/parity counters.
    pub parity: Phase8TyParityCounters,
    /// TY execution-shape counters for copy/fingerprint/helper evidence.
    pub execution_shape: Phase8TyExecutionShapeCounters,
    /// TY native-path counters.
    pub native_path: Phase8TyNativePathCounters,
    /// TY artifact counters.
    pub artifacts: Phase8TyArtifactCounters,
}

/// TY profile-generate/profile-use report binding counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8TyProfileReportCounters {
    /// Profile-generate report identity/hash binding.
    pub profile_generate: Phase8TyProfileReportBinding,
    /// Profile-use report identity/hash binding and freshness verdict.
    pub profile_use: Phase8TyProfileUseReportBinding,
    /// Missing profile-generate report identity/hash count.
    pub profile_generate_report_missing_count: usize,
    /// Missing profile-use report identity/hash count.
    pub profile_use_report_missing_count: usize,
    /// Profile-use report explicitly stale count.
    pub profile_use_report_stale_count: usize,
    /// Profile-use report present but not marked fresh count.
    pub profile_use_report_not_fresh_count: usize,
    /// Profile-generate/profile-use profile hash or key mismatch count.
    pub profile_report_binding_mismatch_count: usize,
}

/// TY shape/parity counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8TyParityCounters {
    /// Action-count mismatch count.
    pub action_count_mismatch_count: usize,
    /// Invariant-count mismatch count.
    pub invariant_count_mismatch_count: usize,
    /// State-constraint-count mismatch count.
    pub state_constraint_count_mismatch_count: usize,
    /// Serialized state-length mismatch count.
    pub state_len_mismatch_count: usize,
    /// Missing shape evidence count.
    pub shape_evidence_missing_count: usize,
    /// Wrong-answer or semantic mismatch count.
    pub wrong_answer_count: usize,
}

/// TY execution-shape counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8TyExecutionShapeCounters {
    /// Generated successor count.
    pub generated_state_count: usize,
    /// Distinct/new successor count.
    pub distinct_state_count: usize,
    /// Fingerprint computation count.
    pub fingerprint_count: usize,
    /// Parent-index checks performed.
    pub parent_index_checked_count: usize,
    /// Flat-state bytes copied by the native path.
    pub flat_state_copy_bytes: usize,
    /// Fingerprint payload bytes processed by the native path.
    pub fingerprint_bytes: usize,
    /// Helper calls proven inlined.
    pub helper_inline_count: usize,
    /// Alias/readonly metadata hits observed by verifier or artifact evidence.
    pub alias_readonly_metadata_hit_count: usize,
    /// Missing execution-shape evidence count.
    pub execution_shape_evidence_missing_count: usize,
}

/// TY native-path counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8TyNativePathCounters {
    /// Strict native selftest completion count.
    pub strict_selftest_completed_count: usize,
    /// Native-fused path activation count.
    pub native_fused_path_active_count: usize,
    /// Compiled BFS level-loop marker count.
    pub compiled_bfs_level_loop_fused_count: usize,
    /// Native dispatch promotion count.
    pub native_dispatch_promoted_count: usize,
    /// Non-promoting artifact count.
    pub non_promoting_count: usize,
    /// Compiled BFS levels completed.
    pub compiled_bfs_levels_completed: usize,
    /// Compiled BFS parents processed.
    pub compiled_bfs_parents_processed: usize,
    /// Compiled BFS successors generated.
    pub compiled_bfs_successors_generated: usize,
    /// Compiled BFS new successors.
    pub compiled_bfs_successors_new: usize,
    /// Compiled BFS total states.
    pub compiled_bfs_total_states: usize,
}

/// TY artifact counters.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8TyArtifactCounters {
    /// Replay artifact count.
    pub replay_artifact_count: usize,
    /// Telemetry artifact count.
    pub telemetry_artifact_count: usize,
    /// Crash packet count.
    pub crash_packet_count: usize,
}

impl Phase8TyConsumerCounters {
    /// Whether this payload is the empty non-TY marker.
    pub fn is_not_applicable(&self) -> bool {
        self.spec_name == "not_applicable"
            && self.artifact_root.is_none()
            && self.state_layout_sha256.is_none()
            && self.transition_cluster_sha256.is_none()
            && !self.profile_reports.profile_generate.has_identity_or_hash()
            && !self.profile_reports.profile_use.has_identity_or_hash()
            && self.profile_reports.profile_use.fresh.is_none()
            && self.profile_reports.profile_use.freshness_reason.is_none()
            && self.profile_reports.profile_use.scheduled.is_none()
            && self.profile_reports.profile_generate_report_missing_count == 0
            && self.profile_reports.profile_use_report_missing_count == 0
            && self.profile_reports.profile_use_report_stale_count == 0
            && self.profile_reports.profile_use_report_not_fresh_count == 0
            && self.profile_reports.profile_report_binding_mismatch_count == 0
            && self.parity.action_count_mismatch_count == 0
            && self.parity.invariant_count_mismatch_count == 0
            && self.parity.state_constraint_count_mismatch_count == 0
            && self.parity.state_len_mismatch_count == 0
            && self.parity.shape_evidence_missing_count == 0
            && self.parity.wrong_answer_count == 0
            && self.execution_shape.generated_state_count == 0
            && self.execution_shape.distinct_state_count == 0
            && self.execution_shape.fingerprint_count == 0
            && self.execution_shape.parent_index_checked_count == 0
            && self.execution_shape.flat_state_copy_bytes == 0
            && self.execution_shape.fingerprint_bytes == 0
            && self.execution_shape.helper_inline_count == 0
            && self.execution_shape.alias_readonly_metadata_hit_count == 0
            && self.execution_shape.execution_shape_evidence_missing_count == 0
            && self.native_path.strict_selftest_completed_count == 0
            && self.native_path.native_fused_path_active_count == 0
            && self.native_path.compiled_bfs_level_loop_fused_count == 0
            && self.native_path.native_dispatch_promoted_count == 0
            && self.native_path.non_promoting_count == 0
            && self.native_path.compiled_bfs_levels_completed == 0
            && self.native_path.compiled_bfs_parents_processed == 0
            && self.native_path.compiled_bfs_successors_generated == 0
            && self.native_path.compiled_bfs_successors_new == 0
            && self.native_path.compiled_bfs_total_states == 0
            && self.artifacts.replay_artifact_count == 0
            && self.artifacts.telemetry_artifact_count == 0
            && self.artifacts.crash_packet_count == 0
    }

    /// Empty TY counter payload for non-TY Phase 8 evidence records.
    pub fn not_applicable() -> Self {
        Self {
            spec_name: "not_applicable".to_string(),
            artifact_root: None,
            state_layout_sha256: None,
            transition_cluster_sha256: None,
            profile_reports: Phase8TyProfileReportCounters {
                profile_generate: Phase8TyProfileReportBinding {
                    report_identity: None,
                    report_sha256: None,
                    profile_sha256: None,
                    profile_key_digest: None,
                },
                profile_use: Phase8TyProfileUseReportBinding {
                    report_identity: None,
                    report_sha256: None,
                    profile_sha256: None,
                    profile_key_digest: None,
                    fresh: None,
                    freshness_reason: None,
                    scheduled: None,
                },
                profile_generate_report_missing_count: 0,
                profile_use_report_missing_count: 0,
                profile_use_report_stale_count: 0,
                profile_use_report_not_fresh_count: 0,
                profile_report_binding_mismatch_count: 0,
            },
            parity: Phase8TyParityCounters {
                action_count_mismatch_count: 0,
                invariant_count_mismatch_count: 0,
                state_constraint_count_mismatch_count: 0,
                state_len_mismatch_count: 0,
                shape_evidence_missing_count: 0,
                wrong_answer_count: 0,
            },
            execution_shape: Phase8TyExecutionShapeCounters {
                generated_state_count: 0,
                distinct_state_count: 0,
                fingerprint_count: 0,
                parent_index_checked_count: 0,
                flat_state_copy_bytes: 0,
                fingerprint_bytes: 0,
                helper_inline_count: 0,
                alias_readonly_metadata_hit_count: 0,
                execution_shape_evidence_missing_count: 0,
            },
            native_path: Phase8TyNativePathCounters {
                strict_selftest_completed_count: 0,
                native_fused_path_active_count: 0,
                compiled_bfs_level_loop_fused_count: 0,
                native_dispatch_promoted_count: 0,
                non_promoting_count: 0,
                compiled_bfs_levels_completed: 0,
                compiled_bfs_parents_processed: 0,
                compiled_bfs_successors_generated: 0,
                compiled_bfs_successors_new: 0,
                compiled_bfs_total_states: 0,
            },
            artifacts: Phase8TyArtifactCounters {
                replay_artifact_count: 0,
                telemetry_artifact_count: 0,
                crash_packet_count: 0,
            },
        }
    }
}

/// Phase 8 promotion verdict.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8PromotionVerdict {
    /// Whether this scoped counter bundle can promote beyond canary.
    pub can_promote_beyond_canary: bool,
    /// Typed blockers that explain a false verdict.
    pub blockers: Vec<Phase8PromotionBlocker>,
}

/// Typed Phase 8 promotion blocker.
#[derive(Clone, Debug, Serialize)]
pub struct Phase8PromotionBlocker {
    /// Stable blocker code.
    pub code: String,
    /// Number of rows or mismatches represented by this blocker.
    pub count: usize,
    /// Human-readable blocker message.
    pub message: String,
}

/// Return fail-closed blockers for required ay promotion packet artifacts that
/// are missing from `packet_root`.
pub fn phase8_ay_promotion_packet_missing_artifact_blockers(
    packet_root: &Path,
    required_artifacts: &[&str],
) -> Vec<Phase8PromotionBlocker> {
    required_artifacts
        .iter()
        .filter(|artifact| !packet_root.join(artifact).is_file())
        .map(|artifact| Phase8PromotionBlocker {
            code: "required_packet_artifact_missing".to_string(),
            count: 1,
            message: format!("required ay promotion packet artifact is missing: {artifact}"),
        })
        .collect()
}

/// Readiness artifact for backend adapters that will populate the matrix.
#[derive(Clone, Debug, Serialize)]
pub struct BackendReadinessReport {
    /// Artifact schema.
    pub schema: &'static str,
    /// Runner status.
    pub status: &'static str,
    /// Workload summary.
    pub workload: WorkloadSummary,
    /// One row per requested backend variant.
    pub rows: Vec<BackendReadinessRow>,
    /// Why this is not final #571 acceptance evidence.
    pub note: &'static str,
}

/// ay reference backend discovery state.
#[derive(Clone, Debug, Serialize)]
pub struct AYReferenceBackendState {
    /// ay checkout path.
    pub repo: String,
    /// Requested ay revision.
    pub requested_rev: String,
    /// Resolved ay commit, if available.
    pub resolved_rev: Option<String>,
    /// Whether the ay checkout is dirty.
    pub dirty: Option<bool>,
    /// Expected ay source file path.
    pub source_path: String,
    /// Whether the expected source file exists.
    pub source_exists: bool,
    /// Source path inspected through the requested git revision.
    pub revision_source_path: String,
    /// Whether the source exists at the requested git revision.
    pub revision_source_exists: bool,
    /// SHA256 of the requested-revision source, when inspectable.
    pub revision_source_sha256: Option<String>,
    /// Byte length of the requested-revision source, when inspectable.
    pub revision_source_size_bytes: Option<u64>,
    /// Deterministic checks for expected ay scanner/NEON symbols.
    pub source_checks: Vec<AYReferenceSourceCheck>,
    /// Whether the ay reference adapter has enough data to populate artifacts.
    pub adapter_ready: bool,
}

/// Expected ay source symbol check.
#[derive(Clone, Debug, Serialize)]
pub struct AYReferenceSourceCheck {
    /// Symbol or token inspected in the ay source.
    pub token: &'static str,
    /// Whether the token is present.
    pub present: bool,
}

/// Optional ay reference execution artifact.
#[derive(Clone, Debug, Serialize)]
pub struct AYReferenceExecutionReport {
    /// Artifact schema.
    pub schema: &'static str,
    /// Aggregate execution status.
    pub status: &'static str,
    /// Adapter family.
    pub backend_kind: &'static str,
    /// Host architecture that produced this artifact.
    pub host_arch: &'static str,
    /// Host OS that produced this artifact.
    pub host_os: &'static str,
    /// ay checkout path.
    pub repo: Option<String>,
    /// Requested ay revision.
    pub requested_rev: Option<String>,
    /// Resolved ay commit, if available.
    pub resolved_rev: Option<String>,
    /// ay requested-revision source SHA256, when inspectable.
    pub source_sha256: Option<String>,
    /// Generated helper source path.
    pub helper_source_path: Option<String>,
    /// Generated helper binary path.
    pub helper_binary_path: Option<String>,
    /// Number of containment mismatches found by executing ay.
    pub contains_mismatch_count: usize,
    /// Number of subsumption mismatches found by executing ay.
    pub subsumption_mismatch_count: usize,
    /// Operation timing rows produced by ay execution.
    pub operation_measurements: Vec<AYReferenceOperationMeasurement>,
    /// Stable machine-readable error code, when unavailable.
    pub error_code: Option<&'static str>,
    /// Human-readable status detail.
    pub message: String,
    /// Why this is not final #571 acceptance evidence.
    pub note: &'static str,
}

/// One measured ay reference operation row.
#[derive(Clone, Debug, Serialize)]
pub struct AYReferenceOperationMeasurement {
    /// Operation under measurement.
    pub operation: &'static str,
    /// Workload bucket covered by this bounded reference measurement.
    pub workload_bucket: String,
    /// Measurement status.
    pub status: &'static str,
    /// Warmup iterations run before timing.
    pub warmup_iterations: usize,
    /// Number of timed repetitions.
    pub measurement_repetitions: usize,
    /// Number of fixture batches per timed repetition.
    pub batches_per_repetition: usize,
    /// Logical operation items per fixture batch.
    pub items_per_batch: usize,
    /// Total timed logical operation items.
    pub total_items: usize,
    /// Raw elapsed nanoseconds per timed repetition.
    pub raw_elapsed_ns: Vec<u64>,
    /// Mean elapsed nanoseconds per timed repetition.
    pub mean_elapsed_ns: Option<f64>,
    /// Standard deviation of elapsed nanoseconds across repetitions.
    pub stddev_elapsed_ns: Option<f64>,
    /// Mean logical operation throughput per microsecond.
    pub mean_throughput_per_us: Option<f64>,
    /// Standard deviation of logical operation throughput per microsecond.
    pub stddev_throughput_per_us: Option<f64>,
    /// Coefficient of variation for throughput, when measured.
    pub coefficient_of_variation: Option<f64>,
    /// Deterministic checksum accumulated across measured repetitions.
    pub checksum: u64,
    /// Human-readable status detail.
    pub message: String,
}

/// Backend readiness row.
#[derive(Clone, Debug, Serialize)]
pub struct BackendReadinessRow {
    /// Backend variant.
    pub variant: String,
    /// Adapter family.
    pub backend_kind: &'static str,
    /// Deterministic readiness status.
    pub status: &'static str,
    /// Stable machine-readable error code, when execution is unavailable.
    pub error_code: Option<&'static str>,
    /// Human-readable status detail.
    pub message: String,
    /// ay reference discovery state, only set for the ay backend.
    pub ay_reference: Option<AYReferenceBackendState>,
    /// Trust Codegen backend probe state, only set for Trust Codegen variants when requested.
    pub trust_cg_probe: Option<TrustCgBackendProbeRow>,
    /// Real Trust Codegen O2/O3 backend state, only set for Trust Codegen variants when requested.
    pub trust_cg_backend: Option<TrustCgBackendExecutionRow>,
}

/// Deterministic correctness row for a backend adapter.
#[derive(Clone, Debug, Serialize)]
pub struct CorrectnessBackendRow {
    /// Backend variant.
    pub variant: String,
    /// Adapter family.
    pub backend_kind: &'static str,
    /// Deterministic adapter status.
    pub status: &'static str,
    /// Stable machine-readable error code, when unavailable.
    pub error_code: Option<&'static str>,
    /// Number of containment mismatches against the fixture oracle.
    pub contains_mismatch_count: usize,
    /// Number of subsumption mismatches against the fixture oracle.
    pub subsumption_mismatch_count: usize,
    /// ay requested-revision source SHA256, when inspectable.
    pub source_sha256: Option<String>,
    /// Human-readable status detail.
    pub message: String,
}

/// Optional Trust Codegen backend probe artifact.
#[derive(Clone, Debug, Serialize)]
pub struct TrustCgBackendProbeReport {
    /// Artifact schema.
    pub schema: &'static str,
    /// Aggregate probe status.
    pub status: &'static str,
    /// Probe implementation family.
    pub probe_kind: &'static str,
    /// Phase 7/8 promotion disposition for this raw probe artifact.
    pub promotion_disposition: &'static str,
    /// Whether this raw probe artifact is installable product evidence.
    pub product_install_evidence: bool,
    /// Host architecture that produced this artifact.
    pub host_arch: &'static str,
    /// Host OS that produced this artifact.
    pub host_os: &'static str,
    /// One row per requested Trust Codegen variant.
    pub rows: Vec<TrustCgBackendProbeRow>,
    /// Why this is not final #571 acceptance evidence.
    pub note: &'static str,
}

/// One Trust Codegen backend probe row.
#[derive(Clone, Debug, Serialize)]
pub struct TrustCgBackendProbeRow {
    /// Backend variant from the #571 matrix.
    pub variant: String,
    /// Adapter family.
    pub backend_kind: &'static str,
    /// Phase 7/8 promotion disposition for this raw probe row.
    pub promotion_disposition: &'static str,
    /// Whether this raw probe row is installable product evidence.
    pub product_install_evidence: bool,
    /// Trust Codegen optimization level requested for this variant.
    pub opt_level: &'static str,
    /// Vectorizer mode requested by this variant.
    pub vectorizer_mode: &'static str,
    /// Probe status.
    pub status: &'static str,
    /// Stable machine-readable error code, when unavailable or incomplete.
    pub error_code: Option<&'static str>,
    /// Probe function symbol.
    pub function_name: &'static str,
    /// Number of fixture cases checked by the probe.
    pub checked_cases: usize,
    /// Number of padded 4-lane chunk mismatches found by the probe.
    pub chunk_mismatch_count: usize,
    /// Number of fixture containment queries checked by the probe.
    pub contains_query_count: usize,
    /// Number of fixture containment mismatches found by the probe.
    pub contains_mismatch_count: usize,
    /// Number of fixture subsumption pairs checked by the probe.
    pub subsumption_pair_count: usize,
    /// Number of fixture subsumption mismatches found by the probe.
    pub subsumption_mismatch_count: usize,
    /// Correctness mismatches found by the probe.
    pub mismatches: Vec<TrustCgBackendProbeMismatch>,
    /// Probe-only operation timings over the deterministic fixture workload.
    pub operation_measurements: Vec<TrustCgProbeOperationMeasurement>,
    /// Number of timed JIT calls, when the probe executed.
    pub timed_calls: usize,
    /// Elapsed time for the timed calls, when the probe executed.
    pub elapsed_ns: Option<u64>,
    /// Calls per microsecond for the probe, when the probe executed.
    pub calls_per_us: Option<f64>,
    /// Human-readable status detail.
    pub message: String,
}

/// One measured Trust Codegen probe operation row.
#[derive(Clone, Debug, Serialize)]
pub struct TrustCgProbeOperationMeasurement {
    /// Operation under measurement.
    pub operation: &'static str,
    /// Workload bucket covered by this bounded probe measurement.
    pub workload_bucket: String,
    /// Measurement status.
    pub status: &'static str,
    /// Phase 7/8 promotion disposition for this raw probe measurement.
    pub promotion_disposition: &'static str,
    /// Warmup iterations run before timing.
    pub warmup_iterations: usize,
    /// Number of timed repetitions.
    pub measurement_repetitions: usize,
    /// Number of fixture batches per timed repetition.
    pub batches_per_repetition: usize,
    /// Logical operation items per fixture batch.
    pub items_per_batch: usize,
    /// Total timed logical operation items.
    pub total_items: usize,
    /// Raw elapsed nanoseconds per timed repetition.
    pub raw_elapsed_ns: Vec<u64>,
    /// Mean elapsed nanoseconds per timed repetition.
    pub mean_elapsed_ns: Option<f64>,
    /// Standard deviation of elapsed nanoseconds across repetitions.
    pub stddev_elapsed_ns: Option<f64>,
    /// Mean logical operation throughput per microsecond.
    pub mean_throughput_per_us: Option<f64>,
    /// Standard deviation of logical operation throughput per microsecond.
    pub stddev_throughput_per_us: Option<f64>,
    /// Coefficient of variation for throughput, when measured.
    pub coefficient_of_variation: Option<f64>,
    /// Deterministic checksum accumulated across measured repetitions.
    pub checksum: u64,
    /// Human-readable status detail.
    pub message: String,
}

/// Optional real Trust Codegen O2/O3 backend execution artifact.
#[derive(Clone, Debug, Serialize)]
pub struct TrustCgBackendExecutionReport {
    /// Artifact schema.
    pub schema: &'static str,
    /// Aggregate backend execution status.
    pub status: &'static str,
    /// Backend implementation family.
    pub backend_kind: &'static str,
    /// Host architecture that produced this artifact.
    pub host_arch: &'static str,
    /// Host OS that produced this artifact.
    pub host_os: &'static str,
    /// One row per requested Trust Codegen variant.
    pub rows: Vec<TrustCgBackendExecutionRow>,
    /// Direct vectorized-vs-scalar-control correctness comparisons.
    pub scalar_control_comparisons: Vec<TrustCgContains4ScalarControlComparison>,
    /// Measured vectorized-vs-scalar-control throughput comparisons.
    pub profitability_comparisons: Vec<TrustCgBackendProfitabilityComparison>,
    /// Why this is not final #571 acceptance evidence.
    pub note: &'static str,
}

/// One real Trust Codegen O2/O3 backend execution row.
#[derive(Clone, Debug, Serialize)]
pub struct TrustCgBackendExecutionRow {
    /// Backend variant from the #571 matrix.
    pub variant: String,
    /// Adapter family.
    pub backend_kind: &'static str,
    /// Trust Codegen optimization level requested for this variant.
    pub opt_level: &'static str,
    /// Vectorizer mode requested by this variant.
    pub vectorizer_mode: &'static str,
    /// Effective `TRUST_CG_DISABLE_PASSES` override used while preparing IR.
    pub disabled_passes: Option<&'static str>,
    /// Structural contains4 lowering shape after Trust Codegen pipeline preparation.
    pub contains4_backend_shape: &'static str,
    /// Backend status.
    pub status: &'static str,
    /// Stable machine-readable error code, when unavailable or incomplete.
    pub error_code: Option<&'static str>,
    /// Backend function symbol.
    pub function_name: &'static str,
    /// Number of fixture cases checked by the backend.
    pub checked_cases: usize,
    /// Number of padded 4-lane chunk mismatches found by the backend.
    pub chunk_mismatch_count: usize,
    /// Number of fixture containment queries checked by the backend.
    pub contains_query_count: usize,
    /// Number of fixture containment mismatches found by the backend.
    pub contains_mismatch_count: usize,
    /// Number of fixture subsumption pairs checked by the backend.
    pub subsumption_pair_count: usize,
    /// Number of fixture subsumption mismatches found by the backend.
    pub subsumption_mismatch_count: usize,
    /// Correctness mismatches found by the backend.
    pub mismatches: Vec<TrustCgBackendProbeMismatch>,
    /// Operation timings over explicitly requested numeric length buckets.
    pub operation_measurements: Vec<TrustCgBackendOperationMeasurement>,
    /// Human-readable status detail.
    pub message: String,
}

/// One measured real Trust Codegen O2/O3 backend operation row.
#[derive(Clone, Debug, Serialize)]
pub struct TrustCgBackendOperationMeasurement {
    /// Operation under measurement.
    pub operation: &'static str,
    /// Workload bucket covered by this bounded backend measurement.
    pub workload_bucket: String,
    /// Measurement status.
    pub status: &'static str,
    /// Warmup iterations run before timing.
    pub warmup_iterations: usize,
    /// Number of timed repetitions.
    pub measurement_repetitions: usize,
    /// Number of fixture batches per timed repetition.
    pub batches_per_repetition: usize,
    /// Logical operation items per fixture batch.
    pub items_per_batch: usize,
    /// Total timed logical operation items.
    pub total_items: usize,
    /// Raw elapsed nanoseconds per timed repetition.
    pub raw_elapsed_ns: Vec<u64>,
    /// Mean elapsed nanoseconds per timed repetition.
    pub mean_elapsed_ns: Option<f64>,
    /// Standard deviation of elapsed nanoseconds across repetitions.
    pub stddev_elapsed_ns: Option<f64>,
    /// Mean logical operation throughput per microsecond.
    pub mean_throughput_per_us: Option<f64>,
    /// Standard deviation of logical operation throughput per microsecond.
    pub stddev_throughput_per_us: Option<f64>,
    /// Coefficient of variation for throughput, when measured.
    pub coefficient_of_variation: Option<f64>,
    /// Deterministic checksum accumulated across measured repetitions.
    pub checksum: u64,
    /// Human-readable status detail.
    pub message: String,
}

/// Direct masked contains4 comparison between a vectorized row and scalar control.
#[derive(Clone, Debug, Serialize)]
pub struct TrustCgContains4ScalarControlComparison {
    /// Vectorized backend variant.
    pub vectorized_variant: String,
    /// Scalar-control backend variant.
    pub scalar_control_variant: String,
    /// Trust Codegen optimization level shared by the pair.
    pub opt_level: &'static str,
    /// Comparison status.
    pub status: &'static str,
    /// Stable machine-readable error code, when unavailable.
    pub error_code: Option<&'static str>,
    /// Number of direct primitive cases checked.
    pub checked_cases: usize,
    /// Number of vectorized/scalar-control/expected mismatches.
    pub mismatch_count: usize,
    /// Detailed mismatches, if any.
    pub mismatches: Vec<TrustCgContains4ScalarControlMismatch>,
    /// Human-readable status detail.
    pub message: String,
}

/// One direct masked contains4 vectorized-vs-scalar-control mismatch.
#[derive(Clone, Debug, Serialize)]
pub struct TrustCgContains4ScalarControlMismatch {
    /// Case index in the deterministic direct-comparison matrix.
    pub case_index: usize,
    /// Four lanes passed to the primitive.
    pub lanes: [i32; 4],
    /// Valid-lane mask passed to the primitive.
    pub valid_mask: u8,
    /// Literal passed to the primitive.
    pub literal: i32,
    /// Scalar-oracle expected mask.
    pub expected_mask: i32,
    /// Mask returned by the vectorized backend.
    pub vectorized_mask: i32,
    /// Mask returned by the scalar-control backend.
    pub scalar_control_mask: i32,
}

/// One measured vectorized-vs-scalar-control profitability comparison.
#[derive(Clone, Debug, Serialize)]
pub struct TrustCgBackendProfitabilityComparison {
    /// Operation under measurement.
    pub operation: &'static str,
    /// Workload bucket covered by the measurement.
    pub workload_bucket: String,
    /// Vectorized backend variant.
    pub vectorized_variant: String,
    /// Scalar-control backend variant.
    pub scalar_control_variant: String,
    /// Mean vectorized throughput per microsecond.
    pub vectorized_mean_throughput_per_us: Option<f64>,
    /// Mean scalar-control throughput per microsecond.
    pub scalar_control_mean_throughput_per_us: Option<f64>,
    /// Vectorized throughput divided by scalar-control throughput, when measured.
    pub scalar_speedup: Option<f64>,
    /// Comparison status.
    pub status: &'static str,
    /// Human-readable status detail.
    pub message: String,
}

/// One Trust Codegen backend probe mismatch.
#[derive(Clone, Debug, Serialize)]
pub struct TrustCgBackendProbeMismatch {
    /// Probe operation that found the mismatch.
    pub operation: &'static str,
    /// Clause id under test, when the mismatch is clause-local.
    pub clause_id: Option<usize>,
    /// Subsumption pair A clause id, when applicable.
    pub pair_a: Option<usize>,
    /// Subsumption pair B clause id, when applicable.
    pub pair_b: Option<usize>,
    /// First real/padded lane index in the 4-lane chunk, when applicable.
    pub chunk_start_lane: Option<usize>,
    /// Four padded lanes passed to the JIT primitive, when applicable.
    pub lanes: Option<[i32; 4]>,
    /// Valid-lane bitmask passed to the JIT primitive, when applicable.
    pub valid_mask: Option<u8>,
    /// Literal under test, when applicable.
    pub literal: Option<i32>,
    /// Expected matching clause ids for containment query mismatches.
    pub expected_clause_ids: Option<Vec<usize>>,
    /// Actual matching clause ids for containment query mismatches.
    pub actual_clause_ids: Option<Vec<usize>>,
    /// Expected scalar-oracle boolean result, when applicable.
    pub expected_bool: Option<bool>,
    /// JIT probe boolean result, when applicable.
    pub actual_bool: Option<bool>,
    /// Expected matching-lane bitmask for chunk mismatches.
    pub expected_mask: Option<i32>,
    /// Actual matching-lane bitmask returned by the JIT primitive.
    pub actual_mask: Option<i32>,
}

/// One containment oracle row.
#[derive(Clone, Debug, Serialize)]
pub struct ContainsResult {
    /// Query literal.
    pub literal: i32,
    /// Expected clause ids from fixture.
    pub expected_clause_ids: Vec<usize>,
    /// Scalar-oracle actual clause ids.
    pub actual_clause_ids: Vec<usize>,
    /// Whether expected and actual match.
    pub matched: bool,
    /// Coverage note.
    pub covers: String,
}

/// One subsumption oracle row.
#[derive(Clone, Debug, Serialize)]
pub struct SubsumptionResult {
    /// Candidate subset clause id.
    pub a: usize,
    /// Candidate superset clause id.
    pub b: usize,
    /// Expected result from fixture.
    pub expected: bool,
    /// Scalar-oracle actual result.
    pub actual: bool,
    /// Whether expected and actual match.
    pub matched: bool,
    /// Coverage note.
    pub covers: String,
}

/// Load ay subsumption cases from JSON.
pub fn load_ay_subsumption_cases(path: &Path) -> Result<AYSubsumptionCases> {
    let text = read_to_string_bounded(
        path,
        MAX_AY_SUBSUMPTION_CASES_BYTES,
        "ay subsumption cases file",
    )?;
    serde_json::from_str(&text).with_context(|| format!("parsing cases file {}", path.display()))
}

fn read_to_string_bounded(path: &Path, limit: u64, kind: &str) -> Result<String> {
    let size = fs::metadata(path)
        .with_context(|| format!("statting {kind} {}", path.display()))?
        .len();
    if size > limit {
        bail!(
            "{kind} {} is {} byte(s), over limit {}",
            path.display(),
            size,
            limit
        );
    }

    let file = fs::File::open(path).with_context(|| format!("reading {}", path.display()))?;
    let mut text = String::with_capacity(size as usize);
    let mut bounded = file.take(limit + 1);
    bounded
        .read_to_string(&mut text)
        .with_context(|| format!("reading {}", path.display()))?;
    if text.len() as u64 > limit {
        bail!(
            "{kind} {} grew over limit {} while reading",
            path.display(),
            limit
        );
    }
    Ok(text)
}

/// Validate the fixture and return the deterministic scalar correctness report.
pub fn validate_ay_subsumption_cases(cases: &AYSubsumptionCases) -> Result<CorrectnessReport> {
    if cases.issue != 571 {
        bail!("expected issue 571 workload, found issue {}", cases.issue);
    }
    if cases.sentinel != i32::MAX {
        bail!("expected i32::MAX sentinel, found {}", cases.sentinel);
    }
    if cases.clauses.is_empty() {
        bail!("workload has no clauses");
    }

    let mut ids = BTreeSet::new();
    let mut by_id = BTreeMap::new();
    let mut real_literal_lanes = 0usize;
    let mut padded_literal_lanes = 0usize;
    for clause in &cases.clauses {
        if !ids.insert(clause.id) {
            bail!("duplicate clause id {}", clause.id);
        }
        if clause.length != clause.lits.len() {
            bail!(
                "clause {} length {} does not match {} literals",
                clause.id,
                clause.length,
                clause.lits.len()
            );
        }
        if clause.padded_length < clause.length || clause.padded_length % 4 != 0 {
            bail!(
                "clause {} has invalid padded length {} for real length {}",
                clause.id,
                clause.padded_length,
                clause.length
            );
        }
        if clause.lits.contains(&cases.sentinel) {
            bail!("clause {} includes sentinel as a real literal", clause.id);
        }
        real_literal_lanes += clause.length;
        padded_literal_lanes += clause.padded_length;
        by_id.insert(clause.id, clause);
    }

    let covered_lengths: BTreeSet<usize> =
        cases.clauses.iter().map(|clause| clause.length).collect();
    for length in &cases.clause_lengths {
        if !covered_lengths.contains(length) {
            bail!("declared clause length {length} has no fixture clause");
        }
    }

    let contains = cases
        .contains_queries
        .iter()
        .map(|query| {
            let actual_clause_ids = find_clauses_containing(&cases.clauses, query.literal);
            let matched = actual_clause_ids == query.expected_clause_ids;
            ContainsResult {
                literal: query.literal,
                expected_clause_ids: query.expected_clause_ids.clone(),
                actual_clause_ids,
                matched,
                covers: query.covers.clone(),
            }
        })
        .collect::<Vec<_>>();

    let subsumption = cases
        .subsumption_pairs
        .iter()
        .map(|pair| {
            let a = by_id.get(&pair.a).with_context(|| {
                format!("subsumption pair references missing clause {}", pair.a)
            })?;
            let b = by_id.get(&pair.b).with_context(|| {
                format!("subsumption pair references missing clause {}", pair.b)
            })?;
            let actual = clause_subsumes(a, b);
            Ok(SubsumptionResult {
                a: pair.a,
                b: pair.b,
                expected: pair.expected,
                actual,
                matched: actual == pair.expected,
                covers: pair.covers.clone(),
            })
        })
        .collect::<Result<Vec<_>>>()?;

    let mismatch_count = contains.iter().filter(|row| !row.matched).count()
        + subsumption.iter().filter(|row| !row.matched).count();

    Ok(CorrectnessReport {
        schema: "trust-cg.ay_subsumption.correctness_plan.v1",
        workload: WorkloadSummary {
            name: cases.name.clone(),
            issue: cases.issue,
            clause_count: cases.clauses.len(),
            real_literal_lanes,
            padded_literal_lanes,
            contains_query_count: cases.contains_queries.len(),
            subsumption_pair_count: cases.subsumption_pairs.len(),
            length_buckets: cases.benchmark_matrix.length_buckets.clone(),
            variants: cases.benchmark_matrix.variants.clone(),
            warmup_iterations: cases.benchmark_matrix.warmup_iterations,
            measurement_repetitions: cases.benchmark_matrix.measurement_repetitions,
        },
        contains,
        subsumption,
        backend_rows: Vec::new(),
        mismatch_count,
        status: if mismatch_count == 0 {
            "fixture_oracle_pass"
        } else {
            "fixture_oracle_fail"
        },
        note: "This checks the deterministic fixture against a scalar oracle only; it is not Apple Silicon ay NEON versus Trust Codegen throughput evidence.",
    })
}

/// Build the throughput result schema for the configured ay subsumption matrix.
pub fn planned_ay_subsumption_throughput(
    correctness: &CorrectnessReport,
) -> ThroughputSummaryReport {
    planned_ay_subsumption_throughput_with_ay_reference(correctness, None)
}

/// Build the throughput result schema and attach optional ay reference rows.
pub fn planned_ay_subsumption_throughput_with_ay_reference(
    correctness: &CorrectnessReport,
    ay_execution: Option<&AYReferenceExecutionReport>,
) -> ThroughputSummaryReport {
    planned_ay_subsumption_throughput_with_backend_execution(correctness, ay_execution, None, false)
}

/// Build the throughput result schema and attach optional bounded execution rows.
pub fn planned_ay_subsumption_throughput_with_backend_execution(
    correctness: &CorrectnessReport,
    ay_execution: Option<&AYReferenceExecutionReport>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
    include_trust_cg_mixed_rows: bool,
) -> ThroughputSummaryReport {
    planned_ay_subsumption_throughput_with_probe_buckets(
        correctness,
        ay_execution,
        trust_cg_probe,
        include_trust_cg_mixed_rows,
        &[],
    )
}

/// Return numeric ay length bucket labels from the fixture matrix in fixture order.
pub fn ay_numeric_length_buckets(length_buckets: &[String]) -> Vec<String> {
    length_buckets
        .iter()
        .filter(|bucket| bucket.parse::<usize>().is_ok())
        .cloned()
        .collect()
}

/// Build the throughput result schema and attach optional bounded probe buckets.
pub fn planned_ay_subsumption_throughput_with_probe_buckets(
    correctness: &CorrectnessReport,
    ay_execution: Option<&AYReferenceExecutionReport>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
    include_trust_cg_mixed_rows: bool,
    trust_cg_probe_length_buckets: &[String],
) -> ThroughputSummaryReport {
    planned_ay_subsumption_throughput_with_backend_buckets(
        correctness,
        ay_execution,
        trust_cg_probe,
        include_trust_cg_mixed_rows,
        trust_cg_probe_length_buckets,
        None,
        &[],
    )
}

/// Build the throughput result schema and attach optional real backend buckets.
pub fn planned_ay_subsumption_throughput_with_backend_buckets(
    correctness: &CorrectnessReport,
    ay_execution: Option<&AYReferenceExecutionReport>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
    include_trust_cg_mixed_rows: bool,
    trust_cg_probe_length_buckets: &[String],
    trust_cg_backend: Option<&TrustCgBackendExecutionReport>,
    trust_cg_backend_length_buckets: &[String],
) -> ThroughputSummaryReport {
    let mut rows = Vec::new();
    for operation in ["contains_literal", "batch_subsumption"] {
        for length_bucket in &correctness.workload.length_buckets {
            for variant in &correctness.workload.variants {
                let ay_measurement = ay_execution.and_then(|execution| {
                    ay_reference_measurement_for_row(execution, operation, length_bucket, variant)
                });
                let trust_cg_measurement = trust_cg_probe.and_then(|probe| {
                    trust_cg_probe_measurement_for_row(
                        probe,
                        operation,
                        length_bucket,
                        variant,
                        include_trust_cg_mixed_rows,
                        trust_cg_probe_length_buckets,
                    )
                });
                let trust_cg_backend_measurement = trust_cg_backend.and_then(|backend| {
                    trust_cg_backend_measurement_for_row(
                        backend,
                        operation,
                        length_bucket,
                        variant,
                        trust_cg_backend_length_buckets,
                    )
                });
                let ay_reference_throughput = ay_execution.and_then(|execution| {
                    ay_reference_throughput_for_row(execution, operation, length_bucket)
                });
                let status = if let Some(measurement) = ay_measurement {
                    measurement.status
                } else if trust_cg_backend_measurement.is_some() {
                    trust_cg_backend_throughput_status_for_bucket(length_bucket)
                } else if trust_cg_measurement.is_some() {
                    trust_cg_probe_throughput_status_for_bucket(length_bucket)
                } else {
                    "pending_backend"
                };
                let (promotion_disposition, product_install_evidence) = if ay_measurement.is_some()
                {
                    (TRUST_CG_REFERENCE_PROMOTION_DISPOSITION, false)
                } else if trust_cg_backend_measurement.is_some() {
                    trust_cg_backend_row_evidence_disposition(variant)
                } else if trust_cg_measurement.is_some() {
                    (TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION, false)
                } else {
                    (TRUST_CG_PENDING_PROMOTION_DISPOSITION, false)
                };
                rows.push(ThroughputSummaryRow {
                    operation,
                    length_bucket: length_bucket.clone(),
                    variant: variant.clone(),
                    warmup_iterations: correctness.workload.warmup_iterations,
                    measurement_repetitions: correctness.workload.measurement_repetitions,
                    status,
                    promotion_disposition,
                    product_install_evidence,
                    mean_throughput_per_us: ay_measurement
                        .and_then(|measurement| measurement.mean_throughput_per_us),
                    stddev_throughput_per_us: ay_measurement
                        .and_then(|measurement| measurement.stddev_throughput_per_us)
                        .or_else(|| {
                            trust_cg_backend_measurement
                                .and_then(|measurement| measurement.stddev_throughput_per_us)
                        })
                        .or_else(|| {
                            trust_cg_measurement
                                .and_then(|measurement| measurement.stddev_throughput_per_us)
                        }),
                    coefficient_of_variation: ay_measurement
                        .and_then(|measurement| measurement.coefficient_of_variation)
                        .or_else(|| {
                            trust_cg_backend_measurement
                                .and_then(|measurement| measurement.coefficient_of_variation)
                        })
                        .or_else(|| {
                            trust_cg_measurement
                                .and_then(|measurement| measurement.coefficient_of_variation)
                        }),
                    ay_relative_ratio: if ay_measurement.is_some() {
                        Some(1.0)
                    } else {
                        let trust_cg_mean = trust_cg_backend_measurement
                            .and_then(|measurement| measurement.mean_throughput_per_us)
                            .or_else(|| {
                                trust_cg_measurement
                                    .and_then(|measurement| measurement.mean_throughput_per_us)
                            });
                        match (trust_cg_mean, ay_reference_throughput) {
                            (Some(trust_cg), Some(ay)) if ay != 0.0 => Some(trust_cg / ay),
                            _ => None,
                        }
                    },
                    scalar_speedup: None,
                });
                if let Some(trust_cg_measurement) = trust_cg_measurement {
                    let row = rows.last_mut().expect("row was just pushed");
                    row.mean_throughput_per_us = trust_cg_measurement.mean_throughput_per_us;
                }
                if let Some(trust_cg_backend_measurement) = trust_cg_backend_measurement {
                    let row = rows.last_mut().expect("row was just pushed");
                    row.mean_throughput_per_us =
                        trust_cg_backend_measurement.mean_throughput_per_us;
                }
            }
        }
    }
    attach_trust_cg_scalar_speedups(&mut rows);
    let measured_ay_rows = rows
        .iter()
        .filter(|row| row.variant == "ay_neon_reference" && row.status == "ay_reference_measured")
        .count();
    let measured_trust_cg_mixed_rows = rows
        .iter()
        .filter(|row| row.status == TRUST_CG_PROBE_MIXED_ROW_STATUS)
        .count();
    let measured_trust_cg_bucket_rows = rows
        .iter()
        .filter(|row| row.status == TRUST_CG_PROBE_BUCKET_ROW_STATUS)
        .count();
    let measured_trust_cg_backend_rows = rows
        .iter()
        .filter(|row| is_trust_cg_backend_throughput_status(row.status))
        .count();
    let pending_backend_rows = rows
        .iter()
        .filter(|row| row.status == "pending_backend")
        .count();
    let gate = throughput_gate_for_rows(&rows, &correctness.workload.length_buckets);
    let status = throughput_summary_status(
        measured_ay_rows > 0,
        measured_trust_cg_mixed_rows > 0,
        measured_trust_cg_bucket_rows > 0,
        measured_trust_cg_backend_rows > 0,
        pending_backend_rows,
    );
    let note = if gate.passed.is_some() {
        "Throughput rows are complete and the Trust Codegen/ay recommendation gate has been evaluated from measured ay NEON and Trust Codegen O2/O3 backend rows. This artifact is still evidence for #571 review rather than manager acceptance."
    } else {
        "Throughput rows remain incomplete until ay NEON and Trust Codegen execution backends populate the full matrix. Optional mixed/numeric ay reference rows, Trust Codegen raw-JIT probe rows, and bounded real Trust Codegen O2/O3 pipeline rows are partial evidence only; the Trust Codegen/ay gate remains unset."
    };

    ThroughputSummaryReport {
        schema: "trust-cg.ay_subsumption.throughput_summary.v1",
        status,
        workload: correctness.workload.clone(),
        row_accounting: ThroughputRowAccounting {
            planned_rows: rows.len(),
            measured_ay_reference_rows: measured_ay_rows,
            measured_trust_cg_mixed_probe_rows: measured_trust_cg_mixed_rows,
            measured_trust_cg_bucket_probe_rows: measured_trust_cg_bucket_rows,
            measured_trust_cg_backend_rows,
            pending_backend_rows,
        },
        rows,
        gate,
        note,
    }
}

/// Derive Phase 8 ay native-promotion counters from correctness and throughput reports.
pub fn phase8_ay_subsumption_native_promotion_counters(
    correctness: &CorrectnessReport,
    throughput: &ThroughputSummaryReport,
    counter_scope: Phase8NativePromotionCounterScope,
) -> Phase8NativePromotionCounters {
    let scalar_contains_mismatches = correctness
        .contains
        .iter()
        .filter(|row| !row.matched)
        .count();
    let scalar_subsumption_mismatches = correctness
        .subsumption
        .iter()
        .filter(|row| !row.matched)
        .count();
    let (backend_contains_mismatches, backend_subsumption_mismatches) = correctness
        .backend_rows
        .iter()
        .filter(|row| phase8_executed_correctness_backend_row(row))
        .fold((0usize, 0usize), |(contains, subsumption), row| {
            (
                contains + row.contains_mismatch_count,
                subsumption + row.subsumption_mismatch_count,
            )
        });
    let wrong_answer_count = scalar_contains_mismatches
        + scalar_subsumption_mismatches
        + backend_contains_mismatches
        + backend_subsumption_mismatches;
    let solver_result_mismatch_count =
        scalar_subsumption_mismatches + backend_subsumption_mismatches;
    let backend_status_error_count = correctness
        .backend_rows
        .iter()
        .filter(|row| row.variant.starts_with("trust_cg_") && row.error_code.is_some())
        .count();
    let measured_ay_rows = throughput.row_accounting.measured_ay_reference_rows;
    let measured_backend_rows = throughput.row_accounting.measured_trust_cg_backend_rows;
    let profile_only_probe_rows = throughput.row_accounting.measured_trust_cg_mixed_probe_rows
        + throughput
            .row_accounting
            .measured_trust_cg_bucket_probe_rows;
    let pending_backend_rows = throughput.row_accounting.pending_backend_rows;
    let vectorized_backend_rows = throughput
        .rows
        .iter()
        .filter(|row| phase8_ay_product_backend_row(row))
        .count();
    let complete_backend_gate = throughput.status
        == "complete_ay_reference_and_trust_cg_backend_rows"
        && pending_backend_rows == 0
        && measured_ay_rows > 0
        && measured_backend_rows > 0;
    let throughput_gate_passed = throughput.gate.passed == Some(true);
    let manifest_sha256 = counter_scope
        .manifest_sha256
        .as_deref()
        .map(str::trim)
        .filter(|hash| !hash.is_empty());
    let expected_manifest_sha256 = counter_scope
        .expected_manifest_sha256
        .as_deref()
        .map(str::trim)
        .filter(|hash| !hash.is_empty());
    let manifest_missing_count = usize::from(manifest_sha256.is_none());
    let manifest_hash_mismatch_count = usize::from(matches!(
        (manifest_sha256, expected_manifest_sha256),
        (Some(actual), Some(expected)) if actual != expected
    ));
    let layout_evidence_missing_count =
        usize::from(counter_scope.layout_checksum.trim().is_empty());
    let proof_policy_missing_count =
        usize::from(counter_scope.proof_policy_sha256.trim().is_empty());
    let target_evidence_missing_count = [
        counter_scope.target_triple.trim(),
        counter_scope.target_cpu.trim(),
        counter_scope.target_features_sha256.trim(),
    ]
    .into_iter()
    .filter(|field| field.is_empty())
    .count();

    let mut blockers = Vec::new();
    if manifest_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "manifest_hash_missing",
            manifest_missing_count,
            "Phase 8 promotion manifest SHA256 is missing from the counter scope",
        ));
    }
    if manifest_hash_mismatch_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "manifest_hash_mismatch",
            manifest_hash_mismatch_count,
            "Phase 8 promotion manifest SHA256 does not match the expected bundle or gate reference",
        ));
    }
    if layout_evidence_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "layout_evidence_missing",
            layout_evidence_missing_count,
            "Phase 8 promotion layout checksum is missing from the counter scope",
        ));
    }
    if proof_policy_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "proof_policy_missing",
            proof_policy_missing_count,
            "Phase 8 proof policy checksum is missing from the counter scope",
        ));
    }
    if target_evidence_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "target_evidence_missing",
            target_evidence_missing_count,
            "Phase 8 target triple, CPU, or feature evidence is missing from the counter scope",
        ));
    }
    if wrong_answer_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "ay_correctness_mismatch",
            wrong_answer_count,
            "ay subsumption correctness rows contain scalar or backend mismatches",
        ));
    }
    if pending_backend_rows > 0 {
        blockers.push(phase8_promotion_blocker(
            "throughput_rows_pending",
            pending_backend_rows,
            "throughput matrix still has pending backend rows",
        ));
    }
    if measured_ay_rows == 0 {
        blockers.push(phase8_promotion_blocker(
            "ay_reference_rows_missing",
            1,
            "ay reference throughput rows are missing",
        ));
    }
    if measured_backend_rows == 0 {
        blockers.push(phase8_promotion_blocker(
            "trust_cg_backend_rows_missing",
            1,
            "Trust Codegen O2/O3 backend throughput rows are missing",
        ));
    }
    if !complete_backend_gate {
        blockers.push(phase8_promotion_blocker(
            "throughput_summary_incomplete",
            1,
            "throughput summary is not complete for ay reference and Trust Codegen backend rows",
        ));
    }
    match throughput.gate.passed {
        Some(true) => {}
        Some(false) => blockers.push(phase8_promotion_blocker(
            "throughput_gate_failed",
            1,
            "Trust Codegen vectorized geometric-mean throughput is below the ay-relative gate",
        )),
        None => blockers.push(phase8_promotion_blocker(
            "throughput_gate_not_evaluated",
            1,
            "throughput gate is unset because the complete matrix has not run",
        )),
    }
    if vectorized_backend_rows == 0 || !throughput_gate_passed || wrong_answer_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "native_useful_application_missing",
            1,
            "no correctness-gated useful native Trust Codegen backend rows are promotable",
        ));
    }
    if backend_status_error_count > 0 && measured_backend_rows > 0 {
        blockers.push(phase8_promotion_blocker(
            "native_status_error",
            backend_status_error_count,
            "Trust Codegen backend correctness rows include status errors",
        ));
    }

    let can_promote_beyond_canary = blockers.is_empty();
    let product_authorized_backend_rows = if can_promote_beyond_canary {
        vectorized_backend_rows
    } else {
        0
    };
    let baseline_latency_us = phase8_mean_item_time_us(throughput.rows.iter().filter(|row| {
        row.variant == "ay_neon_reference"
            && row.status == "ay_reference_measured"
            && row.mean_throughput_per_us.is_some()
    }));
    let native_latency_us =
        phase8_mean_item_time_us(throughput.rows.iter().filter(|row| {
            phase8_ay_product_backend_row(row) && row.mean_throughput_per_us.is_some()
        }));

    Phase8NativePromotionCounters {
        schema: PHASE8_NATIVE_PROMOTION_COUNTERS_SCHEMA,
        counter_scope,
        lifecycle: Phase8LifecycleCounters {
            observed_count: throughput.row_accounting.planned_rows,
            nominated_count: vectorized_backend_rows,
            profile_only_compiled_count: profile_only_probe_rows,
            shadow_dispatch_count: 0,
            canary_install_count: product_authorized_backend_rows,
            active_promotion_count: usize::from(can_promote_beyond_canary),
            install_rejected_count: usize::from(!can_promote_beyond_canary),
            invalidated_count: 0,
            rolled_back_count: 0,
            revoked_count: 0,
        },
        artifact_gate: Phase8ArtifactGateCounters {
            manifest_missing_count,
            manifest_hash_mismatch_count,
            abi_mismatch_count: 0,
            layout_mismatch_count: layout_evidence_missing_count,
            target_mismatch_count: target_evidence_missing_count,
            replay_missing_count: 0,
            telemetry_missing_count: 0,
        },
        proof_gate: Phase8ProofGateCounters {
            proof_verified_count: product_authorized_backend_rows,
            proof_missing_count: proof_policy_missing_count,
            proof_failed_count: wrong_answer_count,
            proof_timeout_count: 0,
            proof_unknown_count: 0,
            proof_unsupported_target_count: 0,
            proof_stale_count: 0,
        },
        invalidation_gate: Phase8InvalidationGateCounters {
            fresh_install_count: product_authorized_backend_rows,
            stale_install_reject_count: 0,
            stale_call_reject_count: 0,
            kill_switch_reject_count: 0,
            revoked_artifact_reject_count: 0,
            generation_mismatch_count: 0,
        },
        dispatch: Phase8DispatchCounters {
            eligible_call_count: vectorized_backend_rows,
            native_call_count: product_authorized_backend_rows,
            baseline_call_count: measured_ay_rows,
            useful_native_count: product_authorized_backend_rows,
            fallback_count: pending_backend_rows,
            deopt_count: 0,
            native_status_error_count: backend_status_error_count,
            shadow_mismatch_count: wrong_answer_count,
            crash_count: 0,
            internal_error_count: 0,
        },
        performance: Phase8PerformanceCounters {
            baseline_p50_us: baseline_latency_us,
            baseline_p95_us: baseline_latency_us,
            baseline_p99_us: baseline_latency_us,
            native_p50_us: native_latency_us,
            native_p95_us: native_latency_us,
            native_p99_us: native_latency_us,
            compile_p50_ms: 0.0,
            proof_p50_ms: 0.0,
            code_size_bytes: 0,
            cache_hit_count: 0,
            cache_miss_count: 0,
        },
        consumer: Phase8ConsumerCounters {
            ay: Phase8AYConsumerCounters {
                solver_program_sha256: None,
                solver_semantic_generation: correctness.workload.name.clone(),
                solver_state_hash: None,
                basis_epoch: correctness.workload.issue.to_string(),
                kernel_family: "other_allowlisted".to_string(),
                row_region_sha256: None,
                result_parity: Phase8AYResultParityCounters {
                    solver_result_mismatch_count,
                    witness_mismatch_count: scalar_contains_mismatches
                        + backend_contains_mismatches,
                    proof_regression_count: 0,
                    wrong_answer_count,
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
                    competition_instance_count: correctness.workload.contains_query_count
                        + correctness.workload.subsumption_pair_count,
                    native_useful_application_count: product_authorized_backend_rows,
                    fallback_application_count: pending_backend_rows,
                    profile_only_application_count: profile_only_probe_rows,
                },
            },
        },
        promotion_verdict: Phase8PromotionVerdict {
            can_promote_beyond_canary,
            blockers,
        },
    }
}

/// Derive Phase 8 TY parent-loop native-promotion counters from downstream smoke evidence.
pub fn phase8_ty_parent_loop_native_promotion_counters(
    evidence: &Phase8TyParentLoopEvidence,
    counter_scope: Phase8NativePromotionCounterScope,
) -> Phase8TyNativePromotionCounters {
    let manifest_sha256 = counter_scope
        .manifest_sha256
        .as_deref()
        .map(str::trim)
        .filter(|hash| !hash.is_empty());
    let expected_manifest_sha256 = counter_scope
        .expected_manifest_sha256
        .as_deref()
        .map(str::trim)
        .filter(|hash| !hash.is_empty());
    let manifest_missing_count = usize::from(manifest_sha256.is_none());
    let manifest_hash_mismatch_count = usize::from(matches!(
        (manifest_sha256, expected_manifest_sha256),
        (Some(actual), Some(expected)) if actual != expected
    ));
    let layout_evidence_missing_count =
        usize::from(counter_scope.layout_checksum.trim().is_empty())
            + usize::from(
                evidence
                    .state_layout_sha256
                    .as_deref()
                    .map(str::trim)
                    .filter(|hash| !hash.is_empty())
                    .is_none(),
            );
    let proof_policy_missing_count =
        usize::from(counter_scope.proof_policy_sha256.trim().is_empty())
            + usize::from(
                evidence
                    .transition_cluster_sha256
                    .as_deref()
                    .map(str::trim)
                    .filter(|hash| !hash.is_empty())
                    .is_none(),
            );
    let target_evidence_missing_count = [
        counter_scope.target_triple.trim(),
        counter_scope.target_cpu.trim(),
        counter_scope.target_features_sha256.trim(),
    ]
    .into_iter()
    .filter(|field| field.is_empty())
    .count();
    let action_count_mismatch_count = usize::from(matches!(
        evidence.actual_action_count,
        Some(actual) if actual != evidence.expected_action_count
    ));
    let invariant_count_mismatch_count = usize::from(matches!(
        evidence.actual_invariant_count,
        Some(actual) if actual != evidence.expected_invariant_count
    ));
    let state_constraint_count_mismatch_count = usize::from(matches!(
        evidence.actual_state_constraint_count,
        Some(actual) if actual != evidence.expected_state_constraint_count
    ));
    let state_len_mismatch_count = usize::from(matches!(
        evidence.actual_state_len,
        Some(actual) if actual != evidence.expected_state_len
    ));
    let shape_evidence_missing_count = [
        evidence.actual_action_count.is_none(),
        evidence.actual_invariant_count.is_none(),
        evidence.actual_state_constraint_count.is_none(),
        evidence.actual_state_len.is_none(),
    ]
    .into_iter()
    .filter(|missing| *missing)
    .count();
    let execution_shape_evidence_missing_count = [
        evidence.compiled_bfs_successors_generated == 0,
        evidence.compiled_bfs_successors_new == 0,
        evidence.compiled_bfs_parents_processed == 0,
        evidence.flat_state_copy_bytes == 0,
        evidence.fingerprint_count == 0,
        evidence.fingerprint_bytes == 0,
        evidence.helper_inline_count == 0,
        evidence.alias_readonly_metadata_hit_count == 0,
    ]
    .into_iter()
    .filter(|missing| *missing)
    .count();
    let wrong_answer_count = action_count_mismatch_count
        + invariant_count_mismatch_count
        + state_constraint_count_mismatch_count
        + state_len_mismatch_count
        + evidence.shadow_mismatch_count;
    let missing_replay_count = usize::from(evidence.replay_artifact_count == 0);
    let missing_telemetry_count = usize::from(evidence.telemetry_artifact_count == 0);
    let native_path_missing_count = [
        !evidence.strict_selftest_completed,
        !evidence.native_fused_path_active,
        !evidence.compiled_bfs_level_loop_fused,
        !evidence.native_dispatch_promoted,
    ]
    .into_iter()
    .filter(|missing| *missing)
    .count();
    let downstream_cli_missing_count = usize::from(evidence.downstream_cli_passed.is_none());
    let downstream_cli_failed_count = usize::from(evidence.downstream_cli_passed == Some(false));
    let native_runtime_failure_count = evidence.crash_count
        + evidence.internal_error_count
        + evidence.native_status_error_count
        + evidence.deopt_count;
    let profile_generate_report_missing_count =
        usize::from(!evidence.profile_generate_report.has_identity_or_hash());
    let profile_use_report_present = evidence.profile_use_report.has_identity_or_hash();
    let profile_use_report_missing_count = usize::from(!profile_use_report_present);
    let profile_use_report_stale_count =
        usize::from(profile_use_report_present && evidence.profile_use_report.fresh == Some(false));
    let profile_use_report_not_fresh_count =
        usize::from(profile_use_report_present && evidence.profile_use_report.fresh.is_none());
    let profile_sha256_mismatch_count = usize::from(matches!(
        (
            evidence.profile_generate_report.profile_sha256(),
            evidence.profile_use_report.profile_sha256()
        ),
        (Some(generated), Some(used)) if generated != used
    ));
    let profile_key_mismatch_count = usize::from(matches!(
        (
            evidence.profile_generate_report.profile_key_digest(),
            evidence.profile_use_report.profile_key_digest()
        ),
        (Some(generated), Some(used)) if generated != used
    ));
    let profile_report_binding_mismatch_count =
        profile_sha256_mismatch_count + profile_key_mismatch_count;
    let profile_use_fresh_binding_failure_count = profile_generate_report_missing_count
        + profile_use_report_missing_count
        + profile_use_report_stale_count
        + profile_use_report_not_fresh_count
        + profile_report_binding_mismatch_count;

    let mut blockers = Vec::new();
    if manifest_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "manifest_hash_missing",
            manifest_missing_count,
            "Phase 8 promotion manifest SHA256 is missing from the counter scope",
        ));
    }
    if manifest_hash_mismatch_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "manifest_hash_mismatch",
            manifest_hash_mismatch_count,
            "Phase 8 promotion manifest SHA256 does not match the expected bundle or gate reference",
        ));
    }
    if layout_evidence_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "layout_evidence_missing",
            layout_evidence_missing_count,
            "TY state layout evidence or Phase 8 layout checksum is missing",
        ));
    }
    if proof_policy_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "proof_policy_missing",
            proof_policy_missing_count,
            "TY transition-cluster evidence or Phase 8 proof policy checksum is missing",
        ));
    }
    if target_evidence_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "target_evidence_missing",
            target_evidence_missing_count,
            "Phase 8 target triple, CPU, or feature evidence is missing from the counter scope",
        ));
    }
    if profile_generate_report_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "profile_generate_report_missing",
            profile_generate_report_missing_count,
            "TY profile-generate report identity or hash is missing",
        ));
    }
    if profile_use_report_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "profile_use_report_missing",
            profile_use_report_missing_count,
            "TY profile-use report identity or hash is missing",
        ));
    }
    if profile_use_report_stale_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "profile_use_report_stale",
            profile_use_report_stale_count,
            "TY profile-use report marked the profdata stale",
        ));
    }
    if profile_use_report_not_fresh_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "profile_use_report_not_marked_fresh",
            profile_use_report_not_fresh_count,
            "TY profile-use report did not mark the profdata fresh",
        ));
    }
    if profile_report_binding_mismatch_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "profile_report_binding_mismatch",
            profile_report_binding_mismatch_count,
            "TY profile-generate and profile-use report bindings do not match",
        ));
    }
    if downstream_cli_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "downstream_cli_verdict_missing",
            downstream_cli_missing_count,
            "TY downstream CLI verdict is missing",
        ));
    }
    if downstream_cli_failed_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "downstream_cli_failed",
            downstream_cli_failed_count,
            "TY downstream CLI verdict failed",
        ));
    }
    if shape_evidence_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "ty_shape_evidence_missing",
            shape_evidence_missing_count,
            "TY action, invariant, state-constraint, or state-length evidence is missing",
        ));
    }
    if wrong_answer_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "ty_semantic_mismatch",
            wrong_answer_count,
            "TY downstream shape or shadow-dispatch evidence contains mismatches",
        ));
    }
    if execution_shape_evidence_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "ty_execution_shape_evidence_missing",
            execution_shape_evidence_missing_count,
            "TY flat-state copy, fingerprint, helper-inline, or alias/readonly evidence is missing",
        ));
    }
    if native_path_missing_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "ty_native_path_missing",
            native_path_missing_count,
            "TY strict selftest, native-fused path, compiled BFS marker, or dispatch promotion is missing",
        ));
    }
    if evidence.non_promoting {
        blockers.push(phase8_promotion_blocker(
            "ty_non_promoting_artifact",
            1,
            "TY downstream artifact explicitly marked the run non-promoting",
        ));
    }
    if missing_replay_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "replay_artifact_missing",
            missing_replay_count,
            "TY replay artifacts are missing",
        ));
    }
    if missing_telemetry_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "telemetry_artifact_missing",
            missing_telemetry_count,
            "TY telemetry artifacts are missing",
        ));
    }
    if native_runtime_failure_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "native_runtime_failure",
            native_runtime_failure_count,
            "TY native dispatch reported a crash, deopt, status error, or internal error",
        ));
    }
    if evidence.fallback_count > 0 {
        blockers.push(phase8_promotion_blocker(
            "fallback_observed",
            evidence.fallback_count,
            "TY fallback dispatch was observed and cannot count as useful native work",
        ));
    }
    if evidence.useful_native_call_count == 0 {
        blockers.push(phase8_promotion_blocker(
            "native_useful_application_missing",
            1,
            "no correctness-gated useful native TY calls are promotable",
        ));
    }

    let can_promote_beyond_canary = blockers.is_empty();
    let useful_native_count = if can_promote_beyond_canary {
        evidence.useful_native_call_count
    } else {
        0
    };
    let canary_install_count = if downstream_cli_failed_count == 0
        && wrong_answer_count == 0
        && native_runtime_failure_count == 0
        && profile_use_fresh_binding_failure_count == 0
        && evidence.native_call_count > 0
    {
        1
    } else {
        0
    };

    Phase8TyNativePromotionCounters {
        schema: PHASE8_NATIVE_PROMOTION_COUNTERS_SCHEMA,
        counter_scope,
        lifecycle: Phase8LifecycleCounters {
            observed_count: 1,
            nominated_count: evidence.eligible_native_call_count,
            profile_only_compiled_count: 0,
            shadow_dispatch_count: evidence.shadow_mismatch_count,
            canary_install_count,
            active_promotion_count: usize::from(can_promote_beyond_canary),
            install_rejected_count: usize::from(!can_promote_beyond_canary),
            invalidated_count: 0,
            rolled_back_count: 0,
            revoked_count: 0,
        },
        artifact_gate: Phase8ArtifactGateCounters {
            manifest_missing_count,
            manifest_hash_mismatch_count,
            abi_mismatch_count: 0,
            layout_mismatch_count: layout_evidence_missing_count
                + shape_evidence_missing_count
                + execution_shape_evidence_missing_count,
            target_mismatch_count: target_evidence_missing_count,
            replay_missing_count: missing_replay_count,
            telemetry_missing_count: missing_telemetry_count,
        },
        proof_gate: Phase8ProofGateCounters {
            proof_verified_count: usize::from(can_promote_beyond_canary),
            proof_missing_count: proof_policy_missing_count
                + downstream_cli_missing_count
                + profile_generate_report_missing_count
                + profile_use_report_missing_count
                + profile_use_report_not_fresh_count
                + execution_shape_evidence_missing_count,
            proof_failed_count: wrong_answer_count + downstream_cli_failed_count,
            proof_timeout_count: 0,
            proof_unknown_count: usize::from(evidence.downstream_cli_passed.is_none()),
            proof_unsupported_target_count: 0,
            proof_stale_count: profile_use_report_stale_count
                + profile_report_binding_mismatch_count,
        },
        invalidation_gate: Phase8InvalidationGateCounters {
            fresh_install_count: canary_install_count,
            stale_install_reject_count: profile_use_report_stale_count
                + profile_report_binding_mismatch_count,
            stale_call_reject_count: profile_use_report_not_fresh_count,
            kill_switch_reject_count: 0,
            revoked_artifact_reject_count: 0,
            generation_mismatch_count: profile_report_binding_mismatch_count,
        },
        dispatch: Phase8DispatchCounters {
            eligible_call_count: evidence.eligible_native_call_count,
            native_call_count: evidence.native_call_count,
            baseline_call_count: evidence.baseline_call_count,
            useful_native_count,
            fallback_count: evidence.fallback_count,
            deopt_count: evidence.deopt_count,
            native_status_error_count: evidence.native_status_error_count,
            shadow_mismatch_count: evidence.shadow_mismatch_count,
            crash_count: evidence.crash_count,
            internal_error_count: evidence.internal_error_count,
        },
        performance: Phase8PerformanceCounters {
            baseline_p50_us: 0.0,
            baseline_p95_us: 0.0,
            baseline_p99_us: 0.0,
            native_p50_us: 0.0,
            native_p95_us: 0.0,
            native_p99_us: 0.0,
            compile_p50_ms: 0.0,
            proof_p50_ms: 0.0,
            code_size_bytes: 0,
            cache_hit_count: evidence.cache_hit_count,
            cache_miss_count: evidence.cache_miss_count,
        },
        consumer: Phase8TyConsumerCounterEnvelope {
            ty: Phase8TyConsumerCounters {
                spec_name: evidence.spec_name.clone(),
                artifact_root: evidence.artifact_root.clone(),
                state_layout_sha256: evidence.state_layout_sha256.clone(),
                transition_cluster_sha256: evidence.transition_cluster_sha256.clone(),
                profile_reports: Phase8TyProfileReportCounters {
                    profile_generate: evidence.profile_generate_report.clone(),
                    profile_use: evidence.profile_use_report.clone(),
                    profile_generate_report_missing_count,
                    profile_use_report_missing_count,
                    profile_use_report_stale_count,
                    profile_use_report_not_fresh_count,
                    profile_report_binding_mismatch_count,
                },
                parity: Phase8TyParityCounters {
                    action_count_mismatch_count,
                    invariant_count_mismatch_count,
                    state_constraint_count_mismatch_count,
                    state_len_mismatch_count,
                    shape_evidence_missing_count,
                    wrong_answer_count,
                },
                execution_shape: Phase8TyExecutionShapeCounters {
                    generated_state_count: evidence.compiled_bfs_successors_generated,
                    distinct_state_count: evidence.compiled_bfs_successors_new,
                    fingerprint_count: evidence.fingerprint_count,
                    parent_index_checked_count: evidence.compiled_bfs_parents_processed,
                    flat_state_copy_bytes: evidence.flat_state_copy_bytes,
                    fingerprint_bytes: evidence.fingerprint_bytes,
                    helper_inline_count: evidence.helper_inline_count,
                    alias_readonly_metadata_hit_count: evidence.alias_readonly_metadata_hit_count,
                    execution_shape_evidence_missing_count,
                },
                native_path: Phase8TyNativePathCounters {
                    strict_selftest_completed_count: usize::from(
                        evidence.strict_selftest_completed,
                    ),
                    native_fused_path_active_count: usize::from(evidence.native_fused_path_active),
                    compiled_bfs_level_loop_fused_count: usize::from(
                        evidence.compiled_bfs_level_loop_fused,
                    ),
                    native_dispatch_promoted_count: usize::from(evidence.native_dispatch_promoted),
                    non_promoting_count: usize::from(evidence.non_promoting),
                    compiled_bfs_levels_completed: evidence.compiled_bfs_levels_completed,
                    compiled_bfs_parents_processed: evidence.compiled_bfs_parents_processed,
                    compiled_bfs_successors_generated: evidence.compiled_bfs_successors_generated,
                    compiled_bfs_successors_new: evidence.compiled_bfs_successors_new,
                    compiled_bfs_total_states: evidence.compiled_bfs_total_states,
                },
                artifacts: Phase8TyArtifactCounters {
                    replay_artifact_count: evidence.replay_artifact_count,
                    telemetry_artifact_count: evidence.telemetry_artifact_count,
                    crash_packet_count: evidence.crash_packet_count,
                },
            },
        },
        promotion_verdict: Phase8PromotionVerdict {
            can_promote_beyond_canary,
            blockers,
        },
    }
}

/// Build the backend-readiness schema for the configured ay subsumption matrix.
pub fn planned_ay_subsumption_backend_readiness(
    correctness: &CorrectnessReport,
    ay_reference: Option<AYReferenceBackendState>,
) -> BackendReadinessReport {
    planned_ay_subsumption_backend_readiness_with_trust_cg_probe(correctness, ay_reference, None)
}

/// Build the backend-readiness schema and attach optional Trust Codegen probe rows.
pub fn planned_ay_subsumption_backend_readiness_with_trust_cg_probe(
    correctness: &CorrectnessReport,
    ay_reference: Option<AYReferenceBackendState>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
) -> BackendReadinessReport {
    planned_ay_subsumption_backend_readiness_with_backend_execution(
        correctness,
        ay_reference,
        trust_cg_probe,
        None,
    )
}

/// Build the backend-readiness schema and attach optional execution rows.
pub fn planned_ay_subsumption_backend_readiness_with_backend_execution(
    correctness: &CorrectnessReport,
    ay_reference: Option<AYReferenceBackendState>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
    ay_execution: Option<&AYReferenceExecutionReport>,
) -> BackendReadinessReport {
    planned_ay_subsumption_backend_readiness_with_full_backend_execution(
        correctness,
        ay_reference,
        trust_cg_probe,
        ay_execution,
        None,
    )
}

/// Build the backend-readiness schema and attach optional real Trust Codegen backend rows.
pub fn planned_ay_subsumption_backend_readiness_with_full_backend_execution(
    correctness: &CorrectnessReport,
    ay_reference: Option<AYReferenceBackendState>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
    ay_execution: Option<&AYReferenceExecutionReport>,
    trust_cg_backend: Option<&TrustCgBackendExecutionReport>,
) -> BackendReadinessReport {
    let rows = correctness
        .workload
        .variants
        .iter()
        .map(|variant| {
            backend_readiness_row(
                variant,
                ay_reference.clone(),
                trust_cg_probe.and_then(|probe| trust_cg_probe_row_for_variant(probe, variant)),
                ay_execution,
                trust_cg_backend
                    .and_then(|backend| trust_cg_backend_row_for_variant(backend, variant)),
            )
        })
        .collect();

    BackendReadinessReport {
        schema: "trust-cg.ay_subsumption.backend_readiness.v1",
        status: backend_artifact_status(
            trust_cg_probe.is_some(),
            ay_execution.is_some(),
            trust_cg_backend.is_some(),
        ),
        workload: correctness.workload.clone(),
        rows,
        note: "The optional ay reference path executes the real ay scanner for bounded rows, the optional Trust Codegen probe exercises a raw-JIT padded 4-lane primitive, and optional Trust Codegen backend rows compile that primitive through the requested O2/O3 pipeline mode. Full O2/O3 throughput matrix execution remains pending.",
    }
}

/// Add deterministic backend correctness rows for the configured matrix.
pub fn ay_subsumption_correctness_with_backend_rows(
    correctness: &CorrectnessReport,
    ay_reference: Option<&AYReferenceBackendState>,
) -> CorrectnessReport {
    ay_subsumption_correctness_with_backend_rows_and_trust_cg_probe(correctness, ay_reference, None)
}

/// Add deterministic backend correctness rows and optional Trust Codegen probe evidence.
pub fn ay_subsumption_correctness_with_backend_rows_and_trust_cg_probe(
    correctness: &CorrectnessReport,
    ay_reference: Option<&AYReferenceBackendState>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
) -> CorrectnessReport {
    ay_subsumption_correctness_with_backend_execution(
        correctness,
        ay_reference,
        trust_cg_probe,
        None,
    )
}

/// Add backend correctness rows and optional bounded execution evidence.
pub fn ay_subsumption_correctness_with_backend_execution(
    correctness: &CorrectnessReport,
    ay_reference: Option<&AYReferenceBackendState>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
    ay_execution: Option<&AYReferenceExecutionReport>,
) -> CorrectnessReport {
    ay_subsumption_correctness_with_full_backend_execution(
        correctness,
        ay_reference,
        trust_cg_probe,
        ay_execution,
        None,
    )
}

/// Add backend correctness rows and optional real Trust Codegen backend execution evidence.
pub fn ay_subsumption_correctness_with_full_backend_execution(
    correctness: &CorrectnessReport,
    ay_reference: Option<&AYReferenceBackendState>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
    ay_execution: Option<&AYReferenceExecutionReport>,
    trust_cg_backend: Option<&TrustCgBackendExecutionReport>,
) -> CorrectnessReport {
    let mut report = correctness.clone();
    let contains_mismatch_count = report.contains.iter().filter(|row| !row.matched).count();
    let subsumption_mismatch_count = report.subsumption.iter().filter(|row| !row.matched).count();
    report.backend_rows = report
        .workload
        .variants
        .iter()
        .map(|variant| {
            correctness_backend_row(
                variant,
                ay_reference,
                trust_cg_probe.and_then(|probe| trust_cg_probe_row_for_variant(probe, variant)),
                ay_execution,
                trust_cg_backend
                    .and_then(|backend| trust_cg_backend_row_for_variant(backend, variant)),
                contains_mismatch_count,
                subsumption_mismatch_count,
            )
        })
        .collect();
    report
}

/// Deterministic source-token checks for the ay reference scanner.
pub fn ay_reference_source_checks(source: &str) -> Vec<AYReferenceSourceCheck> {
    [
        "SimdClauseScanner",
        "find_clauses_containing",
        "batch_subsumption_check",
        "subsumes_neon",
        "vld1q_s32",
        "vceqq_s32",
        "vmaxvq_u32",
    ]
    .into_iter()
    .map(|token| AYReferenceSourceCheck {
        token,
        present: source.contains(token),
    })
    .collect()
}

const AY_REFERENCE_HELPER_FN: &str = "ay_reference_simd_clause_scanner_helper";
const AY_REFERENCE_WORKLOAD_BUCKET: &str = "mixed_2_16";
const AY_REFERENCE_BATCHES_PER_REPETITION: usize = 64;

#[derive(Clone, Debug)]
struct AYReferenceHelperOutput {
    contains_mismatch_count: usize,
    subsumption_mismatch_count: usize,
    operations: Vec<AYReferenceHelperOperation>,
}

#[derive(Clone, Debug)]
struct AYReferenceHelperOperation {
    operation: String,
    workload_bucket: String,
    warmup_iterations: usize,
    measurement_repetitions: usize,
    batches_per_repetition: usize,
    items_per_batch: usize,
    checksum: u64,
    raw_elapsed_ns: Vec<u64>,
}

/// Run the real ay `SimdClauseScanner` reference over the deterministic fixture.
///
/// This compiles a small helper against the ay source file from the provided
/// clean checkout, then executes ay's public `find_clauses_containing` and
/// `batch_subsumption_check` APIs. It only populates bounded mixed-fixture ay
/// rows; the Trust Codegen/ay throughput gate remains unset until the full matrix runs.
pub fn run_ay_reference_execution(
    cases: &AYSubsumptionCases,
    ay_reference: Option<&AYReferenceBackendState>,
    work_dir: &Path,
) -> AYReferenceExecutionReport {
    run_ay_reference_execution_with_length_buckets(cases, ay_reference, work_dir, &[])
}

/// Run the real ay reference and collect optional numeric length-bucket rows.
pub fn run_ay_reference_execution_with_length_buckets(
    cases: &AYSubsumptionCases,
    ay_reference: Option<&AYReferenceBackendState>,
    work_dir: &Path,
    length_buckets: &[String],
) -> AYReferenceExecutionReport {
    let Some(state) = ay_reference else {
        return ay_reference_unavailable_report(
            None,
            Some("ay_repo_not_provided"),
            "provide --ay-repo to execute the ay reference backend".to_string(),
        );
    };
    if std::env::consts::ARCH != "aarch64" {
        return ay_reference_unavailable_report(
            Some(state),
            Some("ay_reference_host_unsupported"),
            format!(
                "ay_neon_reference execution requires an aarch64 host; host is {}-{}",
                std::env::consts::ARCH,
                std::env::consts::OS
            ),
        );
    }
    if state.resolved_rev.is_none() {
        return ay_reference_unavailable_report(
            Some(state),
            Some("ay_rev_unresolved"),
            format!("could not resolve ay revision {}", state.requested_rev),
        );
    }
    if state.dirty != Some(false) {
        return ay_reference_unavailable_report(
            Some(state),
            Some("ay_repo_dirty"),
            "refusing to execute ay reference from a dirty or unknown checkout".to_string(),
        );
    }
    if !state.source_exists || !state.revision_source_exists || !state.adapter_ready {
        return ay_reference_unavailable_report(
            Some(state),
            Some("ay_reference_source_unavailable"),
            "ay reference source is missing or does not contain the expected scanner tokens"
                .to_string(),
        );
    }

    let helper_dir = work_dir.join("ay_reference_helper");
    let materialized_ay_source_path = helper_dir.join("ay_simd_inprocess_at_requested_rev.rs");
    let helper_source_path = helper_dir.join(format!("{AY_REFERENCE_HELPER_FN}.rs"));
    let helper_binary_path = helper_dir.join(AY_REFERENCE_HELPER_FN);
    if let Err(err) = fs::create_dir_all(&helper_dir) {
        return ay_reference_unavailable_report(
            Some(state),
            Some("ay_reference_helper_io_failed"),
            format!("creating ay reference helper dir failed: {err}"),
        );
    }
    let ay_source = match git_show_ay_reference_source(state) {
        Ok(source) => source,
        Err(message) => {
            return ay_reference_unavailable_report(
                Some(state),
                Some("ay_reference_source_materialize_failed"),
                message,
            );
        }
    };
    if let Err(err) = fs::write(&materialized_ay_source_path, ay_source) {
        return ay_reference_unavailable_report(
            Some(state),
            Some("ay_reference_helper_io_failed"),
            format!("writing requested-revision ay source failed: {err}"),
        );
    }
    let helper_source =
        ay_reference_helper_source(cases, &materialized_ay_source_path, length_buckets);
    if let Err(err) = fs::write(&helper_source_path, helper_source) {
        return ay_reference_unavailable_report(
            Some(state),
            Some("ay_reference_helper_io_failed"),
            format!("writing ay reference helper source failed: {err}"),
        );
    }

    let compile = Command::new("rustc")
        .arg("--edition=2021")
        .arg("-C")
        .arg("opt-level=3")
        .arg(&helper_source_path)
        .arg("-o")
        .arg(&helper_binary_path)
        .output();
    let compile = match compile {
        Ok(output) if output.status.success() => output,
        Ok(output) => {
            return ay_reference_unavailable_report(
                Some(state),
                Some("ay_reference_helper_compile_failed"),
                format!(
                    "rustc failed compiling ay reference helper: {}",
                    String::from_utf8_lossy(&output.stderr).trim()
                ),
            );
        }
        Err(err) => {
            return ay_reference_unavailable_report(
                Some(state),
                Some("ay_reference_helper_compile_failed"),
                format!("launching rustc for ay reference helper failed: {err}"),
            );
        }
    };
    std::hint::black_box(compile);

    let run = Command::new(&helper_binary_path).output();
    let run = match run {
        Ok(output) if output.status.success() => output,
        Ok(output) => {
            return ay_reference_unavailable_report(
                Some(state),
                Some("ay_reference_helper_execution_failed"),
                format!(
                    "ay reference helper exited unsuccessfully: {}",
                    String::from_utf8_lossy(&output.stderr).trim()
                ),
            );
        }
        Err(err) => {
            return ay_reference_unavailable_report(
                Some(state),
                Some("ay_reference_helper_execution_failed"),
                format!("launching ay reference helper failed: {err}"),
            );
        }
    };
    let stdout = String::from_utf8_lossy(&run.stdout);
    let helper = match parse_ay_reference_helper_output(&stdout) {
        Ok(helper) => helper,
        Err(err) => {
            return ay_reference_unavailable_report(
                Some(state),
                Some("ay_reference_helper_output_invalid"),
                err,
            );
        }
    };
    let operation_measurements = helper
        .operations
        .iter()
        .map(ay_reference_operation_from_helper)
        .collect::<Vec<_>>();
    let all_measured = operation_measurements
        .iter()
        .all(|measurement| measurement.status == "ay_reference_measured");
    let mismatch_count = helper.contains_mismatch_count + helper.subsumption_mismatch_count;
    let status = if mismatch_count == 0 && all_measured {
        "ay_reference_execution_pass"
    } else if all_measured {
        "ay_reference_execution_mismatch"
    } else {
        "ay_reference_execution_partial"
    };

    AYReferenceExecutionReport {
        schema: "trust-cg.ay_subsumption.ay_reference_execution.v1",
        status,
        backend_kind: "ay_neon_reference",
        host_arch: std::env::consts::ARCH,
        host_os: std::env::consts::OS,
        repo: Some(state.repo.clone()),
        requested_rev: Some(state.requested_rev.clone()),
        resolved_rev: state.resolved_rev.clone(),
        source_sha256: state.revision_source_sha256.clone(),
        helper_source_path: Some(helper_source_path.display().to_string()),
        helper_binary_path: Some(helper_binary_path.display().to_string()),
        contains_mismatch_count: helper.contains_mismatch_count,
        subsumption_mismatch_count: helper.subsumption_mismatch_count,
        operation_measurements,
        error_code: if status == "ay_reference_execution_pass" {
            None
        } else {
            Some("ay_reference_mismatch_or_measurement_incomplete")
        },
        message: format!(
            "Executed ay SimdClauseScanner from clean checkout {} at {} over the mixed fixture plus {} requested numeric bucket(s): {} contains mismatches, {} subsumption mismatches. This is bounded ay reference evidence only.",
            state.repo,
            state
                .resolved_rev
                .as_deref()
                .unwrap_or(&state.requested_rev),
            length_buckets.len(),
            helper.contains_mismatch_count,
            helper.subsumption_mismatch_count
        ),
        note: "This executes real ay scanner APIs for mixed-fixture rows and explicitly requested numeric ay bucket rows only. Full #571 acceptance still requires Trust Codegen O2/O3 vectorized and scalar-control rows over every bucket plus the 0.90x ay-relative gate.",
    }
}

fn ay_reference_unavailable_report(
    state: Option<&AYReferenceBackendState>,
    error_code: Option<&'static str>,
    message: String,
) -> AYReferenceExecutionReport {
    AYReferenceExecutionReport {
        schema: "trust-cg.ay_subsumption.ay_reference_execution.v1",
        status: "ay_reference_unavailable",
        backend_kind: "ay_neon_reference",
        host_arch: std::env::consts::ARCH,
        host_os: std::env::consts::OS,
        repo: state.map(|state| state.repo.clone()),
        requested_rev: state.map(|state| state.requested_rev.clone()),
        resolved_rev: state.and_then(|state| state.resolved_rev.clone()),
        source_sha256: state.and_then(|state| state.revision_source_sha256.clone()),
        helper_source_path: None,
        helper_binary_path: None,
        contains_mismatch_count: 0,
        subsumption_mismatch_count: 0,
        operation_measurements: Vec::new(),
        error_code,
        message,
        note: "This executes real ay scanner APIs for mixed-fixture rows and explicitly requested numeric ay bucket rows only. Full #571 acceptance still requires Trust Codegen O2/O3 vectorized and scalar-control rows over every bucket plus the 0.90x ay-relative gate.",
    }
}

fn git_show_ay_reference_source(state: &AYReferenceBackendState) -> Result<String, String> {
    let git_path = format!("{}:{}", state.requested_rev, state.revision_source_path);
    let output = Command::new("git")
        .arg("-C")
        .arg(&state.repo)
        .arg("show")
        .arg(&git_path)
        .output()
        .map_err(|err| format!("launching git show for ay reference source failed: {err}"))?;
    if !output.status.success() {
        return Err(format!(
            "git show {git_path} failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

fn ay_reference_operation_from_helper(
    operation: &AYReferenceHelperOperation,
) -> AYReferenceOperationMeasurement {
    let elapsed_values = operation
        .raw_elapsed_ns
        .iter()
        .map(|elapsed| *elapsed as f64)
        .collect::<Vec<_>>();
    let throughput_values = operation
        .raw_elapsed_ns
        .iter()
        .filter_map(|elapsed| {
            if *elapsed == 0 {
                None
            } else {
                let items_per_repetition =
                    operation.items_per_batch * operation.batches_per_repetition;
                Some(items_per_repetition as f64 / (*elapsed as f64 / 1_000.0))
            }
        })
        .collect::<Vec<_>>();
    let (mean_elapsed_ns, stddev_elapsed_ns) = mean_and_stddev(&elapsed_values);
    let (mean_throughput_per_us, stddev_throughput_per_us) = mean_and_stddev(&throughput_values);
    let coefficient_of_variation = match (mean_throughput_per_us, stddev_throughput_per_us) {
        (Some(mean), Some(stddev)) if mean != 0.0 => Some(stddev / mean),
        _ => None,
    };
    let total_items = operation.items_per_batch
        * operation.batches_per_repetition
        * operation.measurement_repetitions;
    let operation_name = match operation.operation.as_str() {
        "contains_literal" => "contains_literal",
        "batch_subsumption" => "batch_subsumption",
        _ => "unknown",
    };

    AYReferenceOperationMeasurement {
        operation: operation_name,
        workload_bucket: operation.workload_bucket.clone(),
        status: if mean_throughput_per_us.is_some()
            && operation.raw_elapsed_ns.len() == operation.measurement_repetitions
        {
            "ay_reference_measured"
        } else {
            "ay_reference_measurement_unavailable"
        },
        warmup_iterations: operation.warmup_iterations,
        measurement_repetitions: operation.measurement_repetitions,
        batches_per_repetition: operation.batches_per_repetition,
        items_per_batch: operation.items_per_batch,
        total_items,
        raw_elapsed_ns: operation.raw_elapsed_ns.clone(),
        mean_elapsed_ns,
        stddev_elapsed_ns,
        mean_throughput_per_us,
        stddev_throughput_per_us,
        coefficient_of_variation,
        checksum: operation.checksum,
        message: format!(
            "Measured {operation_name} through ay SimdClauseScanner over fixture bucket {}; this is a ay reference row, not the full #571 Trust Codegen/ay throughput gate.",
            operation.workload_bucket
        ),
    }
}

fn ay_reference_measurement_for_row<'a>(
    execution: &'a AYReferenceExecutionReport,
    operation: &str,
    length_bucket: &str,
    variant: &str,
) -> Option<&'a AYReferenceOperationMeasurement> {
    if execution.status != "ay_reference_execution_pass" || variant != "ay_neon_reference" {
        return None;
    }
    execution.operation_measurements.iter().find(|measurement| {
        measurement.operation == operation
            && measurement.workload_bucket == length_bucket
            && measurement.status == "ay_reference_measured"
    })
}

fn ay_reference_throughput_for_row(
    execution: &AYReferenceExecutionReport,
    operation: &str,
    length_bucket: &str,
) -> Option<f64> {
    ay_reference_measurement_for_row(execution, operation, length_bucket, "ay_neon_reference")
        .and_then(|measurement| measurement.mean_throughput_per_us)
}

fn trust_cg_probe_measurement_for_row<'a>(
    probe: &'a TrustCgBackendProbeReport,
    operation: &str,
    length_bucket: &str,
    variant: &str,
    include_trust_cg_mixed_rows: bool,
    trust_cg_probe_length_buckets: &[String],
) -> Option<&'a TrustCgProbeOperationMeasurement> {
    if probe.status != "padded_scanner_probe_pass" || !variant.starts_with("trust_cg_") {
        return None;
    }
    let probe_bucket = if length_bucket == AY_REFERENCE_WORKLOAD_BUCKET {
        if !include_trust_cg_mixed_rows {
            return None;
        }
        TRUST_CG_PROBE_WORKLOAD_BUCKET
    } else {
        if !trust_cg_probe_length_buckets
            .iter()
            .any(|bucket| bucket == length_bucket)
        {
            return None;
        }
        length_bucket
    };
    let row = trust_cg_probe_row_for_variant(probe, variant)?;
    if row.status != "padded_scanner_probe_executed"
        || row.chunk_mismatch_count != 0
        || row.contains_mismatch_count != 0
        || row.subsumption_mismatch_count != 0
        || !row.mismatches.is_empty()
    {
        return None;
    }
    row.operation_measurements.iter().find(|measurement| {
        measurement.operation == operation
            && measurement.status == "probe_measured"
            && measurement.workload_bucket == probe_bucket
    })
}

fn trust_cg_backend_measurement_for_row<'a>(
    backend: &'a TrustCgBackendExecutionReport,
    operation: &str,
    length_bucket: &str,
    variant: &str,
    trust_cg_backend_length_buckets: &[String],
) -> Option<&'a TrustCgBackendOperationMeasurement> {
    if backend.status != "trust_cg_backend_execution_pass" || !variant.starts_with("trust_cg_") {
        return None;
    }
    if length_bucket != AY_REFERENCE_WORKLOAD_BUCKET
        && !trust_cg_backend_length_buckets
            .iter()
            .any(|bucket| bucket == length_bucket)
    {
        return None;
    }
    let row = trust_cg_backend_row_for_variant(backend, variant)?;
    if row.status != "trust_cg_backend_executed"
        || row.chunk_mismatch_count != 0
        || row.contains_mismatch_count != 0
        || row.subsumption_mismatch_count != 0
        || !row.mismatches.is_empty()
    {
        return None;
    }
    row.operation_measurements.iter().find(|measurement| {
        measurement.operation == operation
            && measurement.status == "backend_measured"
            && measurement.workload_bucket == length_bucket
    })
}

fn attach_trust_cg_scalar_speedups(rows: &mut [ThroughputSummaryRow]) {
    let measured = rows
        .iter()
        .filter_map(|row| {
            row.mean_throughput_per_us.map(|mean| {
                (
                    (
                        row.operation,
                        row.length_bucket.clone(),
                        row.variant.clone(),
                    ),
                    mean,
                )
            })
        })
        .collect::<BTreeMap<_, _>>();

    for row in rows {
        if !is_trust_cg_throughput_status(row.status) {
            continue;
        }
        let Some(scalar_variant) = trust_cg_scalar_control_variant(&row.variant) else {
            continue;
        };
        let Some(vectorized_mean) = row.mean_throughput_per_us else {
            continue;
        };
        let Some(scalar_mean) = measured.get(&(
            row.operation,
            row.length_bucket.clone(),
            scalar_variant.to_string(),
        )) else {
            continue;
        };
        if *scalar_mean != 0.0 {
            row.scalar_speedup = Some(vectorized_mean / *scalar_mean);
        }
    }
}

fn phase8_executed_correctness_backend_row(row: &CorrectnessBackendRow) -> bool {
    matches!(
        row.status,
        "ay_reference_execution_pass"
            | "ay_reference_execution_mismatch"
            | "ay_reference_execution_partial"
            | "trust_cg_o2_o3_backend_pass"
            | "trust_cg_backend_executed"
            | "padded_scanner_jit_probe_pass"
            | "padded_scanner_probe_executed"
    )
}

fn phase8_promotion_blocker(
    code: &'static str,
    count: usize,
    message: &'static str,
) -> Phase8PromotionBlocker {
    Phase8PromotionBlocker {
        code: code.to_string(),
        count,
        message: message.to_string(),
    }
}

fn phase8_non_empty_optional(value: Option<&str>) -> Option<&str> {
    value.map(str::trim).filter(|field| !field.is_empty())
}

fn phase8_mean_item_time_us<'a>(rows: impl Iterator<Item = &'a ThroughputSummaryRow>) -> f64 {
    let item_times = rows
        .filter_map(|row| row.mean_throughput_per_us)
        .filter(|throughput| *throughput > 0.0)
        .map(|throughput| 1.0 / throughput)
        .collect::<Vec<_>>();
    if item_times.is_empty() {
        0.0
    } else {
        item_times.iter().sum::<f64>() / item_times.len() as f64
    }
}

fn phase8_ay_product_backend_row(row: &ThroughputSummaryRow) -> bool {
    is_trust_cg_backend_throughput_status(row.status)
        && row.product_install_evidence
        && row.promotion_disposition == TRUST_CG_BACKEND_PROMOTION_DISPOSITION
        && matches!(
            row.variant.as_str(),
            "trust_cg_o2_vectorized" | "trust_cg_o3_vectorized"
        )
}

fn throughput_summary_status(
    measured_ay_rows: bool,
    measured_trust_cg_mixed_rows: bool,
    measured_trust_cg_bucket_rows: bool,
    measured_trust_cg_backend_rows: bool,
    pending_backend_rows: usize,
) -> &'static str {
    if pending_backend_rows == 0 && measured_ay_rows && measured_trust_cg_backend_rows {
        return "complete_ay_reference_and_trust_cg_backend_rows";
    }
    match (
        measured_ay_rows,
        measured_trust_cg_mixed_rows,
        measured_trust_cg_bucket_rows,
        measured_trust_cg_backend_rows,
    ) {
        (true, _, _, true) => "partial_ay_reference_and_trust_cg_backend_rows",
        (false, _, _, true) => "partial_trust_cg_backend_rows",
        (true, true, true, false) => "partial_ay_reference_and_trust_cg_probe_rows",
        (true, true, false, false) => "partial_ay_reference_and_trust_cg_mixed_probe",
        (true, false, true, false) => "partial_ay_reference_and_trust_cg_bucket_probe",
        (true, false, false, false) => "partial_ay_reference",
        (false, true, true, false) => "partial_trust_cg_probe_rows",
        (false, true, false, false) => "partial_trust_cg_mixed_probe",
        (false, false, true, false) => "partial_trust_cg_bucket_probe",
        (false, false, false, false) => "plan_only",
    }
}

fn throughput_gate_for_rows(
    rows: &[ThroughputSummaryRow],
    length_buckets: &[String],
) -> ThroughputGate {
    let o2_geomean =
        trust_cg_vectorized_ay_relative_geomean(rows, length_buckets, "trust_cg_o2_vectorized");
    let o3_geomean =
        trust_cg_vectorized_ay_relative_geomean(rows, length_buckets, "trust_cg_o3_vectorized");
    let passed = o2_geomean.map(|ratio| ratio >= 0.90);

    ThroughputGate {
        required_ay_relative_geomean: 0.90,
        trust_cg_o2_vectorized_geomean: o2_geomean,
        trust_cg_o3_vectorized_geomean: o3_geomean,
        passed,
    }
}

fn trust_cg_vectorized_ay_relative_geomean(
    rows: &[ThroughputSummaryRow],
    length_buckets: &[String],
    variant: &str,
) -> Option<f64> {
    let expected_rows = 2 * length_buckets.len();
    let ratios = rows
        .iter()
        .filter(|row| row.variant == variant && is_trust_cg_backend_throughput_status(row.status))
        .filter_map(|row| row.ay_relative_ratio)
        .filter(|ratio| *ratio > 0.0)
        .collect::<Vec<_>>();

    if ratios.len() != expected_rows {
        return None;
    }
    Some((ratios.iter().map(|ratio| ratio.ln()).sum::<f64>() / ratios.len() as f64).exp())
}

fn trust_cg_probe_throughput_status_for_bucket(length_bucket: &str) -> &'static str {
    if length_bucket == AY_REFERENCE_WORKLOAD_BUCKET {
        TRUST_CG_PROBE_MIXED_ROW_STATUS
    } else {
        TRUST_CG_PROBE_BUCKET_ROW_STATUS
    }
}

fn trust_cg_backend_throughput_status_for_bucket(length_bucket: &str) -> &'static str {
    if length_bucket == AY_REFERENCE_WORKLOAD_BUCKET {
        TRUST_CG_BACKEND_MIXED_ROW_STATUS
    } else {
        TRUST_CG_BACKEND_BUCKET_ROW_STATUS
    }
}

fn is_trust_cg_throughput_status(status: &str) -> bool {
    status == TRUST_CG_PROBE_MIXED_ROW_STATUS
        || status == TRUST_CG_PROBE_BUCKET_ROW_STATUS
        || is_trust_cg_backend_throughput_status(status)
}

fn is_trust_cg_backend_throughput_status(status: &str) -> bool {
    status == TRUST_CG_BACKEND_MIXED_ROW_STATUS || status == TRUST_CG_BACKEND_BUCKET_ROW_STATUS
}

fn trust_cg_scalar_control_variant(variant: &str) -> Option<&'static str> {
    match variant {
        "trust_cg_o2_vectorized" => Some("trust_cg_o2_disable_vec"),
        "trust_cg_o3_vectorized" => Some("trust_cg_o3_disable_vec"),
        _ => None,
    }
}

fn parse_ay_reference_helper_output(stdout: &str) -> Result<AYReferenceHelperOutput, String> {
    let mut contains_mismatch_count = None;
    let mut subsumption_mismatch_count = None;
    let mut operations = Vec::new();

    for line in stdout.lines().filter(|line| !line.trim().is_empty()) {
        let parts = line.split('\t').collect::<Vec<_>>();
        match parts.as_slice() {
            ["schema", "ay_reference_helper_v1"] => {}
            ["contains_mismatch_count", value] => {
                contains_mismatch_count = Some(
                    value
                        .parse::<usize>()
                        .map_err(|err| format!("invalid contains mismatch count: {err}"))?,
                );
            }
            ["subsumption_mismatch_count", value] => {
                subsumption_mismatch_count = Some(
                    value
                        .parse::<usize>()
                        .map_err(|err| format!("invalid subsumption mismatch count: {err}"))?,
                );
            }
            [
                "operation",
                operation,
                workload_bucket,
                warmup,
                repetitions,
                batches,
                items,
                checksum,
                elapsed,
            ] => {
                let raw_elapsed_ns = if elapsed.is_empty() {
                    Vec::new()
                } else {
                    elapsed
                        .split(',')
                        .map(|value| {
                            value
                                .parse::<u64>()
                                .map_err(|err| format!("invalid elapsed ns value: {err}"))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                };
                operations.push(AYReferenceHelperOperation {
                    operation: (*operation).to_string(),
                    workload_bucket: (*workload_bucket).to_string(),
                    warmup_iterations: warmup
                        .parse::<usize>()
                        .map_err(|err| format!("invalid warmup count: {err}"))?,
                    measurement_repetitions: repetitions
                        .parse::<usize>()
                        .map_err(|err| format!("invalid repetition count: {err}"))?,
                    batches_per_repetition: batches
                        .parse::<usize>()
                        .map_err(|err| format!("invalid batch count: {err}"))?,
                    items_per_batch: items
                        .parse::<usize>()
                        .map_err(|err| format!("invalid item count: {err}"))?,
                    checksum: checksum
                        .parse::<u64>()
                        .map_err(|err| format!("invalid checksum: {err}"))?,
                    raw_elapsed_ns,
                });
            }
            [
                "operation",
                operation,
                warmup,
                repetitions,
                batches,
                items,
                checksum,
                elapsed,
            ] => {
                let raw_elapsed_ns = if elapsed.is_empty() {
                    Vec::new()
                } else {
                    elapsed
                        .split(',')
                        .map(|value| {
                            value
                                .parse::<u64>()
                                .map_err(|err| format!("invalid elapsed ns value: {err}"))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                };
                operations.push(AYReferenceHelperOperation {
                    operation: (*operation).to_string(),
                    workload_bucket: AY_REFERENCE_WORKLOAD_BUCKET.to_string(),
                    warmup_iterations: warmup
                        .parse::<usize>()
                        .map_err(|err| format!("invalid warmup count: {err}"))?,
                    measurement_repetitions: repetitions
                        .parse::<usize>()
                        .map_err(|err| format!("invalid repetition count: {err}"))?,
                    batches_per_repetition: batches
                        .parse::<usize>()
                        .map_err(|err| format!("invalid batch count: {err}"))?,
                    items_per_batch: items
                        .parse::<usize>()
                        .map_err(|err| format!("invalid item count: {err}"))?,
                    checksum: checksum
                        .parse::<u64>()
                        .map_err(|err| format!("invalid checksum: {err}"))?,
                    raw_elapsed_ns,
                });
            }
            _ => {
                return Err(format!(
                    "unexpected ay reference helper output line: {line}"
                ));
            }
        }
    }

    Ok(AYReferenceHelperOutput {
        contains_mismatch_count: contains_mismatch_count
            .ok_or_else(|| "missing contains mismatch count".to_string())?,
        subsumption_mismatch_count: subsumption_mismatch_count
            .ok_or_else(|| "missing subsumption mismatch count".to_string())?,
        operations,
    })
}

fn ay_reference_helper_source(
    cases: &AYSubsumptionCases,
    source_path: &Path,
    length_buckets: &[String],
) -> String {
    let clauses = cases
        .clauses
        .iter()
        .map(|clause| format!("    &{:?},", clause.lits))
        .collect::<Vec<_>>()
        .join("\n");
    let clause_ids = cases
        .clauses
        .iter()
        .map(|clause| format!("    {}u32,", clause.id))
        .collect::<Vec<_>>()
        .join("\n");
    let clause_lengths = cases
        .clauses
        .iter()
        .map(|clause| format!("    {}usize,", clause.length))
        .collect::<Vec<_>>()
        .join("\n");
    let contains_queries = cases
        .contains_queries
        .iter()
        .map(|query| {
            let expected = query
                .expected_clause_ids
                .iter()
                .map(|id| format!("{id}u32"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("    ({}, &[{}]),", query.literal, expected)
        })
        .collect::<Vec<_>>()
        .join("\n");
    let subsumption_pairs = cases
        .subsumption_pairs
        .iter()
        .map(|pair| format!("    ({}, {}, {}),", pair.a, pair.b, pair.expected))
        .collect::<Vec<_>>()
        .join("\n");
    let source_path_literal = rust_string_literal(&source_path.display().to_string());
    let warmup_iterations = cases.benchmark_matrix.warmup_iterations as usize;
    let measurement_repetitions = cases.benchmark_matrix.measurement_repetitions.max(1) as usize;
    let numeric_buckets = length_buckets
        .iter()
        .filter_map(|bucket| {
            bucket
                .parse::<usize>()
                .ok()
                .map(|length| format!("    ({:?}, {}usize),", bucket, length))
        })
        .collect::<Vec<_>>()
        .join("\n");

    format!(
        r#"
#[path = {source_path_literal}]
mod simd_inprocess;

use simd_inprocess::SimdClauseScanner;
use std::time::Instant;

const CLAUSES: &[&[i32]] = &[
{clauses}
];
const CLAUSE_IDS: &[u32] = &[
{clause_ids}
];
const CLAUSE_LENGTHS: &[usize] = &[
{clause_lengths}
];
const CONTAINS_QUERIES: &[(i32, &[u32])] = &[
{contains_queries}
];
const SUBSUMPTION_PAIRS: &[(usize, usize, bool)] = &[
{subsumption_pairs}
];
const NUMERIC_BUCKETS: &[(&str, usize)] = &[
{numeric_buckets}
];
const WARMUP_ITERATIONS: usize = {warmup_iterations};
const MEASUREMENT_REPETITIONS: usize = {measurement_repetitions};
const BATCHES_PER_REPETITION: usize = {AY_REFERENCE_BATCHES_PER_REPETITION};

struct Measurement {{
    operation: &'static str,
    workload_bucket: &'static str,
    raw_elapsed_ns: Vec<u64>,
    checksum: u64,
    items_per_batch: usize,
}}

fn main() {{
    let scanner = build_scanner();
    let all_indexes = (0..CLAUSES.len()).collect::<Vec<_>>();
    let pairs = SUBSUMPTION_PAIRS
        .iter()
        .map(|(a, b, _)| (*a, *b))
        .collect::<Vec<_>>();
    let contains_mismatch_count = contains_mismatch_count(&scanner);
    let subsumption_mismatch_count = subsumption_mismatch_count(&scanner, &pairs);
    let mut measurements = Vec::new();
    measurements.push(measure_operation(
        "contains_literal",
        "mixed_2_16",
        CONTAINS_QUERIES.len() * CLAUSES.len(),
        || run_contains_batch_for_clause_indexes(&scanner, &all_indexes),
    ));
    measurements.push(measure_operation(
        "batch_subsumption",
        "mixed_2_16",
        SUBSUMPTION_PAIRS.len(),
        || run_subsumption_batch(&scanner, &pairs),
    ));

    for &(bucket_label, bucket_length) in NUMERIC_BUCKETS {{
        let indexes = clause_indexes_for_length(bucket_length);
        if indexes.is_empty() {{
            continue;
        }}
        let bucket_scanner = build_scanner_for_indexes(&indexes);
        let self_pairs = (0..indexes.len())
            .map(|index| (index, index))
            .collect::<Vec<_>>();
        measurements.push(measure_operation(
            "contains_literal",
            bucket_label,
            CONTAINS_QUERIES.len() * indexes.len(),
            || run_contains_batch_for_clause_indexes(&bucket_scanner, &indexes),
        ));
        measurements.push(measure_operation(
            "batch_subsumption",
            bucket_label,
            self_pairs.len(),
            || run_subsumption_batch(&bucket_scanner, &self_pairs),
        ));
    }}

    println!("schema\tay_reference_helper_v1");
    println!("contains_mismatch_count\t{{contains_mismatch_count}}");
    println!("subsumption_mismatch_count\t{{subsumption_mismatch_count}}");
    for measurement in &measurements {{
        print_measurement(measurement);
    }}
}}

fn build_scanner() -> SimdClauseScanner {{
    let all_indexes = (0..CLAUSES.len()).collect::<Vec<_>>();
    build_scanner_for_indexes(&all_indexes)
}}

fn build_scanner_for_indexes(indexes: &[usize]) -> SimdClauseScanner {{
    let total_lits = indexes
        .iter()
        .map(|index| CLAUSES[*index].len())
        .sum::<usize>();
    let mut scanner = SimdClauseScanner::with_capacity(indexes.len(), total_lits);
    for index in indexes {{
        scanner.push(CLAUSES[*index]);
    }}
    scanner
}}

fn clause_indexes_for_length(length: usize) -> Vec<usize> {{
    CLAUSE_LENGTHS
        .iter()
        .enumerate()
        .filter_map(|(index, clause_length)| (*clause_length == length).then_some(index))
        .collect()
}}

fn contains_mismatch_count(scanner: &SimdClauseScanner) -> usize {{
    let mut mismatches = 0usize;
    for &(literal, expected) in CONTAINS_QUERIES {{
        let actual = scanner
            .find_clauses_containing(literal)
            .iter()
            .filter_map(|id| CLAUSE_IDS.get(*id as usize).copied())
            .collect::<Vec<_>>();
        if actual.as_slice() != expected {{
            mismatches += 1;
        }}
    }}
    mismatches
}}

fn subsumption_mismatch_count(scanner: &SimdClauseScanner, pairs: &[(usize, usize)]) -> usize {{
    let actual = scanner.batch_subsumption_check(pairs);
    let mut mismatches = 0usize;
    for (expected, actual) in SUBSUMPTION_PAIRS.iter().zip(actual.iter()) {{
        if expected.2 != actual.2 {{
            mismatches += 1;
        }}
    }}
    mismatches
}}

fn measure_operation<F>(
    operation: &'static str,
    workload_bucket: &'static str,
    items_per_batch: usize,
    mut run_batch: F,
) -> Measurement
where
    F: FnMut() -> u64,
{{
    for _ in 0..WARMUP_ITERATIONS {{
        std::hint::black_box(run_batch());
    }}

    let mut checksum = 0u64;
    let mut raw_elapsed_ns = Vec::with_capacity(MEASUREMENT_REPETITIONS);
    for _ in 0..MEASUREMENT_REPETITIONS {{
        let start = Instant::now();
        let mut repetition_checksum = 0u64;
        for _ in 0..BATCHES_PER_REPETITION {{
            repetition_checksum = repetition_checksum.wrapping_add(run_batch());
        }}
        std::hint::black_box(repetition_checksum);
        checksum = checksum.wrapping_add(repetition_checksum);
        raw_elapsed_ns.push(start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64);
    }}
    Measurement {{
        operation,
        workload_bucket,
        raw_elapsed_ns,
        checksum,
        items_per_batch,
    }}
}}

fn run_contains_batch_for_clause_indexes(
    scanner: &SimdClauseScanner,
    clause_indexes: &[usize],
) -> u64 {{
    let mut checksum = 0u64;
    for &(literal, _) in CONTAINS_QUERIES {{
        let found = scanner.find_clauses_containing(literal);
        let mut id_checksum = 0u64;
        for id in &found {{
            let original_index = clause_indexes.get(*id as usize).copied().unwrap_or(usize::MAX);
            let original_id = CLAUSE_IDS.get(original_index).copied().unwrap_or(u32::MAX);
            id_checksum ^= u64::from(original_id);
        }}
        checksum = checksum
            .wrapping_mul(131)
            .wrapping_add(literal as u32 as u64)
            .wrapping_add(found.len() as u64)
            .wrapping_add(id_checksum);
    }}
    checksum
}}

fn run_subsumption_batch(scanner: &SimdClauseScanner, pairs: &[(usize, usize)]) -> u64 {{
    let actual = scanner.batch_subsumption_check(pairs);
    let mut checksum = 0u64;
    for (a, b, result) in actual {{
        checksum = checksum
            .wrapping_mul(131)
            .wrapping_add(a as u64)
            .wrapping_add((b as u64) << 8)
            .wrapping_add(u64::from(result));
    }}
    checksum
}}

fn print_measurement(measurement: &Measurement) {{
    let elapsed = measurement
        .raw_elapsed_ns
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "operation\t{{}}\t{{}}\t{{}}\t{{}}\t{{}}\t{{}}\t{{}}\t{{}}",
        measurement.operation,
        measurement.workload_bucket,
        WARMUP_ITERATIONS,
        MEASUREMENT_REPETITIONS,
        BATCHES_PER_REPETITION,
        measurement.items_per_batch,
        measurement.checksum,
        elapsed
    );
}}
"#
    )
}

fn rust_string_literal(value: &str) -> String {
    format!("{value:?}")
}

/// CSV header for raw throughput measurements.
pub fn ay_subsumption_throughput_csv_header() -> &'static str {
    "operation,length_bucket,variant,repetition,elapsed_ns,items,throughput_per_us,status\n"
}

/// Build raw throughput CSV rows for optional partial backend execution.
pub fn ay_subsumption_throughput_csv(ay_execution: Option<&AYReferenceExecutionReport>) -> String {
    ay_subsumption_throughput_csv_with_backend_execution(ay_execution, None, false)
}

/// Build raw throughput CSV rows for optional partial backend execution.
pub fn ay_subsumption_throughput_csv_with_backend_execution(
    ay_execution: Option<&AYReferenceExecutionReport>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
    include_trust_cg_mixed_rows: bool,
) -> String {
    ay_subsumption_throughput_csv_with_probe_buckets(
        ay_execution,
        trust_cg_probe,
        include_trust_cg_mixed_rows,
        &[],
    )
}

/// Build raw throughput CSV rows for optional partial backend execution.
pub fn ay_subsumption_throughput_csv_with_probe_buckets(
    ay_execution: Option<&AYReferenceExecutionReport>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
    include_trust_cg_mixed_rows: bool,
    trust_cg_probe_length_buckets: &[String],
) -> String {
    ay_subsumption_throughput_csv_with_backend_buckets(
        ay_execution,
        trust_cg_probe,
        include_trust_cg_mixed_rows,
        trust_cg_probe_length_buckets,
        None,
        &[],
    )
}

/// Build raw throughput CSV rows for optional partial backend execution.
pub fn ay_subsumption_throughput_csv_with_backend_buckets(
    ay_execution: Option<&AYReferenceExecutionReport>,
    trust_cg_probe: Option<&TrustCgBackendProbeReport>,
    include_trust_cg_mixed_rows: bool,
    trust_cg_probe_length_buckets: &[String],
    trust_cg_backend: Option<&TrustCgBackendExecutionReport>,
    trust_cg_backend_length_buckets: &[String],
) -> String {
    let mut csv = ay_subsumption_throughput_csv_header().to_string();
    if let Some(execution) = ay_execution
        && execution.status == "ay_reference_execution_pass"
    {
        for measurement in &execution.operation_measurements {
            if measurement.status != "ay_reference_measured" {
                continue;
            }
            let items_per_repetition =
                measurement.items_per_batch * measurement.batches_per_repetition;
            for (index, elapsed_ns) in measurement.raw_elapsed_ns.iter().enumerate() {
                let throughput_per_us = if *elapsed_ns == 0 {
                    0.0
                } else {
                    items_per_repetition as f64 / (*elapsed_ns as f64 / 1_000.0)
                };
                csv.push_str(&format!(
                    "{},{},ay_neon_reference,{},{},{},{:.9},ay_reference_measured\n",
                    measurement.operation,
                    measurement.workload_bucket,
                    index,
                    elapsed_ns,
                    items_per_repetition,
                    throughput_per_us
                ));
            }
        }
    }
    if (include_trust_cg_mixed_rows || !trust_cg_probe_length_buckets.is_empty())
        && let Some(probe) = trust_cg_probe
        && probe.status == "padded_scanner_probe_pass"
    {
        for row in &probe.rows {
            if row.status != "padded_scanner_probe_executed"
                || row.chunk_mismatch_count != 0
                || row.contains_mismatch_count != 0
                || row.subsumption_mismatch_count != 0
                || !row.mismatches.is_empty()
            {
                continue;
            }
            for measurement in &row.operation_measurements {
                if measurement.status != "probe_measured" {
                    continue;
                }
                let Some((length_bucket, status)) = trust_cg_probe_csv_bucket_status(
                    &measurement.workload_bucket,
                    include_trust_cg_mixed_rows,
                    trust_cg_probe_length_buckets,
                ) else {
                    continue;
                };
                let items_per_repetition =
                    measurement.items_per_batch * measurement.batches_per_repetition;
                for (index, elapsed_ns) in measurement.raw_elapsed_ns.iter().enumerate() {
                    let throughput_per_us = if *elapsed_ns == 0 {
                        0.0
                    } else {
                        items_per_repetition as f64 / (*elapsed_ns as f64 / 1_000.0)
                    };
                    csv.push_str(&format!(
                        "{},{},{},{},{},{},{:.9},{}\n",
                        measurement.operation,
                        length_bucket,
                        row.variant,
                        index,
                        elapsed_ns,
                        items_per_repetition,
                        throughput_per_us,
                        status
                    ));
                }
            }
        }
    }
    if !trust_cg_backend_length_buckets.is_empty()
        && let Some(backend) = trust_cg_backend
        && backend.status == "trust_cg_backend_execution_pass"
    {
        for row in &backend.rows {
            if row.status != "trust_cg_backend_executed"
                || row.chunk_mismatch_count != 0
                || row.contains_mismatch_count != 0
                || row.subsumption_mismatch_count != 0
                || !row.mismatches.is_empty()
            {
                continue;
            }
            for measurement in &row.operation_measurements {
                if measurement.status != "backend_measured"
                    || (measurement.workload_bucket != AY_REFERENCE_WORKLOAD_BUCKET
                        && !trust_cg_backend_length_buckets
                            .iter()
                            .any(|bucket| bucket == &measurement.workload_bucket))
                {
                    continue;
                }
                let items_per_repetition =
                    measurement.items_per_batch * measurement.batches_per_repetition;
                for (index, elapsed_ns) in measurement.raw_elapsed_ns.iter().enumerate() {
                    let throughput_per_us = if *elapsed_ns == 0 {
                        0.0
                    } else {
                        items_per_repetition as f64 / (*elapsed_ns as f64 / 1_000.0)
                    };
                    csv.push_str(&format!(
                        "{},{},{},{},{},{},{:.9},{}\n",
                        measurement.operation,
                        measurement.workload_bucket,
                        row.variant,
                        index,
                        elapsed_ns,
                        items_per_repetition,
                        throughput_per_us,
                        trust_cg_backend_throughput_status_for_bucket(&measurement.workload_bucket)
                    ));
                }
            }
        }
    }
    csv
}

fn trust_cg_probe_csv_bucket_status<'a>(
    workload_bucket: &'a str,
    include_trust_cg_mixed_rows: bool,
    trust_cg_probe_length_buckets: &'a [String],
) -> Option<(&'a str, &'static str)> {
    if workload_bucket == TRUST_CG_PROBE_WORKLOAD_BUCKET {
        return include_trust_cg_mixed_rows.then_some((
            AY_REFERENCE_WORKLOAD_BUCKET,
            TRUST_CG_PROBE_MIXED_ROW_STATUS,
        ));
    }
    trust_cg_probe_length_buckets
        .iter()
        .any(|bucket| bucket == workload_bucket)
        .then_some((workload_bucket, TRUST_CG_PROBE_BUCKET_ROW_STATUS))
}

fn backend_artifact_status(
    trust_cg_probe: bool,
    ay_execution: bool,
    trust_cg_backend: bool,
) -> &'static str {
    match (ay_execution, trust_cg_probe, trust_cg_backend) {
        (true, _, true) => "plan_with_ay_reference_and_trust_cg_backend",
        (false, _, true) => "plan_with_trust_cg_backend",
        (true, true, false) => "plan_with_ay_reference_and_trust_cg_probe",
        (true, false, false) => "plan_with_ay_reference",
        (false, true, false) => "plan_with_trust_cg_probe",
        (false, false, false) => "plan_only",
    }
}

/// Run a bounded Trust Codegen raw-JIT probe for the Trust Codegen variants in the workload.
///
/// This checks a masked `contains4(chunk_ptr, literal, valid_mask)` kernel
/// over fixture padded chunks, then uses that JIT primitive to validate the
/// fixture containment and subsumption rows. It proves that the matrix runner
/// can compile and call an Trust Codegen JIT symbol for the ay padded 4-lane scanner
/// primitive, but it is not the full O2/O3 vectorized workload or throughput
/// acceptance matrix.
pub fn run_trust_cg_backend_probe(cases: &AYSubsumptionCases) -> TrustCgBackendProbeReport {
    run_trust_cg_backend_probe_with_length_buckets(cases, &[])
}

/// Run the bounded Trust Codegen raw-JIT probe and collect optional numeric bucket rows.
pub fn run_trust_cg_backend_probe_with_length_buckets(
    cases: &AYSubsumptionCases,
    length_buckets: &[String],
) -> TrustCgBackendProbeReport {
    let rows = cases
        .benchmark_matrix
        .variants
        .iter()
        .filter(|variant| variant.starts_with("trust_cg_"))
        .map(|variant| run_trust_cg_backend_probe_row(cases, variant, length_buckets))
        .collect::<Vec<_>>();
    let status = if rows.iter().all(|row| {
        row.status == "padded_scanner_probe_executed"
            && row.chunk_mismatch_count == 0
            && row.contains_mismatch_count == 0
            && row.subsumption_mismatch_count == 0
            && row.mismatches.is_empty()
    }) {
        "padded_scanner_probe_pass"
    } else if rows
        .iter()
        .any(|row| row.status == "padded_scanner_probe_executed")
    {
        "padded_scanner_probe_partial"
    } else {
        "padded_scanner_probe_unavailable"
    };

    TrustCgBackendProbeReport {
        schema: "trust-cg.ay_subsumption.trust_cg_backend_probe.v1",
        status,
        probe_kind: "aarch64_raw_jit_contains4_masked",
        promotion_disposition: TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION,
        product_install_evidence: false,
        host_arch: std::env::consts::ARCH,
        host_os: std::env::consts::OS,
        rows,
        note: "This optional probe executes a raw Trust Codegen JIT masked contains4 primitive over fixture padded chunks, validates containment/subsumption rows through that primitive, and records profile-only/non-promoting mixed 2..16 plus explicitly requested numeric-bucket operation timings. It is not installable product evidence. Full #571 acceptance still requires whole-workload Trust Codegen O2/O3 vectorized and scalar-control backends plus measured ay NEON throughput over the complete 160-row matrix.",
    }
}

/// Run bounded real Trust Codegen O2/O3 backend rows for selected buckets.
pub fn run_trust_cg_backend_execution_with_length_buckets(
    cases: &AYSubsumptionCases,
    length_buckets: &[String],
) -> TrustCgBackendExecutionReport {
    let rows = cases
        .benchmark_matrix
        .variants
        .iter()
        .filter(|variant| variant.starts_with("trust_cg_"))
        .map(|variant| run_trust_cg_backend_execution_row(cases, variant, length_buckets))
        .collect::<Vec<_>>();
    let scalar_control_comparisons = run_trust_cg_contains4_scalar_control_comparisons(cases);
    let profitability_comparisons = trust_cg_backend_profitability_comparisons(&rows);
    let rows_pass = rows.iter().all(|row| {
        row.status == "trust_cg_backend_executed"
            && row.chunk_mismatch_count == 0
            && row.contains_mismatch_count == 0
            && row.subsumption_mismatch_count == 0
            && row.mismatches.is_empty()
            && row
                .operation_measurements
                .iter()
                .all(|measurement| measurement.status == "backend_measured")
    });
    let scalar_control_pass = scalar_control_comparisons
        .iter()
        .all(|comparison| comparison.status == "scalar_control_match");
    let status = if rows_pass && scalar_control_pass {
        "trust_cg_backend_execution_pass"
    } else if rows
        .iter()
        .any(|row| row.status == "trust_cg_backend_executed")
        || scalar_control_comparisons
            .iter()
            .any(|comparison| comparison.status == "scalar_control_match")
    {
        "trust_cg_backend_execution_partial"
    } else {
        "trust_cg_backend_execution_unavailable"
    };

    TrustCgBackendExecutionReport {
        schema: "trust-cg.ay_subsumption.trust_cg_backend_execution.v1",
        status,
        backend_kind: "aarch64_o2_o3_pipeline_jit_contains4_masked",
        host_arch: std::env::consts::ARCH,
        host_os: std::env::consts::OS,
        rows,
        scalar_control_comparisons,
        profitability_comparisons,
        note: "This optional backend execution compiles a bounded masked contains4 primitive through the requested Trust Codegen O2/O3 pipeline mode, including TRUST_CG_DISABLE_PASSES=vec scalar controls, then uses it to populate selected scanner/subsumption rows. A request for every numeric fixture bucket also measures the mixed 2..16 workload. Full #571 acceptance still requires complete artifacts and the 0.90x ay-relative gate.",
    }
}

fn trust_cg_probe_row_for_variant<'a>(
    probe: &'a TrustCgBackendProbeReport,
    variant: &str,
) -> Option<&'a TrustCgBackendProbeRow> {
    probe.rows.iter().find(|row| row.variant == variant)
}

fn trust_cg_backend_row_for_variant<'a>(
    backend: &'a TrustCgBackendExecutionReport,
    variant: &str,
) -> Option<&'a TrustCgBackendExecutionRow> {
    backend.rows.iter().find(|row| row.variant == variant)
}

fn correctness_backend_row(
    variant: &str,
    ay_reference: Option<&AYReferenceBackendState>,
    trust_cg_probe: Option<&TrustCgBackendProbeRow>,
    ay_execution: Option<&AYReferenceExecutionReport>,
    trust_cg_backend: Option<&TrustCgBackendExecutionRow>,
    contains_mismatch_count: usize,
    subsumption_mismatch_count: usize,
) -> CorrectnessBackendRow {
    if variant == "ay_neon_reference" {
        if let Some(execution) = ay_execution {
            return CorrectnessBackendRow {
                variant: variant.to_string(),
                backend_kind: execution.backend_kind,
                status: execution.status,
                error_code: execution.error_code,
                contains_mismatch_count: execution.contains_mismatch_count,
                subsumption_mismatch_count: execution.subsumption_mismatch_count,
                source_sha256: execution.source_sha256.clone(),
                message: execution.message.clone(),
            };
        }
        return match ay_reference {
            Some(state) if state.adapter_ready => CorrectnessBackendRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "reference_adapter_ready",
                error_code: None,
                contains_mismatch_count,
                subsumption_mismatch_count,
                source_sha256: state.revision_source_sha256.clone(),
                message: format!(
                    "ay source {} resolved at {}; deterministic fixture oracle rows are populated for reference comparison, but NEON execution was not run",
                    state.revision_source_path,
                    state
                        .resolved_rev
                        .as_deref()
                        .unwrap_or(&state.requested_rev)
                ),
            },
            Some(state) if state.resolved_rev.is_none() => CorrectnessBackendRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "unavailable",
                error_code: Some("ay_rev_unresolved"),
                contains_mismatch_count,
                subsumption_mismatch_count,
                source_sha256: None,
                message: format!("could not resolve ay revision {}", state.requested_rev),
            },
            Some(state) if !state.revision_source_exists => CorrectnessBackendRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "unavailable",
                error_code: Some("ay_source_missing_at_rev"),
                contains_mismatch_count,
                subsumption_mismatch_count,
                source_sha256: None,
                message: format!(
                    "could not inspect ay source {} at {}",
                    state.revision_source_path, state.requested_rev
                ),
            },
            Some(_) => CorrectnessBackendRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "unavailable",
                error_code: Some("ay_source_symbols_missing"),
                contains_mismatch_count,
                subsumption_mismatch_count,
                source_sha256: None,
                message: "ay source was found, but expected scanner/NEON tokens were missing"
                    .to_string(),
            },
            None => CorrectnessBackendRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "unavailable",
                error_code: Some("ay_repo_not_provided"),
                contains_mismatch_count,
                subsumption_mismatch_count,
                source_sha256: None,
                message: "provide --ay-repo to inspect the ay reference backend".to_string(),
            },
        };
    }

    if let Some(backend) = trust_cg_backend {
        return CorrectnessBackendRow {
            variant: variant.to_string(),
            backend_kind: backend.backend_kind,
            status: if backend.status == "trust_cg_backend_executed"
                && backend.chunk_mismatch_count == 0
                && backend.contains_mismatch_count == 0
                && backend.subsumption_mismatch_count == 0
                && backend.mismatches.is_empty()
            {
                "trust_cg_o2_o3_backend_pass"
            } else {
                backend.status
            },
            error_code: backend.error_code,
            contains_mismatch_count: backend.chunk_mismatch_count + backend.contains_mismatch_count,
            subsumption_mismatch_count: backend.subsumption_mismatch_count,
            source_sha256: None,
            message: format!(
                "{} Full all-bucket O2/O3 vectorized and scalar-control correctness remain pending.",
                backend.message
            ),
        };
    }

    if let Some(probe) = trust_cg_probe {
        return CorrectnessBackendRow {
            variant: variant.to_string(),
            backend_kind: probe.backend_kind,
            status: if probe.status == "padded_scanner_probe_executed"
                && probe.chunk_mismatch_count == 0
                && probe.contains_mismatch_count == 0
                && probe.subsumption_mismatch_count == 0
                && probe.mismatches.is_empty()
            {
                "padded_scanner_jit_probe_pass"
            } else {
                probe.status
            },
            error_code: probe.error_code,
            contains_mismatch_count: probe.chunk_mismatch_count + probe.contains_mismatch_count,
            subsumption_mismatch_count: probe.subsumption_mismatch_count,
            source_sha256: None,
            message: format!(
                "{} Full O2/O3 vectorized and scalar-control correctness remain pending.",
                probe.message
            ),
        };
    }

    CorrectnessBackendRow {
        variant: variant.to_string(),
        backend_kind: if variant.starts_with("trust_cg_") {
            "trust-cg"
        } else {
            "unknown"
        },
        status: "execution_unsupported",
        error_code: Some("trust_cg_backend_not_wired"),
        contains_mismatch_count,
        subsumption_mismatch_count,
        source_sha256: None,
        message: "Trust Codegen benchmark execution backend is not wired yet".to_string(),
    }
}

fn backend_readiness_row(
    variant: &str,
    ay_reference: Option<AYReferenceBackendState>,
    trust_cg_probe: Option<&TrustCgBackendProbeRow>,
    ay_execution: Option<&AYReferenceExecutionReport>,
    trust_cg_backend: Option<&TrustCgBackendExecutionRow>,
) -> BackendReadinessRow {
    if variant == "ay_neon_reference" {
        if let Some(execution) = ay_execution {
            return BackendReadinessRow {
                variant: variant.to_string(),
                backend_kind: execution.backend_kind,
                status: execution.status,
                error_code: execution.error_code,
                message: execution.message.clone(),
                ay_reference,
                trust_cg_probe: None,
                trust_cg_backend: None,
            };
        }
        return match ay_reference {
            Some(state) if state.resolved_rev.is_none() => BackendReadinessRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "unavailable",
                error_code: Some("ay_rev_unresolved"),
                message: format!("could not resolve ay revision {}", state.requested_rev),
                ay_reference: Some(state),
                trust_cg_probe: None,
                trust_cg_backend: None,
            },
            Some(state) if !state.source_exists => BackendReadinessRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "unavailable",
                error_code: Some("ay_source_missing"),
                message: format!("expected ay source file {} is missing", state.source_path),
                ay_reference: Some(state),
                trust_cg_probe: None,
                trust_cg_backend: None,
            },
            Some(state) if state.adapter_ready => BackendReadinessRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "reference_adapter_ready",
                error_code: None,
                message: format!(
                    "ay reference source {} resolved at {}; deterministic adapter artifacts can be populated without running throughput",
                    state.revision_source_path,
                    state
                        .resolved_rev
                        .as_deref()
                        .unwrap_or(&state.requested_rev)
                ),
                ay_reference: Some(state),
                trust_cg_probe: None,
                trust_cg_backend: None,
            },
            Some(state) if !state.revision_source_exists => BackendReadinessRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "unavailable",
                error_code: Some("ay_source_missing_at_rev"),
                message: format!(
                    "expected ay source {} is missing at {}",
                    state.revision_source_path, state.requested_rev
                ),
                ay_reference: Some(state),
                trust_cg_probe: None,
                trust_cg_backend: None,
            },
            Some(state) => BackendReadinessRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "unavailable",
                error_code: Some("ay_source_symbols_missing"),
                message: "expected ay scanner/NEON tokens are missing from the requested source"
                    .to_string(),
                ay_reference: Some(state),
                trust_cg_probe: None,
                trust_cg_backend: None,
            },
            None => BackendReadinessRow {
                variant: variant.to_string(),
                backend_kind: "ay_reference",
                status: "unavailable",
                error_code: Some("ay_repo_not_provided"),
                message: "provide --ay-repo to inspect the ay reference backend".to_string(),
                ay_reference: None,
                trust_cg_probe: None,
                trust_cg_backend: None,
            },
        };
    }

    if let Some(backend) = trust_cg_backend {
        return BackendReadinessRow {
            variant: variant.to_string(),
            backend_kind: backend.backend_kind,
            status: backend.status,
            error_code: backend.error_code,
            message: backend.message.clone(),
            ay_reference: None,
            trust_cg_probe: None,
            trust_cg_backend: Some(backend.clone()),
        };
    }

    if let Some(probe) = trust_cg_probe {
        return BackendReadinessRow {
            variant: variant.to_string(),
            backend_kind: probe.backend_kind,
            status: probe.status,
            error_code: probe.error_code,
            message: probe.message.clone(),
            ay_reference: None,
            trust_cg_probe: Some(probe.clone()),
            trust_cg_backend: None,
        };
    }

    let backend_kind = if variant.starts_with("trust_cg_") {
        "trust-cg"
    } else {
        "unknown"
    };
    BackendReadinessRow {
        variant: variant.to_string(),
        backend_kind,
        status: "execution_unsupported",
        error_code: Some("trust_cg_backend_not_wired"),
        message: "Trust Codegen benchmark execution backend is not wired yet".to_string(),
        ay_reference: None,
        trust_cg_probe: None,
        trust_cg_backend: None,
    }
}

const TRUST_CG_CONTAINS4_MASKED_PROBE_FN: &str = "trust_cg_ay_contains4_masked_probe";
const TRUST_CG_CONTAINS4_MASKED_BACKEND_FN: &str = "trust_cg_ay_contains4_masked_backend";
// #1066: these scanner fixtures/builders are live in unit tests on every host
// and in production only for the supported AArch64 JIT backend path.
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
const TRUST_CG_CONTAINS_LITERAL_SCANNER_BACKEND_FN: &str =
    "trust_cg_ay_contains_literal_scanner_backend";
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
const TRUST_CG_CONTAINS_LITERAL_QUERY_BATCH_BACKEND_FN: &str =
    "trust_cg_ay_contains_literal_query_batch_backend";
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
const TRUST_CG_BATCH_SUBSUMPTION_SCANNER_BACKEND_FN: &str =
    "trust_cg_ay_batch_subsumption_scanner_backend";
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
const TRUST_CG_BATCH_SUBSUMPTION_REPEATED_CHECKSUM_BACKEND_FN: &str =
    "trust_cg_ay_batch_subsumption_repeated_checksum_backend";
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
const TRUST_CG_PROBE_BATCHES_PER_REPETITION: usize = 64;
const TRUST_CG_PROBE_WORKLOAD_BUCKET: &str = "fixture_mixed_2_16_probe";
const TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION: &str = "profile_only_non_promoting";
const TRUST_CG_REFERENCE_PROMOTION_DISPOSITION: &str = "reference_only";
const TRUST_CG_BACKEND_PROMOTION_DISPOSITION: &str = "backend_candidate";
const TRUST_CG_BACKEND_SCALAR_CONTROL_PROMOTION_DISPOSITION: &str = "scalar_control_non_promoting";
const TRUST_CG_PENDING_PROMOTION_DISPOSITION: &str = "not_evidence";
const TRUST_CG_PROBE_MIXED_ROW_STATUS: &str = "trust_cg_profile_only_probe_mixed_measured";
const TRUST_CG_PROBE_BUCKET_ROW_STATUS: &str = "trust_cg_profile_only_probe_bucket_measured";
const TRUST_CG_BACKEND_MIXED_ROW_STATUS: &str = "trust_cg_backend_mixed_measured";
const TRUST_CG_BACKEND_BUCKET_ROW_STATUS: &str = "trust_cg_backend_bucket_measured";
const TRUST_CG_BACKEND_SCALAR_EQUIVALENT_PROFITABILITY_STATUS: &str =
    "scalar_equivalent_not_slower_than_scalar_control";
const TRUST_CG_CONTAINS4_SCALAR_BACKEND_SHAPE: &str = "scalar_contains4";
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
const TRUST_CG_CONTAINS4_SCANNER_MEMORY_BACKEND_SHAPE: &str = "scanner_memory_contains4_rewrite";
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
const TRUST_CG_CONTAINS4_INLINED_BATCH_BACKEND_SHAPE: &str = "inlined_batch_contains4_scanner";
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
const TRUST_CG_CONTAINS4_SCALAR_ARGUMENT_BACKEND_SHAPE: &str = "scalar_argument_contains4_rewrite";
const TRUST_CG_CONTAINS4_UNKNOWN_BACKEND_SHAPE: &str = "unknown_contains4_shape";
#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
#[derive(Clone, Debug)]
struct TrustCgPaddedChunk {
    clause_id: usize,
    chunk_start_lane: usize,
    lanes: [i32; 4],
    valid_mask: u8,
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
#[derive(Clone, Debug)]
struct TrustCgPaddedChunkArena {
    chunks: Vec<TrustCgPaddedChunk>,
    ranges_by_clause_id: BTreeMap<usize, std::ops::Range<usize>>,
    sentinel: i32,
    flat_lanes: Vec<i32>,
    chunk_valid_masks: Vec<u8>,
    start_chunks: Vec<u32>,
    end_chunks: Vec<u32>,
    clause_ids: Vec<u32>,
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
#[derive(Clone, Debug)]
struct TrustCgPaddedChunkScannerView {
    start_chunks: Vec<u32>,
    end_chunks: Vec<u32>,
    clause_ids: Vec<u32>,
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
impl TrustCgPaddedChunkScannerView {
    fn len(&self) -> usize {
        self.clause_ids.len()
    }
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
#[derive(Clone, Debug)]
struct TrustCgSubsumptionScannerBatch {
    a_start_chunks: Vec<u32>,
    a_end_chunks: Vec<u32>,
    b_start_chunks: Vec<u32>,
    b_end_chunks: Vec<u32>,
    records: Vec<u32>,
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
impl TrustCgSubsumptionScannerBatch {
    fn len(&self) -> usize {
        self.a_start_chunks.len()
    }
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
impl TrustCgPaddedChunkArena {
    fn new(cases: &AYSubsumptionCases) -> Self {
        let mut chunks = Vec::new();
        let mut ranges_by_clause_id = BTreeMap::new();
        let mut flat_lanes = Vec::new();
        let mut chunk_valid_masks = Vec::new();
        let mut start_chunks = Vec::new();
        let mut end_chunks = Vec::new();
        let mut clause_ids = Vec::new();

        for clause in &cases.clauses {
            let start = chunks.len();
            for chunk_start_lane in (0..clause.padded_length).step_by(4) {
                let mut lanes = [cases.sentinel; 4];
                let mut valid_mask = 0u8;
                for (lane_offset, lane) in lanes.iter_mut().enumerate() {
                    let lane_index = chunk_start_lane + lane_offset;
                    if lane_index < clause.length {
                        *lane = clause.lits[lane_index];
                        valid_mask |= 1 << lane_offset;
                    }
                }
                chunks.push(TrustCgPaddedChunk {
                    clause_id: clause.id,
                    chunk_start_lane,
                    lanes,
                    valid_mask,
                });
                flat_lanes.extend_from_slice(&lanes);
                chunk_valid_masks.push(valid_mask);
            }
            let end = chunks.len();
            ranges_by_clause_id.insert(clause.id, start..end);
            start_chunks.push(u32::try_from(start).expect("chunk arena start fits u32"));
            end_chunks.push(u32::try_from(end).expect("chunk arena end fits u32"));
            clause_ids.push(u32::try_from(clause.id).expect("clause id fits u32"));
        }

        Self {
            chunks,
            ranges_by_clause_id,
            sentinel: cases.sentinel,
            flat_lanes,
            chunk_valid_masks,
            start_chunks,
            end_chunks,
            clause_ids,
        }
    }

    fn chunks_for_clause(&self, clause_id: usize) -> &[TrustCgPaddedChunk] {
        let range = self
            .ranges_by_clause_id
            .get(&clause_id)
            .unwrap_or_else(|| panic!("missing padded chunk arena entry for clause {clause_id}"));
        &self.chunks[range.clone()]
    }

    fn scanner_view(&self) -> TrustCgPaddedChunkScannerView {
        TrustCgPaddedChunkScannerView {
            start_chunks: self.start_chunks.clone(),
            end_chunks: self.end_chunks.clone(),
            clause_ids: self.clause_ids.clone(),
        }
    }

    fn scanner_view_for_clauses(&self, clauses: &[&ClauseCase]) -> TrustCgPaddedChunkScannerView {
        let mut start_chunks = Vec::with_capacity(clauses.len());
        let mut end_chunks = Vec::with_capacity(clauses.len());
        let mut clause_ids = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let range = self.ranges_by_clause_id.get(&clause.id).unwrap_or_else(|| {
                panic!("missing padded chunk arena entry for clause {}", clause.id)
            });
            start_chunks.push(u32::try_from(range.start).expect("chunk arena start fits u32"));
            end_chunks.push(u32::try_from(range.end).expect("chunk arena end fits u32"));
            clause_ids.push(u32::try_from(clause.id).expect("clause id fits u32"));
        }
        TrustCgPaddedChunkScannerView {
            start_chunks,
            end_chunks,
            clause_ids,
        }
    }

    fn subsumption_scanner_batch_for_pairs(
        &self,
        pairs: &[(usize, usize)],
    ) -> TrustCgSubsumptionScannerBatch {
        let mut a_start_chunks = Vec::with_capacity(pairs.len());
        let mut a_end_chunks = Vec::with_capacity(pairs.len());
        let mut b_start_chunks = Vec::with_capacity(pairs.len());
        let mut b_end_chunks = Vec::with_capacity(pairs.len());
        let mut records = Vec::with_capacity(pairs.len() * 6);
        for &(a_clause_id, b_clause_id) in pairs {
            let a_range = self
                .ranges_by_clause_id
                .get(&a_clause_id)
                .unwrap_or_else(|| {
                    panic!("missing padded chunk arena entry for clause {a_clause_id}")
                });
            let b_range = self
                .ranges_by_clause_id
                .get(&b_clause_id)
                .unwrap_or_else(|| {
                    panic!("missing padded chunk arena entry for clause {b_clause_id}")
                });
            a_start_chunks.push(u32::try_from(a_range.start).expect("chunk arena start fits u32"));
            a_end_chunks.push(u32::try_from(a_range.end).expect("chunk arena end fits u32"));
            b_start_chunks.push(u32::try_from(b_range.start).expect("chunk arena start fits u32"));
            b_end_chunks.push(u32::try_from(b_range.end).expect("chunk arena end fits u32"));
            records.extend([
                u32::try_from(a_range.start).expect("chunk arena start fits u32"),
                u32::try_from(a_range.end).expect("chunk arena end fits u32"),
                u32::try_from(b_range.start).expect("chunk arena start fits u32"),
                u32::try_from(b_range.end).expect("chunk arena end fits u32"),
                u32::try_from(a_clause_id).expect("clause id fits u32"),
                u32::try_from(b_clause_id).expect("clause id fits u32"),
            ]);
        }
        TrustCgSubsumptionScannerBatch {
            a_start_chunks,
            a_end_chunks,
            b_start_chunks,
            b_end_chunks,
            records,
        }
    }

    #[cfg(test)]
    fn scanner_contains_literal_scalar(
        &self,
        view: &TrustCgPaddedChunkScannerView,
        literal: i32,
        scratch: &mut [u32],
    ) -> usize {
        assert!(
            scratch.len() >= view.len(),
            "scanner scratch must hold one id per selected clause"
        );
        let mut match_count = 0usize;
        for ((start_chunk, end_chunk), clause_id) in view
            .start_chunks
            .iter()
            .zip(&view.end_chunks)
            .zip(&view.clause_ids)
        {
            let contains = (*start_chunk..*end_chunk).any(|chunk_index| {
                let base = usize::try_from(chunk_index).expect("chunk index fits usize") * 4;
                let mask = self.chunk_valid_masks
                    [usize::try_from(chunk_index).expect("chunk index fits usize")];
                (0..4).any(|lane_offset| {
                    (mask & (1 << lane_offset)) != 0
                        && self.flat_lanes[base + lane_offset] == literal
                })
            });
            if contains {
                scratch[match_count] = *clause_id;
                match_count += 1;
            }
        }
        match_count
    }

    #[cfg(test)]
    fn scanner_batch_subsumption_scalar(
        &self,
        batch: &TrustCgSubsumptionScannerBatch,
        out_results: &mut [u8],
    ) -> usize {
        assert!(
            out_results.len() >= batch.len(),
            "subsumption scanner output must hold one byte per pair"
        );
        let mut true_count = 0usize;
        for (pair_index, result) in out_results.iter_mut().enumerate().take(batch.len()) {
            let actual = self.chunk_range_subsumes_scalar(
                batch.a_start_chunks[pair_index],
                batch.a_end_chunks[pair_index],
                batch.b_start_chunks[pair_index],
                batch.b_end_chunks[pair_index],
            );
            *result = u8::from(actual);
            true_count += usize::from(actual);
        }
        true_count
    }

    #[cfg(test)]
    fn chunk_range_subsumes_scalar(
        &self,
        a_start_chunk: u32,
        a_end_chunk: u32,
        b_start_chunk: u32,
        b_end_chunk: u32,
    ) -> bool {
        for a_chunk_index in a_start_chunk..a_end_chunk {
            let a_chunk_index = usize::try_from(a_chunk_index).expect("chunk index fits usize");
            let a_base = a_chunk_index * 4;
            let a_mask = self.chunk_valid_masks[a_chunk_index];
            for lane_offset in 0..4 {
                if a_mask & (1 << lane_offset) == 0 {
                    continue;
                }
                if !self.chunk_range_contains_literal_scalar(
                    b_start_chunk,
                    b_end_chunk,
                    self.flat_lanes[a_base + lane_offset],
                ) {
                    return false;
                }
            }
        }
        true
    }

    #[cfg(test)]
    fn chunk_range_contains_literal_scalar(
        &self,
        start_chunk: u32,
        end_chunk: u32,
        literal: i32,
    ) -> bool {
        (start_chunk..end_chunk).any(|chunk_index| {
            let chunk_index = usize::try_from(chunk_index).expect("chunk index fits usize");
            let base = chunk_index * 4;
            let mask = self.chunk_valid_masks[chunk_index];
            (0..4).any(|lane_offset| {
                mask & (1 << lane_offset) != 0 && self.flat_lanes[base + lane_offset] == literal
            })
        })
    }

    #[cfg(test)]
    fn clause_contains_scalar(&self, clause_id: usize, literal: i32) -> bool {
        self.chunks_for_clause(clause_id)
            .iter()
            .any(|chunk| contains4_expected_mask(chunk, literal) != 0)
    }
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
#[derive(Clone, Debug)]
struct TrustCgContains4ProbeCase {
    chunk: TrustCgPaddedChunk,
    literal: i32,
    expected_mask: i32,
}

fn trust_cg_variant_probe_mode(variant: &str) -> (&'static str, &'static str) {
    let opt_level = if variant.contains("_o3_") {
        "O3"
    } else if variant.contains("_o2_") {
        "O2"
    } else {
        "unknown"
    };
    let vectorizer_mode = if variant.contains("disable_vec") {
        "TRUST_CG_DISABLE_PASSES=vec"
    } else {
        "vectorizer_enabled"
    };
    (opt_level, vectorizer_mode)
}

fn trust_cg_backend_row_evidence_disposition(variant: &str) -> (&'static str, bool) {
    if trust_cg_scalar_control_variant(variant).is_some() {
        (TRUST_CG_BACKEND_PROMOTION_DISPOSITION, true)
    } else {
        (TRUST_CG_BACKEND_SCALAR_CONTROL_PROMOTION_DISPOSITION, false)
    }
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
fn trust_cg_contains4_probe_cases(cases: &AYSubsumptionCases) -> Vec<TrustCgContains4ProbeCase> {
    let arena = TrustCgPaddedChunkArena::new(cases);
    trust_cg_contains4_probe_cases_from_arena(cases, &arena)
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
fn trust_cg_contains4_probe_cases_from_arena(
    cases: &AYSubsumptionCases,
    arena: &TrustCgPaddedChunkArena,
) -> Vec<TrustCgContains4ProbeCase> {
    arena
        .chunks
        .iter()
        .cloned()
        .flat_map(|chunk| {
            cases.contains_queries.iter().map(move |query| {
                let expected_mask = contains4_expected_mask(&chunk, query.literal);
                TrustCgContains4ProbeCase {
                    chunk: chunk.clone(),
                    literal: query.literal,
                    expected_mask,
                }
            })
        })
        .collect()
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
fn trust_cg_contains4_scalar_control_cases(
    cases: &AYSubsumptionCases,
) -> Vec<TrustCgContains4ProbeCase> {
    let mut direct_cases = Vec::new();
    let literal = 0x5a5a_i32;
    for valid_mask in 0u8..=0b1111 {
        for match_mask in 0u8..=0b1111 {
            let mut lanes = [cases.sentinel; 4];
            for (lane_offset, lane) in lanes.iter_mut().enumerate() {
                let lane_bit = 1u8 << lane_offset;
                if valid_mask & lane_bit != 0 {
                    *lane = if match_mask & lane_bit != 0 {
                        literal
                    } else {
                        literal + lane_offset as i32 + 1
                    };
                }
            }
            let chunk = TrustCgPaddedChunk {
                clause_id: 0,
                chunk_start_lane: usize::from(valid_mask) * 16 + usize::from(match_mask),
                lanes,
                valid_mask,
            };
            direct_cases.push(TrustCgContains4ProbeCase {
                expected_mask: contains4_expected_mask(&chunk, literal),
                chunk,
                literal,
            });
        }
    }

    for valid_mask in 0u8..=0b1111 {
        let mut lanes = [cases.sentinel; 4];
        for (lane_offset, lane) in lanes.iter_mut().enumerate() {
            let lane_bit = 1u8 << lane_offset;
            if valid_mask & lane_bit != 0 {
                *lane = 0x7000_i32 + lane_offset as i32;
            }
        }
        let chunk = TrustCgPaddedChunk {
            clause_id: 0,
            chunk_start_lane: 0x100 + usize::from(valid_mask),
            lanes,
            valid_mask,
        };
        direct_cases.push(TrustCgContains4ProbeCase {
            expected_mask: contains4_expected_mask(&chunk, cases.sentinel),
            chunk,
            literal: cases.sentinel,
        });
    }

    direct_cases.extend(trust_cg_contains4_probe_cases(cases));
    direct_cases
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
fn contains4_expected_mask(chunk: &TrustCgPaddedChunk, literal: i32) -> i32 {
    let mut mask = 0i32;
    for lane_offset in 0..4 {
        let lane_bit = 1u8 << lane_offset;
        if chunk.valid_mask & lane_bit != 0 && chunk.lanes[lane_offset] == literal {
            mask |= i32::from(lane_bit);
        }
    }
    mask
}

#[cfg(any(
    test,
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))
))]
fn clause_by_id(cases: &AYSubsumptionCases, clause_id: usize) -> Option<&ClauseCase> {
    cases.clauses.iter().find(|clause| clause.id == clause_id)
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn contains4_chunk_mismatch(
    case: &TrustCgContains4ProbeCase,
    actual_mask: i32,
) -> TrustCgBackendProbeMismatch {
    TrustCgBackendProbeMismatch {
        operation: "contains4_chunk",
        clause_id: Some(case.chunk.clause_id),
        pair_a: None,
        pair_b: None,
        chunk_start_lane: Some(case.chunk.chunk_start_lane),
        lanes: Some(case.chunk.lanes),
        valid_mask: Some(case.chunk.valid_mask),
        literal: Some(case.literal),
        expected_clause_ids: None,
        actual_clause_ids: None,
        expected_bool: None,
        actual_bool: None,
        expected_mask: Some(case.expected_mask),
        actual_mask: Some(actual_mask),
    }
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn contains_query_mismatch(
    literal: i32,
    expected_clause_ids: Vec<usize>,
    actual_clause_ids: Vec<usize>,
) -> TrustCgBackendProbeMismatch {
    TrustCgBackendProbeMismatch {
        operation: "contains_literal",
        clause_id: None,
        pair_a: None,
        pair_b: None,
        chunk_start_lane: None,
        lanes: None,
        valid_mask: None,
        literal: Some(literal),
        expected_clause_ids: Some(expected_clause_ids),
        actual_clause_ids: Some(actual_clause_ids),
        expected_bool: None,
        actual_bool: None,
        expected_mask: None,
        actual_mask: None,
    }
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn subsumption_mismatch(pair: &SubsumptionPair, actual: bool) -> TrustCgBackendProbeMismatch {
    TrustCgBackendProbeMismatch {
        operation: "batch_subsumption",
        clause_id: None,
        pair_a: Some(pair.a),
        pair_b: Some(pair.b),
        chunk_start_lane: None,
        lanes: None,
        valid_mask: None,
        literal: None,
        expected_clause_ids: None,
        actual_clause_ids: None,
        expected_bool: Some(pair.expected),
        actual_bool: Some(actual),
        expected_mask: None,
        actual_mask: None,
    }
}

fn trust_cg_probe_unavailable_row(
    variant: &str,
    status: &'static str,
    error_code: Option<&'static str>,
    message: String,
) -> TrustCgBackendProbeRow {
    let (opt_level, vectorizer_mode) = trust_cg_variant_probe_mode(variant);
    TrustCgBackendProbeRow {
        variant: variant.to_string(),
        backend_kind: "trust_cg_jit_scanner_probe",
        promotion_disposition: TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION,
        product_install_evidence: false,
        opt_level,
        vectorizer_mode,
        status,
        error_code,
        function_name: TRUST_CG_CONTAINS4_MASKED_PROBE_FN,
        checked_cases: 0,
        chunk_mismatch_count: 0,
        contains_query_count: 0,
        contains_mismatch_count: 0,
        subsumption_pair_count: 0,
        subsumption_mismatch_count: 0,
        mismatches: Vec::new(),
        operation_measurements: Vec::new(),
        timed_calls: 0,
        elapsed_ns: None,
        calls_per_us: None,
        message,
    }
}

fn trust_cg_backend_unavailable_row(
    variant: &str,
    status: &'static str,
    error_code: Option<&'static str>,
    message: String,
) -> TrustCgBackendExecutionRow {
    let (opt_level, vectorizer_mode) = trust_cg_variant_probe_mode(variant);
    TrustCgBackendExecutionRow {
        variant: variant.to_string(),
        backend_kind: "trust_cg_o2_o3_pipeline_jit_scanner",
        opt_level,
        vectorizer_mode,
        disabled_passes: trust_cg_backend_disabled_passes_for_variant(variant),
        contains4_backend_shape: TRUST_CG_CONTAINS4_UNKNOWN_BACKEND_SHAPE,
        status,
        error_code,
        function_name: TRUST_CG_CONTAINS4_MASKED_BACKEND_FN,
        checked_cases: 0,
        chunk_mismatch_count: 0,
        contains_query_count: 0,
        contains_mismatch_count: 0,
        subsumption_pair_count: 0,
        subsumption_mismatch_count: 0,
        mismatches: Vec::new(),
        operation_measurements: Vec::new(),
        message,
    }
}

fn trust_cg_contains4_scalar_control_pairs() -> [(&'static str, &'static str); 2] {
    [
        ("trust_cg_o2_vectorized", "trust_cg_o2_disable_vec"),
        ("trust_cg_o3_vectorized", "trust_cg_o3_disable_vec"),
    ]
}

fn trust_cg_contains4_scalar_control_unavailable_comparison(
    vectorized_variant: &str,
    scalar_control_variant: &str,
    status: &'static str,
    error_code: Option<&'static str>,
    message: String,
) -> TrustCgContains4ScalarControlComparison {
    let (opt_level, _) = trust_cg_variant_probe_mode(vectorized_variant);
    TrustCgContains4ScalarControlComparison {
        vectorized_variant: vectorized_variant.to_string(),
        scalar_control_variant: scalar_control_variant.to_string(),
        opt_level,
        status,
        error_code,
        checked_cases: 0,
        mismatch_count: 0,
        mismatches: Vec::new(),
        message,
    }
}

fn trust_cg_backend_profitability_comparisons(
    rows: &[TrustCgBackendExecutionRow],
) -> Vec<TrustCgBackendProfitabilityComparison> {
    let rows_by_variant = rows
        .iter()
        .map(|row| (row.variant.as_str(), row))
        .collect::<BTreeMap<_, _>>();
    let mut comparisons = Vec::new();

    for row in rows {
        let Some(scalar_variant) = trust_cg_scalar_control_variant(&row.variant) else {
            continue;
        };
        let Some(scalar_row) = rows_by_variant.get(scalar_variant) else {
            continue;
        };

        for measurement in &row.operation_measurements {
            if measurement.status != "backend_measured" {
                continue;
            }
            let vectorized_mean = measurement.mean_throughput_per_us;
            let scalar_measurement = scalar_row.operation_measurements.iter().find(|candidate| {
                candidate.operation == measurement.operation
                    && candidate.workload_bucket == measurement.workload_bucket
                    && candidate.status == "backend_measured"
            });
            let scalar_mean =
                scalar_measurement.and_then(|candidate| candidate.mean_throughput_per_us);
            let speedup = match (vectorized_mean, scalar_mean) {
                (Some(vectorized_mean), Some(scalar_mean)) if scalar_mean != 0.0 => {
                    Some(vectorized_mean / scalar_mean)
                }
                _ => None,
            };
            let scalar_equivalent = row.contains4_backend_shape
                == TRUST_CG_CONTAINS4_SCALAR_BACKEND_SHAPE
                && scalar_row.contains4_backend_shape == TRUST_CG_CONTAINS4_SCALAR_BACKEND_SHAPE
                && speedup.is_some();
            let status = match (speedup, scalar_equivalent) {
                (Some(_), true) => TRUST_CG_BACKEND_SCALAR_EQUIVALENT_PROFITABILITY_STATUS,
                (Some(speedup), false) if speedup >= 1.0 => {
                    "vectorized_not_slower_than_scalar_control"
                }
                (Some(_), false) => "vectorized_slower_than_scalar_control",
                (None, _) => "scalar_control_measurement_unavailable",
            };
            let message = match (vectorized_mean, scalar_mean, speedup, scalar_equivalent) {
                (Some(vectorized_mean), Some(scalar_mean), Some(speedup), true) => format!(
                    "Measured {} bucket {}: {} throughput {:.6}/us, {} throughput {:.6}/us, measured scalar-control speedup {:.6}. Both prepared backend rows have structural shape {}, so the default gated path is treated as scalar-equivalent/not-slower by construction.",
                    measurement.operation,
                    measurement.workload_bucket,
                    row.variant,
                    vectorized_mean,
                    scalar_variant,
                    scalar_mean,
                    speedup,
                    TRUST_CG_CONTAINS4_SCALAR_BACKEND_SHAPE
                ),
                (Some(vectorized_mean), Some(scalar_mean), Some(speedup), false) => format!(
                    "Measured {} bucket {}: {} throughput {:.6}/us, {} throughput {:.6}/us, scalar-control speedup {:.6}. This records profitability telemetry only; it does not assert a speedup gate.",
                    measurement.operation,
                    measurement.workload_bucket,
                    row.variant,
                    vectorized_mean,
                    scalar_variant,
                    scalar_mean,
                    speedup
                ),
                _ => format!(
                    "Missing comparable scalar-control measurement for {} bucket {} in {} vs {}.",
                    measurement.operation, measurement.workload_bucket, row.variant, scalar_variant
                ),
            };
            comparisons.push(TrustCgBackendProfitabilityComparison {
                operation: measurement.operation,
                workload_bucket: measurement.workload_bucket.clone(),
                vectorized_variant: row.variant.clone(),
                scalar_control_variant: scalar_variant.to_string(),
                vectorized_mean_throughput_per_us: vectorized_mean,
                scalar_control_mean_throughput_per_us: scalar_mean,
                scalar_speedup: speedup,
                status,
                message,
            });
        }
    }

    comparisons
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
type Contains4MaskedProbe = extern "C" fn(*const i32, i32, i32) -> i32;

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
type ContainsLiteralScannerBackend =
    extern "C" fn(*const i32, *const u32, *const u32, *const u32, u32, i32, i32, *mut u32) -> u32;

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
type ContainsLiteralQueryBatchBackend =
    extern "C" fn(*const i32, *const u32, *const u32, *const u32, u32, *const i32, u32, i32) -> u64;

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
type BatchSubsumptionScannerBackend = extern "C" fn(
    *const i32,
    *const u8,
    *const u32,
    *const u32,
    *const u32,
    *const u32,
    u32,
    *mut u8,
) -> u32;

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
type BatchSubsumptionRepeatedChecksumBackend =
    extern "C" fn(*const i32, *const u8, *const u32, u32, u32, *mut u8) -> u64;

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn call_contains4_masked(
    contains4: &Contains4MaskedProbe,
    chunk: &TrustCgPaddedChunk,
    literal: i32,
) -> i32 {
    contains4(chunk.lanes.as_ptr(), literal, i32::from(chunk.valid_mask))
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn call_contains_literal_scanner(
    scanner: &ContainsLiteralScannerBackend,
    arena: &TrustCgPaddedChunkArena,
    view: &TrustCgPaddedChunkScannerView,
    literal: i32,
    scratch: &mut [u32],
) -> usize {
    assert!(
        scratch.len() >= view.len(),
        "scanner scratch must hold one id per selected clause"
    );
    let match_count = scanner(
        arena.flat_lanes.as_ptr(),
        view.start_chunks.as_ptr(),
        view.end_chunks.as_ptr(),
        view.clause_ids.as_ptr(),
        u32::try_from(view.len()).expect("scanner view length fits u32"),
        literal,
        arena.sentinel,
        scratch.as_mut_ptr(),
    );
    let match_count = usize::try_from(match_count).expect("scanner match count fits usize");
    assert!(
        match_count <= scratch.len(),
        "scanner returned more matches than scratch capacity"
    );
    match_count
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn call_contains_literal_query_batch_scanner(
    scanner: &ContainsLiteralQueryBatchBackend,
    arena: &TrustCgPaddedChunkArena,
    view: &TrustCgPaddedChunkScannerView,
    query_literals: &[i32],
) -> u64 {
    scanner(
        arena.flat_lanes.as_ptr(),
        view.start_chunks.as_ptr(),
        view.end_chunks.as_ptr(),
        view.clause_ids.as_ptr(),
        u32::try_from(view.len()).expect("scanner view length fits u32"),
        query_literals.as_ptr(),
        u32::try_from(query_literals.len()).expect("query literal count fits u32"),
        arena.sentinel,
    )
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn call_batch_subsumption_scanner(
    scanner: &BatchSubsumptionScannerBackend,
    arena: &TrustCgPaddedChunkArena,
    batch: &TrustCgSubsumptionScannerBatch,
    out_results: &mut [u8],
) -> usize {
    assert!(
        out_results.len() >= batch.len(),
        "subsumption scanner output must hold one byte per pair"
    );
    let true_count = scanner(
        arena.flat_lanes.as_ptr(),
        arena.chunk_valid_masks.as_ptr(),
        batch.a_start_chunks.as_ptr(),
        batch.a_end_chunks.as_ptr(),
        batch.b_start_chunks.as_ptr(),
        batch.b_end_chunks.as_ptr(),
        u32::try_from(batch.len()).expect("subsumption batch length fits u32"),
        out_results.as_mut_ptr(),
    );
    let true_count = usize::try_from(true_count).expect("subsumption true count fits usize");
    assert!(
        true_count <= batch.len(),
        "subsumption scanner returned more true results than pairs"
    );
    true_count
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn call_batch_subsumption_repeated_checksum_scanner(
    scanner: &BatchSubsumptionRepeatedChecksumBackend,
    arena: &TrustCgPaddedChunkArena,
    batch: &TrustCgSubsumptionScannerBatch,
    repetitions: usize,
    out_results: &mut [u8],
) -> u64 {
    assert!(
        out_results.len() >= batch.len(),
        "subsumption scanner output must hold one byte per pair"
    );
    assert_eq!(
        batch.records.len(),
        batch.len() * 6,
        "subsumption checksum records must hold six u32 fields per pair"
    );
    scanner(
        arena.flat_lanes.as_ptr(),
        arena.chunk_valid_masks.as_ptr(),
        batch.records.as_ptr(),
        u32::try_from(batch.len()).expect("subsumption batch length fits u32"),
        u32::try_from(repetitions).expect("subsumption repetition count fits u32"),
        out_results.as_mut_ptr(),
    )
}

fn trust_cg_backend_disabled_passes_for_variant(variant: &str) -> Option<&'static str> {
    variant.contains("disable_vec").then_some("vec")
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn trust_cg_backend_enables_contains4_batch_scanner(variant: &str) -> bool {
    trust_cg_scalar_control_variant(variant).is_some()
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn trust_cg_contains4_backend_shape(func: &trust_cg_ir::MachFunction) -> &'static str {
    let opcode_count = |opcode| {
        func.block_order
            .iter()
            .flat_map(|block| func.block(*block).insts.iter().copied())
            .filter(|inst_id| func.inst(*inst_id).opcode == opcode)
            .count()
    };
    let ld1_count = opcode_count(trust_cg_ir::AArch64Opcode::NeonLd1Post);
    let cmeq_count = opcode_count(trust_cg_ir::AArch64Opcode::NeonCmeqV);
    let ins_count = opcode_count(trust_cg_ir::AArch64Opcode::NeonInsGen);
    let call_count = opcode_count(trust_cg_ir::AArch64Opcode::Bl)
        + opcode_count(trust_cg_ir::AArch64Opcode::Blr)
        + opcode_count(trust_cg_ir::AArch64Opcode::BL)
        + opcode_count(trust_cg_ir::AArch64Opcode::BLR);

    if ld1_count > 0 && cmeq_count > 0 && call_count == 0 {
        TRUST_CG_CONTAINS4_INLINED_BATCH_BACKEND_SHAPE
    } else if ld1_count > 0 && cmeq_count > 0 {
        TRUST_CG_CONTAINS4_SCANNER_MEMORY_BACKEND_SHAPE
    } else if cmeq_count > 0 || ins_count > 0 {
        TRUST_CG_CONTAINS4_SCALAR_ARGUMENT_BACKEND_SHAPE
    } else {
        TRUST_CG_CONTAINS4_SCALAR_BACKEND_SHAPE
    }
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn trust_cg_probe_opt_level(variant: &str) -> trust_cg_codegen::pipeline::OptLevel {
    if variant.contains("_o3_") {
        trust_cg_codegen::pipeline::OptLevel::O3
    } else {
        trust_cg_codegen::pipeline::OptLevel::O2
    }
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn run_trust_cg_backend_probe_row(
    cases: &AYSubsumptionCases,
    variant: &str,
    length_buckets: &[String],
) -> TrustCgBackendProbeRow {
    match execute_trust_cg_backend_probe_row(cases, variant, length_buckets) {
        Ok(row) => row,
        Err(message) => trust_cg_probe_unavailable_row(
            variant,
            "padded_scanner_probe_unavailable",
            Some("trust_cg_jit_probe_failed"),
            message,
        ),
    }
}

#[cfg(not(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))))]
fn run_trust_cg_backend_probe_row(
    _cases: &AYSubsumptionCases,
    variant: &str,
    _length_buckets: &[String],
) -> TrustCgBackendProbeRow {
    trust_cg_probe_unavailable_row(
        variant,
        "padded_scanner_probe_unavailable",
        Some("trust_cg_jit_probe_host_unsupported"),
        format!(
            "Trust Codegen raw AArch64 JIT scanner probe is supported on aarch64 macOS/Linux only; host is {}-{}",
            std::env::consts::ARCH,
            std::env::consts::OS
        ),
    )
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn run_trust_cg_backend_execution_row(
    cases: &AYSubsumptionCases,
    variant: &str,
    length_buckets: &[String],
) -> TrustCgBackendExecutionRow {
    match execute_trust_cg_backend_execution_row(cases, variant, length_buckets) {
        Ok(row) => row,
        Err(message) => trust_cg_backend_unavailable_row(
            variant,
            "trust_cg_backend_unavailable",
            Some("trust_cg_backend_execution_failed"),
            message,
        ),
    }
}

#[cfg(not(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))))]
fn run_trust_cg_backend_execution_row(
    _cases: &AYSubsumptionCases,
    variant: &str,
    _length_buckets: &[String],
) -> TrustCgBackendExecutionRow {
    trust_cg_backend_unavailable_row(
        variant,
        "trust_cg_backend_unavailable",
        Some("trust_cg_backend_host_unsupported"),
        format!(
            "Trust Codegen O2/O3 AArch64 backend rows are supported on aarch64 macOS/Linux only; host is {}-{}",
            std::env::consts::ARCH,
            std::env::consts::OS
        ),
    )
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn prepare_trust_cg_contains4_masked_backend_function(
    variant: &str,
) -> Result<trust_cg_ir::MachFunction, String> {
    let opt_level = trust_cg_probe_opt_level(variant);
    let disabled_passes = trust_cg_backend_disabled_passes_for_variant(variant);
    let mut func = build_trust_cg_contains4_masked_backend_function();
    let pipeline =
        trust_cg_codegen::pipeline::Pipeline::new(trust_cg_codegen::pipeline::PipelineConfig {
            opt_level,
            verify: false,
            verify_dispatch: trust_cg_codegen::pipeline::DispatchVerifyMode::Off,
            disabled_passes_override: Some(disabled_passes.unwrap_or_default().to_string()),
            contains4_scanner_batch_rewrite_override: Some(
                trust_cg_backend_enables_contains4_batch_scanner(variant),
            ),
            ..trust_cg_codegen::pipeline::PipelineConfig::default()
        });
    pipeline.prepare_ir_function(&mut func).map_err(|err| {
        format!("Trust Codegen backend prepare_ir_function failed for {variant}: {err}")
    })?;
    Ok(func)
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn run_trust_cg_contains4_scalar_control_comparisons(
    cases: &AYSubsumptionCases,
) -> Vec<TrustCgContains4ScalarControlComparison> {
    trust_cg_contains4_scalar_control_pairs()
        .into_iter()
        .map(|(vectorized_variant, scalar_control_variant)| {
            match execute_trust_cg_contains4_scalar_control_comparison(
                cases,
                vectorized_variant,
                scalar_control_variant,
            ) {
                Ok(comparison) => comparison,
                Err(message) => trust_cg_contains4_scalar_control_unavailable_comparison(
                    vectorized_variant,
                    scalar_control_variant,
                    "scalar_control_comparison_unavailable",
                    Some("trust_cg_scalar_control_comparison_failed"),
                    message,
                ),
            }
        })
        .collect()
}

#[cfg(not(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))))]
fn run_trust_cg_contains4_scalar_control_comparisons(
    _cases: &AYSubsumptionCases,
) -> Vec<TrustCgContains4ScalarControlComparison> {
    trust_cg_contains4_scalar_control_pairs()
        .into_iter()
        .map(|(vectorized_variant, scalar_control_variant)| {
            trust_cg_contains4_scalar_control_unavailable_comparison(
                vectorized_variant,
                scalar_control_variant,
                "scalar_control_comparison_unavailable",
                Some("trust_cg_backend_host_unsupported"),
                format!(
                    "Trust Codegen masked contains4 scalar-control comparison is supported on aarch64 macOS/Linux only; host is {}-{}",
                    std::env::consts::ARCH,
                    std::env::consts::OS
                ),
            )
        })
        .collect()
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_trust_cg_contains4_scalar_control_comparison(
    cases: &AYSubsumptionCases,
    vectorized_variant: &str,
    scalar_control_variant: &str,
) -> Result<TrustCgContains4ScalarControlComparison, String> {
    use std::collections::HashMap;

    let comparison_cases = trust_cg_contains4_scalar_control_cases(cases);
    if comparison_cases.is_empty() {
        return Err(
            "Trust Codegen masked contains4 scalar-control comparison has no cases".to_string(),
        );
    }

    let vectorized_func = prepare_trust_cg_contains4_masked_backend_function(vectorized_variant)?;
    let scalar_control_func =
        prepare_trust_cg_contains4_masked_backend_function(scalar_control_variant)?;
    let externs: HashMap<String, *const u8> = HashMap::new();

    let vectorized_jit = trust_cg_codegen::JitCompiler::new(trust_cg_codegen::JitConfig {
        opt_level: trust_cg_probe_opt_level(vectorized_variant),
        verify: false,
        verify_dispatch: trust_cg_codegen::DispatchVerifyMode::Off,
        ..trust_cg_codegen::JitConfig::default()
    });
    let vectorized_buffer = vectorized_jit
        .compile_raw(&[vectorized_func], &externs)
        .map_err(|err| {
            format!("Trust Codegen vectorized JIT compile failed for {vectorized_variant}: {err}")
        })?;
    let vectorized_guard = unsafe {
        vectorized_buffer
            .get_fn_bound::<Contains4MaskedProbe>(TRUST_CG_CONTAINS4_MASKED_BACKEND_FN)
            .ok_or_else(|| format!("missing JIT symbol {TRUST_CG_CONTAINS4_MASKED_BACKEND_FN}"))?
    };

    let scalar_control_jit = trust_cg_codegen::JitCompiler::new(trust_cg_codegen::JitConfig {
        opt_level: trust_cg_probe_opt_level(scalar_control_variant),
        verify: false,
        verify_dispatch: trust_cg_codegen::DispatchVerifyMode::Off,
        ..trust_cg_codegen::JitConfig::default()
    });
    let scalar_control_buffer = scalar_control_jit
        .compile_raw(&[scalar_control_func], &externs)
        .map_err(|err| {
            format!("Trust Codegen scalar-control JIT compile failed for {scalar_control_variant}: {err}")
        })?;
    let scalar_control_guard = unsafe {
        scalar_control_buffer
            .get_fn_bound::<Contains4MaskedProbe>(TRUST_CG_CONTAINS4_MASKED_BACKEND_FN)
            .ok_or_else(|| format!("missing JIT symbol {TRUST_CG_CONTAINS4_MASKED_BACKEND_FN}"))?
    };
    let vectorized = vectorized_guard.as_ref();
    let scalar_control = scalar_control_guard.as_ref();
    trust_cg_codegen::ensure_jit_execute_mode();

    let mut mismatches = Vec::new();
    for (case_index, case) in comparison_cases.iter().enumerate() {
        let vectorized_mask = call_contains4_masked(vectorized, &case.chunk, case.literal);
        let scalar_control_mask = call_contains4_masked(scalar_control, &case.chunk, case.literal);
        if vectorized_mask != scalar_control_mask || vectorized_mask != case.expected_mask {
            mismatches.push(TrustCgContains4ScalarControlMismatch {
                case_index,
                lanes: case.chunk.lanes,
                valid_mask: case.chunk.valid_mask,
                literal: case.literal,
                expected_mask: case.expected_mask,
                vectorized_mask,
                scalar_control_mask,
            });
        }
    }
    let mismatch_count = mismatches.len();
    let (opt_level, _) = trust_cg_variant_probe_mode(vectorized_variant);

    Ok(TrustCgContains4ScalarControlComparison {
        vectorized_variant: vectorized_variant.to_string(),
        scalar_control_variant: scalar_control_variant.to_string(),
        opt_level,
        status: if mismatch_count == 0 {
            "scalar_control_match"
        } else {
            "scalar_control_mismatch"
        },
        error_code: if mismatch_count == 0 {
            None
        } else {
            Some("trust_cg_scalar_control_mismatch")
        },
        checked_cases: comparison_cases.len(),
        mismatch_count,
        mismatches,
        message: format!(
            "Compared {vectorized_variant} against {scalar_control_variant} over {} direct masked contains4 cases covering all valid masks, all lane/literal match masks, sentinel-literal masking, and fixture padded chunks.",
            comparison_cases.len()
        ),
    })
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_trust_cg_backend_probe_row(
    cases: &AYSubsumptionCases,
    variant: &str,
    length_buckets: &[String],
) -> Result<TrustCgBackendProbeRow, String> {
    use std::collections::HashMap;

    let arena = TrustCgPaddedChunkArena::new(cases);
    let probe_cases = trust_cg_contains4_probe_cases_from_arena(cases, &arena);
    if probe_cases.is_empty() {
        return Err(
            "Trust Codegen masked contains4 probe has no fixture cases to execute".to_string(),
        );
    }

    let jit = trust_cg_codegen::JitCompiler::new(trust_cg_codegen::JitConfig {
        opt_level: trust_cg_probe_opt_level(variant),
        verify: false,
        verify_dispatch: trust_cg_codegen::DispatchVerifyMode::Off,
        ..trust_cg_codegen::JitConfig::default()
    });
    let func = build_trust_cg_contains4_masked_probe_function();
    let externs: HashMap<String, *const u8> = HashMap::new();
    let buffer = jit
        .compile_raw(&[func], &externs)
        .map_err(|err| format!("Trust Codegen JIT probe compile failed for {variant}: {err}"))?;
    let contains4_guard = unsafe {
        buffer
            .get_fn_bound::<Contains4MaskedProbe>(TRUST_CG_CONTAINS4_MASKED_PROBE_FN)
            .ok_or_else(|| format!("missing JIT symbol {TRUST_CG_CONTAINS4_MASKED_PROBE_FN}"))?
    };
    let contains4 = contains4_guard.as_ref();
    trust_cg_codegen::ensure_jit_execute_mode();

    let mut mismatches = Vec::new();
    for case in &probe_cases {
        let actual_mask = call_contains4_masked(contains4, &case.chunk, case.literal);
        if actual_mask != case.expected_mask {
            mismatches.push(contains4_chunk_mismatch(case, actual_mask));
        }
    }
    let chunk_mismatch_count = mismatches.len();

    for query in &cases.contains_queries {
        let actual_clause_ids = cases
            .clauses
            .iter()
            .filter(|clause| {
                trust_cg_probe_clause_contains(&arena, clause, query.literal, contains4)
            })
            .map(|clause| clause.id)
            .collect::<Vec<_>>();
        if actual_clause_ids != query.expected_clause_ids {
            mismatches.push(contains_query_mismatch(
                query.literal,
                query.expected_clause_ids.clone(),
                actual_clause_ids,
            ));
        }
    }
    let contains_mismatch_count = mismatches
        .iter()
        .filter(|mismatch| mismatch.operation == "contains_literal")
        .count();

    for pair in &cases.subsumption_pairs {
        let a = clause_by_id(cases, pair.a)
            .ok_or_else(|| format!("subsumption pair references missing clause {}", pair.a))?;
        let b = clause_by_id(cases, pair.b)
            .ok_or_else(|| format!("subsumption pair references missing clause {}", pair.b))?;
        let actual = a
            .lits
            .iter()
            .all(|literal| trust_cg_probe_clause_contains(&arena, b, *literal, contains4));
        if actual != pair.expected {
            mismatches.push(subsumption_mismatch(pair, actual));
        }
    }
    let subsumption_mismatch_count = mismatches
        .iter()
        .filter(|mismatch| mismatch.operation == "batch_subsumption")
        .count();

    let batches = 1_000usize;
    let timed_calls = probe_cases.len() * batches;
    let mut checksum = 0i32;
    let start = Instant::now();
    for _ in 0..batches {
        for case in &probe_cases {
            checksum ^= call_contains4_masked(contains4, &case.chunk, case.literal);
        }
    }
    std::hint::black_box(checksum);
    let elapsed_ns = start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
    let calls_per_us = if elapsed_ns == 0 {
        None
    } else {
        Some(timed_calls as f64 / (elapsed_ns as f64 / 1_000.0))
    };
    let operation_measurements =
        measure_trust_cg_probe_operations(cases, &arena, contains4, length_buckets);
    let operation_measurement_count = operation_measurements.len();
    let (opt_level, vectorizer_mode) = trust_cg_variant_probe_mode(variant);

    Ok(TrustCgBackendProbeRow {
        variant: variant.to_string(),
        backend_kind: "trust_cg_jit_scanner_probe",
        promotion_disposition: TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION,
        product_install_evidence: false,
        opt_level,
        vectorizer_mode,
        status: "padded_scanner_probe_executed",
        error_code: None,
        function_name: TRUST_CG_CONTAINS4_MASKED_PROBE_FN,
        checked_cases: probe_cases.len(),
        chunk_mismatch_count,
        contains_query_count: cases.contains_queries.len(),
        contains_mismatch_count,
        subsumption_pair_count: cases.subsumption_pairs.len(),
        subsumption_mismatch_count,
        mismatches,
        operation_measurements,
        timed_calls,
        elapsed_ns: Some(elapsed_ns),
        calls_per_us,
        message: format!(
            "Executed Trust Codegen raw-JIT masked contains4 scanner probe for {variant}: prebuilt {} padded chunks once for the row, checked {} padded chunk comparisons, {} containment queries, {} subsumption pairs, {} timed primitive calls, and {} profile-only/non-promoting operation timing rows. This is a backend smoke step, not installable product evidence or the full #571 O2/O3 throughput matrix.",
            arena.chunks.len(),
            probe_cases.len(),
            cases.contains_queries.len(),
            cases.subsumption_pairs.len(),
            timed_calls,
            operation_measurement_count
        ),
    })
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_trust_cg_backend_execution_row(
    cases: &AYSubsumptionCases,
    variant: &str,
    length_buckets: &[String],
) -> Result<TrustCgBackendExecutionRow, String> {
    use std::collections::HashMap;

    let arena = TrustCgPaddedChunkArena::new(cases);
    let probe_cases = trust_cg_contains4_probe_cases_from_arena(cases, &arena);
    if probe_cases.is_empty() {
        return Err(
            "Trust Codegen masked contains4 backend has no fixture cases to execute".to_string(),
        );
    }

    let opt_level = trust_cg_probe_opt_level(variant);
    let disabled_passes = trust_cg_backend_disabled_passes_for_variant(variant);
    let func = prepare_trust_cg_contains4_masked_backend_function(variant)?;
    let contains4_backend_shape = trust_cg_contains4_backend_shape(&func);
    let scanner_func = build_trust_cg_contains_literal_scanner_backend_function();
    let contains_query_batch_func = build_trust_cg_contains_literal_query_batch_backend_function();
    let subsumption_scanner_func = build_trust_cg_batch_subsumption_scanner_backend_function();
    let subsumption_repeated_checksum_func =
        build_trust_cg_batch_subsumption_repeated_checksum_backend_function();

    let jit = trust_cg_codegen::JitCompiler::new(trust_cg_codegen::JitConfig {
        opt_level,
        verify: false,
        verify_dispatch: trust_cg_codegen::DispatchVerifyMode::Off,
        ..trust_cg_codegen::JitConfig::default()
    });
    let externs: HashMap<String, *const u8> = HashMap::new();
    let buffer = jit
        .compile_raw(
            &[
                func,
                scanner_func,
                contains_query_batch_func,
                subsumption_scanner_func,
                subsumption_repeated_checksum_func,
            ],
            &externs,
        )
        .map_err(|err| format!("Trust Codegen backend JIT compile failed for {variant}: {err}"))?;
    let contains4_guard = unsafe {
        buffer
            .get_fn_bound::<Contains4MaskedProbe>(TRUST_CG_CONTAINS4_MASKED_BACKEND_FN)
            .ok_or_else(|| format!("missing JIT symbol {TRUST_CG_CONTAINS4_MASKED_BACKEND_FN}"))?
    };
    let contains_literal_scanner_guard = unsafe {
        buffer
            .get_fn_bound::<ContainsLiteralScannerBackend>(
                TRUST_CG_CONTAINS_LITERAL_SCANNER_BACKEND_FN,
            )
            .ok_or_else(|| {
                format!("missing JIT symbol {TRUST_CG_CONTAINS_LITERAL_SCANNER_BACKEND_FN}")
            })?
    };
    let batch_subsumption_scanner_guard = unsafe {
        buffer
            .get_fn_bound::<BatchSubsumptionScannerBackend>(
                TRUST_CG_BATCH_SUBSUMPTION_SCANNER_BACKEND_FN,
            )
            .ok_or_else(|| {
                format!("missing JIT symbol {TRUST_CG_BATCH_SUBSUMPTION_SCANNER_BACKEND_FN}")
            })?
    };
    let contains_literal_query_batch_guard = unsafe {
        buffer
            .get_fn_bound::<ContainsLiteralQueryBatchBackend>(
                TRUST_CG_CONTAINS_LITERAL_QUERY_BATCH_BACKEND_FN,
            )
            .ok_or_else(|| {
                format!("missing JIT symbol {TRUST_CG_CONTAINS_LITERAL_QUERY_BATCH_BACKEND_FN}")
            })?
    };
    let batch_subsumption_repeated_checksum_guard = unsafe {
        buffer
            .get_fn_bound::<BatchSubsumptionRepeatedChecksumBackend>(
                TRUST_CG_BATCH_SUBSUMPTION_REPEATED_CHECKSUM_BACKEND_FN,
            )
            .ok_or_else(|| {
                format!(
                    "missing JIT symbol {TRUST_CG_BATCH_SUBSUMPTION_REPEATED_CHECKSUM_BACKEND_FN}"
                )
            })?
    };
    let contains4 = contains4_guard.as_ref();
    let contains_literal_scanner = contains_literal_scanner_guard.as_ref();
    let contains_literal_query_batch = contains_literal_query_batch_guard.as_ref();
    let batch_subsumption_scanner = batch_subsumption_scanner_guard.as_ref();
    let batch_subsumption_repeated_checksum = batch_subsumption_repeated_checksum_guard.as_ref();
    trust_cg_codegen::ensure_jit_execute_mode();

    let mut mismatches = Vec::new();
    for case in &probe_cases {
        let actual_mask = call_contains4_masked(contains4, &case.chunk, case.literal);
        if actual_mask != case.expected_mask {
            mismatches.push(contains4_chunk_mismatch(case, actual_mask));
        }
    }
    let chunk_mismatch_count = mismatches.len();

    let contains_scanner_view = arena.scanner_view();
    let mut contains_scanner_scratch = vec![0u32; contains_scanner_view.len()];
    for query in &cases.contains_queries {
        let match_count = call_contains_literal_scanner(
            contains_literal_scanner,
            &arena,
            &contains_scanner_view,
            query.literal,
            &mut contains_scanner_scratch,
        );
        let actual_clause_ids = contains_scanner_scratch[..match_count]
            .iter()
            .map(|clause_id| usize::try_from(*clause_id).expect("clause id fits usize"))
            .collect::<Vec<_>>();
        if actual_clause_ids != query.expected_clause_ids {
            mismatches.push(contains_query_mismatch(
                query.literal,
                query.expected_clause_ids.clone(),
                actual_clause_ids,
            ));
        }
    }
    let contains_mismatch_count = mismatches
        .iter()
        .filter(|mismatch| mismatch.operation == "contains_literal")
        .count();

    let subsumption_pairs = cases
        .subsumption_pairs
        .iter()
        .map(|pair| (pair.a, pair.b))
        .collect::<Vec<_>>();
    let subsumption_batch = arena.subsumption_scanner_batch_for_pairs(&subsumption_pairs);
    let mut subsumption_results = vec![0u8; subsumption_batch.len()];
    call_batch_subsumption_scanner(
        batch_subsumption_scanner,
        &arena,
        &subsumption_batch,
        &mut subsumption_results,
    );
    for (pair, actual) in cases.subsumption_pairs.iter().zip(&subsumption_results) {
        let actual = *actual != 0;
        if actual != pair.expected {
            mismatches.push(subsumption_mismatch(pair, actual));
        }
    }
    let subsumption_mismatch_count = mismatches
        .iter()
        .filter(|mismatch| mismatch.operation == "batch_subsumption")
        .count();
    let operation_measurements = measure_trust_cg_backend_operations(
        cases,
        &arena,
        contains_literal_query_batch,
        batch_subsumption_repeated_checksum,
        length_buckets,
    );
    let operation_measurement_count = operation_measurements.len();
    let (opt_level_name, vectorizer_mode) = trust_cg_variant_probe_mode(variant);

    Ok(TrustCgBackendExecutionRow {
        variant: variant.to_string(),
        backend_kind: "trust_cg_o2_o3_pipeline_jit_scanner",
        opt_level: opt_level_name,
        vectorizer_mode,
        disabled_passes,
        contains4_backend_shape,
        status: "trust_cg_backend_executed",
        error_code: None,
        function_name: TRUST_CG_CONTAINS4_MASKED_BACKEND_FN,
        checked_cases: probe_cases.len(),
        chunk_mismatch_count,
        contains_query_count: cases.contains_queries.len(),
        contains_mismatch_count,
        subsumption_pair_count: cases.subsumption_pairs.len(),
        subsumption_mismatch_count,
        mismatches,
        operation_measurements,
        message: format!(
            "Executed Trust Codegen O2/O3 pipeline backend row for {variant}: prepared masked contains4 through {opt_level_name} with {vectorizer_mode}, compiled the scanner-level contains_literal and batch_subsumption entrypoints alongside it, prebuilt {} padded chunks once for the row, checked {} padded chunk comparisons, {} containment queries, {} subsumption pairs, and measured {} operation row(s). This is a bounded backend slice, not the full #571 gate.",
            arena.chunks.len(),
            probe_cases.len(),
            cases.contains_queries.len(),
            cases.subsumption_pairs.len(),
            operation_measurement_count
        ),
    })
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn trust_cg_probe_clause_contains(
    arena: &TrustCgPaddedChunkArena,
    clause: &ClauseCase,
    literal: i32,
    contains4: &Contains4MaskedProbe,
) -> bool {
    arena
        .chunks_for_clause(clause.id)
        .iter()
        .any(|chunk| call_contains4_masked(contains4, chunk, literal) != 0)
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn measure_trust_cg_probe_operations(
    cases: &AYSubsumptionCases,
    arena: &TrustCgPaddedChunkArena,
    contains4: &Contains4MaskedProbe,
    length_buckets: &[String],
) -> Vec<TrustCgProbeOperationMeasurement> {
    let warmup_iterations = cases.benchmark_matrix.warmup_iterations as usize;
    let measurement_repetitions = cases.benchmark_matrix.measurement_repetitions.max(1) as usize;
    let batches_per_repetition = TRUST_CG_PROBE_BATCHES_PER_REPETITION;
    let all_clauses = cases.clauses.iter().collect::<Vec<_>>();
    let mixed_pairs = cases
        .subsumption_pairs
        .iter()
        .map(|pair| (pair.a, pair.b))
        .collect::<Vec<_>>();

    let mut measurements = vec![
        measure_trust_cg_probe_operation(
            "contains_literal",
            TRUST_CG_PROBE_WORKLOAD_BUCKET,
            warmup_iterations,
            measurement_repetitions,
            batches_per_repetition,
            cases.contains_queries.len() * cases.clauses.len(),
            || run_trust_cg_contains_probe_batch_for_clauses(cases, arena, contains4, &all_clauses),
        ),
        measure_trust_cg_probe_operation(
            "batch_subsumption",
            TRUST_CG_PROBE_WORKLOAD_BUCKET,
            warmup_iterations,
            measurement_repetitions,
            batches_per_repetition,
            cases.subsumption_pairs.len(),
            || {
                run_trust_cg_subsumption_probe_batch_for_pairs(
                    cases,
                    arena,
                    contains4,
                    &mixed_pairs,
                )
            },
        ),
    ];

    for bucket in length_buckets {
        measurements.extend(measure_trust_cg_probe_length_bucket_operations(
            cases,
            arena,
            contains4,
            bucket,
            warmup_iterations,
            measurement_repetitions,
            batches_per_repetition,
        ));
    }

    measurements
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn measure_trust_cg_probe_length_bucket_operations(
    cases: &AYSubsumptionCases,
    arena: &TrustCgPaddedChunkArena,
    contains4: &Contains4MaskedProbe,
    bucket: &str,
    warmup_iterations: usize,
    measurement_repetitions: usize,
    batches_per_repetition: usize,
) -> Vec<TrustCgProbeOperationMeasurement> {
    let bucket_clauses = cases
        .clauses
        .iter()
        .filter(|clause| clause.length.to_string() == bucket)
        .collect::<Vec<_>>();
    if bucket_clauses.is_empty() {
        return Vec::new();
    }
    let self_pairs = bucket_clauses
        .iter()
        .map(|clause| (clause.id, clause.id))
        .collect::<Vec<_>>();

    vec![
        measure_trust_cg_probe_operation(
            "contains_literal",
            bucket,
            warmup_iterations,
            measurement_repetitions,
            batches_per_repetition,
            cases.contains_queries.len() * bucket_clauses.len(),
            || {
                run_trust_cg_contains_probe_batch_for_clauses(
                    cases,
                    arena,
                    contains4,
                    &bucket_clauses,
                )
            },
        ),
        measure_trust_cg_probe_operation(
            "batch_subsumption",
            bucket,
            warmup_iterations,
            measurement_repetitions,
            batches_per_repetition,
            self_pairs.len(),
            || run_trust_cg_subsumption_probe_batch_for_pairs(cases, arena, contains4, &self_pairs),
        ),
    ]
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn measure_trust_cg_backend_operations(
    cases: &AYSubsumptionCases,
    arena: &TrustCgPaddedChunkArena,
    contains_literal_query_batch: &ContainsLiteralQueryBatchBackend,
    batch_subsumption_repeated_checksum: &BatchSubsumptionRepeatedChecksumBackend,
    length_buckets: &[String],
) -> Vec<TrustCgBackendOperationMeasurement> {
    let warmup_iterations = cases.benchmark_matrix.warmup_iterations as usize;
    let measurement_repetitions = cases.benchmark_matrix.measurement_repetitions.max(1) as usize;
    let batches_per_repetition = TRUST_CG_PROBE_BATCHES_PER_REPETITION;
    let contains_query_literals = cases
        .contains_queries
        .iter()
        .map(|query| query.literal)
        .collect::<Vec<_>>();
    let all_scanner_view = arena.scanner_view();
    let mixed_pairs = cases
        .subsumption_pairs
        .iter()
        .map(|pair| (pair.a, pair.b))
        .collect::<Vec<_>>();
    let mixed_subsumption_batch = arena.subsumption_scanner_batch_for_pairs(&mixed_pairs);
    let mut mixed_subsumption_results = vec![0u8; mixed_subsumption_batch.len()];

    let mut measurements = Vec::new();
    if trust_cg_backend_should_measure_mixed_rows(cases, length_buckets) {
        measurements.extend([
            measure_trust_cg_backend_operation(
                "contains_literal",
                AY_REFERENCE_WORKLOAD_BUCKET,
                warmup_iterations,
                measurement_repetitions,
                batches_per_repetition,
                cases.contains_queries.len() * cases.clauses.len(),
                || {
                    run_trust_cg_contains_query_batch_for_view(
                        arena,
                        contains_literal_query_batch,
                        &all_scanner_view,
                        &contains_query_literals,
                    )
                },
            ),
            measure_trust_cg_backend_operation_repeated_batches(
                "batch_subsumption",
                AY_REFERENCE_WORKLOAD_BUCKET,
                warmup_iterations,
                measurement_repetitions,
                batches_per_repetition,
                cases.subsumption_pairs.len(),
                |repetition_batches| {
                    run_trust_cg_subsumption_scanner_repeated_checksum_for_batch(
                        arena,
                        batch_subsumption_repeated_checksum,
                        &mixed_subsumption_batch,
                        repetition_batches,
                        &mut mixed_subsumption_results,
                    )
                },
            ),
        ]);
    }
    for bucket in length_buckets {
        measurements.extend(measure_trust_cg_backend_length_bucket_operations(
            cases,
            arena,
            contains_literal_query_batch,
            batch_subsumption_repeated_checksum,
            &contains_query_literals,
            bucket,
            warmup_iterations,
            measurement_repetitions,
            batches_per_repetition,
        ));
    }

    measurements
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn trust_cg_backend_should_measure_mixed_rows(
    cases: &AYSubsumptionCases,
    length_buckets: &[String],
) -> bool {
    let numeric_buckets = ay_numeric_length_buckets(&cases.benchmark_matrix.length_buckets);
    if numeric_buckets.is_empty() {
        return false;
    }
    let requested = length_buckets.iter().collect::<BTreeSet<_>>();
    numeric_buckets
        .iter()
        .all(|bucket| requested.contains(bucket))
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
#[allow(clippy::too_many_arguments)] // Measurement inputs are independent benchmark dimensions.
fn measure_trust_cg_backend_length_bucket_operations(
    cases: &AYSubsumptionCases,
    arena: &TrustCgPaddedChunkArena,
    contains_literal_query_batch: &ContainsLiteralQueryBatchBackend,
    batch_subsumption_repeated_checksum: &BatchSubsumptionRepeatedChecksumBackend,
    contains_query_literals: &[i32],
    bucket: &str,
    warmup_iterations: usize,
    measurement_repetitions: usize,
    batches_per_repetition: usize,
) -> Vec<TrustCgBackendOperationMeasurement> {
    let bucket_clauses = cases
        .clauses
        .iter()
        .filter(|clause| clause.length.to_string() == bucket)
        .collect::<Vec<_>>();
    if bucket_clauses.is_empty() {
        return Vec::new();
    }
    let self_pairs = bucket_clauses
        .iter()
        .map(|clause| (clause.id, clause.id))
        .collect::<Vec<_>>();
    let self_subsumption_batch = arena.subsumption_scanner_batch_for_pairs(&self_pairs);
    let mut self_subsumption_results = vec![0u8; self_subsumption_batch.len()];
    let bucket_scanner_view = arena.scanner_view_for_clauses(&bucket_clauses);

    vec![
        measure_trust_cg_backend_operation(
            "contains_literal",
            bucket,
            warmup_iterations,
            measurement_repetitions,
            batches_per_repetition,
            cases.contains_queries.len() * bucket_clauses.len(),
            || {
                run_trust_cg_contains_query_batch_for_view(
                    arena,
                    contains_literal_query_batch,
                    &bucket_scanner_view,
                    contains_query_literals,
                )
            },
        ),
        measure_trust_cg_backend_operation_repeated_batches(
            "batch_subsumption",
            bucket,
            warmup_iterations,
            measurement_repetitions,
            batches_per_repetition,
            self_pairs.len(),
            |repetition_batches| {
                run_trust_cg_subsumption_scanner_repeated_checksum_for_batch(
                    arena,
                    batch_subsumption_repeated_checksum,
                    &self_subsumption_batch,
                    repetition_batches,
                    &mut self_subsumption_results,
                )
            },
        ),
    ]
}

fn mean_and_stddev(values: &[f64]) -> (Option<f64>, Option<f64>) {
    if values.is_empty() {
        return (None, None);
    }
    let mean = values.iter().sum::<f64>() / values.len() as f64;
    let variance = values
        .iter()
        .map(|value| {
            let delta = value - mean;
            delta * delta
        })
        .sum::<f64>()
        / values.len() as f64;
    (Some(mean), Some(variance.sqrt()))
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn measure_trust_cg_backend_operation<F>(
    operation: &'static str,
    workload_bucket: &str,
    warmup_iterations: usize,
    measurement_repetitions: usize,
    batches_per_repetition: usize,
    items_per_batch: usize,
    mut run_batch: F,
) -> TrustCgBackendOperationMeasurement
where
    F: FnMut() -> u64,
{
    for _ in 0..warmup_iterations {
        std::hint::black_box(run_batch());
    }

    let mut checksum = 0u64;
    let mut raw_elapsed_ns = Vec::with_capacity(measurement_repetitions);
    let mut throughput_per_us = Vec::with_capacity(measurement_repetitions);
    let items_per_repetition = items_per_batch * batches_per_repetition;

    for _ in 0..measurement_repetitions {
        let start = Instant::now();
        let mut repetition_checksum = 0u64;
        for _ in 0..batches_per_repetition {
            repetition_checksum = repetition_checksum.wrapping_add(run_batch());
        }
        std::hint::black_box(repetition_checksum);
        checksum = checksum.wrapping_add(repetition_checksum);

        let elapsed = start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        raw_elapsed_ns.push(elapsed);
        if elapsed != 0 {
            throughput_per_us.push(items_per_repetition as f64 / (elapsed as f64 / 1_000.0));
        }
    }

    let elapsed_ns = raw_elapsed_ns
        .iter()
        .map(|elapsed| *elapsed as f64)
        .collect::<Vec<_>>();
    let (mean_elapsed_ns, stddev_elapsed_ns) = mean_and_stddev(&elapsed_ns);
    let (mean_throughput_per_us, stddev_throughput_per_us) = mean_and_stddev(&throughput_per_us);
    let coefficient_of_variation = match (mean_throughput_per_us, stddev_throughput_per_us) {
        (Some(mean), Some(stddev)) if mean != 0.0 => Some(stddev / mean),
        _ => None,
    };
    let total_items = items_per_repetition * measurement_repetitions;

    TrustCgBackendOperationMeasurement {
        operation,
        workload_bucket: workload_bucket.to_string(),
        status: if mean_throughput_per_us.is_some() {
            "backend_measured"
        } else {
            "backend_measurement_unavailable"
        },
        warmup_iterations,
        measurement_repetitions,
        batches_per_repetition,
        items_per_batch,
        total_items,
        raw_elapsed_ns,
        mean_elapsed_ns,
        stddev_elapsed_ns,
        mean_throughput_per_us,
        stddev_throughput_per_us,
        coefficient_of_variation,
        checksum,
        message: format!(
            "Measured {operation} through the Trust Codegen O2/O3 pipeline backend over fixture bucket {workload_bucket}; this bounded row is not the full #571 throughput gate."
        ),
    }
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn measure_trust_cg_backend_operation_repeated_batches<F>(
    operation: &'static str,
    workload_bucket: &str,
    warmup_iterations: usize,
    measurement_repetitions: usize,
    batches_per_repetition: usize,
    items_per_batch: usize,
    mut run_repeated_batches: F,
) -> TrustCgBackendOperationMeasurement
where
    F: FnMut(usize) -> u64,
{
    for _ in 0..warmup_iterations {
        std::hint::black_box(run_repeated_batches(1));
    }

    let mut checksum = 0u64;
    let mut raw_elapsed_ns = Vec::with_capacity(measurement_repetitions);
    let mut throughput_per_us = Vec::with_capacity(measurement_repetitions);
    let items_per_repetition = items_per_batch * batches_per_repetition;

    for _ in 0..measurement_repetitions {
        let start = Instant::now();
        let repetition_checksum = run_repeated_batches(batches_per_repetition);
        std::hint::black_box(repetition_checksum);
        checksum = checksum.wrapping_add(repetition_checksum);

        let elapsed = start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        raw_elapsed_ns.push(elapsed);
        if elapsed != 0 {
            throughput_per_us.push(items_per_repetition as f64 / (elapsed as f64 / 1_000.0));
        }
    }

    let elapsed_ns = raw_elapsed_ns
        .iter()
        .map(|elapsed| *elapsed as f64)
        .collect::<Vec<_>>();
    let (mean_elapsed_ns, stddev_elapsed_ns) = mean_and_stddev(&elapsed_ns);
    let (mean_throughput_per_us, stddev_throughput_per_us) = mean_and_stddev(&throughput_per_us);
    let coefficient_of_variation = match (mean_throughput_per_us, stddev_throughput_per_us) {
        (Some(mean), Some(stddev)) if mean != 0.0 => Some(stddev / mean),
        _ => None,
    };
    let total_items = items_per_repetition * measurement_repetitions;

    TrustCgBackendOperationMeasurement {
        operation,
        workload_bucket: workload_bucket.to_string(),
        status: if mean_throughput_per_us.is_some() {
            "backend_measured"
        } else {
            "backend_measurement_unavailable"
        },
        warmup_iterations,
        measurement_repetitions,
        batches_per_repetition,
        items_per_batch,
        total_items,
        raw_elapsed_ns,
        mean_elapsed_ns,
        stddev_elapsed_ns,
        mean_throughput_per_us,
        stddev_throughput_per_us,
        coefficient_of_variation,
        checksum,
        message: format!(
            "Measured {operation} through the Trust Codegen O2/O3 pipeline backend over fixture bucket {workload_bucket}; this bounded row is not the full #571 throughput gate."
        ),
    }
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn measure_trust_cg_probe_operation<F>(
    operation: &'static str,
    workload_bucket: &str,
    warmup_iterations: usize,
    measurement_repetitions: usize,
    batches_per_repetition: usize,
    items_per_batch: usize,
    mut run_batch: F,
) -> TrustCgProbeOperationMeasurement
where
    F: FnMut() -> u64,
{
    for _ in 0..warmup_iterations {
        std::hint::black_box(run_batch());
    }

    let mut checksum = 0u64;
    let mut raw_elapsed_ns = Vec::with_capacity(measurement_repetitions);
    let mut throughput_per_us = Vec::with_capacity(measurement_repetitions);
    let items_per_repetition = items_per_batch * batches_per_repetition;

    for _ in 0..measurement_repetitions {
        let start = Instant::now();
        let mut repetition_checksum = 0u64;
        for _ in 0..batches_per_repetition {
            repetition_checksum = repetition_checksum.wrapping_add(run_batch());
        }
        std::hint::black_box(repetition_checksum);
        checksum = checksum.wrapping_add(repetition_checksum);

        let elapsed = start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        raw_elapsed_ns.push(elapsed);
        if elapsed != 0 {
            throughput_per_us.push(items_per_repetition as f64 / (elapsed as f64 / 1_000.0));
        }
    }

    let elapsed_ns = raw_elapsed_ns
        .iter()
        .map(|elapsed| *elapsed as f64)
        .collect::<Vec<_>>();
    let (mean_elapsed_ns, stddev_elapsed_ns) = mean_and_stddev(&elapsed_ns);
    let (mean_throughput_per_us, stddev_throughput_per_us) = mean_and_stddev(&throughput_per_us);
    let coefficient_of_variation = match (mean_throughput_per_us, stddev_throughput_per_us) {
        (Some(mean), Some(stddev)) if mean != 0.0 => Some(stddev / mean),
        _ => None,
    };
    let total_items = items_per_repetition * measurement_repetitions;

    TrustCgProbeOperationMeasurement {
        operation,
        workload_bucket: workload_bucket.to_string(),
        status: if mean_throughput_per_us.is_some() {
            "probe_measured"
        } else {
            "probe_measurement_unavailable"
        },
        promotion_disposition: TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION,
        warmup_iterations,
        measurement_repetitions,
        batches_per_repetition,
        items_per_batch,
        total_items,
        raw_elapsed_ns,
        mean_elapsed_ns,
        stddev_elapsed_ns,
        mean_throughput_per_us,
        stddev_throughput_per_us,
        coefficient_of_variation,
        checksum,
        message: format!(
            "Measured {operation} through the Trust Codegen raw-JIT masked contains4 scanner probe over fixture bucket {workload_bucket}; this row is profile-only/non-promoting and is not installable product evidence."
        ),
    }
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn run_trust_cg_contains_probe_batch_for_clauses(
    cases: &AYSubsumptionCases,
    arena: &TrustCgPaddedChunkArena,
    contains4: &Contains4MaskedProbe,
    clauses: &[&ClauseCase],
) -> u64 {
    let mut checksum = 0u64;
    for query in &cases.contains_queries {
        let mut match_count = 0u64;
        let mut id_checksum = 0u64;
        for clause in clauses {
            if trust_cg_probe_clause_contains(arena, clause, query.literal, contains4) {
                match_count += 1;
                id_checksum ^= clause.id as u64;
            }
        }
        checksum = checksum
            .wrapping_mul(131)
            .wrapping_add(query.literal as u32 as u64)
            .wrapping_add(match_count)
            .wrapping_add(id_checksum);
    }
    checksum
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn run_trust_cg_contains_query_batch_for_view(
    arena: &TrustCgPaddedChunkArena,
    contains_literal_query_batch: &ContainsLiteralQueryBatchBackend,
    view: &TrustCgPaddedChunkScannerView,
    query_literals: &[i32],
) -> u64 {
    call_contains_literal_query_batch_scanner(
        contains_literal_query_batch,
        arena,
        view,
        query_literals,
    )
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn run_trust_cg_subsumption_probe_batch_for_pairs(
    cases: &AYSubsumptionCases,
    arena: &TrustCgPaddedChunkArena,
    contains4: &Contains4MaskedProbe,
    pairs: &[(usize, usize)],
) -> u64 {
    let mut checksum = 0u64;
    for &(pair_a, pair_b) in pairs {
        let a = clause_by_id(cases, pair_a).expect("validated fixture should contain A clause");
        let b = clause_by_id(cases, pair_b).expect("validated fixture should contain B clause");
        let actual = a
            .lits
            .iter()
            .all(|literal| trust_cg_probe_clause_contains(arena, b, *literal, contains4));
        checksum = checksum
            .wrapping_mul(131)
            .wrapping_add(pair_a as u64)
            .wrapping_add((pair_b as u64) << 8)
            .wrapping_add(u64::from(actual));
    }
    checksum
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn run_trust_cg_subsumption_scanner_repeated_checksum_for_batch(
    arena: &TrustCgPaddedChunkArena,
    scanner: &BatchSubsumptionRepeatedChecksumBackend,
    batch: &TrustCgSubsumptionScannerBatch,
    repetitions: usize,
    out_results: &mut [u8],
) -> u64 {
    call_batch_subsumption_repeated_checksum_scanner(
        scanner,
        arena,
        batch,
        repetitions,
        out_results,
    )
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn build_trust_cg_contains4_masked_backend_function() -> trust_cg_ir::MachFunction {
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::AArch64Opcode;
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{RegClass, VReg, W0, W1, W2, X0};

    let sig = Signature::new(vec![Type::Ptr, Type::I32, Type::I32], vec![Type::I32]);
    let mut func = MachFunction::new(TRUST_CG_CONTAINS4_MASKED_BACKEND_FN.to_string(), sig);
    let entry = func.entry;
    let base = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let lane0 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let lane1 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let lane2 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let lane3 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let literal = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let valid_mask = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let acc0 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let eq0 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let eq1_raw = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let eq1 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let acc1 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let eq2_raw = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let eq2 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let acc2 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let eq3_raw = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let eq3 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let acc3 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let acc4 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let masked = VReg::new(func.alloc_vreg(), RegClass::Gpr32);

    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::MovR,
        vec![MachOperand::VReg(base), MachOperand::PReg(X0)],
    );
    for (dst, src) in [(literal, W1), (valid_mask, W2)] {
        append_probe_inst(
            &mut func,
            entry,
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(dst), MachOperand::PReg(src)],
        );
    }
    for (dst, offset) in [(lane0, 0), (lane1, 4), (lane2, 8), (lane3, 12)] {
        append_probe_inst(
            &mut func,
            entry,
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(base),
                MachOperand::Imm(offset),
            ],
        );
    }

    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(acc0), MachOperand::Imm(0)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CmpRR,
        vec![MachOperand::VReg(lane0), MachOperand::VReg(literal)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CSet,
        vec![MachOperand::VReg(eq0), MachOperand::Imm(0)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CmpRR,
        vec![MachOperand::VReg(lane1), MachOperand::VReg(literal)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CSet,
        vec![MachOperand::VReg(eq1_raw), MachOperand::Imm(0)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::LslRI,
        vec![
            MachOperand::VReg(eq1),
            MachOperand::VReg(eq1_raw),
            MachOperand::Imm(1),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::OrrRR,
        vec![
            MachOperand::VReg(acc1),
            MachOperand::VReg(acc0),
            MachOperand::VReg(eq0),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::OrrRR,
        vec![
            MachOperand::VReg(acc2),
            MachOperand::VReg(acc1),
            MachOperand::VReg(eq1),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CmpRR,
        vec![MachOperand::VReg(lane2), MachOperand::VReg(literal)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CSet,
        vec![MachOperand::VReg(eq2_raw), MachOperand::Imm(0)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::LslRI,
        vec![
            MachOperand::VReg(eq2),
            MachOperand::VReg(eq2_raw),
            MachOperand::Imm(2),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::OrrRR,
        vec![
            MachOperand::VReg(acc3),
            MachOperand::VReg(acc2),
            MachOperand::VReg(eq2),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CmpRR,
        vec![MachOperand::VReg(lane3), MachOperand::VReg(literal)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CSet,
        vec![MachOperand::VReg(eq3_raw), MachOperand::Imm(0)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::LslRI,
        vec![
            MachOperand::VReg(eq3),
            MachOperand::VReg(eq3_raw),
            MachOperand::Imm(3),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::OrrRR,
        vec![
            MachOperand::VReg(acc4),
            MachOperand::VReg(acc3),
            MachOperand::VReg(eq3),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::AndRR,
        vec![
            MachOperand::VReg(masked),
            MachOperand::VReg(acc4),
            MachOperand::VReg(valid_mask),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(W0), MachOperand::VReg(masked)],
    );
    append_probe_inst(&mut func, entry, AArch64Opcode::Ret, vec![]);

    func
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn build_trust_cg_contains_literal_scanner_backend_function() -> trust_cg_ir::MachFunction {
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::AArch64Opcode;
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{
        S0, V0, V1, W0, W4, W5, W6, W8, W9, W11, W12, W13, W15, X0, X1, X2, X3, X7, X8, X9, X10,
        X13, X14,
    };

    fn patch_branch_imm(
        func: &mut MachFunction,
        block: trust_cg_ir::BlockId,
        branch_inst_pos: usize,
        imm_operand_index: usize,
        target_inst_pos: usize,
    ) {
        let inst_id = func.block(block).insts[branch_inst_pos];
        let displacement = target_inst_pos as i64 - branch_inst_pos as i64;
        func.inst_mut(inst_id).operands[imm_operand_index] = MachOperand::Imm(displacement);
    }

    let sig = Signature::new(
        vec![
            Type::Ptr,
            Type::Ptr,
            Type::Ptr,
            Type::Ptr,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::Ptr,
        ],
        vec![Type::I32],
    );
    let mut func = MachFunction::new(
        TRUST_CG_CONTAINS_LITERAL_SCANNER_BACKEND_FN.to_string(),
        sig,
    );
    let entry = func.entry;

    macro_rules! emit {
        ($opcode:expr, $operands:expr) => {{
            append_probe_inst(&mut func, entry, $opcode, $operands);
            let inst_pos = func.block(entry).insts.len() - 1;
            inst_pos
        }};
    }

    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W8), MachOperand::Imm(0)]
    );
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W5), MachOperand::PReg(W6)]
    );
    let sentinel_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::EQ as i64),
            MachOperand::Imm(0),
        ]
    );
    emit!(
        AArch64Opcode::NeonDupGen,
        vec![
            MachOperand::PReg(V1),
            MachOperand::PReg(W5),
            MachOperand::Imm(4),
        ]
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W9), MachOperand::Imm(0)]
    );

    let clause_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W9), MachOperand::PReg(W4)]
    );
    let clause_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ]
    );

    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X10),
            MachOperand::PReg(X9),
            MachOperand::Imm(2),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W11),
            MachOperand::PReg(X1),
            MachOperand::PReg(X10),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W12),
            MachOperand::PReg(X2),
            MachOperand::PReg(X10),
        ]
    );
    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(W13), MachOperand::PReg(W11)]
    );

    let chunk_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W13), MachOperand::PReg(W12)]
    );
    let chunk_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ]
    );

    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X10),
            MachOperand::PReg(X13),
            MachOperand::Imm(4),
        ]
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X10),
            MachOperand::PReg(X0),
            MachOperand::PReg(X10),
        ]
    );
    emit!(
        AArch64Opcode::NeonLd1Post,
        vec![
            MachOperand::PReg(V0),
            MachOperand::PReg(X10),
            MachOperand::Imm(5),
        ]
    );
    emit!(
        AArch64Opcode::NeonCmeqV,
        vec![
            MachOperand::PReg(V0),
            MachOperand::PReg(V0),
            MachOperand::PReg(V1),
            MachOperand::Imm(5),
        ]
    );
    emit!(
        AArch64Opcode::NeonUmaxv,
        vec![
            MachOperand::PReg(S0),
            MachOperand::PReg(V0),
            MachOperand::Imm(5),
        ]
    );
    emit!(
        AArch64Opcode::NeonUmovGen,
        vec![
            MachOperand::PReg(W15),
            MachOperand::PReg(V0),
            MachOperand::Imm(0),
            MachOperand::Imm(4),
        ]
    );
    let chunk_found_branch = emit!(
        AArch64Opcode::Cbnz,
        vec![MachOperand::PReg(W15), MachOperand::Imm(0)]
    );
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W13),
            MachOperand::PReg(W13),
            MachOperand::Imm(1),
        ]
    );
    let chunk_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let chunk_found = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X10),
            MachOperand::PReg(X8),
            MachOperand::Imm(2),
        ]
    );
    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X14),
            MachOperand::PReg(X9),
            MachOperand::Imm(2),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W11),
            MachOperand::PReg(X3),
            MachOperand::PReg(X14),
        ]
    );
    emit!(
        AArch64Opcode::StrRO,
        vec![
            MachOperand::PReg(W11),
            MachOperand::PReg(X7),
            MachOperand::PReg(X10),
        ]
    );
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W8),
            MachOperand::PReg(W8),
            MachOperand::Imm(1),
        ]
    );

    let next_clause = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W9),
            MachOperand::PReg(W9),
            MachOperand::Imm(1),
        ]
    );
    let clause_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let done = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(W0), MachOperand::PReg(W8)]
    );
    emit!(AArch64Opcode::Ret, vec![]);

    patch_branch_imm(&mut func, entry, sentinel_done_branch, 1, done);
    patch_branch_imm(&mut func, entry, clause_done_branch, 1, done);
    patch_branch_imm(&mut func, entry, chunk_done_branch, 1, next_clause);
    patch_branch_imm(&mut func, entry, chunk_found_branch, 1, chunk_found);
    patch_branch_imm(&mut func, entry, chunk_loop_branch, 0, chunk_header);
    patch_branch_imm(&mut func, entry, clause_loop_branch, 0, clause_header);
    materialize_resolved_probe_cfg_blocks(&mut func);

    func
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn build_trust_cg_contains_literal_query_batch_backend_function() -> trust_cg_ir::MachFunction {
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::AArch64Opcode;
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{
        S0, V0, V1, W4, W6, W7, W9, W10, W11, W13, W14, W15, X0, X1, X2, X3, X5, X8, X9, X10, X11,
        X12, X13, X14, X15, X16, X17,
    };

    fn patch_branch_imm(
        func: &mut MachFunction,
        block: trust_cg_ir::BlockId,
        branch_inst_pos: usize,
        imm_operand_index: usize,
        target_inst_pos: usize,
    ) {
        let inst_id = func.block(block).insts[branch_inst_pos];
        let displacement = target_inst_pos as i64 - branch_inst_pos as i64;
        func.inst_mut(inst_id).operands[imm_operand_index] = MachOperand::Imm(displacement);
    }

    let sig = Signature::new(
        vec![
            Type::Ptr,
            Type::Ptr,
            Type::Ptr,
            Type::Ptr,
            Type::I32,
            Type::Ptr,
            Type::I32,
            Type::I32,
        ],
        vec![Type::I64],
    );
    let mut func = MachFunction::new(
        TRUST_CG_CONTAINS_LITERAL_QUERY_BATCH_BACKEND_FN.to_string(),
        sig,
    );
    let entry = func.entry;

    macro_rules! emit {
        ($opcode:expr, $operands:expr) => {{
            append_probe_inst(&mut func, entry, $opcode, $operands);
            let inst_pos = func.block(entry).insts.len() - 1;
            inst_pos
        }};
    }

    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X8), MachOperand::Imm(0)]
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W9), MachOperand::Imm(0)]
    );

    let query_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W9), MachOperand::PReg(W6)]
    );
    let query_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ]
    );

    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X15),
            MachOperand::PReg(X9),
            MachOperand::Imm(2),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W10),
            MachOperand::PReg(X5),
            MachOperand::PReg(X15),
        ]
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W11), MachOperand::Imm(0)]
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X12), MachOperand::Imm(0)]
    );
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W10), MachOperand::PReg(W7)]
    );
    let sentinel_skip_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::EQ as i64),
            MachOperand::Imm(0),
        ]
    );
    emit!(
        AArch64Opcode::NeonDupGen,
        vec![
            MachOperand::PReg(V1),
            MachOperand::PReg(W10),
            MachOperand::Imm(4),
        ]
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W13), MachOperand::Imm(0)]
    );

    let clause_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W13), MachOperand::PReg(W4)]
    );
    let clauses_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ]
    );

    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X15),
            MachOperand::PReg(X13),
            MachOperand::Imm(2),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W14),
            MachOperand::PReg(X1),
            MachOperand::PReg(X15),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W15),
            MachOperand::PReg(X2),
            MachOperand::PReg(X15),
        ]
    );
    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X16),
            MachOperand::PReg(X14),
            MachOperand::Imm(4),
        ]
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X16),
            MachOperand::PReg(X0),
            MachOperand::PReg(X16),
        ]
    );
    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X17),
            MachOperand::PReg(X15),
            MachOperand::Imm(4),
        ]
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X17),
            MachOperand::PReg(X0),
            MachOperand::PReg(X17),
        ]
    );

    let chunk_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(X16), MachOperand::PReg(X17)]
    );
    let chunk_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ]
    );
    emit!(
        AArch64Opcode::NeonLd1Post,
        vec![
            MachOperand::PReg(V0),
            MachOperand::PReg(X16),
            MachOperand::Imm(5),
        ]
    );
    emit!(
        AArch64Opcode::NeonCmeqV,
        vec![
            MachOperand::PReg(V0),
            MachOperand::PReg(V0),
            MachOperand::PReg(V1),
            MachOperand::Imm(5),
        ]
    );
    emit!(
        AArch64Opcode::NeonUmaxv,
        vec![
            MachOperand::PReg(S0),
            MachOperand::PReg(V0),
            MachOperand::Imm(5),
        ]
    );
    emit!(
        AArch64Opcode::NeonUmovGen,
        vec![
            MachOperand::PReg(W15),
            MachOperand::PReg(V0),
            MachOperand::Imm(0),
            MachOperand::Imm(4),
        ]
    );
    let chunk_found_branch = emit!(
        AArch64Opcode::Cbnz,
        vec![MachOperand::PReg(W15), MachOperand::Imm(0)]
    );
    let chunk_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let clause_found = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X15),
            MachOperand::PReg(X13),
            MachOperand::Imm(2),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W15),
            MachOperand::PReg(X3),
            MachOperand::PReg(X15),
        ]
    );
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W11),
            MachOperand::PReg(W11),
            MachOperand::Imm(1),
        ]
    );
    emit!(
        AArch64Opcode::EorRR,
        vec![
            MachOperand::PReg(X12),
            MachOperand::PReg(X12),
            MachOperand::PReg(X15),
        ]
    );

    let next_clause = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W13),
            MachOperand::PReg(W13),
            MachOperand::Imm(1),
        ]
    );
    let clause_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let accumulate_query = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X16), MachOperand::Imm(131)]
    );
    emit!(
        AArch64Opcode::MulRR,
        vec![
            MachOperand::PReg(X8),
            MachOperand::PReg(X8),
            MachOperand::PReg(X16),
        ]
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X8),
            MachOperand::PReg(X8),
            MachOperand::PReg(X10),
        ]
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X8),
            MachOperand::PReg(X8),
            MachOperand::PReg(X11),
        ]
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X8),
            MachOperand::PReg(X8),
            MachOperand::PReg(X12),
        ]
    );
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W9),
            MachOperand::PReg(W9),
            MachOperand::Imm(1),
        ]
    );
    let query_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let done = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X0), MachOperand::PReg(X8)]
    );
    emit!(AArch64Opcode::Ret, vec![]);

    patch_branch_imm(&mut func, entry, query_done_branch, 1, done);
    patch_branch_imm(&mut func, entry, sentinel_skip_branch, 1, accumulate_query);
    patch_branch_imm(&mut func, entry, clauses_done_branch, 1, accumulate_query);
    patch_branch_imm(&mut func, entry, chunk_done_branch, 1, next_clause);
    patch_branch_imm(&mut func, entry, chunk_found_branch, 1, clause_found);
    patch_branch_imm(&mut func, entry, chunk_loop_branch, 0, chunk_header);
    patch_branch_imm(&mut func, entry, clause_loop_branch, 0, clause_header);
    patch_branch_imm(&mut func, entry, query_loop_branch, 0, query_header);
    materialize_resolved_probe_cfg_blocks(&mut func);

    func
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn build_trust_cg_batch_subsumption_scanner_backend_function() -> trust_cg_ir::MachFunction {
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::AArch64Opcode;
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{
        S0, V0, V1, W0, W1, W6, W8, W9, W11, W12, W13, W14, W15, X0, X1, X2, X3, X4, X5, X7, X9,
        X10, X13, X15, X16, X17,
    };

    fn patch_branch_imm(
        func: &mut MachFunction,
        block: trust_cg_ir::BlockId,
        branch_inst_pos: usize,
        imm_operand_index: usize,
        target_inst_pos: usize,
    ) {
        let inst_id = func.block(block).insts[branch_inst_pos];
        let displacement = target_inst_pos as i64 - branch_inst_pos as i64;
        func.inst_mut(inst_id).operands[imm_operand_index] = MachOperand::Imm(displacement);
    }

    let sig = Signature::new(
        vec![
            Type::Ptr,
            Type::Ptr,
            Type::Ptr,
            Type::Ptr,
            Type::Ptr,
            Type::Ptr,
            Type::I32,
            Type::Ptr,
        ],
        vec![Type::I32],
    );
    let mut func = MachFunction::new(
        TRUST_CG_BATCH_SUBSUMPTION_SCANNER_BACKEND_FN.to_string(),
        sig,
    );
    let entry = func.entry;

    macro_rules! emit {
        ($opcode:expr, $operands:expr) => {{
            append_probe_inst(&mut func, entry, $opcode, $operands);
            let inst_pos = func.block(entry).insts.len() - 1;
            inst_pos
        }};
    }

    macro_rules! emit_a_lane_search {
        ($offset:expr, $valid_bit:expr, $false_next_branches:ident) => {{
            emit!(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X17),
                    MachOperand::PReg(X15),
                ]
            );
            emit!(
                AArch64Opcode::LdrbRI,
                vec![
                    MachOperand::PReg(W0),
                    MachOperand::PReg(X10),
                    MachOperand::Imm(0),
                ]
            );
            emit!(
                AArch64Opcode::Movz,
                vec![MachOperand::PReg(W1), MachOperand::Imm($valid_bit)]
            );
            emit!(
                AArch64Opcode::AndRR,
                vec![
                    MachOperand::PReg(W1),
                    MachOperand::PReg(W0),
                    MachOperand::PReg(W1),
                ]
            );
            let skip_a_lane = emit!(
                AArch64Opcode::Cbz,
                vec![MachOperand::PReg(W1), MachOperand::Imm(0)]
            );

            emit!(
                AArch64Opcode::LslRI,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X15),
                    MachOperand::Imm(4),
                ]
            );
            emit!(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X16),
                    MachOperand::PReg(X10),
                ]
            );
            emit!(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(W11),
                    MachOperand::PReg(X10),
                    MachOperand::Imm($offset),
                ]
            );
            emit!(
                AArch64Opcode::NeonDupGen,
                vec![
                    MachOperand::PReg(V1),
                    MachOperand::PReg(W11),
                    MachOperand::Imm(4),
                ]
            );
            emit!(
                AArch64Opcode::LslRI,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X9),
                    MachOperand::Imm(2),
                ]
            );
            emit!(
                AArch64Opcode::LdrRO,
                vec![
                    MachOperand::PReg(W13),
                    MachOperand::PReg(X4),
                    MachOperand::PReg(X10),
                ]
            );

            let search_header = func.block(entry).insts.len();
            emit!(
                AArch64Opcode::CmpRR,
                vec![MachOperand::PReg(W13), MachOperand::PReg(W14)]
            );
            let search_done_branch = emit!(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
                    MachOperand::Imm(0),
                ]
            );
            emit!(
                AArch64Opcode::LslRI,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X13),
                    MachOperand::Imm(4),
                ]
            );
            emit!(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X16),
                    MachOperand::PReg(X10),
                ]
            );
            emit!(
                AArch64Opcode::NeonLd1Post,
                vec![
                    MachOperand::PReg(V0),
                    MachOperand::PReg(X10),
                    MachOperand::Imm(5),
                ]
            );
            emit!(
                AArch64Opcode::NeonCmeqV,
                vec![
                    MachOperand::PReg(V0),
                    MachOperand::PReg(V0),
                    MachOperand::PReg(V1),
                    MachOperand::Imm(5),
                ]
            );
            emit!(
                AArch64Opcode::NeonUmaxv,
                vec![
                    MachOperand::PReg(S0),
                    MachOperand::PReg(V0),
                    MachOperand::Imm(5),
                ]
            );
            emit!(
                AArch64Opcode::NeonUmovGen,
                vec![
                    MachOperand::PReg(W1),
                    MachOperand::PReg(V0),
                    MachOperand::Imm(0),
                    MachOperand::Imm(4),
                ]
            );
            let found_branch = emit!(
                AArch64Opcode::Cbnz,
                vec![MachOperand::PReg(W1), MachOperand::Imm(0)]
            );
            emit!(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::PReg(W13),
                    MachOperand::PReg(W13),
                    MachOperand::Imm(1),
                ]
            );
            let search_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

            let not_found = func.block(entry).insts.len();
            emit!(
                AArch64Opcode::Movz,
                vec![MachOperand::PReg(W0), MachOperand::Imm(0)]
            );
            emit!(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X7),
                    MachOperand::PReg(X9),
                ]
            );
            emit!(
                AArch64Opcode::StrbRI,
                vec![
                    MachOperand::PReg(W0),
                    MachOperand::PReg(X10),
                    MachOperand::Imm(0),
                ]
            );
            let false_next_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);
            $false_next_branches.push(false_next_branch);

            let found = func.block(entry).insts.len();
            patch_branch_imm(&mut func, entry, search_done_branch, 1, not_found);
            patch_branch_imm(&mut func, entry, search_loop_branch, 0, search_header);
            patch_branch_imm(&mut func, entry, found_branch, 1, found);
            let after_search = func.block(entry).insts.len();
            patch_branch_imm(&mut func, entry, skip_a_lane, 1, after_search);
        }};
    }

    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X16), MachOperand::PReg(X0)]
    );
    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X17), MachOperand::PReg(X1)]
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W8), MachOperand::Imm(0)]
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W9), MachOperand::Imm(0)]
    );

    let pair_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W9), MachOperand::PReg(W6)]
    );
    let pair_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ]
    );

    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X10),
            MachOperand::PReg(X9),
            MachOperand::Imm(2),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W11),
            MachOperand::PReg(X2),
            MachOperand::PReg(X10),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W12),
            MachOperand::PReg(X3),
            MachOperand::PReg(X10),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W14),
            MachOperand::PReg(X5),
            MachOperand::PReg(X10),
        ]
    );
    emit!(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(W13),
            MachOperand::PReg(X4),
            MachOperand::PReg(X10),
        ]
    );
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W11), MachOperand::PReg(W13)]
    );
    let same_start_miss_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::NE as i64),
            MachOperand::Imm(0),
        ]
    );
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W12), MachOperand::PReg(W14)]
    );
    let same_range_true_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::EQ as i64),
            MachOperand::Imm(0),
        ]
    );
    let after_same_range_fast_path = func.block(entry).insts.len();
    patch_branch_imm(
        &mut func,
        entry,
        same_start_miss_branch,
        1,
        after_same_range_fast_path,
    );
    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(W15), MachOperand::PReg(W11)]
    );

    let mut false_next_branches = Vec::new();
    let a_chunk_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W15), MachOperand::PReg(W12)]
    );
    let a_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ]
    );
    emit_a_lane_search!(0, 1, false_next_branches);
    emit_a_lane_search!(4, 2, false_next_branches);
    emit_a_lane_search!(8, 4, false_next_branches);
    emit_a_lane_search!(12, 8, false_next_branches);
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W15),
            MachOperand::PReg(W15),
            MachOperand::Imm(1),
        ]
    );
    let a_chunk_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let pair_true = func.block(entry).insts.len();
    patch_branch_imm(&mut func, entry, same_range_true_branch, 1, pair_true);
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W0), MachOperand::Imm(1)]
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X10),
            MachOperand::PReg(X7),
            MachOperand::PReg(X9),
        ]
    );
    emit!(
        AArch64Opcode::StrbRI,
        vec![
            MachOperand::PReg(W0),
            MachOperand::PReg(X10),
            MachOperand::Imm(0),
        ]
    );
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W8),
            MachOperand::PReg(W8),
            MachOperand::Imm(1),
        ]
    );

    let next_pair = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W9),
            MachOperand::PReg(W9),
            MachOperand::Imm(1),
        ]
    );
    let pair_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let done = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(W0), MachOperand::PReg(W8)]
    );
    emit!(AArch64Opcode::Ret, vec![]);

    patch_branch_imm(&mut func, entry, pair_done_branch, 1, done);
    patch_branch_imm(&mut func, entry, a_done_branch, 1, pair_true);
    patch_branch_imm(&mut func, entry, a_chunk_loop_branch, 0, a_chunk_header);
    patch_branch_imm(&mut func, entry, pair_loop_branch, 0, pair_header);
    for false_next_branch in false_next_branches {
        patch_branch_imm(&mut func, entry, false_next_branch, 0, next_pair);
    }
    materialize_resolved_probe_cfg_blocks(&mut func);

    func
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn build_trust_cg_batch_subsumption_repeated_checksum_backend_function() -> trust_cg_ir::MachFunction
{
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::AArch64Opcode;
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{
        S0, V0, V1, W0, W1, W3, W4, W6, W7, W9, W11, W12, W13, W14, W15, X0, X1, X2, X5, X7, X8,
        X9, X10, X11, X12, X13, X15, X16, X17,
    };

    fn patch_branch_imm(
        func: &mut MachFunction,
        block: trust_cg_ir::BlockId,
        branch_inst_pos: usize,
        imm_operand_index: usize,
        target_inst_pos: usize,
    ) {
        let inst_id = func.block(block).insts[branch_inst_pos];
        let displacement = target_inst_pos as i64 - branch_inst_pos as i64;
        func.inst_mut(inst_id).operands[imm_operand_index] = MachOperand::Imm(displacement);
    }

    let sig = Signature::new(
        vec![
            Type::Ptr,
            Type::Ptr,
            Type::Ptr,
            Type::I32,
            Type::I32,
            Type::Ptr,
        ],
        vec![Type::I64],
    );
    let mut func = MachFunction::new(
        TRUST_CG_BATCH_SUBSUMPTION_REPEATED_CHECKSUM_BACKEND_FN.to_string(),
        sig,
    );
    let entry = func.entry;

    macro_rules! emit {
        ($opcode:expr, $operands:expr $(,)?) => {{
            append_probe_inst(&mut func, entry, $opcode, $operands);
            let inst_pos = func.block(entry).insts.len() - 1;
            inst_pos
        }};
    }

    macro_rules! emit_record_base {
        () => {{
            emit!(
                AArch64Opcode::LslRI,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X9),
                    MachOperand::Imm(4),
                ],
            );
            emit!(
                AArch64Opcode::LslRI,
                vec![
                    MachOperand::PReg(X13),
                    MachOperand::PReg(X9),
                    MachOperand::Imm(3),
                ],
            );
            emit!(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X13),
                ],
            );
            emit!(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X2),
                    MachOperand::PReg(X10),
                ],
            );
        }};
    }

    macro_rules! emit_store_pair_result {
        ($actual:expr) => {{
            emit!(
                AArch64Opcode::Movz,
                vec![MachOperand::PReg(W0), MachOperand::Imm($actual)],
            );
            emit!(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X5),
                    MachOperand::PReg(X9),
                ],
            );
            emit!(
                AArch64Opcode::StrbRI,
                vec![
                    MachOperand::PReg(W0),
                    MachOperand::PReg(X10),
                    MachOperand::Imm(0),
                ],
            );
        }};
    }

    macro_rules! emit_a_lane_search {
        ($offset:expr, $valid_bit:expr, $false_cond_branches:ident) => {{
            emit!(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X17),
                    MachOperand::PReg(X15),
                ],
            );
            emit!(
                AArch64Opcode::LdrbRI,
                vec![
                    MachOperand::PReg(W0),
                    MachOperand::PReg(X10),
                    MachOperand::Imm(0),
                ],
            );
            emit!(
                AArch64Opcode::Movz,
                vec![MachOperand::PReg(W1), MachOperand::Imm($valid_bit)],
            );
            emit!(
                AArch64Opcode::AndRR,
                vec![
                    MachOperand::PReg(W1),
                    MachOperand::PReg(W0),
                    MachOperand::PReg(W1),
                ],
            );
            let skip_a_lane = emit!(
                AArch64Opcode::Cbz,
                vec![MachOperand::PReg(W1), MachOperand::Imm(0)],
            );

            emit!(
                AArch64Opcode::LslRI,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X15),
                    MachOperand::Imm(4),
                ],
            );
            emit!(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X16),
                    MachOperand::PReg(X10),
                ],
            );
            emit!(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(W11),
                    MachOperand::PReg(X10),
                    MachOperand::Imm($offset),
                ],
            );
            emit!(
                AArch64Opcode::NeonDupGen,
                vec![
                    MachOperand::PReg(V1),
                    MachOperand::PReg(W11),
                    MachOperand::Imm(4),
                ],
            );
            emit!(
                AArch64Opcode::MovR,
                vec![MachOperand::PReg(W0), MachOperand::PReg(W13)],
            );

            let search_header = func.block(entry).insts.len();
            emit!(
                AArch64Opcode::CmpRR,
                vec![MachOperand::PReg(W0), MachOperand::PReg(W14)],
            );
            let search_done_branch = emit!(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
                    MachOperand::Imm(0),
                ],
            );
            $false_cond_branches.push(search_done_branch);
            emit!(
                AArch64Opcode::LslRI,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X0),
                    MachOperand::Imm(4),
                ],
            );
            emit!(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X10),
                    MachOperand::PReg(X16),
                    MachOperand::PReg(X10),
                ],
            );
            emit!(
                AArch64Opcode::NeonLd1Post,
                vec![
                    MachOperand::PReg(V0),
                    MachOperand::PReg(X10),
                    MachOperand::Imm(5),
                ],
            );
            emit!(
                AArch64Opcode::NeonCmeqV,
                vec![
                    MachOperand::PReg(V0),
                    MachOperand::PReg(V0),
                    MachOperand::PReg(V1),
                    MachOperand::Imm(5),
                ],
            );
            emit!(
                AArch64Opcode::NeonUmaxv,
                vec![
                    MachOperand::PReg(S0),
                    MachOperand::PReg(V0),
                    MachOperand::Imm(5),
                ],
            );
            emit!(
                AArch64Opcode::NeonUmovGen,
                vec![
                    MachOperand::PReg(W1),
                    MachOperand::PReg(V0),
                    MachOperand::Imm(0),
                    MachOperand::Imm(4),
                ],
            );
            let found_branch = emit!(
                AArch64Opcode::Cbnz,
                vec![MachOperand::PReg(W1), MachOperand::Imm(0)],
            );
            emit!(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::PReg(W0),
                    MachOperand::PReg(W0),
                    MachOperand::Imm(1),
                ],
            );
            let search_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

            let found = func.block(entry).insts.len();
            patch_branch_imm(&mut func, entry, search_loop_branch, 0, search_header);
            patch_branch_imm(&mut func, entry, found_branch, 1, found);
            let after_search = func.block(entry).insts.len();
            patch_branch_imm(&mut func, entry, skip_a_lane, 1, after_search);
        }};
    }

    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X16), MachOperand::PReg(X0)],
    );
    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X17), MachOperand::PReg(X1)],
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X8), MachOperand::Imm(0)],
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W6), MachOperand::Imm(0)],
    );

    let repeat_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W6), MachOperand::PReg(W4)],
    );
    let repeat_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ],
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W7), MachOperand::Imm(0)],
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W9), MachOperand::Imm(0)],
    );

    let pair_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W9), MachOperand::PReg(W3)],
    );
    let pair_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ],
    );

    emit_record_base!();
    emit!(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(W11),
            MachOperand::PReg(X10),
            MachOperand::Imm(0),
        ],
    );
    emit!(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(W12),
            MachOperand::PReg(X10),
            MachOperand::Imm(4),
        ],
    );
    emit!(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(W13),
            MachOperand::PReg(X10),
            MachOperand::Imm(8),
        ],
    );
    emit!(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(W14),
            MachOperand::PReg(X10),
            MachOperand::Imm(12),
        ],
    );
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W11), MachOperand::PReg(W13)],
    );
    let same_start_miss_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::NE as i64),
            MachOperand::Imm(0),
        ],
    );
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W12), MachOperand::PReg(W14)],
    );
    let same_range_true_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::EQ as i64),
            MachOperand::Imm(0),
        ],
    );
    let after_same_range_fast_path = func.block(entry).insts.len();
    patch_branch_imm(
        &mut func,
        entry,
        same_start_miss_branch,
        1,
        after_same_range_fast_path,
    );

    let mut false_cond_branches = Vec::new();
    emit!(
        AArch64Opcode::SubRR,
        vec![
            MachOperand::PReg(W0),
            MachOperand::PReg(W12),
            MachOperand::PReg(W11),
        ],
    );
    emit!(
        AArch64Opcode::SubRR,
        vec![
            MachOperand::PReg(W1),
            MachOperand::PReg(W14),
            MachOperand::PReg(W13),
        ],
    );
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W0), MachOperand::PReg(W1)],
    );
    let more_a_chunks_false_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HI as i64),
            MachOperand::Imm(0),
        ],
    );
    false_cond_branches.push(more_a_chunks_false_branch);
    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(W15), MachOperand::PReg(W11)],
    );

    let a_chunk_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W15), MachOperand::PReg(W12)],
    );
    let a_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ],
    );
    emit_a_lane_search!(0, 1, false_cond_branches);
    emit_a_lane_search!(4, 2, false_cond_branches);
    emit_a_lane_search!(8, 4, false_cond_branches);
    emit_a_lane_search!(12, 8, false_cond_branches);
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W15),
            MachOperand::PReg(W15),
            MachOperand::Imm(1),
        ],
    );
    let a_chunk_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let pair_false = func.block(entry).insts.len();
    emit_store_pair_result!(0);
    let false_next_pair_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let pair_true = func.block(entry).insts.len();
    patch_branch_imm(&mut func, entry, same_range_true_branch, 1, pair_true);
    patch_branch_imm(&mut func, entry, a_done_branch, 1, pair_true);
    emit_store_pair_result!(1);
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W7),
            MachOperand::PReg(W7),
            MachOperand::Imm(1),
        ],
    );

    let next_pair = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W9),
            MachOperand::PReg(W9),
            MachOperand::Imm(1),
        ],
    );
    let pair_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let checksum_reset = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(W9), MachOperand::Imm(0)],
    );
    let checksum_header = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W9), MachOperand::PReg(W3)],
    );
    let checksum_done_branch = emit!(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(trust_cg_ir::AArch64CC::HS as i64),
            MachOperand::Imm(0),
        ],
    );
    emit_record_base!();
    emit!(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(W11),
            MachOperand::PReg(X10),
            MachOperand::Imm(16),
        ],
    );
    emit!(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(W12),
            MachOperand::PReg(X10),
            MachOperand::Imm(20),
        ],
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X10),
            MachOperand::PReg(X5),
            MachOperand::PReg(X9),
        ],
    );
    emit!(
        AArch64Opcode::LdrbRI,
        vec![
            MachOperand::PReg(W0),
            MachOperand::PReg(X10),
            MachOperand::Imm(0),
        ],
    );
    emit!(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X13), MachOperand::Imm(131)],
    );
    emit!(
        AArch64Opcode::MulRR,
        vec![
            MachOperand::PReg(X7),
            MachOperand::PReg(X7),
            MachOperand::PReg(X13),
        ],
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X7),
            MachOperand::PReg(X7),
            MachOperand::PReg(X11),
        ],
    );
    emit!(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(X12),
            MachOperand::PReg(X12),
            MachOperand::Imm(8),
        ],
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X7),
            MachOperand::PReg(X7),
            MachOperand::PReg(X12),
        ],
    );
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X7),
            MachOperand::PReg(X7),
            MachOperand::PReg(X0),
        ],
    );
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W9),
            MachOperand::PReg(W9),
            MachOperand::Imm(1),
        ],
    );
    let checksum_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let finish_repeat = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X8),
            MachOperand::PReg(X8),
            MachOperand::PReg(X7),
        ],
    );
    emit!(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(W6),
            MachOperand::PReg(W6),
            MachOperand::Imm(1),
        ],
    );
    let repeat_loop_branch = emit!(AArch64Opcode::B, vec![MachOperand::Imm(0)]);

    let done = func.block(entry).insts.len();
    emit!(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X0), MachOperand::PReg(X8)],
    );
    emit!(AArch64Opcode::Ret, vec![]);

    patch_branch_imm(&mut func, entry, repeat_done_branch, 1, done);
    patch_branch_imm(&mut func, entry, pair_done_branch, 1, checksum_reset);
    patch_branch_imm(&mut func, entry, a_chunk_loop_branch, 0, a_chunk_header);
    patch_branch_imm(&mut func, entry, false_next_pair_branch, 0, next_pair);
    patch_branch_imm(&mut func, entry, pair_loop_branch, 0, pair_header);
    patch_branch_imm(&mut func, entry, checksum_done_branch, 1, finish_repeat);
    patch_branch_imm(&mut func, entry, checksum_loop_branch, 0, checksum_header);
    patch_branch_imm(&mut func, entry, repeat_loop_branch, 0, repeat_header);
    for false_cond_branch in false_cond_branches {
        patch_branch_imm(&mut func, entry, false_cond_branch, 1, pair_false);
    }
    materialize_resolved_probe_cfg_blocks(&mut func);

    func
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn build_trust_cg_contains4_masked_probe_function() -> trust_cg_ir::MachFunction {
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::AArch64Opcode;
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{W0, W1, W2, W3, W4, W5, W6, W7, W8, W9, W10, X0};

    let sig = Signature::new(vec![Type::Ptr, Type::I32, Type::I32], vec![Type::I32]);
    let mut func = MachFunction::new(TRUST_CG_CONTAINS4_MASKED_PROBE_FN.to_string(), sig);
    let entry = func.entry;

    for (dst, offset) in [(W3, 0), (W4, 4), (W5, 8), (W6, 12)] {
        append_probe_inst(
            &mut func,
            entry,
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::PReg(dst),
                MachOperand::PReg(X0),
                MachOperand::Imm(offset),
            ],
        );
    }

    // Build a 4-bit equality mask, then clear invalid padding lanes.
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W3), MachOperand::PReg(W1)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CSet,
        vec![MachOperand::PReg(W7), MachOperand::Imm(0)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W4), MachOperand::PReg(W1)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CSet,
        vec![MachOperand::PReg(W8), MachOperand::Imm(0)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(W8),
            MachOperand::PReg(W8),
            MachOperand::Imm(1),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W5), MachOperand::PReg(W1)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CSet,
        vec![MachOperand::PReg(W9), MachOperand::Imm(0)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(W9),
            MachOperand::PReg(W9),
            MachOperand::Imm(2),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(W6), MachOperand::PReg(W1)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::CSet,
        vec![MachOperand::PReg(W10), MachOperand::Imm(0)],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(W10),
            MachOperand::PReg(W10),
            MachOperand::Imm(3),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::OrrRR,
        vec![
            MachOperand::PReg(W7),
            MachOperand::PReg(W7),
            MachOperand::PReg(W8),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::OrrRR,
        vec![
            MachOperand::PReg(W7),
            MachOperand::PReg(W7),
            MachOperand::PReg(W9),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::OrrRR,
        vec![
            MachOperand::PReg(W7),
            MachOperand::PReg(W7),
            MachOperand::PReg(W10),
        ],
    );
    append_probe_inst(
        &mut func,
        entry,
        AArch64Opcode::AndRR,
        vec![
            MachOperand::PReg(W0),
            MachOperand::PReg(W7),
            MachOperand::PReg(W2),
        ],
    );

    append_probe_inst(&mut func, entry, AArch64Opcode::Ret, vec![]);
    func
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn append_probe_inst(
    func: &mut trust_cg_ir::MachFunction,
    block: trust_cg_ir::BlockId,
    opcode: trust_cg_ir::AArch64Opcode,
    operands: Vec<trust_cg_ir::MachOperand>,
) {
    let inst_id = func.push_inst(trust_cg_ir::MachInst::new(opcode, operands));
    func.append_inst(block, inst_id);
}

/// Turn a flat, already-resolved raw-JIT probe stream into an honest CFG.
///
/// These hand-built AArch64 probes use instruction-relative immediates because
/// `JitCompiler::compile_raw` consumes post-register-allocation MachIR.  Keeping
/// every instruction in the entry block used to work only because the final
/// encoder trusted that flat stream.  The post-RA verifier now reconstructs
/// control flow from those immediates and correctly rejects a branch whose
/// destination is hidden in the middle of a declared block.  Split at every
/// destination and every post-terminator fallthrough so the declared blocks,
/// the encoded branch targets, and verifier dataflow all describe the same
/// program.
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn materialize_resolved_probe_cfg_blocks(func: &mut trust_cg_ir::MachFunction) {
    use trust_cg_ir::{AArch64Opcode, BlockId};

    let entry = func.entry;
    assert_eq!(
        func.block_order.as_slice(),
        &[entry],
        "resolved probe CFG materialization expects one flat entry block"
    );

    let flat_insts = func.block(entry).insts.clone();
    if flat_insts.is_empty() {
        return;
    }

    let mut block_starts = BTreeSet::from([0usize]);
    let mut resolved_targets = BTreeMap::<usize, usize>::new();
    let mut conditional_branches = BTreeSet::new();
    let mut hard_terminators = BTreeSet::new();

    for (position, &inst_id) in flat_insts.iter().enumerate() {
        let inst = func.inst(inst_id);
        let (target_operand, conditional, hard_terminator) = match inst.opcode {
            AArch64Opcode::B | AArch64Opcode::TailCall => (Some(0), false, true),
            AArch64Opcode::BCond
            | AArch64Opcode::Bcc
            | AArch64Opcode::Cbz
            | AArch64Opcode::Cbnz => (Some(1), true, false),
            AArch64Opcode::Tbz | AArch64Opcode::Tbnz => (Some(2), true, false),
            AArch64Opcode::Br | AArch64Opcode::Ret => (None, false, true),
            _ => continue,
        };

        if let Some(operand_index) = target_operand
            && let Some(displacement) = inst
                .operands
                .get(operand_index)
                .and_then(trust_cg_ir::MachOperand::as_imm)
        {
            let target = position as i64 + displacement;
            assert!(
                (0..flat_insts.len() as i64).contains(&target),
                "resolved probe branch at instruction {position} has out-of-range target {target}"
            );
            let target = target as usize;
            block_starts.insert(target);
            resolved_targets.insert(position, target);
            if conditional {
                conditional_branches.insert(position);
            }
        }

        if hard_terminator {
            hard_terminators.insert(position);
        }
        if position + 1 < flat_insts.len() {
            block_starts.insert(position + 1);
        }
    }

    let block_starts = block_starts.into_iter().collect::<Vec<_>>();
    let flat_insts = std::mem::take(&mut func.block_mut(entry).insts);
    func.block_mut(entry).preds.clear();
    func.block_mut(entry).succs.clear();

    let mut blocks_by_start = BTreeMap::<usize, BlockId>::new();
    for (index, &start) in block_starts.iter().enumerate() {
        let end = block_starts
            .get(index + 1)
            .copied()
            .unwrap_or(flat_insts.len());
        let block = if index == 0 {
            entry
        } else {
            func.create_block()
        };
        func.block_mut(block)
            .insts
            .extend_from_slice(&flat_insts[start..end]);
        blocks_by_start.insert(start, block);
    }

    let mut edges = BTreeSet::<(BlockId, BlockId)>::new();
    for (index, &start) in block_starts.iter().enumerate() {
        let end = block_starts
            .get(index + 1)
            .copied()
            .unwrap_or(flat_insts.len());
        let source = blocks_by_start[&start];
        let last_position = end - 1;
        let fallthrough = block_starts
            .get(index + 1)
            .map(|next| blocks_by_start[next]);

        if let Some(&target_position) = resolved_targets.get(&last_position) {
            edges.insert((source, blocks_by_start[&target_position]));
            if conditional_branches.contains(&last_position)
                && let Some(fallthrough) = fallthrough
            {
                edges.insert((source, fallthrough));
            }
        } else if !hard_terminators.contains(&last_position)
            && let Some(fallthrough) = fallthrough
        {
            edges.insert((source, fallthrough));
        }
    }

    for (source, target) in edges {
        func.block_mut(source).succs.push(target);
        func.block_mut(target).preds.push(source);
    }
}

fn find_clauses_containing(clauses: &[ClauseCase], literal: i32) -> Vec<usize> {
    clauses
        .iter()
        .filter(|clause| clause.lits.contains(&literal))
        .map(|clause| clause.id)
        .collect()
}

fn clause_subsumes(a: &ClauseCase, b: &ClauseCase) -> bool {
    a.lits.iter().all(|literal| b.lits.contains(literal))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ay_subsumption_cases_fixture() -> AYSubsumptionCases {
        serde_json::from_str(include_str!("../tests/fixtures/ay_subsumption_cases.json"))
            .expect("fixture should parse")
    }

    #[test]
    fn load_ay_subsumption_cases_rejects_oversized_file_before_reading() {
        let path = std::env::temp_dir().join(format!(
            "trust-cg-jit-matrix-oversized-cases-{}-{}.json",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let file = fs::File::create(&path).unwrap();
        file.set_len(MAX_AY_SUBSUMPTION_CASES_BYTES + 1).unwrap();
        drop(file);

        let error = load_ay_subsumption_cases(&path).unwrap_err();
        let _ = fs::remove_file(&path);

        assert!(
            error.to_string().contains("over limit"),
            "unexpected error: {error:?}"
        );
    }

    fn phase8_test_scope() -> Phase8NativePromotionCounterScope {
        Phase8NativePromotionCounterScope {
            consumer: "ay".to_string(),
            family: PHASE8_AY_SUBSUMPTION_COUNTER_FAMILY.to_string(),
            mode: PHASE8_NATIVE_PROMOTION_CANARY_MODE.to_string(),
            target_triple: "aarch64-apple-darwin".to_string(),
            target_cpu: "test-cpu".to_string(),
            target_features_sha256: "test-target-features".to_string(),
            proof_policy_sha256: "test-proof-policy".to_string(),
            layout_checksum: "test-layout".to_string(),
            invalidation_key: "test-invalidation-key".to_string(),
            manifest_sha256: Some(
                "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".to_string(),
            ),
            expected_manifest_sha256: Some(
                "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".to_string(),
            ),
        }
    }

    fn phase8_ty_test_scope() -> Phase8NativePromotionCounterScope {
        Phase8NativePromotionCounterScope {
            consumer: "ty".to_string(),
            family: PHASE8_TY_PARENT_LOOP_COUNTER_FAMILY.to_string(),
            mode: PHASE8_NATIVE_PROMOTION_CANARY_MODE.to_string(),
            target_triple: "aarch64-apple-darwin".to_string(),
            target_cpu: "test-cpu".to_string(),
            target_features_sha256: "test-target-features".to_string(),
            proof_policy_sha256: "test-proof-policy".to_string(),
            layout_checksum: "test-layout".to_string(),
            invalidation_key: "test-invalidation-key".to_string(),
            manifest_sha256: Some(
                "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".to_string(),
            ),
            expected_manifest_sha256: Some(
                "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".to_string(),
            ),
        }
    }

    fn phase8_ty_profile_generate_report() -> Phase8TyProfileReportBinding {
        Phase8TyProfileReportBinding {
            report_identity: Some("reports/perf/test-mcl/profile-generate.json".to_string()),
            report_sha256: Some("sha256:test-profile-generate-report".to_string()),
            profile_sha256: Some("sha256:test-ty-profdata".to_string()),
            profile_key_digest: Some("test-ty-profile-key".to_string()),
        }
    }

    fn phase8_ty_profile_use_report() -> Phase8TyProfileUseReportBinding {
        Phase8TyProfileUseReportBinding {
            report_identity: Some("reports/perf/test-mcl/profile-use.json".to_string()),
            report_sha256: Some("sha256:test-profile-use-report".to_string()),
            profile_sha256: Some("sha256:test-ty-profdata".to_string()),
            profile_key_digest: Some("test-ty-profile-key".to_string()),
            fresh: Some(true),
            freshness_reason: Some("opt-level-enables-profile-use".to_string()),
            scheduled: Some(true),
        }
    }

    fn phase8_ty_mcl_evidence() -> Phase8TyParentLoopEvidence {
        Phase8TyParentLoopEvidence {
            spec_name: "MCLamportMutex".to_string(),
            artifact_root: Some("reports/perf/test-mcl".to_string()),
            state_layout_sha256: Some("test-state-layout".to_string()),
            transition_cluster_sha256: Some("test-transition-cluster".to_string()),
            profile_generate_report: phase8_ty_profile_generate_report(),
            profile_use_report: phase8_ty_profile_use_report(),
            downstream_cli_passed: Some(true),
            strict_selftest_completed: true,
            native_fused_path_active: true,
            compiled_bfs_level_loop_fused: true,
            native_dispatch_promoted: true,
            non_promoting: false,
            expected_action_count: 27,
            actual_action_count: Some(27),
            expected_invariant_count: 3,
            actual_invariant_count: Some(3),
            expected_state_constraint_count: 1,
            actual_state_constraint_count: Some(1),
            expected_state_len: 89,
            actual_state_len: Some(89),
            flat_state_copy_bytes: 8192,
            fingerprint_count: 64,
            fingerprint_bytes: 512,
            helper_inline_count: 6,
            alias_readonly_metadata_hit_count: 4,
            compiled_bfs_levels_completed: 4,
            compiled_bfs_parents_processed: 32,
            compiled_bfs_successors_generated: 128,
            compiled_bfs_successors_new: 64,
            compiled_bfs_total_states: 65,
            eligible_native_call_count: 32,
            native_call_count: 32,
            baseline_call_count: 32,
            useful_native_call_count: 32,
            fallback_count: 0,
            deopt_count: 0,
            native_status_error_count: 0,
            shadow_mismatch_count: 0,
            crash_count: 0,
            crash_packet_count: 0,
            internal_error_count: 0,
            replay_artifact_count: 1,
            telemetry_artifact_count: 1,
            cache_hit_count: 3,
            cache_miss_count: 1,
        }
    }

    fn phase8_blocker_codes(
        counters: &Phase8NativePromotionCounters,
    ) -> std::collections::BTreeSet<&str> {
        phase8_blocker_codes_from_verdict(&counters.promotion_verdict)
    }

    fn phase8_ty_blocker_codes(
        counters: &Phase8TyNativePromotionCounters,
    ) -> std::collections::BTreeSet<&str> {
        phase8_blocker_codes_from_verdict(&counters.promotion_verdict)
    }

    fn phase8_blocker_codes_from_verdict(
        verdict: &Phase8PromotionVerdict,
    ) -> std::collections::BTreeSet<&str> {
        verdict
            .blockers
            .iter()
            .map(|blocker| blocker.code.as_str())
            .collect()
    }

    #[test]
    fn ay_subsumption_fixture_matches_scalar_oracle() {
        let cases = ay_subsumption_cases_fixture();
        let report = validate_ay_subsumption_cases(&cases).expect("fixture should validate");

        assert_eq!(report.workload.issue, 571);
        assert_eq!(report.mismatch_count, 0);
        assert_eq!(report.workload.clause_count, 15);
        assert_eq!(
            report.workload.variants,
            [
                "ay_neon_reference",
                "trust_cg_o2_vectorized",
                "trust_cg_o3_vectorized",
                "trust_cg_o2_disable_vec",
                "trust_cg_o3_disable_vec"
            ]
        );
    }

    #[test]
    fn ay_subsumption_planned_throughput_schema_covers_full_matrix() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let throughput = planned_ay_subsumption_throughput(&correctness);

        assert_eq!(
            throughput.schema,
            "trust-cg.ay_subsumption.throughput_summary.v1"
        );
        assert_eq!(throughput.status, "plan_only");
        assert_eq!(
            throughput.rows.len(),
            2 * correctness.workload.length_buckets.len() * correctness.workload.variants.len()
        );
        assert_eq!(
            throughput.row_accounting.planned_rows,
            throughput.rows.len()
        );
        assert_eq!(throughput.row_accounting.measured_ay_reference_rows, 0);
        assert_eq!(
            throughput.row_accounting.measured_trust_cg_mixed_probe_rows,
            0
        );
        assert_eq!(
            throughput
                .row_accounting
                .measured_trust_cg_bucket_probe_rows,
            0
        );
        assert_eq!(
            throughput.row_accounting.pending_backend_rows,
            throughput.rows.len()
        );
        assert!(
            throughput
                .rows
                .iter()
                .all(|row| row.status == "pending_backend"
                    && row.promotion_disposition == TRUST_CG_PENDING_PROMOTION_DISPOSITION
                    && !row.product_install_evidence
                    && row.mean_throughput_per_us.is_none()
                    && row.ay_relative_ratio.is_none())
        );
        assert_eq!(throughput.gate.required_ay_relative_geomean, 0.90);
        assert_eq!(
            ay_subsumption_throughput_csv_header(),
            "operation,length_bucket,variant,repetition,elapsed_ns,items,throughput_per_us,status\n"
        );
    }

    #[test]
    fn ay_reference_execution_populates_only_mixed_reference_rows() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let execution = fake_ay_reference_execution();
        let throughput =
            planned_ay_subsumption_throughput_with_ay_reference(&correctness, Some(&execution));

        assert_eq!(throughput.status, "partial_ay_reference");
        let measured = throughput
            .rows
            .iter()
            .filter(|row| row.status == "ay_reference_measured")
            .collect::<Vec<_>>();
        assert_eq!(measured.len(), 2);
        assert_eq!(throughput.row_accounting.measured_ay_reference_rows, 2);
        assert_eq!(throughput.row_accounting.pending_backend_rows, 158);
        assert!(measured.iter().all(|row| {
            row.variant == "ay_neon_reference"
                && row.length_bucket == "mixed_2_16"
                && row.promotion_disposition == TRUST_CG_REFERENCE_PROMOTION_DISPOSITION
                && !row.product_install_evidence
                && row.ay_relative_ratio == Some(1.0)
                && row.mean_throughput_per_us.is_some()
        }));
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| row.status == "pending_backend")
                .count(),
            throughput.rows.len() - measured.len()
        );
        assert_eq!(throughput.gate.trust_cg_o2_vectorized_geomean, None);
        assert_eq!(throughput.gate.trust_cg_o3_vectorized_geomean, None);
        assert_eq!(throughput.gate.passed, None);

        let csv = ay_subsumption_throughput_csv(Some(&execution));
        assert_eq!(csv.lines().count(), 5);
        assert_eq!(
            csv.lines().next().expect("csv header"),
            ay_subsumption_throughput_csv_header().trim_end()
        );
        assert!(csv.contains("ay_neon_reference"));
        assert!(csv.contains("ay_reference_measured"));
    }

    #[test]
    fn ay_reference_bucket_rows_supply_matching_trust_cg_ratios_without_gate() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let ay_execution = fake_ay_reference_execution_with_buckets(&["4", "8", "16"]);
        let trust_cg_probe = fake_trust_cg_backend_probe_with_buckets(&["4", "8", "16"]);
        let buckets = vec!["4".to_string(), "8".to_string(), "16".to_string()];
        let throughput = planned_ay_subsumption_throughput_with_probe_buckets(
            &correctness,
            Some(&ay_execution),
            Some(&trust_cg_probe),
            true,
            &buckets,
        );

        assert_eq!(
            throughput.status,
            "partial_ay_reference_and_trust_cg_probe_rows"
        );
        let ay_bucket_rows = throughput
            .rows
            .iter()
            .filter(|row| {
                row.variant == "ay_neon_reference"
                    && ["4", "8", "16"].contains(&row.length_bucket.as_str())
                    && row.status == "ay_reference_measured"
            })
            .collect::<Vec<_>>();
        assert_eq!(ay_bucket_rows.len(), 6);
        assert!(ay_bucket_rows.iter().all(|row| {
            row.mean_throughput_per_us.is_some() && row.ay_relative_ratio == Some(1.0)
        }));

        let trust_cg_bucket_rows = throughput
            .rows
            .iter()
            .filter(|row| row.status == TRUST_CG_PROBE_BUCKET_ROW_STATUS)
            .collect::<Vec<_>>();
        assert_eq!(trust_cg_bucket_rows.len(), 24);
        assert!(trust_cg_bucket_rows.iter().all(|row| {
            ["4", "8", "16"].contains(&row.length_bucket.as_str())
                && row.promotion_disposition == TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION
                && !row.product_install_evidence
                && row.mean_throughput_per_us.is_some()
                && row.ay_relative_ratio.is_some()
        }));
        assert_eq!(throughput.row_accounting.measured_ay_reference_rows, 8);
        assert_eq!(
            throughput.row_accounting.measured_trust_cg_mixed_probe_rows,
            8
        );
        assert_eq!(
            throughput
                .row_accounting
                .measured_trust_cg_bucket_probe_rows,
            24
        );
        assert_eq!(throughput.row_accounting.pending_backend_rows, 120);
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| row.status == "pending_backend")
                .count(),
            120
        );
        assert_eq!(throughput.gate.trust_cg_o2_vectorized_geomean, None);
        assert_eq!(throughput.gate.trust_cg_o3_vectorized_geomean, None);
        assert_eq!(throughput.gate.passed, None);

        let csv = ay_subsumption_throughput_csv_with_probe_buckets(
            Some(&ay_execution),
            Some(&trust_cg_probe),
            true,
            &buckets,
        );
        assert!(csv.contains(",4,ay_neon_reference,"));
        assert!(csv.contains(",8,ay_neon_reference,"));
        assert!(csv.contains(",16,ay_neon_reference,"));
        assert!(csv.contains(",4,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",8,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",16,trust_cg_o2_vectorized,"));
    }

    #[test]
    fn all_ay_numeric_bucket_rows_account_without_gate() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let buckets = ay_numeric_length_buckets(&correctness.workload.length_buckets);
        let expected_buckets = (2..=16)
            .map(|length| length.to_string())
            .collect::<Vec<_>>();
        assert_eq!(buckets, expected_buckets);

        let bucket_refs = buckets.iter().map(String::as_str).collect::<Vec<_>>();
        let ay_execution = fake_ay_reference_execution_with_buckets(&bucket_refs);
        let throughput = planned_ay_subsumption_throughput_with_probe_buckets(
            &correctness,
            Some(&ay_execution),
            None,
            false,
            &[],
        );

        assert_eq!(throughput.status, "partial_ay_reference");
        assert_eq!(throughput.row_accounting.planned_rows, 160);
        assert_eq!(throughput.row_accounting.measured_ay_reference_rows, 32);
        assert_eq!(
            throughput.row_accounting.measured_trust_cg_mixed_probe_rows,
            0
        );
        assert_eq!(
            throughput
                .row_accounting
                .measured_trust_cg_bucket_probe_rows,
            0
        );
        assert_eq!(throughput.row_accounting.pending_backend_rows, 128);
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| row.variant == "ay_neon_reference"
                    && row.status == "ay_reference_measured")
                .count(),
            32
        );
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| row.status == "pending_backend")
                .count(),
            128
        );
        assert_eq!(throughput.gate.trust_cg_o2_vectorized_geomean, None);
        assert_eq!(throughput.gate.trust_cg_o3_vectorized_geomean, None);
        assert_eq!(throughput.gate.passed, None);

        let csv =
            ay_subsumption_throughput_csv_with_probe_buckets(Some(&ay_execution), None, false, &[]);
        assert!(csv.contains(",2,ay_neon_reference,"));
        assert!(csv.contains(",15,ay_neon_reference,"));
        assert!(!csv.contains(TRUST_CG_PROBE_MIXED_ROW_STATUS));
        assert!(!csv.contains(TRUST_CG_PROBE_BUCKET_ROW_STATUS));
        assert_eq!(csv.lines().count(), 65);
    }

    #[test]
    fn trust_cg_probe_mixed_rows_populate_partial_throughput_without_gate() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let ay_execution = fake_ay_reference_execution();
        let trust_cg_probe = fake_trust_cg_backend_probe();
        let throughput = planned_ay_subsumption_throughput_with_backend_execution(
            &correctness,
            Some(&ay_execution),
            Some(&trust_cg_probe),
            true,
        );

        assert_eq!(
            throughput.status,
            "partial_ay_reference_and_trust_cg_mixed_probe"
        );
        let trust_cg_measured = throughput
            .rows
            .iter()
            .filter(|row| row.status == TRUST_CG_PROBE_MIXED_ROW_STATUS)
            .collect::<Vec<_>>();
        assert_eq!(trust_cg_measured.len(), 8);
        assert!(trust_cg_measured.iter().all(|row| {
            row.variant.starts_with("trust_cg_")
                && row.length_bucket == "mixed_2_16"
                && row.promotion_disposition == TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION
                && !row.product_install_evidence
                && row.mean_throughput_per_us.is_some()
                && row.ay_relative_ratio.is_some()
        }));
        assert!(
            throughput
                .rows
                .iter()
                .find(|row| {
                    row.operation == "contains_literal"
                        && row.variant == "trust_cg_o2_vectorized"
                        && row.length_bucket == "mixed_2_16"
                })
                .expect("o2 vectorized mixed row")
                .scalar_speedup
                .is_some()
        );
        assert_eq!(throughput.gate.trust_cg_o2_vectorized_geomean, None);
        assert_eq!(throughput.gate.trust_cg_o3_vectorized_geomean, None);
        assert_eq!(throughput.gate.passed, None);

        let counters = phase8_ay_subsumption_native_promotion_counters(
            &correctness,
            &throughput,
            phase8_test_scope(),
        );
        assert_eq!(
            counters.lifecycle.profile_only_compiled_count,
            throughput.row_accounting.measured_trust_cg_mixed_probe_rows
        );
        assert_eq!(
            counters
                .consumer
                .ay
                .usefulness
                .profile_only_application_count,
            throughput.row_accounting.measured_trust_cg_mixed_probe_rows
        );
        assert_eq!(counters.dispatch.useful_native_count, 0);
        assert!(!counters.promotion_verdict.can_promote_beyond_canary);

        let csv = ay_subsumption_throughput_csv_with_backend_execution(
            Some(&ay_execution),
            Some(&trust_cg_probe),
            true,
        );
        assert!(csv.contains(TRUST_CG_PROBE_MIXED_ROW_STATUS));
        assert!(csv.contains("trust_cg_o2_vectorized"));
        assert_eq!(csv.lines().count(), 21);
    }

    #[test]
    fn trust_cg_probe_bucket_rows_populate_selected_bucket_without_gate() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let ay_execution = fake_ay_reference_execution();
        let trust_cg_probe = fake_trust_cg_backend_probe_with_bucket("4");
        let buckets = vec!["4".to_string()];
        let throughput = planned_ay_subsumption_throughput_with_probe_buckets(
            &correctness,
            Some(&ay_execution),
            Some(&trust_cg_probe),
            true,
            &buckets,
        );

        assert_eq!(
            throughput.status,
            "partial_ay_reference_and_trust_cg_probe_rows"
        );
        let bucket_rows = throughput
            .rows
            .iter()
            .filter(|row| row.status == TRUST_CG_PROBE_BUCKET_ROW_STATUS)
            .collect::<Vec<_>>();
        assert_eq!(bucket_rows.len(), 8);
        assert_eq!(
            throughput
                .row_accounting
                .measured_trust_cg_bucket_probe_rows,
            8
        );
        assert!(bucket_rows.iter().all(|row| {
            row.variant.starts_with("trust_cg_")
                && row.length_bucket == "4"
                && row.promotion_disposition == TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION
                && !row.product_install_evidence
                && row.mean_throughput_per_us.is_some()
                && row.ay_relative_ratio.is_none()
        }));
        assert!(
            throughput
                .rows
                .iter()
                .find(|row| {
                    row.operation == "contains_literal"
                        && row.variant == "trust_cg_o2_vectorized"
                        && row.length_bucket == "4"
                })
                .expect("o2 vectorized bucket row")
                .scalar_speedup
                .is_some()
        );
        assert_eq!(throughput.gate.trust_cg_o2_vectorized_geomean, None);
        assert_eq!(throughput.gate.trust_cg_o3_vectorized_geomean, None);
        assert_eq!(throughput.gate.passed, None);

        let csv = ay_subsumption_throughput_csv_with_probe_buckets(
            Some(&ay_execution),
            Some(&trust_cg_probe),
            true,
            &buckets,
        );
        assert!(csv.contains(TRUST_CG_PROBE_BUCKET_ROW_STATUS));
        assert!(csv.contains(",4,trust_cg_o2_vectorized,"));
        assert_eq!(csv.lines().count(), 37);

        let bucket_only_csv = ay_subsumption_throughput_csv_with_probe_buckets(
            Some(&ay_execution),
            Some(&trust_cg_probe),
            false,
            &buckets,
        );
        assert!(bucket_only_csv.contains(TRUST_CG_PROBE_BUCKET_ROW_STATUS));
        assert!(bucket_only_csv.contains(",4,trust_cg_o2_vectorized,"));
        assert!(!bucket_only_csv.contains(TRUST_CG_PROBE_MIXED_ROW_STATUS));
        assert_eq!(bucket_only_csv.lines().count(), 21);
    }

    #[test]
    fn trust_cg_backend_bucket_rows_populate_selected_buckets_without_gate() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let ay_numeric_buckets = ay_numeric_length_buckets(&correctness.workload.length_buckets);
        let ay_bucket_refs = ay_numeric_buckets
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let ay_execution = fake_ay_reference_execution_with_buckets(&ay_bucket_refs);
        let backend_bucket_labels = [
            "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16",
        ];
        let trust_cg_backend = fake_trust_cg_backend_execution_with_buckets(&backend_bucket_labels);
        let backend_buckets = backend_bucket_labels
            .iter()
            .map(|bucket| bucket.to_string())
            .collect::<Vec<_>>();
        let throughput = planned_ay_subsumption_throughput_with_backend_buckets(
            &correctness,
            Some(&ay_execution),
            None,
            false,
            &[],
            Some(&trust_cg_backend),
            &backend_buckets,
        );
        assert_eq!(
            throughput.status,
            "partial_ay_reference_and_trust_cg_backend_rows"
        );
        assert_eq!(throughput.row_accounting.measured_ay_reference_rows, 32);
        assert_eq!(
            throughput
                .row_accounting
                .measured_trust_cg_bucket_probe_rows,
            0
        );
        assert_eq!(
            throughput.row_accounting.measured_trust_cg_backend_rows,
            120
        );
        assert_eq!(throughput.row_accounting.pending_backend_rows, 8);
        let pending_numeric_buckets = throughput
            .rows
            .iter()
            .filter(|row| {
                row.status == "pending_backend"
                    && row.variant.starts_with("trust_cg_")
                    && row.length_bucket.parse::<usize>().is_ok()
            })
            .map(|row| row.length_bucket.clone())
            .collect::<BTreeSet<_>>();
        assert!(pending_numeric_buckets.is_empty());
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| {
                    row.status == "pending_backend"
                        && row.variant.starts_with("trust_cg_")
                        && row.length_bucket == "mixed_2_16"
                })
                .count(),
            8
        );
        let backend_rows = throughput
            .rows
            .iter()
            .filter(|row| row.status == TRUST_CG_BACKEND_BUCKET_ROW_STATUS)
            .collect::<Vec<_>>();
        assert_eq!(backend_rows.len(), 120);
        assert!(backend_rows.iter().all(|row| {
            row.variant.starts_with("trust_cg_")
                && backend_bucket_labels.contains(&row.length_bucket.as_str())
                && row.mean_throughput_per_us.is_some()
                && row.ay_relative_ratio.is_some()
        }));
        assert!(backend_rows.iter().all(|row| {
            let vectorized = trust_cg_scalar_control_variant(&row.variant).is_some();
            row.product_install_evidence == vectorized
                && row.promotion_disposition
                    == if vectorized {
                        TRUST_CG_BACKEND_PROMOTION_DISPOSITION
                    } else {
                        TRUST_CG_BACKEND_SCALAR_CONTROL_PROMOTION_DISPOSITION
                    }
        }));
        assert!(backend_rows.iter().all(|row| {
            throughput.rows.iter().all(|candidate| {
                candidate.status != TRUST_CG_PROBE_BUCKET_ROW_STATUS
                    || candidate.length_bucket != row.length_bucket
            })
        }));
        assert!(
            throughput
                .rows
                .iter()
                .find(|row| {
                    row.operation == "contains_literal"
                        && row.variant == "trust_cg_o2_vectorized"
                        && row.length_bucket == "4"
                })
                .expect("o2 vectorized backend bucket row")
                .scalar_speedup
                .is_some()
        );
        assert_eq!(throughput.gate.trust_cg_o2_vectorized_geomean, None);
        assert_eq!(throughput.gate.trust_cg_o3_vectorized_geomean, None);
        assert_eq!(throughput.gate.passed, None);

        let csv = ay_subsumption_throughput_csv_with_backend_buckets(
            Some(&ay_execution),
            None,
            false,
            &[],
            Some(&trust_cg_backend),
            &backend_buckets,
        );
        assert!(csv.contains(TRUST_CG_BACKEND_BUCKET_ROW_STATUS));
        assert!(csv.contains(",2,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",3,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",4,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",5,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",6,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",7,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",8,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",9,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",10,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",11,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",12,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",13,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",14,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",15,trust_cg_o2_vectorized,"));
        assert!(csv.contains(",16,trust_cg_o2_vectorized,"));
        assert!(!csv.contains(TRUST_CG_PROBE_BUCKET_ROW_STATUS));
        assert_eq!(csv.lines().count(), 305);
    }

    #[test]
    fn trust_cg_backend_full_rows_populate_mixed_rows_and_gate() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let ay_numeric_buckets = ay_numeric_length_buckets(&correctness.workload.length_buckets);
        let ay_bucket_refs = ay_numeric_buckets
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let ay_execution = fake_ay_reference_execution_with_buckets(&ay_bucket_refs);
        let backend_bucket_labels = [
            "2",
            "3",
            "4",
            "5",
            "6",
            "7",
            "8",
            "9",
            "10",
            "11",
            "12",
            "13",
            "14",
            "15",
            "16",
            "mixed_2_16",
        ];
        let trust_cg_backend = fake_trust_cg_backend_execution_with_buckets(&backend_bucket_labels);
        let backend_buckets = ay_numeric_buckets;
        let throughput = planned_ay_subsumption_throughput_with_backend_buckets(
            &correctness,
            Some(&ay_execution),
            None,
            false,
            &[],
            Some(&trust_cg_backend),
            &backend_buckets,
        );

        assert_eq!(
            throughput.status,
            "complete_ay_reference_and_trust_cg_backend_rows"
        );
        assert_eq!(throughput.row_accounting.planned_rows, 160);
        assert_eq!(throughput.row_accounting.measured_ay_reference_rows, 32);
        assert_eq!(
            throughput.row_accounting.measured_trust_cg_backend_rows,
            128
        );
        assert_eq!(throughput.row_accounting.pending_backend_rows, 0);
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| row.status == TRUST_CG_BACKEND_BUCKET_ROW_STATUS)
                .count(),
            120
        );
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| row.status == TRUST_CG_BACKEND_MIXED_ROW_STATUS)
                .count(),
            8
        );
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| phase8_ay_product_backend_row(row))
                .count(),
            64
        );
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| is_trust_cg_backend_throughput_status(row.status)
                    && !row.product_install_evidence
                    && row.promotion_disposition
                        == TRUST_CG_BACKEND_SCALAR_CONTROL_PROMOTION_DISPOSITION)
                .count(),
            64
        );
        assert!(throughput.rows.iter().all(|row| {
            row.status != "pending_backend"
                && (row.variant == "ay_neon_reference" || row.ay_relative_ratio.is_some())
        }));
        assert!(
            (throughput
                .gate
                .trust_cg_o2_vectorized_geomean
                .expect("o2 geomean")
                - 1.4)
                .abs()
                < 1e-12
        );
        assert!(
            (throughput
                .gate
                .trust_cg_o3_vectorized_geomean
                .expect("o3 geomean")
                - 1.4)
                .abs()
                < 1e-12
        );
        assert_eq!(throughput.gate.passed, Some(true));

        let csv = ay_subsumption_throughput_csv_with_backend_buckets(
            Some(&ay_execution),
            None,
            false,
            &[],
            Some(&trust_cg_backend),
            &backend_buckets,
        );
        assert!(csv.contains(TRUST_CG_BACKEND_BUCKET_ROW_STATUS));
        assert!(csv.contains(TRUST_CG_BACKEND_MIXED_ROW_STATUS));
        assert!(csv.contains(",mixed_2_16,trust_cg_o2_vectorized,"));
        assert_eq!(csv.lines().count(), 321);
    }

    #[test]
    fn phase8_ay_subsumption_plan_only_counters_block_promotion() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let throughput = planned_ay_subsumption_throughput(&correctness);
        let counters = phase8_ay_subsumption_native_promotion_counters(
            &correctness,
            &throughput,
            phase8_test_scope(),
        );

        assert_eq!(counters.schema, PHASE8_NATIVE_PROMOTION_COUNTERS_SCHEMA);
        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.consumer.ay.result_parity.wrong_answer_count, 0);
        assert_eq!(
            counters.dispatch.fallback_count,
            throughput.row_accounting.pending_backend_rows
        );
        assert_eq!(counters.dispatch.useful_native_count, 0);
        let blockers = phase8_blocker_codes(&counters);
        assert!(blockers.contains("throughput_rows_pending"));
        assert!(blockers.contains("throughput_gate_not_evaluated"));
        assert!(blockers.contains("native_useful_application_missing"));
    }

    #[test]
    fn phase8_ay_subsumption_backend_slice_counters_do_not_authorize_product() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let backend_buckets = vec!["4".to_string()];
        let trust_cg_backend = fake_trust_cg_backend_execution_with_buckets(&["4"]);
        let correctness = ay_subsumption_correctness_with_full_backend_execution(
            &correctness,
            None,
            None,
            None,
            Some(&trust_cg_backend),
        );
        let throughput = planned_ay_subsumption_throughput_with_backend_buckets(
            &correctness,
            None,
            None,
            false,
            &[],
            Some(&trust_cg_backend),
            &backend_buckets,
        );

        assert_eq!(throughput.status, "partial_trust_cg_backend_rows");
        assert_eq!(throughput.row_accounting.measured_ay_reference_rows, 0);
        assert_eq!(throughput.row_accounting.measured_trust_cg_backend_rows, 8);
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| phase8_ay_product_backend_row(row))
                .count(),
            4
        );
        assert_eq!(
            throughput
                .rows
                .iter()
                .filter(|row| is_trust_cg_backend_throughput_status(row.status)
                    && !row.product_install_evidence
                    && row.promotion_disposition
                        == TRUST_CG_BACKEND_SCALAR_CONTROL_PROMOTION_DISPOSITION)
                .count(),
            4
        );

        let counters = phase8_ay_subsumption_native_promotion_counters(
            &correctness,
            &throughput,
            phase8_test_scope(),
        );

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.lifecycle.nominated_count, 4);
        assert_eq!(counters.dispatch.eligible_call_count, 4);
        assert_eq!(counters.lifecycle.canary_install_count, 0);
        assert_eq!(counters.invalidation_gate.fresh_install_count, 0);
        assert_eq!(counters.proof_gate.proof_verified_count, 0);
        assert_eq!(counters.dispatch.native_call_count, 0);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        assert_eq!(
            counters
                .consumer
                .ay
                .usefulness
                .native_useful_application_count,
            0
        );
        let blockers = phase8_blocker_codes(&counters);
        assert!(blockers.contains("ay_reference_rows_missing"));
        assert!(blockers.contains("throughput_summary_incomplete"));
        assert!(blockers.contains("throughput_gate_not_evaluated"));
    }

    #[test]
    fn phase8_ty_parent_loop_complete_evidence_allows_promotion() {
        let evidence = phase8_ty_mcl_evidence();
        let counters =
            phase8_ty_parent_loop_native_promotion_counters(&evidence, phase8_ty_test_scope());

        assert_eq!(counters.schema, PHASE8_NATIVE_PROMOTION_COUNTERS_SCHEMA);
        assert!(counters.promotion_verdict.can_promote_beyond_canary);
        assert!(counters.promotion_verdict.blockers.is_empty());
        assert_eq!(
            counters.counter_scope.family,
            PHASE8_TY_PARENT_LOOP_COUNTER_FAMILY
        );
        assert_eq!(counters.consumer.ty.spec_name, "MCLamportMutex");
        assert_eq!(counters.consumer.ty.parity.wrong_answer_count, 0);
        assert_eq!(
            counters
                .consumer
                .ty
                .native_path
                .native_dispatch_promoted_count,
            1
        );
        assert_eq!(counters.dispatch.useful_native_count, 32);
        assert_eq!(
            counters
                .consumer
                .ty
                .profile_reports
                .profile_generate
                .profile_sha256
                .as_deref(),
            Some("sha256:test-ty-profdata")
        );
        assert_eq!(
            counters.consumer.ty.profile_reports.profile_use.fresh,
            Some(true)
        );
        assert_eq!(counters.consumer.ty.execution_shape.fingerprint_count, 64);
        assert_eq!(
            counters.consumer.ty.execution_shape.flat_state_copy_bytes,
            8192
        );
        assert_eq!(counters.consumer.ty.execution_shape.fingerprint_bytes, 512);
        assert_eq!(counters.consumer.ty.execution_shape.helper_inline_count, 6);
        assert_eq!(
            counters
                .consumer
                .ty
                .execution_shape
                .alias_readonly_metadata_hit_count,
            4
        );
        assert_eq!(
            counters
                .consumer
                .ty
                .execution_shape
                .execution_shape_evidence_missing_count,
            0
        );
        assert_eq!(
            counters
                .consumer
                .ty
                .profile_reports
                .profile_use_report_missing_count,
            0
        );
        assert_eq!(counters.artifact_gate.replay_missing_count, 0);
        assert_eq!(counters.artifact_gate.telemetry_missing_count, 0);
        assert_eq!(counters.performance.cache_hit_count, 3);
    }

    #[test]
    fn phase8_ty_parent_loop_blocks_missing_profile_use_report() {
        let mut evidence = phase8_ty_mcl_evidence();
        evidence.profile_use_report = Phase8TyProfileUseReportBinding {
            report_identity: None,
            report_sha256: None,
            profile_sha256: None,
            profile_key_digest: None,
            fresh: None,
            freshness_reason: None,
            scheduled: None,
        };

        let counters =
            phase8_ty_parent_loop_native_promotion_counters(&evidence, phase8_ty_test_scope());

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        assert_eq!(counters.lifecycle.canary_install_count, 0);
        assert_eq!(counters.invalidation_gate.fresh_install_count, 0);
        assert_eq!(
            counters
                .consumer
                .ty
                .profile_reports
                .profile_use_report_missing_count,
            1
        );
        let blockers = phase8_ty_blocker_codes(&counters);
        assert!(blockers.contains("profile_use_report_missing"));
    }

    #[test]
    fn phase8_ty_parent_loop_blocks_stale_profile_use_report() {
        let mut evidence = phase8_ty_mcl_evidence();
        evidence.profile_use_report.fresh = Some(false);
        evidence.profile_use_report.freshness_reason = Some("profile-key-mismatch".to_string());

        let counters =
            phase8_ty_parent_loop_native_promotion_counters(&evidence, phase8_ty_test_scope());

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        assert_eq!(counters.lifecycle.canary_install_count, 0);
        assert_eq!(counters.invalidation_gate.stale_install_reject_count, 1);
        assert_eq!(counters.proof_gate.proof_stale_count, 1);
        assert_eq!(
            counters
                .consumer
                .ty
                .profile_reports
                .profile_use_report_stale_count,
            1
        );
        let blockers = phase8_ty_blocker_codes(&counters);
        assert!(blockers.contains("profile_use_report_stale"));
    }

    #[test]
    fn phase8_ty_parent_loop_blocks_profile_use_not_marked_fresh() {
        let mut evidence = phase8_ty_mcl_evidence();
        evidence.profile_use_report.fresh = None;

        let counters =
            phase8_ty_parent_loop_native_promotion_counters(&evidence, phase8_ty_test_scope());

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        assert_eq!(counters.lifecycle.canary_install_count, 0);
        assert_eq!(counters.invalidation_gate.stale_call_reject_count, 1);
        assert_eq!(
            counters
                .consumer
                .ty
                .profile_reports
                .profile_use_report_not_fresh_count,
            1
        );
        let blockers = phase8_ty_blocker_codes(&counters);
        assert!(blockers.contains("profile_use_report_not_marked_fresh"));
    }

    #[test]
    fn phase8_ty_parent_loop_blocks_profile_generate_use_binding_mismatch() {
        let mut evidence = phase8_ty_mcl_evidence();
        evidence.profile_use_report.profile_sha256 = Some("sha256:stale-profdata".to_string());
        evidence.profile_use_report.profile_key_digest = Some("stale-profile-key".to_string());

        let counters =
            phase8_ty_parent_loop_native_promotion_counters(&evidence, phase8_ty_test_scope());

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        assert_eq!(counters.lifecycle.canary_install_count, 0);
        assert_eq!(counters.invalidation_gate.generation_mismatch_count, 2);
        assert_eq!(
            counters
                .consumer
                .ty
                .profile_reports
                .profile_report_binding_mismatch_count,
            2
        );
        let blockers = phase8_ty_blocker_codes(&counters);
        assert!(blockers.contains("profile_report_binding_mismatch"));
    }

    #[test]
    fn phase8_ty_parent_loop_blocks_missing_downstream_native_path_and_artifacts() {
        let mut evidence = phase8_ty_mcl_evidence();
        evidence.downstream_cli_passed = None;
        evidence.strict_selftest_completed = false;
        evidence.native_fused_path_active = false;
        evidence.compiled_bfs_level_loop_fused = false;
        evidence.native_dispatch_promoted = false;
        evidence.actual_action_count = None;
        evidence.actual_state_len = None;
        evidence.replay_artifact_count = 0;
        evidence.telemetry_artifact_count = 0;
        evidence.useful_native_call_count = 0;

        let counters =
            phase8_ty_parent_loop_native_promotion_counters(&evidence, phase8_ty_test_scope());

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        assert_eq!(counters.artifact_gate.replay_missing_count, 1);
        assert_eq!(counters.artifact_gate.telemetry_missing_count, 1);
        assert_eq!(counters.proof_gate.proof_unknown_count, 1);
        let blockers = phase8_ty_blocker_codes(&counters);
        assert!(blockers.contains("downstream_cli_verdict_missing"));
        assert!(blockers.contains("ty_shape_evidence_missing"));
        assert!(blockers.contains("ty_native_path_missing"));
        assert!(blockers.contains("replay_artifact_missing"));
        assert!(blockers.contains("telemetry_artifact_missing"));
        assert!(blockers.contains("native_useful_application_missing"));
    }

    #[test]
    fn phase8_ty_parent_loop_blocks_semantic_mismatch_and_crash() {
        let mut evidence = phase8_ty_mcl_evidence();
        evidence.actual_action_count = Some(26);
        evidence.shadow_mismatch_count = 2;
        evidence.crash_count = 1;
        evidence.crash_packet_count = 1;
        evidence.non_promoting = true;

        let counters =
            phase8_ty_parent_loop_native_promotion_counters(&evidence, phase8_ty_test_scope());

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.consumer.ty.parity.action_count_mismatch_count, 1);
        assert_eq!(counters.consumer.ty.parity.wrong_answer_count, 3);
        assert_eq!(counters.consumer.ty.artifacts.crash_packet_count, 1);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        let blockers = phase8_ty_blocker_codes(&counters);
        assert!(blockers.contains("ty_semantic_mismatch"));
        assert!(blockers.contains("native_runtime_failure"));
        assert!(blockers.contains("ty_non_promoting_artifact"));
    }

    #[test]
    fn phase8_ty_parent_loop_blocks_missing_execution_shape_evidence() {
        let mut evidence = phase8_ty_mcl_evidence();
        evidence.flat_state_copy_bytes = 0;
        evidence.fingerprint_count = 0;
        evidence.fingerprint_bytes = 0;
        evidence.helper_inline_count = 0;
        evidence.alias_readonly_metadata_hit_count = 0;

        let counters =
            phase8_ty_parent_loop_native_promotion_counters(&evidence, phase8_ty_test_scope());

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        assert_eq!(
            counters
                .consumer
                .ty
                .execution_shape
                .execution_shape_evidence_missing_count,
            5
        );
        assert_eq!(counters.artifact_gate.layout_mismatch_count, 5);
        assert_eq!(counters.proof_gate.proof_missing_count, 5);
        let blockers = phase8_ty_blocker_codes(&counters);
        assert!(blockers.contains("ty_execution_shape_evidence_missing"));
    }

    #[test]
    fn phase8_ty_parent_loop_blocks_missing_manifest_layout_proof_target_scope() {
        let evidence = phase8_ty_mcl_evidence();
        let mut scope = phase8_ty_test_scope();
        scope.manifest_sha256 = None;
        scope.layout_checksum.clear();
        scope.proof_policy_sha256.clear();
        scope.target_features_sha256.clear();

        let counters = phase8_ty_parent_loop_native_promotion_counters(&evidence, scope);

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.artifact_gate.manifest_missing_count, 1);
        assert_eq!(counters.artifact_gate.layout_mismatch_count, 1);
        assert_eq!(counters.proof_gate.proof_missing_count, 1);
        assert_eq!(counters.artifact_gate.target_mismatch_count, 1);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        let blockers = phase8_ty_blocker_codes(&counters);
        assert!(blockers.contains("manifest_hash_missing"));
        assert!(blockers.contains("layout_evidence_missing"));
        assert!(blockers.contains("proof_policy_missing"));
        assert!(blockers.contains("target_evidence_missing"));
    }

    #[test]
    fn phase8_ty_parent_loop_blocks_fallback_even_with_useful_native_calls() {
        let mut evidence = phase8_ty_mcl_evidence();
        evidence.fallback_count = 1;

        let counters =
            phase8_ty_parent_loop_native_promotion_counters(&evidence, phase8_ty_test_scope());

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.dispatch.fallback_count, 1);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        let blockers = phase8_ty_blocker_codes(&counters);
        assert!(blockers.contains("fallback_observed"));
    }

    #[test]
    fn phase8_ay_packet_missing_required_artifacts_fail_closed() {
        let temp_dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(temp_dir.path().join("gate-results.json"), "{}\n")
            .expect("write present artifact");

        let blockers = phase8_ay_promotion_packet_missing_artifact_blockers(
            temp_dir.path(),
            &["gate-results.json", "artifact.manifest.sha256"],
        );

        assert_eq!(blockers.len(), 1);
        assert_eq!(blockers[0].code, "required_packet_artifact_missing");
        assert!(blockers[0].message.contains("artifact.manifest.sha256"));
    }

    #[test]
    fn phase8_ay_subsumption_complete_backend_gate_allows_promotion() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let ay_numeric_buckets = ay_numeric_length_buckets(&correctness.workload.length_buckets);
        let ay_bucket_refs = ay_numeric_buckets
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let ay_execution = fake_ay_reference_execution_with_buckets(&ay_bucket_refs);
        let backend_bucket_labels = [
            "2",
            "3",
            "4",
            "5",
            "6",
            "7",
            "8",
            "9",
            "10",
            "11",
            "12",
            "13",
            "14",
            "15",
            "16",
            "mixed_2_16",
        ];
        let trust_cg_backend = fake_trust_cg_backend_execution_with_buckets(&backend_bucket_labels);
        let correctness = ay_subsumption_correctness_with_full_backend_execution(
            &correctness,
            None,
            None,
            Some(&ay_execution),
            Some(&trust_cg_backend),
        );
        let throughput = planned_ay_subsumption_throughput_with_backend_buckets(
            &correctness,
            Some(&ay_execution),
            None,
            false,
            &[],
            Some(&trust_cg_backend),
            &ay_numeric_buckets,
        );
        let counters = phase8_ay_subsumption_native_promotion_counters(
            &correctness,
            &throughput,
            phase8_test_scope(),
        );

        assert!(counters.promotion_verdict.can_promote_beyond_canary);
        assert!(counters.promotion_verdict.blockers.is_empty());
        assert_eq!(counters.lifecycle.profile_only_compiled_count, 0);
        assert_eq!(counters.lifecycle.nominated_count, 64);
        assert_eq!(counters.lifecycle.canary_install_count, 64);
        assert_eq!(counters.invalidation_gate.fresh_install_count, 64);
        assert_eq!(counters.proof_gate.proof_verified_count, 64);
        assert_eq!(counters.dispatch.eligible_call_count, 64);
        assert_eq!(counters.dispatch.native_call_count, 64);
        assert_eq!(counters.consumer.ay.result_parity.wrong_answer_count, 0);
        assert_eq!(counters.dispatch.useful_native_count, 64);
        assert_eq!(
            counters
                .consumer
                .ay
                .usefulness
                .native_useful_application_count,
            counters.dispatch.useful_native_count
        );
        assert_eq!(
            counters
                .consumer
                .ay
                .usefulness
                .profile_only_application_count,
            0
        );
        assert!(counters.performance.baseline_p50_us > counters.performance.native_p50_us);
    }

    #[test]
    fn phase8_ay_subsumption_complete_backend_gate_blocks_missing_manifest() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let ay_numeric_buckets = ay_numeric_length_buckets(&correctness.workload.length_buckets);
        let ay_bucket_refs = ay_numeric_buckets
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let ay_execution = fake_ay_reference_execution_with_buckets(&ay_bucket_refs);
        let backend_bucket_labels = [
            "2",
            "3",
            "4",
            "5",
            "6",
            "7",
            "8",
            "9",
            "10",
            "11",
            "12",
            "13",
            "14",
            "15",
            "16",
            "mixed_2_16",
        ];
        let trust_cg_backend = fake_trust_cg_backend_execution_with_buckets(&backend_bucket_labels);
        let correctness = ay_subsumption_correctness_with_full_backend_execution(
            &correctness,
            None,
            None,
            Some(&ay_execution),
            Some(&trust_cg_backend),
        );
        let throughput = planned_ay_subsumption_throughput_with_backend_buckets(
            &correctness,
            Some(&ay_execution),
            None,
            false,
            &[],
            Some(&trust_cg_backend),
            &ay_numeric_buckets,
        );
        assert_eq!(
            throughput.status,
            "complete_ay_reference_and_trust_cg_backend_rows"
        );
        assert_eq!(throughput.gate.passed, Some(true));

        let mut scope = phase8_test_scope();
        scope.manifest_sha256 = None;
        let counters =
            phase8_ay_subsumption_native_promotion_counters(&correctness, &throughput, scope);

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.artifact_gate.manifest_missing_count, 1);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        let blockers = phase8_blocker_codes(&counters);
        assert!(blockers.contains("manifest_hash_missing"));
    }

    #[test]
    fn phase8_ay_subsumption_complete_backend_gate_blocks_missing_layout_proof_target_scope() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let ay_numeric_buckets = ay_numeric_length_buckets(&correctness.workload.length_buckets);
        let ay_bucket_refs = ay_numeric_buckets
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let ay_execution = fake_ay_reference_execution_with_buckets(&ay_bucket_refs);
        let backend_bucket_labels = [
            "2",
            "3",
            "4",
            "5",
            "6",
            "7",
            "8",
            "9",
            "10",
            "11",
            "12",
            "13",
            "14",
            "15",
            "16",
            "mixed_2_16",
        ];
        let trust_cg_backend = fake_trust_cg_backend_execution_with_buckets(&backend_bucket_labels);
        let correctness = ay_subsumption_correctness_with_full_backend_execution(
            &correctness,
            None,
            None,
            Some(&ay_execution),
            Some(&trust_cg_backend),
        );
        let throughput = planned_ay_subsumption_throughput_with_backend_buckets(
            &correctness,
            Some(&ay_execution),
            None,
            false,
            &[],
            Some(&trust_cg_backend),
            &ay_numeric_buckets,
        );
        assert_eq!(throughput.gate.passed, Some(true));

        let mut scope = phase8_test_scope();
        scope.layout_checksum.clear();
        scope.proof_policy_sha256.clear();
        scope.target_features_sha256.clear();
        let counters =
            phase8_ay_subsumption_native_promotion_counters(&correctness, &throughput, scope);

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.artifact_gate.layout_mismatch_count, 1);
        assert_eq!(counters.proof_gate.proof_missing_count, 1);
        assert_eq!(counters.artifact_gate.target_mismatch_count, 1);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        let blockers = phase8_blocker_codes(&counters);
        assert!(blockers.contains("layout_evidence_missing"));
        assert!(blockers.contains("proof_policy_missing"));
        assert!(blockers.contains("target_evidence_missing"));
    }

    #[test]
    fn phase8_ay_subsumption_complete_backend_gate_blocks_mismatched_manifest() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let ay_numeric_buckets = ay_numeric_length_buckets(&correctness.workload.length_buckets);
        let ay_bucket_refs = ay_numeric_buckets
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let ay_execution = fake_ay_reference_execution_with_buckets(&ay_bucket_refs);
        let backend_bucket_labels = [
            "2",
            "3",
            "4",
            "5",
            "6",
            "7",
            "8",
            "9",
            "10",
            "11",
            "12",
            "13",
            "14",
            "15",
            "16",
            "mixed_2_16",
        ];
        let trust_cg_backend = fake_trust_cg_backend_execution_with_buckets(&backend_bucket_labels);
        let correctness = ay_subsumption_correctness_with_full_backend_execution(
            &correctness,
            None,
            None,
            Some(&ay_execution),
            Some(&trust_cg_backend),
        );
        let throughput = planned_ay_subsumption_throughput_with_backend_buckets(
            &correctness,
            Some(&ay_execution),
            None,
            false,
            &[],
            Some(&trust_cg_backend),
            &ay_numeric_buckets,
        );
        assert_eq!(
            throughput.status,
            "complete_ay_reference_and_trust_cg_backend_rows"
        );
        assert_eq!(throughput.gate.passed, Some(true));

        let mut scope = phase8_test_scope();
        scope.expected_manifest_sha256 =
            Some("fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210".to_string());
        let counters =
            phase8_ay_subsumption_native_promotion_counters(&correctness, &throughput, scope);

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.artifact_gate.manifest_missing_count, 0);
        assert_eq!(counters.artifact_gate.manifest_hash_mismatch_count, 1);
        assert_eq!(counters.dispatch.useful_native_count, 0);
        let blockers = phase8_blocker_codes(&counters);
        assert!(blockers.contains("manifest_hash_mismatch"));
    }

    #[test]
    fn phase8_ay_subsumption_correctness_mismatch_blocks_promotion() {
        let mut cases = ay_subsumption_cases_fixture();
        cases.subsumption_pairs[0].expected = !cases.subsumption_pairs[0].expected;
        let correctness =
            validate_ay_subsumption_cases(&cases).expect("fixture should still validate");
        assert_eq!(correctness.mismatch_count, 1);

        let ay_numeric_buckets = ay_numeric_length_buckets(&correctness.workload.length_buckets);
        let ay_bucket_refs = ay_numeric_buckets
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let ay_execution = fake_ay_reference_execution_with_buckets(&ay_bucket_refs);
        let backend_bucket_labels = [
            "2",
            "3",
            "4",
            "5",
            "6",
            "7",
            "8",
            "9",
            "10",
            "11",
            "12",
            "13",
            "14",
            "15",
            "16",
            "mixed_2_16",
        ];
        let trust_cg_backend = fake_trust_cg_backend_execution_with_buckets(&backend_bucket_labels);
        let correctness = ay_subsumption_correctness_with_full_backend_execution(
            &correctness,
            None,
            None,
            Some(&ay_execution),
            Some(&trust_cg_backend),
        );
        let throughput = planned_ay_subsumption_throughput_with_backend_buckets(
            &correctness,
            Some(&ay_execution),
            None,
            false,
            &[],
            Some(&trust_cg_backend),
            &ay_numeric_buckets,
        );
        assert_eq!(throughput.gate.passed, Some(true));

        let counters = phase8_ay_subsumption_native_promotion_counters(
            &correctness,
            &throughput,
            phase8_test_scope(),
        );

        assert!(!counters.promotion_verdict.can_promote_beyond_canary);
        assert_eq!(counters.consumer.ay.result_parity.wrong_answer_count, 1);
        assert_eq!(
            counters
                .consumer
                .ay
                .result_parity
                .solver_result_mismatch_count,
            1
        );
        assert_eq!(counters.dispatch.useful_native_count, 0);
        let blockers = phase8_blocker_codes(&counters);
        assert!(blockers.contains("ay_correctness_mismatch"));
        assert!(blockers.contains("native_useful_application_missing"));
    }

    #[test]
    fn ay_subsumption_backend_readiness_reports_deterministic_stubs() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let readiness = planned_ay_subsumption_backend_readiness(&correctness, None);

        assert_eq!(
            readiness.schema,
            "trust-cg.ay_subsumption.backend_readiness.v1"
        );
        assert_eq!(readiness.rows.len(), correctness.workload.variants.len());
        assert_eq!(readiness.rows[0].variant, "ay_neon_reference");
        assert_eq!(readiness.rows[0].status, "unavailable");
        assert_eq!(readiness.rows[0].error_code, Some("ay_repo_not_provided"));
        assert!(
            readiness.rows[1..]
                .iter()
                .all(|row| row.status == "execution_unsupported"
                    && row.error_code == Some("trust_cg_backend_not_wired"))
        );
    }

    #[test]
    fn ay_reference_adapter_marks_correctness_and_readiness_ready() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let source = "SimdClauseScanner find_clauses_containing batch_subsumption_check \
            subsumes_neon vld1q_s32 vceqq_s32 vmaxvq_u32";
        let state = AYReferenceBackendState {
            repo: "/tmp/ay".to_string(),
            requested_rev: "origin/main".to_string(),
            resolved_rev: Some("abc123".to_string()),
            dirty: Some(false),
            source_path: "/tmp/ay/crates/ay-jit/src/simd_inprocess.rs".to_string(),
            source_exists: true,
            revision_source_path: "crates/ay-jit/src/simd_inprocess.rs".to_string(),
            revision_source_exists: true,
            revision_source_sha256: Some("feedface".to_string()),
            revision_source_size_bytes: Some(source.len() as u64),
            source_checks: ay_reference_source_checks(source),
            adapter_ready: true,
        };

        let with_rows = ay_subsumption_correctness_with_backend_rows(&correctness, Some(&state));
        assert_eq!(
            with_rows.backend_rows.len(),
            correctness.workload.variants.len()
        );
        assert_eq!(with_rows.backend_rows[0].variant, "ay_neon_reference");
        assert_eq!(with_rows.backend_rows[0].status, "reference_adapter_ready");
        assert_eq!(with_rows.backend_rows[0].error_code, None);
        assert_eq!(with_rows.backend_rows[0].contains_mismatch_count, 0);
        assert_eq!(with_rows.backend_rows[0].subsumption_mismatch_count, 0);

        let readiness = planned_ay_subsumption_backend_readiness(&correctness, Some(state));
        assert_eq!(readiness.rows[0].status, "reference_adapter_ready");
        assert_eq!(readiness.rows[0].error_code, None);
        assert!(
            readiness.rows[0]
                .ay_reference
                .as_ref()
                .expect("ay state")
                .source_checks
                .iter()
                .all(|check| check.present)
        );
    }

    #[test]
    fn trust_cg_backend_probe_cases_cover_padded_chunks_and_sentinel_masking() {
        let cases = ay_subsumption_cases_fixture();
        let probe_cases = trust_cg_contains4_probe_cases(&cases);
        let chunk_count = cases
            .clauses
            .iter()
            .map(|clause| clause.padded_length / 4)
            .sum::<usize>();

        assert_eq!(
            probe_cases.len(),
            chunk_count * cases.contains_queries.len()
        );
        assert!(probe_cases.iter().any(|case| {
            case.literal == cases.sentinel
                && case.chunk.valid_mask != 0b1111
                && case.expected_mask == 0
        }));
    }

    #[test]
    fn trust_cg_padded_chunk_arena_preserves_fixture_oracles() {
        let cases = ay_subsumption_cases_fixture();
        validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let arena = TrustCgPaddedChunkArena::new(&cases);
        let chunk_count = cases
            .clauses
            .iter()
            .map(|clause| clause.padded_length / 4)
            .sum::<usize>();

        assert_eq!(arena.chunks.len(), chunk_count);
        assert_eq!(arena.sentinel, cases.sentinel);
        assert_eq!(arena.flat_lanes.len(), chunk_count * 4);
        assert_eq!(arena.chunk_valid_masks.len(), chunk_count);
        assert_eq!(arena.start_chunks.len(), cases.clauses.len());
        assert_eq!(arena.end_chunks.len(), cases.clauses.len());
        assert_eq!(arena.clause_ids.len(), cases.clauses.len());
        for clause in &cases.clauses {
            let chunks = arena.chunks_for_clause(clause.id);
            assert_eq!(chunks.len(), clause.padded_length / 4);
            for chunk in chunks {
                assert_eq!(chunk.clause_id, clause.id);
                for lane_offset in 0..4 {
                    let lane_index = chunk.chunk_start_lane + lane_offset;
                    let lane_bit = 1u8 << lane_offset;
                    if lane_index < clause.length {
                        assert_eq!(chunk.lanes[lane_offset], clause.lits[lane_index]);
                        assert_ne!(chunk.lanes[lane_offset], cases.sentinel);
                        assert_ne!(chunk.valid_mask & lane_bit, 0);
                    } else {
                        assert_eq!(chunk.lanes[lane_offset], cases.sentinel);
                        assert_eq!(chunk.valid_mask & lane_bit, 0);
                    }
                }
            }
        }

        for query in &cases.contains_queries {
            let actual_clause_ids = cases
                .clauses
                .iter()
                .filter(|clause| arena.clause_contains_scalar(clause.id, query.literal))
                .map(|clause| clause.id)
                .collect::<Vec<_>>();
            assert_eq!(actual_clause_ids, query.expected_clause_ids);
        }

        for pair in &cases.subsumption_pairs {
            let a = clause_by_id(&cases, pair.a).expect("fixture should contain A clause");
            let actual = a
                .lits
                .iter()
                .all(|literal| arena.clause_contains_scalar(pair.b, *literal));
            assert_eq!(actual, pair.expected);
        }
    }

    #[test]
    fn trust_cg_padded_chunk_arena_flat_scanner_view_preserves_contains_queries() {
        let cases = ay_subsumption_cases_fixture();
        validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let arena = TrustCgPaddedChunkArena::new(&cases);
        let all_view = arena.scanner_view();
        let mut scratch = vec![0u32; all_view.len()];

        for query in &cases.contains_queries {
            let match_count =
                arena.scanner_contains_literal_scalar(&all_view, query.literal, &mut scratch);
            let actual_clause_ids = scratch[..match_count]
                .iter()
                .map(|clause_id| usize::try_from(*clause_id).expect("clause id fits usize"))
                .collect::<Vec<_>>();
            assert_eq!(actual_clause_ids, query.expected_clause_ids);
        }

        for bucket in ay_numeric_length_buckets(&cases.benchmark_matrix.length_buckets) {
            let bucket_clauses = cases
                .clauses
                .iter()
                .filter(|clause| clause.length.to_string() == bucket)
                .collect::<Vec<_>>();
            let bucket_view = arena.scanner_view_for_clauses(&bucket_clauses);
            let expected_ids = bucket_clauses
                .iter()
                .map(|clause| u32::try_from(clause.id).expect("clause id fits u32"))
                .collect::<Vec<_>>();
            assert_eq!(bucket_view.clause_ids, expected_ids);
            assert_eq!(bucket_view.start_chunks.len(), bucket_clauses.len());
            assert_eq!(bucket_view.end_chunks.len(), bucket_clauses.len());
        }
    }

    #[test]
    fn trust_cg_padded_chunk_arena_subsumption_scanner_batch_preserves_fixture_oracles() {
        let cases = ay_subsumption_cases_fixture();
        validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let arena = TrustCgPaddedChunkArena::new(&cases);
        let pairs = cases
            .subsumption_pairs
            .iter()
            .map(|pair| (pair.a, pair.b))
            .collect::<Vec<_>>();
        let batch = arena.subsumption_scanner_batch_for_pairs(&pairs);
        let mut out_results = vec![0xaa; batch.len()];

        assert_eq!(batch.a_start_chunks.len(), cases.subsumption_pairs.len());
        assert_eq!(batch.a_end_chunks.len(), cases.subsumption_pairs.len());
        assert_eq!(batch.b_start_chunks.len(), cases.subsumption_pairs.len());
        assert_eq!(batch.b_end_chunks.len(), cases.subsumption_pairs.len());
        assert_eq!(batch.records.len(), cases.subsumption_pairs.len() * 6);
        for (record, pair) in batch.records.chunks_exact(6).zip(&cases.subsumption_pairs) {
            let a_range = arena
                .ranges_by_clause_id
                .get(&pair.a)
                .expect("fixture should contain A clause chunks");
            let b_range = arena
                .ranges_by_clause_id
                .get(&pair.b)
                .expect("fixture should contain B clause chunks");
            assert_eq!(
                record,
                &[
                    u32::try_from(a_range.start).expect("chunk arena start fits u32"),
                    u32::try_from(a_range.end).expect("chunk arena end fits u32"),
                    u32::try_from(b_range.start).expect("chunk arena start fits u32"),
                    u32::try_from(b_range.end).expect("chunk arena end fits u32"),
                    u32::try_from(pair.a).expect("clause id fits u32"),
                    u32::try_from(pair.b).expect("clause id fits u32"),
                ]
            );
        }

        let true_count = arena.scanner_batch_subsumption_scalar(&batch, &mut out_results);
        let expected_true_count = cases
            .subsumption_pairs
            .iter()
            .filter(|pair| pair.expected)
            .count();
        assert_eq!(true_count, expected_true_count);

        for (pair, actual) in cases.subsumption_pairs.iter().zip(out_results) {
            assert_eq!(actual != 0, pair.expected, "pair {} -> {}", pair.a, pair.b);
        }
    }

    #[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
    #[test]
    fn trust_cg_contains_literal_scanner_backend_matches_fixture_oracles() {
        use std::collections::HashMap;

        let cases = ay_subsumption_cases_fixture();
        validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let arena = TrustCgPaddedChunkArena::new(&cases);
        let view = arena.scanner_view();
        let mut scratch = vec![0u32; view.len()];

        let jit = trust_cg_codegen::JitCompiler::new(trust_cg_codegen::JitConfig {
            opt_level: trust_cg_codegen::pipeline::OptLevel::O2,
            verify: false,
            verify_dispatch: trust_cg_codegen::DispatchVerifyMode::Off,
            ..trust_cg_codegen::JitConfig::default()
        });
        let buffer = jit
            .compile_raw(
                &[build_trust_cg_contains_literal_scanner_backend_function()],
                &HashMap::new(),
            )
            .expect("scanner backend should compile");
        let scanner_guard = unsafe {
            buffer
                .get_fn_bound::<ContainsLiteralScannerBackend>(
                    TRUST_CG_CONTAINS_LITERAL_SCANNER_BACKEND_FN,
                )
                .expect("scanner symbol should exist")
        };
        let scanner = scanner_guard.as_ref();
        trust_cg_codegen::ensure_jit_execute_mode();

        for query in &cases.contains_queries {
            let match_count =
                call_contains_literal_scanner(scanner, &arena, &view, query.literal, &mut scratch);
            let actual_clause_ids = scratch[..match_count]
                .iter()
                .map(|clause_id| usize::try_from(*clause_id).expect("clause id fits usize"))
                .collect::<Vec<_>>();
            assert_eq!(actual_clause_ids, query.expected_clause_ids);
        }
    }

    #[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
    #[test]
    fn trust_cg_contains_literal_query_batch_backend_matches_fixture_oracles() {
        use std::collections::HashMap;

        fn expected_checksum(
            arena: &TrustCgPaddedChunkArena,
            view: &TrustCgPaddedChunkScannerView,
            query_literals: &[i32],
        ) -> u64 {
            let mut scratch = vec![0u32; view.len()];
            let mut checksum = 0u64;
            for literal in query_literals {
                let match_count =
                    arena.scanner_contains_literal_scalar(view, *literal, &mut scratch);
                let id_checksum = scratch[..match_count]
                    .iter()
                    .fold(0u64, |acc, clause_id| acc ^ u64::from(*clause_id));
                checksum = checksum
                    .wrapping_mul(131)
                    .wrapping_add(*literal as u32 as u64)
                    .wrapping_add(match_count as u64)
                    .wrapping_add(id_checksum);
            }
            checksum
        }

        let cases = ay_subsumption_cases_fixture();
        validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let arena = TrustCgPaddedChunkArena::new(&cases);
        let query_literals = cases
            .contains_queries
            .iter()
            .map(|query| query.literal)
            .collect::<Vec<_>>();
        let full_view = arena.scanner_view();
        let bucket_clauses = cases
            .clauses
            .iter()
            .filter(|clause| clause.length == 4)
            .collect::<Vec<_>>();
        let bucket_view = arena.scanner_view_for_clauses(&bucket_clauses);

        let jit = trust_cg_codegen::JitCompiler::new(trust_cg_codegen::JitConfig {
            opt_level: trust_cg_codegen::pipeline::OptLevel::O2,
            verify: false,
            verify_dispatch: trust_cg_codegen::DispatchVerifyMode::Off,
            ..trust_cg_codegen::JitConfig::default()
        });
        let buffer = jit
            .compile_raw(
                &[build_trust_cg_contains_literal_query_batch_backend_function()],
                &HashMap::new(),
            )
            .expect("query batch scanner backend should compile");
        let scanner_guard = unsafe {
            buffer
                .get_fn_bound::<ContainsLiteralQueryBatchBackend>(
                    TRUST_CG_CONTAINS_LITERAL_QUERY_BATCH_BACKEND_FN,
                )
                .expect("query batch scanner symbol should exist")
        };
        let scanner = scanner_guard.as_ref();
        trust_cg_codegen::ensure_jit_execute_mode();

        for view in [&full_view, &bucket_view] {
            let actual =
                call_contains_literal_query_batch_scanner(scanner, &arena, view, &query_literals);
            let expected = expected_checksum(&arena, view, &query_literals);
            assert_eq!(actual, expected);
        }
    }

    #[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
    #[test]
    fn trust_cg_batch_subsumption_scanner_backend_matches_fixture_oracles() {
        use std::collections::HashMap;

        let cases = ay_subsumption_cases_fixture();
        validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let arena = TrustCgPaddedChunkArena::new(&cases);
        let pairs = cases
            .subsumption_pairs
            .iter()
            .map(|pair| (pair.a, pair.b))
            .collect::<Vec<_>>();
        let batch = arena.subsumption_scanner_batch_for_pairs(&pairs);
        let mut out_results = vec![0xaa; batch.len()];

        let jit = trust_cg_codegen::JitCompiler::new(trust_cg_codegen::JitConfig {
            opt_level: trust_cg_codegen::pipeline::OptLevel::O2,
            verify: false,
            verify_dispatch: trust_cg_codegen::DispatchVerifyMode::Off,
            ..trust_cg_codegen::JitConfig::default()
        });
        let buffer = jit
            .compile_raw(
                &[build_trust_cg_batch_subsumption_scanner_backend_function()],
                &HashMap::new(),
            )
            .expect("batch subsumption scanner backend should compile");
        let scanner_guard = unsafe {
            buffer
                .get_fn_bound::<BatchSubsumptionScannerBackend>(
                    TRUST_CG_BATCH_SUBSUMPTION_SCANNER_BACKEND_FN,
                )
                .expect("batch subsumption scanner symbol should exist")
        };
        let scanner = scanner_guard.as_ref();
        trust_cg_codegen::ensure_jit_execute_mode();

        let true_count = call_batch_subsumption_scanner(scanner, &arena, &batch, &mut out_results);
        let expected_true_count = cases
            .subsumption_pairs
            .iter()
            .filter(|pair| pair.expected)
            .count();
        assert_eq!(true_count, expected_true_count);

        for (pair, actual) in cases.subsumption_pairs.iter().zip(out_results) {
            assert_eq!(actual != 0, pair.expected, "pair {} -> {}", pair.a, pair.b);
        }
    }

    #[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
    #[test]
    fn trust_cg_batch_subsumption_repeated_checksum_backend_matches_fixture_oracles() {
        use std::collections::HashMap;

        let cases = ay_subsumption_cases_fixture();
        validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let arena = TrustCgPaddedChunkArena::new(&cases);
        let pairs = cases
            .subsumption_pairs
            .iter()
            .map(|pair| (pair.a, pair.b))
            .collect::<Vec<_>>();
        let batch = arena.subsumption_scanner_batch_for_pairs(&pairs);
        let mut out_results = vec![0xaa; batch.len()];

        let jit = trust_cg_codegen::JitCompiler::new(trust_cg_codegen::JitConfig {
            opt_level: trust_cg_codegen::pipeline::OptLevel::O2,
            verify: false,
            verify_dispatch: trust_cg_codegen::DispatchVerifyMode::Off,
            ..trust_cg_codegen::JitConfig::default()
        });
        let buffer = jit
            .compile_raw(
                &[build_trust_cg_batch_subsumption_repeated_checksum_backend_function()],
                &HashMap::new(),
            )
            .expect("repeated batch subsumption checksum backend should compile");
        let scanner_guard = unsafe {
            buffer
                .get_fn_bound::<BatchSubsumptionRepeatedChecksumBackend>(
                    TRUST_CG_BATCH_SUBSUMPTION_REPEATED_CHECKSUM_BACKEND_FN,
                )
                .expect("repeated batch subsumption checksum symbol should exist")
        };
        let scanner = scanner_guard.as_ref();
        trust_cg_codegen::ensure_jit_execute_mode();

        let repetitions = 7usize;
        let actual_checksum = call_batch_subsumption_repeated_checksum_scanner(
            scanner,
            &arena,
            &batch,
            repetitions,
            &mut out_results,
        );
        let expected_one = cases.subsumption_pairs.iter().fold(
            cases
                .subsumption_pairs
                .iter()
                .filter(|pair| pair.expected)
                .count() as u64,
            |checksum, pair| {
                checksum
                    .wrapping_mul(131)
                    .wrapping_add(pair.a as u64)
                    .wrapping_add((pair.b as u64) << 8)
                    .wrapping_add(u64::from(pair.expected))
            },
        );
        let expected_checksum =
            (0..repetitions).fold(0u64, |checksum, _| checksum.wrapping_add(expected_one));
        assert_eq!(actual_checksum, expected_checksum);

        for (pair, actual) in cases.subsumption_pairs.iter().zip(out_results) {
            assert_eq!(actual != 0, pair.expected, "pair {} -> {}", pair.a, pair.b);
        }
    }

    #[test]
    fn trust_cg_contains4_scalar_control_cases_cover_all_valid_masks_and_match_masks() {
        let cases = ay_subsumption_cases_fixture();
        let comparison_cases = trust_cg_contains4_scalar_control_cases(&cases);
        let fixture_case_count = trust_cg_contains4_probe_cases(&cases).len();

        assert_eq!(comparison_cases.len(), 16 * 16 + 16 + fixture_case_count);
        let encoded_match_cases = comparison_cases[..16 * 16]
            .iter()
            .map(|case| case.chunk.chunk_start_lane)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            encoded_match_cases,
            (0usize..16 * 16).collect::<BTreeSet<_>>()
        );
        for case in &comparison_cases[..16 * 16] {
            let valid_mask = case.chunk.valid_mask;
            let match_mask = (case.chunk.chunk_start_lane % 16) as u8;
            assert_eq!(case.expected_mask, i32::from(valid_mask & match_mask));
            for lane_offset in 0..4 {
                let lane_bit = 1u8 << lane_offset;
                if valid_mask & lane_bit == 0 {
                    assert_eq!(case.chunk.lanes[lane_offset], cases.sentinel);
                }
            }
        }

        for case in &comparison_cases[16 * 16..16 * 16 + 16] {
            assert_eq!(case.literal, cases.sentinel);
            assert_eq!(case.expected_mask, 0);
            for lane_offset in 0..4 {
                let lane_bit = 1u8 << lane_offset;
                if case.chunk.valid_mask & lane_bit != 0 {
                    assert_ne!(case.chunk.lanes[lane_offset], cases.sentinel);
                }
            }
        }
    }

    #[test]
    fn trust_cg_backend_probe_reports_variant_rows() {
        let cases = ay_subsumption_cases_fixture();
        let correctness = validate_ay_subsumption_cases(&cases).expect("fixture should validate");
        let probe = run_trust_cg_backend_probe(&cases);

        assert_eq!(
            probe.schema,
            "trust-cg.ay_subsumption.trust_cg_backend_probe.v1"
        );
        assert_eq!(
            probe.promotion_disposition,
            TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION
        );
        assert!(!probe.product_install_evidence);
        assert_eq!(probe.rows.len(), 4);
        assert!(
            probe
                .rows
                .iter()
                .all(|row| row.variant.starts_with("trust_cg_")
                    && row.promotion_disposition == TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION
                    && !row.product_install_evidence)
        );

        if cfg!(all(
            target_arch = "aarch64",
            any(target_os = "macos", target_os = "linux")
        )) {
            assert_eq!(probe.status, "padded_scanner_probe_pass");
            assert!(probe.rows.iter().all(|row| {
                row.status == "padded_scanner_probe_executed"
                    && row.checked_cases > 0
                    && row.chunk_mismatch_count == 0
                    && row.contains_query_count == cases.contains_queries.len()
                    && row.contains_mismatch_count == 0
                    && row.subsumption_pair_count == cases.subsumption_pairs.len()
                    && row.subsumption_mismatch_count == 0
                    && row.mismatches.is_empty()
                    && row.operation_measurements.len() == 2
                    && row.operation_measurements.iter().all(|measurement| {
                        measurement.status == "probe_measured"
                            && measurement.promotion_disposition
                                == TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION
                            && measurement.raw_elapsed_ns.len()
                                == measurement.measurement_repetitions
                            && measurement.mean_throughput_per_us.is_some()
                            && measurement.coefficient_of_variation.is_some()
                    })
                    && row.timed_calls >= row.checked_cases
            }));

            let readiness = planned_ay_subsumption_backend_readiness_with_trust_cg_probe(
                &correctness,
                None,
                Some(&probe),
            );
            assert!(
                readiness.rows[1..]
                    .iter()
                    .all(|row| row.status == "padded_scanner_probe_executed"
                        && row.error_code.is_none()
                        && row.trust_cg_probe.is_some())
            );
        } else {
            assert_eq!(probe.status, "padded_scanner_probe_unavailable");
            assert!(probe.rows.iter().all(|row| {
                row.status == "padded_scanner_probe_unavailable"
                    && row.error_code == Some("trust_cg_jit_probe_host_unsupported")
                    && row.operation_measurements.is_empty()
            }));
        }
    }

    #[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
    fn prepare_contains4_masked_backend_variant(variant: &str) -> trust_cg_ir::MachFunction {
        let opt_level = trust_cg_probe_opt_level(variant);
        let disabled_passes = trust_cg_backend_disabled_passes_for_variant(variant);
        let mut func = build_trust_cg_contains4_masked_backend_function();
        let pipeline =
            trust_cg_codegen::pipeline::Pipeline::new(trust_cg_codegen::pipeline::PipelineConfig {
                opt_level,
                verify: false,
                verify_dispatch: trust_cg_codegen::pipeline::DispatchVerifyMode::Off,
                disabled_passes_override: Some(disabled_passes.unwrap_or_default().to_string()),
                contains4_scanner_batch_rewrite_override: Some(
                    trust_cg_backend_enables_contains4_batch_scanner(variant),
                ),
                ..trust_cg_codegen::pipeline::PipelineConfig::default()
            });
        pipeline
            .prepare_ir_function(&mut func)
            .unwrap_or_else(|err| panic!("prepare_ir_function failed for {variant}: {err}"));
        func
    }

    #[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
    fn block_opcode_count(
        func: &trust_cg_ir::MachFunction,
        opcode: trust_cg_ir::AArch64Opcode,
    ) -> usize {
        func.block_order
            .iter()
            .flat_map(|block| func.block(*block).insts.iter().copied())
            .filter(|inst_id| func.inst(*inst_id).opcode == opcode)
            .count()
    }

    #[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
    fn scalar_load_lane_count(func: &trust_cg_ir::MachFunction) -> usize {
        use trust_cg_ir::AArch64Opcode;

        block_opcode_count(func, AArch64Opcode::LdrRI)
            + block_opcode_count(func, AArch64Opcode::LdrPreIndex)
            + block_opcode_count(func, AArch64Opcode::LdrPostIndex)
            + 2 * block_opcode_count(func, AArch64Opcode::LdpRI)
            + 2 * block_opcode_count(func, AArch64Opcode::LdpPostIndex)
    }

    #[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
    #[test]
    fn trust_cg_contains4_masked_backend_structural_vectorization_tracks_vec_toggle() {
        use trust_cg_ir::AArch64Opcode;

        for variant in ["trust_cg_o2_vectorized", "trust_cg_o3_vectorized"] {
            let func = prepare_contains4_masked_backend_variant(variant);
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::NeonCmeqV),
                1,
                "{variant} should use the inlined batch scanner NEON compare"
            );
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::NeonLd1Post),
                1,
                "{variant} should load the padded scanner chunk with LD1"
            );
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::NeonDupGen),
                1,
                "{variant} should materialize one literal DUP for the inlined scanner"
            );
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::NeonInsGen),
                0,
                "{variant} should not pack scalar lane arguments"
            );
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::NeonUmovGen),
                4,
                "{variant} should extract exact lane bits for valid-mask preservation"
            );
            assert!(
                block_opcode_count(&func, AArch64Opcode::LdrRI) < 4,
                "{variant} should remove the four scalar scanner loads"
            );
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::Bl)
                    + block_opcode_count(&func, AArch64Opcode::Blr),
                0,
                "{variant} should not introduce a per-chunk helper call"
            );
            assert_eq!(
                trust_cg_contains4_backend_shape(&func),
                TRUST_CG_CONTAINS4_INLINED_BATCH_BACKEND_SHAPE
            );
        }

        for variant in ["trust_cg_o2_disable_vec", "trust_cg_o3_disable_vec"] {
            let func = prepare_contains4_masked_backend_variant(variant);
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::NeonCmeqV),
                0,
                "{variant} should not contain the NEON compare when vec is disabled"
            );
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::NeonLd1Post),
                0,
                "{variant} should not use LD1 when vec is disabled"
            );
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::NeonInsGen),
                0,
                "{variant} should not pack lanes when vec is disabled"
            );
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::NeonDupGen),
                0,
                "{variant} should not duplicate literals when vec is disabled"
            );
            assert_eq!(
                block_opcode_count(&func, AArch64Opcode::NeonUmovGen),
                0,
                "{variant} should not extract vector lanes when vec is disabled"
            );
            assert!(
                scalar_load_lane_count(&func) >= 4,
                "{variant} should retain four scalar scanner load lanes (pair formation \
                 may use offset, pre-index, or post-index loads)"
            );
            assert!(
                block_opcode_count(&func, AArch64Opcode::CmpRR) >= 4,
                "{variant} should retain the scalar compare chain"
            );
            assert!(
                block_opcode_count(&func, AArch64Opcode::CSet) >= 4,
                "{variant} should retain the scalar flag materialization chain"
            );
        }
    }

    #[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
    #[test]
    fn trust_cg_contains4_masked_backend_scalar_control_correctness_and_profitability_report() {
        let mut cases = ay_subsumption_cases_fixture();
        cases.benchmark_matrix.warmup_iterations = 1;
        cases.benchmark_matrix.measurement_repetitions = 3;
        let backend_buckets = ay_numeric_length_buckets(&cases.benchmark_matrix.length_buckets);
        assert!(backend_buckets.iter().any(|bucket| bucket == "4"));
        let backend = run_trust_cg_backend_execution_with_length_buckets(&cases, &backend_buckets);

        assert!(matches!(
            backend.status,
            "trust_cg_backend_execution_pass" | "trust_cg_backend_execution_partial"
        ));
        let vectorized_mismatch_count = backend
            .rows
            .iter()
            .filter(|row| trust_cg_scalar_control_variant(&row.variant).is_some())
            .map(|row| {
                row.chunk_mismatch_count
                    + row.contains_mismatch_count
                    + row.subsumption_mismatch_count
                    + row.mismatches.len()
            })
            .sum::<usize>();
        assert!(backend.rows.iter().all(|row| {
            !row.variant.contains("disable_vec")
                || (row.chunk_mismatch_count == 0
                    && row.contains_mismatch_count == 0
                    && row.subsumption_mismatch_count == 0
                    && row.mismatches.is_empty())
        }));
        assert!(backend.rows.iter().all(|row| {
            if trust_cg_scalar_control_variant(&row.variant).is_some() {
                row.contains4_backend_shape == TRUST_CG_CONTAINS4_INLINED_BATCH_BACKEND_SHAPE
            } else {
                row.contains4_backend_shape == TRUST_CG_CONTAINS4_SCALAR_BACKEND_SHAPE
            }
        }));
        assert_eq!(backend.scalar_control_comparisons.len(), 2);
        assert!(backend.scalar_control_comparisons.iter().all(|comparison| {
            matches!(
                comparison.status,
                "scalar_control_match" | "scalar_control_mismatch"
            ) && comparison.checked_cases >= 16 * 16 + 16
                && comparison.mismatch_count == comparison.mismatches.len()
        }));
        if vectorized_mismatch_count == 0 {
            assert_eq!(backend.status, "trust_cg_backend_execution_pass");
            assert!(backend.scalar_control_comparisons.iter().all(|comparison| {
                comparison.status == "scalar_control_match"
                    && comparison.error_code.is_none()
                    && comparison.mismatch_count == 0
                    && comparison.mismatches.is_empty()
            }));
        } else {
            assert_eq!(backend.status, "trust_cg_backend_execution_partial");
            assert!(backend.scalar_control_comparisons.iter().any(|comparison| {
                comparison.status == "scalar_control_mismatch"
                    && comparison.error_code == Some("trust_cg_scalar_control_mismatch")
                    && comparison.mismatch_count > 0
            }));
        }
        assert!(backend.scalar_control_comparisons.iter().all(|comparison| {
            comparison.checked_cases >= 16 * 16 + 16
                && ((comparison.mismatch_count == 0)
                    == (comparison.status == "scalar_control_match"))
        }));
        for comparison in &backend.scalar_control_comparisons {
            println!(
                "contains4 scalar-control {} vs {} checked={} mismatches={} status={}",
                comparison.vectorized_variant,
                comparison.scalar_control_variant,
                comparison.checked_cases,
                comparison.mismatch_count,
                comparison.status
            );
        }

        let required_profitability_rows = [
            ("contains_literal", "trust_cg_o2_vectorized", "4"),
            ("batch_subsumption", "trust_cg_o2_vectorized", "4"),
            ("contains_literal", "trust_cg_o3_vectorized", "4"),
            ("batch_subsumption", "trust_cg_o3_vectorized", "4"),
            ("contains_literal", "trust_cg_o2_vectorized", "mixed_2_16"),
            ("batch_subsumption", "trust_cg_o2_vectorized", "mixed_2_16"),
            ("contains_literal", "trust_cg_o3_vectorized", "mixed_2_16"),
            ("batch_subsumption", "trust_cg_o3_vectorized", "mixed_2_16"),
        ];
        for (operation, variant, bucket) in required_profitability_rows {
            let comparison = backend
                .profitability_comparisons
                .iter()
                .find(|comparison| {
                    comparison.operation == operation
                        && comparison.vectorized_variant == variant
                        && comparison.workload_bucket == bucket
                })
                .unwrap_or_else(|| {
                    panic!("missing profitability row {operation} {variant} {bucket}")
                });
            assert!(comparison.vectorized_mean_throughput_per_us.is_some());
            assert!(comparison.scalar_control_mean_throughput_per_us.is_some());
            assert!(comparison.scalar_speedup.is_some());
            assert!(
                matches!(
                    comparison.status,
                    "vectorized_not_slower_than_scalar_control"
                        | "vectorized_slower_than_scalar_control"
                        | TRUST_CG_BACKEND_SCALAR_EQUIVALENT_PROFITABILITY_STATUS
                ),
                "required profitability row {operation} {variant} {bucket} should carry measured scalar-control evidence: {}",
                comparison.message
            );
        }
        for comparison in &backend.profitability_comparisons {
            println!(
                "contains4 profitability {} {} vs {} bucket {} speedup={:?} status={}",
                comparison.operation,
                comparison.vectorized_variant,
                comparison.scalar_control_variant,
                comparison.workload_bucket,
                comparison.scalar_speedup,
                comparison.status
            );
        }
    }

    fn fake_ay_reference_execution() -> AYReferenceExecutionReport {
        AYReferenceExecutionReport {
            schema: "trust-cg.ay_subsumption.ay_reference_execution.v1",
            status: "ay_reference_execution_pass",
            backend_kind: "ay_neon_reference",
            host_arch: "aarch64",
            host_os: "macos",
            repo: Some("/tmp/ay".to_string()),
            requested_rev: Some("origin/main".to_string()),
            resolved_rev: Some("abc123".to_string()),
            source_sha256: Some("feedface".to_string()),
            helper_source_path: Some("/tmp/helper.rs".to_string()),
            helper_binary_path: Some("/tmp/helper".to_string()),
            contains_mismatch_count: 0,
            subsumption_mismatch_count: 0,
            operation_measurements: vec![
                fake_ay_reference_measurement("contains_literal", 120),
                fake_ay_reference_measurement("batch_subsumption", 10),
            ],
            error_code: None,
            message: "executed fake ay reference".to_string(),
            note: "fake test report",
        }
    }

    fn fake_ay_reference_execution_with_buckets(buckets: &[&str]) -> AYReferenceExecutionReport {
        let mut execution = fake_ay_reference_execution();
        for bucket in buckets {
            execution.operation_measurements.extend([
                fake_ay_reference_measurement_for_bucket("contains_literal", 8, bucket),
                fake_ay_reference_measurement_for_bucket("batch_subsumption", 1, bucket),
            ]);
        }
        execution
    }

    fn fake_ay_reference_measurement(
        operation: &'static str,
        items_per_batch: usize,
    ) -> AYReferenceOperationMeasurement {
        fake_ay_reference_measurement_for_bucket(operation, items_per_batch, "mixed_2_16")
    }

    fn fake_ay_reference_measurement_for_bucket(
        operation: &'static str,
        items_per_batch: usize,
        workload_bucket: &str,
    ) -> AYReferenceOperationMeasurement {
        AYReferenceOperationMeasurement {
            operation,
            workload_bucket: workload_bucket.to_string(),
            status: "ay_reference_measured",
            warmup_iterations: 1,
            measurement_repetitions: 2,
            batches_per_repetition: 3,
            items_per_batch,
            total_items: items_per_batch * 3 * 2,
            raw_elapsed_ns: vec![1_000, 2_000],
            mean_elapsed_ns: Some(1_500.0),
            stddev_elapsed_ns: Some(500.0),
            mean_throughput_per_us: Some(1.0),
            stddev_throughput_per_us: Some(0.1),
            coefficient_of_variation: Some(0.1),
            checksum: 42,
            message: "fake ay measurement".to_string(),
        }
    }

    fn fake_trust_cg_backend_probe() -> TrustCgBackendProbeReport {
        TrustCgBackendProbeReport {
            schema: "trust-cg.ay_subsumption.trust_cg_backend_probe.v1",
            status: "padded_scanner_probe_pass",
            probe_kind: "aarch64_raw_jit_contains4_masked",
            promotion_disposition: TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION,
            product_install_evidence: false,
            host_arch: "aarch64",
            host_os: "macos",
            rows: [
                "trust_cg_o2_vectorized",
                "trust_cg_o3_vectorized",
                "trust_cg_o2_disable_vec",
                "trust_cg_o3_disable_vec",
            ]
            .into_iter()
            .map(fake_trust_cg_probe_row)
            .collect(),
            note: "fake test probe",
        }
    }

    fn fake_trust_cg_backend_probe_with_bucket(bucket: &str) -> TrustCgBackendProbeReport {
        fake_trust_cg_backend_probe_with_buckets(&[bucket])
    }

    fn fake_trust_cg_backend_probe_with_buckets(buckets: &[&str]) -> TrustCgBackendProbeReport {
        let mut probe = fake_trust_cg_backend_probe();
        for row in &mut probe.rows {
            for bucket in buckets {
                row.operation_measurements.extend([
                    fake_trust_cg_probe_measurement_for_bucket("contains_literal", 8, bucket),
                    fake_trust_cg_probe_measurement_for_bucket("batch_subsumption", 1, bucket),
                ]);
            }
        }
        probe
    }

    fn fake_trust_cg_backend_execution_with_buckets(
        buckets: &[&str],
    ) -> TrustCgBackendExecutionReport {
        let rows = [
            "trust_cg_o2_vectorized",
            "trust_cg_o3_vectorized",
            "trust_cg_o2_disable_vec",
            "trust_cg_o3_disable_vec",
        ]
        .into_iter()
        .map(|variant| fake_trust_cg_backend_row(variant, buckets))
        .collect::<Vec<_>>();
        let scalar_control_comparisons = fake_trust_cg_scalar_control_comparisons();
        let profitability_comparisons = trust_cg_backend_profitability_comparisons(&rows);

        TrustCgBackendExecutionReport {
            schema: "trust-cg.ay_subsumption.trust_cg_backend_execution.v1",
            status: "trust_cg_backend_execution_pass",
            backend_kind: "aarch64_o2_o3_pipeline_jit_contains4_masked",
            host_arch: "aarch64",
            host_os: "macos",
            rows,
            scalar_control_comparisons,
            profitability_comparisons,
            note: "fake test backend",
        }
    }

    fn fake_trust_cg_scalar_control_comparisons() -> Vec<TrustCgContains4ScalarControlComparison> {
        trust_cg_contains4_scalar_control_pairs()
            .into_iter()
            .map(|(vectorized_variant, scalar_control_variant)| {
                let (opt_level, _) = trust_cg_variant_probe_mode(vectorized_variant);
                TrustCgContains4ScalarControlComparison {
                    vectorized_variant: vectorized_variant.to_string(),
                    scalar_control_variant: scalar_control_variant.to_string(),
                    opt_level,
                    status: "scalar_control_match",
                    error_code: None,
                    checked_cases: 4,
                    mismatch_count: 0,
                    mismatches: Vec::new(),
                    message: "fake scalar-control comparison".to_string(),
                }
            })
            .collect()
    }

    fn fake_trust_cg_probe_row(variant: &str) -> TrustCgBackendProbeRow {
        let (opt_level, vectorizer_mode) = trust_cg_variant_probe_mode(variant);
        TrustCgBackendProbeRow {
            variant: variant.to_string(),
            backend_kind: "trust_cg_jit_scanner_probe",
            promotion_disposition: TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION,
            product_install_evidence: false,
            opt_level,
            vectorizer_mode,
            status: "padded_scanner_probe_executed",
            error_code: None,
            function_name: TRUST_CG_CONTAINS4_MASKED_PROBE_FN,
            checked_cases: 4,
            chunk_mismatch_count: 0,
            contains_query_count: 2,
            contains_mismatch_count: 0,
            subsumption_pair_count: 2,
            subsumption_mismatch_count: 0,
            mismatches: Vec::new(),
            operation_measurements: vec![
                fake_trust_cg_probe_measurement("contains_literal", 120),
                fake_trust_cg_probe_measurement("batch_subsumption", 10),
            ],
            timed_calls: 4,
            elapsed_ns: Some(1_000),
            calls_per_us: Some(4.0),
            message: "fake Trust Codegen probe row".to_string(),
        }
    }

    fn fake_trust_cg_backend_row(variant: &str, buckets: &[&str]) -> TrustCgBackendExecutionRow {
        let (opt_level, vectorizer_mode) = trust_cg_variant_probe_mode(variant);
        TrustCgBackendExecutionRow {
            variant: variant.to_string(),
            backend_kind: "trust_cg_o2_o3_pipeline_jit_scanner",
            opt_level,
            vectorizer_mode,
            disabled_passes: trust_cg_backend_disabled_passes_for_variant(variant),
            contains4_backend_shape: TRUST_CG_CONTAINS4_SCALAR_BACKEND_SHAPE,
            status: "trust_cg_backend_executed",
            error_code: None,
            function_name: TRUST_CG_CONTAINS4_MASKED_BACKEND_FN,
            checked_cases: 4,
            chunk_mismatch_count: 0,
            contains_query_count: 2,
            contains_mismatch_count: 0,
            subsumption_pair_count: 2,
            subsumption_mismatch_count: 0,
            mismatches: Vec::new(),
            operation_measurements: buckets
                .iter()
                .flat_map(|bucket| {
                    [
                        fake_trust_cg_backend_measurement_for_bucket("contains_literal", 8, bucket),
                        fake_trust_cg_backend_measurement_for_bucket(
                            "batch_subsumption",
                            1,
                            bucket,
                        ),
                    ]
                })
                .collect(),
            message: "fake Trust Codegen backend row".to_string(),
        }
    }

    fn fake_trust_cg_probe_measurement(
        operation: &'static str,
        items_per_batch: usize,
    ) -> TrustCgProbeOperationMeasurement {
        fake_trust_cg_probe_measurement_for_bucket(
            operation,
            items_per_batch,
            TRUST_CG_PROBE_WORKLOAD_BUCKET,
        )
    }

    fn fake_trust_cg_probe_measurement_for_bucket(
        operation: &'static str,
        items_per_batch: usize,
        workload_bucket: &str,
    ) -> TrustCgProbeOperationMeasurement {
        TrustCgProbeOperationMeasurement {
            operation,
            workload_bucket: workload_bucket.to_string(),
            status: "probe_measured",
            promotion_disposition: TRUST_CG_RAW_PROBE_PROMOTION_DISPOSITION,
            warmup_iterations: 1,
            measurement_repetitions: 2,
            batches_per_repetition: 3,
            items_per_batch,
            total_items: items_per_batch * 3 * 2,
            raw_elapsed_ns: vec![900, 1_800],
            mean_elapsed_ns: Some(1_350.0),
            stddev_elapsed_ns: Some(450.0),
            mean_throughput_per_us: Some(1.2),
            stddev_throughput_per_us: Some(0.12),
            coefficient_of_variation: Some(0.1),
            checksum: 43,
            message: "fake Trust Codegen probe measurement".to_string(),
        }
    }

    fn fake_trust_cg_backend_measurement_for_bucket(
        operation: &'static str,
        items_per_batch: usize,
        workload_bucket: &str,
    ) -> TrustCgBackendOperationMeasurement {
        TrustCgBackendOperationMeasurement {
            operation,
            workload_bucket: workload_bucket.to_string(),
            status: "backend_measured",
            warmup_iterations: 1,
            measurement_repetitions: 2,
            batches_per_repetition: 3,
            items_per_batch,
            total_items: items_per_batch * 3 * 2,
            raw_elapsed_ns: vec![800, 1_600],
            mean_elapsed_ns: Some(1_200.0),
            stddev_elapsed_ns: Some(400.0),
            mean_throughput_per_us: Some(1.4),
            stddev_throughput_per_us: Some(0.14),
            coefficient_of_variation: Some(0.1),
            checksum: 44,
            message: "fake Trust Codegen backend measurement".to_string(),
        }
    }
}
