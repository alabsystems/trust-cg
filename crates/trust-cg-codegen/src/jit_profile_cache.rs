// trust-cg-codegen/jit_profile_cache.rs - JIT-everywhere profile-only cache
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only profile cache for JIT-everywhere prework.
//!
//! This cache stores learning records only. Entries may describe compiled
//! payload metadata, failed proof diagnostics, cost data, and replay roots, but
//! they cannot authorize callable handles, installable cache hits, ay registry
//! insertion, TY native activation, or useful-native accounting.

use std::collections::BTreeMap;

use crate::jit_diagnostics::sha256_hex;
use crate::target::Target;

/// Stable schema tag for profile-only cache entries.
pub const JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA: &str = "trust-cg.jit_everywhere.profile_cache.v1";

/// Stable numeric schema version for profile-only cache entries.
pub const JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA_VERSION: u32 = 1;

/// Stable profile-only cache key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileCacheKey {
    /// Consumer source or solver-program SHA-256.
    pub source_sha256: String,
    /// Canonical trust_ir SHA-256.
    pub trust_ir_sha256: String,
    /// Optimization pipeline id or checksum.
    pub optimization_pipeline: String,
    /// Codegen target.
    pub target: Target,
    /// Target fact digest.
    pub target_facts_sha256: String,
    /// Profile schema id or checksum.
    pub profile_schema: String,
    /// Proof-policy id or checksum.
    pub proof_policy: String,
    /// Downstream consumer: `trust-cg`, `ay`, or `ty`.
    pub consumer: String,
    /// Consumer generation domain.
    pub generation_domain: String,
    /// Canonical key SHA-256.
    pub key_sha256: String,
}

impl ProfileCacheKey {
    /// Build a canonical cache key.
    pub fn new(
        source_sha256: impl Into<String>,
        trust_ir_sha256: impl Into<String>,
        optimization_pipeline: impl Into<String>,
        target: Target,
        target_facts_sha256: impl Into<String>,
        profile_schema: impl Into<String>,
        proof_policy: impl Into<String>,
        consumer: impl Into<String>,
        generation_domain: impl Into<String>,
    ) -> Self {
        let mut key = Self {
            source_sha256: source_sha256.into(),
            trust_ir_sha256: trust_ir_sha256.into(),
            optimization_pipeline: optimization_pipeline.into(),
            target,
            target_facts_sha256: target_facts_sha256.into(),
            profile_schema: profile_schema.into(),
            proof_policy: proof_policy.into(),
            consumer: consumer.into(),
            generation_domain: generation_domain.into(),
            key_sha256: String::new(),
        };
        key.key_sha256 = key.canonical_key_sha256();
        key
    }

    /// Return the stable hash of this cache key.
    pub fn canonical_key_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, "trust-cg.jit_everywhere.profile_cache.key.v1");
        put_str(&mut out, &self.source_sha256);
        put_str(&mut out, &self.trust_ir_sha256);
        put_str(&mut out, &self.optimization_pipeline);
        put_str(&mut out, self.target.name());
        put_str(&mut out, &self.target_facts_sha256);
        put_str(&mut out, &self.profile_schema);
        put_str(&mut out, &self.proof_policy);
        put_str(&mut out, &self.consumer);
        put_str(&mut out, &self.generation_domain);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.source_sha256)
            && !missing_required_text(&self.trust_ir_sha256)
            && !missing_required_text(&self.optimization_pipeline)
            && !missing_required_text(&self.target_facts_sha256)
            && !missing_required_text(&self.profile_schema)
            && !missing_required_text(&self.proof_policy)
            && matches!(self.consumer.as_str(), "trust-cg" | "ay" | "ty")
            && !missing_required_text(&self.generation_domain)
            && self.key_sha256 == self.canonical_key_sha256()
    }
}

/// Learning outcome stored in the profile-only cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProfileCacheOutcome {
    /// Compiled payload metadata exists but remains profile-only.
    ProfileOnlyArtifact,
    /// Baseline fallback occurred.
    Fallback,
    /// Proof or verifier timed out.
    VerifierTimeout,
    /// Target was unsupported by this route.
    UnsupportedTarget,
    /// Proof, layout, or generation evidence was stale.
    StaleEvidence,
    /// Proof rejected the candidate.
    ProofRejected,
}

impl ProfileCacheOutcome {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ProfileOnlyArtifact => "profile_only_artifact",
            Self::Fallback => "fallback",
            Self::VerifierTimeout => "verifier_timeout",
            Self::UnsupportedTarget => "unsupported_target",
            Self::StaleEvidence => "stale_evidence",
            Self::ProofRejected => "proof_rejected",
        }
    }

    /// Return true for every profile-only cache outcome.
    pub const fn is_learning_only(self) -> bool {
        true
    }
}

/// Metadata for a profile-only compiled payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileOnlyArtifactMetadata {
    /// Native payload SHA-256 when bytes were produced by a non-installing path.
    pub native_payload_sha256: String,
    /// Object or native code byte length when known.
    pub code_len: u64,
    /// Entry symbol observed by the profile-only route.
    pub entry_symbol: String,
}

impl ProfileOnlyArtifactMetadata {
    /// Build profile-only artifact metadata.
    pub fn new(
        native_payload_sha256: impl Into<String>,
        code_len: u64,
        entry_symbol: impl Into<String>,
    ) -> Self {
        Self {
            native_payload_sha256: native_payload_sha256.into(),
            code_len,
            entry_symbol: entry_symbol.into(),
        }
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.native_payload_sha256)
            && self.code_len > 0
            && !missing_required_text(&self.entry_symbol)
    }
}

/// Failed proof or verifier diagnostic preserved as learning data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileCacheProofDiagnostic {
    /// Verifier or proof route name.
    pub verifier: String,
    /// Stable verdict string, for example `timeout` or `unsupported_target`.
    pub verdict: String,
    /// Stable rejection reason when present.
    pub rejection_reason: Option<String>,
    /// Proof report SHA-256 when available.
    pub proof_report_sha256: Option<String>,
    /// Timeout budget when available.
    pub timeout_ms: Option<u64>,
}

impl ProfileCacheProofDiagnostic {
    /// Build one proof diagnostic.
    pub fn new(
        verifier: impl Into<String>,
        verdict: impl Into<String>,
        rejection_reason: Option<String>,
        proof_report_sha256: Option<String>,
        timeout_ms: Option<u64>,
    ) -> Self {
        Self {
            verifier: verifier.into(),
            verdict: verdict.into(),
            rejection_reason,
            proof_report_sha256,
            timeout_ms,
        }
    }
}

/// Cost data captured by a profile-only route.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProfileCacheCostData {
    /// Compile time in microseconds.
    pub compile_us: u64,
    /// Proof time in microseconds.
    pub proof_us: u64,
    /// Observed baseline time in nanoseconds.
    pub baseline_ns: u64,
    /// Estimated native time in nanoseconds.
    pub estimated_native_ns: u64,
}

impl ProfileCacheCostData {
    /// Build deterministic profile cost data.
    pub const fn new(
        compile_us: u64,
        proof_us: u64,
        baseline_ns: u64,
        estimated_native_ns: u64,
    ) -> Self {
        Self {
            compile_us,
            proof_us,
            baseline_ns,
            estimated_native_ns,
        }
    }
}

/// Replay reference stored with one profile-only learning entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileCacheReplayReference {
    /// Replay root SHA-256.
    pub replay_root_sha256: String,
    /// Replay record SHA-256.
    pub replay_record_sha256: String,
    /// Optional reducer SHA-256.
    pub reducer_sha256: Option<String>,
}

impl ProfileCacheReplayReference {
    /// Build one replay reference.
    pub fn new(
        replay_root_sha256: impl Into<String>,
        replay_record_sha256: impl Into<String>,
        reducer_sha256: Option<String>,
    ) -> Self {
        Self {
            replay_root_sha256: replay_root_sha256.into(),
            replay_record_sha256: replay_record_sha256.into(),
            reducer_sha256,
        }
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.replay_root_sha256)
            && !missing_required_text(&self.replay_record_sha256)
    }
}

/// Explicitly blocked install/call side effects for profile-only entries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ProfileCacheSideEffects {
    /// Whether a callable handle was published.
    pub callable_handle_published: bool,
    /// Whether an installable cache entry was written.
    pub installable_cache_written: bool,
    /// Whether an installable cache hit was accepted.
    pub installable_cache_hit_accepted: bool,
    /// Whether ay registry insertion occurred.
    pub ay_registry_inserted: bool,
    /// Whether TY native activation occurred.
    pub ty_native_activated: bool,
    /// Whether baseline execution was replaced.
    pub baseline_replaced: bool,
    /// Useful-native counter delta.
    pub useful_native_delta: u64,
}

impl ProfileCacheSideEffects {
    /// Return true when every install-authorizing side effect is blocked.
    pub const fn all_install_authority_blocked(self) -> bool {
        !self.callable_handle_published
            && !self.installable_cache_written
            && !self.installable_cache_hit_accepted
            && !self.ay_registry_inserted
            && !self.ty_native_activated
            && !self.baseline_replaced
            && self.useful_native_delta == 0
    }
}

/// Profile-only cache entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileCacheEntry {
    /// Entry schema.
    pub schema: &'static str,
    /// Entry schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Stable profile cache key.
    pub key: ProfileCacheKey,
    /// Learning outcome.
    pub outcome: ProfileCacheOutcome,
    /// Optional non-installing artifact metadata.
    pub artifact: Option<ProfileOnlyArtifactMetadata>,
    /// Optional proof/verifier diagnostic.
    pub proof_diagnostic: Option<ProfileCacheProofDiagnostic>,
    /// Cost data.
    pub cost: ProfileCacheCostData,
    /// Replay reference.
    pub replay: ProfileCacheReplayReference,
    /// Baseline remains authoritative for consumer-visible results.
    pub baseline_authoritative: bool,
    /// Explicit no-install side-effect summary.
    pub side_effects: ProfileCacheSideEffects,
    /// Canonical entry SHA-256.
    pub entry_sha256: String,
}

impl ProfileCacheEntry {
    /// Build a profile-only cache entry.
    pub fn new(
        key: ProfileCacheKey,
        outcome: ProfileCacheOutcome,
        artifact: Option<ProfileOnlyArtifactMetadata>,
        proof_diagnostic: Option<ProfileCacheProofDiagnostic>,
        cost: ProfileCacheCostData,
        replay: ProfileCacheReplayReference,
    ) -> Self {
        let mut entry = Self {
            schema: JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA,
            schema_version: JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA_VERSION,
            issue: 737,
            key,
            outcome,
            artifact,
            proof_diagnostic,
            cost,
            replay,
            baseline_authoritative: true,
            side_effects: ProfileCacheSideEffects::default(),
            entry_sha256: String::new(),
        };
        entry.entry_sha256 = entry.canonical_entry_sha256();
        entry
    }

    /// Return the stable hash of this entry.
    pub fn canonical_entry_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_u64(&mut out, self.issue);
        put_key(&mut out, &self.key);
        put_str(&mut out, self.outcome.as_str());
        put_optional_artifact(&mut out, self.artifact.as_ref());
        put_optional_proof_diagnostic(&mut out, self.proof_diagnostic.as_ref());
        put_cost(&mut out, self.cost);
        put_replay(&mut out, &self.replay);
        put_bool(&mut out, self.baseline_authoritative);
        put_side_effects(&mut out, self.side_effects);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return true when this entry is valid profile-only learning data.
    pub fn is_replayable_learning(&self) -> bool {
        self.schema == JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA
            && self.schema_version == JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA_VERSION
            && self.issue == 737
            && self.key.has_required_identity()
            && self.outcome.is_learning_only()
            && self
                .artifact
                .as_ref()
                .map(ProfileOnlyArtifactMetadata::has_required_identity)
                .unwrap_or(true)
            && self.replay.has_required_identity()
            && self.baseline_authoritative
            && self.side_effects.all_install_authority_blocked()
            && self.entry_sha256 == self.canonical_entry_sha256()
    }
}

/// Rejection reason for attempting to use profile-only cache as install authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProfileCacheInstallRejection {
    /// Entry exists but is profile-only and non-installable.
    ProfileOnlyNonInstallable,
    /// No learning entry exists for this key.
    MissingProfileEntry,
    /// Entry identity or replay binding is invalid.
    InvalidProfileEntry,
}

impl ProfileCacheInstallRejection {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ProfileOnlyNonInstallable => "profile_only_non_installable",
            Self::MissingProfileEntry => "missing_profile_entry",
            Self::InvalidProfileEntry => "invalid_profile_entry",
        }
    }
}

/// Result of a callable/install lookup against the profile-only cache.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileCacheCallableLookup {
    /// Cache key hash requested by the caller.
    pub key_sha256: String,
    /// Whether a profile-only learning entry was present.
    pub entry_present: bool,
    /// Stable rejection reason.
    pub rejection: ProfileCacheInstallRejection,
    /// Baseline remains authoritative.
    pub baseline_authoritative: bool,
    /// No callable handle is ever returned by this surface.
    pub callable_handle_id: Option<String>,
    /// No installable cache hit is ever accepted by this surface.
    pub installable_cache_hit_accepted: bool,
    /// Useful-native counter delta.
    pub useful_native_delta: u64,
}

impl ProfileCacheCallableLookup {
    /// Return true when this lookup preserved all non-installing guarantees.
    pub fn denied_without_install_authority(&self) -> bool {
        self.baseline_authoritative
            && self.callable_handle_id.is_none()
            && !self.installable_cache_hit_accepted
            && self.useful_native_delta == 0
    }
}

/// Profile-only speculative learning cache.
#[derive(Debug, Clone, Default)]
pub struct ProfileOnlySpeculativeCache {
    entries: BTreeMap<String, ProfileCacheEntry>,
}

impl ProfileOnlySpeculativeCache {
    /// Build an empty profile-only cache.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert one replayable profile-only learning entry.
    pub fn insert_learning_entry(
        &mut self,
        entry: ProfileCacheEntry,
    ) -> Result<(), ProfileCacheInstallRejection> {
        if !entry.is_replayable_learning() {
            return Err(ProfileCacheInstallRejection::InvalidProfileEntry);
        }
        self.entries.insert(entry.key.key_sha256.clone(), entry);
        Ok(())
    }

    /// Return one profile-only learning entry.
    pub fn get_learning_entry(&self, key: &ProfileCacheKey) -> Option<&ProfileCacheEntry> {
        self.entries.get(&key.key_sha256)
    }

    /// Return the replay reference for a profile-only learning entry.
    pub fn replay_reference(&self, key: &ProfileCacheKey) -> Option<&ProfileCacheReplayReference> {
        self.get_learning_entry(key).map(|entry| &entry.replay)
    }

    /// Deliberately deny callable or installable-cache retrieval.
    pub fn lookup_callable_install(&self, key: &ProfileCacheKey) -> ProfileCacheCallableLookup {
        let entry = self.entries.get(&key.key_sha256);
        let rejection = match entry {
            Some(entry) if entry.is_replayable_learning() => {
                ProfileCacheInstallRejection::ProfileOnlyNonInstallable
            }
            Some(_) => ProfileCacheInstallRejection::InvalidProfileEntry,
            None => ProfileCacheInstallRejection::MissingProfileEntry,
        };
        ProfileCacheCallableLookup {
            key_sha256: key.key_sha256.clone(),
            entry_present: entry.is_some(),
            rejection,
            baseline_authoritative: true,
            callable_handle_id: None,
            installable_cache_hit_accepted: false,
            useful_native_delta: 0,
        }
    }

    /// Number of learning entries in this cache.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Return true when no learning entries exist.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

fn put_key(out: &mut Vec<u8>, key: &ProfileCacheKey) {
    put_str(out, &key.source_sha256);
    put_str(out, &key.trust_ir_sha256);
    put_str(out, &key.optimization_pipeline);
    put_str(out, key.target.name());
    put_str(out, &key.target_facts_sha256);
    put_str(out, &key.profile_schema);
    put_str(out, &key.proof_policy);
    put_str(out, &key.consumer);
    put_str(out, &key.generation_domain);
    put_str(out, &key.key_sha256);
}

fn put_optional_artifact(out: &mut Vec<u8>, artifact: Option<&ProfileOnlyArtifactMetadata>) {
    if let Some(artifact) = artifact {
        put_bool(out, true);
        put_str(out, &artifact.native_payload_sha256);
        put_u64(out, artifact.code_len);
        put_str(out, &artifact.entry_symbol);
    } else {
        put_bool(out, false);
    }
}

fn put_optional_proof_diagnostic(
    out: &mut Vec<u8>,
    diagnostic: Option<&ProfileCacheProofDiagnostic>,
) {
    if let Some(diagnostic) = diagnostic {
        put_bool(out, true);
        put_str(out, &diagnostic.verifier);
        put_str(out, &diagnostic.verdict);
        put_option_str(out, diagnostic.rejection_reason.as_deref());
        put_option_str(out, diagnostic.proof_report_sha256.as_deref());
        put_option_u64(out, diagnostic.timeout_ms);
    } else {
        put_bool(out, false);
    }
}

fn put_cost(out: &mut Vec<u8>, cost: ProfileCacheCostData) {
    put_u64(out, cost.compile_us);
    put_u64(out, cost.proof_us);
    put_u64(out, cost.baseline_ns);
    put_u64(out, cost.estimated_native_ns);
}

fn put_replay(out: &mut Vec<u8>, replay: &ProfileCacheReplayReference) {
    put_str(out, &replay.replay_root_sha256);
    put_str(out, &replay.replay_record_sha256);
    put_option_str(out, replay.reducer_sha256.as_deref());
}

fn put_side_effects(out: &mut Vec<u8>, side_effects: ProfileCacheSideEffects) {
    put_bool(out, side_effects.callable_handle_published);
    put_bool(out, side_effects.installable_cache_written);
    put_bool(out, side_effects.installable_cache_hit_accepted);
    put_bool(out, side_effects.ay_registry_inserted);
    put_bool(out, side_effects.ty_native_activated);
    put_bool(out, side_effects.baseline_replaced);
    put_u64(out, side_effects.useful_native_delta);
}

fn put_str(out: &mut Vec<u8>, value: &str) {
    put_u64(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

fn put_option_str(out: &mut Vec<u8>, value: Option<&str>) {
    if let Some(value) = value {
        put_bool(out, true);
        put_str(out, value);
    } else {
        put_bool(out, false);
    }
}

fn put_option_u64(out: &mut Vec<u8>, value: Option<u64>) {
    if let Some(value) = value {
        put_bool(out, true);
        put_u64(out, value);
    } else {
        put_bool(out, false);
    }
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}
