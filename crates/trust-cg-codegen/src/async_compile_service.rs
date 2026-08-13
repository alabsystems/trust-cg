// trust-cg-codegen - Runtime-neutral async compile facade
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Runtime-neutral submit/cancel/poll facade for compile-service workers.
//!
//! This module deliberately does not own an executor. Callers enqueue
//! [`CompileRequest`] values, drive backend work with [`AsyncCompileService::start_next`]
//! and [`AsyncCompileService::finish`], and observe state through
//! [`AsyncCompileService::poll`].

use std::collections::{HashMap, HashSet, VecDeque};

use serde_json::{Value, json};

use crate::compile_service::{
    ArtifactInstallDisposition, CompileDiagnostic, CompileGeneration, CompileRequest,
    CompileRequestId, CompileResponse, CompileService, CompileStatus, DiagnosticSeverity,
    ExplainReject, RejectCode,
};
use crate::jit_contract::ArtifactManifestV1;
use crate::jit_install_gate::{
    NATIVE_INSTALL_GATE_PACKET_SCHEMA, NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION,
    NativeInstallGatePacket, NativeInstallGateRejectionCode, NativeInstallGateRevalidationInput,
    NativeInstallGateSurface, NativeInstallGateVerdict,
    validate_native_install_gate_packet_with_current,
};

/// Stable schema tag for metadata-only Phase 6 async compile telemetry.
pub const ASYNC_COMPILE_TELEMETRY_SCHEMA: &str = "trust-cg.phase6.compile_telemetry.v1";

/// Stable numeric schema version for [`AsyncCompileTelemetryPacket`].
pub const ASYNC_COMPILE_TELEMETRY_SCHEMA_VERSION: u32 = 1;

/// Runtime-neutral async facade configuration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AsyncCompileServiceConfig {
    /// Maximum queued requests waiting for a worker.
    pub max_queued: usize,
    /// Maximum accepted requests over this facade lifetime.
    pub max_total_submitted: Option<usize>,
    /// Maximum terminal responses retained for polling.
    pub max_terminal_retained: usize,
    /// Maximum evicted request ids remembered for typed `evicted` polls.
    pub max_evicted_retained: usize,
}

impl Default for AsyncCompileServiceConfig {
    fn default() -> Self {
        Self {
            max_queued: 1024,
            max_total_submitted: None,
            max_terminal_retained: 1024,
            max_evicted_retained: 1024,
        }
    }
}

/// Stable async compile state returned by [`AsyncCompileService::poll`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncCompileState {
    /// Request is accepted and waiting for a worker.
    Queued,
    /// Request has been handed to a worker.
    Running,
    /// Request compiled an installable artifact.
    CompiledInstallable,
    /// Request compiled a profile-only artifact that must not install.
    ProfileOnly,
    /// Request was rejected before producing an installable result.
    Rejected,
    /// Request was cancelled before an installable result could publish.
    Cancelled,
    /// Request generation was stale before an installable result could publish.
    StaleGeneration,
    /// Backend compilation failed.
    Failed,
    /// A terminal result existed but was evicted from this facade.
    Evicted,
    /// The request id is unknown to this facade.
    NotFound,
}

impl AsyncCompileState {
    /// Return the stable lower-snake-case state code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Queued => "queued",
            Self::Running => "running",
            Self::CompiledInstallable => "compiled_installable",
            Self::ProfileOnly => "profile_only",
            Self::Rejected => "rejected",
            Self::Cancelled => "cancelled",
            Self::StaleGeneration => "stale_generation",
            Self::Failed => "failed",
            Self::Evicted => "evicted",
            Self::NotFound => "not_found",
        }
    }

    /// Return whether this state can publish an installed artifact.
    pub const fn is_installable(self) -> bool {
        matches!(self, Self::CompiledInstallable)
    }

    /// Return whether this state is terminal.
    pub const fn is_terminal(self) -> bool {
        !matches!(self, Self::Queued | Self::Running)
    }
}

/// Stable immediate submit rejection code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncSubmitRejectCode {
    /// The queue is at capacity.
    QueueFull,
    /// This facade's configured submit budget has been exhausted.
    BudgetExceeded,
    /// The request generation is older than its effective generation fence.
    StaleGeneration,
    /// The request was already cancelled at submit time.
    Cancelled,
    /// The request id is already queued, running, or retained as terminal.
    DuplicateRequest,
    /// Another queued or running request has the same manifest cache key.
    DuplicateCacheKey,
}

impl AsyncSubmitRejectCode {
    /// Return the stable lower-snake-case rejection code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::QueueFull => "queue_full",
            Self::BudgetExceeded => "budget_exceeded",
            Self::StaleGeneration => "stale_generation",
            Self::Cancelled => "cancelled",
            Self::DuplicateRequest => "duplicate_request",
            Self::DuplicateCacheKey => "duplicate_cache_key",
        }
    }

    const fn state(self) -> AsyncCompileState {
        match self {
            Self::StaleGeneration => AsyncCompileState::StaleGeneration,
            Self::Cancelled => AsyncCompileState::Cancelled,
            Self::QueueFull
            | Self::BudgetExceeded
            | Self::DuplicateRequest
            | Self::DuplicateCacheKey => AsyncCompileState::Rejected,
        }
    }

    const fn compile_status(self) -> CompileStatus {
        match self {
            Self::StaleGeneration => CompileStatus::Stale,
            Self::Cancelled => CompileStatus::Cancelled,
            Self::QueueFull
            | Self::BudgetExceeded
            | Self::DuplicateRequest
            | Self::DuplicateCacheKey => CompileStatus::Rejected,
        }
    }
}

/// Manifest-keyed async cache lookup outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncCacheLookupOutcome {
    /// Cache has an artifact marked installable by its metadata.
    HitInstallable,
    /// Cache has replay metadata but no install authority.
    HitReplayOnly,
    /// No entry exists for the manifest key.
    Miss,
    /// Cache entry is stale for the requested manifest key.
    Stale,
    /// Cache entry cannot be decoded or validated.
    Corrupt,
    /// Cache entry schema is not compatible with this async facade.
    SchemaMismatch,
    /// Cache entry requires a feature this facade does not support.
    UnsupportedRequiredFeature,
    /// Cache entry claims install authority but has no native install gate packet.
    GateMetadataMissing,
    /// Cache entry native install gate packet does not match the requested manifest.
    GateMetadataMismatch,
    /// Cache entry native install gate packet is present but not accepted.
    GateRejected,
}

impl AsyncCacheLookupOutcome {
    /// Return the stable lower-snake-case outcome code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::HitInstallable => "hit_installable",
            Self::HitReplayOnly => "hit_replay_only",
            Self::Miss => "miss",
            Self::Stale => "stale",
            Self::Corrupt => "corrupt",
            Self::SchemaMismatch => "schema_mismatch",
            Self::UnsupportedRequiredFeature => "unsupported_required_feature",
            Self::GateMetadataMissing => "gate_metadata_missing",
            Self::GateMetadataMismatch => "gate_metadata_mismatch",
            Self::GateRejected => "gate_rejected",
        }
    }
}

/// Stable async/cache gate metadata blocker code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncInstallGateBlockerCode {
    /// Installable-looking metadata did not carry a gate packet.
    MissingGateMetadata,
    /// A gate packet was present but did not bind the same manifest/surface.
    GateMetadataMismatch,
    /// A gate packet was present but the gate verdict did not authorize install.
    GateRejected,
}

impl AsyncInstallGateBlockerCode {
    /// Return the stable lower-snake-case blocker code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingGateMetadata => "missing_gate_metadata",
            Self::GateMetadataMismatch => "gate_metadata_mismatch",
            Self::GateRejected => "gate_rejected",
        }
    }

    const fn cache_outcome(self) -> AsyncCacheLookupOutcome {
        match self {
            Self::MissingGateMetadata => AsyncCacheLookupOutcome::GateMetadataMissing,
            Self::GateMetadataMismatch => AsyncCacheLookupOutcome::GateMetadataMismatch,
            Self::GateRejected => AsyncCacheLookupOutcome::GateRejected,
        }
    }

    const fn diagnostic_code(self) -> &'static str {
        match self {
            Self::MissingGateMetadata => "async.native_install_gate_missing_metadata",
            Self::GateMetadataMismatch => "async.native_install_gate_metadata_mismatch",
            Self::GateRejected => "async.native_install_gate_rejected",
        }
    }

    const fn diagnostic_message(self) -> &'static str {
        match self {
            Self::MissingGateMetadata => {
                "async installable response missing native install gate metadata"
            }
            Self::GateMetadataMismatch => {
                "async installable response native install gate metadata mismatch"
            }
            Self::GateRejected => "async installable response native install gate verdict rejected",
        }
    }
}

/// Immediate submit rejection with stable reason code.
#[derive(Debug, Clone)]
pub struct AsyncSubmitReject {
    /// Rejected request id.
    pub request_id: CompileRequestId,
    /// Stable lower-snake-case reason code.
    pub code: AsyncSubmitRejectCode,
    /// Poll state represented by this rejection.
    pub state: AsyncCompileState,
    /// Rejection response retained for `explain_reject`.
    pub response: CompileResponse,
}

/// Successful submit result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AsyncSubmitAccepted {
    /// Accepted request id.
    pub request_id: CompileRequestId,
    /// Initial poll state.
    pub state: AsyncCompileState,
}

/// Worker-owned ticket returned when a queued request starts.
#[derive(Debug, Clone)]
pub struct AsyncCompileTicket {
    /// Request id being compiled.
    pub request_id: CompileRequestId,
    /// Request generation being compiled.
    pub generation: CompileGeneration,
    /// Full request to pass to [`CompileService`].
    pub request: CompileRequest,
}

/// Typed poll result for a request id.
#[derive(Debug, Clone)]
pub struct AsyncCompilePoll {
    /// Polled request id.
    pub request_id: CompileRequestId,
    /// Current async state.
    pub state: AsyncCompileState,
    /// Terminal compile response, when retained.
    pub response: Option<CompileResponse>,
}

impl AsyncCompilePoll {
    /// Return whether this poll result can publish an installed artifact.
    pub fn is_installable(&self) -> bool {
        if !self.state.is_installable() {
            return false;
        }
        let Some(response) = self.response.as_ref() else {
            return false;
        };
        let native_install_gate = response_native_install_gate_packet(response);
        response_gate_blocker(self.state, response, native_install_gate.as_ref()).is_none()
    }
}

/// Stable async telemetry lifecycle event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncCompileTelemetryEvent {
    /// A request reached the async submit API.
    Submit,
    /// A request was rejected synchronously by submit.
    ImmediateReject,
    /// A request was accepted into the queue.
    Queued,
    /// A worker started a queued request.
    Running,
    /// A queued or running request was cancelled.
    Cancel,
    /// A request became stale before publishing a useful response.
    StaleDrop,
    /// A worker finished and published a terminal response.
    Finish,
    /// A caller polled request state.
    Poll,
    /// A caller asked for a non-installable explanation.
    ExplainReject,
    /// Backend compilation failed.
    Failed,
    /// A compiled response was retained for profile-only use.
    ProfileOnly,
    /// A compiled response was visible to telemetry.
    CompiledResponse,
}

impl AsyncCompileTelemetryEvent {
    /// Return the stable lower-snake-case event code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Submit => "submit",
            Self::ImmediateReject => "immediate_reject",
            Self::Queued => "queued",
            Self::Running => "running",
            Self::Cancel => "cancel",
            Self::StaleDrop => "stale_drop",
            Self::Finish => "finish",
            Self::Poll => "poll",
            Self::ExplainReject => "explain_reject",
            Self::Failed => "failed",
            Self::ProfileOnly => "profile_only",
            Self::CompiledResponse => "compiled_response",
        }
    }
}

/// Metadata-only async compile lifecycle packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AsyncCompileTelemetryPacket {
    /// Stable schema name.
    pub schema: &'static str,
    /// Stable numeric schema version.
    pub schema_version: u32,
    /// Lifecycle event.
    pub event: AsyncCompileTelemetryEvent,
    /// Caller-supplied request id.
    pub request_id: String,
    /// Request id repeated as provenance join key.
    pub request_provenance: String,
    /// Compile generation, when known.
    pub generation: Option<u64>,
    /// Caller-visible artifact identity, when a response has one.
    pub artifact_ref: Option<String>,
    /// Deterministic manifest reference, when a response has one.
    pub manifest_ref: Option<String>,
    /// Proof-policy checksum reference, when a manifest reference has one.
    pub proof_ref: Option<String>,
    /// Release/replay bundle reference, when async compile owns one.
    pub release_ref: Option<String>,
    /// Manifest-keyed async cache identity, when a request has a manifest.
    pub cache_key: Option<String>,
    /// Manifest-keyed async cache lookup outcome, when a lookup was possible.
    pub cache_lookup_outcome: Option<AsyncCacheLookupOutcome>,
    /// Native install gate packet preserved for async/cache joins.
    pub native_install_gate: Option<NativeInstallGatePacket>,
    /// Typed fail-closed blocker for missing or mismatched gate metadata.
    pub native_install_gate_blocker: Option<AsyncInstallGateBlockerCode>,
    /// Async state at emission time.
    pub async_state: AsyncCompileState,
    /// Stable lower-snake-case reason code.
    pub reason_code: Option<String>,
    /// Compile-service install disposition, when a response has one.
    pub install_disposition: Option<String>,
    /// Issue references governing this metadata-only packet family.
    pub issue_refs: Vec<String>,
    /// Telemetry visibility never authorizes useful-native promotion.
    pub useful_native_eligible: bool,
}

impl AsyncCompileTelemetryPacket {
    /// Return a deterministic JSON value for this packet.
    pub fn to_json_value(&self) -> Value {
        json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "event": self.event.as_str(),
            "request_id": self.request_id,
            "request_provenance": self.request_provenance,
            "generation": self.generation,
            "artifact_ref": self.artifact_ref,
            "manifest_ref": self.manifest_ref,
            "proof_ref": self.proof_ref,
            "release_ref": self.release_ref,
            "cache_key": self.cache_key,
            "cache_lookup_outcome": self.cache_lookup_outcome.map(AsyncCacheLookupOutcome::as_str),
            "native_install_gate": self.native_install_gate.as_ref().map(native_install_gate_packet_json),
            "native_install_gate_blocker": self.native_install_gate_blocker.map(AsyncInstallGateBlockerCode::as_str),
            "async_state": self.async_state.as_str(),
            "reason_code": self.reason_code,
            "install_disposition": self.install_disposition,
            "issue_refs": self.issue_refs,
            "useful_native_eligible": self.useful_native_eligible,
        })
    }

    /// Return deterministic compact JSON for this packet.
    pub fn to_json_string(&self) -> String {
        match serde_json::to_string(&self.to_json_value()) {
            Ok(output) => output,
            Err(error) => json!({
                "schema": self.schema,
                "schema_version": self.schema_version,
                "event": self.event.as_str(),
                "serialization_error": error.to_string(),
            })
            .to_string(),
        }
    }
}

/// Terminal async telemetry counters.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AsyncCompileTelemetrySummary {
    /// Accepted submit packets.
    pub submit: u64,
    /// Cancel lifecycle packets.
    pub cancel: u64,
    /// Poll lifecycle packets.
    pub poll: u64,
    /// Immediate or terminal reject packets.
    pub reject: u64,
    /// Stale-drop lifecycle packets.
    pub stale: u64,
    /// Profile-only response packets.
    pub profile_only: u64,
    /// Failed response packets.
    pub failed: u64,
    /// Compiled-response packets.
    pub compiled: u64,
    /// Useful-native promotions authorized by telemetry. Always zero in #695.
    pub useful_native: u64,
}

impl AsyncCompileTelemetrySummary {
    /// Return a deterministic JSON value for the summary.
    pub fn to_json_value(&self) -> Value {
        json!({
            "schema": ASYNC_COMPILE_TELEMETRY_SCHEMA,
            "schema_version": ASYNC_COMPILE_TELEMETRY_SCHEMA_VERSION,
            "submit": self.submit,
            "cancel": self.cancel,
            "poll": self.poll,
            "reject": self.reject,
            "stale": self.stale,
            "profile_only": self.profile_only,
            "failed": self.failed,
            "compiled": self.compiled,
            "useful_native": self.useful_native,
        })
    }

    /// Return deterministic compact JSON for this summary.
    pub fn to_json_string(&self) -> String {
        match serde_json::to_string(&self.to_json_value()) {
            Ok(output) => output,
            Err(error) => json!({
                "schema": ASYNC_COMPILE_TELEMETRY_SCHEMA,
                "schema_version": ASYNC_COMPILE_TELEMETRY_SCHEMA_VERSION,
                "serialization_error": error.to_string(),
            })
            .to_string(),
        }
    }
}

#[derive(Debug, Clone)]
struct RunningRequest {
    request: CompileRequest,
}

#[derive(Debug, Clone)]
struct TerminalRequest {
    state: AsyncCompileState,
    response: Option<CompileResponse>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AsyncCacheLookupRecord {
    key: String,
    outcome: AsyncCacheLookupOutcome,
    native_install_gate: Option<NativeInstallGatePacket>,
    native_install_gate_blocker: Option<AsyncInstallGateBlockerCode>,
    proof_tv_checksum: Option<String>,
    telemetry_checksum: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AsyncManifestCacheEntry {
    outcome: AsyncCacheLookupOutcome,
    cache_insert_gate: Option<NativeInstallGatePacket>,
    cache_hit_gate: Option<NativeInstallGatePacket>,
    native_install_gate_blocker: Option<AsyncInstallGateBlockerCode>,
    proof_tv_checksum: Option<String>,
    telemetry_checksum: Option<String>,
}

/// Runtime-neutral async compile facade.
#[derive(Debug, Clone)]
pub struct AsyncCompileService {
    service: CompileService,
    config: AsyncCompileServiceConfig,
    queued: VecDeque<CompileRequest>,
    running: HashMap<CompileRequestId, RunningRequest>,
    terminal: HashMap<CompileRequestId, TerminalRequest>,
    terminal_order: VecDeque<CompileRequestId>,
    evicted: HashSet<CompileRequestId>,
    evicted_order: VecDeque<CompileRequestId>,
    cache_entries: HashMap<String, AsyncManifestCacheEntry>,
    cache_records: HashMap<CompileRequestId, AsyncCacheLookupRecord>,
    cache_in_flight: HashMap<String, CompileRequestId>,
    native_install_gate_packets: HashMap<CompileRequestId, NativeInstallGatePacket>,
    native_install_gate_blockers: HashMap<CompileRequestId, AsyncInstallGateBlockerCode>,
    accepted_submits: usize,
    telemetry_packets: Vec<AsyncCompileTelemetryPacket>,
}

impl AsyncCompileService {
    /// Create an async facade around an existing compile service.
    pub fn new(service: CompileService, config: AsyncCompileServiceConfig) -> Self {
        Self {
            service,
            config,
            queued: VecDeque::new(),
            running: HashMap::new(),
            terminal: HashMap::new(),
            terminal_order: VecDeque::new(),
            evicted: HashSet::new(),
            evicted_order: VecDeque::new(),
            cache_entries: HashMap::new(),
            cache_records: HashMap::new(),
            cache_in_flight: HashMap::new(),
            native_install_gate_packets: HashMap::new(),
            native_install_gate_blockers: HashMap::new(),
            accepted_submits: 0,
            telemetry_packets: Vec::new(),
        }
    }

    /// Create an async facade using a default compile service.
    pub fn with_default_service(config: AsyncCompileServiceConfig) -> Self {
        Self::new(CompileService::default(), config)
    }

    /// Borrow the underlying synchronous compile service.
    pub fn service(&self) -> &CompileService {
        &self.service
    }

    /// Borrow emitted metadata-only async telemetry packets.
    pub fn telemetry_packets(&self) -> &[AsyncCompileTelemetryPacket] {
        &self.telemetry_packets
    }

    /// Return terminal metadata-only async telemetry counters.
    pub fn telemetry_summary(&self) -> AsyncCompileTelemetrySummary {
        let mut summary = AsyncCompileTelemetrySummary::default();
        for packet in &self.telemetry_packets {
            match packet.event {
                AsyncCompileTelemetryEvent::Submit => summary.submit += 1,
                AsyncCompileTelemetryEvent::Cancel => summary.cancel += 1,
                AsyncCompileTelemetryEvent::Poll => summary.poll += 1,
                AsyncCompileTelemetryEvent::ImmediateReject => summary.reject += 1,
                AsyncCompileTelemetryEvent::StaleDrop => summary.stale += 1,
                AsyncCompileTelemetryEvent::ProfileOnly => summary.profile_only += 1,
                AsyncCompileTelemetryEvent::Failed => summary.failed += 1,
                AsyncCompileTelemetryEvent::CompiledResponse => summary.compiled += 1,
                AsyncCompileTelemetryEvent::Finish => {
                    if packet.async_state == AsyncCompileState::Rejected {
                        summary.reject += 1;
                    }
                }
                AsyncCompileTelemetryEvent::Queued
                | AsyncCompileTelemetryEvent::Running
                | AsyncCompileTelemetryEvent::ExplainReject => {}
            }
        }
        summary
    }

    /// Return deterministic JSON values for all emitted telemetry packets.
    pub fn telemetry_json_values(&self) -> Vec<Value> {
        self.telemetry_packets
            .iter()
            .map(AsyncCompileTelemetryPacket::to_json_value)
            .collect()
    }

    /// Seed a manifest-keyed cache lookup outcome for async telemetry.
    ///
    /// This records cache metadata only. It does not authorize installable poll
    /// results unless a matching accepted gate packet is also recorded.
    pub fn record_manifest_cache_entry(
        &mut self,
        manifest: &ArtifactManifestV1,
        outcome: AsyncCacheLookupOutcome,
    ) {
        let native_install_gate_blocker = (outcome == AsyncCacheLookupOutcome::HitInstallable)
            .then_some(AsyncInstallGateBlockerCode::MissingGateMetadata);
        let outcome = native_install_gate_blocker
            .map(AsyncInstallGateBlockerCode::cache_outcome)
            .unwrap_or(outcome);
        self.cache_entries.insert(
            manifest_cache_key(manifest),
            AsyncManifestCacheEntry {
                outcome,
                cache_insert_gate: None,
                cache_hit_gate: None,
                native_install_gate_blocker,
                proof_tv_checksum: None,
                telemetry_checksum: None,
            },
        );
    }

    /// Seed a manifest-keyed cache lookup outcome with a native install gate packet.
    ///
    /// The packet is revalidated against the requested manifest before a
    /// `hit_installable` outcome is allowed to remain installable metadata.
    pub fn record_manifest_cache_gate_entry(
        &mut self,
        manifest: &ArtifactManifestV1,
        outcome: AsyncCacheLookupOutcome,
        native_install_gate: NativeInstallGatePacket,
    ) {
        let proof_tv_checksum = native_install_gate.validation.proof_report_sha256.clone();
        let telemetry_checksum = native_install_gate
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.event_id.clone());
        self.record_manifest_cache_gate_entry_with_identity(
            manifest,
            outcome,
            native_install_gate,
            proof_tv_checksum,
            telemetry_checksum,
        );
    }

    /// Seed a manifest-keyed cache lookup outcome with an expected native gate
    /// proof/telemetry identity.
    pub fn record_manifest_cache_gate_entry_with_identity(
        &mut self,
        manifest: &ArtifactManifestV1,
        outcome: AsyncCacheLookupOutcome,
        native_install_gate: NativeInstallGatePacket,
        proof_tv_checksum: Option<String>,
        telemetry_checksum: Option<String>,
    ) {
        if native_install_gate.surface == NativeInstallGateSurface::CacheInsert {
            self.record_manifest_cache_insert_gate_entry_with_identity(
                manifest,
                outcome,
                native_install_gate,
                proof_tv_checksum,
                telemetry_checksum,
            );
            return;
        }

        self.record_manifest_cache_hit_gate_entry_with_identity(
            manifest,
            outcome,
            native_install_gate,
            proof_tv_checksum,
            telemetry_checksum,
        );
    }

    /// Seed an installable manifest-cache insertion with a native install gate
    /// packet for the cache-insert boundary.
    pub fn record_manifest_cache_insert_gate_entry(
        &mut self,
        manifest: &ArtifactManifestV1,
        outcome: AsyncCacheLookupOutcome,
        native_install_gate: NativeInstallGatePacket,
    ) {
        let proof_tv_checksum = native_install_gate.validation.proof_report_sha256.clone();
        let telemetry_checksum = native_install_gate
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.event_id.clone());
        self.record_manifest_cache_insert_gate_entry_with_identity(
            manifest,
            outcome,
            native_install_gate,
            proof_tv_checksum,
            telemetry_checksum,
        );
    }

    /// Seed an installable manifest-cache insertion with an expected native
    /// gate proof/telemetry identity.
    pub fn record_manifest_cache_insert_gate_entry_with_identity(
        &mut self,
        manifest: &ArtifactManifestV1,
        outcome: AsyncCacheLookupOutcome,
        native_install_gate: NativeInstallGatePacket,
        proof_tv_checksum: Option<String>,
        telemetry_checksum: Option<String>,
    ) {
        let key = manifest_cache_key(manifest);
        let existing_hit_gate = self
            .cache_entries
            .get(&key)
            .and_then(|entry| entry.cache_hit_gate.clone());
        let native_install_gate_blocker = cache_insert_gate_blocker(
            manifest,
            outcome,
            Some(&native_install_gate),
            proof_tv_checksum.as_deref(),
            telemetry_checksum.as_deref(),
        );
        let outcome = native_install_gate_blocker
            .map(AsyncInstallGateBlockerCode::cache_outcome)
            .unwrap_or(outcome);
        self.cache_entries.insert(
            key,
            AsyncManifestCacheEntry {
                outcome,
                cache_insert_gate: Some(native_install_gate),
                cache_hit_gate: native_install_gate_blocker
                    .is_none()
                    .then_some(existing_hit_gate)
                    .flatten(),
                native_install_gate_blocker,
                proof_tv_checksum,
                telemetry_checksum,
            },
        );
    }

    /// Preserve a native install gate packet for a request id.
    ///
    /// The async facade also extracts packets from completed compile responses;
    /// this hook remains available for integrations that already materialize
    /// the gate decision before worker completion.
    pub fn record_native_install_gate_packet(
        &mut self,
        request_id: CompileRequestId,
        native_install_gate: NativeInstallGatePacket,
    ) {
        self.native_install_gate_packets
            .insert(request_id, native_install_gate);
    }

    fn record_manifest_cache_hit_gate_entry_with_identity(
        &mut self,
        manifest: &ArtifactManifestV1,
        outcome: AsyncCacheLookupOutcome,
        native_install_gate: NativeInstallGatePacket,
        proof_tv_checksum: Option<String>,
        telemetry_checksum: Option<String>,
    ) {
        let key = manifest_cache_key(manifest);
        let mut entry = self
            .cache_entries
            .get(&key)
            .cloned()
            .unwrap_or(AsyncManifestCacheEntry {
                outcome,
                cache_insert_gate: None,
                cache_hit_gate: None,
                native_install_gate_blocker: (outcome == AsyncCacheLookupOutcome::HitInstallable)
                    .then_some(AsyncInstallGateBlockerCode::MissingGateMetadata),
                proof_tv_checksum: None,
                telemetry_checksum: None,
            });

        if outcome == AsyncCacheLookupOutcome::HitInstallable {
            if entry.native_install_gate_blocker.is_none()
                && entry.outcome == AsyncCacheLookupOutcome::HitInstallable
                && entry.cache_insert_gate.is_some()
            {
                entry.cache_hit_gate = Some(native_install_gate);
                entry.proof_tv_checksum = proof_tv_checksum;
                entry.telemetry_checksum = telemetry_checksum;
            } else if entry.native_install_gate_blocker.is_some() {
                entry.cache_hit_gate = Some(native_install_gate);
            } else {
                entry.outcome = AsyncCacheLookupOutcome::GateMetadataMissing;
                entry.cache_hit_gate = Some(native_install_gate);
                entry.native_install_gate_blocker =
                    Some(AsyncInstallGateBlockerCode::MissingGateMetadata);
                entry.proof_tv_checksum = proof_tv_checksum;
                entry.telemetry_checksum = telemetry_checksum;
            }
        } else {
            entry.outcome = outcome;
            entry.cache_hit_gate = Some(native_install_gate);
            entry.native_install_gate_blocker = None;
            entry.proof_tv_checksum = proof_tv_checksum;
            entry.telemetry_checksum = telemetry_checksum;
        }

        self.cache_entries.insert(key, entry);
    }

    /// Submit a request for later worker execution.
    pub fn submit(
        &mut self,
        request: CompileRequest,
    ) -> Result<AsyncSubmitAccepted, AsyncSubmitReject> {
        let cache_record = self.cache_lookup_record(&request);
        if let Some(code) = self.submit_reject_code(&request, cache_record.as_ref()) {
            let duplicate_active_request = code == AsyncSubmitRejectCode::DuplicateRequest
                && self.has_active_request_id(&request.request_id);
            if let Some(record) = cache_record.clone().filter(|_| !duplicate_active_request) {
                self.cache_records
                    .insert(request.request_id.clone(), record);
            }
            let reject = self.submit_reject(request, code);
            self.record_response_event_with_cache_record(
                AsyncCompileTelemetryEvent::Submit,
                &reject.response,
                reject.state,
                Some(reject.code.as_str()),
                cache_record.as_ref(),
            );
            self.record_response_event_with_cache_record(
                AsyncCompileTelemetryEvent::ImmediateReject,
                &reject.response,
                reject.state,
                Some(reject.code.as_str()),
                cache_record.as_ref(),
            );
            if !duplicate_active_request
                && (!matches!(
                    code,
                    AsyncSubmitRejectCode::DuplicateRequest
                        | AsyncSubmitRejectCode::DuplicateCacheKey
                ) || !self.terminal.contains_key(&reject.request_id))
            {
                self.insert_terminal(
                    reject.request_id.clone(),
                    reject.state,
                    Some(reject.response.clone()),
                );
            }
            return Err(reject);
        }

        let request_id = request.request_id.clone();
        let generation = request.generation;
        if let Some(record) = cache_record {
            self.cache_in_flight
                .insert(record.key.clone(), request_id.clone());
            self.cache_records.insert(request_id.clone(), record);
        }
        self.record_request_event(
            AsyncCompileTelemetryEvent::Submit,
            &request_id,
            Some(generation),
            AsyncCompileState::Queued,
            None,
            None,
            None,
        );
        self.record_request_event(
            AsyncCompileTelemetryEvent::Queued,
            &request_id,
            Some(generation),
            AsyncCompileState::Queued,
            None,
            None,
            None,
        );
        self.queued.push_back(request);
        self.accepted_submits += 1;
        Ok(AsyncSubmitAccepted {
            request_id,
            state: AsyncCompileState::Queued,
        })
    }

    /// Cancel a queued or running request.
    pub fn cancel(&mut self, request_id: &CompileRequestId) -> AsyncCompilePoll {
        if let Some(position) = self
            .queued
            .iter()
            .position(|request| request.request_id == *request_id)
        {
            let request = self
                .queued
                .remove(position)
                .expect("queued position exists");
            request.cancellation.cancel();
            let response = terminal_response(
                &request,
                CompileStatus::Cancelled,
                "async.cancelled",
                "async compile request cancelled while queued",
                "async_compile.cancel_queued",
            );
            self.insert_terminal(
                request_id.clone(),
                AsyncCompileState::Cancelled,
                Some(response.clone()),
            );
            self.record_response_event(
                AsyncCompileTelemetryEvent::Cancel,
                &response,
                AsyncCompileState::Cancelled,
                Some("cancelled"),
            );
            let poll = AsyncCompilePoll {
                request_id: request_id.clone(),
                state: AsyncCompileState::Cancelled,
                response: Some(response),
            };
            return poll;
        }

        if let Some(running) = self.running.remove(request_id) {
            running.request.cancellation.cancel();
            let response = terminal_response(
                &running.request,
                CompileStatus::Cancelled,
                "async.cancelled",
                "async compile request cancelled while running",
                "async_compile.cancel_running",
            );
            self.insert_terminal(
                request_id.clone(),
                AsyncCompileState::Cancelled,
                Some(response.clone()),
            );
            self.record_response_event(
                AsyncCompileTelemetryEvent::Cancel,
                &response,
                AsyncCompileState::Cancelled,
                Some("cancelled"),
            );
            let poll = AsyncCompilePoll {
                request_id: request_id.clone(),
                state: AsyncCompileState::Cancelled,
                response: Some(response),
            };
            return poll;
        }

        self.poll(request_id)
    }

    /// Poll the current state for a request id.
    pub fn poll(&mut self, request_id: &CompileRequestId) -> AsyncCompilePoll {
        if let Some(position) = self
            .queued
            .iter()
            .position(|request| request.request_id == *request_id)
        {
            let request = &self.queued[position];
            if request.cancellation.is_cancelled() || request_is_stale(request) {
                let request = self
                    .queued
                    .remove(position)
                    .expect("queued position exists");
                let (status, state, code, message) = if request.cancellation.is_cancelled() {
                    (
                        CompileStatus::Cancelled,
                        AsyncCompileState::Cancelled,
                        "async.cancelled",
                        "async compile request cancelled while queued",
                    )
                } else {
                    (
                        CompileStatus::Stale,
                        AsyncCompileState::StaleGeneration,
                        "async.stale_generation",
                        "async compile request stale while queued",
                    )
                };
                let response =
                    terminal_response(&request, status, code, message, "async_compile.poll");
                self.insert_terminal(request_id.clone(), state, Some(response.clone()));
                self.record_response_event(
                    if state == AsyncCompileState::StaleGeneration {
                        AsyncCompileTelemetryEvent::StaleDrop
                    } else {
                        AsyncCompileTelemetryEvent::Cancel
                    },
                    &response,
                    state,
                    Some(if state == AsyncCompileState::StaleGeneration {
                        "stale_generation"
                    } else {
                        "cancelled"
                    }),
                );
                let poll = AsyncCompilePoll {
                    request_id: request_id.clone(),
                    state,
                    response: Some(response),
                };
                self.record_poll_event(&poll);
                return poll;
            }
            let poll = AsyncCompilePoll {
                request_id: request_id.clone(),
                state: AsyncCompileState::Queued,
                response: None,
            };
            self.record_poll_event(&poll);
            return poll;
        }

        if let Some(running) = self.running.get(request_id) {
            if running.request.cancellation.is_cancelled() || request_is_stale(&running.request) {
                let running = self
                    .running
                    .remove(request_id)
                    .expect("running request exists");
                let (status, state, code, message) = if running.request.cancellation.is_cancelled()
                {
                    (
                        CompileStatus::Cancelled,
                        AsyncCompileState::Cancelled,
                        "async.cancelled",
                        "async compile request cancelled while running",
                    )
                } else {
                    (
                        CompileStatus::Stale,
                        AsyncCompileState::StaleGeneration,
                        "async.stale_generation",
                        "async compile request stale while running",
                    )
                };
                let response = terminal_response(
                    &running.request,
                    status,
                    code,
                    message,
                    "async_compile.poll",
                );
                self.insert_terminal(request_id.clone(), state, Some(response.clone()));
                self.record_response_event(
                    if state == AsyncCompileState::StaleGeneration {
                        AsyncCompileTelemetryEvent::StaleDrop
                    } else {
                        AsyncCompileTelemetryEvent::Cancel
                    },
                    &response,
                    state,
                    Some(if state == AsyncCompileState::StaleGeneration {
                        "stale_generation"
                    } else {
                        "cancelled"
                    }),
                );
                let poll = AsyncCompilePoll {
                    request_id: request_id.clone(),
                    state,
                    response: Some(response),
                };
                self.record_poll_event(&poll);
                return poll;
            } else {
                let poll = AsyncCompilePoll {
                    request_id: request_id.clone(),
                    state: AsyncCompileState::Running,
                    response: None,
                };
                self.record_poll_event(&poll);
                return poll;
            }
        }

        if let Some(terminal) = self.terminal.get(request_id) {
            let poll = AsyncCompilePoll {
                request_id: request_id.clone(),
                state: terminal.state,
                response: terminal.response.clone(),
            };
            self.record_poll_event(&poll);
            return poll;
        }

        if self.evicted.contains(request_id) {
            let poll = AsyncCompilePoll {
                request_id: request_id.clone(),
                state: AsyncCompileState::Evicted,
                response: None,
            };
            self.record_poll_event(&poll);
            return poll;
        }

        let poll = AsyncCompilePoll {
            request_id: request_id.clone(),
            state: AsyncCompileState::NotFound,
            response: None,
        };
        self.record_poll_event(&poll);
        poll
    }

    /// Start the next queued request and return a worker ticket.
    pub fn start_next(&mut self) -> Option<AsyncCompileTicket> {
        while let Some(request) = self.queued.pop_front() {
            if request.cancellation.is_cancelled() {
                let response = terminal_response(
                    &request,
                    CompileStatus::Cancelled,
                    "async.cancelled",
                    "async compile request cancelled before start",
                    "async_compile.start_next",
                );
                self.insert_terminal(
                    request.request_id.clone(),
                    AsyncCompileState::Cancelled,
                    Some(response.clone()),
                );
                self.record_response_event(
                    AsyncCompileTelemetryEvent::Cancel,
                    &response,
                    AsyncCompileState::Cancelled,
                    Some("cancelled"),
                );
                continue;
            }

            if request_is_stale(&request) {
                let response = terminal_response(
                    &request,
                    CompileStatus::Stale,
                    "async.stale_generation",
                    "async compile request stale before start",
                    "async_compile.start_next",
                );
                self.insert_terminal(
                    request.request_id.clone(),
                    AsyncCompileState::StaleGeneration,
                    Some(response.clone()),
                );
                self.record_response_event(
                    AsyncCompileTelemetryEvent::StaleDrop,
                    &response,
                    AsyncCompileState::StaleGeneration,
                    Some("stale_generation"),
                );
                continue;
            }

            let request_id = request.request_id.clone();
            let generation = request.generation;
            self.running.insert(
                request_id.clone(),
                RunningRequest {
                    request: request.clone(),
                },
            );
            self.record_request_event(
                AsyncCompileTelemetryEvent::Running,
                &request_id,
                Some(generation),
                AsyncCompileState::Running,
                None,
                None,
                None,
            );
            return Some(AsyncCompileTicket {
                request_id,
                generation,
                request,
            });
        }

        None
    }

    /// Finish a running request and publish a non-installable result if the
    /// request became cancelled or stale while backend work was running.
    pub fn finish(
        &mut self,
        ticket: AsyncCompileTicket,
        response: CompileResponse,
    ) -> AsyncCompilePoll {
        let Some(running) = self.running.remove(&ticket.request_id) else {
            return self.poll(&ticket.request_id);
        };

        let (mut state, mut response) = if running.request.cancellation.is_cancelled() {
            (
                AsyncCompileState::Cancelled,
                terminal_response(
                    &running.request,
                    CompileStatus::Cancelled,
                    "async.cancelled",
                    "async compile request cancelled before publish",
                    "async_compile.finish",
                ),
            )
        } else if request_is_stale(&running.request) {
            (
                AsyncCompileState::StaleGeneration,
                terminal_response(
                    &running.request,
                    CompileStatus::Stale,
                    "async.stale_generation",
                    "async compile request stale before publish",
                    "async_compile.finish",
                ),
            )
        } else {
            (state_for_response(&response), response)
        };
        let native_install_gate_blocker = if state == AsyncCompileState::CompiledInstallable {
            let response_native_install_gate = response_native_install_gate_packet(&response);
            let native_install_gate = response_native_install_gate.clone().or_else(|| {
                self.native_install_gate_packets
                    .get(&ticket.request_id)
                    .cloned()
            });
            if let Some(packet) = native_install_gate.clone() {
                attach_async_poll_gate_packet(&mut response, packet.clone());
                self.native_install_gate_packets
                    .insert(ticket.request_id.clone(), packet);
            }
            let blocker = response_gate_blocker(state, &response, native_install_gate.as_ref());
            if let Some(blocker) = blocker {
                self.native_install_gate_blockers
                    .insert(ticket.request_id.clone(), blocker);
                response = gate_blocked_response(response, blocker);
                state = AsyncCompileState::Rejected;
            }
            blocker
        } else {
            None
        };

        self.insert_terminal(ticket.request_id.clone(), state, Some(response.clone()));
        let finish_reason = native_install_gate_blocker
            .map(AsyncInstallGateBlockerCode::as_str)
            .or_else(|| terminal_reason_code(state, &response));
        self.record_response_event(
            AsyncCompileTelemetryEvent::Finish,
            &response,
            state,
            finish_reason,
        );
        match state {
            AsyncCompileState::CompiledInstallable => self.record_response_event(
                AsyncCompileTelemetryEvent::CompiledResponse,
                &response,
                state,
                Some("compiled"),
            ),
            AsyncCompileState::ProfileOnly => self.record_response_event(
                AsyncCompileTelemetryEvent::ProfileOnly,
                &response,
                state,
                Some("profile_only"),
            ),
            AsyncCompileState::Failed => self.record_response_event(
                AsyncCompileTelemetryEvent::Failed,
                &response,
                state,
                Some("failed"),
            ),
            AsyncCompileState::StaleGeneration => self.record_response_event(
                AsyncCompileTelemetryEvent::StaleDrop,
                &response,
                state,
                Some("stale_generation"),
            ),
            AsyncCompileState::Cancelled => self.record_response_event(
                AsyncCompileTelemetryEvent::Cancel,
                &response,
                state,
                Some("cancelled"),
            ),
            AsyncCompileState::Rejected
            | AsyncCompileState::Queued
            | AsyncCompileState::Running
            | AsyncCompileState::Evicted
            | AsyncCompileState::NotFound => {}
        }
        AsyncCompilePoll {
            request_id: ticket.request_id,
            state,
            response: Some(response),
        }
    }

    /// Convenience synchronous worker hook for tests and simple integrations.
    pub fn run_next_with<F>(&mut self, compile: F) -> Option<AsyncCompilePoll>
    where
        F: FnOnce(&CompileService, CompileRequest) -> CompileResponse,
    {
        let ticket = self.start_next()?;
        let response = compile(&self.service, ticket.request.clone());
        Some(self.finish(ticket, response))
    }

    /// Explain a terminal non-installable async state.
    pub fn explain_reject(&mut self, request_id: &CompileRequestId) -> Option<ExplainReject> {
        let poll = self.poll(request_id);
        let response = poll.response?;
        let explanation = response
            .explain_reject()
            .or_else(|| async_reject_explanation(&response));
        if let Some(explanation) = &explanation {
            self.record_response_event(
                AsyncCompileTelemetryEvent::ExplainReject,
                &response,
                poll.state,
                Some(explanation.code.as_str()),
            );
        }
        explanation
    }

    fn submit_reject_code(
        &self,
        request: &CompileRequest,
        cache_record: Option<&AsyncCacheLookupRecord>,
    ) -> Option<AsyncSubmitRejectCode> {
        if self.has_request_id(&request.request_id) {
            return Some(AsyncSubmitRejectCode::DuplicateRequest);
        }
        if request.cancellation.is_cancelled() {
            return Some(AsyncSubmitRejectCode::Cancelled);
        }
        if request_is_stale(request) {
            return Some(AsyncSubmitRejectCode::StaleGeneration);
        }
        if cache_record.is_some_and(|record| self.cache_in_flight.contains_key(&record.key)) {
            return Some(AsyncSubmitRejectCode::DuplicateCacheKey);
        }
        if self.queued.len() >= self.config.max_queued {
            return Some(AsyncSubmitRejectCode::QueueFull);
        }
        if self
            .config
            .max_total_submitted
            .is_some_and(|budget| self.accepted_submits >= budget)
        {
            return Some(AsyncSubmitRejectCode::BudgetExceeded);
        }
        None
    }

    fn cache_lookup_record(&self, request: &CompileRequest) -> Option<AsyncCacheLookupRecord> {
        let manifest = request.artifact_manifest.as_ref()?;
        let key = manifest_cache_key(manifest);
        let entry = self
            .cache_entries
            .get(&key)
            .cloned()
            .unwrap_or(AsyncManifestCacheEntry {
                outcome: AsyncCacheLookupOutcome::Miss,
                cache_insert_gate: None,
                cache_hit_gate: None,
                native_install_gate_blocker: None,
                proof_tv_checksum: None,
                telemetry_checksum: None,
            });
        let insert_blocker = if entry.outcome == AsyncCacheLookupOutcome::HitInstallable
            && entry.cache_insert_gate.is_none()
            && entry.native_install_gate_blocker.is_none()
        {
            Some(AsyncInstallGateBlockerCode::MissingGateMetadata)
        } else {
            entry.native_install_gate_blocker
        };
        let native_install_gate_blocker = insert_blocker.or_else(|| {
            cache_hit_gate_blocker(
                manifest,
                entry.outcome,
                entry.cache_hit_gate.as_ref(),
                entry.proof_tv_checksum.as_deref(),
                entry.telemetry_checksum.as_deref(),
            )
        });
        let native_install_gate = if insert_blocker.is_some() {
            entry.cache_insert_gate
        } else {
            entry.cache_hit_gate
        };
        let outcome = native_install_gate_blocker
            .map(AsyncInstallGateBlockerCode::cache_outcome)
            .unwrap_or(entry.outcome);
        Some(AsyncCacheLookupRecord {
            key,
            outcome,
            native_install_gate,
            native_install_gate_blocker,
            proof_tv_checksum: entry.proof_tv_checksum,
            telemetry_checksum: entry.telemetry_checksum,
        })
    }

    fn has_request_id(&self, request_id: &CompileRequestId) -> bool {
        self.has_active_request_id(request_id) || self.terminal.contains_key(request_id)
    }

    fn has_active_request_id(&self, request_id: &CompileRequestId) -> bool {
        self.queued
            .iter()
            .any(|request| request.request_id == *request_id)
            || self.running.contains_key(request_id)
    }

    fn submit_reject(
        &self,
        request: CompileRequest,
        code: AsyncSubmitRejectCode,
    ) -> AsyncSubmitReject {
        let state = code.state();
        let response = terminal_response(
            &request,
            code.compile_status(),
            submit_diagnostic_code(code),
            submit_diagnostic_message(code),
            "async_compile.submit",
        );
        AsyncSubmitReject {
            request_id: request.request_id,
            code,
            state,
            response,
        }
    }

    fn insert_terminal(
        &mut self,
        request_id: CompileRequestId,
        state: AsyncCompileState,
        response: Option<CompileResponse>,
    ) {
        if let Some(record) = self.cache_records.get(&request_id)
            && self.cache_in_flight.get(&record.key) == Some(&request_id)
        {
            self.cache_in_flight.remove(&record.key);
        }
        if !self.terminal.contains_key(&request_id) {
            self.terminal_order.push_back(request_id.clone());
        }
        self.terminal
            .insert(request_id.clone(), TerminalRequest { state, response });

        while self.terminal.len() > self.config.max_terminal_retained {
            let Some(evicted_id) = self.terminal_order.pop_front() else {
                break;
            };
            if self.terminal.remove(&evicted_id).is_some() {
                self.cache_records.remove(&evicted_id);
                self.native_install_gate_packets.remove(&evicted_id);
                self.native_install_gate_blockers.remove(&evicted_id);
                self.remember_evicted(evicted_id);
            }
        }
    }

    fn remember_evicted(&mut self, request_id: CompileRequestId) {
        if self.evicted.insert(request_id.clone()) {
            self.evicted_order.push_back(request_id);
        }
        while self.evicted.len() > self.config.max_evicted_retained {
            let Some(evicted_id) = self.evicted_order.pop_front() else {
                break;
            };
            self.evicted.remove(&evicted_id);
        }
    }

    fn record_poll_event(&mut self, poll: &AsyncCompilePoll) {
        self.record_request_event(
            AsyncCompileTelemetryEvent::Poll,
            &poll.request_id,
            poll.response.as_ref().map(|response| response.generation),
            poll.state,
            poll.response
                .as_ref()
                .and_then(|response| terminal_reason_code(poll.state, response)),
            poll.response.as_ref(),
            None,
        );
    }

    fn record_response_event(
        &mut self,
        event: AsyncCompileTelemetryEvent,
        response: &CompileResponse,
        state: AsyncCompileState,
        reason_code: Option<&str>,
    ) {
        self.record_response_event_with_cache_record(event, response, state, reason_code, None);
    }

    fn record_response_event_with_cache_record(
        &mut self,
        event: AsyncCompileTelemetryEvent,
        response: &CompileResponse,
        state: AsyncCompileState,
        reason_code: Option<&str>,
        cache_record: Option<&AsyncCacheLookupRecord>,
    ) {
        self.record_request_event(
            event,
            &response.request_id,
            Some(response.generation),
            state,
            reason_code.or_else(|| terminal_reason_code(state, response)),
            Some(response),
            cache_record,
        );
    }

    fn record_request_event(
        &mut self,
        event: AsyncCompileTelemetryEvent,
        request_id: &CompileRequestId,
        generation: Option<CompileGeneration>,
        async_state: AsyncCompileState,
        reason_code: Option<&str>,
        response: Option<&CompileResponse>,
        cache_record: Option<&AsyncCacheLookupRecord>,
    ) {
        let artifact = response.and_then(|response| response.artifact.as_ref());
        let artifact_ref = artifact.map(|artifact| artifact.identity.as_str().to_owned());
        let manifest_ref = artifact.and_then(telemetry_manifest_ref);
        let proof_ref = artifact.and_then(telemetry_proof_ref);
        let cache_record = cache_record.or_else(|| self.cache_records.get(request_id));
        let cache_key = cache_record.map(|record| record.key.clone());
        let cache_lookup_outcome = cache_record.map(|record| record.outcome);
        let response_native_install_gate = response.and_then(response_native_install_gate_packet);
        let native_install_gate = response_native_install_gate
            .or_else(|| cache_record.and_then(|record| record.native_install_gate.clone()))
            .or_else(|| self.native_install_gate_packets.get(request_id).cloned());
        let native_install_gate_blocker = cache_record
            .and_then(|record| record.native_install_gate_blocker)
            .or_else(|| self.native_install_gate_blockers.get(request_id).copied())
            .or_else(|| {
                response.and_then(|response| {
                    response_gate_blocker(async_state, response, native_install_gate.as_ref())
                })
            });
        let install_disposition = artifact
            .map(|artifact| artifact.install.disposition.as_str())
            .or_else(|| response.map(|response| response.disposition.as_str()));

        self.telemetry_packets.push(AsyncCompileTelemetryPacket {
            schema: ASYNC_COMPILE_TELEMETRY_SCHEMA,
            schema_version: ASYNC_COMPILE_TELEMETRY_SCHEMA_VERSION,
            event,
            request_id: request_id.as_str().to_owned(),
            request_provenance: request_id.as_str().to_owned(),
            generation: generation.map(CompileGeneration::get),
            artifact_ref,
            manifest_ref,
            proof_ref,
            release_ref: None,
            cache_key,
            cache_lookup_outcome,
            native_install_gate,
            native_install_gate_blocker,
            async_state,
            reason_code: reason_code.map(str::to_owned),
            install_disposition: install_disposition.map(str::to_owned),
            issue_refs: vec![
                "#695".to_owned(),
                "#707".to_owned(),
                "#681".to_owned(),
                "#721".to_owned(),
            ],
            useful_native_eligible: false,
        });
    }
}

impl Default for AsyncCompileService {
    fn default() -> Self {
        Self::with_default_service(AsyncCompileServiceConfig::default())
    }
}

fn state_for_response(response: &CompileResponse) -> AsyncCompileState {
    match response.status {
        CompileStatus::Compiled => response
            .artifact
            .as_ref()
            .map(|artifact| match artifact.install.disposition {
                ArtifactInstallDisposition::Installable => AsyncCompileState::CompiledInstallable,
                ArtifactInstallDisposition::ProfileOnly => AsyncCompileState::ProfileOnly,
                ArtifactInstallDisposition::Rejected => AsyncCompileState::Rejected,
            })
            .unwrap_or(AsyncCompileState::Rejected),
        CompileStatus::Cancelled => AsyncCompileState::Cancelled,
        CompileStatus::Stale => AsyncCompileState::StaleGeneration,
        CompileStatus::Rejected => AsyncCompileState::Rejected,
        CompileStatus::Failed => AsyncCompileState::Failed,
    }
}

fn async_poll_response_gate_packet(response: &CompileResponse) -> Option<NativeInstallGatePacket> {
    response.native_install_gate_packet_for_surface(NativeInstallGateSurface::AsyncPoll)
}

fn response_native_install_gate_packet(
    response: &CompileResponse,
) -> Option<NativeInstallGatePacket> {
    response
        .artifact
        .as_ref()
        .and_then(|artifact| artifact.install.native_install_gate.clone())
        .or_else(|| async_poll_response_gate_packet(response))
}

fn attach_async_poll_gate_packet(response: &mut CompileResponse, packet: NativeInstallGatePacket) {
    if let Some(artifact) = response.artifact.as_mut() {
        artifact.install.native_install_gate = Some(packet);
    }
}

fn gate_blocked_response(
    mut response: CompileResponse,
    blocker: AsyncInstallGateBlockerCode,
) -> CompileResponse {
    response.disposition = ArtifactInstallDisposition::Rejected;
    if let Some(artifact) = response.artifact.as_mut() {
        artifact.install.disposition = ArtifactInstallDisposition::Rejected;
    }
    response.diagnostics.push(CompileDiagnostic {
        severity: DiagnosticSeverity::Error,
        code: blocker.diagnostic_code(),
        message: blocker.diagnostic_message().to_owned(),
        function: None,
        phase: Some("async_compile.native_install_gate".to_owned()),
        backend_error: None,
    });
    response
}

fn response_gate_blocker(
    state: AsyncCompileState,
    response: &CompileResponse,
    native_install_gate: Option<&NativeInstallGatePacket>,
) -> Option<AsyncInstallGateBlockerCode> {
    if state != AsyncCompileState::CompiledInstallable {
        return None;
    }
    let Some(packet) = native_install_gate else {
        return Some(AsyncInstallGateBlockerCode::MissingGateMetadata);
    };
    if !response_matches_gate_packet(response, packet, NativeInstallGateSurface::AsyncPoll) {
        return Some(AsyncInstallGateBlockerCode::GateMetadataMismatch);
    }
    let current = response_gate_revalidation_input(response, packet);
    let verdict = validate_native_install_gate_packet_with_current(
        packet,
        Some(packet.packet_hash),
        &current,
    );
    if !verdict.disposition.is_installable() || verdict.rejection_code.is_some() {
        return Some(AsyncInstallGateBlockerCode::GateRejected);
    }
    None
}

fn response_gate_revalidation_input(
    response: &CompileResponse,
    packet: &NativeInstallGatePacket,
) -> NativeInstallGateRevalidationInput {
    response
        .artifact
        .as_ref()
        .and_then(|artifact| artifact.artifact_manifest.as_ref())
        .map(NativeInstallGateRevalidationInput::from_manifest)
        .unwrap_or_else(|| NativeInstallGateRevalidationInput::from_packet(packet))
}

fn response_matches_gate_packet(
    response: &CompileResponse,
    packet: &NativeInstallGatePacket,
    surface: NativeInstallGateSurface,
) -> bool {
    if !gate_packet_schema_and_surface_match(packet, surface) {
        return false;
    }
    let Some(artifact) = response.artifact.as_ref() else {
        return false;
    };
    if let Some(reference) = artifact.install.artifact_manifest.as_ref() {
        return packet.artifact.artifact_id == reference.artifact_id
            && packet.artifact.manifest_checksum == reference.manifest_checksum
            && packet.artifact.target_checksum == reference.target_checksum
            && packet.artifact.abi_checksum == reference.abi_checksum
            && packet.artifact.layout_checksum == reference.layout_checksum
            && packet.artifact.proof_policy_checksum == reference.proof_policy_checksum
            && packet.artifact.invalidation_checksum == reference.invalidation_checksum;
    }
    artifact
        .artifact_manifest
        .as_ref()
        .is_some_and(|manifest| gate_packet_matches_manifest(packet, manifest, surface))
}

fn cache_insert_gate_blocker(
    manifest: &ArtifactManifestV1,
    outcome: AsyncCacheLookupOutcome,
    native_install_gate: Option<&NativeInstallGatePacket>,
    proof_tv_checksum: Option<&str>,
    telemetry_checksum: Option<&str>,
) -> Option<AsyncInstallGateBlockerCode> {
    cache_surface_gate_blocker(
        manifest,
        outcome,
        native_install_gate,
        proof_tv_checksum,
        telemetry_checksum,
        NativeInstallGateSurface::CacheInsert,
    )
}

fn cache_hit_gate_blocker(
    manifest: &ArtifactManifestV1,
    outcome: AsyncCacheLookupOutcome,
    native_install_gate: Option<&NativeInstallGatePacket>,
    proof_tv_checksum: Option<&str>,
    telemetry_checksum: Option<&str>,
) -> Option<AsyncInstallGateBlockerCode> {
    cache_surface_gate_blocker(
        manifest,
        outcome,
        native_install_gate,
        proof_tv_checksum,
        telemetry_checksum,
        NativeInstallGateSurface::CacheHit,
    )
}

fn cache_surface_gate_blocker(
    manifest: &ArtifactManifestV1,
    outcome: AsyncCacheLookupOutcome,
    native_install_gate: Option<&NativeInstallGatePacket>,
    proof_tv_checksum: Option<&str>,
    telemetry_checksum: Option<&str>,
    surface: NativeInstallGateSurface,
) -> Option<AsyncInstallGateBlockerCode> {
    if outcome != AsyncCacheLookupOutcome::HitInstallable {
        return None;
    }
    let Some(packet) = native_install_gate else {
        return Some(AsyncInstallGateBlockerCode::MissingGateMetadata);
    };
    if !gate_packet_matches_manifest(packet, manifest, surface) {
        return Some(AsyncInstallGateBlockerCode::GateMetadataMismatch);
    }
    if !gate_packet_matches_cache_identity(packet, proof_tv_checksum, telemetry_checksum) {
        return Some(AsyncInstallGateBlockerCode::GateMetadataMismatch);
    }
    let current = NativeInstallGateRevalidationInput::from_manifest(manifest);
    let verdict = validate_native_install_gate_packet_with_current(
        packet,
        Some(packet.packet_hash),
        &current,
    );
    if !verdict.disposition.is_installable()
        || verdict.rejection_code.is_some()
        || !cache_surface_authorized(&verdict, surface)
    {
        return Some(AsyncInstallGateBlockerCode::GateRejected);
    }
    None
}

fn cache_surface_authorized(
    verdict: &NativeInstallGateVerdict,
    surface: NativeInstallGateSurface,
) -> bool {
    match surface {
        NativeInstallGateSurface::CacheInsert => verdict.actions.insert_installable_cache,
        NativeInstallGateSurface::CacheHit => verdict.actions.accept_installable_cache_hit,
        _ => false,
    }
}

fn gate_packet_matches_cache_identity(
    packet: &NativeInstallGatePacket,
    proof_tv_checksum: Option<&str>,
    telemetry_checksum: Option<&str>,
) -> bool {
    let (Some(proof_tv_checksum), Some(telemetry_checksum)) =
        (proof_tv_checksum, telemetry_checksum)
    else {
        return false;
    };
    packet.validation.proof_report_sha256.as_deref() == Some(proof_tv_checksum)
        && packet
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.event_id.as_str())
            == Some(telemetry_checksum)
}

fn gate_packet_matches_manifest(
    packet: &NativeInstallGatePacket,
    manifest: &ArtifactManifestV1,
    surface: NativeInstallGateSurface,
) -> bool {
    gate_packet_schema_and_surface_match(packet, surface)
        && packet.artifact.artifact_id == manifest.artifact_id
        && packet.artifact.manifest_checksum == manifest.checksum()
        && packet.artifact.target_checksum == manifest.target.checksum()
        && packet.artifact.abi_checksum == manifest.abi.checksum()
        && packet.artifact.layout_checksum == manifest.layout.checksum()
        && packet.artifact.proof_policy_checksum == manifest.proof_policy.checksum()
        && packet.artifact.invalidation_checksum == manifest.invalidation.checksum()
}

fn gate_packet_schema_and_surface_match(
    packet: &NativeInstallGatePacket,
    surface: NativeInstallGateSurface,
) -> bool {
    packet.schema == NATIVE_INSTALL_GATE_PACKET_SCHEMA
        && packet.schema_version == NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION
        && packet.surface == surface
}

fn native_install_gate_packet_json(packet: &NativeInstallGatePacket) -> Value {
    json!({
        "schema": packet.schema,
        "schema_version": packet.schema_version,
        "gate_issue": packet.gate_issue,
        "design_issue": packet.design_issue,
        "consumer": packet.consumer,
        "consumer_mode": packet.consumer_mode,
        "surface": packet.surface.as_str(),
        "disposition": packet.disposition.as_str(),
        "rejection_code": packet.rejection_code.map(NativeInstallGateRejectionCode::as_str),
        "packet_hash": packet.packet_hash.to_string(),
        "install_authority": packet.install_authority.as_str(),
        "requested_authority": packet.requested_authority.as_str(),
        "artifact": {
            "artifact_id": packet.artifact.artifact_id,
            "manifest_schema": packet.artifact.manifest_schema,
            "manifest_schema_version": packet.artifact.manifest_schema_version,
            "manifest_checksum": packet.artifact.manifest_checksum.to_string(),
            "source_sha256": packet.artifact.source_sha256,
            "trust_ir_sha256": packet.artifact.trust_ir_sha256,
            "native_payload_sha256": packet.artifact.native_payload_sha256,
            "target_checksum": packet.artifact.target_checksum.to_string(),
            "abi_checksum": packet.artifact.abi_checksum.to_string(),
            "layout_checksum": packet.artifact.layout_checksum.to_string(),
            "proof_policy_checksum": packet.artifact.proof_policy_checksum.to_string(),
            "invalidation_checksum": packet.artifact.invalidation_checksum.to_string(),
        },
        "validation": {
            "layout_status": packet.validation.layout_status,
            "layout_evidence_sha256": packet.validation.layout_evidence_sha256,
            "layout_wrapper_identity": packet.validation.layout_wrapper_identity,
            "layout_validation_provenance": packet.validation.layout_validation_provenance,
            "layout_invalidation_checksum": packet.validation.layout_invalidation_checksum.map(|checksum| checksum.to_string()),
            "layout_generation_domains": packet.validation.layout_generation_domains,
            "proof_verdict": packet.validation.proof_verdict,
            "proof_reject_code": packet.validation.proof_reject_code,
            "proof_tv_checksum": packet.validation.proof_report_sha256,
            "proof_verifier": packet.validation.proof_verifier,
            "obligation_set": packet.validation.obligation_set,
            "timeout_ms": packet.validation.timeout_ms,
        },
        "freshness": {
            "artifact_generation": packet.freshness.artifact_generation,
            "current_generation": packet.freshness.current_generation,
            "freshness_domains": packet.freshness.freshness_domains.iter().map(|observation| json!({
                "domain": observation.domain.as_str(),
                "observed_generation": observation.observed_generation,
                "current_generation": observation.current_generation,
                "stale": observation.is_stale(),
            })).collect::<Vec<_>>(),
            "revoked": packet.freshness.revoked,
            "deny_control": packet.freshness.deny_control.as_ref().map(|deny| json!({
                "active": deny.active,
                "reason": deny.reason.as_str(),
                "scope": deny.scope.as_str(),
                "deny_sha256": deny.deny_sha256,
            })),
        },
        "telemetry": packet.telemetry.as_ref().map(|telemetry| json!({
            "schema": telemetry.schema.as_str(),
            "schema_version": telemetry.schema_version,
            "event_id": telemetry.event_id.as_str(),
            "counter_scope": telemetry.counter_scope.as_str(),
            "record_sha256": telemetry.record_sha256.as_str(),
            "artifact_id": telemetry.artifact_id.as_str(),
            "manifest_checksum": telemetry.manifest_checksum.to_string(),
            "proof_report_sha256": telemetry.proof_report_sha256,
            "layout_checksum": telemetry.layout_checksum.to_string(),
            "invalidation_checksum": telemetry.invalidation_checksum.to_string(),
            "disposition": telemetry.disposition.as_str(),
            "rejection_code": telemetry.rejection_code.map(NativeInstallGateRejectionCode::as_str),
            "install_authority": telemetry.install_authority.as_str(),
            "useful_native_delta": telemetry.useful_native_delta,
        })),
        "replay_identity": packet.replay_identity.as_ref().map(|replay| json!({
            "schema": replay.schema.as_str(),
            "schema_version": replay.schema_version,
            "replay_root_sha256": replay.replay_root_sha256.as_str(),
            "replay_consumer": replay.replay_consumer.as_str(),
            "replay_family": replay.replay_family.as_str(),
            "artifact_id": replay.artifact_id.as_str(),
            "source_sha256": replay.source_sha256.as_str(),
            "trust_ir_sha256": replay.trust_ir_sha256.as_str(),
            "native_payload_sha256": replay.native_payload_sha256.as_str(),
            "replay_record_sha256": replay.replay_record_sha256.as_str(),
        })),
        "replay_binding": {
            "packet_hash": packet.replay_binding.packet_hash.to_string(),
            "replay_root_sha256": packet.replay_binding.replay_root_sha256,
        },
        "consumer_verdict": {
            "consumer": packet.consumer_verdict.consumer,
            "consumer_mode": packet.consumer_verdict.consumer_mode,
            "surface": packet.consumer_verdict.surface.as_str(),
            "verdict_id": packet.consumer_verdict.verdict_id,
            "verdict_sha256": packet.consumer_verdict.verdict_sha256,
        },
        "actions": {
            "expose_callable": packet.actions.expose_callable,
            "typed_symbol_lookup": packet.actions.typed_symbol_lookup,
            "insert_installable_cache": packet.actions.insert_installable_cache,
            "accept_installable_cache_hit": packet.actions.accept_installable_cache_hit,
            "release_installable": packet.actions.release_installable,
            "ay_registry_insert": packet.actions.ay_registry_insert,
            "ty_native_activate": packet.actions.ty_native_activate,
            "useful_native_eligible": packet.actions.useful_native_eligible,
        },
    })
}

fn terminal_reason_code(
    state: AsyncCompileState,
    response: &CompileResponse,
) -> Option<&'static str> {
    match state {
        AsyncCompileState::CompiledInstallable => Some("compiled"),
        AsyncCompileState::ProfileOnly => Some("profile_only"),
        AsyncCompileState::Cancelled => Some("cancelled"),
        AsyncCompileState::StaleGeneration => Some("stale_generation"),
        AsyncCompileState::Failed => Some("failed"),
        AsyncCompileState::Rejected => response
            .explain_reject()
            .map(|explanation| explanation.code.as_str())
            .or(Some("rejected")),
        AsyncCompileState::Queued
        | AsyncCompileState::Running
        | AsyncCompileState::Evicted
        | AsyncCompileState::NotFound => None,
    }
}

fn telemetry_manifest_ref(artifact: &crate::compile_service::CompiledArtifact) -> Option<String> {
    artifact
        .install
        .artifact_manifest
        .as_ref()
        .map(|reference| {
            format!(
                "{}:{}:{}:{}",
                reference.schema,
                reference.schema_version,
                reference.artifact_id,
                reference.manifest_checksum
            )
        })
        .or_else(|| artifact.metadata.deterministic_manifest_reference.clone())
        .or_else(|| {
            artifact
                .artifact_manifest
                .as_ref()
                .map(|manifest| manifest.artifact_id.clone())
        })
}

fn telemetry_proof_ref(artifact: &crate::compile_service::CompiledArtifact) -> Option<String> {
    artifact
        .install
        .artifact_manifest
        .as_ref()
        .map(|reference| reference.proof_policy_checksum.to_string())
}

fn manifest_cache_key(manifest: &ArtifactManifestV1) -> String {
    format!(
        "{}:{}:{}:{}",
        manifest.schema,
        manifest.schema_version,
        manifest.artifact_id,
        manifest.checksum()
    )
}

fn async_reject_explanation(response: &CompileResponse) -> Option<ExplainReject> {
    if state_for_response(response) != AsyncCompileState::Rejected {
        return None;
    }

    let diagnostic = response
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
        .or_else(|| response.diagnostics.first());
    Some(ExplainReject {
        code: RejectCode::Rejected,
        status: response.status,
        diagnostic_code: diagnostic
            .map(|diagnostic| diagnostic.code)
            .unwrap_or_else(|| RejectCode::Rejected.default_diagnostic_code()),
        message: diagnostic.map(|diagnostic| diagnostic.message.clone()),
        phase: diagnostic.and_then(|diagnostic| diagnostic.phase.clone()),
    })
}

fn request_is_stale(request: &CompileRequest) -> bool {
    let fence = request
        .generation_fence
        .as_ref()
        .map(|fence| fence.stale_before());
    let stale_before = match (request.stale_before, fence) {
        (Some(left), Some(right)) => Some(left.max(right)),
        (Some(generation), None) | (None, Some(generation)) => Some(generation),
        (None, None) => None,
    };
    stale_before.is_some_and(|stale_before| request.generation < stale_before)
}

fn terminal_response(
    request: &CompileRequest,
    status: CompileStatus,
    code: &'static str,
    message: &'static str,
    phase: &'static str,
) -> CompileResponse {
    CompileResponse {
        request_id: request.request_id.clone(),
        generation: request.generation,
        status,
        disposition: ArtifactInstallDisposition::Rejected,
        artifact: None,
        payload: None,
        diagnostics: vec![CompileDiagnostic {
            severity: DiagnosticSeverity::Error,
            code,
            message: message.to_owned(),
            function: None,
            phase: Some(phase.to_owned()),
            backend_error: None,
        }],
    }
}

fn submit_diagnostic_code(code: AsyncSubmitRejectCode) -> &'static str {
    match code {
        AsyncSubmitRejectCode::QueueFull => "async.queue_full",
        AsyncSubmitRejectCode::BudgetExceeded => "async.budget_exceeded",
        AsyncSubmitRejectCode::StaleGeneration => "async.stale_generation",
        AsyncSubmitRejectCode::Cancelled => "async.cancelled",
        AsyncSubmitRejectCode::DuplicateRequest => "async.duplicate_request",
        AsyncSubmitRejectCode::DuplicateCacheKey => "async.duplicate_cache_key",
    }
}

fn submit_diagnostic_message(code: AsyncSubmitRejectCode) -> &'static str {
    match code {
        AsyncSubmitRejectCode::QueueFull => "async compile queue full",
        AsyncSubmitRejectCode::BudgetExceeded => "async compile budget exceeded",
        AsyncSubmitRejectCode::StaleGeneration => "async compile request stale at submit",
        AsyncSubmitRejectCode::Cancelled => "async compile request cancelled at submit",
        AsyncSubmitRejectCode::DuplicateRequest => "async compile request id already exists",
        AsyncSubmitRejectCode::DuplicateCacheKey => {
            "async compile manifest cache key already exists"
        }
    }
}
