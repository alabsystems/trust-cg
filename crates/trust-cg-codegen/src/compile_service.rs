// trust-cg-codegen - Compile service API surface
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Runtime-neutral compile-service request, cancellation, and install model.
//!
//! This module intentionally stays above the concrete JIT pipeline. It defines
//! the public state model that background compile workers can use before the
//! backend is wired through this service API.
//!
//! Trust Codegen returns installed executable-memory handles and metadata suitable for
//! downstream registries. Registry policy remains downstream-owned: callers
//! decide keys, replacement rules, eviction, and stale-generation handling.
//!
//! Raw entrypoint accessors on installed artifacts are retained for low-level
//! compatibility and internal wrappers. Product native dispatch must validate
//! a manifest-backed [`SymbolLookupContract`] through
//! [`InstalledArtifact::get_contract_symbol_bound`] before converting a symbol
//! into a callable function pointer.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU64, Ordering},
};
use std::time::{Duration, Instant, SystemTime};

use crate::{
    compile_artifact_cache_profile::{
        CompileArtifactCacheBoundary, CompileArtifactCacheConfig, CompileArtifactCacheTelemetry,
        CompileArtifactProofPolicy,
    },
    compiler::{
        CompilationMetrics, CompilationResult, CompileError, Compiler, CompilerConfig,
        CompilerTrace, CompilerTraceLevel, FunctionQualityMetrics, JitCompilationResult,
        ProofCertificate,
    },
    jit::{
        ExecutableBuffer, JitConfig, JitError, JitFn, JitPtr, JitSymbolPublicationProof,
        ProfileHookMode,
    },
    jit_contract::{
        AbiDescriptor, AbiValue, AbiValueKind, ArtifactChecksum, ArtifactContractError,
        ArtifactManifestV1, Endianness, InvalidationKey, JitArtifactKind, LayoutManifest,
        ProofEvidenceRejectionCode, ProofEvidenceSummary, ProofEvidenceVerdict, ProofMode,
        ProofPolicy, SymbolLookupContract, SymbolSignature, SymbolVisibility, TargetDescriptor,
        TypedSymbol,
    },
    jit_diagnostics::{
        JIT_REPLAY_SCHEMA, JIT_REPLAY_SCHEMA_VERSION, JitReplayReportMetadata, JitTrapStatusBlock,
        JitTrapStatusKind, sha256_hex,
    },
    jit_install_gate::{
        NATIVE_INSTALL_GATE_REPLAY_SCHEMA, NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
        NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA, NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
        NativeInstallGateActions, NativeInstallGateAuthority, NativeInstallGateDisposition,
        NativeInstallGateExpectedBindings, NativeInstallGateInput, NativeInstallGateLayoutAccess,
        NativeInstallGateLayoutEntryAbiEvidence, NativeInstallGateLayoutEvidence,
        NativeInstallGatePacket, NativeInstallGatePayloadIdentity, NativeInstallGateProofEvidence,
        NativeInstallGateRejectionCode, NativeInstallGateReplayIdentity,
        NativeInstallGateRevalidationInput, NativeInstallGateRuntimeTelemetryPacket,
        NativeInstallGateSurface, NativeInstallGateTelemetryInput, PetriNativeSuccessorCallPacket,
        PetriNativeSuccessorCallableLifetimeProof, PetriNativeSuccessorCallablePointer,
        PetriNativeSuccessorCompileArtifactHandoffEvidence,
        PetriNativeSuccessorCompileArtifactHandoffInput, PetriNativeSuccessorRuntimeAbiProof,
        PetriNativeSuccessorRuntimeReadinessPacket, PetriNativeSuccessorTrampolineContract,
        native_install_gate_packet_is_canonical_blocked_reporting_evidence,
        native_install_gate_runtime_telemetry,
        petri_native_successor_compile_artifact_handoff_evidence,
        petri_native_successor_runtime_readiness_packet, validate_native_install_gate,
        validate_native_install_gate_packet_with_current,
    },
    pipeline::{DispatchVerifyMode, OptLevel, encode_tmbc},
    proof_evidence::{
        PROOF_STRENGTH_UNAVAILABLE_CODE, ROUTE_EVIDENCE_VERIFIER, RouteFacts, StrengthRefusal,
        evidence_environment_for, refuse_required_strength, route_evidence,
        route_evidence_for_manifest,
    },
    target::{Target, TargetSpec},
};
use trust_cg_opt::cache::StableHasher;

/// Lightweight runtime-agnostic cancellation token.
#[derive(Clone, Default)]
pub struct CancellationToken {
    cancelled: Arc<AtomicBool>,
}

impl CancellationToken {
    /// Create a token in the non-cancelled state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a token that is already cancelled.
    pub fn cancelled() -> Self {
        let token = Self::new();
        token.cancel();
        token
    }

    /// Request cooperative cancellation.
    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Release);
    }

    /// Return whether cancellation has been requested.
    pub fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }
}

impl fmt::Debug for CancellationToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CancellationToken")
            .field("cancelled", &self.is_cancelled())
            .finish()
    }
}

/// Caller-provided request id for logs and deduplication.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompileRequestId(String);

impl CompileRequestId {
    /// Create a request id from a caller-controlled string.
    pub fn new(id: impl Into<String>) -> Self {
        Self(id.into())
    }

    /// Borrow the request id as a string.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for CompileRequestId {
    fn from(value: &str) -> Self {
        Self::new(value)
    }
}

impl From<String> for CompileRequestId {
    fn from(value: String) -> Self {
        Self::new(value)
    }
}

/// Monotonic downstream freshness generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct CompileGeneration(u64);

impl CompileGeneration {
    /// Create a generation value.
    pub const fn new(value: u64) -> Self {
        Self(value)
    }

    /// Return the raw generation value.
    pub const fn get(self) -> u64 {
        self.0
    }
}

impl From<u64> for CompileGeneration {
    fn from(value: u64) -> Self {
        Self::new(value)
    }
}

/// Shared stale-generation fence.
///
/// A request with `generation < stale_before()` is stale and must not return an
/// installable artifact.
#[derive(Debug, Clone, Default)]
pub struct CompileGenerationFence {
    stale_before: Arc<AtomicU64>,
}

impl CompileGenerationFence {
    /// Create a fence with no stale generations.
    pub fn new() -> Self {
        Self::default()
    }

    /// Mark generations lower than `generation` as stale.
    pub fn mark_stale_before(&self, generation: CompileGeneration) {
        let mut current = self.stale_before.load(Ordering::Acquire);
        while generation.get() > current {
            match self.stale_before.compare_exchange_weak(
                current,
                generation.get(),
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return,
                Err(observed) => current = observed,
            }
        }
    }

    /// Return the current exclusive stale-before generation.
    pub fn stale_before(&self) -> CompileGeneration {
        CompileGeneration::new(self.stale_before.load(Ordering::Acquire))
    }
}

/// Compile result status.
///
/// These states are intentionally plain data so background workers can pass
/// results across channels owned by any async runtime, a thread pool, or a
/// synchronous driver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileStatus {
    /// Compilation produced an artifact. Install eligibility is recorded on
    /// the artifact's install disposition.
    Compiled,
    /// The request was cooperatively cancelled.
    Cancelled,
    /// The request generation is older than the stale-generation fence.
    Stale,
    /// The service rejected the request before backend work.
    Rejected,
    /// Backend compilation failed.
    Failed,
}

/// Typed diagnostic severity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    /// Extra context useful for logs and tracing.
    Note,
    /// Recoverable concern that did not stop compilation.
    Warning,
    /// Terminal failure for this request.
    Error,
}

/// Artifact payload kind requested by a compile-service caller.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArtifactKind {
    /// Return relocatable object bytes.
    Object,
    /// Return executable memory suitable for JIT calls.
    ExecutableMemory,
}

impl ArtifactKind {
    const fn contract_name(self) -> &'static str {
        match self {
            Self::Object => "object",
            Self::ExecutableMemory => "executable_memory",
        }
    }
}

/// Compile/install intent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstallIntent {
    /// Compile only; caller will decide whether and where to install.
    CompileOnly,
    /// Compile and validate that the artifact is still fresh at install time.
    Install,
}

/// Compile-service install eligibility for a compiled artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ArtifactInstallDisposition {
    /// Artifact may be converted into an installed runtime handle.
    #[default]
    Installable,
    /// Artifact is retained only for profiling/telemetry and must not install.
    ProfileOnly,
    /// Artifact was compiled but rejected by install-time policy.
    Rejected,
}

impl ArtifactInstallDisposition {
    /// Return the stable manifest/log string for this disposition.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Installable => "installable",
            Self::ProfileOnly => "profile_only",
            Self::Rejected => "rejected",
        }
    }
}

/// Service profile for common downstream compile policies.
#[derive(Debug, Clone)]
pub enum CompileProfile {
    /// Low-latency AArch64 executable-memory profile for solver programs.
    FastAarch64Solver,
    /// Low-latency executable-memory profile for the current host.
    HostJitFast,
    /// Caller-provided backend knobs.
    Custom {
        /// Object/compiler configuration.
        compiler: CompilerConfig,
        /// JIT configuration.
        jit: JitConfig,
    },
}

/// Stable profile identifier for artifact metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompileProfileId {
    /// [`CompileProfile::FastAarch64Solver`].
    FastAarch64Solver,
    /// [`CompileProfile::HostJitFast`].
    HostJitFast,
    /// [`CompileProfile::Custom`].
    Custom,
}

/// Concrete backend knobs selected by a service profile.
#[derive(Debug, Clone)]
pub struct ExpandedCompileProfile {
    /// Object/compiler configuration.
    pub compiler: CompilerConfig,
    /// JIT configuration.
    pub jit: JitConfig,
    /// Default artifact kind for the profile.
    pub artifact_kind: ArtifactKind,
}

impl CompileProfile {
    /// Return the stable identifier for this profile.
    pub fn id(&self) -> CompileProfileId {
        match self {
            Self::FastAarch64Solver => CompileProfileId::FastAarch64Solver,
            Self::HostJitFast => CompileProfileId::HostJitFast,
            Self::Custom { .. } => CompileProfileId::Custom,
        }
    }

    /// Expand a service-level profile into existing backend configurations.
    pub fn expand(&self) -> ExpandedCompileProfile {
        match self {
            Self::FastAarch64Solver => ExpandedCompileProfile {
                compiler: CompilerConfig::jit_fast(Target::Aarch64),
                jit: JitConfig {
                    opt_level: OptLevel::O1,
                    verify: false,
                    verify_dispatch: DispatchVerifyMode::ErrorOnFailure,
                    profile_hooks: ProfileHookMode::None,
                    emit_entry_counters: false,
                    ..JitConfig::default()
                },
                artifact_kind: ArtifactKind::ExecutableMemory,
            },
            Self::HostJitFast => ExpandedCompileProfile {
                compiler: CompilerConfig::for_host_jit(),
                jit: JitConfig {
                    opt_level: OptLevel::O1,
                    verify: false,
                    verify_dispatch: DispatchVerifyMode::ErrorOnFailure,
                    profile_hooks: ProfileHookMode::None,
                    emit_entry_counters: false,
                    ..JitConfig::default()
                },
                artifact_kind: ArtifactKind::ExecutableMemory,
            },
            Self::Custom { compiler, jit } => ExpandedCompileProfile {
                compiler: compiler.clone(),
                jit: jit.clone(),
                artifact_kind: ArtifactKind::ExecutableMemory,
            },
        }
    }
}

/// Compile-service configuration.
#[derive(Debug, Clone)]
pub struct CompileServiceConfig {
    /// Default profile for requests that do not override it.
    pub profile: CompileProfile,
    /// Optional durable compile artifact cache for object artifacts.
    pub compile_artifact_cache: Option<CompileArtifactCacheConfig>,
}

impl Default for CompileServiceConfig {
    fn default() -> Self {
        Self {
            profile: CompileProfile::HostJitFast,
            compile_artifact_cache: None,
        }
    }
}

/// Compile request envelope.
///
/// The request carries only cloneable metadata and a small cooperative
/// cancellation token. Callers can enqueue it on background workers without
/// taking a dependency on Tokio, futures, or any other runtime.
#[derive(Debug, Clone)]
pub struct CompileRequest {
    /// Caller-supplied request id for logs and dedupe.
    pub request_id: CompileRequestId,
    /// Downstream freshness generation.
    pub generation: CompileGeneration,
    /// Optional request-local exclusive stale-before fence.
    pub stale_before: Option<CompileGeneration>,
    /// Optional shared stale-generation fence.
    pub generation_fence: Option<CompileGenerationFence>,
    /// Requested profile.
    pub profile: CompileProfile,
    /// Requested artifact kind.
    pub artifact_kind: ArtifactKind,
    /// Compile/install policy.
    pub install_intent: InstallIntent,
    /// Proof policy required before an artifact may be installed.
    pub proof_policy: ProofPolicy,
    /// Optional local proof/translation-validation evidence outcome.
    pub proof_tv_evidence: Option<ProofTvEvidenceOutcome>,
    /// Caller-supplied provenance for the artifact this request would produce.
    pub provenance: ArtifactProvenance,
    /// Optional deterministic artifact manifest supplied by the caller.
    ///
    /// The manifest is carried as install/dispatch metadata. It is not part of
    /// the existing compile-service identity hash, preserving request-id and
    /// provenance exclusion behavior from #518.
    pub artifact_manifest: Option<ArtifactManifestV1>,
    /// Cooperative cancellation token.
    pub cancellation: CancellationToken,
}

impl CompileRequest {
    /// Create a compile request with default host-JIT settings.
    pub fn new(request_id: impl Into<CompileRequestId>, generation: CompileGeneration) -> Self {
        let profile = CompileProfile::HostJitFast;
        let artifact_kind = profile.expand().artifact_kind;
        Self {
            request_id: request_id.into(),
            generation,
            stale_before: None,
            generation_fence: None,
            profile,
            artifact_kind,
            install_intent: InstallIntent::Install,
            proof_policy: ProofPolicy::disabled(),
            proof_tv_evidence: None,
            provenance: ArtifactProvenance::default(),
            artifact_manifest: None,
            cancellation: CancellationToken::new(),
        }
    }

    /// Attach the deterministic artifact manifest this request is producing.
    pub fn with_artifact_manifest(mut self, manifest: ArtifactManifestV1) -> Self {
        self.artifact_manifest = Some(manifest);
        self
    }

    fn effective_stale_before(&self) -> Option<CompileGeneration> {
        let fence = self
            .generation_fence
            .as_ref()
            .map(CompileGenerationFence::stale_before);
        match (self.stale_before, fence) {
            (Some(left), Some(right)) => Some(left.max(right)),
            (Some(generation), None) | (None, Some(generation)) => Some(generation),
            (None, None) => None,
        }
    }

    fn is_stale(&self) -> bool {
        self.effective_stale_before()
            .is_some_and(|stale_before| self.generation < stale_before)
    }
}

/// Stable artifact identity placeholder.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArtifactIdentity(String);

impl ArtifactIdentity {
    /// Create an artifact identity.
    pub fn new(identity: impl Into<String>) -> Self {
        Self(identity.into())
    }

    /// Borrow the artifact identity as a string.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for ArtifactIdentity {
    fn from(value: &str) -> Self {
        Self::new(value)
    }
}

impl From<String> for ArtifactIdentity {
    fn from(value: String) -> Self {
        Self::new(value)
    }
}

/// Process-local native symbol binding recorded in provenance/install metadata.
///
/// Raw addresses are intentionally excluded from stable artifact identity
/// hashes because they vary between processes and runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawExternBinding {
    /// External symbol name as seen by the generated artifact.
    pub symbol: String,
    /// Raw native address installed for this process.
    pub address: usize,
}

impl RawExternBinding {
    /// Create a raw extern binding metadata record.
    pub fn new(symbol: impl Into<String>, address: usize) -> Self {
        Self {
            symbol: symbol.into(),
            address,
        }
    }
}

/// Canonical input to the deterministic artifact identity hash.
#[derive(Debug, Clone)]
pub struct ArtifactIdentityInput {
    /// Canonical lowered trust_ir/module bytes or prepared backend input bytes.
    pub module_bytes: Vec<u8>,
    /// Target architecture selected for compilation.
    pub target: Target,
    /// Requested profile identifier.
    pub profile: CompileProfileId,
    /// Expanded compiler knobs that affect generated code.
    pub compiler: CompilerConfig,
    /// Expanded JIT knobs that affect generated code.
    pub jit: JitConfig,
    /// Requested artifact payload kind.
    pub artifact_kind: ArtifactKind,
    /// Exported symbol names in caller-visible order.
    pub exported_symbols: Vec<String>,
    /// Proof/install policy selected by the caller.
    pub proof_policy: ProofPolicy,
    /// Install intent selected by the caller.
    pub install_intent: InstallIntent,
}

impl ArtifactIdentityInput {
    /// Build identity input from a compile request and canonical module bytes.
    pub fn from_request(
        request: &CompileRequest,
        module_bytes: impl AsRef<[u8]>,
        exported_symbols: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        let expanded = expanded_profile_for_request(request);
        Self {
            module_bytes: module_bytes.as_ref().to_vec(),
            target: expanded.compiler.target,
            profile: request.profile.id(),
            compiler: expanded.compiler,
            jit: expanded.jit,
            artifact_kind: request.artifact_kind,
            exported_symbols: exported_symbols.into_iter().map(Into::into).collect(),
            proof_policy: request.proof_policy.clone(),
            install_intent: request.install_intent,
        }
    }

    /// Compute the stable artifact identity digest.
    pub fn identity(&self) -> ArtifactIdentity {
        let mut hasher = StableHasher::new();
        hash_str(&mut hasher, "trust-cg.compile_service.artifact_identity.v1");
        hash_bytes(&mut hasher, &self.module_bytes);
        hash_target(&mut hasher, self.target);
        hash_profile_id(&mut hasher, self.profile);
        hash_compiler_config(&mut hasher, &self.compiler);
        hash_jit_config(&mut hasher, &self.jit);
        hash_artifact_kind(&mut hasher, self.artifact_kind);
        hash_usize(&mut hasher, self.exported_symbols.len());
        for symbol in &self.exported_symbols {
            hash_str(&mut hasher, symbol);
        }
        hash_proof_policy(&mut hasher, &self.proof_policy);
        hash_install_intent(&mut hasher, self.install_intent);
        ArtifactIdentity::new(format!("trust-cg-stable128:{:032x}", hasher.finish128()))
    }
}

/// Input category recorded in artifact provenance.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum SourceKind {
    /// Caller did not provide a source category.
    #[default]
    Unspecified,
    /// Whole trust_ir module input.
    TrustIrModule,
    /// Pre-lowered prepared-function input.
    PreparedFunctions,
    /// Caller-provided object bytes.
    ObjectBytes,
    /// Downstream-specific input category.
    Other(String),
}

/// Reproducibility metadata for a compiled artifact.
///
/// The service treats provenance as caller-owned data. It is suitable for
/// background queues because it records stable strings and fingerprints rather
/// than process-local pointers or runtime handles.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactProvenance {
    /// Producer crate or adapter name.
    pub producer: &'static str,
    /// Producer version or revision when available.
    pub producer_version: Option<String>,
    /// Source category used to produce the artifact.
    pub source_kind: SourceKind,
    /// Stable source fingerprint supplied by the caller.
    pub source_fingerprint: Option<String>,
    /// Optional issue number or task id that requested the artifact.
    pub upstream_issue: Option<u64>,
    /// Downstream context such as solver-program id or region name.
    pub caller_context: BTreeMap<String, String>,
    /// Process-local external bindings used for this artifact.
    pub raw_extern_bindings: Vec<RawExternBinding>,
}

impl Default for ArtifactProvenance {
    fn default() -> Self {
        Self {
            producer: "trust-cg-codegen",
            producer_version: Some(env!("CARGO_PKG_VERSION").to_owned()),
            source_kind: SourceKind::Unspecified,
            source_fingerprint: None,
            upstream_issue: None,
            caller_context: BTreeMap::new(),
            raw_extern_bindings: Vec::new(),
        }
    }
}

/// Stable install-time reference to a deterministic artifact manifest.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArtifactManifestReference {
    /// Manifest schema name.
    pub schema: String,
    /// Manifest schema version.
    pub schema_version: u32,
    /// Caller-visible artifact id.
    pub artifact_id: String,
    /// Whole-manifest checksum over canonical manifest bytes.
    pub manifest_checksum: ArtifactChecksum,
    /// Target descriptor checksum.
    pub target_checksum: ArtifactChecksum,
    /// ABI descriptor checksum.
    pub abi_checksum: ArtifactChecksum,
    /// Layout descriptor checksum.
    pub layout_checksum: ArtifactChecksum,
    /// Invalidation key checksum.
    pub invalidation_checksum: ArtifactChecksum,
    /// Proof policy checksum.
    pub proof_policy_checksum: ArtifactChecksum,
}

impl ArtifactManifestReference {
    /// Build a stable reference from a full v1 artifact manifest.
    pub fn from_manifest(manifest: &ArtifactManifestV1) -> Self {
        Self {
            schema: manifest.schema.clone(),
            schema_version: manifest.schema_version,
            artifact_id: manifest.artifact_id.clone(),
            manifest_checksum: manifest.checksum(),
            target_checksum: manifest.target.checksum(),
            abi_checksum: manifest.abi.checksum(),
            layout_checksum: manifest.layout.checksum(),
            invalidation_checksum: manifest.invalidation.checksum(),
            proof_policy_checksum: manifest.proof_policy.checksum(),
        }
    }

    /// Validate a full manifest against this reference.
    pub fn verify_manifest(
        &self,
        manifest: &ArtifactManifestV1,
    ) -> Result<(), ArtifactContractError> {
        if self.schema != manifest.schema || self.schema_version != manifest.schema_version {
            return Err(ArtifactContractError::SchemaMismatch {
                expected_schema: self.schema.clone(),
                expected_version: self.schema_version,
                actual_schema: manifest.schema.clone(),
                actual_version: manifest.schema_version,
            });
        }

        if self.artifact_id != manifest.artifact_id {
            return Err(ArtifactContractError::ChecksumMismatch {
                component: "artifact_id".to_owned(),
                expected: ArtifactChecksum::for_bytes(self.artifact_id.as_bytes()),
                actual: ArtifactChecksum::for_bytes(manifest.artifact_id.as_bytes()),
            });
        }

        manifest.verify_schema()?;
        manifest.verify_checksum(self.manifest_checksum)?;
        manifest.verify_target_checksum(self.target_checksum)?;
        manifest.verify_abi_checksum(self.abi_checksum)?;
        manifest.verify_layout_checksum(self.layout_checksum)?;
        manifest.verify_invalidation_checksum(self.invalidation_checksum)?;

        let actual_proof_policy_checksum = manifest.proof_policy.checksum();
        if actual_proof_policy_checksum != self.proof_policy_checksum {
            return Err(ArtifactContractError::ChecksumMismatch {
                component: "proof_policy".to_owned(),
                expected: self.proof_policy_checksum,
                actual: actual_proof_policy_checksum,
            });
        }

        Ok(())
    }
}

/// Metadata describing a compiled artifact without carrying executable bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactMetadata {
    /// Payload kind represented by the artifact.
    pub artifact_kind: ArtifactKind,
    /// Target architecture selected for compilation.
    pub target: Target,
    /// Stable profile identifier selected for compilation.
    pub profile: CompileProfileId,
    /// Size of emitted code or object bytes when known.
    pub code_size_bytes: usize,
    /// Size of executable allocation when known.
    pub allocation_size_bytes: Option<usize>,
    /// Optional deterministic artifact manifest checksum.
    pub deterministic_manifest_checksum: Option<ArtifactChecksum>,
    /// Optional caller-visible deterministic artifact manifest reference.
    pub deterministic_manifest_reference: Option<String>,
    /// Request proof-policy checksum used for artifact identity/install gating.
    pub proof_policy_checksum: ArtifactChecksum,
}

impl ArtifactMetadata {
    /// Create metadata from a compile profile expansion.
    pub fn from_profile(profile: &CompileProfile, artifact_kind: ArtifactKind) -> Self {
        let expanded = profile.expand();
        Self {
            artifact_kind,
            target: expanded.compiler.target,
            profile: profile.id(),
            code_size_bytes: 0,
            allocation_size_bytes: None,
            deterministic_manifest_checksum: None,
            deterministic_manifest_reference: None,
            proof_policy_checksum: ProofPolicy::disabled().checksum(),
        }
    }

    /// Attach a deterministic artifact manifest reference and checksum.
    pub fn with_deterministic_manifest(mut self, manifest: &ArtifactManifestV1) -> Self {
        self.deterministic_manifest_checksum = Some(manifest.checksum());
        self.deterministic_manifest_reference = Some(manifest.artifact_id.clone());
        self
    }
}

impl Default for ArtifactMetadata {
    fn default() -> Self {
        Self::from_profile(&CompileProfile::HostJitFast, ArtifactKind::ExecutableMemory)
    }
}

/// Install metadata suitable for a downstream registry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstallMetadata {
    /// Generation that was compiled.
    pub generation: CompileGeneration,
    /// Artifact identity to compare during install.
    pub identity: ArtifactIdentity,
    /// Compile-service install eligibility.
    pub disposition: ArtifactInstallDisposition,
    /// Stable artifact metadata used by downstream registries.
    pub artifact: ArtifactMetadata,
    /// Stable manifest reference used by manifest-validated wrappers.
    pub artifact_manifest: Option<ArtifactManifestReference>,
    /// Replayable JIT diagnostics metadata for executable-memory artifacts.
    pub replay_report_metadata: Option<JitReplayReportMetadata>,
    /// Versioned, compiler-derived binding between the manifest/install
    /// authority and the exact executable bytes + symbol layout that were
    /// published. Product callable exposure requires this binding and
    /// revalidates it against the live [`ExecutableBuffer`].
    pub installed_payload_binding: Option<InstalledPayloadBinding>,
    /// Time when compilation finished.
    pub compiled_at: SystemTime,
    /// End-to-end compile latency when measured by the caller.
    pub compile_latency: Duration,
    /// Exported entrypoints with canonical names and offsets inside the
    /// executable allocation. Raw function pointers are deliberately omitted.
    pub exported_entrypoints: Vec<EntryPointMetadata>,
    /// Per-function metadata for the compiled module.
    pub functions: Vec<FunctionArtifactMetadata>,
    /// Proof summary available at install time.
    pub proofs: InstallProofSummary,
    /// Artifact-bound proof/translation-validation evidence report.
    pub proof_evidence_report: Option<ProofTvEvidenceReportV1>,
    /// Always-present statement of what proof evidence this compile route
    /// actually produced, and what it is relying on rather than checking.
    ///
    /// Unlike [`Self::proof_evidence_report`], this field is **not** optional.
    /// A compile on which nothing ran carries an explicit
    /// [`ProofEvidenceVerdict::MissingEvidence`] summary at
    /// [`EvidenceStrength::NotRun`](crate::jit_contract::EvidenceStrength::NotRun),
    /// because an absent evidence field is indistinguishable from a passing
    /// one. It is reporting only: nothing gates on it, and it is not part of
    /// any artifact identity, manifest, or install-gate checksum.
    pub proof_evidence_summary: ProofEvidenceSummary,
    /// Evidence packet supplied to the shared native install gate.
    pub native_install_gate_input: Option<NativeInstallGateInput>,
    /// Shared native install gate verdict for this install boundary.
    pub native_install_gate: Option<NativeInstallGatePacket>,
    /// Request proof policy used to decide installability.
    pub proof_policy: ProofPolicy,
    /// Snapshot of counters available at install time.
    pub counters: Vec<CounterSummary>,
    /// Process-local external bindings used when installing executable memory.
    pub raw_extern_bindings: Vec<RawExternBinding>,
}

/// Canonical executable entrypoint metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EntryPointMetadata {
    /// Canonical function symbol name.
    pub name: String,
    /// Offset in bytes from the start of the executable allocation.
    pub offset_bytes: u64,
}

/// Stable schema for the non-circular installed executable payload binding.
pub const INSTALLED_PAYLOAD_BINDING_SCHEMA: &str =
    "trust-cg.compile_service.installed_payload_binding.v3";

/// Stable numeric version for [`InstalledPayloadBinding`].
pub const INSTALLED_PAYLOAD_BINDING_SCHEMA_VERSION: u32 = 3;

/// One exact function range in an installed executable payload binding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstalledPayloadSymbolBinding {
    /// Canonical function name.
    pub name: String,
    /// Compiler/module-derived symbol visibility.
    pub visibility: SymbolVisibility,
    /// Half-open byte-range start in the executable code image.
    pub start_offset: u64,
    /// Half-open byte-range end in the executable code image.
    pub end_offset: u64,
    /// Additional lookup aliases resolving to `start_offset`.
    pub aliases: Vec<String>,
    /// Compiler/module-derived canonical C ABI signature. This is never copied
    /// from the caller manifest.
    pub signature: SymbolSignature,
}

/// Compiler-derived authority for one installed executable image.
///
/// This record is deliberately separate from the caller manifest. The target,
/// ABI, and core layout come from the exact [`Compiler`] used for codegen; the
/// payload digest and symbol ranges come from the live published buffer. The
/// optional manifest checksum then binds those independent facts to the caller
/// contract without treating a self-consistent caller manifest as codegen
/// evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstalledPayloadBinding {
    /// Stable schema tag.
    pub schema: String,
    /// Stable schema version.
    pub schema_version: u32,
    /// Payload category covered by this binding.
    pub artifact_kind: ArtifactKind,
    /// Exact effective compiler target triple.
    pub compiler_target_triple: String,
    /// Compile-service artifact identity that owns this binding.
    pub artifact_identity: String,
    /// Canonical trust_ir module digest whose signatures were bound.
    pub trust_ir_module_sha256: String,
    /// Compiler-derived target descriptor.
    pub authoritative_target: TargetDescriptor,
    /// Compiler-derived ABI descriptor.
    pub authoritative_abi: AbiDescriptor,
    /// Compiler-derived target-core layout plus any optional symbol rows that
    /// were independently verified against the live executable. Caller-owned
    /// records/slices/pointers are never copied into this authority record.
    pub authoritative_layout: LayoutManifest,
    /// Full caller manifest checksum, when a manifest was supplied at compile
    /// time. Typed product lookup requires this to match the presented
    /// manifest exactly.
    pub manifest_checksum: Option<ArtifactChecksum>,
    /// SHA-256 of exactly `ExecutableBuffer::code_slice()`.
    pub native_payload_sha256: String,
    /// SHA-256 of the complete published executable image, including any
    /// target metadata appended after the encoded code prefix (for example,
    /// Windows unwind tables).
    pub published_image_sha256: String,
    /// Exact encoded code length, excluding appended platform unwind tables.
    pub code_size_bytes: u64,
    /// Exact live executable allocation extent owned by the published buffer.
    pub allocation_size_bytes: u64,
    /// Exact canonical function ranges and aliases.
    pub symbols: Vec<InstalledPayloadSymbolBinding>,
    /// SHA-256 over every preceding field in canonical order. Kept private so
    /// downstream code can inspect/clone compiler authority but cannot mutate
    /// public fields and reseal a fabricated binding through safe Rust.
    binding_sha256: String,
}

impl InstalledPayloadBinding {
    /// Return the compiler-sealed canonical binding digest.
    pub fn binding_sha256(&self) -> &str {
        &self.binding_sha256
    }

    fn with_canonical_binding_sha256(mut self, manifest: Option<&ArtifactManifestV1>) -> Self {
        self.binding_sha256 = installed_payload_binding_sha256(&self, manifest);
        self
    }

    fn has_canonical_binding_sha256(&self, manifest: Option<&ArtifactManifestV1>) -> bool {
        self.binding_sha256 == installed_payload_binding_sha256(self, manifest)
    }
}

/// Stable proof-policy state for a compiled artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofPolicyStatus {
    /// Proofs were not required for this artifact.
    NotRequired,
    /// Required proof evidence satisfied the compile-service policy.
    Satisfied,
    /// Required proof evidence was missing or not fully verified.
    Rejected,
}

impl ProofPolicyStatus {
    /// Return the stable manifest/log string for this proof status.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NotRequired => "not_required",
            Self::Satisfied => "satisfied",
            Self::Rejected => "rejected",
        }
    }
}

/// Stable rejection code for compile-service proof policy failures.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofRejectionCode {
    /// Lowering proof certificates were required but absent.
    MissingLoweringCertificates,
    /// At least one lowering proof certificate was not verified.
    UnverifiedLoweringCertificates,
    /// JIT buffer proof certificates were required but absent.
    MissingJitCertificates,
    /// At least one JIT buffer certificate was not verified.
    UnverifiedJitCertificates,
}

impl ProofRejectionCode {
    /// Return the stable manifest/log string for this rejection code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingLoweringCertificates => "missing_lowering_certificates",
            Self::UnverifiedLoweringCertificates => "unverified_lowering_certificates",
            Self::MissingJitCertificates => "missing_jit_certificates",
            Self::UnverifiedJitCertificates => "unverified_jit_certificates",
        }
    }
}

/// Stable proof/translation-validation outcome carried by evidence report v1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofTvVerdict {
    /// Evidence is accepted for this artifact and policy.
    Accepted,
    /// Required proof or translation-validation evidence is absent.
    MissingEvidence,
    /// A verifier rejected the artifact or evidence.
    VerifierFailure,
    /// Verification or replay timed out.
    Timeout,
    /// Verification returned an unknown outcome.
    Unknown,
    /// Solver execution failed.
    SolverError,
    /// This compile route cannot produce the required evidence.
    UnsupportedRoute,
    /// The target is unsupported for the required evidence.
    UnsupportedTarget,
    /// Evidence is not fresh for the artifact/source/invalidation key.
    StaleEvidence,
    /// The evidence report is malformed.
    MalformedReport,
    /// The evidence report omitted a required field.
    MissingRequiredFields,
}

impl ProofTvVerdict {
    /// Return the stable lower-snake-case report string for this verdict.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::MissingEvidence => "missing_evidence",
            Self::VerifierFailure => "verifier_failure",
            Self::Timeout => "timeout",
            Self::Unknown => "unknown",
            Self::SolverError => "solver_error",
            Self::UnsupportedRoute => "unsupported_route",
            Self::UnsupportedTarget => "unsupported_target",
            Self::StaleEvidence => "stale_evidence",
            Self::MalformedReport => "malformed_report",
            Self::MissingRequiredFields => "missing_required_fields",
        }
    }
}

/// Stable product rejection code for proof/translation-validation outcomes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofTvRejectionCode {
    /// Required evidence is absent.
    MissingEvidence,
    /// A verifier rejected the artifact or evidence.
    VerifierFailure,
    /// Verification or replay timed out.
    Timeout,
    /// Verification returned an unknown outcome.
    Unknown,
    /// Solver execution failed.
    SolverError,
    /// This compile route cannot produce the required evidence.
    UnsupportedRoute,
    /// The target is unsupported for the required evidence.
    UnsupportedTarget,
    /// Evidence is stale for this artifact/source/invalidation key.
    StaleEvidence,
    /// The report is malformed.
    MalformedReport,
    /// The report omitted a required field.
    MissingRequiredFields,
}

impl ProofTvRejectionCode {
    /// Return the stable lower-snake-case product code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingEvidence => "proof_missing_evidence",
            Self::VerifierFailure => "proof_verifier_failure",
            Self::Timeout => "proof_timeout",
            Self::Unknown => "proof_unknown",
            Self::SolverError => "proof_solver_error",
            Self::UnsupportedRoute => "proof_unsupported_route",
            Self::UnsupportedTarget => "proof_unsupported_target",
            Self::StaleEvidence => "proof_stale_evidence",
            Self::MalformedReport => "proof_malformed_report",
            Self::MissingRequiredFields => "proof_missing_required_fields",
        }
    }
}

/// Caller-supplied proof/translation-validation evidence outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofTvEvidenceOutcome {
    /// Stable evidence verdict.
    pub verdict: ProofTvVerdict,
    /// Stable product rejection code when the verdict is rejected.
    pub rejection_code: Option<ProofTvRejectionCode>,
    /// Replay/diagnostic reason emitted for downstream audit and Phase 3.
    pub diagnostic_reason: String,
}

impl ProofTvEvidenceOutcome {
    /// Build a rejected proof/translation-validation evidence outcome.
    pub fn rejected(
        verdict: ProofTvVerdict,
        rejection_code: ProofTvRejectionCode,
        diagnostic_reason: impl Into<String>,
    ) -> Self {
        Self {
            verdict,
            rejection_code: Some(rejection_code),
            diagnostic_reason: diagnostic_reason.into(),
        }
    }
}

/// Artifact-bound proof/translation-validation evidence report v1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofTvEvidenceReportV1 {
    /// Report schema name.
    pub schema: &'static str,
    /// Report schema version.
    pub schema_version: u32,
    /// Proof policy checksum covered by this report.
    pub proof_policy_checksum: ArtifactChecksum,
    /// Stable report verdict.
    pub verdict: ProofTvVerdict,
    /// Stable product rejection code when verdict is not accepted.
    pub rejection_code: Option<ProofTvRejectionCode>,
    /// Report hash over canonical report fields excluding this hash.
    pub report_hash: ArtifactChecksum,
    /// Target facts checksum covered by this report.
    pub target_checksum: ArtifactChecksum,
    /// ABI facts checksum covered by this report.
    pub abi_checksum: ArtifactChecksum,
    /// Layout facts checksum covered by this report.
    pub layout_checksum: ArtifactChecksum,
    /// Invalidation key checksum covered by this report.
    pub invalidation_checksum: ArtifactChecksum,
    /// Artifact identity covered by this report.
    pub artifact_identity: ArtifactIdentity,
    /// Source fingerprint covered by this report when known.
    pub source_fingerprint: Option<String>,
    /// Backend proof-family report schema covered by this report when known.
    pub backend_proof_family_schema: Option<String>,
    /// Backend proof-family target covered by this report when known.
    pub backend_proof_family_target: Option<String>,
    /// Backend proof-family obligation set covered by this report when known.
    pub backend_proof_family_obligation_set: Option<String>,
    /// Backend proof-family report policy id covered by this report when known.
    pub backend_proof_family_policy_id: Option<String>,
    /// Backend proof-family installability marker covered by this report when known.
    pub backend_proof_family_installable: Option<bool>,
    /// Backend proof-family report hash covered by this report when known.
    pub backend_proof_family_report_hash: Option<String>,
    /// Replay/diagnostic reason for rejected evidence.
    pub diagnostic_reason: Option<String>,
}

impl ProofTvEvidenceReportV1 {
    /// Current report schema name.
    pub const SCHEMA: &'static str = "trust-cg.compile_service.proof_tv_evidence_report/v1";
    /// Current report schema version.
    pub const SCHEMA_VERSION: u32 = 1;

    fn new(
        request: &CompileRequest,
        artifact: &CompiledArtifact,
        verdict: ProofTvVerdict,
        rejection_code: Option<ProofTvRejectionCode>,
        diagnostic_reason: Option<String>,
    ) -> Self {
        let (target_checksum, abi_checksum, layout_checksum, invalidation_checksum) =
            report_binding_checksums(request, artifact);
        let backend_proof_family = backend_proof_family_report_identity(artifact.metadata.target);
        let mut report = Self {
            schema: Self::SCHEMA,
            schema_version: Self::SCHEMA_VERSION,
            proof_policy_checksum: request.proof_policy.checksum(),
            verdict,
            rejection_code,
            report_hash: ArtifactChecksum::new(0),
            target_checksum,
            abi_checksum,
            layout_checksum,
            invalidation_checksum,
            artifact_identity: artifact.identity.clone(),
            source_fingerprint: artifact.provenance.source_fingerprint.clone(),
            backend_proof_family_schema: backend_proof_family
                .as_ref()
                .map(|identity| identity.schema.clone()),
            backend_proof_family_target: backend_proof_family
                .as_ref()
                .map(|identity| identity.target.clone()),
            backend_proof_family_obligation_set: backend_proof_family
                .as_ref()
                .map(|identity| identity.obligation_set.clone()),
            backend_proof_family_policy_id: backend_proof_family
                .as_ref()
                .map(|identity| identity.policy_id.clone()),
            backend_proof_family_installable: backend_proof_family
                .as_ref()
                .map(|identity| identity.installable),
            backend_proof_family_report_hash: backend_proof_family
                .as_ref()
                .map(|identity| identity.report_hash.clone()),
            diagnostic_reason,
        };
        report.report_hash = report.compute_report_hash();
        report
    }

    fn accepted(request: &CompileRequest, artifact: &CompiledArtifact) -> Self {
        Self::new(request, artifact, ProofTvVerdict::Accepted, None, None)
    }

    fn rejected(
        request: &CompileRequest,
        artifact: &CompiledArtifact,
        verdict: ProofTvVerdict,
        rejection_code: ProofTvRejectionCode,
        diagnostic_reason: Option<String>,
    ) -> Self {
        Self::new(
            request,
            artifact,
            verdict,
            Some(rejection_code),
            diagnostic_reason,
        )
    }

    fn compute_report_hash(&self) -> ArtifactChecksum {
        let mut hasher = StableHasher::new();
        hash_str(&mut hasher, Self::SCHEMA);
        hash_u64(&mut hasher, Self::SCHEMA_VERSION as u64);
        hash_u128(&mut hasher, self.proof_policy_checksum.get());
        hash_str(&mut hasher, self.verdict.as_str());
        hash_str(
            &mut hasher,
            self.rejection_code
                .map(ProofTvRejectionCode::as_str)
                .unwrap_or("none"),
        );
        hash_u128(&mut hasher, self.target_checksum.get());
        hash_u128(&mut hasher, self.abi_checksum.get());
        hash_u128(&mut hasher, self.layout_checksum.get());
        hash_u128(&mut hasher, self.invalidation_checksum.get());
        hash_str(&mut hasher, self.artifact_identity.as_str());
        match &self.source_fingerprint {
            Some(source_fingerprint) => {
                hash_bool(&mut hasher, true);
                hash_str(&mut hasher, source_fingerprint);
            }
            None => hash_bool(&mut hasher, false),
        }
        hash_optional_str(&mut hasher, self.backend_proof_family_schema.as_deref());
        hash_optional_str(&mut hasher, self.backend_proof_family_target.as_deref());
        hash_optional_str(
            &mut hasher,
            self.backend_proof_family_obligation_set.as_deref(),
        );
        hash_optional_str(&mut hasher, self.backend_proof_family_policy_id.as_deref());
        match self.backend_proof_family_installable {
            Some(installable) => {
                hash_bool(&mut hasher, true);
                hash_bool(&mut hasher, installable);
            }
            None => hash_bool(&mut hasher, false),
        }
        hash_optional_str(
            &mut hasher,
            self.backend_proof_family_report_hash.as_deref(),
        );
        match &self.diagnostic_reason {
            Some(reason) => {
                hash_bool(&mut hasher, true);
                hash_str(&mut hasher, reason);
            }
            None => hash_bool(&mut hasher, false),
        }
        ArtifactChecksum::new(hasher.finish128())
    }

    fn is_accepted(&self) -> bool {
        self.verdict == ProofTvVerdict::Accepted && self.rejection_code.is_none()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BackendProofFamilyReportIdentity {
    schema: String,
    target: String,
    obligation_set: String,
    policy_id: String,
    installable: bool,
    report_hash: String,
}

/// Summary of proof material attached to an installed artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstallProofSummary {
    /// Stable compile-service proof-policy status.
    pub policy_status: ProofPolicyStatus,
    /// Stable proof rejection code when [`Self::policy_status`] is rejected.
    pub rejection_code: Option<ProofRejectionCode>,
    /// Number of lowering proof certificates returned by the compiler.
    pub lowering_certificate_count: usize,
    /// Number of lowering proof certificates marked verified.
    pub verified_lowering_certificate_count: usize,
    /// Number of JIT proof certificates attached to the executable buffer.
    pub jit_certificate_count: usize,
    /// Whether every attached JIT certificate reports verified.
    pub all_jit_certificates_verified: bool,
}

impl Default for InstallProofSummary {
    fn default() -> Self {
        Self {
            policy_status: ProofPolicyStatus::NotRequired,
            rejection_code: None,
            lowering_certificate_count: 0,
            verified_lowering_certificate_count: 0,
            jit_certificate_count: 0,
            all_jit_certificates_verified: false,
        }
    }
}

/// Counter snapshot for one installed entrypoint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CounterSummary {
    /// Canonical function symbol name.
    pub name: String,
    /// Function-entry call count when entry counters/profile hooks are present.
    pub entry_count: Option<u64>,
}

/// Installed executable-memory artifact retained by a downstream registry.
///
/// The handle owns the executable allocation through an [`Arc`]. Entrypoints
/// are exposed only through lifetime-bound [`ExecutableBuffer`] accessors so
/// callers do not persist raw function pointers beyond the buffer lifetime.
/// Those raw accessors are low-level compatibility hooks, not product
/// dispatch evidence. Product `ay`/`ty` callers should use
/// [`Self::get_contract_symbol_bound`] with the artifact manifest and a
/// [`SymbolLookupContract`] before native execution.
#[derive(Clone)]
pub struct InstalledArtifact {
    /// Executable buffer containing every compiled function.
    pub buffer: Arc<ExecutableBuffer>,
    /// Registry-facing install metadata.
    pub metadata: InstallMetadata,
}

impl fmt::Debug for InstalledArtifact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InstalledArtifact")
            .field("metadata", &self.metadata)
            .field("buffer_allocated_size", &self.buffer.allocated_size())
            .field("buffer_symbol_count", &self.buffer.symbol_count())
            .finish()
    }
}

impl InstalledArtifact {
    /// Create an installed artifact handle from executable memory and metadata.
    pub fn new(buffer: Arc<ExecutableBuffer>, metadata: InstallMetadata) -> Self {
        Self { buffer, metadata }
    }

    /// Create a minimal installed artifact handle from executable memory and replay metadata.
    ///
    /// This is intended for direct-JIT consumers that already own an
    /// [`ExecutableBuffer`] but did not route through [`CompileResponse`].
    /// The synthesized metadata is sufficient for replay-backed handoff
    /// evidence such as
    /// [`Self::petri_native_successor_compile_artifact_handoff_evidence`].
    /// It does not attach a manifest, native install-gate packet, or product
    /// install authority.
    pub fn from_executable_buffer_replay_metadata(
        buffer: Arc<ExecutableBuffer>,
        generation: CompileGeneration,
        replay_report_metadata: JitReplayReportMetadata,
    ) -> Self {
        let identity = installed_artifact_identity_from_replay_metadata(&replay_report_metadata);
        let artifact =
            artifact_metadata_from_executable_replay_metadata(&buffer, &replay_report_metadata);
        let exported_entrypoints =
            entrypoints_from_executable_replay_metadata(&replay_report_metadata);
        let functions = functions_from_executable_replay_metadata(&replay_report_metadata);
        let counters = exported_entrypoints
            .iter()
            .map(|entrypoint| CounterSummary {
                name: entrypoint.name.clone(),
                entry_count: buffer.entry_count(&entrypoint.name),
            })
            .collect();

        Self::new(
            buffer,
            InstallMetadata {
                generation,
                identity: identity.clone(),
                disposition: ArtifactInstallDisposition::ProfileOnly,
                artifact,
                artifact_manifest: None,
                replay_report_metadata: Some(replay_report_metadata),
                installed_payload_binding: None,
                compiled_at: SystemTime::now(),
                compile_latency: Duration::ZERO,
                exported_entrypoints,
                functions,
                proofs: InstallProofSummary::default(),
                proof_evidence_report: None,
                // The direct-JIT handoff route: the caller already owns an
                // executable buffer and never went through a compile request,
                // so no lowering proof, TV gate, or verifier ran here. Say so
                // explicitly rather than leaving the field empty.
                proof_evidence_summary: direct_jit_route_evidence(),
                native_install_gate_input: None,
                native_install_gate: None,
                proof_policy: ProofPolicy::disabled(),
                counters,
                raw_extern_bindings: Vec::new(),
            },
        )
    }

    /// Borrow a lifetime-bound raw entrypoint pointer from the owned buffer.
    ///
    /// This is a low-level/legacy escape hatch for wrappers, tests, fuzzing,
    /// or explicitly non-product/profile-only probes. It does not validate
    /// the artifact manifest, target/layout compatibility, ABI signature, or
    /// downstream invalidation state. Product dispatch should use
    /// [`Self::get_contract_symbol_bound`].
    pub fn entrypoint_ptr(&self, name: &str) -> Option<JitPtr<'_>> {
        self.buffer.get_fn_ptr_bound(name)
    }

    /// Reassert executable publication for the whole installed buffer before
    /// invoking a cached raw entrypoint.
    pub fn ensure_published_executable(&self) -> Result<(), JitError> {
        self.buffer.ensure_published_executable()
    }

    /// Record post-call useful-native telemetry under the installed gate packet.
    pub fn native_install_runtime_telemetry(
        &self,
        current: &NativeInstallGateRevalidationInput,
        native_call_succeeded: bool,
    ) -> Option<NativeInstallGateRuntimeTelemetryPacket> {
        let packet = self.metadata.native_install_gate.as_ref()?;
        Some(native_install_gate_runtime_telemetry(
            packet,
            Some(packet.packet_hash),
            current,
            native_call_succeeded,
        ))
    }

    /// Reassert executable publication for a cached raw entrypoint after
    /// proving that the pointer belongs to this artifact and exactly matches
    /// the named symbol.
    pub fn ensure_published_entrypoint_ptr(
        &self,
        name: &str,
        ptr: *const u8,
    ) -> Result<JitPtr<'_>, JitError> {
        self.buffer.ensure_published_symbol_ptr(name, ptr)
    }

    /// Borrow a lifetime-bound typed entrypoint from the owned buffer.
    ///
    /// This typed raw lookup checks the buffer lifetime but not the product
    /// artifact contract. It is non-product unless the caller has already
    /// guarded the symbol with a manifest-backed [`SymbolLookupContract`].
    /// Prefer [`Self::get_contract_symbol_bound`] for installable `ay`/`ty`
    /// native dispatch.
    ///
    /// # Safety
    /// `F` must match the compiled entrypoint's ABI.
    pub unsafe fn entrypoint<F: Copy>(&self, name: &str) -> Option<JitFn<'_, F>> {
        // SAFETY: forwarded to `ExecutableBuffer::get_fn_bound`; the caller
        // upholds the ABI contract for `F`.
        unsafe { self.buffer.get_fn_bound(name) }
    }

    /// Validate this installed artifact's manifest reference and borrow a typed
    /// contract symbol from the owned executable buffer.
    ///
    /// This is the supported lookup path for product native dispatch. It
    /// verifies the installed artifact's recorded manifest reference, then
    /// delegates to the executable buffer's manifest-backed symbol contract
    /// validation before returning a callable handle.
    pub fn get_contract_symbol_bound<'a, F: Copy>(
        &'a self,
        manifest: &'a ArtifactManifestV1,
        contract: &SymbolLookupContract,
    ) -> Result<TypedSymbol<'a, F>, ArtifactContractError> {
        validate_installed_payload_binding(&self.metadata, Some(manifest), &self.buffer)?;
        let binding = self
            .metadata
            .installed_payload_binding
            .as_ref()
            .ok_or_else(|| {
                installed_payload_binding_mismatch(
                    "callable lookup has no compiler-derived payload binding",
                )
            })?;
        let bound_symbol =
            find_installed_symbol(&binding.symbols, &contract.symbol).ok_or_else(|| {
                installed_payload_binding_mismatch(format!(
                    "callable `{}` is absent from the compiler-derived symbol binding",
                    contract.symbol
                ))
            })?;
        if bound_symbol.visibility != SymbolVisibility::Exported {
            return Err(installed_payload_binding_mismatch(format!(
                "callable `{}` resolves to compiler-private symbol `{}`",
                contract.symbol, bound_symbol.name
            )));
        }
        if bound_symbol.signature != contract.signature {
            return Err(ArtifactContractError::SignatureMismatch {
                symbol: contract.symbol.clone(),
                expected: contract.signature.clone(),
                actual: Some(bound_symbol.signature.clone()),
            });
        }
        self.buffer.get_contract_symbol_bound(manifest, contract)
    }

    /// Derive Petri native successor compile-artifact handoff evidence from this installed artifact.
    ///
    /// This is a metadata and publication-proof bridge only. It does not
    /// authorize Petri execution or call native code. It exposes the concrete
    /// fields TY/MCC needs for Trust Codegen's Petri handoff from the real installed
    /// native artifact: native payload digest, entry symbol, lifetime-bound
    /// callable pointer identity, executable-region identity, lifetime owner,
    /// and current generation. Missing inputs flow through the shared Petri
    /// handoff blocker vocabulary.
    pub fn petri_native_successor_compile_artifact_handoff_evidence(
        &self,
        entry_symbol: Option<&str>,
    ) -> PetriNativeSuccessorCompileArtifactHandoffEvidence {
        let replay = self.metadata.replay_report_metadata.as_ref();
        let native_payload_sha256 = replay
            .and_then(|report| report.properties.get("native_payload_sha256"))
            .map(String::as_str)
            .filter(|value| !value.trim().is_empty());
        let entry_symbol = entry_symbol
            .filter(|value| !value.trim().is_empty())
            .or_else(|| {
                replay
                    .and_then(|report| report.entry_symbol.as_deref())
                    .filter(|value| !value.trim().is_empty())
            })
            .or_else(|| {
                self.metadata
                    .exported_entrypoints
                    .first()
                    .map(|entrypoint| entrypoint.name.as_str())
                    .filter(|value| !value.trim().is_empty())
            });
        let publication = entry_symbol.and_then(|symbol| {
            let ptr = self.entrypoint_ptr(symbol)?;
            let proof = self
                .buffer
                .diagnose_published_symbol_ptr(symbol, ptr.as_ptr())
                .ok()?;
            let callable_pointer = PetriNativeSuccessorCallablePointer::from_ptr(ptr.as_ptr())?;
            Some((callable_pointer, proof))
        });
        let executable_region_sha256 = publication.as_ref().and_then(|(_, proof)| {
            let symbol = entry_symbol?;
            native_payload_sha256.map(|native_payload_sha256| {
                petri_native_successor_executable_region_sha256(
                    &self.metadata,
                    symbol,
                    native_payload_sha256,
                    proof,
                )
            })
        });
        let lifetime_owner = petri_native_successor_lifetime_owner(&self.metadata);
        let input = PetriNativeSuccessorCompileArtifactHandoffInput {
            native_payload_sha256,
            entry_symbol,
            callable_pointer: publication.map(|(callable_pointer, _)| callable_pointer),
            executable_region_sha256: executable_region_sha256.as_deref(),
            lifetime_owner: Some(lifetime_owner.as_str()),
            current_generation: Some(self.metadata.generation.get()),
        };

        petri_native_successor_compile_artifact_handoff_evidence(input)
    }

    /// Derive the callable lifetime proof for this installed artifact's Petri successor entrypoint.
    ///
    /// This proves that the non-null pointer came from the owned executable
    /// region and current install generation. It does not grant call authority;
    /// callers still need a Petri native-successor install packet and call
    /// packet before the runtime readiness join can become ready.
    pub fn petri_native_successor_callable_lifetime_proof(
        &self,
        entry_symbol: Option<&str>,
        expires_after_generation: Option<u64>,
    ) -> Option<PetriNativeSuccessorCallableLifetimeProof> {
        let evidence = self.petri_native_successor_compile_artifact_handoff_evidence(entry_symbol);
        if !evidence.is_ready() {
            return None;
        }

        PetriNativeSuccessorCallableLifetimeProof::new(
            evidence.callable_pointer?,
            evidence.executable_region_sha256?,
            evidence.lifetime_owner?,
            evidence.current_generation?,
            expires_after_generation,
        )
    }

    /// Join this installed artifact's lifetime evidence with Petri runtime readiness inputs.
    ///
    /// The installed artifact can supply the lifetime proof and, when a call
    /// packet exists, the stable ABI proof for that packet. The Petri
    /// native-successor install packet, trampoline, and call packet remain
    /// explicit inputs so a direct compile-install packet cannot be promoted to
    /// Petri runtime call authority.
    pub fn petri_native_successor_runtime_readiness_packet(
        &self,
        entry_symbol: Option<&str>,
        install_packet: Option<&NativeInstallGatePacket>,
        trampoline: Option<&PetriNativeSuccessorTrampolineContract>,
        call_packet: Option<&PetriNativeSuccessorCallPacket>,
        expires_after_generation: Option<u64>,
    ) -> PetriNativeSuccessorRuntimeReadinessPacket {
        let lifetime_proof = self
            .petri_native_successor_callable_lifetime_proof(entry_symbol, expires_after_generation);
        let runtime_abi_proof =
            call_packet.map(PetriNativeSuccessorRuntimeAbiProof::for_call_packet);

        petri_native_successor_runtime_readiness_packet(
            call_packet,
            install_packet,
            trampoline,
            lifetime_proof.as_ref(),
            runtime_abi_proof.as_ref(),
            self.metadata.generation.get(),
        )
    }
}

/// Opaque compiled artifact handle for the service state model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledArtifact {
    /// Stable identity.
    pub identity: ArtifactIdentity,
    /// Full deterministic artifact manifest, when supplied by the request.
    pub artifact_manifest: Option<ArtifactManifestV1>,
    /// Reproducibility metadata for the compiled artifact.
    pub provenance: ArtifactProvenance,
    /// Metadata about the artifact payload.
    pub metadata: ArtifactMetadata,
    /// Metadata used by downstream install registries.
    pub install: InstallMetadata,
}

impl CompiledArtifact {
    /// Create a metadata-only artifact for tests and early API integration.
    pub fn metadata_only(
        identity: impl Into<ArtifactIdentity>,
        generation: CompileGeneration,
    ) -> Self {
        Self::metadata_only_with(
            identity,
            generation,
            ArtifactProvenance::default(),
            ArtifactMetadata::default(),
        )
    }

    /// Create a metadata-only artifact with explicit provenance and metadata.
    pub fn metadata_only_with(
        identity: impl Into<ArtifactIdentity>,
        generation: CompileGeneration,
        provenance: ArtifactProvenance,
        metadata: ArtifactMetadata,
    ) -> Self {
        let identity = identity.into();
        Self {
            install: InstallMetadata {
                generation,
                identity: identity.clone(),
                disposition: ArtifactInstallDisposition::Installable,
                artifact: metadata.clone(),
                artifact_manifest: None,
                replay_report_metadata: None,
                installed_payload_binding: None,
                compiled_at: SystemTime::now(),
                compile_latency: Duration::ZERO,
                exported_entrypoints: Vec::new(),
                functions: Vec::new(),
                proofs: InstallProofSummary::default(),
                proof_evidence_report: None,
                // Metadata-only artifacts run no backend at all.
                proof_evidence_summary: direct_jit_route_evidence(),
                native_install_gate_input: None,
                native_install_gate: None,
                proof_policy: ProofPolicy::disabled(),
                counters: Vec::new(),
                raw_extern_bindings: provenance.raw_extern_bindings.clone(),
            },
            artifact_manifest: None,
            provenance,
            metadata,
            identity,
        }
    }

    /// Attach a full deterministic manifest and refresh all manifest references.
    pub fn with_artifact_manifest(mut self, manifest: ArtifactManifestV1) -> Self {
        self.attach_artifact_manifest(manifest);
        self
    }

    /// Attach a full deterministic manifest in place.
    pub fn attach_artifact_manifest(&mut self, manifest: ArtifactManifestV1) {
        let reference = ArtifactManifestReference::from_manifest(&manifest);
        self.metadata = self.metadata.clone().with_deterministic_manifest(&manifest);
        self.install.artifact = self.metadata.clone();
        self.install.artifact_manifest = Some(reference);
        self.artifact_manifest = Some(manifest);
    }
}

/// Per-function metadata for a compiled module artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionArtifactMetadata {
    /// Function symbol name as it appears in the trust_ir module or JIT buffer.
    pub name: String,
    /// Size of emitted code for this function when known.
    pub code_size_bytes: Option<usize>,
    /// Number of machine instructions for this function when known.
    pub instruction_count: Option<usize>,
    /// Number of spill slots allocated for this function when known.
    pub spill_slot_count: Option<usize>,
    /// Number of branch-like instructions for this function when known.
    pub branch_count: Option<usize>,
}

impl FunctionArtifactMetadata {
    fn from_trust_ir_name(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            code_size_bytes: None,
            instruction_count: None,
            spill_slot_count: None,
            branch_count: None,
        }
    }

    fn from_quality_metrics(metrics: &FunctionQualityMetrics) -> Self {
        Self {
            name: metrics.name.clone(),
            code_size_bytes: None,
            instruction_count: Some(metrics.instruction_count),
            spill_slot_count: Some(metrics.spill_slot_count),
            branch_count: Some(metrics.branch_count),
        }
    }
}

/// Relocatable object artifact payload.
#[derive(Debug, Clone)]
pub struct ObjectArtifactPayload {
    /// Target-format object bytes (Mach-O, ELF, or COFF) containing every
    /// compiled function.
    pub bytes: Vec<u8>,
    /// Module-level compilation metrics.
    pub metrics: CompilationMetrics,
    /// Optional compiler trace.
    pub trace: Option<CompilerTrace>,
    /// Optional proof certificates.
    pub proofs: Option<Vec<ProofCertificate>>,
    /// Per-function metadata for the module.
    pub functions: Vec<FunctionArtifactMetadata>,
    /// Compile artifact cache telemetry emitted by the service object path.
    pub compile_artifact_cache_telemetry: Vec<CompileArtifactCacheTelemetry>,
}

/// Executable-memory artifact payload.
#[derive(Clone)]
pub struct ExecutableArtifactPayload {
    /// Executable buffer containing every compiled function.
    pub buffer: Arc<ExecutableBuffer>,
    /// Module-level compilation metrics.
    pub metrics: CompilationMetrics,
    /// Optional compiler trace.
    pub trace: Option<CompilerTrace>,
    /// Optional proof certificates.
    pub proofs: Option<Vec<ProofCertificate>>,
    /// Per-function metadata for the module.
    pub functions: Vec<FunctionArtifactMetadata>,
}

impl fmt::Debug for ExecutableArtifactPayload {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ExecutableArtifactPayload")
            .field("buffer_allocated_size", &self.buffer.allocated_size())
            .field("buffer_symbol_count", &self.buffer.symbol_count())
            .field("metrics", &self.metrics)
            .field("trace", &self.trace)
            .field("proofs", &self.proofs)
            .field("functions", &self.functions)
            .finish()
    }
}

/// Concrete compiled artifact payload.
#[derive(Debug, Clone)]
pub enum ArtifactPayload {
    /// Relocatable object bytes.
    Object(ObjectArtifactPayload),
    /// Executable memory suitable for JIT calls.
    Executable(ExecutableArtifactPayload),
}

/// Compile diagnostic.
#[derive(Debug, Clone)]
pub struct CompileDiagnostic {
    /// Typed severity for log routing and error handling.
    pub severity: DiagnosticSeverity,
    /// Stable diagnostic code.
    pub code: &'static str,
    /// Human-readable diagnostic text.
    pub message: String,
    /// Optional function that produced the diagnostic.
    pub function: Option<String>,
    /// Optional service or backend phase.
    pub phase: Option<String>,
    /// Typed backend source error, when this diagnostic came from codegen/JIT.
    pub backend_error: Option<Arc<CompileError>>,
}

impl CompileDiagnostic {
    /// Create an error diagnostic.
    pub fn new(code: &'static str, message: impl Into<String>) -> Self {
        Self::error(code, message)
    }

    /// Create an error diagnostic.
    pub fn error(code: &'static str, message: impl Into<String>) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            code,
            message: message.into(),
            function: None,
            phase: None,
            backend_error: None,
        }
    }

    /// Attach a service or backend phase.
    pub fn with_phase(mut self, phase: impl Into<String>) -> Self {
        self.phase = Some(phase.into());
        self
    }

    /// Attach a typed backend source error.
    pub fn with_backend_error(mut self, error: CompileError) -> Self {
        self.backend_error = Some(Arc::new(error));
        self
    }
}

/// Stable reason code for non-compiled service responses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RejectCode {
    /// The request was cancelled before an installable artifact could be returned.
    Cancelled,
    /// The request generation was older than the effective stale-generation fence.
    StaleGeneration,
    /// The service rejected the request before backend work.
    Rejected,
    /// Compilation failed before producing an installable artifact.
    Failed,
}

impl RejectCode {
    /// Return the stable manifest/log string for this reject code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Cancelled => "cancelled",
            Self::StaleGeneration => "stale_generation",
            Self::Rejected => "rejected",
            Self::Failed => "failed",
        }
    }

    /// Return a stable diagnostic code to use when a response has no diagnostic.
    pub const fn default_diagnostic_code(self) -> &'static str {
        match self {
            Self::Cancelled => "compile.cancelled",
            Self::StaleGeneration => "compile.stale",
            Self::Rejected => "compile.rejected",
            Self::Failed => "compile.failed",
        }
    }

    fn from_status(status: CompileStatus) -> Option<Self> {
        match status {
            CompileStatus::Compiled => None,
            CompileStatus::Cancelled => Some(Self::Cancelled),
            CompileStatus::Stale => Some(Self::StaleGeneration),
            CompileStatus::Rejected => Some(Self::Rejected),
            CompileStatus::Failed => Some(Self::Failed),
        }
    }
}

/// Manifest-friendly explanation for a terminal non-compiled response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExplainReject {
    /// Stable high-level reason code.
    pub code: RejectCode,
    /// Terminal response status that produced this explanation.
    pub status: CompileStatus,
    /// Stable diagnostic code, falling back to the status-derived code.
    pub diagnostic_code: &'static str,
    /// Human-readable diagnostic text, when available.
    pub message: Option<String>,
    /// Service or backend phase, when available.
    pub phase: Option<String>,
}

/// Stable compile-service proof/install telemetry summary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofInstallTelemetrySummary {
    /// Summary schema name.
    pub schema: &'static str,
    /// Summary schema version.
    pub schema_version: u32,
    /// Terminal compile-service status.
    pub status: CompileStatus,
    /// Response-level install disposition.
    pub install_disposition: ArtifactInstallDisposition,
    /// Stable proof/install rejection category, when non-installable.
    pub rejection_category: Option<&'static str>,
    /// Stable proof/TV rejection code, when available.
    pub proof_tv_code: Option<&'static str>,
    /// Stable proof/TV verdict, when available.
    pub proof_tv_verdict: Option<&'static str>,
    /// Stable diagnostic code used to classify non-artifact outcomes.
    pub diagnostic_code: Option<&'static str>,
    /// Product native eligibility. True only for an accepted native install gate verdict.
    pub useful_native_eligible: bool,
    /// Count of useful-native installs attributed by this response.
    pub useful_native_count: u64,
    /// Rejection code or legacy issue gate blocking install authority.
    pub install_authority_blocked_on: Option<&'static str>,
    /// Shared native install gate disposition when an executable install was evaluated.
    pub native_install_gate_disposition: Option<&'static str>,
    /// Shared native install gate rejection code when one was produced.
    pub native_install_gate_code: Option<&'static str>,
}

impl ProofInstallTelemetrySummary {
    /// Current summary schema name.
    pub const SCHEMA: &'static str = "trust-cg.compile_service.proof_install_telemetry/v1";
    /// Current summary schema version.
    pub const SCHEMA_VERSION: u32 = 1;
}

/// Compile-service response.
#[derive(Debug, Clone)]
pub struct CompileResponse {
    /// Caller-supplied request id.
    pub request_id: CompileRequestId,
    /// Request generation.
    pub generation: CompileGeneration,
    /// Terminal status.
    pub status: CompileStatus,
    /// Response-level install disposition.
    pub disposition: ArtifactInstallDisposition,
    /// Compiled artifact metadata, present only for [`CompileStatus::Compiled`].
    pub artifact: Option<CompiledArtifact>,
    /// Concrete payload, present only for [`CompileStatus::Compiled`].
    pub payload: Option<ArtifactPayload>,
    /// Diagnostics collected while handling the request.
    pub diagnostics: Vec<CompileDiagnostic>,
}

impl CompileResponse {
    /// Return the stable reject code for non-compiled responses.
    pub fn reject_code(&self) -> Option<RejectCode> {
        RejectCode::from_status(self.status)
    }

    /// Explain why this response did not produce an installable artifact.
    ///
    /// The first error diagnostic is preferred. If a future caller constructs a
    /// non-compiled response without diagnostics, this still returns a stable
    /// status-derived diagnostic code.
    pub fn explain_reject(&self) -> Option<ExplainReject> {
        let code = self.reject_code()?;
        let diagnostic = self
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
            .or_else(|| self.diagnostics.first());

        Some(ExplainReject {
            code,
            status: self.status,
            diagnostic_code: diagnostic
                .map(|diagnostic| diagnostic.code)
                .unwrap_or_else(|| code.default_diagnostic_code()),
            message: diagnostic.map(|diagnostic| diagnostic.message.clone()),
            phase: diagnostic.and_then(|diagnostic| diagnostic.phase.clone()),
        })
    }

    /// Return a stable proof/install telemetry summary for direct
    /// compile-service consumers.
    pub fn proof_install_telemetry_summary(&self) -> ProofInstallTelemetrySummary {
        let diagnostic_code = self
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
            .or_else(|| self.diagnostics.first())
            .map(|diagnostic| diagnostic.code);
        let report = self
            .artifact
            .as_ref()
            .and_then(|artifact| artifact.install.proof_evidence_report.as_ref());
        let proof_tv_code = report
            .and_then(|report| report.rejection_code)
            .map(ProofTvRejectionCode::as_str)
            .or_else(|| diagnostic_code.and_then(proof_tv_code_from_diagnostic_code));
        let proof_tv_verdict = report
            .map(|report| report.verdict.as_str())
            .or_else(|| proof_tv_code.and_then(proof_tv_verdict_from_code));
        let native_install_gate = self.native_install_gate_packet();
        let useful_native_eligible = native_install_gate
            .as_ref()
            .is_some_and(|packet| packet.actions.useful_native_eligible);
        let install_authority_blocked_on = match native_install_gate.as_ref() {
            Some(packet) if packet.is_installable() => None,
            Some(packet) => packet
                .rejection_code
                .map(NativeInstallGateRejectionCode::as_str)
                .or(Some("native_install_gate")),
            None => Some("#681"),
        };

        ProofInstallTelemetrySummary {
            schema: ProofInstallTelemetrySummary::SCHEMA,
            schema_version: ProofInstallTelemetrySummary::SCHEMA_VERSION,
            status: self.status,
            install_disposition: self.disposition,
            rejection_category: proof_install_rejection_category(
                self,
                proof_tv_code,
                diagnostic_code,
                native_install_gate.as_ref(),
            ),
            proof_tv_code,
            proof_tv_verdict,
            diagnostic_code,
            useful_native_eligible,
            useful_native_count: 0,
            install_authority_blocked_on,
            native_install_gate_disposition: native_install_gate
                .as_ref()
                .map(|packet| packet.disposition.as_str()),
            native_install_gate_code: native_install_gate
                .as_ref()
                .and_then(|packet| packet.rejection_code)
                .map(NativeInstallGateRejectionCode::as_str),
        }
    }

    /// Return the shared native install gate packet for the direct compile
    /// install boundary, when this response carries executable memory.
    pub fn native_install_gate_packet(&self) -> Option<NativeInstallGatePacket> {
        self.native_install_gate_packet_for_surface(NativeInstallGateSurface::DirectCompileInstall)
    }

    /// Return the shared native install gate packet for a specific install
    /// surface when this response carries validated executable memory. Without
    /// an executable payload, only a canonically validated, fully blocked
    /// negative packet can be returned for rejection telemetry.
    pub fn native_install_gate_packet_for_surface(
        &self,
        surface: NativeInstallGateSurface,
    ) -> Option<NativeInstallGatePacket> {
        let artifact = self.artifact.as_ref()?;
        if let Some(ArtifactPayload::Executable(payload)) = &self.payload {
            validate_installed_payload_binding(
                &artifact.install,
                artifact.artifact_manifest.as_ref(),
                &payload.buffer,
            )
            .ok()?;
            return Some(native_install_gate_packet_for_artifact(artifact, surface));
        }
        blocked_native_install_gate_packet_for_reporting(
            artifact.install.native_install_gate.as_ref()?,
            surface,
        )
    }

    /// Convert a successful executable-memory response into an installed
    /// artifact handle.
    ///
    /// Returns `None` for non-compiled responses, object-only payloads, and
    /// artifacts whose disposition is not installable.
    pub fn into_installed_artifact(mut self) -> Option<InstalledArtifact> {
        if self.status != CompileStatus::Compiled {
            return None;
        }
        let mut artifact = self.artifact.take()?;
        let payload = match self.payload.take()? {
            ArtifactPayload::Executable(payload) => payload,
            ArtifactPayload::Object(_) => return None,
        };
        validate_installed_payload_binding(
            &artifact.install,
            artifact.artifact_manifest.as_ref(),
            &payload.buffer,
        )
        .ok()?;
        let packet = native_install_gate_packet_for_artifact(
            &artifact,
            NativeInstallGateSurface::DirectCompileInstall,
        );
        let current = artifact
            .artifact_manifest
            .as_ref()
            .map(NativeInstallGateRevalidationInput::from_manifest)
            .unwrap_or_else(|| NativeInstallGateRevalidationInput::from_packet(&packet));
        let verdict = validate_native_install_gate_packet_with_current(
            &packet,
            Some(packet.packet_hash),
            &current,
        );
        if !verdict.disposition.is_installable() || !verdict.actions.expose_callable {
            return None;
        }
        if self.disposition != ArtifactInstallDisposition::Installable {
            return None;
        }
        if artifact.install.disposition != ArtifactInstallDisposition::Installable {
            return None;
        }
        artifact.install.native_install_gate = Some(packet);
        Some(InstalledArtifact::new(payload.buffer, artifact.install))
    }
}

fn blocked_native_install_gate_packet_for_reporting(
    packet: &NativeInstallGatePacket,
    surface: NativeInstallGateSurface,
) -> Option<NativeInstallGatePacket> {
    if packet.surface != surface
        || !native_install_gate_packet_is_canonical_blocked_reporting_evidence(packet)
    {
        return None;
    }

    Some(packet.clone())
}

fn native_install_gate_packet_for_artifact(
    artifact: &CompiledArtifact,
    surface: NativeInstallGateSurface,
) -> NativeInstallGatePacket {
    // A stored packet is only historical evidence. Re-derive every decision
    // from this exact artifact's compiler-sealed binding and current negative
    // controls; accepting a same-surface packet here would allow a validated
    // artifact to lend its install authority to a different payload.
    let mut input = native_install_gate_input_for_artifact(artifact, surface);
    if let Some(packet) = artifact
        .install
        .native_install_gate
        .as_ref()
        .filter(|packet| packet.surface == surface)
    {
        preserve_stored_native_install_gate_negative_controls(&mut input, packet);
    }
    validate_native_install_gate(&input)
}

fn preserve_stored_native_install_gate_negative_controls(
    input: &mut NativeInstallGateInput,
    packet: &NativeInstallGatePacket,
) {
    if !packet.disposition.is_installable()
        || packet.actions != NativeInstallGateActions::for_surface(input.surface)
    {
        input.candidate_disposition = if packet.disposition.is_installable() {
            NativeInstallGateDisposition::Rejected
        } else {
            packet.disposition
        };
    }
    // Historical freshness evidence is deny-only. A fresh stored packet must
    // never repair a stale live input, while either side's stale generation
    // must remain stale after the merge. When only the packet is stale, pick
    // one member of its mismatched pair that differs from the live artifact
    // generation so the re-derived decision necessarily fails closed.
    let input_generation_is_fresh = input.current_generation == input.artifact_generation
        && input.current_generation == input.expected.current_generation;
    let packet_generation_is_stale =
        packet.freshness.current_generation != packet.freshness.artifact_generation;
    if input_generation_is_fresh && packet_generation_is_stale {
        input.current_generation =
            if packet.freshness.current_generation != input.artifact_generation {
                packet.freshness.current_generation
            } else {
                packet.freshness.artifact_generation
            };
    }
    input.revoked |= packet.freshness.revoked;
    if let Some(stored_active_deny) = packet
        .freshness
        .deny_control
        .as_ref()
        .filter(|deny| deny.active)
    {
        match input.deny_control.as_ref().filter(|deny| deny.active) {
            None => input.deny_control = Some(stored_active_deny.clone()),
            Some(live_active_deny) if live_active_deny != stored_active_deny => {
                // The input model carries one deny packet, so two distinct
                // active controls cannot be represented simultaneously. Do
                // not select one and risk dropping the other's matching
                // scope; an unrepresentable active-deny union is itself a
                // fail-closed conflict.
                input.candidate_disposition = NativeInstallGateDisposition::Rejected;
            }
            Some(_) => {}
        }
    }
    if packet.replay_identity.is_none() {
        input.replay_identity = None;
    }
    if packet.telemetry.is_none() {
        input.telemetry = None;
    }
}

fn native_install_gate_input_for_artifact(
    artifact: &CompiledArtifact,
    surface: NativeInstallGateSurface,
) -> NativeInstallGateInput {
    let expected = native_install_expected_bindings(artifact);
    let manifest = artifact.artifact_manifest.clone();
    let manifest_reference = artifact.install.artifact_manifest.clone();
    let artifact_generation = artifact.install.generation.get();
    let supplied = artifact.install.native_install_gate_input.as_ref();
    let consumer = supplied
        .map(|input| input.consumer.clone())
        .unwrap_or_else(|| native_install_consumer(artifact).to_owned());
    let consumer_mode = supplied
        .map(|input| input.consumer_mode.clone())
        .unwrap_or_else(|| native_install_consumer_mode(artifact).to_owned());
    let payload_identity = native_install_payload_identity(artifact);
    let proof_evidence = if supplied.is_some_and(|input| input.proof_evidence.is_none()) {
        None
    } else {
        native_install_proof_evidence(artifact)
    };
    let layout_evidence = if supplied.is_some_and(|input| input.layout_evidence.is_none()) {
        None
    } else {
        native_install_layout_evidence_for_artifact(artifact, surface)
    };
    let replay_identity = native_install_replay_identity_for_artifact(
        artifact,
        &consumer,
        &consumer_mode,
        &expected,
        &payload_identity,
    );
    let telemetry = native_install_telemetry_for_artifact(
        &consumer,
        &consumer_mode,
        surface,
        &expected,
        proof_evidence.as_ref(),
    );

    NativeInstallGateInput {
        consumer,
        consumer_mode,
        surface,
        candidate_disposition: supplied
            .map(|input| input.candidate_disposition)
            .filter(|_| {
                synthesized_native_install_disposition(artifact)
                    == NativeInstallGateDisposition::Installable
            })
            .unwrap_or_else(|| synthesized_native_install_disposition(artifact)),
        requested_authority: NativeInstallGateAuthority::CanaryCallable,
        manifest,
        manifest_reference,
        expected: expected.clone(),
        payload_identity: payload_identity.clone(),
        candidate_payload_identity: payload_identity,
        layout_evidence,
        proof_evidence,
        current_invalidation_checksum: supplied
            .map(|input| input.current_invalidation_checksum)
            .unwrap_or(expected.invalidation_checksum),
        artifact_generation,
        current_generation: supplied
            .map(|input| input.current_generation)
            .unwrap_or(expected.current_generation),
        revoked: supplied.is_some_and(|input| input.revoked),
        deny_control: supplied.and_then(|input| input.deny_control.clone()),
        replay_identity: supplied
            .is_none_or(|input| input.replay_identity.is_some())
            .then_some(replay_identity),
        telemetry: supplied
            .is_none_or(|input| input.telemetry.is_some())
            .then_some(telemetry),
    }
}

fn native_install_layout_evidence_for_artifact(
    artifact: &CompiledArtifact,
    surface: NativeInstallGateSurface,
) -> Option<NativeInstallGateLayoutEvidence> {
    if surface != NativeInstallGateSurface::DirectCompileInstall {
        return None;
    }

    let manifest = artifact.artifact_manifest.as_ref()?;
    let binding = artifact.install.installed_payload_binding.as_ref()?;
    if !binding.has_canonical_binding_sha256(Some(manifest))
        || binding.manifest_checksum != Some(manifest.checksum())
    {
        return None;
    }
    let generation_domain = "compile_service_executable_generation";
    let executable_region = "executable_text";
    let byte_len = binding.code_size_bytes;
    let entry_abis = if artifact.install.exported_entrypoints.is_empty() {
        vec![native_install_entry_abi(
            "compiled_artifact",
            binding.authoritative_abi.checksum(),
            executable_region,
            generation_domain,
        )]
    } else {
        artifact
            .install
            .exported_entrypoints
            .iter()
            .map(|entrypoint| {
                native_install_entry_abi(
                    &entrypoint.name,
                    binding.authoritative_abi.checksum(),
                    executable_region,
                    generation_domain,
                )
            })
            .collect()
    };

    Some(
        NativeInstallGateLayoutEvidence {
            layout_checksum: binding.authoritative_layout.checksum(),
            abi_checksum: binding.authoritative_abi.checksum(),
            invalidation_checksum: manifest.invalidation.checksum(),
            validation_provenance: "trust-cg.compile_service.direct_executable_layout.v1"
                .to_owned(),
            evidence_sha256: None,
            wrapper_identity: Some(format!(
                "trust-cg.compile_service.direct_executable:{}:{}",
                artifact.metadata.target.name(),
                artifact.identity.as_str()
            )),
            regions: vec![NativeInstallGateLayoutEvidence::region(
                executable_region,
                "native_executable_allocation",
                1,
                byte_len,
                NativeInstallGateLayoutAccess::ReadOnly,
                "native_executable_code",
                generation_domain,
            )],
            entry_abis,
        }
        .with_canonical_evidence_sha256(),
    )
}

fn native_install_entry_abi(
    name: &str,
    abi_checksum: ArtifactChecksum,
    executable_region: &str,
    generation_domain: &str,
) -> NativeInstallGateLayoutEntryAbiEvidence {
    NativeInstallGateLayoutEntryAbiEvidence {
        name: name.to_owned(),
        abi: "trust-cg-direct-executable-entry".to_owned(),
        abi_checksum,
        argument_regions: vec![executable_region.to_owned()],
        status_region: None,
        generation_domain: generation_domain.to_owned(),
    }
}

fn native_install_replay_identity_for_artifact(
    artifact: &CompiledArtifact,
    consumer: &str,
    consumer_mode: &str,
    expected: &NativeInstallGateExpectedBindings,
    payload_identity: &NativeInstallGatePayloadIdentity,
) -> NativeInstallGateReplayIdentity {
    NativeInstallGateReplayIdentity {
        schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
        replay_root_sha256: native_install_replay_root_sha256(artifact, expected, payload_identity),
        replay_consumer: consumer.to_owned(),
        replay_family: consumer_mode.to_owned(),
        artifact_id: expected.artifact_id.clone(),
        source_sha256: payload_identity.source_sha256.clone(),
        trust_ir_sha256: payload_identity.trust_ir_sha256.clone(),
        native_payload_sha256: payload_identity.native_payload_sha256.clone(),
        replay_record_sha256: String::new(),
    }
    .with_canonical_record_sha256()
}

fn native_install_replay_root_sha256(
    artifact: &CompiledArtifact,
    expected: &NativeInstallGateExpectedBindings,
    payload_identity: &NativeInstallGatePayloadIdentity,
) -> String {
    let mut bytes = Vec::new();
    push_native_install_replay_field(
        &mut bytes,
        "trust-cg.compile_service.native_install_replay_root.v1",
    );
    push_native_install_replay_field(&mut bytes, artifact.identity.as_str());
    push_native_install_replay_field(&mut bytes, &expected.artifact_id);
    push_native_install_replay_field(&mut bytes, &expected.manifest_checksum.to_string());
    push_native_install_replay_field(&mut bytes, &expected.target_checksum.to_string());
    push_native_install_replay_field(&mut bytes, &expected.abi_checksum.to_string());
    push_native_install_replay_field(&mut bytes, &expected.layout_checksum.to_string());
    push_native_install_replay_field(&mut bytes, &expected.proof_policy_checksum.to_string());
    push_native_install_replay_field(&mut bytes, &expected.invalidation_checksum.to_string());
    push_native_install_replay_field(&mut bytes, &payload_identity.source_sha256);
    push_native_install_replay_field(&mut bytes, &payload_identity.trust_ir_sha256);
    push_native_install_replay_field(&mut bytes, &payload_identity.native_payload_sha256);
    push_native_install_replay_field(&mut bytes, &artifact.install.generation.get().to_string());
    format!("sha256:{}", sha256_hex(&bytes))
}

fn push_native_install_replay_field(bytes: &mut Vec<u8>, field: &str) {
    bytes.extend_from_slice(&(field.len() as u64).to_le_bytes());
    bytes.extend_from_slice(field.as_bytes());
}

fn installed_artifact_identity_from_replay_metadata(
    replay: &JitReplayReportMetadata,
) -> ArtifactIdentity {
    if let Some(artifact_id) = replay
        .artifact_id
        .as_deref()
        .filter(|artifact_id| !artifact_id.trim().is_empty())
    {
        return ArtifactIdentity::new(artifact_id);
    }
    if let Some(native_payload_sha256) = replay
        .properties
        .get("native_payload_sha256")
        .filter(|native_payload_sha256| !native_payload_sha256.trim().is_empty())
    {
        return ArtifactIdentity::new(format!("trust-cg-installed-replay:{native_payload_sha256}"));
    }

    ArtifactIdentity::new(format!(
        "trust-cg-installed-replay:{}",
        executable_replay_metadata_sha256(replay)
    ))
}

fn artifact_metadata_from_executable_replay_metadata(
    buffer: &ExecutableBuffer,
    replay: &JitReplayReportMetadata,
) -> ArtifactMetadata {
    let mut metadata = ArtifactMetadata::from_profile(
        &CompileProfile::HostJitFast,
        ArtifactKind::ExecutableMemory,
    );
    metadata.target = Target::host();
    metadata.code_size_bytes = usize::try_from(replay.code_size).unwrap_or(usize::MAX);
    metadata.allocation_size_bytes = Some(buffer.allocated_size());
    metadata
}

fn entrypoints_from_executable_replay_metadata(
    replay: &JitReplayReportMetadata,
) -> Vec<EntryPointMetadata> {
    let mut entrypoints: Vec<_> = replay
        .symbols
        .iter()
        .map(|symbol| EntryPointMetadata {
            name: symbol.name.clone(),
            offset_bytes: symbol.range.start_offset,
        })
        .collect();
    entrypoints.sort_by(|left, right| left.name.cmp(&right.name));
    entrypoints
}

fn functions_from_executable_replay_metadata(
    replay: &JitReplayReportMetadata,
) -> Vec<FunctionArtifactMetadata> {
    let mut functions: Vec<_> = replay
        .symbols
        .iter()
        .map(|symbol| FunctionArtifactMetadata {
            name: symbol.name.clone(),
            code_size_bytes: Some(usize::try_from(symbol.range.byte_len()).unwrap_or(usize::MAX)),
            instruction_count: None,
            spill_slot_count: None,
            branch_count: None,
        })
        .collect();
    functions.sort_by(|left, right| left.name.cmp(&right.name));
    functions
}

fn executable_replay_metadata_sha256(replay: &JitReplayReportMetadata) -> String {
    let mut bytes = Vec::new();
    push_native_install_replay_field(
        &mut bytes,
        "trust-cg.compile_service.executable_replay_metadata_identity.v1",
    );
    push_native_install_replay_field(&mut bytes, &replay.schema);
    push_native_install_replay_field(&mut bytes, &replay.schema_version.to_string());
    push_native_install_replay_field(&mut bytes, &replay.producer);
    push_native_install_replay_field(&mut bytes, replay.artifact_id.as_deref().unwrap_or(""));
    push_native_install_replay_field(&mut bytes, replay.target.as_deref().unwrap_or(""));
    push_native_install_replay_field(&mut bytes, replay.entry_symbol.as_deref().unwrap_or(""));
    push_native_install_replay_field(&mut bytes, &replay.code_size.to_string());
    for (key, value) in &replay.properties {
        push_native_install_replay_field(&mut bytes, key);
        push_native_install_replay_field(&mut bytes, value);
    }
    for symbol in &replay.symbols {
        push_native_install_replay_field(&mut bytes, &symbol.name);
        push_native_install_replay_field(&mut bytes, &symbol.range.start_offset.to_string());
        push_native_install_replay_field(&mut bytes, &symbol.range.end_offset.to_string());
        for alias in &symbol.aliases {
            push_native_install_replay_field(&mut bytes, alias);
        }
    }
    format!("sha256:{}", sha256_hex(&bytes))
}

fn petri_native_successor_lifetime_owner(metadata: &InstallMetadata) -> String {
    format!(
        "trust-cg.compile_service.installed_artifact:{}:{}",
        metadata.identity.as_str(),
        metadata.generation.get()
    )
}

fn petri_native_successor_executable_region_sha256(
    metadata: &InstallMetadata,
    entry_symbol: &str,
    native_payload_sha256: &str,
    proof: &JitSymbolPublicationProof,
) -> String {
    let mut bytes = Vec::new();
    push_native_install_replay_field(
        &mut bytes,
        "trust-cg.compile_service.petri_native_successor.executable_region.v1",
    );
    push_native_install_replay_field(&mut bytes, metadata.identity.as_str());
    push_native_install_replay_field(&mut bytes, &metadata.generation.get().to_string());
    push_native_install_replay_field(&mut bytes, entry_symbol);
    push_native_install_replay_field(&mut bytes, native_payload_sha256);
    push_native_install_replay_field(&mut bytes, &proof.symbol);
    push_native_install_replay_field(&mut bytes, &proof.pointer.to_string());
    push_native_install_replay_field(&mut bytes, &proof.buffer_base.to_string());
    push_native_install_replay_field(&mut bytes, &proof.buffer_end.to_string());
    push_native_install_replay_field(&mut bytes, &proof.code_len.to_string());
    push_native_install_replay_field(&mut bytes, &proof.published_len.to_string());
    push_native_install_replay_field(&mut bytes, &proof.allocation_len.to_string());
    push_native_install_replay_field(&mut bytes, &proof.expected_symbol_offset.to_string());
    push_native_install_replay_field(&mut bytes, &proof.actual_ptr_offset.to_string());
    push_native_install_replay_field(&mut bytes, proof.exact_symbol_match.to_string().as_str());
    push_native_install_replay_field(
        &mut bytes,
        proof.publication_contract.map_jit.to_string().as_str(),
    );
    push_native_install_replay_field(
        &mut bytes,
        proof
            .publication_contract
            .write_protect_supported
            .to_string()
            .as_str(),
    );
    push_native_install_replay_field(
        &mut bytes,
        proof.publication_contract.published_rx.to_string().as_str(),
    );
    push_native_install_replay_field(&mut bytes, proof.mprotect_rx_ok.to_string().as_str());
    push_native_install_replay_field(
        &mut bytes,
        proof.execute_mode_reasserted.to_string().as_str(),
    );
    let first_code_sha256 = proof
        .first_code_bytes
        .as_deref()
        .map(|bytes| format!("sha256:{}", sha256_hex(bytes)))
        .unwrap_or_else(|| "none".to_owned());
    push_native_install_replay_field(&mut bytes, &first_code_sha256);
    format!("sha256:{}", sha256_hex(&bytes))
}

fn native_install_telemetry_for_artifact(
    consumer: &str,
    consumer_mode: &str,
    surface: NativeInstallGateSurface,
    expected: &NativeInstallGateExpectedBindings,
    proof_evidence: Option<&NativeInstallGateProofEvidence>,
) -> NativeInstallGateTelemetryInput {
    NativeInstallGateTelemetryInput {
        schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
        event_id: format!(
            "compile-service-native-install:{}:{}",
            surface.as_str(),
            expected.artifact_id
        ),
        counter_scope: native_install_counter_scope(consumer, consumer_mode, surface, expected),
        record_sha256: String::new(),
        artifact_id: expected.artifact_id.clone(),
        manifest_checksum: expected.manifest_checksum,
        proof_report_sha256: proof_evidence.and_then(|proof| proof.proof_report_sha256.clone()),
        layout_checksum: expected.layout_checksum,
        invalidation_checksum: expected.invalidation_checksum,
        disposition: NativeInstallGateDisposition::Installable,
        rejection_code: None,
        install_authority: NativeInstallGateAuthority::CanaryCallable,
        useful_native_delta: 0,
    }
    .with_canonical_record_sha256()
}

fn native_install_counter_scope(
    consumer: &str,
    consumer_mode: &str,
    surface: NativeInstallGateSurface,
    expected: &NativeInstallGateExpectedBindings,
) -> String {
    format!(
        "{}:{}:{}:{}",
        consumer,
        consumer_mode,
        surface.as_str(),
        expected.artifact_id
    )
}

fn native_install_expected_bindings(
    artifact: &CompiledArtifact,
) -> NativeInstallGateExpectedBindings {
    if let (Some(binding), Some(manifest), Some(reference)) = (
        artifact.install.installed_payload_binding.as_ref(),
        artifact.artifact_manifest.as_ref(),
        artifact.install.artifact_manifest.as_ref(),
    ) && binding.has_canonical_binding_sha256(Some(manifest))
        && binding.manifest_checksum == Some(manifest.checksum())
        && reference.manifest_checksum == manifest.checksum()
    {
        return NativeInstallGateExpectedBindings {
            artifact_id: manifest.artifact_id.clone(),
            // The whole-manifest checksum remains the separate caller contract
            // binding. Machine authority below comes only from the private,
            // compiler-sealed payload binding.
            manifest_checksum: manifest.checksum(),
            target_checksum: binding.authoritative_target.checksum(),
            abi_checksum: binding.authoritative_abi.checksum(),
            layout_checksum: binding.authoritative_layout.checksum(),
            proof_policy_checksum: manifest.proof_policy.checksum(),
            invalidation_checksum: manifest.invalidation.checksum(),
            current_generation: artifact.install.generation.get(),
        };
    }

    NativeInstallGateExpectedBindings {
        artifact_id: artifact.identity.as_str().to_owned(),
        manifest_checksum: ArtifactChecksum::new(0),
        target_checksum: ArtifactChecksum::new(0),
        abi_checksum: ArtifactChecksum::new(0),
        layout_checksum: ArtifactChecksum::new(0),
        proof_policy_checksum: artifact.install.proof_policy.checksum(),
        invalidation_checksum: ArtifactChecksum::new(0),
        current_generation: artifact.install.generation.get(),
    }
}

fn synthesized_native_install_disposition(
    artifact: &CompiledArtifact,
) -> NativeInstallGateDisposition {
    let binding_is_valid = artifact
        .install
        .installed_payload_binding
        .as_ref()
        .is_some_and(|binding| {
            binding.artifact_kind == ArtifactKind::ExecutableMemory
                && binding.has_canonical_binding_sha256(artifact.artifact_manifest.as_ref())
                && binding.manifest_checksum
                    == artifact
                        .artifact_manifest
                        .as_ref()
                        .map(ArtifactManifestV1::checksum)
        });
    if !binding_is_valid {
        return NativeInstallGateDisposition::Rejected;
    }
    match artifact.install.disposition {
        ArtifactInstallDisposition::ProfileOnly => NativeInstallGateDisposition::ProfileOnly,
        ArtifactInstallDisposition::Installable => NativeInstallGateDisposition::Installable,
        ArtifactInstallDisposition::Rejected => NativeInstallGateDisposition::Rejected,
    }
}

fn native_install_consumer(artifact: &CompiledArtifact) -> &str {
    artifact
        .provenance
        .caller_context
        .get("native_install_consumer")
        .or_else(|| artifact.provenance.caller_context.get("consumer"))
        .map(String::as_str)
        .unwrap_or("ay")
}

fn native_install_consumer_mode(artifact: &CompiledArtifact) -> &str {
    artifact
        .provenance
        .caller_context
        .get("native_install_consumer_mode")
        .map(String::as_str)
        .unwrap_or("direct_compile")
}

fn native_install_payload_identity(
    artifact: &CompiledArtifact,
) -> NativeInstallGatePayloadIdentity {
    let source_sha256 = artifact
        .provenance
        .source_fingerprint
        .clone()
        .unwrap_or_else(|| artifact.identity.as_str().to_owned());
    let trust_ir_sha256 = artifact
        .install
        .installed_payload_binding
        .as_ref()
        .filter(|binding| binding.has_canonical_binding_sha256(artifact.artifact_manifest.as_ref()))
        .map(|binding| binding.trust_ir_module_sha256.clone())
        .unwrap_or_default();
    let native_payload_sha256 = artifact
        .install
        .installed_payload_binding
        .as_ref()
        .filter(|binding| binding.has_canonical_binding_sha256(artifact.artifact_manifest.as_ref()))
        .map(|binding| binding.native_payload_sha256.clone())
        .unwrap_or_default();

    NativeInstallGatePayloadIdentity {
        source_sha256,
        trust_ir_sha256,
        native_payload_sha256,
    }
}

fn native_install_proof_evidence(
    artifact: &CompiledArtifact,
) -> Option<NativeInstallGateProofEvidence> {
    let report = artifact.install.proof_evidence_report.as_ref()?;
    let manifest = artifact.artifact_manifest.as_ref()?;
    let (mut summary, proof_report_sha256) = match report.verdict {
        ProofTvVerdict::Accepted if report.rejection_code.is_none() => (
            ProofEvidenceSummary::verified(
                "compile_service.proof_tv",
                manifest.target.checksum(),
                manifest.abi.checksum(),
                manifest.layout.checksum(),
                manifest.invalidation.checksum(),
                manifest.proof_policy.checksum(),
            ),
            Some(report.report_hash.to_string()),
        ),
        _ => {
            let (verdict, code) = native_install_proof_rejection(report);
            (
                ProofEvidenceSummary::rejected(
                    "compile_service.proof_tv",
                    verdict,
                    code,
                    manifest.target.checksum(),
                    manifest.abi.checksum(),
                    manifest.layout.checksum(),
                    manifest.invalidation.checksum(),
                    manifest.proof_policy.checksum(),
                ),
                Some(report.report_hash.to_string()),
            )
        }
    };
    attach_backend_proof_family_evidence_metadata(&mut summary, report);
    let payload_identity = native_install_payload_identity(artifact);

    Some(NativeInstallGateProofEvidence {
        summary,
        proof_report_sha256,
        obligation_set: Some(format!(
            "compile-service-direct-install:{}",
            artifact.identity.as_str()
        )),
        timeout_ms: Some(
            artifact
                .install
                .compile_latency
                .as_millis()
                .min(u128::from(u64::MAX)) as u64,
        ),
        native_payload_sha256: Some(payload_identity.native_payload_sha256),
    })
}

fn attach_backend_proof_family_evidence_metadata(
    summary: &mut ProofEvidenceSummary,
    report: &ProofTvEvidenceReportV1,
) {
    let Some(schema) = &report.backend_proof_family_schema else {
        return;
    };
    summary
        .metadata
        .insert("backend_proof_family_schema".to_owned(), schema.clone());
    if let Some(target) = &report.backend_proof_family_target {
        summary
            .metadata
            .insert("backend_proof_family_target".to_owned(), target.clone());
    }
    if let Some(obligation_set) = &report.backend_proof_family_obligation_set {
        summary.metadata.insert(
            "backend_proof_family_obligation_set".to_owned(),
            obligation_set.clone(),
        );
    }
    if let Some(policy_id) = &report.backend_proof_family_policy_id {
        summary.metadata.insert(
            "backend_proof_family_policy_id".to_owned(),
            policy_id.clone(),
        );
    }
    if let Some(installable) = report.backend_proof_family_installable {
        summary.metadata.insert(
            "backend_proof_family_installable".to_owned(),
            installable.to_string(),
        );
    }
    if let Some(report_hash) = &report.backend_proof_family_report_hash {
        summary.metadata.insert(
            "backend_proof_family_report_hash".to_owned(),
            report_hash.clone(),
        );
    }
}

fn native_install_proof_rejection(
    report: &ProofTvEvidenceReportV1,
) -> (ProofEvidenceVerdict, ProofEvidenceRejectionCode) {
    match report.rejection_code {
        Some(ProofTvRejectionCode::MissingEvidence) => (
            ProofEvidenceVerdict::MissingEvidence,
            ProofEvidenceRejectionCode::MissingEvidence,
        ),
        Some(ProofTvRejectionCode::VerifierFailure) => (
            ProofEvidenceVerdict::VerifierFailure,
            ProofEvidenceRejectionCode::VerifierFailure,
        ),
        Some(ProofTvRejectionCode::Timeout) => (
            ProofEvidenceVerdict::Timeout,
            ProofEvidenceRejectionCode::Timeout,
        ),
        Some(ProofTvRejectionCode::Unknown) => (
            ProofEvidenceVerdict::Unknown,
            ProofEvidenceRejectionCode::Unknown,
        ),
        Some(ProofTvRejectionCode::SolverError) => (
            ProofEvidenceVerdict::SolverError,
            ProofEvidenceRejectionCode::SolverError,
        ),
        Some(ProofTvRejectionCode::UnsupportedRoute) => (
            ProofEvidenceVerdict::UnsupportedRoute,
            ProofEvidenceRejectionCode::UnsupportedRoute,
        ),
        Some(ProofTvRejectionCode::UnsupportedTarget) => (
            ProofEvidenceVerdict::UnsupportedTarget,
            ProofEvidenceRejectionCode::UnsupportedTarget,
        ),
        Some(ProofTvRejectionCode::StaleEvidence) => (
            ProofEvidenceVerdict::StaleEvidence,
            ProofEvidenceRejectionCode::StaleEvidence,
        ),
        Some(ProofTvRejectionCode::MalformedReport) => (
            ProofEvidenceVerdict::MalformedReport,
            ProofEvidenceRejectionCode::MalformedReport,
        ),
        Some(ProofTvRejectionCode::MissingRequiredFields) => (
            ProofEvidenceVerdict::MissingRequiredFields,
            ProofEvidenceRejectionCode::MissingRequiredFields,
        ),
        None => (
            ProofEvidenceVerdict::UnknownSolverError,
            ProofEvidenceRejectionCode::UnknownSolverError,
        ),
    }
}

fn proof_install_rejection_category(
    response: &CompileResponse,
    proof_tv_code: Option<&'static str>,
    diagnostic_code: Option<&'static str>,
    native_install_gate: Option<&NativeInstallGatePacket>,
) -> Option<&'static str> {
    if native_install_gate.is_some_and(|packet| !packet.is_installable()) {
        return Some("native_install_gate");
    }

    match response.status {
        CompileStatus::Cancelled => Some("cancelled"),
        CompileStatus::Stale => Some("stale"),
        CompileStatus::Failed => proof_tv_code
            .and_then(proof_install_rejection_category_from_proof_tv_code)
            .or(Some("compile_failed")),
        CompileStatus::Rejected => proof_tv_code
            .and_then(proof_install_rejection_category_from_proof_tv_code)
            .or_else(|| diagnostic_code.and_then(proof_install_rejection_category_from_diagnostic))
            .or(Some("rejected")),
        CompileStatus::Compiled => match response.disposition {
            ArtifactInstallDisposition::Installable => {
                if policy_mode_is_disabled_or_audit(response) {
                    Some("disabled_or_audit_only")
                } else {
                    None
                }
            }
            ArtifactInstallDisposition::ProfileOnly => Some("profile_only"),
            ArtifactInstallDisposition::Rejected => proof_tv_code
                .and_then(proof_install_rejection_category_from_proof_tv_code)
                .or(Some("proof_rejected")),
        },
    }
}

fn proof_tv_code_from_diagnostic_code(code: &'static str) -> Option<&'static str> {
    match code {
        "proof_missing_evidence"
        | "proof_verifier_failure"
        | "proof_timeout"
        | "proof_unknown"
        | "proof_solver_error"
        | "proof_unsupported_route"
        | "proof_unsupported_target"
        | "proof_stale_evidence"
        | "proof_malformed_report"
        | "proof_missing_required_fields" => Some(code),
        _ => None,
    }
}

fn proof_tv_verdict_from_code(code: &'static str) -> Option<&'static str> {
    Some(match code {
        "proof_missing_evidence" => "missing_evidence",
        "proof_verifier_failure" => "verifier_failure",
        "proof_timeout" => "timeout",
        "proof_unknown" => "unknown",
        "proof_solver_error" => "solver_error",
        "proof_unsupported_route" => "unsupported_route",
        "proof_unsupported_target" => "unsupported_target",
        "proof_stale_evidence" => "stale_evidence",
        "proof_malformed_report" => "malformed_report",
        "proof_missing_required_fields" => "missing_required_fields",
        _ => return None,
    })
}

fn proof_install_rejection_category_from_proof_tv_code(code: &'static str) -> Option<&'static str> {
    Some(match code {
        "proof_missing_evidence" => "missing_evidence",
        "proof_verifier_failure" => "proof_rejected",
        "proof_timeout" => "timeout",
        "proof_unknown" => "unknown",
        "proof_solver_error" => "solver_error",
        "proof_unsupported_route" => "unsupported_route",
        "proof_unsupported_target" => "unsupported_target",
        "proof_stale_evidence" => "stale_evidence",
        "proof_malformed_report" => "malformed_report",
        "proof_missing_required_fields" => "missing_required_fields",
        _ => return None,
    })
}

fn proof_install_rejection_category_from_diagnostic(code: &'static str) -> Option<&'static str> {
    Some(match code {
        "compile.stale" => "stale",
        "compile.cancelled" => "cancelled",
        "compile.failed" | "compile.backend" => "compile_failed",
        _ => return None,
    })
}

fn policy_mode_is_disabled_or_audit(response: &CompileResponse) -> bool {
    response.artifact.as_ref().is_some_and(|artifact| {
        matches!(
            artifact.install.proof_policy.mode,
            ProofMode::Disabled | ProofMode::AuditOnly
        )
    })
}

/// Runtime-neutral compile-service facade.
#[derive(Debug, Clone)]
pub struct CompileService {
    config: CompileServiceConfig,
}

impl CompileService {
    /// Create a compile service.
    pub fn new(config: CompileServiceConfig) -> Self {
        Self { config }
    }

    /// Return the service configuration.
    pub fn config(&self) -> &CompileServiceConfig {
        &self.config
    }

    /// Run a compile operation with cooperative cancellation and generation
    /// checks around the backend work supplied by `compile`.
    pub fn compile_with<F>(&self, request: CompileRequest, compile: F) -> CompileResponse
    where
        F: FnOnce() -> Result<CompiledArtifact, CompileDiagnostic>,
    {
        if let Some(response) = self.check_gate(&request, "before_compile") {
            return response;
        }

        // Refuse before any backend work when the caller demands a discharge
        // strength this host cannot reach. Emitting a weaker certificate under
        // a stronger label would be the exact dishonesty this gate exists to
        // prevent.
        if let Some(response) = required_strength_rejection_response(&request) {
            return response;
        }

        // Bind caller contract claims to the exact target spec selected by the
        // same expanded compiler configuration the request authorizes. This
        // runs before the caller closure, lowering, allocation, or manifest
        // attachment, so a mismatched manifest cannot acquire artifact state.
        let expanded = expanded_profile_for_request(&request);
        let authority_compiler = Compiler::new(expanded.compiler);
        if let Some(diagnostic) =
            manifest_contract_preflight_diagnostic(&request, &authority_compiler, "before_compile")
        {
            return manifest_contract_rejection_response(&request, diagnostic);
        }

        if let Some(response) = self.check_gate(&request, "before_lowering") {
            return response;
        }

        if let Some(response) = self.check_gate(&request, "before_executable_allocation") {
            return response;
        }

        let mut artifact = match compile() {
            Ok(artifact) => artifact,
            Err(diagnostic) => {
                return CompileResponse {
                    request_id: request.request_id,
                    generation: request.generation,
                    status: CompileStatus::Failed,
                    disposition: ArtifactInstallDisposition::Rejected,
                    artifact: None,
                    payload: None,
                    diagnostics: vec![diagnostic],
                };
            }
        };

        if let Some(response) = self.check_gate(&request, "before_install") {
            return response;
        }

        attach_request_manifest(&request, &mut artifact);
        apply_install_disposition(&request, &mut artifact);
        let disposition = artifact.install.disposition;
        let diagnostics = proof_tv_diagnostics(&artifact);

        CompileResponse {
            request_id: request.request_id,
            generation: request.generation,
            status: CompileStatus::Compiled,
            disposition,
            artifact: Some(artifact),
            payload: None,
            diagnostics,
        }
    }

    /// Compile a trust_ir module into the artifact kind requested by `request`.
    pub fn compile(&self, request: CompileRequest, module: &trust_ir::Module) -> CompileResponse {
        self.compile_with_extern_symbols(request, module, &HashMap::new())
    }

    /// Compile a trust_ir module with explicit external symbols for executable
    /// memory artifacts.
    pub fn compile_with_extern_symbols(
        &self,
        request: CompileRequest,
        module: &trust_ir::Module,
        extern_symbols: &HashMap<String, *const u8>,
    ) -> CompileResponse {
        if let Some(response) = self.check_gate(&request, "before_compile") {
            return response;
        }

        // See `compile_with`: strength refusal precedes all backend work.
        if let Some(response) = required_strength_rejection_response(&request) {
            return response;
        }

        let started = Instant::now();
        let expanded = expanded_profile_for_request(&request);
        let compiler = self.compiler_for_request(expanded.compiler.clone(), &request);
        if let Some(diagnostic) =
            manifest_contract_preflight_diagnostic(&request, &compiler, "before_lowering")
        {
            return manifest_contract_rejection_response(&request, diagnostic);
        }
        if let Some(diagnostic) =
            manifest_module_signature_preflight_diagnostic(&request, module, &compiler)
        {
            return manifest_contract_rejection_response(&request, diagnostic);
        }
        let generation = request.generation;
        let mut provenance = request.provenance.clone();
        provenance.raw_extern_bindings = raw_extern_bindings_from_map(extern_symbols);
        let profile = request.profile.clone();
        let artifact_kind = request.artifact_kind;
        let identity = match artifact_identity_for_module(&request, module) {
            Ok(identity) => identity,
            Err(diagnostic) => {
                return CompileResponse {
                    request_id: request.request_id,
                    generation,
                    status: CompileStatus::Failed,
                    disposition: ArtifactInstallDisposition::Rejected,
                    artifact: None,
                    payload: None,
                    diagnostics: vec![diagnostic],
                };
            }
        };

        if let Some(response) = self.check_gate(&request, "before_lowering") {
            return response;
        }

        if let Some(response) =
            verifier_rejection_response(&request, module, &provenance, generation, &identity)
        {
            return response;
        }

        let compiled = match artifact_kind {
            ArtifactKind::Object => compile_object_payload(
                &compiler, module, &request, profile, provenance, generation, started, identity,
            ),
            ArtifactKind::ExecutableMemory => {
                if let Some(response) = self.check_gate(&request, "before_executable_allocation") {
                    return response;
                }
                compile_executable_payload(
                    &compiler,
                    module,
                    extern_symbols,
                    &request,
                    profile,
                    provenance,
                    generation,
                    started,
                    identity,
                )
            }
        };

        let (mut artifact, payload) = match compiled {
            Ok(compiled) => compiled,
            Err(diagnostic) => {
                return CompileResponse {
                    request_id: request.request_id,
                    generation,
                    status: CompileStatus::Failed,
                    disposition: ArtifactInstallDisposition::Rejected,
                    artifact: None,
                    payload: None,
                    diagnostics: vec![diagnostic],
                };
            }
        };

        if let Some(response) = self.check_gate(&request, "before_install") {
            return response;
        }

        attach_request_manifest(&request, &mut artifact);
        apply_install_disposition(&request, &mut artifact);
        let disposition = artifact.install.disposition;
        let diagnostics = proof_tv_diagnostics(&artifact);
        CompileResponse {
            request_id: request.request_id,
            generation,
            status: CompileStatus::Compiled,
            disposition,
            artifact: Some(artifact),
            payload: Some(payload),
            diagnostics,
        }
    }

    fn compiler_for_request(
        &self,
        compiler_config: CompilerConfig,
        request: &CompileRequest,
    ) -> Compiler {
        let compiler = Compiler::new(compiler_config);
        match &self.config.compile_artifact_cache {
            Some(cache) => compiler.with_compile_artifact_cache(
                cache
                    .with_boundary(CompileArtifactCacheBoundary::Service)
                    .with_proof_policy(compile_artifact_proof_policy_for_request(request)),
            ),
            None => compiler,
        }
    }

    fn check_gate(&self, request: &CompileRequest, phase: &'static str) -> Option<CompileResponse> {
        if request.cancellation.is_cancelled() {
            return Some(CompileResponse {
                request_id: request.request_id.clone(),
                generation: request.generation,
                status: CompileStatus::Cancelled,
                disposition: ArtifactInstallDisposition::Rejected,
                artifact: None,
                payload: None,
                diagnostics: vec![
                    CompileDiagnostic::new(
                        "compile.cancelled",
                        format!("compile request cancelled at {phase}"),
                    )
                    .with_phase(phase),
                ],
            });
        }

        if request.is_stale() {
            return Some(CompileResponse {
                request_id: request.request_id.clone(),
                generation: request.generation,
                status: CompileStatus::Stale,
                disposition: ArtifactInstallDisposition::Rejected,
                artifact: None,
                payload: None,
                diagnostics: vec![
                    CompileDiagnostic::new(
                        "compile.stale",
                        format!("compile request stale at {phase}"),
                    )
                    .with_phase(phase),
                ],
            });
        }

        if let Some(diagnostic) = proof_policy_preflight_diagnostic(request, phase) {
            return Some(CompileResponse {
                request_id: request.request_id.clone(),
                generation: request.generation,
                status: CompileStatus::Rejected,
                disposition: ArtifactInstallDisposition::Rejected,
                artifact: None,
                payload: None,
                diagnostics: vec![diagnostic],
            });
        }

        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VerifierRejectionKind {
    InvalidBlockArgs,
    DuplicateEdgeCopyDestinations,
    UnsupportedAbiCast,
    InvalidProvenanceAssumption,
}

impl VerifierRejectionKind {
    const fn failure_code(self) -> &'static str {
        match self {
            Self::InvalidBlockArgs => "trust_ir_invalid_block_args",
            Self::DuplicateEdgeCopyDestinations => "trust_ir_duplicate_edge_copy_destinations",
            Self::UnsupportedAbiCast => "trust_ir_unsupported_abi_cast",
            Self::InvalidProvenanceAssumption => "trust_ir_invalid_provenance_assumption",
        }
    }

    const fn message(self) -> &'static str {
        match self {
            Self::InvalidBlockArgs => "trust_ir verifier rejected invalid block arguments",
            Self::DuplicateEdgeCopyDestinations => {
                "trust_ir verifier rejected duplicate edge-copy destinations"
            }
            Self::UnsupportedAbiCast => "trust_ir verifier rejected an unsupported ABI cast",
            Self::InvalidProvenanceAssumption => {
                "trust_ir verifier rejected invalid provenance assumptions"
            }
        }
    }
}

fn verifier_rejection_response(
    request: &CompileRequest,
    module: &trust_ir::Module,
    provenance: &ArtifactProvenance,
    generation: CompileGeneration,
    identity: &ArtifactIdentity,
) -> Option<CompileResponse> {
    let rejection = first_verifier_rejection(module)?;
    let failure_code = rejection.failure_code();
    let diagnostic = CompileDiagnostic::error(failure_code, rejection.message())
        .with_phase("before_executable_allocation");
    let replay_report_metadata = verifier_rejection_replay_metadata(
        request,
        provenance,
        generation,
        identity,
        failure_code,
        &diagnostic.message,
    );
    let mut metadata = ArtifactMetadata::from_profile(&request.profile, request.artifact_kind);
    metadata.proof_policy_checksum = request.proof_policy.checksum();
    let mut artifact = CompiledArtifact::metadata_only_with(
        identity.clone(),
        generation,
        provenance.clone(),
        metadata,
    );
    artifact.install.disposition = ArtifactInstallDisposition::Rejected;
    artifact.install.artifact = artifact.metadata.clone();
    artifact.install.replay_report_metadata = Some(replay_report_metadata);
    artifact.install.proof_policy = request.proof_policy.clone();
    attach_request_manifest(request, &mut artifact);

    Some(CompileResponse {
        request_id: request.request_id.clone(),
        generation,
        status: CompileStatus::Rejected,
        disposition: ArtifactInstallDisposition::Rejected,
        artifact: Some(artifact),
        payload: None,
        diagnostics: vec![diagnostic],
    })
}

fn first_verifier_rejection(module: &trust_ir::Module) -> Option<VerifierRejectionKind> {
    if has_duplicate_block_param(module) {
        return Some(VerifierRejectionKind::DuplicateEdgeCopyDestinations);
    }

    for error in trust_ir_build::validate::validate_module(module) {
        match error {
            trust_ir_build::validate::ValidationError::BranchArgCountMismatch { .. } => {
                return Some(VerifierRejectionKind::InvalidBlockArgs);
            }
            trust_ir_build::validate::ValidationError::CastIncompatible { .. } => {
                return Some(VerifierRejectionKind::UnsupportedAbiCast);
            }
            trust_ir_build::validate::ValidationError::CastLayoutUnsupported { .. } => {
                return Some(VerifierRejectionKind::UnsupportedAbiCast);
            }
            _ => {}
        }
    }

    if has_invalid_provenance_assumption(module) {
        return Some(VerifierRejectionKind::InvalidProvenanceAssumption);
    }

    None
}

fn has_duplicate_block_param(module: &trust_ir::Module) -> bool {
    module.functions.iter().any(|func| {
        func.blocks.iter().any(|block| {
            let mut seen = HashSet::new();
            block
                .params
                .iter()
                .any(|(value, _ty)| !seen.insert(value.index()))
        })
    })
}

fn has_invalid_provenance_assumption(module: &trust_ir::Module) -> bool {
    if module.proof_summary().failed > 0 {
        return true;
    }

    module.functions.iter().any(|func| {
        let value_types = verifier_value_types(func);
        func.blocks.iter().any(|block| {
            block.body.iter().any(|node| {
                matches!(
                    &node.inst,
                    trust_ir::Inst::Assume { cond }
                        if value_types.get(&cond.index()) != Some(&trust_ir::Ty::Bool)
                )
            })
        })
    })
}

fn verifier_value_types(func: &trust_ir::Function) -> HashMap<u32, trust_ir::Ty> {
    let mut value_types = HashMap::new();
    for block in &func.blocks {
        for (value, ty) in &block.params {
            value_types.insert(value.index(), ty.clone());
        }
        for node in &block.body {
            let ty = match &node.inst {
                trust_ir::Inst::BinOp { ty, .. }
                | trust_ir::Inst::UnOp { ty, .. }
                | trust_ir::Inst::Load { ty, .. }
                | trust_ir::Inst::AtomicLoad { ty, .. }
                | trust_ir::Inst::AtomicRMW { ty, .. }
                | trust_ir::Inst::ExtractField { ty, .. }
                | trust_ir::Inst::InsertField { ty, .. }
                | trust_ir::Inst::ExtractElement { ty, .. }
                | trust_ir::Inst::InsertElement { ty, .. }
                | trust_ir::Inst::Const { ty, .. }
                | trust_ir::Inst::Undef { ty }
                | trust_ir::Inst::Copy { ty, .. }
                | trust_ir::Inst::Select { ty, .. }
                | trust_ir::Inst::LoadSlot { ty, .. } => Some(ty.clone()),
                trust_ir::Inst::ICmp { .. }
                | trust_ir::Inst::FCmp { .. }
                | trust_ir::Inst::IsUnique { .. } => Some(trust_ir::Ty::Bool),
                trust_ir::Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
                trust_ir::Inst::Alloca { .. }
                | trust_ir::Inst::HeapAlloc { .. }
                | trust_ir::Inst::GlobalAddr { .. }
                | trust_ir::Inst::GEP { .. }
                | trust_ir::Inst::NullPtr
                | trust_ir::Inst::Borrow { .. }
                | trust_ir::Inst::BorrowMut { .. }
                | trust_ir::Inst::OpenFrame { .. }
                | trust_ir::Inst::BindSlot { .. } => Some(trust_ir::Ty::Ptr),
                trust_ir::Inst::DialectOp(op) if op.result_tys.len() == 1 => {
                    Some(op.result_tys[0].clone())
                }
                _ => None,
            };
            if let Some(ty) = ty {
                for value in &node.results {
                    value_types.insert(value.index(), ty.clone());
                }
            }
        }
    }
    value_types
}

fn verifier_rejection_replay_metadata(
    request: &CompileRequest,
    provenance: &ArtifactProvenance,
    generation: CompileGeneration,
    identity: &ArtifactIdentity,
    failure_code: &'static str,
    message: &str,
) -> JitReplayReportMetadata {
    let mut report = JitReplayReportMetadata::new(0);
    report.artifact_id = Some(identity.as_str().to_owned());
    report.target = Some(
        expanded_profile_for_request(request)
            .compiler
            .target
            .name()
            .to_owned(),
    );
    report
        .properties
        .insert("generation".to_owned(), generation.get().to_string());
    report.properties.insert(
        "install_disposition".to_owned(),
        ArtifactInstallDisposition::Rejected.as_str().to_owned(),
    );
    report.properties.insert(
        "failure_category".to_owned(),
        "verifier_rejected".to_owned(),
    );
    report
        .properties
        .insert("failure_code".to_owned(), failure_code.to_owned());
    report
        .properties
        .insert("issue_refs".to_owned(), "#704,#657,#661".to_owned());
    report.properties.insert(
        "proof_policy_checksum".to_owned(),
        request.proof_policy.checksum().to_string(),
    );
    report.properties.insert(
        "proof_policy_mode".to_owned(),
        proof_mode_str(&request.proof_policy.mode).to_owned(),
    );
    report.properties.insert(
        "source_kind".to_owned(),
        format!("{:?}", provenance.source_kind),
    );
    if let Some(source_fingerprint) = &provenance.source_fingerprint {
        report
            .properties
            .insert("source_fingerprint".to_owned(), source_fingerprint.clone());
    }
    if let Some(upstream_issue) = provenance.upstream_issue {
        report
            .properties
            .insert("upstream_issue".to_owned(), upstream_issue.to_string());
    }
    if let Some(manifest) = &request.artifact_manifest {
        report.properties.insert(
            "artifact_manifest_checksum".to_owned(),
            manifest.checksum().to_string(),
        );
        report.properties.insert(
            "manifest_proof_policy_checksum".to_owned(),
            manifest.proof_policy.checksum().to_string(),
        );
        report.properties.insert(
            "layout_checksum".to_owned(),
            manifest.layout.checksum().to_string(),
        );
        report.properties.insert(
            "invalidation_key".to_owned(),
            manifest.invalidation.checksum().to_string(),
        );
    }
    report.statuses.push(
        JitTrapStatusBlock::new(
            0,
            JitTrapStatusKind::VerifierRejected,
            "compile_service.trust_ir_verifier",
        )
        .with_message(format!("{failure_code}: {message}")),
    );
    report
}

fn compile_object_payload(
    compiler: &Compiler,
    module: &trust_ir::Module,
    request: &CompileRequest,
    profile: CompileProfile,
    provenance: ArtifactProvenance,
    generation: CompileGeneration,
    started: Instant,
    identity: ArtifactIdentity,
) -> Result<(CompiledArtifact, ArtifactPayload), CompileDiagnostic> {
    let result = compiler.compile(module).map_err(|error| {
        CompileDiagnostic::error("compile.backend", error.to_string())
            .with_phase("compile_object")
            .with_backend_error(error)
    })?;

    let metadata = artifact_metadata_from_compilation(
        &profile,
        ArtifactKind::Object,
        result.metrics.code_size_bytes,
        None,
    );
    let details =
        install_details_from_object_result(module, &result, compiler.config().emit_proofs);
    let artifact = artifact_from_metadata(
        request,
        generation,
        provenance,
        metadata,
        started.elapsed(),
        identity,
        details,
    );
    let payload = ArtifactPayload::Object(object_payload_from_result(module, result));
    Ok((artifact, payload))
}

fn compile_executable_payload(
    compiler: &Compiler,
    module: &trust_ir::Module,
    extern_symbols: &HashMap<String, *const u8>,
    request: &CompileRequest,
    profile: CompileProfile,
    provenance: ArtifactProvenance,
    generation: CompileGeneration,
    started: Instant,
    identity: ArtifactIdentity,
) -> Result<(CompiledArtifact, ArtifactPayload), CompileDiagnostic> {
    let profile_hooks = profile.expand().jit.profile_hooks;
    let result = compiler
        .compile_module_to_jit_with_profile_hooks(module, extern_symbols, profile_hooks)
        .map_err(|error| {
            CompileDiagnostic::error("compile.backend", error.to_string())
                .with_phase("compile_executable")
                .with_backend_error(error)
        })?;

    let installed_payload_binding = build_installed_payload_binding(
        compiler,
        module,
        &result.buffer,
        request.artifact_manifest.as_ref(),
        &identity,
    )?;

    let metadata = artifact_metadata_from_compilation(
        &profile,
        ArtifactKind::ExecutableMemory,
        result.metrics.code_size_bytes,
        Some(result.buffer.allocated_size()),
    );
    let mut details =
        install_details_from_executable_result(&result, compiler.config().emit_proofs);
    details.replay_report_metadata = Some(replay_report_metadata_from_executable_result(
        &result,
        request,
        &provenance,
        generation,
        &identity,
        &installed_payload_binding,
    ));
    details.installed_payload_binding = Some(installed_payload_binding);
    let artifact = artifact_from_metadata(
        request,
        generation,
        provenance,
        metadata,
        started.elapsed(),
        identity,
        details,
    );
    let payload = ArtifactPayload::Executable(executable_payload_from_result(result));
    Ok((artifact, payload))
}

fn artifact_metadata_from_compilation(
    profile: &CompileProfile,
    artifact_kind: ArtifactKind,
    code_size_bytes: usize,
    allocation_size_bytes: Option<usize>,
) -> ArtifactMetadata {
    let mut metadata = ArtifactMetadata::from_profile(profile, artifact_kind);
    metadata.code_size_bytes = code_size_bytes;
    metadata.allocation_size_bytes = allocation_size_bytes;
    metadata
}

fn artifact_from_metadata(
    request: &CompileRequest,
    generation: CompileGeneration,
    provenance: ArtifactProvenance,
    mut metadata: ArtifactMetadata,
    compile_latency: Duration,
    identity: ArtifactIdentity,
    mut details: InstallArtifactDetails,
) -> CompiledArtifact {
    metadata.proof_policy_checksum = request.proof_policy.checksum();
    details.proofs = normalize_proofs_for_policy(request, details.proofs);
    let disposition = install_disposition_for_request(request, details.proofs);
    let mut replay_report_metadata = details.replay_report_metadata;
    attach_install_metadata(
        &mut replay_report_metadata,
        disposition,
        &request.proof_policy,
        details.proofs,
    );
    attach_proof_rejection_status(&mut replay_report_metadata, details.proofs);

    CompiledArtifact {
        install: InstallMetadata {
            generation,
            identity: identity.clone(),
            disposition,
            artifact: metadata.clone(),
            artifact_manifest: request
                .artifact_manifest
                .as_ref()
                .map(ArtifactManifestReference::from_manifest),
            replay_report_metadata,
            installed_payload_binding: details.installed_payload_binding,
            compiled_at: SystemTime::now(),
            compile_latency,
            exported_entrypoints: details.exported_entrypoints,
            functions: details.functions,
            proofs: details.proofs,
            proof_evidence_report: None,
            // Replaced with the request-derived summary in
            // `apply_install_disposition`, which every compile route reaches.
            // Seeded negative — not absent — so a route that somehow skipped
            // that step still reports "nothing ran". Kept allocation-free here
            // because this runs on the hot compile path; the full assumption
            // channel is attached once, at the funnel.
            proof_evidence_summary: ProofEvidenceSummary::missing(ROUTE_EVIDENCE_VERIFIER),
            proof_policy: request.proof_policy.clone(),
            counters: details.counters,
            raw_extern_bindings: provenance.raw_extern_bindings.clone(),
            native_install_gate_input: None,
            native_install_gate: None,
        },
        artifact_manifest: request.artifact_manifest.clone(),
        provenance,
        metadata,
        identity,
    }
}

fn attach_request_manifest(request: &CompileRequest, artifact: &mut CompiledArtifact) {
    if let Some(manifest) = request.artifact_manifest.clone() {
        artifact.attach_artifact_manifest(manifest);
    }
}

/// Evidence for a route that never went through a compile request at all
/// (direct-JIT handoff, metadata-only artifacts).
///
/// Nothing ran, so the summary is explicitly negative rather than absent, and
/// it still carries the host assumptions a consumer would otherwise have to
/// guess at (no solver, TV-3 mode).
fn direct_jit_route_evidence() -> ProofEvidenceSummary {
    route_evidence(
        ROUTE_EVIDENCE_VERIFIER,
        RouteFacts::default(),
        &evidence_environment_for(Target::host()),
    )
}

/// What the compile route selected by `request` actually ran.
///
/// Read off the *expanded* profile, which is the same object the backend is
/// driven with, so the facts cannot drift from the configuration that was
/// executed. Note `evidence_report_present` is keyed on the caller having
/// supplied a real proof/TV outcome — a report the service synthesizes for an
/// otherwise-unverified compile is not evidence that anything ran.
fn route_facts_for_request(request: &CompileRequest) -> RouteFacts {
    let expanded = expanded_profile_for_request(request);
    RouteFacts {
        instruction_verification_ran: expanded.jit.verify,
        dispatch_verification_ran: expanded.jit.verify_dispatch != DispatchVerifyMode::Off,
        proof_certificates_emitted: expanded.compiler.emit_proofs,
        evidence_report_present: request.proof_tv_evidence.is_some(),
        manifest_pin_accepted: request.artifact_manifest.is_some(),
    }
}

/// Build the always-present evidence summary for a compiled artifact.
///
/// The strength and assumption channel comes from the route (what the
/// configuration actually ran, and where). The verdict is then restated from
/// the real proof/TV report when obligations were discharged — the route
/// cannot certify itself, and a compile on which nothing ran keeps its
/// explicit [`ProofEvidenceVerdict::MissingEvidence`] no matter what the
/// synthesized report says.
fn proof_evidence_summary_for_artifact(
    request: &CompileRequest,
    artifact: &CompiledArtifact,
    report: &ProofTvEvidenceReportV1,
) -> ProofEvidenceSummary {
    let facts = route_facts_for_request(request);
    let environment = evidence_environment_for(compile_target_for_request(request));
    let summary = match artifact.artifact_manifest.as_ref() {
        Some(manifest) => {
            route_evidence_for_manifest(ROUTE_EVIDENCE_VERIFIER, facts, &environment, manifest)
        }
        None => route_evidence(ROUTE_EVIDENCE_VERIFIER, facts, &environment),
    };

    if !facts.obligations_discharged() {
        return summary;
    }
    if report.is_accepted() {
        return summary.with_verdict(ProofEvidenceVerdict::Verified, None);
    }
    let (verdict, code) = native_install_proof_rejection(report);
    summary.with_verdict(verdict, Some(code))
}

/// Architecture the request's expanded profile compiles for.
fn compile_target_for_request(request: &CompileRequest) -> Target {
    expanded_profile_for_request(request).compiler.target
}

/// Refuse a request whose proof policy demands a discharge strength this host
/// cannot reach.
///
/// Fail-closed by construction: the default
/// [`RequiredEvidenceStrength::Any`](crate::jit_contract::RequiredEvidenceStrength::Any)
/// is always reachable, so no existing caller changes behaviour, while a
/// caller that explicitly demands solver-backed certificates on a solver-less
/// host gets a rejection instead of a statistically-discharged certificate
/// wearing a stronger label.
fn required_strength_rejection_response(request: &CompileRequest) -> Option<CompileResponse> {
    let environment = evidence_environment_for(compile_target_for_request(request));
    let refusal: StrengthRefusal = refuse_required_strength(&request.proof_policy, &environment)?;
    Some(CompileResponse {
        request_id: request.request_id.clone(),
        generation: request.generation,
        status: CompileStatus::Rejected,
        disposition: ArtifactInstallDisposition::Rejected,
        artifact: None,
        payload: None,
        diagnostics: vec![
            CompileDiagnostic::error(PROOF_STRENGTH_UNAVAILABLE_CODE, refusal.detail)
                .with_phase("proof_strength_policy"),
        ],
    })
}

fn apply_install_disposition(request: &CompileRequest, artifact: &mut CompiledArtifact) {
    artifact.metadata.proof_policy_checksum = request.proof_policy.checksum();
    artifact.install.artifact = artifact.metadata.clone();
    artifact.install.proof_policy = request.proof_policy.clone();
    artifact.install.proofs = normalize_proofs_for_policy(request, artifact.install.proofs);
    artifact.install.disposition = merge_install_disposition(
        artifact.install.disposition,
        install_disposition_for_request(request, artifact.install.proofs),
    );
    attach_install_metadata(
        &mut artifact.install.replay_report_metadata,
        artifact.install.disposition,
        &request.proof_policy,
        artifact.install.proofs,
    );
    attach_proof_rejection_status(
        &mut artifact.install.replay_report_metadata,
        artifact.install.proofs,
    );
    let report = proof_tv_report_for_artifact(request, artifact);
    ensure_proof_tv_replay_metadata(request, artifact, &report);
    attach_proof_tv_report(&mut artifact.install.replay_report_metadata, &report);
    if !report.is_accepted() {
        artifact.install.disposition = ArtifactInstallDisposition::Rejected;
        artifact.install.artifact = artifact.metadata.clone();
    }
    // Reporting only, and last: every compile route funnels through here, so
    // this is the single place that guarantees the evidence field is present
    // (negative when nothing ran) on every artifact the service returns.
    artifact.install.proof_evidence_summary =
        proof_evidence_summary_for_artifact(request, artifact, &report);
    artifact.install.proof_evidence_report = Some(report);
}

fn normalize_proofs_for_policy(
    request: &CompileRequest,
    proofs: InstallProofSummary,
) -> InstallProofSummary {
    if request.proof_policy.requires_evidence() && proof_tv_evidence_accepted(request) {
        return InstallProofSummary {
            policy_status: ProofPolicyStatus::Satisfied,
            rejection_code: None,
            ..proofs
        };
    }

    if !request.proof_policy.requires_evidence()
        || proofs.policy_status != ProofPolicyStatus::NotRequired
    {
        return proofs;
    }

    InstallProofSummary {
        policy_status: ProofPolicyStatus::Rejected,
        rejection_code: Some(ProofRejectionCode::MissingLoweringCertificates),
        ..proofs
    }
}

fn proof_tv_evidence_accepted(request: &CompileRequest) -> bool {
    request.proof_tv_evidence.as_ref().is_some_and(|outcome| {
        outcome.verdict == ProofTvVerdict::Accepted && outcome.rejection_code.is_none()
    })
}

fn attach_install_metadata(
    replay_report_metadata: &mut Option<JitReplayReportMetadata>,
    disposition: ArtifactInstallDisposition,
    proof_policy: &ProofPolicy,
    proofs: InstallProofSummary,
) {
    let Some(report) = replay_report_metadata else {
        return;
    };
    report.properties.insert(
        "install_disposition".to_owned(),
        disposition.as_str().to_owned(),
    );
    report.properties.insert(
        "proof_policy_checksum".to_owned(),
        proof_policy.checksum().to_string(),
    );
    report.properties.insert(
        "proof_policy_mode".to_owned(),
        proof_mode_str(&proof_policy.mode).to_owned(),
    );
    report.properties.insert(
        "proof_policy_status".to_owned(),
        proofs.policy_status.as_str().to_owned(),
    );
    report.properties.insert(
        "proof_rejection_code".to_owned(),
        proofs
            .rejection_code
            .map(ProofRejectionCode::as_str)
            .unwrap_or("none")
            .to_owned(),
    );
}

fn attach_proof_rejection_status(
    replay_report_metadata: &mut Option<JitReplayReportMetadata>,
    proofs: InstallProofSummary,
) {
    if proofs.policy_status != ProofPolicyStatus::Rejected {
        return;
    }

    let Some(report) = replay_report_metadata else {
        return;
    };

    let rejection_code = proofs
        .rejection_code
        .map(ProofRejectionCode::as_str)
        .unwrap_or("unknown");
    let failure_code = proof_rejection_failure_code(proofs.rejection_code);
    report.properties.insert(
        "failure_category".to_owned(),
        "proof_or_install_rejection".to_owned(),
    );
    report
        .properties
        .insert("failure_code".to_owned(), failure_code.to_owned());
    report.properties.insert(
        "proof_policy_status".to_owned(),
        proofs.policy_status.as_str().to_owned(),
    );
    report
        .properties
        .insert("proof_rejection_code".to_owned(), rejection_code.to_owned());

    if report.statuses.iter().any(|status| {
        status.kind == JitTrapStatusKind::VerifierRejected
            && status.stage == "compile_service.proof_policy"
            && status.message.as_deref() == Some(rejection_code)
    }) {
        return;
    }

    let sequence = report
        .statuses
        .iter()
        .map(|status| status.sequence)
        .max()
        .map_or(0, |sequence| sequence.saturating_add(1));
    report.statuses.push(
        JitTrapStatusBlock::new(
            sequence,
            JitTrapStatusKind::VerifierRejected,
            "compile_service.proof_policy",
        )
        .with_message(rejection_code),
    );
}

fn proof_rejection_failure_code(rejection_code: Option<ProofRejectionCode>) -> &'static str {
    match rejection_code {
        Some(ProofRejectionCode::MissingLoweringCertificates)
        | Some(ProofRejectionCode::MissingJitCertificates) => "proof_missing_evidence",
        Some(ProofRejectionCode::UnverifiedLoweringCertificates)
        | Some(ProofRejectionCode::UnverifiedJitCertificates) => "proof_verifier_failure",
        None => "proof_unknown",
    }
}

fn proof_tv_report_for_artifact(
    request: &CompileRequest,
    artifact: &CompiledArtifact,
) -> ProofTvEvidenceReportV1 {
    if let Some(outcome) = &request.proof_tv_evidence {
        if let Some(code) = outcome.rejection_code {
            return ProofTvEvidenceReportV1::rejected(
                request,
                artifact,
                outcome.verdict,
                code,
                Some(outcome.diagnostic_reason.clone()),
            );
        }
        if outcome.verdict == ProofTvVerdict::Accepted {
            return ProofTvEvidenceReportV1::accepted(request, artifact);
        }
        return ProofTvEvidenceReportV1::rejected(
            request,
            artifact,
            outcome.verdict,
            ProofTvRejectionCode::Unknown,
            Some(outcome.diagnostic_reason.clone()),
        );
    }

    match proof_tv_outcome_from_summary(artifact.install.proofs) {
        None => ProofTvEvidenceReportV1::accepted(request, artifact),
        Some((verdict, code)) => {
            ProofTvEvidenceReportV1::rejected(request, artifact, verdict, code, None)
        }
    }
}

fn proof_tv_outcome_from_summary(
    proofs: InstallProofSummary,
) -> Option<(ProofTvVerdict, ProofTvRejectionCode)> {
    if proofs.policy_status != ProofPolicyStatus::Rejected {
        return None;
    }

    Some(match proofs.rejection_code {
        Some(ProofRejectionCode::MissingLoweringCertificates)
        | Some(ProofRejectionCode::MissingJitCertificates) => (
            ProofTvVerdict::MissingEvidence,
            ProofTvRejectionCode::MissingEvidence,
        ),
        Some(ProofRejectionCode::UnverifiedLoweringCertificates)
        | Some(ProofRejectionCode::UnverifiedJitCertificates) => (
            ProofTvVerdict::VerifierFailure,
            ProofTvRejectionCode::VerifierFailure,
        ),
        None => (ProofTvVerdict::Unknown, ProofTvRejectionCode::Unknown),
    })
}

fn proof_tv_diagnostics(artifact: &CompiledArtifact) -> Vec<CompileDiagnostic> {
    let Some(report) = &artifact.install.proof_evidence_report else {
        return Vec::new();
    };
    let Some(code) = report.rejection_code else {
        return Vec::new();
    };
    vec![
        CompileDiagnostic::error(
            code.as_str(),
            match &report.diagnostic_reason {
                Some(reason) => format!(
                    "proof/translation-validation evidence rejected with verdict {}: {reason}",
                    report.verdict.as_str()
                ),
                None => format!(
                    "proof/translation-validation evidence rejected with verdict {}",
                    report.verdict.as_str()
                ),
            },
        )
        .with_phase("proof_tv_evidence"),
    ]
}

fn ensure_proof_tv_replay_metadata(
    request: &CompileRequest,
    artifact: &mut CompiledArtifact,
    report: &ProofTvEvidenceReportV1,
) {
    if report.is_accepted() || artifact.install.replay_report_metadata.is_some() {
        return;
    }

    let mut replay = JitReplayReportMetadata::new(0);
    replay.artifact_id = Some(artifact.identity.as_str().to_owned());
    replay.target = Some(
        expanded_profile_for_request(request)
            .compiler
            .target
            .name()
            .to_owned(),
    );
    replay.properties.insert(
        "generation".to_owned(),
        artifact.install.generation.get().to_string(),
    );
    replay.properties.insert(
        "install_disposition".to_owned(),
        ArtifactInstallDisposition::Rejected.as_str().to_owned(),
    );
    artifact.install.replay_report_metadata = Some(replay);
}

fn attach_proof_tv_report(
    replay_report_metadata: &mut Option<JitReplayReportMetadata>,
    report: &ProofTvEvidenceReportV1,
) {
    let Some(replay) = replay_report_metadata else {
        return;
    };
    replay.properties.insert(
        "proof_tv_schema".to_owned(),
        ProofTvEvidenceReportV1::SCHEMA.to_owned(),
    );
    replay.properties.insert(
        "proof_tv_schema_version".to_owned(),
        ProofTvEvidenceReportV1::SCHEMA_VERSION.to_string(),
    );
    replay.properties.insert(
        "proof_tv_verdict".to_owned(),
        report.verdict.as_str().to_owned(),
    );
    replay.properties.insert(
        "proof_tv_code".to_owned(),
        report
            .rejection_code
            .map(ProofTvRejectionCode::as_str)
            .unwrap_or("none")
            .to_owned(),
    );
    replay.properties.insert(
        "proof_tv_report_hash".to_owned(),
        report.report_hash.to_string(),
    );
    replay.properties.insert(
        "proof_tv_target_checksum".to_owned(),
        report.target_checksum.to_string(),
    );
    replay.properties.insert(
        "proof_tv_abi_checksum".to_owned(),
        report.abi_checksum.to_string(),
    );
    replay.properties.insert(
        "proof_tv_layout_checksum".to_owned(),
        report.layout_checksum.to_string(),
    );
    replay.properties.insert(
        "proof_tv_invalidation_checksum".to_owned(),
        report.invalidation_checksum.to_string(),
    );
    replay.properties.insert(
        "proof_tv_artifact_identity".to_owned(),
        report.artifact_identity.as_str().to_owned(),
    );
    if let Some(source_fingerprint) = &report.source_fingerprint {
        replay.properties.insert(
            "proof_tv_source_fingerprint".to_owned(),
            source_fingerprint.clone(),
        );
    }
    if let Some(schema) = &report.backend_proof_family_schema {
        replay
            .properties
            .insert("backend_proof_family_schema".to_owned(), schema.clone());
    }
    if let Some(target) = &report.backend_proof_family_target {
        replay
            .properties
            .insert("backend_proof_family_target".to_owned(), target.clone());
    }
    if let Some(obligation_set) = &report.backend_proof_family_obligation_set {
        replay.properties.insert(
            "backend_proof_family_obligation_set".to_owned(),
            obligation_set.clone(),
        );
    }
    if let Some(policy_id) = &report.backend_proof_family_policy_id {
        replay.properties.insert(
            "backend_proof_family_policy_id".to_owned(),
            policy_id.clone(),
        );
    }
    if let Some(installable) = report.backend_proof_family_installable {
        replay.properties.insert(
            "backend_proof_family_installable".to_owned(),
            installable.to_string(),
        );
    }
    if let Some(report_hash) = &report.backend_proof_family_report_hash {
        replay.properties.insert(
            "backend_proof_family_report_hash".to_owned(),
            report_hash.clone(),
        );
    }
    if let Some(reason) = &report.diagnostic_reason {
        replay
            .properties
            .insert("proof_tv_diagnostic_reason".to_owned(), reason.clone());
    }

    let Some(code) = report.rejection_code else {
        return;
    };

    replay
        .properties
        .entry("failure_category".to_owned())
        .or_insert_with(|| "proof_tv_rejection".to_owned());
    replay
        .properties
        .entry("failure_code".to_owned())
        .or_insert_with(|| code.as_str().to_owned());

    if replay
        .statuses
        .iter()
        .any(|status| status.stage == "compile_service.proof_policy")
    {
        return;
    }

    if replay.statuses.iter().any(|status| {
        status.stage == "compile_service.proof_tv"
            && status.message.as_deref() == report.diagnostic_reason.as_deref()
    }) {
        return;
    }

    let sequence = replay
        .statuses
        .iter()
        .map(|status| status.sequence)
        .max()
        .map_or(0, |sequence| sequence.saturating_add(1));
    replay.statuses.push(
        JitTrapStatusBlock::new(
            sequence,
            proof_tv_status_kind(report.verdict),
            "compile_service.proof_tv",
        )
        .with_message(
            report
                .diagnostic_reason
                .clone()
                .unwrap_or_else(|| code.as_str().to_owned()),
        ),
    );
}

fn proof_tv_status_kind(verdict: ProofTvVerdict) -> JitTrapStatusKind {
    match verdict {
        ProofTvVerdict::Timeout => JitTrapStatusKind::Timeout,
        ProofTvVerdict::VerifierFailure
        | ProofTvVerdict::MissingEvidence
        | ProofTvVerdict::UnsupportedRoute
        | ProofTvVerdict::UnsupportedTarget
        | ProofTvVerdict::StaleEvidence => JitTrapStatusKind::VerifierRejected,
        ProofTvVerdict::SolverError
        | ProofTvVerdict::MalformedReport
        | ProofTvVerdict::MissingRequiredFields => JitTrapStatusKind::InternalError,
        ProofTvVerdict::Accepted | ProofTvVerdict::Unknown => JitTrapStatusKind::Unknown,
    }
}

fn backend_proof_family_report_identity(
    target: Target,
) -> Option<BackendProofFamilyReportIdentity> {
    if target != Target::Aarch64 {
        return None;
    }

    #[cfg(feature = "verify")]
    {
        let report =
            trust_cg_verify::aarch64_backend_proof_report::build_aarch64_backend_proof_family_report();
        Some(BackendProofFamilyReportIdentity {
            schema: report.schema,
            target: report.target,
            obligation_set: report.obligation_set,
            policy_id: report.policy.policy_id,
            installable: report.policy.installable,
            report_hash: report.report_hash,
        })
    }

    #[cfg(not(feature = "verify"))]
    {
        None
    }
}

fn report_binding_checksums(
    request: &CompileRequest,
    artifact: &CompiledArtifact,
) -> (
    ArtifactChecksum,
    ArtifactChecksum,
    ArtifactChecksum,
    ArtifactChecksum,
) {
    if let Some(binding) = artifact
        .install
        .installed_payload_binding
        .as_ref()
        .filter(|binding| binding.has_canonical_binding_sha256(artifact.artifact_manifest.as_ref()))
    {
        return (
            binding.authoritative_target.checksum(),
            binding.authoritative_abi.checksum(),
            binding.authoritative_layout.checksum(),
            artifact
                .artifact_manifest
                .as_ref()
                .map(|manifest| manifest.invalidation.checksum())
                .unwrap_or_else(|| ArtifactChecksum::new(0)),
        );
    }
    if let Some(manifest) = &artifact.artifact_manifest {
        return (
            manifest.target.checksum(),
            manifest.abi.checksum(),
            manifest.layout.checksum(),
            manifest.invalidation.checksum(),
        );
    }

    let target_spec = TargetSpec::default_for_architecture(artifact.metadata.target);
    let target = TargetDescriptor::for_trust_cg_target_spec(target_spec);
    let abi = AbiDescriptor::for_trust_cg_target_os(
        artifact.metadata.target,
        target.operating_system.clone(),
    );
    let layout = LayoutManifest::lp64(
        Endianness::Little,
        artifact.metadata.target.stack_alignment() as u16,
    );
    let invalidation = InvalidationKey::new(
        artifact
            .provenance
            .source_fingerprint
            .as_deref()
            .unwrap_or_else(|| artifact.identity.as_str()),
        format!("trust-cg-codegen:{:?}", artifact.metadata.profile),
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        request.proof_policy.checksum(),
        artifact.install.generation.get(),
    );

    (
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        invalidation.checksum(),
    )
}

fn merge_install_disposition(
    existing: ArtifactInstallDisposition,
    requested: ArtifactInstallDisposition,
) -> ArtifactInstallDisposition {
    match (existing, requested) {
        (ArtifactInstallDisposition::Rejected, _) | (_, ArtifactInstallDisposition::Rejected) => {
            ArtifactInstallDisposition::Rejected
        }
        (ArtifactInstallDisposition::ProfileOnly, _)
        | (_, ArtifactInstallDisposition::ProfileOnly) => ArtifactInstallDisposition::ProfileOnly,
        (ArtifactInstallDisposition::Installable, ArtifactInstallDisposition::Installable) => {
            ArtifactInstallDisposition::Installable
        }
    }
}

fn install_disposition_for_request(
    request: &CompileRequest,
    proofs: InstallProofSummary,
) -> ArtifactInstallDisposition {
    if proofs.policy_status == ProofPolicyStatus::Rejected {
        return ArtifactInstallDisposition::Rejected;
    }

    let expanded = expanded_profile_for_request(request);
    let profile_only = request.install_intent == InstallIntent::CompileOnly
        || expanded.jit.profile_hooks != ProfileHookMode::None
        || expanded.jit.emit_entry_counters;
    if profile_only {
        ArtifactInstallDisposition::ProfileOnly
    } else {
        ArtifactInstallDisposition::Installable
    }
}

fn expanded_profile_for_request(request: &CompileRequest) -> ExpandedCompileProfile {
    let mut expanded = request.profile.expand();
    if request.proof_policy.requires_evidence() {
        expanded.compiler.emit_proofs = true;
        expanded.jit.verify = true;
        expanded.jit.verify_dispatch = DispatchVerifyMode::ErrorOnFailure;
    }
    expanded
}

fn authoritative_contract_for_compiler(
    compiler: &Compiler,
) -> (TargetDescriptor, AbiDescriptor, LayoutManifest) {
    let target_spec = compiler.target_spec();
    let target = TargetDescriptor::for_trust_cg_target_spec(target_spec);
    let abi = AbiDescriptor::for_trust_cg_target_os(
        target_spec.architecture,
        target.operating_system.clone(),
    );
    let layout = LayoutManifest::lp64(
        Endianness::Little,
        target_spec.architecture.stack_alignment() as u16,
    );
    (target, abi, layout)
}

fn expected_manifest_kind(kind: ArtifactKind) -> JitArtifactKind {
    match kind {
        ArtifactKind::Object => JitArtifactKind::Object,
        ArtifactKind::ExecutableMemory => JitArtifactKind::ExecutableMemory,
    }
}

fn abi_structurally_matches(actual: &AbiDescriptor, expected: &AbiDescriptor) -> bool {
    // Compare all executable ABI facts while allowing callers of this helper
    // to diagnose the descriptive name independently. Install authority also
    // requires the exact compiler name.
    let mut normalized = actual.clone();
    normalized.name = expected.name.clone();
    &normalized == expected
}

fn core_layout_matches(actual: &LayoutManifest, expected: &LayoutManifest) -> bool {
    actual.pointer_size_bytes == expected.pointer_size_bytes
        && actual.pointer_alignment_bytes == expected.pointer_alignment_bytes
        && actual.endianness == expected.endianness
        && actual.stack_alignment_bytes == expected.stack_alignment_bytes
}

fn reserved_manifest_metadata_mismatch(manifest: &ArtifactManifestV1) -> Option<String> {
    const HARDWARE_VECTOR_PREFIX: &str = "trust_ir.hardware_vector_contract.";
    let hardware_entries =
        crate::jit_contract::trust_ir_hardware_vector_contract_metadata_entries();
    let hardware_metadata_is_present = manifest
        .metadata
        .keys()
        .any(|key| key.starts_with(HARDWARE_VECTOR_PREFIX));
    if hardware_metadata_is_present {
        for (key, expected) in &hardware_entries {
            if manifest.metadata.get(key) != Some(expected) {
                return Some(format!(
                    "reserved hardware-vector metadata `{key}` is missing or stale: expected `{expected}`, actual {:?}",
                    manifest.metadata.get(key)
                ));
            }
        }
        if let Some(key) = manifest.metadata.keys().find(|key| {
            key.starts_with(HARDWARE_VECTOR_PREFIX) && !hardware_entries.contains_key(*key)
        }) {
            return Some(format!(
                "unknown caller-defined key `{key}` uses the reserved hardware-vector metadata namespace"
            ));
        }
    }

    let host_entries =
        crate::jit_contract::host_jit_target_feature_profile_metadata_entries(manifest);
    let host_metadata_is_present = manifest.metadata.keys().any(|key| {
        key.starts_with(crate::jit_contract::HOST_JIT_TARGET_FEATURE_PROFILE_METADATA_PREFIX)
    });
    match host_entries {
        Some(expected_entries) if host_metadata_is_present => {
            for (key, expected) in &expected_entries {
                if manifest.metadata.get(key) != Some(expected) {
                    return Some(format!(
                        "reserved host-JIT feature metadata `{key}` is missing or stale: expected `{expected}`, actual {:?}",
                        manifest.metadata.get(key)
                    ));
                }
            }
            if let Some(key) = manifest.metadata.keys().find(|key| {
                key.starts_with(
                    crate::jit_contract::HOST_JIT_TARGET_FEATURE_PROFILE_METADATA_PREFIX,
                ) && !expected_entries.contains_key(*key)
            }) {
                return Some(format!(
                    "unknown caller-defined key `{key}` uses the reserved host-JIT feature metadata namespace"
                ));
            }
        }
        Some(_) => {}
        None => {
            if let Some(key) = manifest.metadata.keys().find(|key| {
                key.starts_with(
                    crate::jit_contract::HOST_JIT_TARGET_FEATURE_PROFILE_METADATA_PREFIX,
                )
            }) {
                return Some(format!(
                    "reserved host-JIT feature metadata `{key}` is out of scope for target {}",
                    manifest.target.triple
                ));
            }
        }
    }
    None
}

fn manifest_contract_preflight_diagnostic(
    request: &CompileRequest,
    compiler: &Compiler,
    phase: &'static str,
) -> Option<CompileDiagnostic> {
    let manifest = request.artifact_manifest.as_ref()?;
    let (expected_target, expected_abi, expected_layout) =
        authoritative_contract_for_compiler(compiler);

    let mismatch = if request.artifact_kind == ArtifactKind::Object {
        Some(
            "manifest-bearing object output is rejected until object bytes, parsed sections, and parsed symbols have a compiler-derived payload binding"
                .to_owned(),
        )
    } else if let Err(error) = manifest.verify_schema() {
        Some(format!("manifest schema is invalid: {error}"))
    } else if manifest.kind != expected_manifest_kind(request.artifact_kind) {
        Some(format!(
            "artifact kind mismatch: request/compiler requires {}, manifest carries {:?}",
            request.artifact_kind.contract_name(),
            manifest.kind
        ))
    } else if manifest.target.triple != expected_target.triple
        || manifest.target.architecture != expected_target.architecture
        || manifest.target.operating_system != expected_target.operating_system
        || manifest.target.pointer_width_bits != expected_target.pointer_width_bits
        || manifest.target.endianness != expected_target.endianness
    {
        Some(format!(
            "target mismatch: compiler authority is {:?}, manifest carries {:?}",
            expected_target, manifest.target
        ))
    } else if manifest.target.cpu.is_some() || !manifest.target.features.is_empty() {
        Some(format!(
            "manifest CPU/features are caller claims with no effective-compiler validation: cpu={:?}, features={:?}",
            manifest.target.cpu, manifest.target.features
        ))
    } else if manifest.abi.name != expected_abi.name
        || !abi_structurally_matches(&manifest.abi, &expected_abi)
    {
        Some(format!(
            "ABI mismatch: compiler authority is {:?}, manifest carries {:?}",
            expected_abi, manifest.abi
        ))
    } else if !core_layout_matches(&manifest.layout, &expected_layout) {
        Some(format!(
            "core layout mismatch: compiler authority is {:?}, manifest carries pointer_size={} pointer_align={} endianness={:?} stack_align={}",
            expected_layout,
            manifest.layout.pointer_size_bytes,
            manifest.layout.pointer_alignment_bytes,
            manifest.layout.endianness,
            manifest.layout.stack_alignment_bytes
        ))
    } else if !manifest.layout.records.is_empty()
        || !manifest.layout.slices.is_empty()
        || !manifest.layout.pointers.is_empty()
        || manifest.layout.wrapper_identity.is_some()
        || !manifest.layout.metadata.is_empty()
    {
        Some(
            "manifest record/slice/pointer/wrapper layout claims are not compiler-derived; callable exposure requires an explicit producer-derived layout binding"
                .to_owned(),
        )
    } else if let Some(detail) = reserved_manifest_metadata_mismatch(manifest) {
        Some(detail)
    } else if manifest.invalidation.target_checksum != manifest.target.checksum() {
        Some(
            "manifest invalidation target checksum does not match its target descriptor".to_owned(),
        )
    } else if manifest.invalidation.abi_checksum != manifest.abi.checksum() {
        Some("manifest invalidation ABI checksum does not match its ABI descriptor".to_owned())
    } else if manifest.invalidation.layout_checksum != manifest.layout.checksum() {
        Some(
            "manifest invalidation layout checksum does not match its layout descriptor".to_owned(),
        )
    } else if manifest.invalidation.proof_policy_checksum != manifest.proof_policy.checksum() {
        Some(
            "manifest invalidation proof-policy checksum does not match its proof policy"
                .to_owned(),
        )
    } else if manifest.invalidation.generation != request.generation.get() {
        Some(format!(
            "manifest generation {} does not match compile request generation {}",
            manifest.invalidation.generation,
            request.generation.get()
        ))
    } else {
        None
    };

    mismatch.map(|detail| {
        CompileDiagnostic::error(
            "compile.manifest_contract_mismatch",
            format!(
                "caller manifest is not authoritative for the effective compiler output: {detail}"
            ),
        )
        .with_phase(phase)
    })
}

fn manifest_module_signature_preflight_diagnostic(
    request: &CompileRequest,
    module: &trust_ir::Module,
    compiler: &Compiler,
) -> Option<CompileDiagnostic> {
    if request.artifact_kind != ArtifactKind::ExecutableMemory {
        return None;
    }
    let manifest = request.artifact_manifest.as_ref()?;
    let mut names = HashSet::new();
    for claimed in &manifest.symbols {
        if !names.insert(claimed.name.as_str()) {
            return Some(
                CompileDiagnostic::error(
                    "compile.manifest_signature_mismatch",
                    format!("manifest contains duplicate symbol `{}`", claimed.name),
                )
                .with_phase("before_lowering"),
            );
        }
        if claimed.visibility == SymbolVisibility::Imported {
            return Some(
                CompileDiagnostic::error(
                    "compile.manifest_signature_mismatch",
                    format!(
                        "manifest import `{}` has no compiler-derived extern signature authority",
                        claimed.name
                    ),
                )
                .with_phase("before_lowering"),
            );
        }
        let function = module.function_by_name(&claimed.name).or_else(|| {
            claimed
                .name
                .strip_prefix('_')
                .and_then(|name| module.function_by_name(name))
        });
        let Some(function) = function else {
            return Some(
                CompileDiagnostic::error(
                    "compile.manifest_signature_mismatch",
                    format!(
                        "manifest symbol `{}` has no source trust_ir function",
                        claimed.name
                    ),
                )
                .with_phase("before_lowering"),
            );
        };
        let visibility = compiler_symbol_visibility(function);
        if visibility != claimed.visibility {
            return Some(
                CompileDiagnostic::error(
                    "compile.manifest_signature_mismatch",
                    format!(
                        "manifest symbol `{}` visibility {:?} differs from compiler visibility {:?}",
                        claimed.name, claimed.visibility, visibility
                    ),
                )
                .with_phase("before_lowering"),
            );
        }
        let signature = match compiler_symbol_signature(module, function, compiler.target_spec()) {
            Ok(signature) => signature,
            Err(detail) => {
                return Some(
                    CompileDiagnostic::error("compile.manifest_signature_mismatch", detail)
                        .with_phase("before_lowering"),
                );
            }
        };
        if signature != claimed.signature {
            return Some(
                CompileDiagnostic::error(
                    "compile.manifest_signature_mismatch",
                    format!(
                        "manifest symbol `{}` signature {:?} differs from compiler/module signature {:?}",
                        claimed.name, claimed.signature, signature
                    ),
                )
                .with_phase("before_lowering"),
            );
        }
    }
    None
}

fn manifest_contract_rejection_response(
    request: &CompileRequest,
    diagnostic: CompileDiagnostic,
) -> CompileResponse {
    CompileResponse {
        request_id: request.request_id.clone(),
        generation: request.generation,
        status: CompileStatus::Rejected,
        disposition: ArtifactInstallDisposition::Rejected,
        artifact: None,
        payload: None,
        diagnostics: vec![diagnostic],
    }
}

fn proof_policy_preflight_diagnostic(
    request: &CompileRequest,
    phase: &'static str,
) -> Option<CompileDiagnostic> {
    if let Some(manifest) = &request.artifact_manifest
        && !proof_policies_semantically_equal(&manifest.proof_policy, &request.proof_policy)
    {
        return Some(
            CompileDiagnostic::error(
                ProofTvRejectionCode::MalformedReport.as_str(),
                "request proof policy does not match artifact manifest proof policy",
            )
            .with_phase(phase),
        );
    }

    if !request.proof_policy.requires_evidence() {
        return None;
    }

    let expanded = expanded_profile_for_request(request);
    if expanded.compiler.target == Target::Riscv64 {
        return Some(
            CompileDiagnostic::error(
                ProofTvRejectionCode::UnsupportedTarget.as_str(),
                "required proof policy is not supported for riscv64",
            )
            .with_phase(phase),
        );
    }

    #[cfg(not(feature = "verify"))]
    {
        Some(
            CompileDiagnostic::error(
                ProofTvRejectionCode::UnsupportedRoute.as_str(),
                "required proof policy needs the verify feature",
            )
            .with_phase(phase),
        )
    }

    #[cfg(feature = "verify")]
    {
        if request.artifact_kind == ArtifactKind::ExecutableMemory
            && expanded.compiler.target != Target::host()
        {
            return Some(
                CompileDiagnostic::error(
                    ProofTvRejectionCode::UnsupportedRoute.as_str(),
                    format!(
                        "required proof policy native install target {:?} does not match host {:?}",
                        expanded.compiler.target,
                        Target::host()
                    ),
                )
                .with_phase(phase),
            );
        }

        None
    }
}

fn proof_policies_semantically_equal(left: &ProofPolicy, right: &ProofPolicy) -> bool {
    left.mode == right.mode
        && left.require_jit_certificate == right.require_jit_certificate
        && left.require_layout_evidence == right.require_layout_evidence
        && left.require_abi_evidence == right.require_abi_evidence
        && normalized_solver_names(&left.accepted_solvers)
            == normalized_solver_names(&right.accepted_solvers)
        && left.max_replay_age_generations == right.max_replay_age_generations
}

#[derive(Default)]
struct InstallArtifactDetails {
    exported_entrypoints: Vec<EntryPointMetadata>,
    functions: Vec<FunctionArtifactMetadata>,
    proofs: InstallProofSummary,
    counters: Vec<CounterSummary>,
    replay_report_metadata: Option<JitReplayReportMetadata>,
    installed_payload_binding: Option<InstalledPayloadBinding>,
}

fn push_installed_payload_binding_component(bytes: &mut Vec<u8>, domain: &str, value: &[u8]) {
    bytes.extend_from_slice(&(domain.len() as u64).to_le_bytes());
    bytes.extend_from_slice(domain.as_bytes());
    bytes.extend_from_slice(&(value.len() as u64).to_le_bytes());
    bytes.extend_from_slice(value);
}

fn installed_payload_binding_checksum_option_bytes(checksum: Option<ArtifactChecksum>) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(17);
    match checksum {
        Some(checksum) => {
            bytes.push(1);
            bytes.extend_from_slice(&checksum.get().to_le_bytes());
        }
        None => bytes.push(0),
    }
    bytes
}

fn installed_payload_binding_manifest_option_bytes(
    manifest: Option<&ArtifactManifestV1>,
) -> Vec<u8> {
    let mut bytes = Vec::new();
    match manifest {
        Some(manifest) => {
            bytes.push(1);
            bytes.extend_from_slice(&manifest.canonical_bytes());
        }
        None => bytes.push(0),
    }
    bytes
}

fn installed_payload_binding_transcript(
    binding: &InstalledPayloadBinding,
    manifest: Option<&ArtifactManifestV1>,
) -> Vec<u8> {
    let mut bytes = Vec::new();
    push_installed_payload_binding_component(
        &mut bytes,
        "transcript.domain",
        b"trust-cg.compile_service.installed_payload_binding.sha256.v3",
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.schema",
        binding.schema.as_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.schema_version",
        &binding.schema_version.to_le_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.artifact_kind",
        binding.artifact_kind.contract_name().as_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.compiler_target_triple",
        binding.compiler_target_triple.as_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.artifact_identity",
        binding.artifact_identity.as_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.trust_ir_module_sha256",
        binding.trust_ir_module_sha256.as_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.authoritative_target.canonical",
        &binding.authoritative_target.canonical_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.authoritative_abi.canonical",
        &binding.authoritative_abi.canonical_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.authoritative_layout.canonical",
        &binding.authoritative_layout.canonical_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.manifest_checksum.option",
        &installed_payload_binding_checksum_option_bytes(binding.manifest_checksum),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.manifest.canonical_option",
        &installed_payload_binding_manifest_option_bytes(manifest),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.native_payload_sha256",
        binding.native_payload_sha256.as_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.published_image_sha256",
        binding.published_image_sha256.as_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.code_size_bytes",
        &binding.code_size_bytes.to_le_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.allocation_size_bytes",
        &binding.allocation_size_bytes.to_le_bytes(),
    );
    push_installed_payload_binding_component(
        &mut bytes,
        "binding.symbols.len",
        &(binding.symbols.len() as u64).to_le_bytes(),
    );
    for symbol in &binding.symbols {
        push_installed_payload_binding_component(
            &mut bytes,
            "binding.symbol.name",
            symbol.name.as_bytes(),
        );
        push_installed_payload_binding_component(
            &mut bytes,
            "binding.symbol.visibility",
            match symbol.visibility {
                SymbolVisibility::Exported => b"exported",
                SymbolVisibility::Internal => b"internal",
                SymbolVisibility::Imported => b"imported",
            },
        );
        push_installed_payload_binding_component(
            &mut bytes,
            "binding.symbol.start_offset",
            &symbol.start_offset.to_le_bytes(),
        );
        push_installed_payload_binding_component(
            &mut bytes,
            "binding.symbol.end_offset",
            &symbol.end_offset.to_le_bytes(),
        );
        push_installed_payload_binding_component(
            &mut bytes,
            "binding.symbol.aliases.len",
            &(symbol.aliases.len() as u64).to_le_bytes(),
        );
        for alias in &symbol.aliases {
            push_installed_payload_binding_component(
                &mut bytes,
                "binding.symbol.alias",
                alias.as_bytes(),
            );
        }
        push_installed_payload_binding_component(
            &mut bytes,
            "binding.symbol.signature.canonical",
            &symbol.signature.canonical_bytes(),
        );
    }
    bytes
}

fn installed_payload_binding_sha256(
    binding: &InstalledPayloadBinding,
    manifest: Option<&ArtifactManifestV1>,
) -> String {
    format!(
        "sha256:{}",
        sha256_hex(&installed_payload_binding_transcript(binding, manifest))
    )
}

fn compiler_symbol_visibility(function: &trust_ir::Function) -> SymbolVisibility {
    match function.linkage {
        trust_ir::Linkage::Internal | trust_ir::Linkage::Private => SymbolVisibility::Internal,
        trust_ir::Linkage::External | trust_ir::Linkage::Weak | trust_ir::Linkage::LinkOnce => {
            SymbolVisibility::Exported
        }
    }
}

fn compiler_abi_value_for_trust_ir_type(
    ty: &trust_ir::Ty,
    nullable_pointer: bool,
    target_spec: TargetSpec,
) -> Result<AbiValue, String> {
    let kind = match ty {
        trust_ir::Ty::Bool => AbiValueKind::I1,
        trust_ir::Ty::I8 | trust_ir::Ty::U8 => AbiValueKind::I8,
        trust_ir::Ty::I16 | trust_ir::Ty::U16 => AbiValueKind::I16,
        trust_ir::Ty::I32 | trust_ir::Ty::U32 | trust_ir::Ty::Char => AbiValueKind::I32,
        trust_ir::Ty::I64 | trust_ir::Ty::U64 => AbiValueKind::I64,
        trust_ir::Ty::Isize | trust_ir::Ty::Usize => AbiValueKind::USize,
        trust_ir::Ty::F32 => AbiValueKind::F32,
        trust_ir::Ty::F64 => AbiValueKind::F64,
        trust_ir::Ty::Ptr
        | trust_ir::Ty::PtrConst(_)
        | trust_ir::Ty::PtrMut(_)
        | trust_ir::Ty::Ref(_)
        | trust_ir::Ty::RefMut(_)
        | trust_ir::Ty::Rc(_)
        | trust_ir::Ty::Func(_) => AbiValueKind::Ptr,
        trust_ir::Ty::Refine(_, _) => {
            return Err(format!(
                "unsupported exported ABI refinement {ty:?} for target {}; the install boundary \
                 must validate the predicate and resolve its base type before classifying it",
                target_spec.triple()
            ));
        }
        trust_ir::Ty::I128
        | trust_ir::Ty::U128
        | trust_ir::Ty::Error
        | trust_ir::Ty::F16
        | trust_ir::Ty::Vector(_, _)
        | trust_ir::Ty::FatPtr(_)
        | trust_ir::Ty::Unit
        | trust_ir::Ty::Never
        | trust_ir::Ty::Struct(_)
        | trust_ir::Ty::Array(_, _)
        | trust_ir::Ty::Tuple(_)
        | trust_ir::Ty::Enum(_)
        | trust_ir::Ty::Set(_, _)
        | trust_ir::Ty::Sequence(_)
        | trust_ir::Ty::Record(_)
        | trust_ir::Ty::Closure(_) => {
            return Err(format!(
                "unsupported exported ABI value {ty:?} for target {}; aggregates, vectors, f16/i128, fat pointers, and non-scalar shapes require an explicit target ABI classifier",
                target_spec.triple()
            ));
        }
    };
    let mut value = AbiValue::new(kind);
    if matches!(value.kind, AbiValueKind::Ptr) && nullable_pointer {
        value = value.nullable();
    }
    Ok(value)
}

fn compiler_symbol_signature(
    module: &trust_ir::Module,
    function: &trust_ir::Function,
    target_spec: TargetSpec,
) -> Result<SymbolSignature, String> {
    if function.calling_conv != trust_ir::CallingConv::C {
        return Err(format!(
            "exported function `{}` uses unsupported calling convention {}; only the C ABI can cross the typed install boundary",
            function.name, function.calling_conv
        ));
    }
    let function_type = module.func_type(function.ty).ok_or_else(|| {
        format!(
            "exported function `{}` references missing function type {:?}",
            function.name, function.ty
        )
    })?;
    if function_type.is_vararg {
        return Err(format!(
            "exported function `{}` is variadic but the installed ABI descriptor rejects varargs",
            function.name
        ));
    }
    if function_type.returns.len() > 1 {
        return Err(format!(
            "exported function `{}` has {} returns; multi-return typed exposure is unsupported",
            function.name,
            function_type.returns.len()
        ));
    }
    if function.attrs.params.len() > function_type.params.len()
        && function.attrs.params[function_type.params.len()..]
            .iter()
            .any(|attrs| !attrs.is_empty())
    {
        return Err(format!(
            "exported function `{}` has ABI attributes beyond its parameter list",
            function.name
        ));
    }

    let mut params = Vec::with_capacity(function_type.params.len());
    for (index, ty) in function_type.params.iter().enumerate() {
        let attrs = function
            .attrs
            .params
            .get(index)
            .copied()
            .unwrap_or_default();
        if attrs.byval || attrs.sret {
            return Err(format!(
                "exported function `{}` parameter {index} uses byval/sret; hidden aggregate ABI lowering is unsupported at the typed install boundary",
                function.name
            ));
        }
        let is_pointer = matches!(
            ty,
            trust_ir::Ty::Ptr
                | trust_ir::Ty::PtrConst(_)
                | trust_ir::Ty::PtrMut(_)
                | trust_ir::Ty::Ref(_)
                | trust_ir::Ty::RefMut(_)
                | trust_ir::Ty::Rc(_)
                | trust_ir::Ty::Func(_)
        );
        if attrs.nonnull && !is_pointer {
            return Err(format!(
                "exported function `{}` parameter {index} claims nonnull for non-pointer type {ty:?}",
                function.name
            ));
        }
        // References, reference-counted values, and bare function pointers
        // are non-null by type. Raw pointers are nullable unless the producer
        // supplied `nonnull`.
        let nullable_pointer = matches!(
            ty,
            trust_ir::Ty::Ptr | trust_ir::Ty::PtrConst(_) | trust_ir::Ty::PtrMut(_)
        ) && !attrs.nonnull;
        params.push(compiler_abi_value_for_trust_ir_type(
            ty,
            nullable_pointer,
            target_spec,
        )?);
    }
    let returns = function_type
        .returns
        .iter()
        .map(|ty| {
            // trust_ir has no return-value `nonnull` carrier. A raw returned
            // pointer therefore remains nullable; references/Rc are non-null
            // by type.
            let nullable_pointer = matches!(
                ty,
                trust_ir::Ty::Ptr | trust_ir::Ty::PtrConst(_) | trust_ir::Ty::PtrMut(_)
            );
            compiler_abi_value_for_trust_ir_type(ty, nullable_pointer, target_spec)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SymbolSignature::extern_c(params, returns))
}

fn executable_symbol_bindings(
    buffer: &ExecutableBuffer,
    module: &trust_ir::Module,
    target_spec: TargetSpec,
) -> Result<Vec<InstalledPayloadSymbolBinding>, String> {
    let code_len = u64::try_from(buffer.code_len())
        .map_err(|_| "executable code length does not fit u64".to_owned())?;
    let canonical: HashSet<&str> = buffer
        .canonical_symbols()
        .iter()
        .map(String::as_str)
        .collect();
    if canonical.len() != buffer.canonical_symbols().len() {
        return Err("executable buffer contains duplicate canonical symbols".to_owned());
    }
    if buffer.function_ranges().len() != canonical.len() {
        return Err(format!(
            "executable symbol/range cardinality mismatch: {} canonical symbols, {} ranges",
            canonical.len(),
            buffer.function_ranges().len()
        ));
    }

    let mut seen = HashSet::new();
    let mut symbols = Vec::with_capacity(buffer.function_ranges().len());
    for (name, range) in buffer.function_ranges() {
        if !canonical.contains(name.as_str()) {
            return Err(format!(
                "function range `{name}` has no canonical executable symbol"
            ));
        }
        if !seen.insert(name.as_str()) {
            return Err(format!("duplicate executable function range for `{name}`"));
        }
        if range.start >= range.end || range.end > code_len {
            return Err(format!(
                "executable function `{name}` has invalid range [{}, {}) for code length {code_len}",
                range.start, range.end
            ));
        }
        let canonical_offset = buffer
            .symbol_offsets()
            .get(name)
            .copied()
            .ok_or_else(|| format!("canonical symbol `{name}` has no executable offset"))?;
        if canonical_offset != range.start {
            return Err(format!(
                "canonical symbol `{name}` offset {canonical_offset} does not match function-range start {}",
                range.start
            ));
        }
        let mut aliases: Vec<String> = buffer
            .symbol_offsets()
            .iter()
            .filter(|&(alias, &offset)| alias != name && offset == range.start)
            .map(|(alias, _)| alias.clone())
            .collect();
        aliases.sort();
        aliases.dedup();
        let function = module.function_by_name(name).ok_or_else(|| {
            format!("published executable symbol `{name}` has no source trust_ir function")
        })?;
        let signature = compiler_symbol_signature(module, function, target_spec)?;
        symbols.push(InstalledPayloadSymbolBinding {
            name: name.clone(),
            visibility: compiler_symbol_visibility(function),
            start_offset: range.start,
            end_offset: range.end,
            aliases,
            signature,
        });
    }
    symbols.sort_by(|left, right| left.name.cmp(&right.name));

    for (name, &offset) in buffer.symbol_offsets() {
        if offset >= code_len {
            return Err(format!(
                "executable symbol `{name}` offset {offset} is outside code length {code_len}"
            ));
        }
        if !symbols.iter().any(|symbol| {
            symbol.start_offset == offset
                && (symbol.name == *name || symbol.aliases.iter().any(|alias| alias == name))
        }) {
            return Err(format!(
                "executable lookup symbol `{name}` is not bound to a canonical function range"
            ));
        }
    }
    Ok(symbols)
}

fn find_installed_symbol<'a>(
    symbols: &'a [InstalledPayloadSymbolBinding],
    name: &str,
) -> Option<&'a InstalledPayloadSymbolBinding> {
    symbols
        .iter()
        .find(|symbol| symbol.name == name || symbol.aliases.iter().any(|alias| alias == name))
}

fn validate_manifest_symbol_layout(
    manifest: &ArtifactManifestV1,
    code: &[u8],
    symbols: &[InstalledPayloadSymbolBinding],
    native_payload_sha256: &str,
) -> Result<(), String> {
    let mut claimed_symbol_names = HashSet::new();
    for claimed in &manifest.symbols {
        if !claimed_symbol_names.insert(claimed.name.as_str()) {
            return Err(format!(
                "manifest contains duplicate symbol entry `{}`",
                claimed.name
            ));
        }
        if claimed.visibility == SymbolVisibility::Imported {
            return Err(format!(
                "manifest import `{}` has no compiler-derived extern signature binding; imported symbol claims are not install authority",
                claimed.name
            ));
        }
        let actual = find_installed_symbol(symbols, &claimed.name).ok_or_else(|| {
            format!(
                "manifest claims {:?} symbol `{}` but the executable exports no such canonical symbol or alias",
                claimed.visibility, claimed.name
            )
        })?;
        if claimed.visibility != actual.visibility {
            return Err(format!(
                "manifest symbol `{}` visibility {:?} does not match compiler-derived visibility {:?}",
                claimed.name, claimed.visibility, actual.visibility
            ));
        }
        if claimed.signature != actual.signature {
            return Err(format!(
                "manifest symbol `{}` signature {:?} does not match compiler/module-derived signature {:?}",
                claimed.name, claimed.signature, actual.signature
            ));
        }
        if let Some(offset) = claimed.offset_bytes
            && offset != actual.start_offset
        {
            return Err(format!(
                "manifest symbol `{}` offset {offset} does not match executable offset {}",
                claimed.name, actual.start_offset
            ));
        }
        if let Some(checksum) = claimed.checksum {
            let start = usize::try_from(actual.start_offset)
                .map_err(|_| format!("symbol `{}` start does not fit usize", claimed.name))?;
            let end = usize::try_from(actual.end_offset)
                .map_err(|_| format!("symbol `{}` end does not fit usize", claimed.name))?;
            let actual_checksum = ArtifactChecksum::for_bytes(&code[start..end]);
            if checksum != actual_checksum {
                return Err(format!(
                    "manifest symbol `{}` checksum {} does not match executable checksum {}",
                    claimed.name, checksum, actual_checksum
                ));
            }
        }
    }

    let mut claimed_layout_symbol_names = HashSet::new();
    for claimed in &manifest.layout.symbols {
        if !claimed_layout_symbol_names.insert(claimed.name.as_str()) {
            return Err(format!(
                "manifest layout contains duplicate symbol entry `{}`",
                claimed.name
            ));
        }
        let actual = find_installed_symbol(symbols, &claimed.name).ok_or_else(|| {
            format!(
                "layout claims symbol `{}` but the executable has no such canonical symbol or alias",
                claimed.name
            )
        })?;
        if actual.name != claimed.name {
            return Err(format!(
                "layout symbol `{}` is an alias for canonical symbol `{}`; layout authority requires canonical names",
                claimed.name, actual.name
            ));
        }
        if claimed.section != "executable_text" {
            return Err(format!(
                "layout symbol `{}` must use canonical section `executable_text`, not `{}`",
                claimed.name, claimed.section
            ));
        }
        if claimed.offset_bytes != Some(actual.start_offset) {
            return Err(format!(
                "layout symbol `{}` offset {:?} does not exactly bind executable offset {}",
                claimed.name, claimed.offset_bytes, actual.start_offset
            ));
        }
        let actual_size = actual.end_offset - actual.start_offset;
        if claimed.size_bytes != actual_size {
            return Err(format!(
                "layout symbol `{}` size {} does not match executable size {actual_size}",
                claimed.name, claimed.size_bytes
            ));
        }
        if claimed.alignment_bytes == 0
            || !claimed.alignment_bytes.is_power_of_two()
            || (code.as_ptr() as usize)
                .checked_add(usize::try_from(actual.start_offset).unwrap_or(usize::MAX))
                .is_none_or(|address| address % claimed.alignment_bytes as usize != 0)
        {
            return Err(format!(
                "layout symbol `{}` alignment {} is not satisfied by executable offset {}",
                claimed.name, claimed.alignment_bytes, actual.start_offset
            ));
        }
    }

    let mut claimed_section_names = HashSet::new();
    for section in &manifest.sections {
        if !claimed_section_names.insert(section.name.as_str()) {
            return Err(format!(
                "manifest contains duplicate section entry `{}`",
                section.name
            ));
        }
        if section.kind != crate::jit_contract::ArtifactSectionKind::Text {
            return Err(format!(
                "manifest section `{}` has {:?} content that is not represented by the executable code binding",
                section.name, section.kind
            ));
        }
        if section.size_bytes != code.len() as u64 {
            return Err(format!(
                "manifest text section `{}` size {} does not match executable code size {}",
                section.name,
                section.size_bytes,
                code.len()
            ));
        }
        if section.alignment_bytes == 0
            || !section.alignment_bytes.is_power_of_two()
            || !(code.as_ptr() as usize).is_multiple_of(section.alignment_bytes as usize)
        {
            return Err(format!(
                "manifest text section `{}` has invalid alignment {}",
                section.name, section.alignment_bytes
            ));
        }
        if let Some(checksum) = section.checksum {
            let actual_checksum = ArtifactChecksum::for_bytes(code);
            if checksum != actual_checksum {
                return Err(format!(
                    "manifest text section `{}` checksum {} does not match executable checksum {}",
                    section.name, checksum, actual_checksum
                ));
            }
        }
    }

    if let Some(claimed) = manifest.metadata.get("native_payload_sha256")
        && claimed != native_payload_sha256
    {
        return Err(format!(
            "manifest native_payload_sha256 `{claimed}` does not match executable `{native_payload_sha256}`"
        ));
    }
    Ok(())
}

fn authoritative_live_layout_symbols(
    manifest: &ArtifactManifestV1,
    code: &[u8],
    symbols: &[InstalledPayloadSymbolBinding],
) -> Result<Vec<crate::jit_contract::SymbolLayout>, String> {
    let mut rows = Vec::with_capacity(manifest.layout.symbols.len());
    for selected in &manifest.layout.symbols {
        let actual = symbols
            .iter()
            .find(|symbol| symbol.name == selected.name)
            .ok_or_else(|| {
                format!(
                    "selected layout symbol `{}` is not a canonical compiler symbol",
                    selected.name
                )
            })?;
        let address = (code.as_ptr() as usize)
            .checked_add(
                usize::try_from(actual.start_offset)
                    .map_err(|_| format!("symbol `{}` offset does not fit usize", actual.name))?,
            )
            .ok_or_else(|| format!("symbol `{}` address overflow", actual.name))?;
        if selected.section != "executable_text"
            || selected.offset_bytes != Some(actual.start_offset)
            || selected.size_bytes != actual.end_offset - actual.start_offset
            || selected.alignment_bytes == 0
            || !selected.alignment_bytes.is_power_of_two()
            || address % selected.alignment_bytes as usize != 0
        {
            return Err(format!(
                "selected layout symbol `{}` is not an exact live executable row",
                selected.name
            ));
        }
        // Reconstruct every authoritative field rather than copying the
        // caller row. Selection is optional, but selected values come from the
        // live compiler symbol and the independently checked alignment proof.
        rows.push(crate::jit_contract::SymbolLayout {
            name: actual.name.clone(),
            section: "executable_text".to_owned(),
            offset_bytes: Some(actual.start_offset),
            size_bytes: actual.end_offset - actual.start_offset,
            alignment_bytes: selected.alignment_bytes,
        });
    }
    rows.sort_by(|left, right| left.name.cmp(&right.name));
    if rows.windows(2).any(|pair| pair[0].name >= pair[1].name) {
        return Err("authoritative live layout contains duplicate symbol names".to_owned());
    }
    Ok(rows)
}

fn build_installed_payload_binding(
    compiler: &Compiler,
    module: &trust_ir::Module,
    buffer: &ExecutableBuffer,
    manifest: Option<&ArtifactManifestV1>,
    artifact_identity: &ArtifactIdentity,
) -> Result<InstalledPayloadBinding, CompileDiagnostic> {
    buffer.verify_published_code_integrity().map_err(|error| {
        CompileDiagnostic::error(
            "compile.installed_payload_binding",
            format!("live executable publication failed integrity validation: {error}"),
        )
        .with_phase("compile_executable")
    })?;
    let symbols =
        executable_symbol_bindings(buffer, module, compiler.target_spec()).map_err(|detail| {
            CompileDiagnostic::error("compile.installed_payload_binding", detail)
                .with_phase("compile_executable")
        })?;
    let code = buffer.code_slice();
    let code_size_bytes = u64::try_from(code.len()).map_err(|_| {
        CompileDiagnostic::error(
            "compile.installed_payload_binding",
            "live executable code size does not fit the installed binding schema",
        )
        .with_phase("compile_executable")
    })?;
    let allocation_size_bytes = u64::try_from(buffer.allocated_size()).map_err(|_| {
        CompileDiagnostic::error(
            "compile.installed_payload_binding",
            "live executable allocation size does not fit the installed binding schema",
        )
        .with_phase("compile_executable")
    })?;
    let native_payload_sha256 = format!("sha256:{}", sha256_hex(code));
    let published_image_sha256 = format!("sha256:{}", buffer.published_image_sha256());
    if let Some(manifest) = manifest {
        validate_manifest_symbol_layout(manifest, code, &symbols, &native_payload_sha256).map_err(
            |detail| {
                CompileDiagnostic::error(
                    "compile.manifest_payload_mismatch",
                    format!("caller manifest does not match emitted executable payload: {detail}"),
                )
                .with_phase("compile_executable")
            },
        )?;
    }
    let (authoritative_target, authoritative_abi, mut authoritative_layout) =
        authoritative_contract_for_compiler(compiler);
    if let Some(manifest) = manifest {
        authoritative_layout.symbols = authoritative_live_layout_symbols(manifest, code, &symbols)
            .map_err(|detail| {
                CompileDiagnostic::error("compile.manifest_payload_mismatch", detail)
                    .with_phase("compile_executable")
            })?;
    }
    Ok(InstalledPayloadBinding {
        schema: INSTALLED_PAYLOAD_BINDING_SCHEMA.to_owned(),
        schema_version: INSTALLED_PAYLOAD_BINDING_SCHEMA_VERSION,
        artifact_kind: ArtifactKind::ExecutableMemory,
        compiler_target_triple: compiler.target_spec().triple(),
        artifact_identity: artifact_identity.as_str().to_owned(),
        trust_ir_module_sha256: module.stable_digest().to_string(),
        authoritative_target,
        authoritative_abi,
        authoritative_layout,
        manifest_checksum: manifest.map(ArtifactManifestV1::checksum),
        native_payload_sha256,
        published_image_sha256,
        code_size_bytes,
        allocation_size_bytes,
        symbols,
        binding_sha256: String::new(),
    }
    .with_canonical_binding_sha256(manifest))
}

fn installed_payload_binding_mismatch(detail: impl Into<String>) -> ArtifactContractError {
    ArtifactContractError::InstalledPayloadBindingMismatch {
        detail: detail.into(),
    }
}

fn validate_bound_symbol_signature(
    symbol: &InstalledPayloadSymbolBinding,
) -> Result<(), ArtifactContractError> {
    if symbol.signature.abi != "extern_c"
        || symbol.signature.variadic
        || symbol.signature.returns.len() > 1
    {
        return Err(installed_payload_binding_mismatch(format!(
            "symbol `{}` carries unsupported compiler signature {:?}",
            symbol.name, symbol.signature
        )));
    }
    for value in symbol
        .signature
        .params
        .iter()
        .chain(symbol.signature.returns.iter())
    {
        if !matches!(
            value.kind,
            AbiValueKind::I1
                | AbiValueKind::I8
                | AbiValueKind::I16
                | AbiValueKind::I32
                | AbiValueKind::I64
                | AbiValueKind::USize
                | AbiValueKind::F32
                | AbiValueKind::F64
                | AbiValueKind::Ptr
        ) || (value.nullable && value.kind != AbiValueKind::Ptr)
        {
            return Err(installed_payload_binding_mismatch(format!(
                "symbol `{}` carries unsupported compiler ABI value {:?}",
                symbol.name, value
            )));
        }
    }
    Ok(())
}

fn validate_manifest_against_installed_binding(
    manifest: &ArtifactManifestV1,
    binding: &InstalledPayloadBinding,
) -> Result<(), ArtifactContractError> {
    manifest.verify_schema()?;
    if let Some(detail) = reserved_manifest_metadata_mismatch(manifest) {
        return Err(installed_payload_binding_mismatch(detail));
    }
    if manifest.kind != JitArtifactKind::ExecutableMemory {
        return Err(installed_payload_binding_mismatch(format!(
            "manifest kind {:?} is not executable memory",
            manifest.kind
        )));
    }
    if manifest.target != binding.authoritative_target {
        return Err(installed_payload_binding_mismatch(format!(
            "manifest target {:?} does not exactly match compiler target {:?}",
            manifest.target, binding.authoritative_target
        )));
    }
    if manifest.target.cpu.is_some() || !manifest.target.features.is_empty() {
        return Err(installed_payload_binding_mismatch(
            "manifest carries CPU/features that were not validated against the effective compiler",
        ));
    }
    if manifest.abi != binding.authoritative_abi {
        return Err(installed_payload_binding_mismatch(format!(
            "manifest ABI {:?} does not structurally match compiler ABI {:?}",
            manifest.abi, binding.authoritative_abi
        )));
    }
    if manifest.layout != binding.authoritative_layout {
        return Err(installed_payload_binding_mismatch(
            "manifest layout does not exactly match compiler/live-validated layout authority",
        ));
    }
    if !manifest.layout.records.is_empty()
        || !manifest.layout.slices.is_empty()
        || !manifest.layout.pointers.is_empty()
        || manifest.layout.wrapper_identity.is_some()
        || !manifest.layout.metadata.is_empty()
    {
        return Err(installed_payload_binding_mismatch(
            "manifest carries caller-owned record/slice/pointer/wrapper layout without producer-derived authority",
        ));
    }
    if manifest.invalidation.target_checksum != manifest.target.checksum()
        || manifest.invalidation.abi_checksum != manifest.abi.checksum()
        || manifest.invalidation.layout_checksum != manifest.layout.checksum()
        || manifest.invalidation.proof_policy_checksum != manifest.proof_policy.checksum()
        || manifest.invalidation.target_checksum != binding.authoritative_target.checksum()
        || manifest.invalidation.abi_checksum != binding.authoritative_abi.checksum()
        || manifest.invalidation.layout_checksum != binding.authoritative_layout.checksum()
    {
        return Err(installed_payload_binding_mismatch(
            "manifest invalidation component checksums are internally inconsistent",
        ));
    }
    Ok(())
}

fn validate_live_symbol_inventory(
    buffer: &ExecutableBuffer,
    binding: &InstalledPayloadBinding,
) -> Result<(), ArtifactContractError> {
    if buffer.canonical_symbols().len() != binding.symbols.len()
        || buffer.function_ranges().len() != binding.symbols.len()
    {
        return Err(installed_payload_binding_mismatch(format!(
            "live/bound symbol cardinality differs: live canonical={}, live ranges={}, bound={}",
            buffer.canonical_symbols().len(),
            buffer.function_ranges().len(),
            binding.symbols.len()
        )));
    }

    let mut previous_name: Option<&str> = None;
    let mut bound_lookup_names = HashSet::new();
    for symbol in &binding.symbols {
        if previous_name.is_some_and(|previous| previous >= symbol.name.as_str()) {
            return Err(installed_payload_binding_mismatch(
                "bound canonical symbols are not strictly name-sorted",
            ));
        }
        previous_name = Some(&symbol.name);
        if symbol.visibility == SymbolVisibility::Imported {
            return Err(installed_payload_binding_mismatch(format!(
                "published symbol `{}` cannot have imported visibility",
                symbol.name
            )));
        }
        validate_bound_symbol_signature(symbol)?;
        if !bound_lookup_names.insert(symbol.name.as_str()) {
            return Err(installed_payload_binding_mismatch(format!(
                "duplicate bound lookup name `{}`",
                symbol.name
            )));
        }
        if symbol.aliases.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(installed_payload_binding_mismatch(format!(
                "aliases for `{}` are not strictly sorted and unique",
                symbol.name
            )));
        }
        for alias in &symbol.aliases {
            if !bound_lookup_names.insert(alias.as_str()) {
                return Err(installed_payload_binding_mismatch(format!(
                    "duplicate/colliding bound lookup alias `{alias}`"
                )));
            }
        }

        let range = buffer
            .function_ranges()
            .iter()
            .find_map(|(name, range)| (name == &symbol.name).then_some(range))
            .ok_or_else(|| {
                installed_payload_binding_mismatch(format!(
                    "bound symbol `{}` has no live function range",
                    symbol.name
                ))
            })?;
        if range.start != symbol.start_offset || range.end != symbol.end_offset {
            return Err(installed_payload_binding_mismatch(format!(
                "live range for `{}` is [{}, {}), binding is [{}, {})",
                symbol.name, range.start, range.end, symbol.start_offset, symbol.end_offset
            )));
        }
        let mut live_aliases = buffer
            .symbol_offsets()
            .iter()
            .filter(|&(name, &offset)| name != &symbol.name && offset == symbol.start_offset)
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        live_aliases.sort();
        live_aliases.dedup();
        if live_aliases != symbol.aliases {
            return Err(installed_payload_binding_mismatch(format!(
                "live aliases for `{}` are {:?}, binding carries {:?}",
                symbol.name, live_aliases, symbol.aliases
            )));
        }
    }

    for (name, &offset) in buffer.symbol_offsets() {
        let bound = find_installed_symbol(&binding.symbols, name).ok_or_else(|| {
            installed_payload_binding_mismatch(format!(
                "live lookup name `{name}` is absent from the sealed binding"
            ))
        })?;
        if offset != bound.start_offset {
            return Err(installed_payload_binding_mismatch(format!(
                "live lookup name `{name}` offset {offset} differs from bound offset {}",
                bound.start_offset
            )));
        }
    }
    Ok(())
}

fn validate_replay_against_installed_binding(
    replay: &JitReplayReportMetadata,
    install: &InstallMetadata,
    binding: &InstalledPayloadBinding,
) -> Result<(), ArtifactContractError> {
    if replay.schema != JIT_REPLAY_SCHEMA || replay.schema_version != JIT_REPLAY_SCHEMA_VERSION {
        return Err(installed_payload_binding_mismatch(format!(
            "replay schema/version is {} v{}, expected {} v{}",
            replay.schema, replay.schema_version, JIT_REPLAY_SCHEMA, JIT_REPLAY_SCHEMA_VERSION
        )));
    }
    let allocation_size_bytes = binding.allocation_size_bytes.to_string();
    if replay.artifact_id.as_deref() != Some(install.identity.as_str())
        || replay.target.as_deref() != Some(binding.compiler_target_triple.as_str())
        || replay.code_size != binding.code_size_bytes
        || replay.properties.get("native_payload_sha256") != Some(&binding.native_payload_sha256)
        || replay.properties.get("published_image_sha256") != Some(&binding.published_image_sha256)
        || replay.properties.get("allocation_size_bytes") != Some(&allocation_size_bytes)
        || replay.properties.get("trust_ir_module_sha256") != Some(&binding.trust_ir_module_sha256)
        || replay.properties.get("installed_payload_binding_sha256")
            != Some(&binding.binding_sha256)
    {
        return Err(installed_payload_binding_mismatch(
            "replay artifact id, target, code size, allocation extent, native payload, published image, module, or binding digest differs from the sealed binding",
        ));
    }
    if replay.symbols.len() != binding.symbols.len() {
        return Err(installed_payload_binding_mismatch(
            "replay/binding symbol cardinality differs",
        ));
    }
    let mut replay_names = HashSet::new();
    for label in &replay.symbols {
        if !replay_names.insert(label.name.as_str()) {
            return Err(installed_payload_binding_mismatch(format!(
                "replay contains duplicate symbol `{}`",
                label.name
            )));
        }
        let bound = binding
            .symbols
            .iter()
            .find(|symbol| symbol.name == label.name)
            .ok_or_else(|| {
                installed_payload_binding_mismatch(format!(
                    "replay symbol `{}` is absent from the sealed binding",
                    label.name
                ))
            })?;
        let mut aliases = label.aliases.clone();
        aliases.sort();
        aliases.dedup();
        if label.range.start_offset != bound.start_offset
            || label.range.end_offset != bound.end_offset
            || aliases != bound.aliases
        {
            return Err(installed_payload_binding_mismatch(format!(
                "replay range/aliases for `{}` differ from the sealed binding",
                label.name
            )));
        }
    }
    let entry_symbol = replay
        .entry_symbol
        .as_deref()
        .ok_or_else(|| installed_payload_binding_mismatch("replay metadata has no entry symbol"))?;
    if find_installed_symbol(&binding.symbols, entry_symbol).is_none() {
        return Err(installed_payload_binding_mismatch(format!(
            "replay entry symbol `{entry_symbol}` is absent from the sealed binding"
        )));
    }

    let mut entrypoints = install.exported_entrypoints.clone();
    entrypoints.sort_by(|left, right| {
        (left.name.as_str(), left.offset_bytes).cmp(&(right.name.as_str(), right.offset_bytes))
    });
    let expected_entrypoints = binding
        .symbols
        .iter()
        .map(|symbol| EntryPointMetadata {
            name: symbol.name.clone(),
            offset_bytes: symbol.start_offset,
        })
        .collect::<Vec<_>>();
    if entrypoints != expected_entrypoints {
        return Err(installed_payload_binding_mismatch(
            "install entrypoint inventory differs from the sealed compiler symbol inventory",
        ));
    }
    Ok(())
}

fn validate_installed_payload_binding(
    install: &InstallMetadata,
    manifest: Option<&ArtifactManifestV1>,
    buffer: &ExecutableBuffer,
) -> Result<(), ArtifactContractError> {
    let binding = install.installed_payload_binding.as_ref().ok_or_else(|| {
        installed_payload_binding_mismatch("missing mandatory compiler-derived v3 binding")
    })?;
    if binding.schema != INSTALLED_PAYLOAD_BINDING_SCHEMA
        || binding.schema_version != INSTALLED_PAYLOAD_BINDING_SCHEMA_VERSION
        || binding.artifact_kind != ArtifactKind::ExecutableMemory
        || !binding.has_canonical_binding_sha256(manifest)
    {
        return Err(installed_payload_binding_mismatch(
            "binding schema/version/kind or private canonical seal is invalid",
        ));
    }
    if install.artifact.artifact_kind != ArtifactKind::ExecutableMemory
        || binding.compiler_target_triple != binding.authoritative_target.triple
        || binding.artifact_identity != install.identity.as_str()
        || !binding.trust_ir_module_sha256.starts_with("sha256:")
    {
        return Err(installed_payload_binding_mismatch(
            "artifact kind, identity, module digest, or binding target triple is internally inconsistent",
        ));
    }
    let artifact_target = TargetDescriptor::for_trust_cg_target(
        install.artifact.target,
        binding.authoritative_target.operating_system.clone(),
    );
    if artifact_target.architecture != binding.authoritative_target.architecture
        || artifact_target.pointer_width_bits != binding.authoritative_target.pointer_width_bits
        || artifact_target.endianness != binding.authoritative_target.endianness
    {
        return Err(installed_payload_binding_mismatch(
            "artifact target architecture differs from compiler target authority",
        ));
    }
    let expected_abi = AbiDescriptor::for_trust_cg_target_os(
        install.artifact.target,
        binding.authoritative_target.operating_system.clone(),
    );
    let expected_layout = LayoutManifest::lp64(
        Endianness::Little,
        install.artifact.target.stack_alignment() as u16,
    );
    if binding.authoritative_abi != expected_abi
        || !core_layout_matches(&binding.authoritative_layout, &expected_layout)
        || !binding.authoritative_layout.records.is_empty()
        || !binding.authoritative_layout.slices.is_empty()
        || !binding.authoritative_layout.pointers.is_empty()
        || binding.authoritative_layout.wrapper_identity.is_some()
        || !binding.authoritative_layout.metadata.is_empty()
        || binding.authoritative_target.cpu.is_some()
        || !binding.authoritative_target.features.is_empty()
    {
        return Err(installed_payload_binding_mismatch(
            "sealed target/ABI/core-layout authority is not an exact Trust Codegen target contract",
        ));
    }

    match (binding.manifest_checksum, manifest) {
        (Some(expected), Some(manifest)) if expected == manifest.checksum() => {
            validate_manifest_against_installed_binding(manifest, binding)?;
            let reference = install.artifact_manifest.as_ref().ok_or_else(|| {
                installed_payload_binding_mismatch(
                    "manifest-bound payload has no mandatory install manifest reference",
                )
            })?;
            reference.verify_manifest(manifest).map_err(|error| {
                installed_payload_binding_mismatch(format!(
                    "install manifest reference does not verify: {error}"
                ))
            })?;
        }
        (Some(expected), Some(manifest)) => {
            return Err(installed_payload_binding_mismatch(format!(
                "presented manifest checksum {} differs from sealed checksum {expected}",
                manifest.checksum()
            )));
        }
        (Some(_), None) => {
            return Err(installed_payload_binding_mismatch(
                "sealed binding requires a manifest but none was presented",
            ));
        }
        (None, Some(_)) => {
            return Err(installed_payload_binding_mismatch(
                "a manifest was presented for a payload compiled without a manifest binding",
            ));
        }
        (None, None) if install.artifact_manifest.is_some() => {
            return Err(installed_payload_binding_mismatch(
                "install metadata has an unsealed manifest reference",
            ));
        }
        (None, None) => {}
    }

    buffer.verify_published_code_integrity().map_err(|error| {
        installed_payload_binding_mismatch(format!(
            "live executable publication integrity failed: {error}"
        ))
    })?;
    let code = buffer.code_slice();
    let live_code_size_bytes = u64::try_from(code.len()).map_err(|_| {
        installed_payload_binding_mismatch(
            "live executable code size does not fit the installed binding schema",
        )
    })?;
    let live_allocation_size = buffer.allocated_size();
    let live_allocation_size_bytes = u64::try_from(live_allocation_size).map_err(|_| {
        installed_payload_binding_mismatch(
            "live executable allocation size does not fit the installed binding schema",
        )
    })?;
    let live_sha256 = format!("sha256:{}", sha256_hex(code));
    let live_published_image_sha256 = format!("sha256:{}", buffer.published_image_sha256());
    if binding.code_size_bytes != live_code_size_bytes
        || binding.native_payload_sha256 != live_sha256
        || binding.published_image_sha256 != live_published_image_sha256
        || binding.allocation_size_bytes != live_allocation_size_bytes
        || install.artifact.code_size_bytes != code.len()
        || install.artifact.allocation_size_bytes != Some(live_allocation_size)
        || live_allocation_size < code.len()
    {
        return Err(installed_payload_binding_mismatch(format!(
            "live executable extent/digest differs from binding: live_len={}, live_allocation_size={live_allocation_size}, live_sha256={live_sha256}, live_published_image_sha256={live_published_image_sha256}",
            code.len(),
        )));
    }
    validate_live_symbol_inventory(buffer, binding)?;
    if let Some(manifest) = manifest {
        validate_manifest_symbol_layout(
            manifest,
            code,
            &binding.symbols,
            &binding.native_payload_sha256,
        )
        .map_err(installed_payload_binding_mismatch)?;
    }
    let replay = install.replay_report_metadata.as_ref().ok_or_else(|| {
        installed_payload_binding_mismatch("missing mandatory executable replay metadata")
    })?;
    validate_replay_against_installed_binding(replay, install, binding)
}

fn object_payload_from_result(
    module: &trust_ir::Module,
    result: CompilationResult,
) -> ObjectArtifactPayload {
    ObjectArtifactPayload {
        bytes: result.object_code,
        metrics: result.metrics,
        trace: result.trace,
        proofs: result.proofs,
        functions: module
            .functions
            .iter()
            .map(|func| FunctionArtifactMetadata::from_trust_ir_name(func.name.clone()))
            .collect(),
        compile_artifact_cache_telemetry: result.compile_artifact_cache_telemetry,
    }
}

fn compile_artifact_proof_policy_for_request(
    request: &CompileRequest,
) -> CompileArtifactProofPolicy {
    match request.proof_policy.mode {
        ProofMode::Disabled => CompileArtifactProofPolicy::Unchecked,
        ProofMode::AuditOnly => CompileArtifactProofPolicy::Smoke,
        ProofMode::RequireCertificates | ProofMode::RequireReplay => {
            CompileArtifactProofPolicy::ProofTvFull
        }
    }
}

fn install_details_from_object_result(
    module: &trust_ir::Module,
    result: &CompilationResult,
    proofs_required: bool,
) -> InstallArtifactDetails {
    let functions = module
        .functions
        .iter()
        .map(|func| FunctionArtifactMetadata::from_trust_ir_name(func.name.clone()))
        .collect();
    let lowering_certificate_count = result.proofs.as_ref().map_or(0, Vec::len);
    let verified_lowering_certificate_count = result.proofs.as_ref().map_or(0, |proofs| {
        proofs.iter().filter(|proof| proof.verified).count()
    });

    InstallArtifactDetails {
        functions,
        proofs: install_proof_summary(
            proofs_required,
            lowering_certificate_count,
            verified_lowering_certificate_count,
            None,
            true,
            0,
        ),
        ..InstallArtifactDetails::default()
    }
}

fn executable_payload_from_result(result: JitCompilationResult) -> ExecutableArtifactPayload {
    let functions = result
        .per_function_metrics
        .iter()
        .map(FunctionArtifactMetadata::from_quality_metrics)
        .collect();
    ExecutableArtifactPayload {
        buffer: Arc::new(result.buffer),
        metrics: result.metrics,
        trace: result.trace,
        proofs: result.proofs,
        functions,
    }
}

fn install_details_from_executable_result(
    result: &JitCompilationResult,
    proofs_required: bool,
) -> InstallArtifactDetails {
    let functions: Vec<_> = result
        .per_function_metrics
        .iter()
        .map(FunctionArtifactMetadata::from_quality_metrics)
        .collect();
    let lowering_certificate_count = result.proofs.as_ref().map_or(0, Vec::len);
    let verified_lowering_certificate_count = result.proofs.as_ref().map_or(0, |proofs| {
        proofs.iter().filter(|proof| proof.verified).count()
    });
    let mut exported_entrypoints: Vec<_> = result
        .buffer
        .symbols()
        .map(|(name, offset_bytes)| EntryPointMetadata {
            name: name.to_owned(),
            offset_bytes,
        })
        .collect();
    exported_entrypoints.sort_by(|left, right| left.name.cmp(&right.name));

    let counters = exported_entrypoints
        .iter()
        .map(|entrypoint| CounterSummary {
            name: entrypoint.name.clone(),
            entry_count: result.buffer.entry_count(&entrypoint.name),
        })
        .collect();

    InstallArtifactDetails {
        exported_entrypoints,
        functions,
        proofs: install_proof_summary(
            proofs_required,
            lowering_certificate_count,
            verified_lowering_certificate_count,
            Some(result.buffer.certificates().count()),
            result.buffer.all_verified(),
            result.metrics.function_count,
        ),
        counters,
        replay_report_metadata: None,
        ..InstallArtifactDetails::default()
    }
}

fn replay_report_metadata_from_executable_result(
    result: &JitCompilationResult,
    request: &CompileRequest,
    provenance: &ArtifactProvenance,
    generation: CompileGeneration,
    identity: &ArtifactIdentity,
    installed_payload_binding: &InstalledPayloadBinding,
) -> JitReplayReportMetadata {
    let mut report = result.buffer.replay_report_metadata();
    report.artifact_id = Some(identity.as_str().to_owned());
    report.target = Some(installed_payload_binding.compiler_target_triple.clone());
    report.properties.insert(
        "trust_ir_module_sha256".to_owned(),
        installed_payload_binding.trust_ir_module_sha256.clone(),
    );
    report.properties.insert(
        "installed_payload_binding_sha256".to_owned(),
        installed_payload_binding.binding_sha256().to_owned(),
    );
    report.properties.insert(
        "published_image_sha256".to_owned(),
        installed_payload_binding.published_image_sha256.clone(),
    );
    report.properties.insert(
        "allocation_size_bytes".to_owned(),
        installed_payload_binding.allocation_size_bytes.to_string(),
    );
    report
        .properties
        .insert("generation".to_owned(), generation.get().to_string());
    report.properties.insert(
        "install_disposition".to_owned(),
        install_disposition_for_request(request, InstallProofSummary::default())
            .as_str()
            .to_owned(),
    );
    report.properties.insert(
        "proof_policy_checksum".to_owned(),
        request.proof_policy.checksum().to_string(),
    );
    report.properties.insert(
        "proof_policy_mode".to_owned(),
        proof_mode_str(&request.proof_policy.mode).to_owned(),
    );

    if let Some(source_fingerprint) = &provenance.source_fingerprint {
        report
            .properties
            .insert("source_fingerprint".to_owned(), source_fingerprint.clone());
    }

    if let Some(manifest) = &request.artifact_manifest {
        report.properties.insert(
            "artifact_manifest_checksum".to_owned(),
            manifest.checksum().to_string(),
        );
        report.properties.insert(
            "manifest_proof_policy_checksum".to_owned(),
            manifest.proof_policy.checksum().to_string(),
        );
        report.properties.insert(
            "layout_checksum".to_owned(),
            manifest.layout.checksum().to_string(),
        );
        report.properties.insert(
            "invalidation_key".to_owned(),
            manifest.invalidation.checksum().to_string(),
        );
    }

    report
}

fn install_proof_summary(
    proofs_required: bool,
    lowering_certificate_count: usize,
    verified_lowering_certificate_count: usize,
    jit_certificate_count: Option<usize>,
    all_jit_certificates_verified: bool,
    function_count: usize,
) -> InstallProofSummary {
    let (policy_status, rejection_code) = if !proofs_required {
        (ProofPolicyStatus::NotRequired, None)
    } else if lowering_certificate_count == 0 {
        (
            ProofPolicyStatus::Rejected,
            Some(ProofRejectionCode::MissingLoweringCertificates),
        )
    } else if lowering_certificate_count != verified_lowering_certificate_count {
        (
            ProofPolicyStatus::Rejected,
            Some(ProofRejectionCode::UnverifiedLoweringCertificates),
        )
    } else if let Some(jit_certificate_count) = jit_certificate_count {
        if jit_certificate_count < function_count {
            (
                ProofPolicyStatus::Rejected,
                Some(ProofRejectionCode::MissingJitCertificates),
            )
        } else if !all_jit_certificates_verified {
            (
                ProofPolicyStatus::Rejected,
                Some(ProofRejectionCode::UnverifiedJitCertificates),
            )
        } else {
            (ProofPolicyStatus::Satisfied, None)
        }
    } else {
        (ProofPolicyStatus::Satisfied, None)
    };

    InstallProofSummary {
        policy_status,
        rejection_code,
        lowering_certificate_count,
        verified_lowering_certificate_count,
        jit_certificate_count: jit_certificate_count.unwrap_or(0),
        all_jit_certificates_verified,
    }
}

fn artifact_identity_for_module(
    request: &CompileRequest,
    module: &trust_ir::Module,
) -> Result<ArtifactIdentity, CompileDiagnostic> {
    let module_bytes = encode_tmbc(module).map_err(|error| {
        CompileDiagnostic::error(
            "compile.identity_input",
            format!("failed to encode canonical trust_ir module bytes: {error}"),
        )
        .with_phase("artifact_identity")
    })?;
    let exported_symbols = module.functions.iter().map(|func| func.name.clone());
    Ok(ArtifactIdentityInput::from_request(request, module_bytes, exported_symbols).identity())
}

fn raw_extern_bindings_from_map(
    extern_symbols: &HashMap<String, *const u8>,
) -> Vec<RawExternBinding> {
    let mut bindings: Vec<_> = extern_symbols
        .iter()
        .map(|(symbol, address)| RawExternBinding::new(symbol.clone(), *address as usize))
        .collect();
    bindings.sort_by(|left, right| left.symbol.cmp(&right.symbol));
    bindings
}

fn hash_bytes(hasher: &mut StableHasher, bytes: &[u8]) {
    hasher.write_framed(bytes);
}

fn hash_str(hasher: &mut StableHasher, value: &str) {
    hasher.write_str(value);
}

fn hash_optional_str(hasher: &mut StableHasher, value: Option<&str>) {
    match value {
        Some(value) => {
            hash_bool(hasher, true);
            hash_str(hasher, value);
        }
        None => hash_bool(hasher, false),
    }
}

fn hash_bool(hasher: &mut StableHasher, value: bool) {
    hasher.write_u8(u8::from(value));
}

fn hash_u64(hasher: &mut StableHasher, value: u64) {
    hasher.write_u64(value);
}

fn hash_usize(hasher: &mut StableHasher, value: usize) {
    hash_u64(hasher, value as u64);
}

fn hash_option_u64(hasher: &mut StableHasher, value: Option<u64>) {
    match value {
        Some(value) => {
            hash_bool(hasher, true);
            hash_u64(hasher, value);
        }
        None => hash_bool(hasher, false),
    }
}

fn hash_u128(hasher: &mut StableHasher, value: u128) {
    hash_u64(hasher, value as u64);
    hash_u64(hasher, (value >> 64) as u64);
}

fn hash_target(hasher: &mut StableHasher, target: Target) {
    hash_str(hasher, target.name());
}

fn hash_opt_level(hasher: &mut StableHasher, opt_level: OptLevel) {
    let tag = match opt_level {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        OptLevel::O3 => "O3",
    };
    hash_str(hasher, tag);
}

fn hash_dispatch_verify_mode(hasher: &mut StableHasher, mode: DispatchVerifyMode) {
    let tag = match mode {
        DispatchVerifyMode::Off => "off".to_owned(),
        DispatchVerifyMode::FallbackOnFailure => "fallback_on_failure".to_owned(),
        DispatchVerifyMode::ErrorOnFailure => "error_on_failure".to_owned(),
        // The modulus changes which functions are verified, so it must key
        // the cache exactly like the mode tag itself.
        DispatchVerifyMode::Sampled { modulus } => format!("sampled:{modulus}"),
    };
    hash_str(hasher, &tag);
}

fn hash_profile_hook_mode(hasher: &mut StableHasher, mode: ProfileHookMode) {
    let tag = match mode {
        ProfileHookMode::None => "none",
        ProfileHookMode::CallCounts => "call_counts",
        ProfileHookMode::CallCountsAndTiming => "call_counts_and_timing",
        ProfileHookMode::BlockCounts => "block_counts",
        ProfileHookMode::BlockCountsAndTiming => "block_counts_and_timing",
        ProfileHookMode::EdgeCounts => "edge_counts",
        ProfileHookMode::BlockFrequency => "block_frequency",
        ProfileHookMode::LoopHeads => "loop_heads",
    };
    hash_str(hasher, tag);
}

fn hash_compiler_trace_level(hasher: &mut StableHasher, trace_level: CompilerTraceLevel) {
    let tag = match trace_level {
        CompilerTraceLevel::None => "none",
        CompilerTraceLevel::Summary => "summary",
        CompilerTraceLevel::Full => "full",
    };
    hash_str(hasher, tag);
}

fn hash_profile_id(hasher: &mut StableHasher, profile: CompileProfileId) {
    let tag = match profile {
        CompileProfileId::FastAarch64Solver => "fast_aarch64_solver",
        CompileProfileId::HostJitFast => "host_jit_fast",
        CompileProfileId::Custom => "custom",
    };
    hash_str(hasher, tag);
}

fn hash_artifact_kind(hasher: &mut StableHasher, artifact_kind: ArtifactKind) {
    let tag = match artifact_kind {
        ArtifactKind::Object => "object",
        ArtifactKind::ExecutableMemory => "executable_memory",
    };
    hash_str(hasher, tag);
}

fn hash_install_intent(hasher: &mut StableHasher, install_intent: InstallIntent) {
    let tag = match install_intent {
        InstallIntent::CompileOnly => "compile_only",
        InstallIntent::Install => "install",
    };
    hash_str(hasher, tag);
}

fn proof_mode_str(mode: &ProofMode) -> &'static str {
    match mode {
        ProofMode::Disabled => "disabled",
        ProofMode::AuditOnly => "audit_only",
        ProofMode::RequireCertificates => "require_certificates",
        ProofMode::RequireReplay => "require_replay",
    }
}

fn hash_proof_policy(hasher: &mut StableHasher, proof_policy: &ProofPolicy) {
    hash_str(hasher, "trust-cg.compile_service.proof_policy.v1");
    hash_str(hasher, proof_mode_str(&proof_policy.mode));
    hash_bool(hasher, proof_policy.require_jit_certificate);
    hash_bool(hasher, proof_policy.require_layout_evidence);
    hash_bool(hasher, proof_policy.require_abi_evidence);
    let accepted_solvers = normalized_solver_names(&proof_policy.accepted_solvers);
    hash_usize(hasher, accepted_solvers.len());
    for solver in accepted_solvers {
        hash_str(hasher, solver);
    }
    hash_option_u64(hasher, proof_policy.max_replay_age_generations);
    hash_u128(hasher, proof_policy.checksum().get());
}

fn normalized_solver_names(solvers: &[String]) -> Vec<&str> {
    let mut solvers = solvers.iter().map(String::as_str).collect::<Vec<_>>();
    solvers.sort_unstable();
    solvers.dedup();
    solvers
}

fn hash_compiler_config(hasher: &mut StableHasher, config: &CompilerConfig) {
    hash_opt_level(hasher, config.opt_level);
    hash_target(hasher, config.target);
    hash_bool(hasher, config.emit_proofs);
    hash_compiler_trace_level(hasher, config.trace_level);
    hash_bool(hasher, config.emit_debug);
    hash_bool(hasher, config.parallel);
    hash_option_u64(hasher, config.cegis_superopt_budget_sec);
}

fn hash_jit_config(hasher: &mut StableHasher, config: &JitConfig) {
    hash_opt_level(hasher, config.opt_level);
    hash_bool(hasher, config.verify);
    hash_dispatch_verify_mode(hasher, config.verify_dispatch);
    hash_profile_hook_mode(hasher, config.profile_hooks);
    hash_bool(hasher, config.emit_entry_counters);
}

impl Default for CompileService {
    fn default() -> Self {
        Self::new(CompileServiceConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile_artifact_cache_profile::{
        CompileArtifactCacheBoundary, CompileArtifactCacheConfig, CompileArtifactCacheStatus,
        CompileArtifactDependencyIdentity, CompileArtifactProofPolicy,
    };
    use crate::compiler::CompilerTraceLevel;
    use crate::jit::JitConfig;
    #[cfg(target_arch = "aarch64")]
    use crate::jit_install_gate::{
        NATIVE_INSTALL_GATE_PACKET_SCHEMA, PetriNativeSuccessorCompileArtifactHandoffBlocker,
        PetriNativeSuccessorExecutableCallStatus, PetriNativeSuccessorManifestIdentityBlocker,
        PetriNativeSuccessorRuntimeReadinessBlocker, PetriNativeSuccessorRuntimeReadinessStatus,
    };
    use crate::jit_install_gate::{
        NATIVE_INSTALL_GATE_REPLAY_SCHEMA, NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
        NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA, NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
        NativeInstallGateDenyControlPlane, NativeInstallGateDenyReason, NativeInstallGateDenyScope,
        NativeInstallGateLayoutAccess, NativeInstallGateLayoutEvidence,
        NativeInstallGateReplayIdentity, NativeInstallGateTelemetryInput,
        persist_native_install_gate_packet_bindings,
    };
    use trust_ir::{
        Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
        Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
    };

    fn service() -> CompileService {
        CompileService::default()
    }

    fn temp_cache_root(name: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "trust-cg-service-artifact-cache-{}-{}-{}",
            name,
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|duration| duration.as_nanos())
                .unwrap_or(0)
        ))
    }

    fn service_cache_config(root: &std::path::Path) -> CompileArtifactCacheConfig {
        CompileArtifactCacheConfig::new(
            root,
            CompileArtifactProofPolicy::Unchecked,
            CompileArtifactDependencyIdentity::new(
                "trust-cg:test",
                "trust_ir:test",
                "ay:test",
                "rustc:test",
                "cargo:test",
                "trust",
            ),
        )
    }

    fn artifact(generation: CompileGeneration) -> CompiledArtifact {
        CompiledArtifact::metadata_only("artifact", generation)
    }

    fn identity_for(
        request_id: &str,
        module_bytes: &[u8],
        target: Target,
        profile_id: CompileProfileId,
        exports: &[&str],
    ) -> ArtifactIdentity {
        let profile = CompileProfile::Custom {
            compiler: CompilerConfig::jit_fast(target),
            jit: JitConfig {
                opt_level: OptLevel::O1,
                verify: false,
                verify_dispatch: DispatchVerifyMode::ErrorOnFailure,
                profile_hooks: ProfileHookMode::None,
                emit_entry_counters: false,
                ..JitConfig::default()
            },
        };
        let mut request = CompileRequest::new(request_id, CompileGeneration::new(1));
        request.profile = profile;
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        let mut input =
            ArtifactIdentityInput::from_request(&request, module_bytes, exports.iter().copied());
        input.profile = profile_id;
        input.identity()
    }

    fn deterministic_manifest(artifact_id: &str) -> ArtifactManifestV1 {
        let target_spec = TargetSpec::default_for_architecture(Target::Aarch64);
        let target = crate::jit_contract::TargetDescriptor::for_trust_cg_target_spec(target_spec);
        let abi = crate::jit_contract::AbiDescriptor::for_trust_cg_target_os(
            Target::Aarch64,
            target.operating_system.clone(),
        );
        let layout = crate::jit_contract::LayoutManifest::lp64(
            crate::jit_contract::Endianness::Little,
            Target::Aarch64.stack_alignment() as u16,
        );
        let proof_policy = crate::jit_contract::ProofPolicy::disabled();
        let invalidation = crate::jit_contract::InvalidationKey::new(
            "sha256:test-module",
            "trust-cg-codegen:FastAarch64Solver",
            target.checksum(),
            abi.checksum(),
            layout.checksum(),
            proof_policy.checksum(),
            12,
        );

        ArtifactManifestV1::new(
            artifact_id,
            crate::jit_contract::JitArtifactKind::Object,
            target,
            abi,
            layout,
            invalidation,
            proof_policy,
        )
    }

    fn native_install_manifest(artifact_id: &str, generation: u64) -> ArtifactManifestV1 {
        let target_spec = TargetSpec::default_for_architecture(Target::host());
        let target = crate::jit_contract::TargetDescriptor::for_trust_cg_target_spec(target_spec);
        let abi = crate::jit_contract::AbiDescriptor::for_trust_cg_target_os(
            Target::host(),
            target.operating_system.clone(),
        );
        let layout = crate::jit_contract::LayoutManifest::lp64(
            crate::jit_contract::Endianness::Little,
            Target::host().stack_alignment() as u16,
        );
        let proof_policy = crate::jit_contract::ProofPolicy::disabled();
        let invalidation = crate::jit_contract::InvalidationKey::new(
            "sha256:native-install-source",
            "trust-cg-codegen:HostJitFast",
            target.checksum(),
            abi.checksum(),
            layout.checksum(),
            proof_policy.checksum(),
            generation,
        );

        let mut manifest = ArtifactManifestV1::new(
            artifact_id,
            crate::jit_contract::JitArtifactKind::ExecutableMemory,
            target,
            abi,
            layout,
            invalidation,
            proof_policy,
        );
        crate::jit_contract::bind_host_jit_target_feature_profile_metadata(&mut manifest);
        manifest
    }

    fn native_install_payload_identity() -> NativeInstallGatePayloadIdentity {
        NativeInstallGatePayloadIdentity {
            source_sha256: "sha256:native-install-source".to_owned(),
            trust_ir_sha256: "sha256:native-install-trust_ir".to_owned(),
            native_payload_sha256: "sha256:native-install-payload".to_owned(),
        }
    }

    fn native_install_gate_input(manifest: &ArtifactManifestV1) -> NativeInstallGateInput {
        let expected = NativeInstallGateExpectedBindings::from_manifest(manifest);
        let payload_identity = native_install_payload_identity();
        let proof_evidence = NativeInstallGateProofEvidence {
            summary: ProofEvidenceSummary::verified(
                "compile_service.synthetic",
                manifest.target.checksum(),
                manifest.abi.checksum(),
                manifest.layout.checksum(),
                manifest.invalidation.checksum(),
                manifest.proof_policy.checksum(),
            ),
            proof_report_sha256: Some("sha256:native-install-proof-report".to_owned()),
            obligation_set: Some("compile-service-direct-install".to_owned()),
            timeout_ms: Some(1_000),
            native_payload_sha256: Some(payload_identity.native_payload_sha256.clone()),
        };
        let counter_scope = format!(
            "{}:{}:{}:{}",
            "ay",
            "direct-compile-test",
            NativeInstallGateSurface::DirectCompileInstall.as_str(),
            expected.artifact_id
        );
        let telemetry = NativeInstallGateTelemetryInput {
            schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
            schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
            event_id: "compile-service-direct-install-gate".to_owned(),
            counter_scope,
            record_sha256: String::new(),
            artifact_id: expected.artifact_id.clone(),
            manifest_checksum: expected.manifest_checksum,
            proof_report_sha256: proof_evidence.proof_report_sha256.clone(),
            layout_checksum: expected.layout_checksum,
            invalidation_checksum: expected.invalidation_checksum,
            disposition: NativeInstallGateDisposition::Installable,
            rejection_code: None,
            install_authority: NativeInstallGateAuthority::CanaryCallable,
            useful_native_delta: 0,
        }
        .with_canonical_record_sha256();
        let replay_identity = NativeInstallGateReplayIdentity {
            schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
            schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
            replay_root_sha256: "sha256:compile-service-direct-install-replay".to_owned(),
            replay_consumer: "ay".to_owned(),
            replay_family: "direct-compile-test".to_owned(),
            artifact_id: expected.artifact_id.clone(),
            source_sha256: payload_identity.source_sha256.clone(),
            trust_ir_sha256: payload_identity.trust_ir_sha256.clone(),
            native_payload_sha256: payload_identity.native_payload_sha256.clone(),
            replay_record_sha256: String::new(),
        }
        .with_canonical_record_sha256();

        NativeInstallGateInput {
            consumer: "ay".to_owned(),
            consumer_mode: "direct-compile-test".to_owned(),
            surface: NativeInstallGateSurface::DirectCompileInstall,
            candidate_disposition: NativeInstallGateDisposition::Installable,
            requested_authority: NativeInstallGateAuthority::CanaryCallable,
            manifest: Some(manifest.clone()),
            manifest_reference: Some(ArtifactManifestReference::from_manifest(manifest)),
            expected,
            payload_identity: payload_identity.clone(),
            candidate_payload_identity: payload_identity,
            layout_evidence: Some(
                NativeInstallGateLayoutEvidence {
                    layout_checksum: manifest.layout.checksum(),
                    abi_checksum: manifest.abi.checksum(),
                    invalidation_checksum: manifest.invalidation.checksum(),
                    validation_provenance: "trust-cg.compile_service.layout_adapter.v1".to_owned(),
                    evidence_sha256: None,
                    wrapper_identity: Some("compile-service-wrapper.v1".to_owned()),
                    regions: vec![NativeInstallGateLayoutEvidence::region(
                        "compile_service_region",
                        "direct_compile_artifact",
                        8,
                        1024,
                        NativeInstallGateLayoutAccess::ReadWrite,
                        "compile-service-alias",
                        "compile_service_generation",
                    )],
                    entry_abis: vec![NativeInstallGateLayoutEvidence::entry_abi(
                        "compile_service_entry",
                        manifest.abi.checksum(),
                        &["compile_service_region"],
                        "compile_service_region",
                        "compile_service_generation",
                    )],
                }
                .with_canonical_evidence_sha256(),
            ),
            proof_evidence: Some(proof_evidence),
            current_invalidation_checksum: manifest.invalidation.checksum(),
            artifact_generation: manifest.invalidation.generation,
            current_generation: manifest.invalidation.generation,
            revoked: false,
            deny_control: None,
            replay_identity: Some(replay_identity),
            telemetry: Some(telemetry),
        }
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn native_install_response(
        input: NativeInstallGateInput,
        manifest: Option<ArtifactManifestV1>,
    ) -> CompileResponse {
        native_install_response_with_value(input, manifest, 42)
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn native_install_response_with_value(
        input: NativeInstallGateInput,
        manifest: Option<ArtifactManifestV1>,
        value: i64,
    ) -> CompileResponse {
        let generation = CompileGeneration::new(input.expected.current_generation);
        let module = const_i64_module("compile_service_native_install_gate", &[("answer", value)]);
        let mut request = CompileRequest::new(
            format!("native-install-gate-{}", input.expected.artifact_id),
            generation,
        );
        if let Some(manifest) = manifest {
            request = request.with_artifact_manifest(manifest);
        }
        request.provenance.source_kind = SourceKind::TrustIrModule;
        request.provenance.source_fingerprint = Some(input.payload_identity.source_sha256.clone());
        request
            .provenance
            .caller_context
            .insert("native_install_consumer".to_owned(), input.consumer.clone());
        request.provenance.caller_context.insert(
            "native_install_consumer_mode".to_owned(),
            input.consumer_mode.clone(),
        );
        request.provenance.caller_context.insert(
            "trust_ir_sha256".to_owned(),
            input.payload_identity.trust_ir_sha256.clone(),
        );

        let mut response = service().compile(request, &module);
        assert_eq!(response.status, CompileStatus::Compiled);
        assert!(matches!(
            response.payload.as_ref(),
            Some(ArtifactPayload::Executable(_))
        ));
        response
            .artifact
            .as_mut()
            .expect("compiled artifact")
            .install
            .native_install_gate_input = Some(input);
        response
    }

    fn required_proof_policy() -> ProofPolicy {
        ProofPolicy::require_certificates(["trust-cg-verify"])
    }

    fn assert_no_useful_native(summary: &ProofInstallTelemetrySummary) {
        assert_eq!(summary.schema, ProofInstallTelemetrySummary::SCHEMA);
        assert_eq!(
            summary.schema_version,
            ProofInstallTelemetrySummary::SCHEMA_VERSION
        );
        assert!(!summary.useful_native_eligible);
        assert_eq!(summary.useful_native_count, 0);
        assert_eq!(summary.install_authority_blocked_on, Some("#681"));
    }

    fn const_i64_module(module_name: &str, functions: &[(&str, i64)]) -> TrustIrModule {
        let mut module = TrustIrModule::new(module_name);
        let ft_id = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });

        for (idx, (name, value)) in functions.iter().enumerate() {
            let mut func =
                TrustIrFunction::new(FuncId::new(idx as u32), *name, ft_id, BlockId::new(0));
            func.blocks = vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int((*value).into()),
                    })
                    .with_result(ValueId::new(0)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(0)],
                    }),
                ],
            }];
            module.add_function(func);
        }

        module
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn compile_manifest_bound_executable(
        request_id: &str,
        module: &TrustIrModule,
        manifest: ArtifactManifestV1,
    ) -> CompileResponse {
        let generation = CompileGeneration::new(manifest.invalidation.generation);
        let mut request =
            CompileRequest::new(request_id, generation).with_artifact_manifest(manifest);
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.provenance.source_kind = SourceKind::TrustIrModule;
        request.provenance.source_fingerprint = Some(format!("sha256:{request_id}-source"));
        service().compile(request, module)
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn installed_binding_validation_error(response: &CompileResponse) -> String {
        let artifact = response.artifact.as_ref().expect("compiled artifact");
        let buffer = match response.payload.as_ref().expect("compiled payload") {
            ArtifactPayload::Executable(payload) => &payload.buffer,
            ArtifactPayload::Object(_) => panic!("expected executable payload"),
        };
        validate_installed_payload_binding(
            &artifact.install,
            artifact.artifact_manifest.as_ref(),
            buffer,
        )
        .expect_err("adversarial binding must fail closed")
        .to_string()
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn assert_binding_mutation_rejected(
        base: &CompileResponse,
        expected_detail: &str,
        mutate: impl FnOnce(&mut CompileResponse),
    ) {
        let mut response = base.clone();
        mutate(&mut response);
        let detail = installed_binding_validation_error(&response);
        assert!(
            detail.contains(expected_detail),
            "expected binding rejection containing {expected_detail:?}, got {detail:?}"
        );
        assert!(response.native_install_gate_packet().is_none());
        assert!(response.into_installed_artifact().is_none());
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn mutate_and_reseal_installed_binding(
        response: &mut CompileResponse,
        mutate: impl FnOnce(&mut InstalledPayloadBinding),
    ) {
        let artifact = response.artifact.as_mut().expect("compiled artifact");
        let manifest = artifact.artifact_manifest.clone();
        let binding = artifact
            .install
            .installed_payload_binding
            .as_mut()
            .expect("installed payload binding");
        mutate(binding);
        binding.binding_sha256 = installed_payload_binding_sha256(binding, manifest.as_ref());
    }

    fn remove_reserved_metadata_namespace(manifest: &mut ArtifactManifestV1, prefix: &str) {
        manifest.metadata.retain(|key, _| !key.starts_with(prefix));
    }

    fn verifier_reject_request(request_id: &str) -> CompileRequest {
        let mut request = CompileRequest::new(request_id, CompileGeneration::new(704));
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.provenance.source_kind = SourceKind::TrustIrModule;
        request.provenance.source_fingerprint = Some(format!("sha256:{request_id}-source"));
        request.provenance.upstream_issue = Some(704);
        request
    }

    fn verifier_reject_module(module_name: &str, blocks: Vec<TrustIrBlock>) -> TrustIrModule {
        let mut module = TrustIrModule::new(module_name);
        let ft_id = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut func = TrustIrFunction::new(FuncId::new(0), "reject_me", ft_id, BlockId::new(0));
        func.blocks = blocks;
        module.add_function(func);
        module
    }

    fn assert_verifier_rejected_response(response: CompileResponse, failure_code: &'static str) {
        assert_eq!(response.status, CompileStatus::Rejected);
        assert_eq!(response.disposition, ArtifactInstallDisposition::Rejected);
        assert!(response.payload.is_none());
        assert_eq!(response.diagnostics[0].code, failure_code);
        assert_eq!(
            response.diagnostics[0].phase.as_deref(),
            Some("before_executable_allocation")
        );
        assert!(response.clone().into_installed_artifact().is_none());

        let artifact = response.artifact.expect("metadata-only rejected artifact");
        assert_eq!(
            artifact.install.disposition,
            ArtifactInstallDisposition::Rejected
        );
        assert!(artifact.install.exported_entrypoints.is_empty());
        assert!(artifact.install.counters.is_empty());
        assert!(artifact.install.functions.is_empty());
        assert_eq!(artifact.metadata.allocation_size_bytes, None);

        let report = artifact
            .install
            .replay_report_metadata
            .expect("verifier rejection replay metadata");
        assert_eq!(report.code_size, 0);
        assert_eq!(
            report
                .properties
                .get("failure_category")
                .map(String::as_str),
            Some("verifier_rejected")
        );
        assert_eq!(
            report.properties.get("failure_code").map(String::as_str),
            Some(failure_code)
        );
        assert_eq!(
            report
                .properties
                .get("install_disposition")
                .map(String::as_str),
            Some("rejected")
        );
        assert_eq!(
            report.properties.get("generation").map(String::as_str),
            Some("704")
        );
        assert_eq!(
            report.properties.get("upstream_issue").map(String::as_str),
            Some("704")
        );
        assert!(report.properties.contains_key("source_fingerprint"));
        assert_eq!(
            report.properties.get("issue_refs").map(String::as_str),
            Some("#704,#657,#661")
        );
        assert_eq!(report.statuses.len(), 1);
        assert_eq!(report.statuses[0].kind, JitTrapStatusKind::VerifierRejected);
        assert_eq!(
            report.statuses[0].stage,
            "compile_service.trust_ir_verifier"
        );
        assert!(
            report.statuses[0]
                .message
                .as_deref()
                .expect("status message")
                .contains(failure_code)
        );
    }

    #[test]
    fn invalid_block_args_reject_before_executable_allocation_with_replay() {
        let entry = TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Br {
                target: BlockId::new(1),
                args: vec![],
            })],
        };
        let exit = TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(10), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)],
            })],
        };
        let module = verifier_reject_module("invalid_block_args", vec![entry, exit]);

        let response = service().compile(verifier_reject_request("invalid-block-args"), &module);

        assert_verifier_rejected_response(response, "trust_ir_invalid_block_args");
    }

    #[test]
    fn duplicate_edge_copy_destinations_reject_before_executable_allocation_with_replay() {
        let entry = TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(0), ValueId::new(1)],
                }),
            ],
        };
        let exit = TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(10), Ty::I64), (ValueId::new(10), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)],
            })],
        };
        let module = verifier_reject_module("duplicate_edge_copy_dests", vec![entry, exit]);

        let response = service().compile(
            verifier_reject_request("duplicate-edge-copy-dests"),
            &module,
        );

        assert_verifier_rejected_response(response, "trust_ir_duplicate_edge_copy_destinations");
    }

    #[test]
    fn unsupported_abi_cast_reject_before_executable_allocation_with_replay() {
        let block = TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty: Ty::I32,
                    dst_ty: Ty::I64,
                    operand: ValueId::new(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(1)],
                }),
            ],
        };
        let module = verifier_reject_module("unsupported_abi_cast", vec![block]);

        let response = service().compile(verifier_reject_request("unsupported-abi-cast"), &module);

        assert_verifier_rejected_response(response, "trust_ir_unsupported_abi_cast");
    }

    #[test]
    fn invalid_provenance_assumption_reject_before_executable_allocation_with_replay() {
        let block = TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Assume {
                    cond: ValueId::new(0),
                }),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        };
        let module = verifier_reject_module("invalid_provenance_assumption", vec![block]);

        let response = service().compile(
            verifier_reject_request("invalid-provenance-assumption"),
            &module,
        );

        assert_verifier_rejected_response(response, "trust_ir_invalid_provenance_assumption");
    }

    #[test]
    fn pre_cancelled_request_returns_cancelled_without_artifact() {
        let mut request = CompileRequest::new("cancelled", CompileGeneration::new(7));
        request.cancellation = CancellationToken::cancelled();

        let response = service().compile_with(request, || panic!("backend work should not run"));

        assert_eq!(response.status, CompileStatus::Cancelled);
        assert!(response.artifact.is_none());
        assert_eq!(response.diagnostics[0].code, "compile.cancelled");

        let reject = response.explain_reject().expect("cancelled reject");
        assert_eq!(reject.code, RejectCode::Cancelled);
        assert_eq!(reject.code.as_str(), "cancelled");
        assert_eq!(reject.status, CompileStatus::Cancelled);
        assert_eq!(reject.diagnostic_code, "compile.cancelled");
        assert_eq!(reject.phase.as_deref(), Some("before_compile"));
    }

    #[test]
    fn stale_before_request_returns_stale_without_artifact() {
        let mut request = CompileRequest::new("stale", CompileGeneration::new(4));
        request.stale_before = Some(CompileGeneration::new(5));

        let response = service().compile_with(request, || panic!("backend work should not run"));

        assert_eq!(response.status, CompileStatus::Stale);
        assert!(response.artifact.is_none());
        assert_eq!(response.diagnostics[0].code, "compile.stale");

        let reject = response.explain_reject().expect("stale reject");
        assert_eq!(reject.code, RejectCode::StaleGeneration);
        assert_eq!(reject.code.as_str(), "stale_generation");
        assert_eq!(reject.status, CompileStatus::Stale);
        assert_eq!(reject.diagnostic_code, "compile.stale");
        assert_eq!(reject.phase.as_deref(), Some("before_compile"));

        let summary = response.proof_install_telemetry_summary();
        assert_eq!(summary.rejection_category, Some("stale"));
        assert_eq!(summary.diagnostic_code, Some("compile.stale"));
        assert_eq!(summary.proof_tv_code, None);
        assert_no_useful_native(&summary);
    }

    #[test]
    fn stale_before_install_drops_finished_artifact() {
        let fence = CompileGenerationFence::new();
        let mut request = CompileRequest::new("stale-install", CompileGeneration::new(9));
        request.generation_fence = Some(fence.clone());

        let response = service().compile_with(request, || {
            fence.mark_stale_before(CompileGeneration::new(10));
            Ok(artifact(CompileGeneration::new(9)))
        });

        assert_eq!(response.status, CompileStatus::Stale);
        assert!(response.artifact.is_none());
        assert_eq!(response.diagnostics[0].code, "compile.stale");
        assert!(response.diagnostics[0].message.contains("before_install"));

        let reject = response.explain_reject().expect("stale install reject");
        assert_eq!(reject.code, RejectCode::StaleGeneration);
        assert_eq!(reject.phase.as_deref(), Some("before_install"));
    }

    #[test]
    fn explain_reject_uses_stable_fallback_without_diagnostic() {
        let response = CompileResponse {
            request_id: CompileRequestId::new("manual-reject"),
            generation: CompileGeneration::new(1),
            status: CompileStatus::Rejected,
            disposition: ArtifactInstallDisposition::Rejected,
            artifact: None,
            payload: None,
            diagnostics: Vec::new(),
        };

        let reject = response.explain_reject().expect("manual reject");
        assert_eq!(reject.code, RejectCode::Rejected);
        assert_eq!(reject.status, CompileStatus::Rejected);
        assert_eq!(reject.diagnostic_code, "compile.rejected");
        assert_eq!(reject.message, None);
        assert_eq!(reject.phase, None);
    }

    #[test]
    fn fast_aarch64_solver_profile_expands_to_low_latency_knobs() {
        let expanded = CompileProfile::FastAarch64Solver.expand();

        assert_eq!(
            CompileProfile::FastAarch64Solver.id(),
            CompileProfileId::FastAarch64Solver
        );
        assert_eq!(expanded.compiler.opt_level, OptLevel::O1);
        assert_eq!(expanded.compiler.target, Target::Aarch64);
        assert!(!expanded.compiler.emit_proofs);
        assert_eq!(expanded.compiler.trace_level, CompilerTraceLevel::None);
        assert!(!expanded.compiler.emit_debug);
        assert!(!expanded.compiler.parallel);
        assert_eq!(expanded.compiler.cegis_superopt_budget_sec, None);
        assert_eq!(expanded.jit.opt_level, OptLevel::O1);
        assert!(!expanded.jit.verify);
        assert_eq!(
            expanded.jit.verify_dispatch,
            DispatchVerifyMode::ErrorOnFailure
        );
        assert_eq!(expanded.jit.profile_hooks, ProfileHookMode::None);
        assert!(!expanded.jit.emit_entry_counters);
        assert_eq!(expanded.artifact_kind, ArtifactKind::ExecutableMemory);
    }

    #[test]
    fn default_request_uses_host_jit_metadata_surface() {
        let request = CompileRequest::new("req-1", CompileGeneration::new(11));

        assert_eq!(request.request_id.as_str(), "req-1");
        assert_eq!(request.generation.get(), 11);
        assert_eq!(request.artifact_kind, ArtifactKind::ExecutableMemory);
        assert_eq!(request.install_intent, InstallIntent::Install);
        assert_eq!(request.profile.id(), CompileProfileId::HostJitFast);
        assert_eq!(request.provenance.producer, "trust-cg-codegen");
        assert_eq!(request.provenance.source_kind, SourceKind::Unspecified);
        assert!(request.provenance.caller_context.is_empty());
        assert!(request.artifact_manifest.is_none());
        assert!(!request.cancellation.is_cancelled());
    }

    #[test]
    fn compile_only_request_marks_artifact_profile_only() {
        let mut request = CompileRequest::new("profile-only", CompileGeneration::new(13));
        request.install_intent = InstallIntent::CompileOnly;

        let response = service().compile_with(request, || Ok(artifact(CompileGeneration::new(13))));

        assert_eq!(response.status, CompileStatus::Compiled);
        {
            let artifact = response.artifact.as_ref().expect("compiled artifact");
            assert_eq!(
                artifact.install.disposition,
                ArtifactInstallDisposition::ProfileOnly
            );
            assert_eq!(artifact.install.disposition.as_str(), "profile_only");
        }
        let summary = response.proof_install_telemetry_summary();
        assert_eq!(summary.rejection_category, Some("profile_only"));
        assert_eq!(summary.proof_tv_code, None);
        assert_no_useful_native(&summary);
        assert!(response.into_installed_artifact().is_none());
    }

    #[test]
    fn disabled_and_audit_only_compile_summaries_do_not_mark_useful_native_before_681() {
        let disabled_response = service().compile_with(
            CompileRequest::new("disabled-install", CompileGeneration::new(31)),
            || Ok(artifact(CompileGeneration::new(31))),
        );
        let disabled_summary = disabled_response.proof_install_telemetry_summary();
        assert_eq!(disabled_summary.status, CompileStatus::Compiled);
        assert_eq!(
            disabled_summary.install_disposition,
            ArtifactInstallDisposition::Installable
        );
        assert_eq!(
            disabled_summary.rejection_category,
            Some("disabled_or_audit_only")
        );
        assert_no_useful_native(&disabled_summary);

        let mut audit_request =
            CompileRequest::new("audit-only-install", CompileGeneration::new(32));
        audit_request.proof_policy.mode = ProofMode::AuditOnly;
        let audit_response =
            service().compile_with(audit_request, || Ok(artifact(CompileGeneration::new(32))));
        let audit_summary = audit_response.proof_install_telemetry_summary();
        assert_eq!(
            audit_summary.install_disposition,
            ArtifactInstallDisposition::Installable
        );
        assert_eq!(
            audit_summary.rejection_category,
            Some("disabled_or_audit_only")
        );
        assert_no_useful_native(&audit_summary);
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn native_install_gate_accepts_synthetic_direct_compile_packet_before_conversion() {
        let manifest = native_install_manifest("artifact-native-install-accepted", 71);
        let input = native_install_gate_input(&manifest);
        let response = native_install_response(input, Some(manifest));

        let packet = response
            .native_install_gate_packet()
            .expect("native install gate packet");
        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Installable
        );
        assert_eq!(packet.rejection_code, None);
        assert!(packet.actions.expose_callable);
        assert!(packet.actions.useful_native_eligible);

        let summary = response.proof_install_telemetry_summary();
        assert!(summary.useful_native_eligible);
        assert_eq!(summary.useful_native_count, 0);
        assert_eq!(summary.install_authority_blocked_on, None);
        assert_eq!(summary.native_install_gate_disposition, Some("installable"));
        assert_eq!(summary.native_install_gate_code, None);

        let installed = response
            .into_installed_artifact()
            .expect("accepted gate should expose installed artifact");
        let installed_packet = installed
            .metadata
            .native_install_gate
            .as_ref()
            .expect("installed artifact should carry gate packet");
        let installed_telemetry = installed_packet
            .telemetry
            .as_ref()
            .expect("installed artifact should carry canonical gate telemetry");
        assert_eq!(
            installed_packet.disposition,
            NativeInstallGateDisposition::Installable
        );
        assert!(installed_packet.actions.expose_callable);
        let runtime_current = NativeInstallGateRevalidationInput::from_packet(installed_packet);
        let runtime_event = installed
            .native_install_runtime_telemetry(&runtime_current, true)
            .expect("installed artifact should record runtime telemetry");
        assert_eq!(runtime_event.useful_native_delta, 1);
        assert_eq!(runtime_event.packet_hash, installed_packet.packet_hash);
        assert_eq!(
            runtime_event.telemetry_event_id.as_deref(),
            Some(installed_telemetry.event_id.as_str())
        );
        assert_eq!(
            runtime_event.replay_root_sha256.as_deref(),
            Some(installed_packet.replay_binding.replay_root_sha256.as_str())
        );
        let fallback_event = installed
            .native_install_runtime_telemetry(&runtime_current, false)
            .expect("installed artifact should record fallback runtime telemetry");
        assert_eq!(fallback_event.useful_native_delta, 0);

        let stale_manifest = native_install_manifest("artifact-native-install-stale-call", 73);
        let stale_input = native_install_gate_input(&stale_manifest);
        let mut stale_response = native_install_response(stale_input, Some(stale_manifest));
        let mut stale_packet = stale_response
            .native_install_gate_packet()
            .expect("native install gate packet");
        stale_packet.freshness.current_generation += 1;
        persist_native_install_gate_packet_bindings(&mut stale_packet);
        stale_response
            .artifact
            .as_mut()
            .expect("compiled artifact")
            .install
            .native_install_gate = Some(stale_packet);
        assert!(
            stale_response.into_installed_artifact().is_none(),
            "call-time revalidation must reject stale direct-compile packets"
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn native_install_gate_rederives_exact_artifact_and_preserves_negative_controls() {
        let accepted_manifest =
            native_install_manifest("artifact-native-install-packet-donor", 711);
        let accepted_response = native_install_response_with_value(
            native_install_gate_input(&accepted_manifest),
            Some(accepted_manifest),
            41,
        );
        let donor_packet = accepted_response
            .native_install_gate_packet()
            .expect("donor packet");
        assert!(donor_packet.is_installable());

        let candidate_manifest =
            native_install_manifest("artifact-native-install-packet-candidate", 711);
        let mut candidate_input = native_install_gate_input(&candidate_manifest);
        candidate_input.proof_evidence = None;
        let mut candidate_response = native_install_response_with_value(
            candidate_input,
            Some(candidate_manifest.clone()),
            42,
        );
        candidate_response
            .artifact
            .as_mut()
            .expect("compiled candidate")
            .install
            .native_install_gate = Some(donor_packet.clone());

        let derived_packet = candidate_response
            .native_install_gate_packet()
            .expect("candidate packet must be re-derived");
        assert_eq!(
            derived_packet.artifact.artifact_id,
            candidate_manifest.artifact_id
        );
        assert_ne!(
            derived_packet.artifact.native_payload_sha256,
            donor_packet.artifact.native_payload_sha256,
            "a donor packet must not substitute its validated payload binding"
        );
        assert_ne!(derived_packet.packet_hash, donor_packet.packet_hash);
        assert_eq!(
            derived_packet.rejection_code,
            Some(NativeInstallGateRejectionCode::ProofMissingEvidence),
            "the candidate's missing-proof negative control must survive re-derivation"
        );
        assert!(derived_packet.actions.all_install_authority_blocked());
        assert!(candidate_response.into_installed_artifact().is_none());

        let action_manifest =
            native_install_manifest("artifact-native-install-action-negative", 713);
        let mut action_response = native_install_response(
            native_install_gate_input(&action_manifest),
            Some(action_manifest),
        );
        let mut action_packet = action_response
            .native_install_gate_packet()
            .expect("exact action packet");
        action_packet.actions.useful_native_eligible = false;
        persist_native_install_gate_packet_bindings(&mut action_packet);
        action_response
            .artifact
            .as_mut()
            .expect("compiled action candidate")
            .install
            .native_install_gate = Some(action_packet);
        let rederived_action_packet = action_response
            .native_install_gate_packet()
            .expect("negative action must produce a fail-closed packet");
        assert_eq!(
            rederived_action_packet.rejection_code,
            Some(NativeInstallGateRejectionCode::ArtifactIdentityMismatch)
        );
        assert!(
            rederived_action_packet
                .actions
                .all_install_authority_blocked()
        );
        assert!(action_response.into_installed_artifact().is_none());
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn native_install_gate_never_promotes_rejected_artifact_disposition() {
        let manifest = native_install_manifest("artifact-native-install-rejected-disposition", 716);
        let mut response =
            native_install_response(native_install_gate_input(&manifest), Some(manifest));
        response
            .artifact
            .as_mut()
            .expect("compiled artifact")
            .install
            .disposition = ArtifactInstallDisposition::Rejected;

        let packet = response
            .native_install_gate_packet()
            .expect("rejected artifact must retain fail-closed telemetry");
        assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
        assert_eq!(
            packet.rejection_code,
            Some(NativeInstallGateRejectionCode::ArtifactIdentityMismatch)
        );
        assert!(packet.actions.all_install_authority_blocked());
        assert!(response.into_installed_artifact().is_none());
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn native_install_gate_historical_freshness_is_monotone_deny_only() {
        let manifest = native_install_manifest("artifact-native-install-stale-live-input", 717);
        let mut response =
            native_install_response(native_install_gate_input(&manifest), Some(manifest));
        let historical_fresh_packet = response
            .native_install_gate_packet()
            .expect("fresh historical packet");
        assert!(historical_fresh_packet.is_installable());

        let artifact = response.artifact.as_mut().expect("compiled artifact");
        artifact
            .install
            .native_install_gate_input
            .as_mut()
            .expect("live gate input")
            .current_generation += 1;
        artifact.install.native_install_gate = Some(historical_fresh_packet);

        let packet = response
            .native_install_gate_packet()
            .expect("stale live input must retain fail-closed telemetry");
        assert_eq!(
            packet.rejection_code,
            Some(NativeInstallGateRejectionCode::StaleInvalidation)
        );
        assert!(packet.actions.all_install_authority_blocked());
        assert!(response.into_installed_artifact().is_none());
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn native_install_gate_active_historical_deny_beats_inactive_live_control() {
        let manifest = native_install_manifest("artifact-native-install-deny-conflict", 718);
        let mut response =
            native_install_response(native_install_gate_input(&manifest), Some(manifest));
        let mut historical_packet = response
            .native_install_gate_packet()
            .expect("historical packet");
        historical_packet.freshness.deny_control = Some(
            NativeInstallGateDenyControlPlane::active(
                NativeInstallGateDenyScope::Global,
                NativeInstallGateDenyReason::KillSwitch,
            )
            .with_canonical_deny_sha256(),
        );
        persist_native_install_gate_packet_bindings(&mut historical_packet);

        let artifact = response.artifact.as_mut().expect("compiled artifact");
        artifact
            .install
            .native_install_gate_input
            .as_mut()
            .expect("live gate input")
            .deny_control = Some(
            NativeInstallGateDenyControlPlane::inactive(
                NativeInstallGateDenyScope::Global,
                NativeInstallGateDenyReason::KillSwitch,
            )
            .with_canonical_deny_sha256(),
        );
        artifact.install.native_install_gate = Some(historical_packet);

        let packet = response
            .native_install_gate_packet()
            .expect("active deny must retain fail-closed telemetry");
        assert_eq!(
            packet.rejection_code,
            Some(NativeInstallGateRejectionCode::KillSwitchActive)
        );
        assert!(packet.actions.all_install_authority_blocked());

        let mut nonmatching_live_deny = NativeInstallGateDenyControlPlane::active(
            NativeInstallGateDenyScope::Consumer,
            NativeInstallGateDenyReason::KillSwitch,
        );
        nonmatching_live_deny.consumer = Some("ty".to_owned());
        response
            .artifact
            .as_mut()
            .expect("compiled artifact")
            .install
            .native_install_gate_input
            .as_mut()
            .expect("live gate input")
            .deny_control = Some(nonmatching_live_deny.with_canonical_deny_sha256());
        let conflicting_packet = response
            .native_install_gate_packet()
            .expect("conflicting active denies must fail closed");
        assert_eq!(
            conflicting_packet.rejection_code,
            Some(NativeInstallGateRejectionCode::ArtifactIdentityMismatch)
        );
        assert!(conflicting_packet.actions.all_install_authority_blocked());
        assert!(response.into_installed_artifact().is_none());
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn object_and_missing_payload_reporting_rejects_positive_packet_substitution() {
        let donor_manifest = native_install_manifest("artifact-reporting-positive-donor", 714);
        let donor_response = native_install_response(
            native_install_gate_input(&donor_manifest),
            Some(donor_manifest),
        );
        let donor_packet = donor_response
            .native_install_gate_packet()
            .expect("installable donor packet");
        assert!(donor_packet.is_installable());
        assert!(donor_packet.actions.expose_callable);

        let module = const_i64_module("object_packet_substitution", &[("answer", 42)]);
        let mut object_request =
            CompileRequest::new("object-packet-substitution", CompileGeneration::new(714));
        object_request.artifact_kind = ArtifactKind::Object;
        object_request.provenance.source_kind = SourceKind::TrustIrModule;
        let mut object_response = service().compile(object_request, &module);
        assert_eq!(object_response.status, CompileStatus::Compiled);
        assert!(matches!(
            object_response.payload.as_ref(),
            Some(ArtifactPayload::Object(_))
        ));
        object_response
            .artifact
            .as_mut()
            .expect("object artifact")
            .install
            .native_install_gate = Some(donor_packet.clone());
        assert!(
            object_response.native_install_gate_packet().is_none(),
            "an object response must not report a positive executable donor packet"
        );

        object_response.payload = None;
        assert!(
            object_response.native_install_gate_packet().is_none(),
            "a payload-free response must not report a positive donor packet"
        );

        let negative_manifest =
            native_install_manifest("artifact-reporting-negative-telemetry", 715);
        let mut negative_input = native_install_gate_input(&negative_manifest);
        negative_input.proof_evidence = None;
        let negative_response = native_install_response(negative_input, Some(negative_manifest));
        let negative_packet = negative_response
            .native_install_gate_packet()
            .expect("canonical negative packet");
        assert_eq!(
            negative_packet.rejection_code,
            Some(NativeInstallGateRejectionCode::ProofMissingEvidence)
        );
        assert!(negative_packet.actions.all_install_authority_blocked());

        object_response
            .artifact
            .as_mut()
            .expect("payload-free artifact")
            .install
            .native_install_gate = Some(negative_packet.clone());
        assert_eq!(
            object_response.native_install_gate_packet(),
            Some(negative_packet.clone()),
            "canonical blocked telemetry must remain reportable"
        );
        let summary = object_response.proof_install_telemetry_summary();
        assert_eq!(
            summary.native_install_gate_code,
            Some(NativeInstallGateRejectionCode::ProofMissingEvidence.as_str())
        );
        assert!(!summary.useful_native_eligible);

        let mut malformed_binding = negative_packet.clone();
        malformed_binding
            .replay_binding
            .replay_root_sha256
            .push_str("-donor-tamper");
        object_response
            .artifact
            .as_mut()
            .expect("payload-free artifact")
            .install
            .native_install_gate = Some(malformed_binding);
        assert!(
            object_response.native_install_gate_packet().is_none(),
            "a blocked packet with stale derived bindings is not canonical reporting evidence"
        );

        let mut malformed_negative = negative_packet;
        malformed_negative.packet_hash =
            ArtifactChecksum::new(malformed_negative.packet_hash.get().wrapping_add(1));
        object_response
            .artifact
            .as_mut()
            .expect("payload-free artifact")
            .install
            .native_install_gate = Some(malformed_negative);
        assert!(
            object_response.native_install_gate_packet().is_none(),
            "a malformed blocked packet is not canonical reporting evidence"
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn native_install_gate_rejects_representative_direct_compile_failures() {
        fn assert_gate_rejects(
            input: NativeInstallGateInput,
            manifest: Option<ArtifactManifestV1>,
            expected_disposition: NativeInstallGateDisposition,
            expected_code: NativeInstallGateRejectionCode,
        ) {
            let response = native_install_response(input, manifest);
            let packet = response
                .native_install_gate_packet()
                .expect("native install gate packet");
            assert_eq!(packet.disposition, expected_disposition);
            assert_eq!(packet.rejection_code, Some(expected_code));
            assert!(!packet.actions.expose_callable);
            assert!(!packet.actions.useful_native_eligible);

            let summary = response.proof_install_telemetry_summary();
            assert!(!summary.useful_native_eligible);
            assert_eq!(summary.useful_native_count, 0);
            assert_eq!(
                summary.install_authority_blocked_on,
                Some(expected_code.as_str())
            );
            assert_eq!(
                summary.native_install_gate_disposition,
                Some(expected_disposition.as_str())
            );
            assert_eq!(
                summary.native_install_gate_code,
                Some(expected_code.as_str())
            );
            assert_eq!(summary.rejection_category, Some("native_install_gate"));
            assert!(response.into_installed_artifact().is_none());
        }

        let manifest = native_install_manifest("artifact-native-install-rejected", 72);

        let mut missing_manifest = native_install_gate_input(&manifest);
        missing_manifest.manifest = None;
        missing_manifest.manifest_reference = None;
        assert_gate_rejects(
            missing_manifest,
            None,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::MissingManifest,
        );

        let mut missing_layout = native_install_gate_input(&manifest);
        missing_layout.layout_evidence = None;
        assert_gate_rejects(
            missing_layout,
            Some(manifest.clone()),
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        );

        let mut missing_proof = native_install_gate_input(&manifest);
        missing_proof.proof_evidence = None;
        assert_gate_rejects(
            missing_proof,
            Some(manifest.clone()),
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::ProofMissingEvidence,
        );

        let mut stale_invalidation = native_install_gate_input(&manifest);
        stale_invalidation.current_generation += 1;
        assert_gate_rejects(
            stale_invalidation,
            Some(manifest.clone()),
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::StaleInvalidation,
        );

        let mut missing_telemetry = native_install_gate_input(&manifest);
        missing_telemetry.telemetry = None;
        assert_gate_rejects(
            missing_telemetry,
            Some(manifest.clone()),
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::MissingTelemetry,
        );

        let mut profile_only = native_install_gate_input(&manifest);
        profile_only.candidate_disposition = NativeInstallGateDisposition::ProfileOnly;
        assert_gate_rejects(
            profile_only,
            Some(manifest.clone()),
            NativeInstallGateDisposition::ProfileOnly,
            NativeInstallGateRejectionCode::ProfileOnlyNonInstallable,
        );

        let mut replay_only = native_install_gate_input(&manifest);
        replay_only.candidate_disposition = NativeInstallGateDisposition::ReplayOnly;
        assert_gate_rejects(
            replay_only,
            Some(manifest.clone()),
            NativeInstallGateDisposition::ReplayOnly,
            NativeInstallGateRejectionCode::ReplayOnlyNonInstallable,
        );

        let mut shadow_only = native_install_gate_input(&manifest);
        shadow_only.candidate_disposition = NativeInstallGateDisposition::ShadowOnly;
        assert_gate_rejects(
            shadow_only,
            Some(manifest),
            NativeInstallGateDisposition::ShadowOnly,
            NativeInstallGateRejectionCode::ShadowOnlyNonInstallable,
        );
    }

    #[test]
    fn required_proof_policy_success_is_installable_and_metadata_bound() {
        let mut request = CompileRequest::new("proof-required-ok", CompileGeneration::new(16));
        request.proof_policy = required_proof_policy();
        let mut compiled_artifact = artifact(CompileGeneration::new(16));
        compiled_artifact.install.proofs = install_proof_summary(true, 2, 2, Some(1), true, 1);

        let response = service().compile_with(request.clone(), || Ok(compiled_artifact));

        assert_eq!(response.status, CompileStatus::Compiled);
        assert_eq!(
            response.disposition,
            ArtifactInstallDisposition::Installable
        );
        let artifact = response.artifact.as_ref().expect("compiled artifact");
        assert_eq!(
            artifact.install.disposition,
            ArtifactInstallDisposition::Installable
        );
        assert_eq!(
            artifact.install.proofs.policy_status,
            ProofPolicyStatus::Satisfied
        );
        assert_eq!(artifact.install.proof_policy, request.proof_policy);
        assert_eq!(
            artifact.metadata.proof_policy_checksum,
            request.proof_policy.checksum()
        );
        let report = artifact
            .install
            .proof_evidence_report
            .as_ref()
            .expect("accepted report");
        assert_eq!(report.verdict, ProofTvVerdict::Accepted);
        assert_eq!(report.rejection_code, None);
        assert_eq!(
            report.proof_policy_checksum,
            request.proof_policy.checksum()
        );
        assert_eq!(report.artifact_identity, artifact.identity);
        assert_eq!(report.report_hash, report.compute_report_hash());
    }

    #[test]
    fn accepted_proof_tv_evidence_satisfies_required_policy_for_install() {
        let mut request = CompileRequest::new(
            "proof-tv-accepted-required-policy",
            CompileGeneration::new(117),
        );
        request.proof_policy = required_proof_policy();
        request.proof_tv_evidence = Some(ProofTvEvidenceOutcome {
            verdict: ProofTvVerdict::Accepted,
            rejection_code: None,
            diagnostic_reason: "external proof/tv report accepted".to_owned(),
        });

        let response = service().compile_with(request.clone(), || {
            Ok(artifact(CompileGeneration::new(117)))
        });

        assert_eq!(response.status, CompileStatus::Compiled);
        assert_eq!(
            response.disposition,
            ArtifactInstallDisposition::Installable
        );
        let artifact = response.artifact.as_ref().expect("compiled artifact");
        assert_eq!(
            artifact.install.disposition,
            ArtifactInstallDisposition::Installable
        );
        assert_eq!(
            artifact.install.proofs.policy_status,
            ProofPolicyStatus::Satisfied
        );
        let report = artifact
            .install
            .proof_evidence_report
            .as_ref()
            .expect("accepted report");
        assert_eq!(report.verdict, ProofTvVerdict::Accepted);
        assert_eq!(report.rejection_code, None);
        assert_eq!(
            report.proof_policy_checksum,
            request.proof_policy.checksum()
        );
    }

    #[cfg(feature = "verify")]
    #[test]
    fn aarch64_backend_proof_family_identity_binds_to_proof_tv_and_native_install_metadata() {
        let generation = CompileGeneration::new(116);
        let profile = CompileProfile::Custom {
            compiler: CompilerConfig::jit_fast(Target::Aarch64),
            jit: JitConfig::default(),
        };
        let metadata = ArtifactMetadata::from_profile(&profile, ArtifactKind::Object);
        let mut artifact = CompiledArtifact::metadata_only_with(
            "aarch64-proof-family",
            generation,
            ArtifactProvenance::default(),
            metadata,
        )
        .with_artifact_manifest(deterministic_manifest("aarch64-proof-family"));
        artifact.install.replay_report_metadata = Some(JitReplayReportMetadata::new(0));

        let mut request = CompileRequest::new("aarch64-proof-family", generation);
        request.profile = profile;
        request.artifact_kind = ArtifactKind::Object;

        apply_install_disposition(&request, &mut artifact);

        let expected =
            trust_cg_verify::aarch64_backend_proof_report::build_aarch64_backend_proof_family_report();
        let report = artifact
            .install
            .proof_evidence_report
            .as_ref()
            .expect("proof/tv report");
        assert_eq!(
            report.backend_proof_family_schema.as_deref(),
            Some(expected.schema.as_str())
        );
        assert_eq!(
            report.backend_proof_family_target.as_deref(),
            Some(expected.target.as_str())
        );
        assert_eq!(
            report.backend_proof_family_obligation_set.as_deref(),
            Some(expected.obligation_set.as_str())
        );
        assert_eq!(
            report.backend_proof_family_policy_id.as_deref(),
            Some(expected.policy.policy_id.as_str())
        );
        assert_eq!(
            report.backend_proof_family_installable,
            Some(expected.policy.installable)
        );
        assert_eq!(
            report.backend_proof_family_report_hash.as_deref(),
            Some(expected.report_hash.as_str())
        );
        assert_eq!(report.report_hash, report.compute_report_hash());

        let replay = artifact
            .install
            .replay_report_metadata
            .as_ref()
            .expect("replay metadata");
        assert_eq!(
            replay
                .properties
                .get("backend_proof_family_obligation_set")
                .map(String::as_str),
            Some(expected.obligation_set.as_str())
        );
        assert_eq!(
            replay
                .properties
                .get("backend_proof_family_report_hash")
                .map(String::as_str),
            Some(expected.report_hash.as_str())
        );

        let native_evidence =
            native_install_proof_evidence(&artifact).expect("native install proof evidence");
        assert_eq!(
            native_evidence
                .summary
                .metadata
                .get("backend_proof_family_obligation_set")
                .map(String::as_str),
            Some(expected.obligation_set.as_str())
        );
        assert_eq!(
            native_evidence
                .summary
                .metadata
                .get("backend_proof_family_report_hash")
                .map(String::as_str),
            Some(expected.report_hash.as_str())
        );
        let expected_installable = expected.policy.installable.to_string();
        assert_eq!(
            native_evidence
                .summary
                .metadata
                .get("backend_proof_family_installable")
                .map(String::as_str),
            Some(expected_installable.as_str())
        );
    }

    #[test]
    fn required_proof_policy_missing_evidence_rejects_install() {
        let mut request = CompileRequest::new("proof-required-missing", CompileGeneration::new(17));
        request.proof_policy = required_proof_policy();

        let response = service().compile_with(request, || Ok(artifact(CompileGeneration::new(17))));

        assert_eq!(response.status, CompileStatus::Compiled);
        assert_eq!(response.disposition, ArtifactInstallDisposition::Rejected);
        {
            let artifact = response.artifact.as_ref().expect("compiled artifact");
            assert_eq!(
                artifact.install.disposition,
                ArtifactInstallDisposition::Rejected
            );
            assert_eq!(
                artifact.install.proofs.policy_status,
                ProofPolicyStatus::Rejected
            );
            assert_eq!(
                artifact.install.proofs.rejection_code,
                Some(ProofRejectionCode::MissingLoweringCertificates)
            );
            let report = artifact
                .install
                .proof_evidence_report
                .as_ref()
                .expect("rejected report");
            assert_eq!(report.verdict, ProofTvVerdict::MissingEvidence);
            assert_eq!(
                report.rejection_code,
                Some(ProofTvRejectionCode::MissingEvidence)
            );
            assert_eq!(
                report.rejection_code.unwrap().as_str(),
                "proof_missing_evidence"
            );
        }
        assert_eq!(response.diagnostics[0].code, "proof_missing_evidence");
        let summary = response.proof_install_telemetry_summary();
        assert_eq!(summary.rejection_category, Some("missing_evidence"));
        assert_eq!(summary.proof_tv_code, Some("proof_missing_evidence"));
        assert_eq!(summary.proof_tv_verdict, Some("missing_evidence"));
        assert_no_useful_native(&summary);
        assert!(response.into_installed_artifact().is_none());
    }

    #[test]
    fn required_proof_policy_rejects_unsupported_target_before_compile() {
        let mut request = CompileRequest::new("proof-required-riscv64", CompileGeneration::new(18));
        request.proof_policy = required_proof_policy();
        request.profile = CompileProfile::Custom {
            compiler: CompilerConfig::jit_fast(Target::Riscv64),
            jit: JitConfig::default(),
        };

        let response = service().compile_with(request, || panic!("backend work should not run"));

        assert_eq!(response.status, CompileStatus::Rejected);
        assert_eq!(response.disposition, ArtifactInstallDisposition::Rejected);
        assert!(response.artifact.is_none());
        assert_eq!(response.diagnostics[0].code, "proof_unsupported_target");
        let summary = response.proof_install_telemetry_summary();
        assert_eq!(summary.rejection_category, Some("unsupported_target"));
        assert_eq!(summary.proof_tv_code, Some("proof_unsupported_target"));
        assert_eq!(summary.proof_tv_verdict, Some("unsupported_target"));
        assert_no_useful_native(&summary);
    }

    #[cfg(feature = "verify")]
    #[test]
    fn required_proof_policy_rejects_non_host_native_install_profile_before_compile() {
        let mut request =
            CompileRequest::new("proof-required-non-host-native", CompileGeneration::new(23));
        request.proof_policy = required_proof_policy();
        let non_host_target = match Target::host() {
            Target::Aarch64 => Target::X86_64,
            Target::X86_64 | Target::Riscv64 => Target::Aarch64,
        };
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.profile = CompileProfile::Custom {
            compiler: CompilerConfig::jit_fast(non_host_target),
            jit: JitConfig::default(),
        };

        let response = service().compile_with(request, || panic!("backend work should not run"));

        assert_eq!(response.status, CompileStatus::Rejected);
        assert_eq!(response.disposition, ArtifactInstallDisposition::Rejected);
        assert!(response.artifact.is_none());
        assert_eq!(response.diagnostics[0].code, "proof_unsupported_route");
    }

    #[test]
    fn required_proof_policy_rejects_manifest_policy_mismatch() {
        let mut request = CompileRequest::new(
            "proof-required-manifest-mismatch",
            CompileGeneration::new(19),
        )
        .with_artifact_manifest(deterministic_manifest("manifest-disabled-policy"));
        request.proof_policy = required_proof_policy();

        let response = service().compile_with(request, || panic!("backend work should not run"));

        assert_eq!(response.status, CompileStatus::Rejected);
        assert_eq!(response.disposition, ArtifactInstallDisposition::Rejected);
        assert_eq!(response.diagnostics[0].code, "proof_malformed_report");
    }

    #[test]
    fn required_proof_policy_accepts_manifest_solver_reordering() {
        let manifest_policy = ProofPolicy::require_certificates(["trust-cg-verify", "ay"]);
        let mut request_policy = manifest_policy.clone();
        request_policy.accepted_solvers = vec!["ay".to_owned(), "trust-cg-verify".to_owned()];
        let mut manifest = native_install_manifest("manifest-reordered-policy", 24);
        manifest.proof_policy = manifest_policy;
        manifest.invalidation.proof_policy_checksum = manifest.proof_policy.checksum();
        let mut request = CompileRequest::new(
            "proof-required-reordered-manifest",
            CompileGeneration::new(24),
        )
        .with_artifact_manifest(manifest);
        request.proof_policy = request_policy.clone();
        let mut compiled_artifact = artifact(CompileGeneration::new(24));
        compiled_artifact.install.proofs = install_proof_summary(true, 1, 1, None, true, 0);

        let response = service().compile_with(request, || Ok(compiled_artifact));

        assert_eq!(response.status, CompileStatus::Compiled);
        assert_eq!(response.diagnostics.len(), 0);
        assert_eq!(
            response
                .artifact
                .as_ref()
                .expect("compiled artifact")
                .install
                .proof_policy,
            request_policy
        );
    }

    #[test]
    fn proof_policy_rejection_marks_artifact_rejected() {
        let request = CompileRequest::new("proof-rejected", CompileGeneration::new(14));
        let mut compiled_artifact = artifact(CompileGeneration::new(14));
        compiled_artifact.install.proofs = install_proof_summary(true, 2, 1, None, true, 0);

        let response = service().compile_with(request, || Ok(compiled_artifact));

        assert_eq!(response.status, CompileStatus::Compiled);
        {
            let artifact = response.artifact.as_ref().expect("compiled artifact");
            assert_eq!(
                artifact.install.disposition,
                ArtifactInstallDisposition::Rejected
            );
            assert_eq!(
                artifact.install.proofs.policy_status,
                ProofPolicyStatus::Rejected
            );
            assert_eq!(
                artifact.install.proofs.rejection_code,
                Some(ProofRejectionCode::UnverifiedLoweringCertificates)
            );
            let report = artifact
                .install
                .proof_evidence_report
                .as_ref()
                .expect("proof tv report");
            assert_eq!(report.verdict, ProofTvVerdict::VerifierFailure);
            assert_eq!(
                report.rejection_code,
                Some(ProofTvRejectionCode::VerifierFailure)
            );
            assert_eq!(
                report.rejection_code.unwrap().as_str(),
                "proof_verifier_failure"
            );
            assert_eq!(artifact.install.disposition.as_str(), "rejected");
            assert_eq!(artifact.install.proofs.policy_status.as_str(), "rejected");
            assert_eq!(
                artifact
                    .install
                    .proofs
                    .rejection_code
                    .expect("proof rejection")
                    .as_str(),
                "unverified_lowering_certificates"
            );
        }
        assert_eq!(response.diagnostics[0].code, "proof_verifier_failure");
        let summary = response.proof_install_telemetry_summary();
        assert_eq!(summary.rejection_category, Some("proof_rejected"));
        assert_eq!(summary.proof_tv_code, Some("proof_verifier_failure"));
        assert_eq!(summary.proof_tv_verdict, Some("verifier_failure"));
        assert_no_useful_native(&summary);
        assert!(response.into_installed_artifact().is_none());
    }

    #[test]
    fn proof_policy_rejection_attaches_typed_replay_status_when_metadata_exists() {
        let request = CompileRequest::new("proof-rejected-replay", CompileGeneration::new(14));
        let mut compiled_artifact = artifact(CompileGeneration::new(14));
        compiled_artifact.install.proofs = install_proof_summary(true, 2, 1, None, true, 0);
        let mut replay_report_metadata = JitReplayReportMetadata::new(32);
        replay_report_metadata
            .statuses
            .push(JitTrapStatusBlock::new(
                7,
                JitTrapStatusKind::Unknown,
                "preexisting",
            ));
        compiled_artifact.install.replay_report_metadata = Some(replay_report_metadata);

        let response = service().compile_with(request, || Ok(compiled_artifact));

        assert_eq!(response.status, CompileStatus::Compiled);
        let artifact = response.artifact.as_ref().expect("compiled artifact");
        assert_eq!(
            artifact.install.disposition,
            ArtifactInstallDisposition::Rejected
        );
        let report = artifact
            .install
            .replay_report_metadata
            .as_ref()
            .expect("rejected artifact should keep replay metadata");
        assert_eq!(
            report
                .properties
                .get("proof_policy_status")
                .map(String::as_str),
            Some("rejected")
        );
        assert_eq!(
            report
                .properties
                .get("proof_rejection_code")
                .map(String::as_str),
            Some("unverified_lowering_certificates")
        );
        assert_eq!(
            report
                .properties
                .get("failure_category")
                .map(String::as_str),
            Some("proof_or_install_rejection")
        );
        assert_eq!(
            report.properties.get("failure_code").map(String::as_str),
            Some("proof_verifier_failure")
        );
        assert_eq!(
            report
                .properties
                .get("proof_tv_verdict")
                .map(String::as_str),
            Some("verifier_failure")
        );
        assert_eq!(
            report.properties.get("proof_tv_code").map(String::as_str),
            Some("proof_verifier_failure")
        );
        assert!(report.properties.contains_key("proof_tv_report_hash"));
        assert_eq!(report.statuses.len(), 2);
        assert_eq!(report.statuses[0].sequence, 7);
        assert_eq!(report.statuses[0].kind, JitTrapStatusKind::Unknown);
        assert_eq!(report.statuses[1].sequence, 8);
        assert_eq!(report.statuses[1].kind, JitTrapStatusKind::VerifierRejected);
        assert_eq!(report.statuses[1].stage, "compile_service.proof_policy");
        assert_eq!(
            report.statuses[1].message.as_deref(),
            Some("unverified_lowering_certificates")
        );
    }

    #[test]
    fn proof_policy_rejection_replay_status_is_idempotent_and_repairs_properties() {
        let request = CompileRequest::new("proof-rejected-metadata", CompileGeneration::new(15));
        let proofs = install_proof_summary(true, 1, 1, Some(1), false, 1);
        let mut replay_report_metadata = JitReplayReportMetadata::new(64);
        replay_report_metadata.statuses.push(
            JitTrapStatusBlock::new(
                3,
                JitTrapStatusKind::VerifierRejected,
                "compile_service.proof_policy",
            )
            .with_message("unverified_jit_certificates"),
        );

        let mut artifact = artifact_from_metadata(
            &request,
            CompileGeneration::new(15),
            ArtifactProvenance::default(),
            ArtifactMetadata::default(),
            Duration::ZERO,
            ArtifactIdentity::from("proof-rejected-metadata"),
            InstallArtifactDetails {
                proofs,
                replay_report_metadata: Some(replay_report_metadata),
                ..InstallArtifactDetails::default()
            },
        );

        apply_install_disposition(&request, &mut artifact);

        assert_eq!(
            artifact.install.disposition,
            ArtifactInstallDisposition::Rejected
        );
        let report = artifact
            .install
            .replay_report_metadata
            .as_ref()
            .expect("rejected artifact should keep replay metadata");
        let proof_rejected_statuses = report
            .statuses
            .iter()
            .filter(|status| {
                status.kind == JitTrapStatusKind::VerifierRejected
                    && status.stage == "compile_service.proof_policy"
            })
            .count();
        assert_eq!(proof_rejected_statuses, 1);
        assert_eq!(report.statuses.len(), 1);
        assert_eq!(report.statuses[0].sequence, 3);
        assert_eq!(
            report
                .properties
                .get("failure_category")
                .map(String::as_str),
            Some("proof_or_install_rejection")
        );
        assert_eq!(
            report.properties.get("failure_code").map(String::as_str),
            Some("proof_verifier_failure")
        );
        assert_eq!(
            report
                .properties
                .get("proof_policy_status")
                .map(String::as_str),
            Some("rejected")
        );
        assert_eq!(
            report
                .properties
                .get("proof_rejection_code")
                .map(String::as_str),
            Some("unverified_jit_certificates")
        );
    }

    #[test]
    fn proof_rejected_compile_only_artifact_stays_rejected_and_non_installable() {
        let mut request =
            CompileRequest::new("compile-only-proof-rejected", CompileGeneration::new(14));
        request.install_intent = InstallIntent::CompileOnly;
        let mut compiled_artifact = artifact(CompileGeneration::new(14));
        compiled_artifact.install.proofs = install_proof_summary(true, 2, 1, None, true, 0);

        let response = service().compile_with(request, || Ok(compiled_artifact));

        assert_eq!(response.status, CompileStatus::Compiled);
        {
            let artifact = response.artifact.as_ref().expect("compiled artifact");
            assert_eq!(
                artifact.install.disposition,
                ArtifactInstallDisposition::Rejected
            );
            assert_eq!(
                artifact.install.proofs.policy_status,
                ProofPolicyStatus::Rejected
            );
            assert_eq!(
                artifact.install.proofs.rejection_code,
                Some(ProofRejectionCode::UnverifiedLoweringCertificates)
            );
            assert_eq!(artifact.install.disposition.as_str(), "rejected");
        }
        assert!(response.into_installed_artifact().is_none());
    }

    #[test]
    fn proof_install_summary_classifies_direct_failed_proof_tv_outcomes_without_useful_native() {
        let cases = [
            ("proof_timeout", "timeout", "timeout"),
            ("proof_solver_error", "solver_error", "solver_error"),
            ("proof_stale_evidence", "stale_evidence", "stale_evidence"),
            ("proof_unknown", "unknown", "unknown"),
        ];

        for (diagnostic_code, category, verdict) in cases {
            let request = CompileRequest::new(
                format!("direct-{diagnostic_code}"),
                CompileGeneration::new(40),
            );
            let response = service().compile_with(request, || {
                Err(CompileDiagnostic::error(
                    diagnostic_code,
                    format!("direct proof/tv outcome {diagnostic_code}"),
                )
                .with_phase("proof_tv_evidence"))
            });

            assert_eq!(response.status, CompileStatus::Failed);
            assert_eq!(response.disposition, ArtifactInstallDisposition::Rejected);
            let summary = response.proof_install_telemetry_summary();
            assert_eq!(summary.rejection_category, Some(category));
            assert_eq!(summary.proof_tv_code, Some(diagnostic_code));
            assert_eq!(summary.proof_tv_verdict, Some(verdict));
            assert_eq!(summary.diagnostic_code, Some(diagnostic_code));
            assert_no_useful_native(&summary);
        }
    }

    #[test]
    fn local_compile_routes_reject_proof_tv_timeout_unknown_stale_and_missing_fields() {
        let cases = [
            (
                "timeout",
                ProofTvVerdict::Timeout,
                ProofTvRejectionCode::Timeout,
                "timeout",
                JitTrapStatusKind::Timeout,
            ),
            (
                "unknown",
                ProofTvVerdict::Unknown,
                ProofTvRejectionCode::Unknown,
                "unknown",
                JitTrapStatusKind::Unknown,
            ),
            (
                "solver-error",
                ProofTvVerdict::SolverError,
                ProofTvRejectionCode::SolverError,
                "solver_error",
                JitTrapStatusKind::InternalError,
            ),
            (
                "stale-evidence",
                ProofTvVerdict::StaleEvidence,
                ProofTvRejectionCode::StaleEvidence,
                "stale_evidence",
                JitTrapStatusKind::VerifierRejected,
            ),
            (
                "missing-required-fields",
                ProofTvVerdict::MissingRequiredFields,
                ProofTvRejectionCode::MissingRequiredFields,
                "missing_required_fields",
                JitTrapStatusKind::InternalError,
            ),
        ];

        for (name, verdict, code, category, status_kind) in cases {
            let module = const_i64_module(
                &format!("compile_service_proof_tv_{name}"),
                &[("answer", 42)],
            );
            let reason = format!("phase2 local proof tv {name}");
            let mut request =
                CompileRequest::new(format!("proof-tv-{name}"), CompileGeneration::new(713));
            request.artifact_kind = ArtifactKind::Object;
            request.profile = CompileProfile::Custom {
                compiler: CompilerConfig::jit_fast(Target::Aarch64),
                jit: JitConfig::default(),
            };
            request.provenance.source_kind = SourceKind::TrustIrModule;
            request.provenance.source_fingerprint = Some(format!("sha256:proof-tv-{name}"));
            request.proof_tv_evidence = Some(ProofTvEvidenceOutcome::rejected(
                verdict,
                code,
                reason.clone(),
            ));

            let response = service().compile(request, &module);

            assert_eq!(response.status, CompileStatus::Compiled);
            assert_eq!(response.disposition, ArtifactInstallDisposition::Rejected);
            assert!(matches!(
                response.payload.as_ref(),
                Some(ArtifactPayload::Object(_))
            ));
            assert_eq!(response.diagnostics[0].code, code.as_str());
            assert_eq!(
                response.diagnostics[0].phase.as_deref(),
                Some("proof_tv_evidence")
            );
            assert!(response.diagnostics[0].message.contains(&reason));
            assert!(response.clone().into_installed_artifact().is_none());

            let artifact = response.artifact.as_ref().expect("compiled artifact");
            assert_eq!(
                artifact.install.disposition,
                ArtifactInstallDisposition::Rejected
            );
            assert!(artifact.install.exported_entrypoints.is_empty());
            let report = artifact
                .install
                .proof_evidence_report
                .as_ref()
                .expect("proof/tv report");
            assert_eq!(report.verdict, verdict);
            assert_eq!(report.rejection_code, Some(code));
            assert_eq!(report.diagnostic_reason.as_deref(), Some(reason.as_str()));

            let replay = artifact
                .install
                .replay_report_metadata
                .as_ref()
                .expect("proof/tv replay metadata");
            assert_eq!(
                replay
                    .properties
                    .get("failure_category")
                    .map(String::as_str),
                Some("proof_tv_rejection")
            );
            assert_eq!(
                replay.properties.get("failure_code").map(String::as_str),
                Some(code.as_str())
            );
            assert_eq!(
                replay.properties.get("proof_tv_code").map(String::as_str),
                Some(code.as_str())
            );
            assert_eq!(
                replay
                    .properties
                    .get("proof_tv_diagnostic_reason")
                    .map(String::as_str),
                Some(reason.as_str())
            );
            assert!(replay.statuses.iter().any(|status| {
                status.kind == status_kind
                    && status.stage == "compile_service.proof_tv"
                    && status.message.as_deref() == Some(reason.as_str())
            }));

            let summary = response.proof_install_telemetry_summary();
            assert_eq!(summary.rejection_category, Some(category));
            assert_eq!(summary.proof_tv_code, Some(code.as_str()));
            assert_eq!(summary.proof_tv_verdict, Some(verdict.as_str()));
            assert_eq!(summary.diagnostic_code, Some(code.as_str()));
            assert_no_useful_native(&summary);
        }
    }

    #[test]
    fn native_install_proof_evidence_preserves_typed_proof_tv_blockers() {
        let cases = [
            (
                ProofTvVerdict::MissingEvidence,
                ProofTvRejectionCode::MissingEvidence,
                ProofEvidenceVerdict::MissingEvidence,
                ProofEvidenceRejectionCode::MissingEvidence,
            ),
            (
                ProofTvVerdict::VerifierFailure,
                ProofTvRejectionCode::VerifierFailure,
                ProofEvidenceVerdict::VerifierFailure,
                ProofEvidenceRejectionCode::VerifierFailure,
            ),
            (
                ProofTvVerdict::Timeout,
                ProofTvRejectionCode::Timeout,
                ProofEvidenceVerdict::Timeout,
                ProofEvidenceRejectionCode::Timeout,
            ),
            (
                ProofTvVerdict::Unknown,
                ProofTvRejectionCode::Unknown,
                ProofEvidenceVerdict::Unknown,
                ProofEvidenceRejectionCode::Unknown,
            ),
            (
                ProofTvVerdict::SolverError,
                ProofTvRejectionCode::SolverError,
                ProofEvidenceVerdict::SolverError,
                ProofEvidenceRejectionCode::SolverError,
            ),
            (
                ProofTvVerdict::UnsupportedRoute,
                ProofTvRejectionCode::UnsupportedRoute,
                ProofEvidenceVerdict::UnsupportedRoute,
                ProofEvidenceRejectionCode::UnsupportedRoute,
            ),
            (
                ProofTvVerdict::UnsupportedTarget,
                ProofTvRejectionCode::UnsupportedTarget,
                ProofEvidenceVerdict::UnsupportedTarget,
                ProofEvidenceRejectionCode::UnsupportedTarget,
            ),
            (
                ProofTvVerdict::StaleEvidence,
                ProofTvRejectionCode::StaleEvidence,
                ProofEvidenceVerdict::StaleEvidence,
                ProofEvidenceRejectionCode::StaleEvidence,
            ),
            (
                ProofTvVerdict::MalformedReport,
                ProofTvRejectionCode::MalformedReport,
                ProofEvidenceVerdict::MalformedReport,
                ProofEvidenceRejectionCode::MalformedReport,
            ),
            (
                ProofTvVerdict::MissingRequiredFields,
                ProofTvRejectionCode::MissingRequiredFields,
                ProofEvidenceVerdict::MissingRequiredFields,
                ProofEvidenceRejectionCode::MissingRequiredFields,
            ),
        ];

        for (proof_tv_verdict, proof_tv_code, evidence_verdict, evidence_code) in cases {
            let generation = CompileGeneration::new(715);
            let mut request = CompileRequest::new(
                format!("native-install-proof-tv-{}", proof_tv_code.as_str()),
                generation,
            )
            .with_artifact_manifest(deterministic_manifest(proof_tv_code.as_str()));
            request.proof_tv_evidence = Some(ProofTvEvidenceOutcome::rejected(
                proof_tv_verdict,
                proof_tv_code,
                format!("typed native install blocker {}", proof_tv_code.as_str()),
            ));
            let mut artifact = artifact(generation)
                .with_artifact_manifest(deterministic_manifest(proof_tv_code.as_str()));

            apply_install_disposition(&request, &mut artifact);

            let evidence =
                native_install_proof_evidence(&artifact).expect("native install proof evidence");
            assert_eq!(&evidence.summary.verdict, &evidence_verdict);
            assert_eq!(
                evidence.summary.rejection_code.as_ref(),
                Some(&evidence_code)
            );
            assert_eq!(evidence.summary.verdict.as_str(), proof_tv_verdict.as_str());
            assert_eq!(
                evidence
                    .summary
                    .rejection_code
                    .as_ref()
                    .map(ProofEvidenceRejectionCode::as_str),
                Some(proof_tv_code.as_str())
            );
        }
    }

    #[test]
    fn proof_tv_rejection_codes_cover_phase2_classes() {
        let cases = [
            (
                ProofTvVerdict::MissingEvidence,
                ProofTvRejectionCode::MissingEvidence,
                "missing_evidence",
                "proof_missing_evidence",
            ),
            (
                ProofTvVerdict::VerifierFailure,
                ProofTvRejectionCode::VerifierFailure,
                "verifier_failure",
                "proof_verifier_failure",
            ),
            (
                ProofTvVerdict::Timeout,
                ProofTvRejectionCode::Timeout,
                "timeout",
                "proof_timeout",
            ),
            (
                ProofTvVerdict::Unknown,
                ProofTvRejectionCode::Unknown,
                "unknown",
                "proof_unknown",
            ),
            (
                ProofTvVerdict::SolverError,
                ProofTvRejectionCode::SolverError,
                "solver_error",
                "proof_solver_error",
            ),
            (
                ProofTvVerdict::UnsupportedRoute,
                ProofTvRejectionCode::UnsupportedRoute,
                "unsupported_route",
                "proof_unsupported_route",
            ),
            (
                ProofTvVerdict::UnsupportedTarget,
                ProofTvRejectionCode::UnsupportedTarget,
                "unsupported_target",
                "proof_unsupported_target",
            ),
            (
                ProofTvVerdict::StaleEvidence,
                ProofTvRejectionCode::StaleEvidence,
                "stale_evidence",
                "proof_stale_evidence",
            ),
            (
                ProofTvVerdict::MalformedReport,
                ProofTvRejectionCode::MalformedReport,
                "malformed_report",
                "proof_malformed_report",
            ),
            (
                ProofTvVerdict::MissingRequiredFields,
                ProofTvRejectionCode::MissingRequiredFields,
                "missing_required_fields",
                "proof_missing_required_fields",
            ),
        ];

        for (verdict, code, verdict_str, code_str) in cases {
            assert_eq!(verdict.as_str(), verdict_str);
            assert_eq!(code.as_str(), code_str);
        }
    }

    #[test]
    fn artifact_identity_excludes_request_id() {
        let left = identity_for(
            "req-a",
            b"canonical-module",
            Target::Aarch64,
            CompileProfileId::FastAarch64Solver,
            &["entry"],
        );
        let right = identity_for(
            "req-b",
            b"canonical-module",
            Target::Aarch64,
            CompileProfileId::FastAarch64Solver,
            &["entry"],
        );

        assert_eq!(left, right);
    }

    #[test]
    fn artifact_identity_hashes_proof_policy_and_profile_only_intent() {
        let mut installable = CompileRequest::new("req", CompileGeneration::new(1));
        installable.profile = CompileProfile::Custom {
            compiler: CompilerConfig::jit_fast(Target::Aarch64),
            jit: JitConfig {
                opt_level: OptLevel::O1,
                verify: false,
                verify_dispatch: DispatchVerifyMode::ErrorOnFailure,
                profile_hooks: ProfileHookMode::None,
                emit_entry_counters: false,
                ..JitConfig::default()
            },
        };

        let disabled_install =
            ArtifactIdentityInput::from_request(&installable, b"canonical-module", ["entry"])
                .identity();
        let mut proof_required = installable.clone();
        proof_required.proof_policy = required_proof_policy();
        let required_install =
            ArtifactIdentityInput::from_request(&proof_required, b"canonical-module", ["entry"])
                .identity();
        let mut profile_only = installable.clone();
        profile_only.install_intent = InstallIntent::CompileOnly;
        let profile_only_identity =
            ArtifactIdentityInput::from_request(&profile_only, b"canonical-module", ["entry"])
                .identity();

        assert_ne!(disabled_install, required_install);
        assert_ne!(disabled_install, profile_only_identity);
        assert_ne!(required_install, profile_only_identity);
    }

    #[test]
    fn artifact_identity_treats_proof_policy_solvers_as_unordered_set() {
        let mut left_request = CompileRequest::new("req", CompileGeneration::new(1));
        left_request.profile = CompileProfile::Custom {
            compiler: CompilerConfig::jit_fast(Target::Aarch64),
            jit: JitConfig::default(),
        };
        left_request.proof_policy = ProofPolicy::require_certificates(["trust-cg-verify", "ay"]);
        let mut right_request = left_request.clone();
        right_request.proof_policy.accepted_solvers = vec![
            "ay".to_owned(),
            "trust-cg-verify".to_owned(),
            "ay".to_owned(),
        ];

        let left =
            ArtifactIdentityInput::from_request(&left_request, b"canonical-module", ["entry"])
                .identity();
        let right =
            ArtifactIdentityInput::from_request(&right_request, b"canonical-module", ["entry"])
                .identity();

        assert_eq!(left, right);
    }

    #[test]
    fn compile_trust_ir_object_identity_excludes_request_id() {
        let module = const_i64_module("compile_service_identity", &[("answer", 42)]);
        let mut left_request = CompileRequest::new("req-a", CompileGeneration::new(30));
        left_request.artifact_kind = ArtifactKind::Object;
        left_request.profile = CompileProfile::Custom {
            compiler: CompilerConfig::jit_fast(Target::Aarch64),
            jit: JitConfig::default(),
        };
        let mut right_request = left_request.clone();
        right_request.request_id = CompileRequestId::new("req-b");

        let left = service().compile(left_request, &module);
        let right = service().compile(right_request, &module);

        assert_eq!(left.status, CompileStatus::Compiled);
        assert_eq!(right.status, CompileStatus::Compiled);
        assert_eq!(
            left.artifact.expect("left artifact").identity,
            right.artifact.expect("right artifact").identity
        );
    }

    #[test]
    fn artifact_identity_changes_for_module_target_profile_and_exports() {
        let base = identity_for(
            "req",
            b"canonical-module",
            Target::Aarch64,
            CompileProfileId::FastAarch64Solver,
            &["entry", "helper"],
        );

        assert_ne!(
            base,
            identity_for(
                "req",
                b"canonical-module-v2",
                Target::Aarch64,
                CompileProfileId::FastAarch64Solver,
                &["entry", "helper"],
            )
        );
        assert_ne!(
            base,
            identity_for(
                "req",
                b"canonical-module",
                Target::X86_64,
                CompileProfileId::FastAarch64Solver,
                &["entry", "helper"],
            )
        );
        assert_ne!(
            base,
            identity_for(
                "req",
                b"canonical-module",
                Target::Aarch64,
                CompileProfileId::HostJitFast,
                &["entry", "helper"],
            )
        );
        assert_ne!(
            base,
            identity_for(
                "req",
                b"canonical-module",
                Target::Aarch64,
                CompileProfileId::FastAarch64Solver,
                &["entry", "helper", "extra"],
            )
        );
        assert_ne!(
            base,
            identity_for(
                "req",
                b"canonical-module",
                Target::Aarch64,
                CompileProfileId::FastAarch64Solver,
                &["helper", "entry"],
            )
        );
    }

    #[test]
    fn artifact_identity_hashes_artifact_kind_and_code_affecting_knobs() {
        let mut request = CompileRequest::new("req", CompileGeneration::new(1));
        request.profile = CompileProfile::Custom {
            compiler: CompilerConfig::jit_fast(Target::Aarch64),
            jit: JitConfig {
                opt_level: OptLevel::O1,
                verify: false,
                verify_dispatch: DispatchVerifyMode::ErrorOnFailure,
                profile_hooks: ProfileHookMode::None,
                emit_entry_counters: false,
                ..JitConfig::default()
            },
        };
        request.artifact_kind = ArtifactKind::ExecutableMemory;

        let base = ArtifactIdentityInput::from_request(&request, b"canonical-module", ["entry"])
            .identity();
        request.artifact_kind = ArtifactKind::Object;
        assert_ne!(
            base,
            ArtifactIdentityInput::from_request(&request, b"canonical-module", ["entry"])
                .identity()
        );

        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.profile = CompileProfile::Custom {
            compiler: CompilerConfig {
                emit_debug: true,
                ..CompilerConfig::jit_fast(Target::Aarch64)
            },
            jit: JitConfig {
                opt_level: OptLevel::O1,
                verify: true,
                verify_dispatch: DispatchVerifyMode::ErrorOnFailure,
                profile_hooks: ProfileHookMode::CallCounts,
                emit_entry_counters: false,
                ..JitConfig::default()
            },
        };
        assert_ne!(
            base,
            ArtifactIdentityInput::from_request(&request, b"canonical-module", ["entry"])
                .identity()
        );
    }

    #[test]
    fn raw_extern_addresses_are_metadata_not_identity_input() {
        let left = identity_for(
            "req",
            b"canonical-module",
            Target::Aarch64,
            CompileProfileId::FastAarch64Solver,
            &["entry"],
        );
        let right = identity_for(
            "req",
            b"canonical-module",
            Target::Aarch64,
            CompileProfileId::FastAarch64Solver,
            &["entry"],
        );
        assert_eq!(left, right);

        let mut provenance = ArtifactProvenance::default();
        provenance.raw_extern_bindings = vec![RawExternBinding::new("_host_callback", 0x1234)];
        let artifact = CompiledArtifact::metadata_only_with(
            left,
            CompileGeneration::new(2),
            provenance.clone(),
            ArtifactMetadata::default(),
        );

        assert_eq!(
            artifact.provenance.raw_extern_bindings,
            provenance.raw_extern_bindings
        );
        assert_eq!(
            artifact.install.raw_extern_bindings,
            vec![RawExternBinding::new("_host_callback", 0x1234)]
        );
    }

    #[test]
    fn metadata_only_artifact_carries_deterministic_manifest_without_identity_change() {
        let identity = identity_for(
            "req",
            b"canonical-module",
            Target::Aarch64,
            CompileProfileId::FastAarch64Solver,
            &["entry"],
        );
        let generation = CompileGeneration::new(12);
        let manifest = deterministic_manifest("artifact-contract-1");
        let manifest_checksum = manifest.checksum();
        let metadata = ArtifactMetadata::from_profile(
            &CompileProfile::FastAarch64Solver,
            ArtifactKind::Object,
        )
        .with_deterministic_manifest(&manifest);

        let without_manifest = CompiledArtifact::metadata_only_with(
            identity.clone(),
            generation,
            ArtifactProvenance::default(),
            ArtifactMetadata::from_profile(
                &CompileProfile::FastAarch64Solver,
                ArtifactKind::Object,
            ),
        );
        let with_manifest = CompiledArtifact::metadata_only_with(
            identity.clone(),
            generation,
            ArtifactProvenance::default(),
            metadata.clone(),
        );

        assert_eq!(with_manifest.identity, identity);
        assert_eq!(with_manifest.identity, without_manifest.identity);
        assert_eq!(
            with_manifest.install.identity,
            without_manifest.install.identity
        );
        assert_eq!(
            with_manifest.metadata.deterministic_manifest_checksum,
            Some(manifest_checksum)
        );
        assert_eq!(
            with_manifest
                .metadata
                .deterministic_manifest_reference
                .as_deref(),
            Some(manifest.artifact_id.as_str())
        );
        assert_eq!(with_manifest.install.artifact, metadata);
    }

    #[test]
    fn manifest_reference_validates_manifest_and_component_checksums() {
        let manifest = deterministic_manifest("artifact-reference-1");
        let reference = ArtifactManifestReference::from_manifest(&manifest);

        reference
            .verify_manifest(&manifest)
            .expect("manifest reference should validate");

        let mut proof_changed = manifest.clone();
        proof_changed.proof_policy.require_abi_evidence = true;
        let mut proof_reference = ArtifactManifestReference::from_manifest(&proof_changed);
        proof_reference.proof_policy_checksum = manifest.proof_policy.checksum();

        let err = proof_reference
            .verify_manifest(&proof_changed)
            .expect_err("proof policy checksum mismatch");
        assert!(matches!(
            err,
            ArtifactContractError::ChecksumMismatch { component, .. }
                if component == "proof_policy"
        ));
    }

    #[test]
    fn request_manifest_attaches_to_compile_with_artifact_and_install_metadata() {
        let generation = CompileGeneration::new(13);
        let manifest = native_install_manifest("artifact-compile-with-manifest", generation.get());
        let reference = ArtifactManifestReference::from_manifest(&manifest);
        let request = CompileRequest::new("manifest-compile-with", generation)
            .with_artifact_manifest(manifest.clone());

        let response = service().compile_with(request, || Ok(artifact(generation)));

        assert_eq!(response.status, CompileStatus::Compiled);
        let artifact = response.artifact.expect("compiled artifact");
        assert_eq!(artifact.identity.as_str(), "artifact");
        assert_eq!(artifact.artifact_manifest.as_ref(), Some(&manifest));
        assert_eq!(
            artifact.metadata.deterministic_manifest_checksum,
            Some(reference.manifest_checksum)
        );
        assert_eq!(
            artifact
                .metadata
                .deterministic_manifest_reference
                .as_deref(),
            Some(manifest.artifact_id.as_str())
        );
        assert_eq!(artifact.install.artifact, artifact.metadata);
        assert_eq!(artifact.install.artifact_manifest, Some(reference.clone()));
        reference
            .verify_manifest(artifact.artifact_manifest.as_ref().expect("manifest"))
            .expect("installed manifest reference should verify");
    }

    #[test]
    fn metadata_only_artifact_carries_provenance_metadata_and_install_contract() {
        let mut provenance = ArtifactProvenance {
            source_kind: SourceKind::TrustIrModule,
            source_fingerprint: Some("sha256:test".to_owned()),
            upstream_issue: Some(546),
            ..ArtifactProvenance::default()
        };
        provenance
            .caller_context
            .insert("solver_program".to_owned(), "sp-7".to_owned());
        let metadata = ArtifactMetadata {
            artifact_kind: ArtifactKind::Object,
            target: Target::Aarch64,
            profile: CompileProfileId::FastAarch64Solver,
            code_size_bytes: 64,
            allocation_size_bytes: None,
            deterministic_manifest_checksum: None,
            deterministic_manifest_reference: None,
            proof_policy_checksum: ProofPolicy::disabled().checksum(),
        };

        let artifact = CompiledArtifact::metadata_only_with(
            "artifact-1",
            CompileGeneration::new(12),
            provenance.clone(),
            metadata.clone(),
        );

        assert_eq!(artifact.identity.as_str(), "artifact-1");
        assert_eq!(artifact.provenance, provenance);
        assert_eq!(artifact.metadata, metadata);
        assert_eq!(artifact.install.identity, artifact.identity);
        assert_eq!(artifact.install.generation, CompileGeneration::new(12));
        assert_eq!(
            artifact.install.disposition,
            ArtifactInstallDisposition::Installable
        );
        assert_eq!(artifact.install.artifact, metadata);
        assert_eq!(artifact.install.compile_latency, Duration::ZERO);
        assert!(artifact.install.exported_entrypoints.is_empty());
        assert!(artifact.install.functions.is_empty());
        assert_eq!(artifact.install.proofs, InstallProofSummary::default());
        assert!(artifact.install.counters.is_empty());
        assert!(artifact.artifact_manifest.is_none());
        assert!(artifact.install.artifact_manifest.is_none());
        assert!(artifact.install.replay_report_metadata.is_none());
    }

    #[test]
    fn diagnostics_are_typed_and_phase_annotated() {
        let diagnostic =
            CompileDiagnostic::new("compile.failed", "backend failed").with_phase("before_install");

        assert_eq!(diagnostic.severity, DiagnosticSeverity::Error);
        assert_eq!(diagnostic.code, "compile.failed");
        assert_eq!(diagnostic.message, "backend failed");
        assert_eq!(diagnostic.phase.as_deref(), Some("before_install"));
        assert!(diagnostic.function.is_none());
        assert!(diagnostic.backend_error.is_none());
    }

    #[test]
    fn compile_trust_ir_object_returns_object_payload_and_metadata() {
        let module = const_i64_module("compile_service_object", &[("answer", 42)]);
        let mut request = CompileRequest::new("object", CompileGeneration::new(20));
        request.artifact_kind = ArtifactKind::Object;
        request.profile = CompileProfile::Custom {
            compiler: CompilerConfig::jit_fast(Target::Aarch64),
            jit: JitConfig::default(),
        };
        request.provenance.source_kind = SourceKind::TrustIrModule;

        let response = service().compile(request, &module);

        assert_eq!(response.status, CompileStatus::Compiled);
        let artifact = response.artifact.expect("compiled artifact");
        assert_eq!(artifact.metadata.artifact_kind, ArtifactKind::Object);
        assert_eq!(artifact.metadata.target, Target::Aarch64);
        assert_eq!(artifact.metadata.profile, CompileProfileId::Custom);
        assert_eq!(artifact.metadata.allocation_size_bytes, None);
        assert_eq!(artifact.provenance.source_kind, SourceKind::TrustIrModule);
        assert_eq!(artifact.install.functions.len(), 1);
        assert_eq!(artifact.install.functions[0].name, "answer");
        assert!(artifact.install.exported_entrypoints.is_empty());
        assert!(artifact.install.replay_report_metadata.is_none());

        match response.payload.expect("object payload") {
            ArtifactPayload::Object(payload) => {
                assert!(!payload.bytes.is_empty());
                assert_eq!(payload.metrics.function_count, 1);
                assert_eq!(payload.functions.len(), 1);
                assert_eq!(payload.functions[0].name, "answer");
            }
            other => panic!("expected object payload, got {other:?}"),
        }
    }

    #[test]
    fn compile_service_object_path_exposes_cache_hit_miss_telemetry() {
        let root = temp_cache_root("object-hit");
        let module = const_i64_module("compile_service_object_cache", &[("answer", 42)]);
        let service = CompileService::new(CompileServiceConfig {
            profile: CompileProfile::HostJitFast,
            compile_artifact_cache: Some(service_cache_config(&root)),
        });

        let mut first_request =
            CompileRequest::new("object-cache-first", CompileGeneration::new(30));
        first_request.artifact_kind = ArtifactKind::Object;
        first_request.profile = CompileProfile::Custom {
            compiler: CompilerConfig {
                opt_level: OptLevel::O0,
                target: Target::Aarch64,
                parallel: false,
                ..CompilerConfig::default()
            },
            jit: JitConfig::default(),
        };
        first_request.provenance.source_kind = SourceKind::TrustIrModule;

        let first = service.compile(first_request, &module);
        assert_eq!(first.status, CompileStatus::Compiled);
        let first_payload = match first.payload.expect("object payload") {
            ArtifactPayload::Object(payload) => payload,
            other => panic!("expected object payload, got {other:?}"),
        };
        assert_eq!(
            first_payload
                .compile_artifact_cache_telemetry
                .iter()
                .map(|event| event.status)
                .collect::<Vec<_>>(),
            vec![
                CompileArtifactCacheStatus::Miss,
                CompileArtifactCacheStatus::Stored
            ]
        );
        assert!(
            first_payload
                .compile_artifact_cache_telemetry
                .iter()
                .all(|event| event.boundary == CompileArtifactCacheBoundary::Service)
        );

        let mut second_request =
            CompileRequest::new("object-cache-second", CompileGeneration::new(31));
        second_request.artifact_kind = ArtifactKind::Object;
        second_request.profile = CompileProfile::Custom {
            compiler: CompilerConfig {
                opt_level: OptLevel::O0,
                target: Target::Aarch64,
                parallel: false,
                ..CompilerConfig::default()
            },
            jit: JitConfig::default(),
        };
        second_request.provenance.source_kind = SourceKind::TrustIrModule;

        let second = service.compile(second_request, &module);
        assert_eq!(second.status, CompileStatus::Compiled);
        match second.payload.expect("object payload") {
            ArtifactPayload::Object(payload) => {
                assert_eq!(
                    payload
                        .compile_artifact_cache_telemetry
                        .iter()
                        .map(|event| event.status)
                        .collect::<Vec<_>>(),
                    vec![CompileArtifactCacheStatus::Hit]
                );
                assert_eq!(
                    payload
                        .compile_artifact_cache_telemetry
                        .first()
                        .map(|event| event.status),
                    Some(CompileArtifactCacheStatus::Hit)
                );
            }
            other => panic!("expected object payload, got {other:?}"),
        }

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn compile_trust_ir_object_manifest_fails_closed_without_payload_binding() {
        let module = const_i64_module("compile_service_manifest_object", &[("answer", 42)]);
        let manifest = deterministic_manifest("artifact-object-manifest");
        let mut request = CompileRequest::new("object-manifest", CompileGeneration::new(23))
            .with_artifact_manifest(manifest.clone());
        request.artifact_kind = ArtifactKind::Object;
        request.profile = CompileProfile::Custom {
            compiler: CompilerConfig::jit_fast(Target::Aarch64),
            jit: JitConfig::default(),
        };

        let response = service().compile(request, &module);

        assert_eq!(response.status, CompileStatus::Rejected);
        assert_eq!(response.disposition, ArtifactInstallDisposition::Rejected);
        assert!(response.artifact.is_none());
        assert!(response.payload.is_none());
        assert_eq!(
            response.diagnostics[0].code,
            "compile.manifest_contract_mismatch"
        );
        assert!(
            response.diagnostics[0]
                .message
                .contains("manifest-bearing object output")
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn manifest_preflight_rejects_each_non_authoritative_target_abi_layout_and_kind_field() {
        let module = const_i64_module("manifest_exact_contract_preflight", &[("answer", 42)]);
        let mutations: &[(&str, &str, fn(&mut ArtifactManifestV1))] = &[
            ("target-triple", "target mismatch", |manifest| {
                manifest.target.triple.push_str("-caller-spoofed");
            }),
            ("target-os", "target mismatch", |manifest| {
                manifest.target.operating_system = if manifest.target.operating_system
                    == crate::jit_contract::TargetOperatingSystem::Macos
                {
                    crate::jit_contract::TargetOperatingSystem::Linux
                } else {
                    crate::jit_contract::TargetOperatingSystem::Macos
                };
            }),
            ("target-width", "target mismatch", |manifest| {
                manifest.target.pointer_width_bits = 32;
            }),
            ("target-endian", "target mismatch", |manifest| {
                manifest.target.endianness = Endianness::Big;
            }),
            ("target-architecture", "target mismatch", |manifest| {
                manifest.target.architecture = crate::jit_contract::TargetArchitecture::Other(
                    "caller-architecture".to_owned(),
                );
            }),
            ("abi-name", "ABI mismatch", |manifest| {
                manifest.abi.name.push_str("-caller-spoofed");
            }),
            ("abi-structure", "ABI mismatch", |manifest| {
                manifest.abi.shadow_space_bytes ^= 32;
            }),
            ("layout-pointer-size", "core layout mismatch", |manifest| {
                manifest.layout.pointer_size_bytes = 4;
            }),
            ("layout-pointer-align", "core layout mismatch", |manifest| {
                manifest.layout.pointer_alignment_bytes = 4;
            }),
            ("layout-endian", "core layout mismatch", |manifest| {
                manifest.layout.endianness = Endianness::Big;
            }),
            ("layout-stack-align", "core layout mismatch", |manifest| {
                manifest.layout.stack_alignment_bytes *= 2;
            }),
            ("artifact-kind", "artifact kind mismatch", |manifest| {
                manifest.kind = JitArtifactKind::Object;
            }),
        ];

        for (case, expected_detail, mutate) in mutations {
            let mut manifest = native_install_manifest("artifact-exact-contract", 901);
            mutate(&mut manifest);
            let request_id = format!("manifest-exact-contract-{case}");
            let response = compile_manifest_bound_executable(&request_id, &module, manifest);
            assert_eq!(response.status, CompileStatus::Rejected, "case {case}");
            assert_eq!(
                response.diagnostics[0].code, "compile.manifest_contract_mismatch",
                "case {case}"
            );
            assert!(
                response.diagnostics[0].message.contains(expected_detail),
                "case {case}: {:?}",
                response.diagnostics[0].message
            );
            assert!(response.artifact.is_none(), "case {case}");
            assert!(response.payload.is_none(), "case {case}");
        }
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn manifest_symbol_visibility_and_signature_are_derived_from_the_exact_module() {
        let module = const_i64_module("manifest_compiler_signature", &[("answer", 42)]);
        let exact_signature =
            SymbolSignature::extern_c(vec![], vec![AbiValue::new(AbiValueKind::I64)]);

        for (case, visibility, signature) in [
            (
                "visibility",
                SymbolVisibility::Internal,
                exact_signature.clone(),
            ),
            (
                "import",
                SymbolVisibility::Imported,
                exact_signature.clone(),
            ),
            (
                "signature",
                SymbolVisibility::Exported,
                SymbolSignature::extern_c(vec![], vec![AbiValue::new(AbiValueKind::I32)]),
            ),
        ] {
            let mut manifest = native_install_manifest("artifact-module-signature-reject", 902);
            manifest.symbols.push(crate::jit_contract::ArtifactSymbol {
                name: "answer".to_owned(),
                visibility,
                signature,
                offset_bytes: None,
                checksum: None,
            });
            let response = compile_manifest_bound_executable(
                &format!("manifest-module-signature-{case}"),
                &module,
                manifest,
            );
            assert_eq!(response.status, CompileStatus::Rejected, "case {case}");
            assert_eq!(
                response.diagnostics[0].code,
                "compile.manifest_signature_mismatch"
            );
            assert!(response.artifact.is_none());
            assert!(response.payload.is_none());
        }

        let mut manifest = native_install_manifest("artifact-module-signature-exact", 903);
        manifest.symbols.push(crate::jit_contract::ArtifactSymbol {
            name: "answer".to_owned(),
            visibility: SymbolVisibility::Exported,
            signature: exact_signature.clone(),
            offset_bytes: None,
            checksum: None,
        });
        let response =
            compile_manifest_bound_executable("manifest-module-signature-exact", &module, manifest);
        assert_eq!(response.status, CompileStatus::Compiled);
        let binding = response
            .artifact
            .as_ref()
            .expect("compiled artifact")
            .install
            .installed_payload_binding
            .as_ref()
            .expect("installed payload binding");
        assert_eq!(binding.symbols.len(), 1);
        assert_eq!(binding.symbols[0].name, "answer");
        assert_eq!(binding.symbols[0].visibility, SymbolVisibility::Exported);
        assert_eq!(binding.symbols[0].signature, exact_signature);
        assert!(response.into_installed_artifact().is_some());
    }

    #[test]
    fn compiler_abi_classifies_bare_function_pointer_as_nonnull_native_pointer() {
        let target_spec = TargetSpec::default_for_architecture(Target::host());
        let value = compiler_abi_value_for_trust_ir_type(
            &Ty::Func(trust_ir::FuncTyId::new(0)),
            false,
            target_spec,
        )
        .expect("bare function pointers are supported scalar ABI values");

        assert_eq!(value, AbiValue::new(AbiValueKind::Ptr));
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn reserved_hardware_vector_metadata_is_optional_but_atomic_exact_and_closed() {
        const PREFIX: &str = "trust_ir.hardware_vector_contract.";
        let module = const_i64_module("reserved_hardware_vector_metadata", &[("answer", 42)]);
        let expected = crate::jit_contract::trust_ir_hardware_vector_contract_metadata_entries();
        assert!(expected.len() > 1);

        let exact = native_install_manifest("artifact-reserved-vector-exact", 904);
        assert_eq!(reserved_manifest_metadata_mismatch(&exact), None);
        let response =
            compile_manifest_bound_executable("reserved-vector-exact", &module, exact.clone());
        assert_eq!(response.status, CompileStatus::Compiled);
        assert!(response.into_installed_artifact().is_some());

        let mut omitted = exact.clone();
        remove_reserved_metadata_namespace(&mut omitted, PREFIX);
        assert_eq!(reserved_manifest_metadata_mismatch(&omitted), None);
        let response =
            compile_manifest_bound_executable("reserved-vector-omitted", &module, omitted);
        assert_eq!(response.status, CompileStatus::Compiled);
        assert!(response.into_installed_artifact().is_some());

        let mut partial = exact.clone();
        remove_reserved_metadata_namespace(&mut partial, PREFIX);
        let (first_key, first_value) = expected.iter().next().expect("vector metadata entry");
        partial
            .metadata
            .insert(first_key.clone(), first_value.clone());
        let response =
            compile_manifest_bound_executable("reserved-vector-partial", &module, partial);
        assert_eq!(response.status, CompileStatus::Rejected);
        assert!(response.diagnostics[0].message.contains("missing or stale"));

        let mut stale = exact.clone();
        stale
            .metadata
            .insert(first_key.clone(), "caller-stale".to_owned());
        let response = compile_manifest_bound_executable("reserved-vector-stale", &module, stale);
        assert_eq!(response.status, CompileStatus::Rejected);
        assert!(response.diagnostics[0].message.contains("missing or stale"));

        let mut unknown = exact;
        unknown
            .metadata
            .insert(format!("{PREFIX}caller_unknown"), "1".to_owned());
        let response =
            compile_manifest_bound_executable("reserved-vector-unknown", &module, unknown);
        assert_eq!(response.status, CompileStatus::Rejected);
        assert!(
            response.diagnostics[0]
                .message
                .contains("unknown caller-defined key")
        );
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn reserved_host_jit_metadata_is_optional_but_atomic_exact_and_closed() {
        let prefix = crate::jit_contract::HOST_JIT_TARGET_FEATURE_PROFILE_METADATA_PREFIX;
        let exact = native_install_manifest("artifact-reserved-host-profile", 905);
        let expected =
            crate::jit_contract::host_jit_target_feature_profile_metadata_entries(&exact)
                .expect("x86_64 host profile metadata");
        assert!(expected.len() > 1);
        assert_eq!(reserved_manifest_metadata_mismatch(&exact), None);

        let mut omitted = exact.clone();
        remove_reserved_metadata_namespace(&mut omitted, prefix);
        assert_eq!(reserved_manifest_metadata_mismatch(&omitted), None);

        let mut partial = omitted;
        let (first_key, first_value) = expected.iter().next().expect("host metadata entry");
        partial
            .metadata
            .insert(first_key.clone(), first_value.clone());
        assert!(
            reserved_manifest_metadata_mismatch(&partial)
                .expect("partial host metadata rejection")
                .contains("missing or stale")
        );

        let mut stale = exact.clone();
        stale
            .metadata
            .insert(first_key.clone(), "caller-stale".to_owned());
        assert!(
            reserved_manifest_metadata_mismatch(&stale)
                .expect("stale host metadata rejection")
                .contains("missing or stale")
        );

        let mut unknown = exact;
        unknown
            .metadata
            .insert(format!("{prefix}caller_unknown"), "1".to_owned());
        assert!(
            reserved_manifest_metadata_mismatch(&unknown)
                .expect("unknown host metadata rejection")
                .contains("unknown caller-defined key")
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn installed_payload_binding_seals_exact_artifact_module_target_and_manifest_identity() {
        let module = const_i64_module(
            "installed_binding_identity",
            &[("forty_one", 41), ("forty_two", 42)],
        );
        let manifest = native_install_manifest("artifact-installed-binding-identity", 906);
        let response = compile_manifest_bound_executable(
            "installed-binding-identity",
            &module,
            manifest.clone(),
        );
        assert_eq!(response.status, CompileStatus::Compiled);

        let artifact = response.artifact.as_ref().expect("compiled artifact");
        let buffer = match response.payload.as_ref().expect("executable payload") {
            ArtifactPayload::Executable(payload) => &payload.buffer,
            ArtifactPayload::Object(_) => panic!("expected executable payload"),
        };
        let binding = artifact
            .install
            .installed_payload_binding
            .as_ref()
            .expect("installed payload binding");
        assert_eq!(binding.schema, INSTALLED_PAYLOAD_BINDING_SCHEMA);
        assert_eq!(
            binding.schema_version,
            INSTALLED_PAYLOAD_BINDING_SCHEMA_VERSION
        );
        assert_eq!(binding.artifact_kind, ArtifactKind::ExecutableMemory);
        assert_eq!(binding.artifact_identity, artifact.identity.as_str());
        assert_eq!(
            binding.trust_ir_module_sha256,
            module.stable_digest().to_string()
        );
        assert_eq!(
            binding.compiler_target_triple,
            binding.authoritative_target.triple
        );
        assert_eq!(binding.manifest_checksum, Some(manifest.checksum()));
        assert_eq!(
            binding.native_payload_sha256,
            format!("sha256:{}", sha256_hex(buffer.code_slice()))
        );
        assert_eq!(
            binding.published_image_sha256,
            format!("sha256:{}", buffer.published_image_sha256())
        );
        assert_eq!(binding.code_size_bytes, buffer.code_slice().len() as u64);
        assert_eq!(
            binding.allocation_size_bytes,
            u64::try_from(buffer.allocated_size()).expect("allocation size fits u64")
        );
        let replay = artifact
            .install
            .replay_report_metadata
            .as_ref()
            .expect("installed replay metadata");
        assert_eq!(
            replay.properties.get("published_image_sha256"),
            Some(&binding.published_image_sha256)
        );
        assert_eq!(
            replay.properties.get("allocation_size_bytes"),
            Some(&binding.allocation_size_bytes.to_string())
        );
        assert!(binding.has_canonical_binding_sha256(Some(&manifest)));
        validate_installed_payload_binding(
            &artifact.install,
            artifact.artifact_manifest.as_ref(),
            buffer,
        )
        .expect("untampered compiler binding validates");

        assert_binding_mutation_rejected(&response, "private canonical seal", |response| {
            response
                .artifact
                .as_mut()
                .unwrap()
                .install
                .installed_payload_binding
                .as_mut()
                .unwrap()
                .artifact_identity
                .push_str("-unsealed-tamper");
        });
        assert_binding_mutation_rejected(
            &response,
            "artifact kind, identity, module digest",
            |response| {
                mutate_and_reseal_installed_binding(response, |binding| {
                    binding.artifact_identity.push_str("-wrong-owner");
                });
            },
        );
        assert_binding_mutation_rejected(
            &response,
            "replay artifact id, target, code size, allocation extent",
            |response| {
                mutate_and_reseal_installed_binding(response, |binding| {
                    binding.trust_ir_module_sha256 = "sha256:wrong-module".to_owned();
                });
            },
        );
        assert_binding_mutation_rejected(
            &response,
            "binding schema/version/kind or private canonical seal",
            |response| {
                mutate_and_reseal_installed_binding(response, |binding| {
                    binding.schema =
                        "trust-cg.compile_service.installed_payload_binding.v2".to_owned();
                    binding.schema_version = 2;
                });
            },
        );
        assert_binding_mutation_rejected(&response, "private canonical seal", |response| {
            let artifact = response.artifact.as_mut().expect("compiled artifact");
            let manifest = artifact.artifact_manifest.clone();
            let binding = artifact
                .install
                .installed_payload_binding
                .as_mut()
                .expect("installed payload binding");
            let mut legacy_transcript =
                installed_payload_binding_transcript(binding, manifest.as_ref());
            let current_domain = b"trust-cg.compile_service.installed_payload_binding.sha256.v3";
            let legacy_domain = b"trust-cg.compile_service.installed_payload_binding.sha256.v2";
            let domain_offset = legacy_transcript
                .windows(current_domain.len())
                .position(|window| window == current_domain)
                .expect("v3 transcript domain");
            legacy_transcript[domain_offset..domain_offset + current_domain.len()]
                .copy_from_slice(legacy_domain);
            binding.binding_sha256 = format!("sha256:{}", sha256_hex(&legacy_transcript));
        });
        assert_binding_mutation_rejected(&response, "manifest target", |response| {
            mutate_and_reseal_installed_binding(response, |binding| {
                binding
                    .authoritative_target
                    .triple
                    .push_str("-wrong-target");
                binding.compiler_target_triple = binding.authoritative_target.triple.clone();
            });
        });
        assert_binding_mutation_rejected(
            &response,
            "binding schema/version/kind or private canonical seal",
            |response| {
                mutate_and_reseal_installed_binding(response, |binding| {
                    binding.artifact_kind = ArtifactKind::Object;
                });
            },
        );
        assert_binding_mutation_rejected(
            &response,
            "artifact kind, identity, module digest",
            |response| {
                response
                    .artifact
                    .as_mut()
                    .unwrap()
                    .install
                    .artifact
                    .artifact_kind = ArtifactKind::Object;
            },
        );
        assert_binding_mutation_rejected(&response, "private canonical seal", |response| {
            response
                .artifact
                .as_mut()
                .unwrap()
                .artifact_manifest
                .as_mut()
                .unwrap()
                .metadata
                .insert("caller.after_compile".to_owned(), "tampered".to_owned());
        });

        assert!(response.into_installed_artifact().is_some());
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn installed_payload_binding_seal_contains_full_canonical_authority_bytes() {
        fn framed_component(domain: &str, value: &[u8]) -> Vec<u8> {
            let mut bytes = Vec::new();
            bytes.extend_from_slice(&(domain.len() as u64).to_le_bytes());
            bytes.extend_from_slice(domain.as_bytes());
            bytes.extend_from_slice(&(value.len() as u64).to_le_bytes());
            bytes.extend_from_slice(value);
            bytes
        }

        fn contains_component(transcript: &[u8], component: &[u8]) -> bool {
            transcript
                .windows(component.len())
                .any(|window| window == component)
        }

        let module = const_i64_module("installed_binding_full_bytes", &[("answer", 42)]);
        let manifest = native_install_manifest("artifact-installed-binding-full-bytes", 912);
        let response = compile_manifest_bound_executable(
            "installed-binding-full-bytes",
            &module,
            manifest.clone(),
        );
        assert_eq!(response.status, CompileStatus::Compiled);
        let binding = response
            .artifact
            .as_ref()
            .expect("compiled artifact")
            .install
            .installed_payload_binding
            .as_ref()
            .expect("installed payload binding");
        let transcript = installed_payload_binding_transcript(binding, Some(&manifest));

        for (domain, canonical) in [
            (
                "binding.authoritative_target.canonical",
                binding.authoritative_target.canonical_bytes(),
            ),
            (
                "binding.authoritative_abi.canonical",
                binding.authoritative_abi.canonical_bytes(),
            ),
            (
                "binding.authoritative_layout.canonical",
                binding.authoritative_layout.canonical_bytes(),
            ),
            (
                "binding.symbol.signature.canonical",
                binding.symbols[0].signature.canonical_bytes(),
            ),
            (
                "binding.published_image_sha256",
                binding.published_image_sha256.as_bytes().to_vec(),
            ),
            (
                "binding.allocation_size_bytes",
                binding.allocation_size_bytes.to_le_bytes().to_vec(),
            ),
        ] {
            assert!(
                contains_component(&transcript, &framed_component(domain, &canonical)),
                "private SHA-256 transcript omitted {domain}"
            );
        }

        let manifest_option = installed_payload_binding_manifest_option_bytes(Some(&manifest));
        assert!(contains_component(
            &transcript,
            &framed_component("binding.manifest.canonical_option", &manifest_option),
        ));
        let checksum_option =
            installed_payload_binding_checksum_option_bytes(binding.manifest_checksum);
        assert!(contains_component(
            &transcript,
            &framed_component("binding.manifest_checksum.option", &checksum_option),
        ));

        // Model an adversary finding a second manifest with the same public
        // stable128 summary: the binding's summary field is deliberately held
        // fixed while the presented canonical manifest bytes change. The
        // private SHA-256 seal must still diverge.
        let mut collision_candidate = manifest.clone();
        collision_candidate.metadata.insert(
            "adversarial.same-public-summary".to_owned(),
            "different-canonical-manifest".to_owned(),
        );
        assert_eq!(binding.manifest_checksum, Some(manifest.checksum()));
        assert_ne!(
            installed_payload_binding_sha256(binding, Some(&manifest)),
            installed_payload_binding_sha256(binding, Some(&collision_candidate)),
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn installed_payload_binding_rejects_live_payload_symbol_and_replay_tampering() {
        let module = const_i64_module(
            "installed_binding_live_inventory",
            &[("alpha", 41), ("beta", 42)],
        );
        let manifest = native_install_manifest("artifact-installed-binding-live", 907);
        let response =
            compile_manifest_bound_executable("installed-binding-live", &module, manifest);
        assert_eq!(response.status, CompileStatus::Compiled);

        assert_binding_mutation_rejected(&response, "live executable extent/digest", |response| {
            mutate_and_reseal_installed_binding(response, |binding| {
                binding.native_payload_sha256 = "sha256:caller-payload".to_owned();
            });
        });
        assert_binding_mutation_rejected(&response, "live executable extent/digest", |response| {
            mutate_and_reseal_installed_binding(response, |binding| {
                binding.code_size_bytes += 1;
            });
        });
        assert_binding_mutation_rejected(&response, "live executable extent/digest", |response| {
            mutate_and_reseal_installed_binding(response, |binding| {
                binding.published_image_sha256 = "sha256:caller-published-image".to_owned();
            });
        });
        assert_binding_mutation_rejected(&response, "live executable extent/digest", |response| {
            mutate_and_reseal_installed_binding(response, |binding| {
                binding.allocation_size_bytes += 1;
            });
        });
        assert_binding_mutation_rejected(&response, "live executable extent/digest", |response| {
            response
                .artifact
                .as_mut()
                .unwrap()
                .install
                .artifact
                .code_size_bytes += 1;
        });
        assert_binding_mutation_rejected(&response, "live executable extent/digest", |response| {
            let allocation_size = response
                .artifact
                .as_mut()
                .unwrap()
                .install
                .artifact
                .allocation_size_bytes
                .as_mut()
                .expect("live allocation metadata");
            *allocation_size = allocation_size
                .checked_add(1)
                .expect("test allocation size increment");
        });
        assert_binding_mutation_rejected(&response, "live range", |response| {
            mutate_and_reseal_installed_binding(response, |binding| {
                binding.symbols[0].start_offset += 1;
            });
        });
        assert_binding_mutation_rejected(&response, "live aliases", |response| {
            mutate_and_reseal_installed_binding(response, |binding| {
                assert!(!binding.symbols[0].aliases.is_empty());
                binding.symbols[0].aliases.clear();
            });
        });
        assert_binding_mutation_rejected(
            &response,
            "bound canonical symbols are not strictly name-sorted",
            |response| {
                mutate_and_reseal_installed_binding(response, |binding| {
                    binding.symbols.swap(0, 1);
                });
            },
        );
        assert_binding_mutation_rejected(&response, "private canonical seal", |response| {
            response
                .artifact
                .as_mut()
                .unwrap()
                .install
                .installed_payload_binding
                .as_mut()
                .unwrap()
                .symbols[0]
                .visibility = SymbolVisibility::Internal;
        });
        assert_binding_mutation_rejected(&response, "private canonical seal", |response| {
            response
                .artifact
                .as_mut()
                .unwrap()
                .install
                .installed_payload_binding
                .as_mut()
                .unwrap()
                .symbols[0]
                .signature =
                SymbolSignature::extern_c(vec![], vec![AbiValue::new(AbiValueKind::I32)]);
        });

        for property in [
            "native_payload_sha256",
            "published_image_sha256",
            "allocation_size_bytes",
            "trust_ir_module_sha256",
            "installed_payload_binding_sha256",
        ] {
            assert_binding_mutation_rejected(
                &response,
                "replay artifact id, target, code size, allocation extent",
                |response| {
                    response
                        .artifact
                        .as_mut()
                        .unwrap()
                        .install
                        .replay_report_metadata
                        .as_mut()
                        .unwrap()
                        .properties
                        .insert(property.to_owned(), "sha256:replay-tamper".to_owned());
                },
            );
        }
        assert_binding_mutation_rejected(
            &response,
            "replay artifact id, target, code size, allocation extent",
            |response| {
                response
                    .artifact
                    .as_mut()
                    .unwrap()
                    .install
                    .replay_report_metadata
                    .as_mut()
                    .unwrap()
                    .target = Some("wrong-target".to_owned());
            },
        );
        assert_binding_mutation_rejected(&response, "replay range/aliases", |response| {
            response
                .artifact
                .as_mut()
                .unwrap()
                .install
                .replay_report_metadata
                .as_mut()
                .unwrap()
                .symbols[0]
                .range
                .end_offset += 1;
        });
        assert_binding_mutation_rejected(&response, "replay entry symbol", |response| {
            response
                .artifact
                .as_mut()
                .unwrap()
                .install
                .replay_report_metadata
                .as_mut()
                .unwrap()
                .entry_symbol = Some("caller-missing-entry".to_owned());
        });
        assert_binding_mutation_rejected(&response, "install entrypoint inventory", |response| {
            response
                .artifact
                .as_mut()
                .unwrap()
                .install
                .exported_entrypoints
                .pop();
        });
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn installed_contract_lookup_never_exposes_compiler_internal_symbols_or_aliases() {
        let mut module = const_i64_module("installed_binding_internal", &[("hidden", 42)]);
        module.functions[0].linkage = trust_ir::Linkage::Internal;
        let manifest = native_install_manifest("artifact-installed-binding-internal", 908);
        let signature = SymbolSignature::extern_c(vec![], vec![AbiValue::new(AbiValueKind::I64)]);
        let contract_for = |symbol: &str| {
            SymbolLookupContract::new(
                symbol,
                signature.clone(),
                manifest.target.checksum(),
                manifest.abi.checksum(),
                manifest.layout.checksum(),
            )
            .with_invalidation_checksum(manifest.invalidation.checksum())
            .with_manifest_checksum(manifest.checksum())
        };
        let response = compile_manifest_bound_executable(
            "installed-binding-internal",
            &module,
            manifest.clone(),
        );
        assert_eq!(response.status, CompileStatus::Compiled);
        let installed = response
            .into_installed_artifact()
            .expect("installed artifact");
        let binding = installed
            .metadata
            .installed_payload_binding
            .as_ref()
            .expect("installed payload binding");
        assert_eq!(binding.symbols[0].visibility, SymbolVisibility::Internal);

        for symbol in ["hidden", "_hidden"] {
            let error = installed
                .get_contract_symbol_bound::<extern "C" fn() -> i64>(
                    &manifest,
                    &contract_for(symbol),
                )
                .expect_err("internal symbol lookup must fail closed");
            assert!(
                error.to_string().contains("compiler-private symbol"),
                "lookup {symbol:?} returned {error}"
            );
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn compile_trust_ir_executable_returns_two_function_payload() {
        let module = const_i64_module(
            "compile_service_executable",
            &[("forty_one", 41), ("forty_two", 42)],
        );
        let mut request = CompileRequest::new("executable", CompileGeneration::new(21));
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.provenance.source_kind = SourceKind::TrustIrModule;

        let response = service().compile(request, &module);

        assert_eq!(response.status, CompileStatus::Compiled);
        let artifact = response.artifact.expect("compiled artifact");
        assert_eq!(
            artifact.metadata.artifact_kind,
            ArtifactKind::ExecutableMemory
        );
        assert_eq!(artifact.metadata.target, Target::Aarch64);
        assert_eq!(artifact.metadata.profile, CompileProfileId::HostJitFast);
        assert!(artifact.metadata.allocation_size_bytes.is_some());
        assert!(artifact.install.replay_report_metadata.is_some());
        assert_eq!(
            artifact
                .install
                .exported_entrypoints
                .iter()
                .map(|entrypoint| entrypoint.name.as_str())
                .collect::<Vec<_>>(),
            vec!["forty_one", "forty_two"]
        );
        assert_eq!(artifact.install.functions.len(), 2);
        assert_eq!(artifact.install.counters.len(), 2);

        match response.payload.expect("executable payload") {
            ArtifactPayload::Executable(payload) => {
                assert_eq!(payload.metrics.function_count, 2);
                assert_eq!(payload.functions.len(), 2);
                assert_eq!(payload.buffer.symbol_count(), 2);
                assert!(payload.buffer.get_fn_ptr_bound("forty_one").is_some());
                assert!(payload.buffer.get_fn_ptr_bound("forty_two").is_some());
            }
            other => panic!("expected executable payload, got {other:?}"),
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn compile_trust_ir_executable_replay_report_reaches_installed_artifact() {
        let module = const_i64_module(
            "compile_service_executable_replay",
            &[("forty_one", 41), ("forty_two", 42)],
        );
        let generation = CompileGeneration::new(24);
        let manifest = native_install_manifest("artifact-executable-replay", generation.get());
        let reference = ArtifactManifestReference::from_manifest(&manifest);
        let mut request =
            CompileRequest::new("executable-replay", generation).with_artifact_manifest(manifest);
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.provenance.source_kind = SourceKind::TrustIrModule;
        request.provenance.source_fingerprint =
            Some("sha256:compile-service-executable-replay".to_owned());

        let response = service().compile(request, &module);

        assert_eq!(response.status, CompileStatus::Compiled);
        let install_report = {
            let artifact = response.artifact.as_ref().expect("compiled artifact");
            let report = artifact
                .install
                .replay_report_metadata
                .as_ref()
                .expect("executable install metadata should carry replay report");
            let installed_payload_binding = artifact
                .install
                .installed_payload_binding
                .as_ref()
                .expect("executable install metadata should carry a payload binding");
            assert_eq!(
                report.artifact_id.as_deref(),
                Some(artifact.identity.as_str())
            );
            assert_eq!(
                report.target.as_deref(),
                Some(installed_payload_binding.compiler_target_triple.as_str())
            );
            assert_eq!(
                report.properties.get("generation").map(String::as_str),
                Some("24")
            );
            assert_eq!(
                report
                    .properties
                    .get("source_fingerprint")
                    .map(String::as_str),
                Some("sha256:compile-service-executable-replay")
            );

            let expected_manifest_checksum = reference.manifest_checksum.to_string();
            let expected_proof_policy_checksum = reference.proof_policy_checksum.to_string();
            let expected_layout_checksum = reference.layout_checksum.to_string();
            let expected_invalidation_key = reference.invalidation_checksum.to_string();
            assert_eq!(
                report.properties.get("artifact_manifest_checksum"),
                Some(&expected_manifest_checksum)
            );
            assert_eq!(
                report.properties.get("proof_policy_checksum"),
                Some(&expected_proof_policy_checksum)
            );
            assert_eq!(
                report.properties.get("layout_checksum"),
                Some(&expected_layout_checksum)
            );
            assert_eq!(
                report.properties.get("invalidation_key"),
                Some(&expected_invalidation_key)
            );

            let mut symbol_names = report
                .symbols
                .iter()
                .map(|symbol| symbol.name.as_str())
                .collect::<Vec<_>>();
            symbol_names.sort();
            assert_eq!(symbol_names, vec!["forty_one", "forty_two"]);
            assert!(report.symbols.iter().all(|symbol| {
                symbol.aliases.contains(&format!("_{}", symbol.name))
                    && symbol.range.is_valid()
                    && symbol.range.byte_len() > 0
            }));

            let mut pc_map_symbols = report
                .pc_map
                .iter()
                .map(|entry| entry.symbol.as_str())
                .collect::<Vec<_>>();
            pc_map_symbols.sort();
            assert_eq!(pc_map_symbols, vec!["forty_one", "forty_two"]);
            for symbol in &report.symbols {
                assert!(report.pc_map.iter().any(|entry| {
                    entry.symbol == symbol.name
                        && entry.pc_offset == symbol.range.start_offset
                        && entry.symbol_offset == 0
                }));
            }

            report.clone()
        };

        let installed = response
            .into_installed_artifact()
            .expect("installable executable artifact");
        assert_eq!(
            installed.metadata.replay_report_metadata.as_ref(),
            Some(&install_report)
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn installed_executable_exposes_petri_native_compile_artifact_handoff_fields() {
        let module = const_i64_module("petri_compile_artifact_handoff", &[("successor", 42)]);
        let generation = CompileGeneration::new(33);
        let manifest = native_install_manifest("artifact-petri-handoff", generation.get());
        let mut request =
            CompileRequest::new("petri-handoff", generation).with_artifact_manifest(manifest);
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.provenance.source_kind = SourceKind::TrustIrModule;
        request.provenance.source_fingerprint =
            Some("sha256:petri-compile-artifact-handoff".to_owned());

        let response = service().compile(request, &module);
        assert_eq!(response.status, CompileStatus::Compiled);
        let installed = response
            .into_installed_artifact()
            .expect("installable executable artifact");
        let report = installed
            .metadata
            .replay_report_metadata
            .as_ref()
            .expect("executable replay report");
        let native_payload_sha256 = report
            .properties
            .get("native_payload_sha256")
            .expect("native payload digest")
            .clone();
        let callable_pointer = PetriNativeSuccessorCallablePointer::from_ptr(
            installed
                .entrypoint_ptr("successor")
                .expect("successor entrypoint")
                .as_ptr(),
        )
        .expect("non-null callable pointer");
        let lifetime_owner = petri_native_successor_lifetime_owner(&installed.metadata);

        let evidence =
            installed.petri_native_successor_compile_artifact_handoff_evidence(Some("successor"));

        assert_eq!(
            evidence.status,
            PetriNativeSuccessorExecutableCallStatus::Ready
        );
        assert_eq!(evidence.blocker, None);
        assert_eq!(evidence.reason_code, None);
        assert!(evidence.is_ready());
        assert_eq!(
            evidence.native_payload_sha256.as_deref(),
            Some(native_payload_sha256.as_str())
        );
        assert_eq!(evidence.entry_symbol.as_deref(), Some("successor"));
        assert_eq!(evidence.callable_pointer, Some(callable_pointer));
        assert!(
            evidence
                .executable_region_sha256
                .as_deref()
                .expect("executable region identity")
                .starts_with("sha256:")
        );
        assert_eq!(
            evidence.lifetime_owner.as_deref(),
            Some(lifetime_owner.as_str())
        );
        assert_eq!(evidence.current_generation, Some(generation.get()));
        assert_eq!(
            evidence.compile_artifact_handoff_sha256,
            evidence.canonical_compile_artifact_handoff_sha256()
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn installed_executable_exposes_lifetime_proof_but_runtime_readiness_stays_fail_closed() {
        let module = const_i64_module(
            "petri_runtime_readiness_from_installed_artifact",
            &[("successor", 42)],
        );
        let generation = CompileGeneration::new(36);
        let manifest =
            native_install_manifest("artifact-petri-runtime-readiness", generation.get());
        let mut request = CompileRequest::new("petri-runtime-readiness", generation)
            .with_artifact_manifest(manifest);
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.provenance.source_kind = SourceKind::TrustIrModule;

        let response = service().compile(request, &module);
        assert_eq!(response.status, CompileStatus::Compiled);
        let installed = response
            .into_installed_artifact()
            .expect("installable executable artifact");
        let callable_pointer = PetriNativeSuccessorCallablePointer::from_ptr(
            installed
                .entrypoint_ptr("successor")
                .expect("successor entrypoint")
                .as_ptr(),
        )
        .expect("non-null callable pointer");

        let lifetime_proof = installed
            .petri_native_successor_callable_lifetime_proof(Some("successor"), None)
            .expect("lifetime proof from installed executable");
        assert_eq!(lifetime_proof.callable_pointer, callable_pointer);
        assert_eq!(lifetime_proof.observed_generation, generation.get());
        assert_eq!(lifetime_proof.expires_after_generation, None);
        assert!(
            lifetime_proof
                .executable_region_sha256
                .starts_with("sha256:")
        );
        assert_eq!(
            lifetime_proof.lifetime_proof_sha256,
            lifetime_proof.canonical_lifetime_proof_sha256()
        );

        let readiness = installed.petri_native_successor_runtime_readiness_packet(
            Some("successor"),
            None,
            None,
            None,
            None,
        );
        assert_eq!(
            readiness.status,
            PetriNativeSuccessorRuntimeReadinessStatus::Blocked
        );
        assert!(!readiness.is_ready_for_runtime_call());
        assert!(!readiness.ready_for_runtime_call);
        assert_eq!(readiness.current_generation, generation.get());
        assert!(!readiness.call_packet_available);
        assert_eq!(readiness.call_packet_sha256, None);
        assert_eq!(readiness.callable_pointer, None);
        assert_eq!(
            readiness.blocker,
            Some(
                PetriNativeSuccessorRuntimeReadinessBlocker::ManifestIdentity(
                    PetriNativeSuccessorManifestIdentityBlocker::MissingNativeInstallGatePacket
                )
            )
        );
        assert_eq!(readiness.blocker_stage, Some("manifest_identity"));
        assert_eq!(
            readiness.reason_code,
            Some("missing_native_install_gate_packet")
        );
        assert_eq!(
            readiness.required_evidence,
            Some(NATIVE_INSTALL_GATE_PACKET_SCHEMA)
        );
        assert!(!readiness.manifest_identity_ready);
        assert_eq!(
            readiness.manifest_identity_blocker,
            Some(PetriNativeSuccessorManifestIdentityBlocker::MissingNativeInstallGatePacket)
        );
        assert_eq!(
            readiness.lifetime_proof_sha256.as_deref(),
            Some(lifetime_proof.lifetime_proof_sha256.as_str())
        );
        assert_eq!(readiness.runtime_abi_proof_sha256, None);
        assert_eq!(
            readiness.runtime_readiness_packet_sha256,
            readiness.canonical_runtime_readiness_packet_sha256()
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn installed_artifact_from_executable_buffer_replay_metadata_exposes_petri_handoff() {
        let module = const_i64_module(
            "petri_direct_jit_compile_artifact_handoff",
            &[("successor", 42), ("helper", 7)],
        );
        let generation = CompileGeneration::new(35);
        let mut request = CompileRequest::new("petri-direct-jit-handoff", generation);
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.provenance.source_kind = SourceKind::TrustIrModule;

        let mut response = service().compile(request, &module);
        assert_eq!(response.status, CompileStatus::Compiled);
        let replay = response
            .artifact
            .as_ref()
            .expect("compiled artifact")
            .install
            .replay_report_metadata
            .clone()
            .expect("executable replay metadata");
        let native_payload_sha256 = replay
            .properties
            .get("native_payload_sha256")
            .expect("native payload digest")
            .clone();
        let payload = match response.payload.take().expect("executable payload") {
            ArtifactPayload::Executable(payload) => payload,
            other => panic!("expected executable payload, got {other:?}"),
        };

        let installed = InstalledArtifact::from_executable_buffer_replay_metadata(
            payload.buffer,
            generation,
            replay.clone(),
        );
        let evidence =
            installed.petri_native_successor_compile_artifact_handoff_evidence(Some("successor"));

        assert_eq!(
            installed.metadata.disposition,
            ArtifactInstallDisposition::ProfileOnly
        );
        assert_eq!(
            installed.metadata.identity.as_str(),
            replay.artifact_id.as_deref().expect("replay artifact id")
        );
        assert_eq!(
            installed.metadata.replay_report_metadata.as_ref(),
            Some(&replay)
        );
        assert_eq!(
            installed
                .metadata
                .exported_entrypoints
                .iter()
                .map(|entrypoint| entrypoint.name.as_str())
                .collect::<Vec<_>>(),
            vec!["helper", "successor"]
        );
        assert_eq!(
            evidence.status,
            PetriNativeSuccessorExecutableCallStatus::Ready
        );
        assert!(evidence.is_ready());
        assert_eq!(
            evidence.native_payload_sha256.as_deref(),
            Some(native_payload_sha256.as_str())
        );
        assert_eq!(evidence.entry_symbol.as_deref(), Some("successor"));
        assert!(evidence.callable_pointer.is_some());
        assert!(
            evidence
                .executable_region_sha256
                .as_deref()
                .expect("executable region identity")
                .starts_with("sha256:")
        );
        assert_eq!(evidence.current_generation, Some(generation.get()));
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn installed_executable_petri_handoff_fails_closed_for_missing_symbol_pointer() {
        let module = const_i64_module(
            "petri_compile_artifact_missing_pointer",
            &[("successor", 42)],
        );
        let generation = CompileGeneration::new(34);
        let manifest = native_install_manifest("artifact-petri-missing-pointer", generation.get());
        let mut request = CompileRequest::new("petri-missing-pointer", generation)
            .with_artifact_manifest(manifest);
        request.artifact_kind = ArtifactKind::ExecutableMemory;
        request.provenance.source_kind = SourceKind::TrustIrModule;

        let response = service().compile(request, &module);
        assert_eq!(response.status, CompileStatus::Compiled);
        let installed = response
            .into_installed_artifact()
            .expect("installable executable artifact");

        let evidence = installed
            .petri_native_successor_compile_artifact_handoff_evidence(Some("missing_successor"));

        assert_eq!(
            evidence.status,
            PetriNativeSuccessorExecutableCallStatus::Blocked
        );
        assert_eq!(
            evidence.blocker,
            Some(PetriNativeSuccessorCompileArtifactHandoffBlocker::MissingCallablePointer)
        );
        assert_eq!(evidence.reason_code, Some("missing_callable_pointer"));
        assert_eq!(evidence.entry_symbol.as_deref(), Some("missing_successor"));
        assert!(evidence.native_payload_sha256.is_some());
        assert_eq!(evidence.callable_pointer, None);
        assert_eq!(evidence.executable_region_sha256, None);
        assert_eq!(evidence.current_generation, Some(generation.get()));
        assert!(!evidence.is_ready());
        assert!(
            installed
                .petri_native_successor_callable_lifetime_proof(Some("missing_successor"), None)
                .is_none()
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn profile_only_executable_response_does_not_convert_to_installed_artifact() {
        let module = const_i64_module("compile_service_profile_only", &[("answer", 42)]);
        let mut request =
            CompileRequest::new("profile-only-executable", CompileGeneration::new(22));
        request.install_intent = InstallIntent::CompileOnly;
        request.provenance.source_kind = SourceKind::TrustIrModule;

        let response = service().compile(request, &module);

        assert_eq!(response.status, CompileStatus::Compiled);
        assert!(matches!(
            response.payload.as_ref(),
            Some(ArtifactPayload::Executable(_))
        ));
        assert_eq!(
            response
                .artifact
                .as_ref()
                .expect("compiled artifact")
                .install
                .disposition,
            ArtifactInstallDisposition::ProfileOnly
        );
        assert!(response.into_installed_artifact().is_none());
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn compile_trust_ir_executable_installs_ay_shaped_registry_handle() {
        #[derive(Default)]
        struct SolverRegistry {
            installed: HashMap<(String, CompileGeneration, ArtifactIdentity), InstalledArtifact>,
            stale_before: CompileGeneration,
        }

        impl SolverRegistry {
            fn mark_stale_before(&mut self, generation: CompileGeneration) {
                self.stale_before = self.stale_before.max(generation);
            }

            fn install(
                &mut self,
                program_id: &str,
                artifact: InstalledArtifact,
            ) -> Result<(), &'static str> {
                if artifact.metadata.generation < self.stale_before {
                    return Err("stale generation");
                }
                let key = (
                    program_id.to_owned(),
                    artifact.metadata.generation,
                    artifact.metadata.identity.clone(),
                );
                self.installed.insert(key, artifact);
                Ok(())
            }

            fn get(
                &self,
                program_id: &str,
                generation: CompileGeneration,
                identity: &ArtifactIdentity,
            ) -> Option<&InstalledArtifact> {
                self.installed
                    .get(&(program_id.to_owned(), generation, identity.clone()))
            }
        }

        let module = const_i64_module(
            "ay_solver_program_region",
            &[("ay_entry", 42), ("ay_helper", 7)],
        );
        let generation = CompileGeneration::new(30);
        let ay_const_i64_signature = crate::jit_contract::SymbolSignature::extern_c(
            vec![],
            vec![crate::jit_contract::AbiValue::new(
                crate::jit_contract::AbiValueKind::I64,
            )],
        );
        let mut manifest = native_install_manifest("artifact-ay-entry-manifest", generation.get());
        manifest.symbols.push(crate::jit_contract::ArtifactSymbol {
            name: "ay_entry".to_owned(),
            visibility: crate::jit_contract::SymbolVisibility::Exported,
            signature: ay_const_i64_signature.clone(),
            offset_bytes: Some(0),
            checksum: None,
        });
        manifest.symbols.push(crate::jit_contract::ArtifactSymbol {
            name: "ay_helper".to_owned(),
            visibility: crate::jit_contract::SymbolVisibility::Exported,
            signature: ay_const_i64_signature.clone(),
            offset_bytes: None,
            checksum: None,
        });
        let manifest_reference = ArtifactManifestReference::from_manifest(&manifest);
        let ay_entry_contract = SymbolLookupContract::new(
            "ay_entry",
            ay_const_i64_signature.clone(),
            manifest.target.checksum(),
            manifest.abi.checksum(),
            manifest.layout.checksum(),
        )
        .with_invalidation_checksum(manifest.invalidation.checksum())
        .with_manifest_checksum(manifest.checksum());
        let ay_helper_contract = SymbolLookupContract::new(
            "ay_helper",
            ay_const_i64_signature.clone(),
            manifest.target.checksum(),
            manifest.abi.checksum(),
            manifest.layout.checksum(),
        )
        .with_invalidation_checksum(manifest.invalidation.checksum())
        .with_manifest_checksum(manifest.checksum());
        let fence = CompileGenerationFence::new();
        let mut request = CompileRequest::new("ay-region-install", generation)
            .with_artifact_manifest(manifest.clone());
        request.generation_fence = Some(fence.clone());
        request.provenance.source_kind = SourceKind::TrustIrModule;
        request
            .provenance
            .caller_context
            .insert("program_id".to_owned(), "solver:ay:region-1".to_owned());
        request
            .provenance
            .caller_context
            .insert("region".to_owned(), "two-function-region".to_owned());

        let response = service().compile(request, &module);
        assert_eq!(response.status, CompileStatus::Compiled);
        let installed = response
            .into_installed_artifact()
            .expect("installed executable artifact");
        assert_eq!(installed.metadata.generation, generation);
        assert_eq!(
            installed.metadata.artifact_manifest,
            Some(manifest_reference.clone())
        );
        manifest_reference
            .verify_manifest(&manifest)
            .expect("ay_entry manifest reference should verify");
        assert_eq!(
            installed
                .metadata
                .exported_entrypoints
                .iter()
                .map(|entrypoint| entrypoint.name.as_str())
                .collect::<Vec<_>>(),
            vec!["ay_entry", "ay_helper"]
        );

        let identity = installed.metadata.identity.clone();
        let mut registry = SolverRegistry::default();
        registry
            .install("solver:ay:region-1", installed.clone())
            .expect("fresh generation installs");

        let registered = registry
            .get("solver:ay:region-1", generation, &identity)
            .expect("registry entry");
        let entry = registered
            .get_contract_symbol_bound::<extern "C" fn() -> i64>(&manifest, &ay_entry_contract)
            .expect("validated ay_entry contract symbol");
        assert_eq!(entry.symbol(), "ay_entry");
        assert_eq!(entry.signature(), &ay_const_i64_signature);
        let entry_fn = unsafe {
            // SAFETY: the manifest-validated contract above matches the
            // compiled ay_entry extern "C" no-arg i64 signature.
            entry.into_fn()
        };
        assert_eq!(entry_fn(), 42);
        let helper = registered
            .get_contract_symbol_bound::<extern "C" fn() -> i64>(&manifest, &ay_helper_contract)
            .expect("validated ay_helper contract symbol");
        assert_eq!(helper.symbol(), "ay_helper");
        assert_eq!(helper.signature(), &ay_const_i64_signature);
        let helper_fn = unsafe {
            // SAFETY: the manifest-validated contract above matches the
            // compiled ay_helper extern "C" no-arg i64 signature.
            helper.into_fn()
        };
        assert_eq!(helper_fn(), 7);

        registry.mark_stale_before(CompileGeneration::new(31));
        assert_eq!(
            registry.install("solver:ay:region-1", installed),
            Err("stale generation")
        );

        let mut stale_request = CompileRequest::new("ay-stale-install", generation);
        stale_request.generation_fence = Some(fence.clone());
        fence.mark_stale_before(CompileGeneration::new(31));
        let stale_response = service().compile(stale_request, &module);
        assert_eq!(stale_response.status, CompileStatus::Stale);
        assert!(stale_response.into_installed_artifact().is_none());
    }
}
