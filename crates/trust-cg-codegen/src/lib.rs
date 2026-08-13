// trust-cg-codegen - Proof-oriented machine code generation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

// Trust Codegen is embedded into tRust's compiler build, so rustc's internal lint set
// is applied here. These rustc query lints are not part of Trust Codegen's standalone
// API contract; deterministic codegen evidence is checked at Trust Codegen
// boundaries.
#![allow(rustc::default_hash_types)]
#![allow(rustc::potential_query_instability)]
#![allow(
    clippy::approx_constant,
    clippy::doc_overindented_list_items,
    clippy::doc_lazy_continuation,
    clippy::empty_line_after_doc_comments,
    clippy::field_reassign_with_default,
    clippy::large_enum_variant,
    clippy::match_like_matches_macro,
    clippy::result_large_err,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::unusual_byte_groupings
)]

//! Machine code generation with proof and validation hooks for Trust Codegen.
//!
//! This crate generates machine code from LIR and attaches the validation or
//! proof evidence available for supported lowering paths. Coverage and evidence
//! strength vary by target and operation.
//!
//! Primary supported targets: AArch64 and x86-64 host JIT/codegen. RISC-V is
//! still a secondary/future target.
//!
//! # Calling convention for JIT-compiled symbols
//!
//! Functions JIT-compiled by [`jit::JitCompiler`] follow the host
//! platform's C calling convention (AAPCS64 / Apple DarwinPCS on
//! aarch64, System V AMD64 on Unix x86-64, Microsoft x64 on Windows
//! x86-64). Raw symbol lookup through
//! [`jit::ExecutableBuffer`] is kept as a low-level ABI compatibility
//! and internal harness surface; it is not the product dispatch contract
//! for external `ay` or `ty` native execution.
//!
//! Product consumers must validate a manifest-backed
//! [`jit_contract::SymbolLookupContract`] and use
//! [`compile_service::InstalledArtifact::get_contract_symbol_bound`]
//! before calling native code. See the full ABI and lookup contract
//! (register assignments, callee-saved sets, sret handling, known gaps,
//! and the raw-vs-product distinction) at the top of [`jit`].

/// Compile-time feature identity consumed by persistent machine-code caches.
///
/// Cargo can build the same source tree with materially different codegen or
/// register-allocation behavior, so source content alone is not a sufficient
/// cache discriminator.
pub const BUILD_FEATURE_IDENTITY: &str =
    match (cfg!(feature = "verify"), cfg!(feature = "ay-regalloc")) {
        (false, false) => "trust-cg-codegen.features.v1:none",
        (true, false) => "trust-cg-codegen.features.v1:verify",
        (false, true) => "trust-cg-codegen.features.v1:ay-regalloc",
        (true, true) => "trust-cg-codegen.features.v1:verify,ay-regalloc",
    };

pub mod aarch64;
pub mod async_compile_service;
pub mod ay_lra_proof_manifest;
pub mod ay_pb_pbo_checked_arithmetic_contract;
pub mod ay_sat_bcp_contract;
pub mod ay_sat_helper_replacement_contract;
pub mod branch_forward;
pub mod coff;
pub mod compile_artifact_cache_profile;
pub mod compile_service;
pub mod compiler;
pub mod constant_pool;
pub mod coreml_emitter;
pub mod debug_provenance;
pub mod decode_check;
pub mod dialect_pipeline;
pub mod dwarf_cfi;
pub mod dwarf_cfi_decode_check;
pub mod dwarf_info;
pub mod elf;
pub use trust_cg_process_env as env_lock;
pub mod error;
pub mod exception_handling;
pub mod frame;
pub mod global_stub;
pub mod guard_ledger;
pub mod interpreter;
pub mod jit;
pub mod jit_ay_canary_allowlist;
pub mod jit_cert;
pub mod jit_contract;
pub mod jit_control_plane;
pub mod jit_diagnostics;
pub mod jit_install_gate;
pub mod jit_nomination;
pub mod jit_profile_cache;
pub mod jit_release;
pub mod jit_shadow_replay;
pub mod jit_ty_canary_allowlist;
pub mod layout;
pub mod loop_align;
pub mod lower;
pub mod macho;
pub mod metal_emitter;
pub mod module_merge;
pub mod pgo_runner;
pub mod pipeline;
pub mod proof_evidence;
pub mod relax;
pub mod resource_limits;
pub mod rewrite_admission;
pub mod riscv;
pub mod target;
pub mod trust_ir_bitfield_builder;
pub mod ty_reducer_evidence;
pub mod unwind;
pub mod wasm;
pub mod x86_64;

pub use async_compile_service::{
    AsyncCompilePoll, AsyncCompileService, AsyncCompileServiceConfig, AsyncCompileState,
    AsyncCompileTicket, AsyncSubmitAccepted, AsyncSubmitReject, AsyncSubmitRejectCode,
};
pub use compile_artifact_cache_profile::{
    COMPILE_ARTIFACT_CACHE_TELEMETRY_ARTIFACT_REUSE_STATUS_CODES,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_BOUNDARY_CODES, COMPILE_ARTIFACT_CACHE_TELEMETRY_DESCRIPTOR,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_DIGEST_FIELDS,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_IDENTITY_FIELDS,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_MANIFEST_SCHEMA,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_MANIFEST_SCHEMA_VERSION,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_METRIC_FIELDS,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_NON_REUSE_STATUS_CODES,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_OPTIONAL_FIELDS,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_OPTIONAL_IDENTITY_FIELDS,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_REQUIRED_FIELDS, COMPILE_ARTIFACT_CACHE_TELEMETRY_SCHEMA,
    COMPILE_ARTIFACT_CACHE_TELEMETRY_SCHEMA_VERSION, COMPILE_ARTIFACT_CACHE_TELEMETRY_STATUS_CODES,
    COMPILE_ARTIFACT_PROFILE_USE_DISABLED_SHA256, CompileArtifactCacheBoundary,
    CompileArtifactCacheConfig, CompileArtifactCacheEntry, CompileArtifactCacheKey,
    CompileArtifactCacheLookup, CompileArtifactCacheStatus, CompileArtifactCacheTelemetry,
    CompileArtifactCacheTelemetryDescriptor, CompileArtifactCacheTelemetryKeyValueRow,
    CompileArtifactCacheTelemetryManifestRow, CompileArtifactCacheTelemetryManifestRowKind,
    CompileArtifactCacheTelemetryRowKind, CompileArtifactDependencyIdentity,
    CompileArtifactProofPolicy, LocalFilesystemCompileArtifactCache,
    TRUST_COMPILE_ARTIFACT_CACHE_SCHEMA, TRUST_COMPILE_ARTIFACT_CACHE_SCHEMA_VERSION,
    compile_artifact_cache_telemetry_descriptor,
};
pub use compile_service::{
    ArtifactIdentity, ArtifactIdentityInput, ArtifactKind, ArtifactManifestReference,
    ArtifactMetadata, ArtifactPayload, ArtifactProvenance, CancellationToken, CompileDiagnostic,
    CompileGeneration, CompileGenerationFence, CompileProfile, CompileProfileId, CompileRequest,
    CompileRequestId, CompileResponse, CompileService, CompileServiceConfig, CompileStatus,
    CompiledArtifact, CounterSummary, DiagnosticSeverity, EntryPointMetadata,
    ExecutableArtifactPayload, ExpandedCompileProfile, FunctionArtifactMetadata, InstallIntent,
    InstallMetadata, InstallProofSummary, InstalledArtifact, ObjectArtifactPayload,
    ProofInstallTelemetrySummary, RawExternBinding, SourceKind,
};
pub use compiler::{
    CompilationMetrics, CompilationResult, CompileError, Compiler, CompilerConfig, CompilerTrace,
    CompilerTraceLevel, FunctionQualityMetrics, JitCompilationResult, ProofCertificate,
};
pub use error::{CodegenError, TrustCgError};
pub use interpreter::{
    InterpreterConfig, InterpreterError, InterpreterValue, interpret, interpret_with_config,
};
pub use jit::{
    ExecutableBuffer, JitCompiler, JitConfig, JitError, ProfileHookMode, ProfileStats,
    ensure_jit_execute_mode,
};
pub use jit_ay_canary_allowlist::{
    AYCanaryActivationPrecheckDecision, AYCanaryAllowlist, AYCanaryAllowlistDecision,
    AYCanaryAllowlistKey, AYCanaryCandidate, AYCanaryCandidateMode, AYCanaryDecisionStatus,
    AYCanaryEquivalenceEvidence, AYCanaryExecutionObservation, AYCanaryFamily,
    AYCanaryGenerationFence, AYCanaryInvalidationState, AYCanaryLayoutProof,
    AYCanaryManifestBinding, AYCanaryParentGateEvidence, AYCanaryProductAdapterPrecheckDecision,
    AYCanaryProofDecision, AYCanaryRejectionReason, AYCanarySideEffects, AYCanaryTelemetryPacket,
    AYCanaryValidationProvenance, JIT_AY_CANARY_ALLOWLIST_SCHEMA,
    JIT_AY_CANARY_ALLOWLIST_SCHEMA_VERSION, evaluate_ay_canary_activation_precheck,
    evaluate_ay_canary_product_adapter_precheck,
};
pub use jit_cert::{JitCertificate, TrustIrPair};
pub use jit_contract::{
    KERNEL_ARTIFACT_CONTRACT_SCHEMA, KERNEL_ARTIFACT_CONTRACT_SCHEMA_VERSION,
    KernelArtifactContract, KernelArtifactKind, KernelStateDomain,
};
pub use jit_control_plane::{
    ControlPlaneCandidate, ControlPlaneConsumerAdmissionProductDecision, ControlPlaneDecision,
    ControlPlaneGateEvidence, ControlPlaneKillSwitch, ControlPlaneKillSwitchScope,
    ControlPlaneMode, ControlPlaneProductAdapterDecision,
    ControlPlaneProductAdapterTelemetryPacket, ControlPlaneProductCallStatus,
    ControlPlaneProductCallStatusRow, ControlPlanePublicationState, ControlPlaneReason,
    ControlPlaneRevocation, ControlPlaneRoute, ControlPlaneSideEffects,
    ControlPlaneTelemetryPacket, JIT_EVERYWHERE_CONTROL_PLANE_SCHEMA,
    JIT_EVERYWHERE_CONTROL_PLANE_SCHEMA_VERSION, JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA,
    JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA_VERSION, JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA,
    JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA_VERSION, JitEverywhereControlPlane,
    consumer_admission_with_control_plane, install_gate_deny_control_for_decision,
    install_gate_revalidation_with_control_plane,
    install_gate_revalidation_with_control_plane_current,
};
pub use jit_diagnostics::{
    JIT_CRASH_REPORT_SCHEMA, JIT_CRASH_REPORT_SCHEMA_VERSION, JIT_REPLAY_SCHEMA,
    JIT_REPLAY_SCHEMA_VERSION, JitCodeRange, JitCrashKind, JitCrashLocation,
    JitCrashReportMetadata, JitPcMapEntry, JitReplayReportMetadata, JitSymbolLabel,
    JitTrapStatusBlock, JitTrapStatusKind,
};
pub use jit_install_gate::{
    NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA,
    NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA_VERSION,
    NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA,
    NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA_VERSION, NATIVE_INSTALL_GATE_EVENT_SCHEMA,
    NATIVE_INSTALL_GATE_EVENT_SCHEMA_VERSION, NATIVE_INSTALL_GATE_PACKET_SCHEMA,
    NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION, NATIVE_INSTALL_GATE_REPLAY_SCHEMA,
    NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION, NATIVE_INSTALL_GATE_RUNTIME_TELEMETRY_SCHEMA,
    NATIVE_INSTALL_GATE_RUNTIME_TELEMETRY_SCHEMA_VERSION, NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA,
    NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION, NativeInstallGateAYLayoutAdapter,
    NativeInstallGateActions, NativeInstallGateAdmissionSummary, NativeInstallGateArtifactPacket,
    NativeInstallGateAuthority, NativeInstallGateConsumerAdmissionDecision,
    NativeInstallGateConsumerAdmissionEvidence, NativeInstallGateConsumerAdmissionTelemetryPacket,
    NativeInstallGateConsumerVerdictBinding, NativeInstallGateDenyControlPlane,
    NativeInstallGateDenyReason, NativeInstallGateDenyScope, NativeInstallGateDisposition,
    NativeInstallGateEventKind, NativeInstallGateEventSource, NativeInstallGateExpectedBindings,
    NativeInstallGateFreshnessObservation, NativeInstallGateFreshnessPacket,
    NativeInstallGateInput, NativeInstallGateLayoutAccess, NativeInstallGateLayoutEntryAbiEvidence,
    NativeInstallGateLayoutEvidence, NativeInstallGateLayoutRegionEvidence,
    NativeInstallGatePacket, NativeInstallGatePayloadIdentity, NativeInstallGateProofEvidence,
    NativeInstallGateRejectionCode, NativeInstallGateReplayBinding,
    NativeInstallGateReplayIdentity, NativeInstallGateRevalidationInput,
    NativeInstallGateRuntimeOutcome, NativeInstallGateRuntimeTelemetryPacket,
    NativeInstallGateSharedPrimitiveContractReason, NativeInstallGateStructuredEvent,
    NativeInstallGateSurface, NativeInstallGateTelemetryInput, NativeInstallGateTelemetryPacket,
    NativeInstallGateTyLayoutAdapter, NativeInstallGateValidationPacket, NativeInstallGateVerdict,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_BLOCKER_CODES,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_ID,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_DUPLICATE_KEY_PREFIX,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_MISMATCHED_KEY_PREFIX,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_MISMATCHED_REQUIRED_FIELD_KEY_PREFIX,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_MISSING_KEY_PREFIX,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_REASON_CODES,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_STALE_SCHEMA_KEY_PREFIX,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_VALIDATION_REASON_CODES,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_VALIDATION_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_VALIDATION_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_VALIDATION_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_UNEXPECTED_KEY_PREFIX,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_REQUIRED_FIELDS,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_REQUIRED_RUNTIME_EVIDENCE,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA, PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_CALLABLE_CONTRACT_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_CALLABLE_CONTRACT_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_CALLABLE_LIFETIME_PROOF_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_CALLABLE_LIFETIME_PROOF_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_BLOCKER_CODES,
    PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_REQUIRED_FIELDS,
    PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_STATUS_CODES, PETRI_NATIVE_SUCCESSOR_CONSUMER,
    PETRI_NATIVE_SUCCESSOR_CONSUMER_MODE, PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_EXECUTABLE_CALL_EVIDENCE_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTABLE_CALL_EVIDENCE_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_BLOCKER_CODES,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_VALIDATION_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_VALIDATION_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_ACCEPTED_REQUIRED_VALUE_KEYS,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_REQUIRED_KEYS,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_REASON_CODES,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REQUIRED_FIELDS,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_VALIDATION_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_VALIDATION_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_BLOCKER_CODES,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_REQUIRED_FIELDS,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_BLOCKER_CODES,
    PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_EVIDENCE_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_EVIDENCE_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_REQUIRED_FIELDS,
    PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_BLOCKER_CODES,
    PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_REQUIRED_FIELDS,
    PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_STATUS_CODES, PETRI_NATIVE_SUCCESSOR_KIND,
    PETRI_NATIVE_SUCCESSOR_MANIFEST_IDENTITY_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_MANIFEST_IDENTITY_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_BLOCKER_CODES,
    PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_REQUIRED_FIELDS,
    PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_ID,
    PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_VALIDATION_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_VALIDATION_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_REQUIRED_ROUTE_VALIDATORS,
    PETRI_NATIVE_SUCCESSOR_PRODUCTION_SELECTION_REASON_CODES,
    PETRI_NATIVE_SUCCESSOR_PRODUCTION_SELECTION_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_PRODUCTION_SELECTION_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_PRODUCTION_SELECTION_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_ABI_PROOF_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_ABI_PROOF_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_BLOCKER_CODES,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_REQUIRED_FIELDS,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_SCHEMA, PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_BLOCKER_CODES,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_REQUIRED_FIELDS,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_BLOCKER_CODES,
    PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_REQUIRED_FIELDS,
    PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_STATUS_CODES,
    PETRI_NATIVE_SUCCESSOR_SEMANTIC_FORMULA_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_STATE_ENCODING_STABLE_BYTES_V1,
    PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_ABI_STABLE_BYTES_V1,
    PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_TRUST_IR_BUNDLE_IDENTITY_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_ID,
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_VALIDATION_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_VALIDATION_SCHEMA_VERSION,
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_REQUIRED_SUMMARY_VALIDATORS,
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_CONTRACT_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR,
    PETRI_NATIVE_SUCCESSOR_VECTOR_CONSTANT_LOWERING_EVIDENCE_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_VECTOR_CONSTANT_LOWERING_EVIDENCE_SCHEMA_VERSION,
    PetriNativeSuccessorAdmissionExpected, PetriNativeSuccessorCallPacket,
    PetriNativeSuccessorCallPacketContractDescriptor,
    PetriNativeSuccessorCallPacketContractDescriptorRow,
    PetriNativeSuccessorCallPacketContractHealthReport,
    PetriNativeSuccessorCallPacketContractHealthStatus,
    PetriNativeSuccessorCallPacketContractHealthSummary,
    PetriNativeSuccessorCallPacketContractHealthSummaryValidationReport,
    PetriNativeSuccessorCallPacketContractHealthSummaryValidationStatus,
    PetriNativeSuccessorCallableContract, PetriNativeSuccessorCallableContractBlocker,
    PetriNativeSuccessorCallableLifetimeProof, PetriNativeSuccessorCallablePointer,
    PetriNativeSuccessorCompileArtifactHandoffBlocker,
    PetriNativeSuccessorCompileArtifactHandoffEvidence,
    PetriNativeSuccessorCompileArtifactHandoffInput,
    PetriNativeSuccessorDownstreamContractDescriptor,
    PetriNativeSuccessorEvidenceSurfaceDescriptor, PetriNativeSuccessorExecutableCallBlocker,
    PetriNativeSuccessorExecutableCallEvidence, PetriNativeSuccessorExecutableCallStatus,
    PetriNativeSuccessorExecutionAuthorityDecision,
    PetriNativeSuccessorExecutionAuthorityDiagnosticFixture,
    PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifest,
    PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestEntry,
    PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow,
    PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestValidationReport,
    PetriNativeSuccessorExecutionAuthorityInput,
    PetriNativeSuccessorExecutionAuthorityManifestValidationReport,
    PetriNativeSuccessorExecutionAuthorityManifestValidationStatus,
    PetriNativeSuccessorExecutionAuthorityReplayIdentity,
    PetriNativeSuccessorExecutionAuthorityStatus, PetriNativeSuccessorExecutionAuthoritySummary,
    PetriNativeSuccessorExecutionAuthoritySummaryRow,
    PetriNativeSuccessorExecutionAuthoritySummaryValidationReport,
    PetriNativeSuccessorExecutionAuthoritySummaryValidationStatus,
    PetriNativeSuccessorExecutionExpected, PetriNativeSuccessorExecutionPlan,
    PetriNativeSuccessorHandoffManifestRow, PetriNativeSuccessorHandoffManifestRowKind,
    PetriNativeSuccessorInstallBindingBlocker, PetriNativeSuccessorInstallBindingEvidence,
    PetriNativeSuccessorManifestIdentity, PetriNativeSuccessorManifestIdentityBlocker,
    PetriNativeSuccessorManifestIdentitySource, PetriNativeSuccessorMockExecutableCallBlocker,
    PetriNativeSuccessorMockExecutableCallGate, PetriNativeSuccessorMockExecutableCallReport,
    PetriNativeSuccessorMockExecutableCallStatus, PetriNativeSuccessorProducerBridgeDescriptor,
    PetriNativeSuccessorProducerBridgeDescriptorRow,
    PetriNativeSuccessorProducerBridgeDescriptorValidationReport,
    PetriNativeSuccessorProducerBridgeDescriptorValidationStatus,
    PetriNativeSuccessorProductionSelectionDecision, PetriNativeSuccessorProductionSelectionStatus,
    PetriNativeSuccessorRuntimeAbiProof, PetriNativeSuccessorRuntimeCallBlocker,
    PetriNativeSuccessorRuntimeCallReport, PetriNativeSuccessorRuntimeCallStatus,
    PetriNativeSuccessorRuntimeCallableEntrypoint, PetriNativeSuccessorRuntimeCallableFn,
    PetriNativeSuccessorRuntimeReadinessBlocker, PetriNativeSuccessorRuntimeReadinessPacket,
    PetriNativeSuccessorRuntimeReadinessStatus, PetriNativeSuccessorSemanticBridgeBlocker,
    PetriNativeSuccessorSemanticBridgeEvidence, PetriNativeSuccessorSemanticBridgeExpected,
    PetriNativeSuccessorTrampolineContract, PetriNativeSuccessorTrustMcAdmissionRouteDescriptor,
    PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow,
    PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationReport,
    PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationStatus,
    native_install_gate_consumer_admission,
    native_install_gate_consumer_admission_structured_event,
    native_install_gate_consumer_allowlist_key, native_install_gate_packet_hash,
    native_install_gate_runtime_structured_event, native_install_gate_runtime_telemetry,
    native_install_gate_shadow_mismatch_event, native_install_gate_structured_event,
    persist_native_install_gate_packet_bindings,
    petri_native_successor_admission_from_trust_ir_bundle,
    petri_native_successor_call_packet_contract_descriptor,
    petri_native_successor_call_packet_from_trust_ir_bundle,
    petri_native_successor_call_runtime_entrypoint,
    petri_native_successor_compile_artifact_handoff_evidence,
    petri_native_successor_downstream_contract_descriptor,
    petri_native_successor_executable_call_evidence,
    petri_native_successor_execution_authority_decision,
    petri_native_successor_execution_authority_diagnostic_fixture_manifest,
    petri_native_successor_execution_authority_healthy_diagnostic_fixture,
    petri_native_successor_execution_authority_incomplete_diagnostic_fixture,
    petri_native_successor_execution_authority_replay_identity_for_manifest_key_value_lines,
    petri_native_successor_execution_authority_replay_identity_for_manifest_rows,
    petri_native_successor_execution_authority_stale_diagnostic_fixture,
    petri_native_successor_execution_authority_summary_for_manifest_key_value_lines,
    petri_native_successor_execution_authority_summary_for_manifest_rows,
    petri_native_successor_execution_plan_from_trust_ir_bundle,
    petri_native_successor_install_binding_evidence,
    petri_native_successor_install_packet_from_trust_ir_bundle,
    petri_native_successor_manifest_identity, petri_native_successor_mock_executable_call_dry_run,
    petri_native_successor_producer_bridge_descriptor,
    petri_native_successor_production_selection_decision,
    petri_native_successor_runtime_readiness_packet,
    petri_native_successor_semantic_bridge_evidence_from_trust_ir_bundle,
    petri_native_successor_semantic_bridge_evidence_from_trust_ir_bundle_with_artifact_attachments,
    petri_native_successor_trampoline_contract,
    petri_native_successor_trust_ir_bundle_identity_descriptor,
    petri_native_successor_trust_ir_shared_primitive_contract_manifest_key_value_lines,
    petri_native_successor_trust_ir_shared_primitive_contract_manifest_row_count,
    petri_native_successor_trust_ir_shared_primitive_contract_manifest_sha256,
    petri_native_successor_trust_mc_admission_route_descriptor,
    petri_native_successor_trust_mc_admission_route_readiness_identity_sha256,
    petri_native_successor_trust_mc_chc_contract_descriptor,
    petri_native_successor_trust_mc_chc_shared_primitive_contract_descriptor,
    validate_native_install_gate, validate_native_install_gate_packet,
    validate_native_install_gate_packet_with_current, validate_native_install_gate_verdict,
    validate_petri_native_successor_call_packet_contract_descriptor_key_value_lines,
    validate_petri_native_successor_call_packet_contract_descriptor_rows,
    validate_petri_native_successor_call_packet_contract_health_summary_key_value_lines,
    validate_petri_native_successor_call_packet_contract_health_summary_rows,
    validate_petri_native_successor_execution_authority_diagnostic_fixture_manifest_key_value_lines,
    validate_petri_native_successor_execution_authority_diagnostic_fixture_manifest_rows,
    validate_petri_native_successor_execution_authority_manifest_key_value_lines,
    validate_petri_native_successor_execution_authority_manifest_rows,
    validate_petri_native_successor_execution_authority_summary_json_str,
    validate_petri_native_successor_execution_authority_summary_json_value,
    validate_petri_native_successor_execution_authority_summary_key_value_lines,
    validate_petri_native_successor_execution_authority_summary_rows,
    validate_petri_native_successor_execution_authority_summary_text,
    validate_petri_native_successor_producer_bridge_descriptor_key_value_lines,
    validate_petri_native_successor_producer_bridge_descriptor_rows,
    validate_petri_native_successor_trust_mc_admission_route_descriptor_json_str,
    validate_petri_native_successor_trust_mc_admission_route_descriptor_json_value,
    validate_petri_native_successor_trust_mc_admission_route_descriptor_key_value_lines,
    validate_petri_native_successor_trust_mc_admission_route_descriptor_rows,
    validate_petri_native_successor_trust_mc_admission_route_descriptor_text,
};
pub use jit_nomination::{
    CandidateId, CandidateRegionKind, JIT_EVERYWHERE_NOMINATION_SCHEMA,
    JIT_EVERYWHERE_NOMINATION_SCHEMA_VERSION, NominationDisposition, NominationInput,
    NominationRecord, NominationRejectionReason, NominationSideEffects, NominationStructuralSignal,
    nominate_jit_everywhere_candidate,
};
pub use jit_profile_cache::{
    JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA, JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA_VERSION,
    ProfileCacheCallableLookup, ProfileCacheCostData, ProfileCacheEntry,
    ProfileCacheInstallRejection, ProfileCacheKey, ProfileCacheOutcome,
    ProfileCacheProofDiagnostic, ProfileCacheReplayReference, ProfileCacheSideEffects,
    ProfileOnlyArtifactMetadata, ProfileOnlySpeculativeCache,
};
pub use jit_shadow_replay::{
    JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA, JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA_VERSION,
    ShadowReplayAYChecks, ShadowReplayBundle, ShadowReplayCompilerConfig, ShadowReplayConsumer,
    ShadowReplayDecision, ShadowReplayEvidenceReference, ShadowReplayGenerationFacts,
    ShadowReplayHook, ShadowReplayInputSlice, ShadowReplayObservation, ShadowReplayOutcome,
    ShadowReplaySideEffects, ShadowReplayStatus, ShadowReplayTyChecks, compare_shadow_replay,
};
pub use jit_ty_canary_allowlist::{
    JIT_TY_CANARY_ALLOWLIST_SCHEMA, JIT_TY_CANARY_ALLOWLIST_SCHEMA_VERSION,
    TyCanaryActivationPrecheckDecision, TyCanaryAllowlist, TyCanaryAllowlistDecision,
    TyCanaryAllowlistKey, TyCanaryCandidate, TyCanaryCandidateMode, TyCanaryDecisionStatus,
    TyCanaryEquivalenceEvidence, TyCanaryExecutionObservation, TyCanaryFamily,
    TyCanaryGenerationTuple, TyCanaryInvalidationState, TyCanaryLayoutProof,
    TyCanaryManifestBinding, TyCanaryParentGateEvidence, TyCanaryProductAdapterPrecheckDecision,
    TyCanaryProofDecision, TyCanaryRejectionReason, TyCanarySideEffects, TyCanaryTelemetryPacket,
    TyCanaryValidationProvenance, evaluate_ty_canary_activation_precheck,
    evaluate_ty_canary_product_adapter_precheck,
};
pub use lower::LowerError;
pub use metal_emitter::{MetalEmitError, MetalOutput, NamedKernel, emit_metal_kernels};
pub use pgo_runner::{
    DEFAULT_I64_PROFILE_INPUTS, DEFAULT_TY_PARENT_PROFILE_INPUTS, HOST_JIT_PGO_CAPTURE_FIELDS,
    HOST_JIT_PGO_ENTRY_SHAPE_CODES, HOST_JIT_PGO_PROFILE_AUTHORITY_FIELDS,
    HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_ROW_KEYS, HOST_JIT_PGO_PROFILE_AUTHORITY_REASON_CODES,
    HOST_JIT_PGO_PROFILE_AUTHORITY_STATUS_CODES, HOST_JIT_PGO_PROFILE_KEY_FIELDS,
    HOST_JIT_PGO_PROFILE_USE_FIELDS, HOST_JIT_PGO_PROFILE_USE_PASS_PROFILE_USE,
    HOST_JIT_PGO_PROFILE_USE_REASON_CODES, HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_BELOW_O2,
    HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_ENABLES, HOST_JIT_PGO_PROFILE_USE_SOUNDNESS_FIELDS,
    HOST_JIT_PGO_PROVENANCE_DESCRIPTOR, HOST_JIT_PGO_RUNNER_ERROR_REASON_CODES,
    HostJitPgoCaptureReport, HostJitPgoEntry, HostJitPgoEntryShape, HostJitPgoGenerateReport,
    HostJitPgoGenerateResult, HostJitPgoInputWindow, HostJitPgoObservation,
    HostJitPgoProfileAuthorityEvidence, HostJitPgoProfileAuthorityManifestRow,
    HostJitPgoProfileAuthorityManifestRowKind, HostJitPgoProfileAuthorityReason,
    HostJitPgoProfileAuthorityStatus, HostJitPgoProvenanceDescriptor, HostJitPgoRunnerError,
    HostJitPgoUseReport, HostJitPgoUseResult, ProfileCounterSummary, ProfileFileReport,
    ProfileReportKey, ProfileUseHotnessSummary, ProfileUseReport,
    TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA,
    TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA_VERSION,
    TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA,
    TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA_VERSION,
    TRUST_CG_HOST_JIT_PGO_PROVENANCE_DESCRIPTOR_SCHEMA,
    TRUST_CG_HOST_JIT_PGO_PROVENANCE_DESCRIPTOR_SCHEMA_VERSION, TRUST_CG_PROFILE_REPORT_SCHEMA_V1,
    TY_PARENT_SUMMARY_SLOTS, TyParentLoopSummary, compile_host_jit_with_profile_use,
    compile_host_jit_with_profile_use_and_symbols, host_jit_pgo_provenance_descriptor,
    pgo_cache_key, pgo_opt_level_name, pgo_opt_level_num, pgo_target_cpu, pgo_target_features,
    pgo_target_triple, profile_use_enables_optimization, run_host_jit_pgo,
    run_host_jit_pgo_with_symbols,
};
pub use pipeline::{
    CoreMLOutput, DispatchVerifyMode, FormatMode, InputFormat, PhaseTimings, Pipeline,
    PipelineConfig, PipelineError, PreparationMetrics, ProofOptimizationCertificateCitation,
    ProofOptimizationConsumedFactCitation, compile_to_object, detect_input_format,
    emit_coreml_program, generate_cpu_only_plan, generate_lsda_for_function, load_module,
    load_module_as, load_module_from_bytes,
};
pub use relax::{BranchRelaxation, RelaxError, RelaxedCode};
pub use rewrite_admission::{
    ProofGuidedAdmissionEvidence, REWRITE_ADMISSION_RECORD_SCHEMA,
    REWRITE_ADMISSION_RECORD_SCHEMA_VERSION, RewriteAdmissionDisposition, RewriteAdmissionRecord,
    RewriteAdmissionRejection,
};
pub use target::{CallingConvention, Target};
pub use ty_reducer_evidence::{
    TY_REDUCER_EVIDENCE_PACKET_SCHEMA, TY_REDUCER_EVIDENCE_PACKET_SCHEMA_VERSION,
    TyReducerCallbackObservation, TyReducerEvidencePacket, TyReducerEvidenceRow,
    TyReducerEvidenceStatus,
};
