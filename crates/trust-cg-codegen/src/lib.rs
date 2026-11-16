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
pub mod aarch64_dispatch;
pub mod aot_frame_inputs;
pub mod apple_deployment;
pub mod async_compile_service;
pub mod ay_lra_proof_manifest;
pub mod ay_pb_pbo_checked_arithmetic_contract;
pub mod ay_sat_bcp_contract;
pub mod ay_sat_helper_replacement_contract;
pub mod branch_forward;
pub mod coff;
pub mod compile_artifact_cache_profile;
pub mod compile_policy;
pub mod compile_service;
pub mod compiler;
pub mod composed_transition;
pub mod constant_pool;
pub mod core_admission;
pub mod coreml_emitter;
pub mod debug_provenance;
pub mod decode_check;
pub mod dialect_legalization;
pub mod dialect_pipeline;
pub mod dwarf_cfi;
pub mod dwarf_cfi_decode_check;
pub mod dwarf_info;
pub mod elf;
pub mod post_index_late;
pub use trust_cg_process_env as env_lock;
pub use trust_cg_process_env::{
    ARTIFACT_REUSE_ENV_EXEMPT_KEYS, ArtifactReuseEnvironmentSafety, ArtifactReusePermit,
    COMPILER_CONTROL_ENV_PREFIXES, artifact_reuse_environment_safety,
    artifact_reuse_environment_safety_from, artifact_reuse_permit,
};
mod aot_profile;
pub mod error;
pub mod exception_handling;
pub mod frame;
pub mod global_stub;
pub mod guard_ledger;
pub mod ingest;
pub mod interpreter;
pub mod jit;
pub mod jit_ay_canary_allowlist;
pub mod jit_cert;
pub mod jit_contract;
pub mod jit_control_plane;
pub mod jit_diagnostics;
pub mod jit_install_gate;
pub mod jit_nomination;
pub mod jit_page_witness;
pub mod jit_profile_cache;
pub mod jit_release;
pub mod jit_shadow_replay;
pub mod jit_ty_canary_allowlist;
pub mod jit_unwind;
pub mod layout;
#[cfg(test)]
#[path = "../../test_support/legacy_module_capture.rs"]
mod legacy_module_capture;
pub mod link_driver;
pub mod lir_module_prep;
pub mod llsc;
pub mod loop_align;
pub mod lower;
pub mod macho;
pub mod metal_emitter;
pub mod module_merge;
pub mod object_sections;
mod stack_resources;
pub use stack_resources::StaticStackFrameReport;
#[cfg(test)]
#[path = "../../trust-cg-lower/src/source_scan.rs"]
mod source_scan;
pub use aot_profile::AotProfileError;
mod aarch64_prepared_dump;
pub mod pgo_runner;
pub mod pipeline;
pub use aarch64_prepared_dump::set_directory as set_aarch64_prepared_dump_directory;
pub mod post_ra_value_flow;
pub mod proof_evidence;
pub mod relax;
pub mod resource_limits;
pub mod rewrite_admission;
pub mod riscv;
pub mod runtime_deps;
pub mod strict_adapter;
pub mod target;
pub mod tier_up;
pub mod trust_ir_bitfield_builder;
pub mod ty_reducer_evidence;
pub mod unwind;
pub mod wasm;
pub mod x86_64;

pub use async_compile_service::{
    AsyncCompilePlanTicket, AsyncCompilePoll, AsyncCompileService, AsyncCompileServiceConfig,
    AsyncCompileState, AsyncCompileTicket, AsyncSubmitAccepted, AsyncSubmitReject,
    AsyncSubmitRejectCode,
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
pub use compile_policy::{
    COMPILE_POLICY_SCHEMA, COMPILE_POLICY_SCHEMA_VERSION, CompilePolicy, CompilePolicyDigest,
    CompilePolicyDigests, CompilePolicyError, CompilePolicyPartition, CompilePolicyScope,
    MAX_COMPILE_POLICY_ENCODING_BYTES,
};
pub use compile_service::{
    ArtifactIdentity, ArtifactIdentityInput, ArtifactKind, ArtifactManifestReference,
    ArtifactMetadata, ArtifactPayload, ArtifactProvenance, CancellationToken, CompileDiagnostic,
    CompileGeneration, CompileGenerationFence, CompilePlan, CompileProfile, CompileProfileId,
    CompileRequest, CompileRequestId, CompileResponse, CompileService, CompileServiceConfig,
    CompileStatus, CompiledArtifact, CounterSummary, DiagnosticSeverity, EntryPointMetadata,
    ExecutableArtifactPayload, ExpandedCompileProfile, FunctionArtifactMetadata, InstallIntent,
    InstallMetadata, InstallProofSummary, InstalledArtifact, ObjectArtifactPayload,
    ProofInstallTelemetrySummary, RawExternBinding, SourceKind,
};
#[cfg(feature = "verify")]
pub use compiler::CoreNativeAggregateSourceEvents;
#[cfg(feature = "verify")]
pub use compiler::CoreNativeAggregateTargetEvents;
pub use compiler::{
    CompilationMetrics, CompilationResult, CompileError, Compiler, CompilerConfig,
    CompilerTargetSelection, CompilerTrace, CompilerTraceLevel, CoreAddressFreeFixup,
    CoreAddressFreeFixupInventory, CoreAddressFreeFixupTarget, CoreAddressFreeMachineArtifact,
    CoreAddressFreeMachineCompilationError, CoreAddressFreeMachineCompilationFailure,
    CoreAddressFreeMachineIdentity, CoreAggregateResultFunction, CoreAggregateResultTransportError,
    CoreAggregateResultTransports, CoreJitCompilationPlan, CoreJitEffectiveOptions,
    CoreJitFastRegallocSelection, CoreJitPlanIdentity, CoreJitPlanningError,
    CoreJitPlanningFailure, CoreJitProofGradeQualificationError,
    CoreJitProofGradeQualificationFailure, FunctionQualityMetrics, JitCompilationResult,
    PolicyQualifiedCoreJitCompilationPlan, ProofCertificate, TargetSelectionOrigin,
};
#[cfg(feature = "verify")]
pub use compiler::{CoreRejectedFrameContext, CoreRejectedFrameError};
pub use core_admission::{
    CORE_DECLARED_IMPORT_MANIFEST_SCHEMA, CORE_DECLARED_IMPORT_MANIFEST_SCHEMA_VERSION,
    CORE_LIR_NATIVE_DEPENDENCY_BINDINGS_SCHEMA, CORE_LIR_NATIVE_DEPENDENCY_BINDINGS_SCHEMA_VERSION,
    CORE_NATIVE_DEPENDENCY_REFERENCE_MAP_SCHEMA,
    CORE_NATIVE_DEPENDENCY_REFERENCE_MAP_SCHEMA_VERSION, CORE_NATIVE_RUNTIME_CATALOG_SCHEMA,
    CORE_NATIVE_RUNTIME_CATALOG_SCHEMA_VERSION, CORE_TARGET_CONTRACT_SCHEMA,
    CORE_TARGET_CONTRACT_SCHEMA_VERSION, CoreAdmissionError, CoreAdmissionFailure,
    CoreAdmittedModule, CoreArenaCensus, CoreConsumptionIntegrityError, CoreDeclaredImportManifest,
    CoreDeclaredImportManifestError, CoreExecutableSurface, CoreHostDeterminism,
    CoreHostFunctionEffects, CoreHostFunctionImport, CoreHostGlobalImport, CoreHostImport,
    CoreHostJitMachineProfile, CoreHostJitTarget, CoreHostMemoryEffect, CoreJitPlanIntegrityError,
    CoreLirNativeDependencyBinding, CoreLirNativeDependencyBindingCoverage,
    CoreLirNativeDependencyBindingError, CoreLirNativeDependencyBindings, CoreModuleClosureError,
    CoreNativeDependencyOrigin, CoreNativeDependencyReference,
    CoreNativeDependencyReferenceCoverage, CoreNativeDependencyReferenceMap,
    CoreNativeDependencyReferenceMapError, CoreNativeRuntimeCatalog,
    CoreNativeRuntimeCatalogCoverage, CoreNativeRuntimeCatalogError, CoreNativeRuntimeEntry,
    CorePermittedNativeMode, CoreProofCensus, CoreRuntimeIdentity, CoreSharedAdmissionFailure,
    CoreTargetContract, CoreTargetContractError, CoreTrustedEvidenceOccurrence,
    IDENTITY_CORE_POLICY_SCHEMA, IDENTITY_CORE_POLICY_SCHEMA_VERSION, IdentityCorePolicy,
    IdentityTransformReceipt, admit_identity_core_module_for_host_jit,
    try_admit_identity_core_module_for_host_jit,
    try_admit_shared_identity_core_module_for_host_jit,
};
pub use error::{CodegenError, TrustCgError};
pub use lir_module_prep::{
    AdmittedInlineOnlyBodies, INLINE_ONLY_BODIES_KILL_SWITCH, InlineOnlyAdmission,
    InlineOnlyAuthentication, InlineOnlyAuthority, InlineOnlyBodyEvidence,
    JIT_LIR_PREPARE_KILL_SWITCH, JitExternBindings, LirModulePreparation, admit_inline_only_bodies,
    admit_inline_only_bodies_with_authority, jit_interposable_definitions, prepare_jit_lir_module,
    prepare_jit_lir_module_with_authority, unvalidated_lir_passes_run,
};
pub use tier_up::{
    ServiceTierBackend, TIER_UP_MAX_TIERS, TIER_UP_REPORT_SCHEMA, TierBackend, TierEntryError,
    TierEntryTable, TierExport, TierFailure, TierInstall, TierInstaller, TierOutcome, TierOutput,
    TierPlan, TierPlanError, TierRecord, TierRefusal, TierRequest, TierStartFailure, TierUpPoll,
    TierUpReport, TierUpSession,
};
// trust-ir v41 codegen license: the adapter decides it, the compiler, service and
// CLI configure it, so the policy vocabulary is reachable from this crate root.
pub use interpreter::{
    InterpreterConfig, InterpreterError, InterpreterValue, interpret, interpret_with_config,
};
pub use jit::{
    ExecutableBuffer, JitCompiler, JitConfig, JitError, JitExternalSymbolResolutionPolicy,
    ProfileHookMode, ProfileStats, ensure_jit_execute_mode,
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
    HOST_JIT_SELECTED_CODEGEN_AUTHORITY_SCOPE, HOST_JIT_SELECTED_CODEGEN_EVIDENCE_BASIS,
    HOST_JIT_SELECTED_CODEGEN_FEATURE_DOMAIN, HOST_JIT_SELECTED_CODEGEN_PROFILE_SCHEMA,
    HOST_JIT_SELECTED_CODEGEN_PROFILE_SCHEMA_VERSION, HOST_JIT_SELECTED_CODEGEN_SELECTION_POLICY,
    HostJitSelectedCodegenProfile, HostJitSelectedCodegenProfileError,
    KERNEL_ARTIFACT_CONTRACT_SCHEMA, KERNEL_ARTIFACT_CONTRACT_SCHEMA_VERSION,
    KernelArtifactContract, KernelArtifactKind, KernelStateDomain,
    X86_64_DETECTED_HOST_FEATURE_DOMAIN,
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
    compile_host_jit_with_profile_use_and_symbols,
    compile_host_jit_with_profile_use_and_symbols_and_license, host_jit_pgo_provenance_descriptor,
    pgo_cache_key, pgo_opt_level_name, pgo_opt_level_num, pgo_target_cpu, pgo_target_features,
    pgo_target_triple, profile_use_enables_optimization, run_host_jit_pgo,
    run_host_jit_pgo_with_symbols, run_host_jit_pgo_with_symbols_and_license,
};
pub use pipeline::{
    AArch64ModuleEmission, CegisPassRun, CegisPassStats, CegisRunOutcome, CheckedAarch64Function,
    CheckedAarch64Functions, CoreMLOutput, DispatchVerifyMode, FormatMode, InputFormat,
    PhaseTimings, Pipeline, PipelineConfig, PipelineError, PreparationMetrics,
    ProofOptimizationCertificateCitation, ProofOptimizationConsumedFactCitation, compile_to_object,
    decode_binary, detect_input_format, emit_coreml_program, generate_cpu_only_plan,
    generate_lsda_for_function, load_module, load_module_as, load_module_from_bytes,
};
pub use relax::{BranchRelaxation, RelaxError, RelaxedCode};
pub use rewrite_admission::{
    ProofGuidedAdmissionEvidence, REWRITE_ADMISSION_RECORD_SCHEMA,
    REWRITE_ADMISSION_RECORD_SCHEMA_VERSION, RewriteAdmissionDisposition, RewriteAdmissionRecord,
    RewriteAdmissionRejection,
};
pub use strict_adapter::{
    StrictCoreAdapterError, StrictCoreAdapterResult, StrictCoreAdapterTarget,
    StrictCoreObjectFormat, translate_core_module_for_target_with_validation,
};
pub use target::{
    AArch64IsaFeature, AArch64IsaProfile, AArch64MachineCodeEvidence, AArch64TargetMachine,
    AdmittedTargetFeatures, CallingConvention, OutputTargetFeatures, RiscVIsaFeature, Target,
    TargetFeature, TargetFeatureSet, TargetFeatureSetError, TargetIdentity, TargetMachine,
    TargetMachineError, host_has_aarch64_dotprod, host_has_aarch64_fp16, host_has_aarch64_lse,
};
pub use trust_cg_ir::NativeDependencyId;
// The JIT's rule for an explicit `Global.section`, for every JIT lane: the
// compiler's JIT entry and a consumer's own JIT lane assembled from trust-cg
// parts call the same function.
pub use object_sections::refuse_jit_object_sections;
pub use trust_cg_lower::{
    AuthenticatedImportSet, CLEAN_KERNEL_TV_AUTHORITY, CodegenLicensePolicy, DefinitionBinding,
    LinkedDependency, LinkedImportRefusal, MUTATION_KNOBS, RelocationModel, SymbolBinding,
    UnlicensedBodyPolicy, UnlicensedPermitException, authenticate_linked_imports,
    definition_is_link_replaceable,
};
// The x86 vectorizer's tracked trace/opt-out settings, re-exported so an
// embedder that depends only on this crate (the rustc bridge) can forward its
// `-Ztrust-ir-cg-args` knobs without a direct `trust-cg-opt` dependency. Under
// trustc the passes' `TCG_*` environment fallbacks are refused before the
// backend loads, so these setters are the only channel that reaches them.
pub use loop_align::set_a64_loop_head_align_enabled;
pub use pipeline::set_x86_spill_reload_cse_xblock_enabled;
pub use trust_cg_lower::x86_64_isel::set_x86_jump_table_disabled;
pub use trust_cg_opt::and_cmp_fuse::set_and_cmp_fuse_rr_enabled;
pub use trust_cg_opt::loop_unroll::set_const_addr_unroll_disabled;
pub use trust_cg_opt::loop_unroll::set_partial_unroll_disabled;
pub use trust_cg_opt::loop_unroll::set_runtime_partial_unroll_enabled;
pub use trust_cg_opt::x86_block_merge::set_block_merge_disabled as set_x86_block_merge_disabled;
pub use trust_cg_opt::x86_bounds_check_elim::set_bce_carrier_enabled as set_x86_bce_carrier_enabled;
pub use trust_cg_opt::x86_bounds_check_elim::set_bce_disabled as set_x86_bce_disabled;
pub use trust_cg_opt::x86_bounds_check_elim::set_bce_early_copy_disabled as set_x86_bce_early_copy_disabled;
pub use trust_cg_opt::x86_bounds_check_elim::set_bce_pointer_reload_enabled as set_x86_bce_pointer_reload_enabled;
pub use trust_cg_opt::x86_bounds_check_elim::set_bce_reload_disabled as set_x86_bce_reload_disabled;
pub use trust_cg_opt::x86_bounds_check_elim::set_bce_trace_enabled as set_x86_bce_trace_enabled;
pub use trust_cg_opt::x86_copy_prop::set_alu_barrier_rewrite_enabled as set_x86_copyprop_alu_enabled;
pub use trust_cg_opt::x86_cse::set_cse_load_transparent_enabled as set_x86_cse_load_transparent_enabled;
pub use trust_cg_opt::x86_latch_dup::set_x86_latch_dup_enabled;
pub use trust_cg_opt::x86_latch_dup::set_x86_latch_dup_max_insts;
pub use trust_cg_opt::x86_latch_dup::set_x86_latch_dup_trace_enabled;
pub use trust_cg_opt::x86_licm::set_guarded_hoist_enabled as set_x86_licm_guarded_hoist_enabled;
pub use trust_cg_opt::x86_licm::set_licm_disabled as set_x86_licm_disabled;
pub use trust_cg_opt::x86_licm::set_outer_iv_invariance_enabled as set_x86_licm_outer_iv_enabled;
pub use trust_cg_opt::x86_licm::set_pointer_base_loads_disabled as set_x86_licm_pointer_base_loads_disabled;
pub use trust_cg_opt::x86_licm::set_pure_call_hoist_disabled as set_x86_pure_call_hoist_disabled;
pub use trust_cg_opt::x86_loop_simplify::set_x86_loop_simplify_enabled;
pub use trust_cg_opt::x86_loop_simplify::set_x86_loop_simplify_trace_enabled;
pub use trust_cg_opt::x86_loop_top::set_x86_loop_top_enabled;
pub use trust_cg_opt::x86_loop_top::set_x86_loop_top_trace_enabled;
pub use trust_cg_opt::x86_loop_top::x86_loop_top_registered;
pub use trust_cg_opt::x86_loop_unroll::set_loop_unroll_disabled as set_x86_loop_unroll_disabled;
pub use trust_cg_opt::x86_peephole::set_add_fuse_disabled as set_x86_add_fuse_disabled;
pub use trust_cg_opt::x86_peephole::set_latch_advance_window_enabled as set_x86_latch_advance_window_enabled;
pub use trust_cg_opt::x86_peephole::set_lea_writeback_disabled as set_x86_lea_writeback_disabled;
pub use trust_cg_opt::x86_peephole::set_peephole_entry_trace_enabled as set_x86_peephole_entry_trace_enabled;
pub use trust_cg_opt::x86_peephole::set_rmw_fuse_disabled as set_x86_rmw_fuse_disabled;
pub use trust_cg_opt::x86_peephole::set_rmw_fuse_sdef_disabled as set_x86_rmw_fuse_sdef_disabled;
pub use trust_cg_opt::x86_peephole::set_rmw_fuse_trace_enabled;
pub use trust_cg_opt::x86_peephole::set_sib_crossblock_flags_disabled as set_x86_sib_crossblock_flags_disabled;
pub use trust_cg_opt::x86_peephole::set_sib_scale1_fold_disabled as set_x86_sib_scale1_fold_disabled;
pub use trust_cg_opt::x86_peephole::set_test_elide_enabled as set_x86_test_elide_enabled;
pub use trust_cg_opt::x86_rotate::set_loop_rotate_disabled as set_x86_loop_rotate_disabled;
pub use trust_cg_opt::x86_slot_forward::set_slot_forward_disabled as set_x86_slot_forward_disabled;
pub use trust_cg_opt::x86_slot_forward::set_slot_forward_trace_enabled as set_x86_slot_forward_trace_enabled;
pub use trust_cg_opt::x86_sroa::set_sroa_multi_block_enabled as set_x86_sroa_multi_block_enabled;
pub use trust_cg_opt::x86_sroa::set_trace_enabled as set_x86_sroa_trace_enabled;
pub use trust_cg_opt::x86_strength_reduce::set_flag_safe_seed_enabled as set_x86_sr_flag_safe_seed_enabled;
pub use trust_cg_opt::x86_strength_reduce::set_strength_reduce_disabled as set_x86_strength_reduce_disabled;
pub use trust_cg_opt::x86_strength_reduce::set_strength_reduce_trace_enabled as set_x86_strength_reduce_trace_enabled;
pub use trust_cg_opt::x86_two_addr_expand::set_commute_enabled as set_x86_twoaddr_commute_enabled;
pub use trust_cg_opt::x86_two_addr_expand::set_expand_all_enabled as set_x86_twoaddr_expand_all_enabled;
pub use trust_cg_opt::x86_two_addr_expand::set_register_enabled as set_x86_twoaddr_expand_enabled;
pub use trust_cg_opt::x86_vectorize::set_bound_remat_disabled as set_x86_vec_bound_remat_disabled;
pub use trust_cg_opt::x86_vectorize::set_regarg_disabled as set_x86_vec_regarg_disabled;
pub use trust_cg_opt::x86_vectorize::set_regarg_unroll_k as set_x86_vec_unroll_k;
pub use trust_cg_opt::x86_vectorize::set_saxpyq_scalar_mul_enabled as set_x86_saxpyq_scalar_mul_enabled;
pub use trust_cg_opt::x86_vectorize::set_vec_ownlen_reload_disabled as set_x86_vec_ownlen_reload_disabled;
pub use trust_cg_opt::x86_vectorize::set_x86_rowreg_gpr_accumulators;
pub use trust_cg_opt::x86_vectorize::set_x86_rowreg_memory_rmw_disabled;
pub use trust_cg_opt::x86_vectorize::set_x86_rowreg_packed_mul_enabled;
pub use trust_cg_opt::x86_vectorize::x86_rowreg_memory_rmw_withheld;
pub use trust_cg_opt::x86_vectorize::{
    set_bail_trace_enabled as set_x86_vectorize_bail_trace_enabled,
    set_const_bound_disabled as set_x86_vectorize_const_bound_disabled,
    set_fill_memset_disabled as set_x86_fill_memset_disabled,
    set_late_run_enabled as set_x86_vectorize_late_enabled,
    set_post_sroa_run_disabled as set_x86_vectorize_post_sroa_disabled,
    set_raise_sink_disabled as set_x86_vectorize_raise_sink_disabled,
    set_trace_dump_enabled as set_x86_vectorize_trace_dump_enabled,
    set_trace_enabled as set_x86_vectorize_trace_enabled,
    set_zero_remainder_disabled as set_x86_vec_zero_remainder_disabled,
};
pub use trust_cg_opt::x86_vectorize::{
    set_x86_sumq_register_seed_disabled, x86_sumq_register_seed_withheld,
};
pub use trust_cg_opt::x86_xorshift_demanded_bits::set_x86_xorshift_demanded_bits_disabled;
pub use trust_cg_opt::x86_xorshift_demanded_bits::set_x86_xorshift_demanded_bits_trace_enabled;
pub use trust_cg_opt::{set_x86_select_flag_fusion_disabled, x86_select_flag_fusion_withheld};
pub use ty_reducer_evidence::{
    TY_REDUCER_EVIDENCE_PACKET_SCHEMA, TY_REDUCER_EVIDENCE_PACKET_SCHEMA_VERSION,
    TyReducerCallbackObservation, TyReducerEvidencePacket, TyReducerEvidenceRow,
    TyReducerEvidenceStatus,
};
pub use x86_64::pipeline::set_branch_layout_fallthrough_enabled as set_x86_branch_layout_fallthrough_enabled;
pub use x86_64::pipeline::set_jcc_align_disabled as set_x86_jcc_align_disabled;
pub use x86_64::pipeline::set_vectorize_disabled as set_x86_vectorize_disabled;
pub use x86_64::pipeline::set_x86_branch_layout_disabled;
pub use x86_64::pipeline::set_x86_cmov_swap_disabled;
pub use x86_64::pipeline::set_x86_cold_arm_sink_enabled;
pub use x86_64::pipeline::set_x86_cold_trap_layout_disabled;
pub use x86_64::pipeline::set_x86_if_convert_disabled;
pub use x86_64::pipeline::set_x86_lea_writeback_collapse_enabled;
pub use x86_64::pipeline::set_x86_licm_loads_disabled;
pub use x86_64::pipeline::set_x86_loop_align_log_enabled;
pub use x86_64::pipeline::set_x86_loop_align_max_body;
pub use x86_64::pipeline::set_x86_loop_align_max_skip;
pub use x86_64::pipeline::set_x86_loop_align_relocate_contained;
pub use x86_64::pipeline::set_x86_loop_align_seam_pad;
pub use x86_64::pipeline::set_x86_loop_exit_layout_disabled;
pub use x86_64::pipeline::set_x86_loop_head_align_disabled;
pub use x86_64::pipeline::set_x86_reload_elide_disabled;
pub use x86_64::pipeline::set_x86_sroa_disabled;
pub use x86_64::pipeline::x86_loop_align_relocate_contained_withheld;
pub use x86_64::pipeline::{
    X86AllocationQuality, set_x86_ra_abi_copy_hints_disabled, set_x86_ra_call_split_disabled,
    set_x86_ra_caller_saved_first_disabled, set_x86_ra_cold_call_weight_disabled,
    set_x86_ra_trace_enabled, x86_ra_quality_withheld,
};

/// The codegen license the crate's unit tests compile their hand-built
/// fixtures under. Those fixtures carry no codegen license (`body_gate:
/// None`), which trust-cg REFUSES by default (roadmap WS7.5, decision gate
/// DG-73), so they state `Permit` explicitly: none of them passes (or is
/// refused) because the license silently refused it. Declared under a plain
/// `#[cfg(test)]`, so the production `Permit` census never counts it.
#[cfg(test)]
pub(crate) mod license_test_support {
    /// The default policy with claim-less bodies permitted.
    pub(crate) fn permit_unlicensed() -> crate::CodegenLicensePolicy {
        crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
    }
}
