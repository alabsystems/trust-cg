// trust-cg-codegen/jit_install_gate.rs - Native install evidence gate
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Pure data-only native install evidence gate for Phase 6.
//!
//! This module deliberately does not publish callable handles, mutate caches,
//! decide release promotion, or touch ay/TY product registries. It validates
//! that one native-dispatch candidate has a complete manifest/proof/layout/
//! invalidation/telemetry bundle and returns a packet that future product paths
//! can persist or consume.

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroUsize;

use crate::ay_lra_proof_manifest::{
    AYLraKernelFamily, AYLraKernelProofConsumptionManifest, ay_lra_basis_update_proof_manifest,
    ay_lra_proof_fact_metadata_key, ay_lra_sparse_affected_row_batch_proof_manifest,
    ay_lra_sparse_substitute_proof_manifest,
};
use crate::compile_service::ArtifactManifestReference;
use crate::jit_contract::{
    ArtifactChecksum, ArtifactManifestV1, JIT_ARTIFACT_MANIFEST_SCHEMA,
    JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION, JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA,
    JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA_VERSION, ProofEvidenceRejectionCode, ProofEvidenceSummary,
    ProofEvidenceVerdict,
};
use crate::jit_diagnostics::sha256_hex;
use crate::pipeline::ProofOptimizationCertificateCitation;
use crate::ty_reducer_evidence::{
    TY_REDUCER_EVIDENCE_FAMILIES_METADATA_KEY, TY_REDUCER_EVIDENCE_PACKET_SCHEMA,
    TY_REDUCER_EVIDENCE_PACKET_SCHEMA_VERSION, TY_REDUCER_EVIDENCE_PACKET_SHA256_METADATA_KEY,
    TY_REDUCER_EVIDENCE_SCHEMA_METADATA_KEY, TY_REDUCER_EVIDENCE_SCHEMA_VERSION_METADATA_KEY,
    TY_REDUCER_REQUIRED_EVIDENCE_FAMILIES, TyReducerEvidenceCoverageSummary,
};

/// Stable schema tag for native install gate packets.
pub const NATIVE_INSTALL_GATE_PACKET_SCHEMA: &str = "trust-cg.phase6.native_install_gate.v1";

/// Stable numeric schema version for [`NativeInstallGatePacket`].
pub const NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for telemetry identity records bound to install packets.
pub const NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA: &str =
    "trust-cg.phase6.native_install_gate.telemetry_identity.v1";

/// Stable numeric schema version for telemetry identity records.
pub const NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for runtime useful-native telemetry records.
pub const NATIVE_INSTALL_GATE_RUNTIME_TELEMETRY_SCHEMA: &str =
    "trust-cg.phase6.native_install_gate.runtime_telemetry.v1";

/// Stable numeric schema version for runtime useful-native telemetry records.
pub const NATIVE_INSTALL_GATE_RUNTIME_TELEMETRY_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for ay/TY consumer admission telemetry records.
pub const NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA: &str =
    "trust-cg.phase6.native_install_gate.consumer_admission.v1";

/// Stable numeric schema version for consumer admission telemetry records.
pub const NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for compact native admission summaries.
pub const NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA: &str =
    "trust-cg.phase6.native_install_gate.admission_summary.v1";

/// Stable numeric schema version for compact native admission summaries.
pub const NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA_VERSION: u32 = 1;

/// Stable Petri/MCC consumer name for native successor admission.
pub const PETRI_NATIVE_SUCCESSOR_CONSUMER: &str = "mcc";

/// Stable Petri/MCC consumer mode for native successor JIT admission.
pub const PETRI_NATIVE_SUCCESSOR_CONSUMER_MODE: &str = "ty_petri_native_jit";

/// Stable Petri/MCC native successor kind.
pub const PETRI_NATIVE_SUCCESSOR_KIND: &str = "petri_successor";

/// Stable schema tag for Petri/MCC native successor callable contracts.
pub const PETRI_NATIVE_SUCCESSOR_CALLABLE_CONTRACT_SCHEMA: &str =
    "trust-cg.petri.native_successor.callable_contract.v1";

/// Stable numeric schema version for Petri/MCC native successor callable contracts.
pub const PETRI_NATIVE_SUCCESSOR_CALLABLE_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor execution plans.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_SCHEMA: &str =
    "trust-cg.petri.native_successor.execution_plan.v1";

/// Stable numeric schema version for Petri/MCC native successor execution plans.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor trampoline contracts.
pub const PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA: &str =
    "trust-cg.petri.native_successor.trampoline_contract.v1";

/// Stable numeric schema version for Petri/MCC native successor trampoline contracts.
pub const PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor host call packets.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA: &str =
    "trust-cg.petri.native_successor.call_packet.v1";

/// Stable numeric schema version for Petri/MCC native successor host call packets.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for the Petri/MCC native successor call-packet contract descriptor.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_SCHEMA: &str =
    "trust-cg.petri.native_successor.call_packet_contract_descriptor.v1";

/// Stable numeric schema version for the call-packet contract descriptor.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_SCHEMA_VERSION: u32 = 1;

/// Stable descriptor identity for the Petri/MCC call-packet evidence surface.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_ID: &str =
    "trust-cg.petri.native_successor.call_packet_contract";

/// Stable schema tag for Petri/MCC call-packet contract descriptor health reports.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SCHEMA: &str =
    "trust-cg.petri.native_successor.call_packet_contract_health.v1";

/// Stable numeric schema version for call-packet contract descriptor health reports.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for compact call-packet contract health summaries.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_SCHEMA: &str =
    "trust-cg.petri.native_successor.call_packet_contract_health_summary.v1";

/// Stable numeric schema version for compact call-packet contract health summaries.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for compact call-packet contract health summary validation.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_VALIDATION_SCHEMA: &str =
    "trust-cg.petri.native_successor.call_packet_contract_health_summary_validation.v1";

/// Stable numeric schema version for compact call-packet contract health summary validation.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_VALIDATION_SCHEMA_VERSION:
    u32 = 1;

/// Stable schema tag for Petri/MCC native successor manifest identities.
pub const PETRI_NATIVE_SUCCESSOR_MANIFEST_IDENTITY_SCHEMA: &str =
    "trust-cg.petri.native_successor.manifest_identity.v1";

/// Stable numeric schema version for Petri/MCC native successor manifest identities.
pub const PETRI_NATIVE_SUCCESSOR_MANIFEST_IDENTITY_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor install binding evidence.
pub const PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_EVIDENCE_SCHEMA: &str =
    "trust-cg.petri.native_successor.install_binding_evidence.v1";

/// Stable numeric schema version for Petri/MCC native successor install binding evidence.
pub const PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_EVIDENCE_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor callable lifetime proofs.
pub const PETRI_NATIVE_SUCCESSOR_CALLABLE_LIFETIME_PROOF_SCHEMA: &str =
    "trust-cg.petri.native_successor.callable_lifetime_proof.v1";

/// Stable numeric schema version for Petri/MCC native successor callable lifetime proofs.
pub const PETRI_NATIVE_SUCCESSOR_CALLABLE_LIFETIME_PROOF_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor runtime ABI proofs.
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_ABI_PROOF_SCHEMA: &str =
    "trust-cg.petri.native_successor.runtime_abi_proof.v1";

/// Stable numeric schema version for Petri/MCC native successor runtime ABI proofs.
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_ABI_PROOF_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor executable call evidence.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTABLE_CALL_EVIDENCE_SCHEMA: &str =
    "trust-cg.petri.native_successor.executable_call_evidence.v1";

/// Stable numeric schema version for Petri/MCC native successor executable call evidence.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTABLE_CALL_EVIDENCE_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor runtime readiness packets.
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA: &str =
    "trust-cg.petri.native_successor.runtime_readiness_packet.v1";

/// Stable numeric schema version for Petri/MCC native successor runtime readiness packets.
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor execution authority decisions.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA: &str =
    "trust-cg.petri.native_successor.execution_authority.v1";

/// Stable numeric schema version for Petri/MCC native successor execution authority decisions.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor production-selection decisions.
pub const PETRI_NATIVE_SUCCESSOR_PRODUCTION_SELECTION_SCHEMA: &str =
    "trust-cg.petri.native_successor.production_selection.v1";

/// Stable numeric schema version for Petri/MCC native successor production-selection decisions.
pub const PETRI_NATIVE_SUCCESSOR_PRODUCTION_SELECTION_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Trust Codegen trust_ir vector-constant lowering evidence used by Petri/MCC.
pub const PETRI_NATIVE_SUCCESSOR_VECTOR_CONSTANT_LOWERING_EVIDENCE_SCHEMA: &str =
    "trust-cg.lower.trust_ir_constant_vector.v128_lane_store.v1";

/// Stable numeric schema version for trust_ir vector-constant lowering evidence.
pub const PETRI_NATIVE_SUCCESSOR_VECTOR_CONSTANT_LOWERING_EVIDENCE_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor execution-authority manifest validation.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA: &str =
    "trust-cg.petri.native_successor.execution_authority_manifest_validation.v1";

/// Stable numeric schema version for execution-authority manifest validation.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor execution-authority replay identities.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA: &str =
    "trust-cg.petri.native_successor.execution_authority_replay_identity.v1";

/// Stable numeric schema version for execution-authority replay identities.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for compact Petri/MCC execution-authority summaries.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_SCHEMA: &str =
    "trust-cg.petri.native_successor.execution_authority_summary.v1";

/// Stable numeric schema version for compact execution-authority summaries.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for compact execution-authority summary validation.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_VALIDATION_SCHEMA: &str =
    "trust-cg.petri.native_successor.execution_authority_summary_validation.v1";

/// Stable numeric schema version for compact execution-authority summary validation.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_VALIDATION_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC execution-authority diagnostic fixture manifests.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA: &str =
    "trust-cg.petri.native_successor.execution_authority_diagnostic_fixture_manifest.v1";

/// Stable numeric schema version for execution-authority diagnostic fixture manifests.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA_VERSION:
    u32 = 1;

/// Stable schema tag for execution-authority diagnostic fixture manifest validation.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_VALIDATION_SCHEMA:
    &str = "trust-cg.petri.native_successor.execution_authority_diagnostic_fixture_manifest_validation.v1";

/// Stable numeric schema version for execution-authority diagnostic fixture manifest validation.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_VALIDATION_SCHEMA_VERSION:
    u32 = 1;

/// Stable schema tag for Petri/MCC native successor mock executable-call dry runs.
pub const PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA: &str =
    "trust-cg.petri.native_successor.mock_executable_call.v1";

/// Stable numeric schema version for Petri/MCC native successor mock executable-call dry runs.
pub const PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor runtime callable invocations.
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_SCHEMA: &str =
    "trust-cg.petri.native_successor.runtime_call.v1";

/// Stable numeric schema version for Petri/MCC native successor runtime callable invocations.
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor compile-artifact handoff evidence.
pub const PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA: &str =
    "trust-cg.petri.native_successor.compile_artifact_handoff.v1";

/// Stable numeric schema version for Petri/MCC native successor compile-artifact handoff evidence.
pub const PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for JSON-free Petri/MCC native successor handoff evidence manifests.
pub const PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA: &str =
    "trust-cg.petri.native_successor.handoff_evidence_manifest.v1";

/// Stable numeric schema version for Petri/MCC native successor handoff evidence manifests.
pub const PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri/MCC native successor semantic bridge evidence.
pub const PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA: &str =
    "trust-cg.petri.native_successor.semantic_bridge.v1";

/// Stable numeric schema version for Petri/MCC native successor semantic bridge evidence.
pub const PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA_VERSION: u32 = 1;

/// Formula schema that identifies trust_ir proof obligations covering Petri successor semantics.
pub const PETRI_NATIVE_SUCCESSOR_SEMANTIC_FORMULA_SCHEMA: &str =
    "ty.petri.native.successor.plan_cache_equivalence.v1";

/// Stable schema tag for the downstream TY/MCC Petri native successor contract descriptor.
pub const PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_SCHEMA: &str =
    "trust-cg.petri.native_successor.downstream_contract.v1";

/// Stable numeric schema version for the downstream TY/MCC Petri native successor contract.
pub const PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for the trust-mc-backed Petri native admission route descriptor.
pub const PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_SCHEMA: &str =
    "trust-cg.petri.native_successor.trust_mc_admission_route_descriptor.v1";

/// Stable numeric schema version for the trust-mc-backed Petri native admission route descriptor.
pub const PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_SCHEMA_VERSION: u32 = 1;

/// Stable descriptor id for the trust-mc-backed Petri native admission route.
pub const PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_ID: &str =
    "trust-cg.petri.native_successor.trust_mc_admission_route";

/// Stable schema tag for trust-mc-backed Petri native admission route descriptor validation.
pub const PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_VALIDATION_SCHEMA: &str =
    "trust-cg.petri.native_successor.trust_mc_admission_route_descriptor_validation.v1";

/// Stable numeric schema version for trust-mc admission route descriptor validation.
pub const PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_VALIDATION_SCHEMA_VERSION:
    u32 = 1;

/// Stable schema tag for the Trust Codegen producer bridge descriptor tying Petri native surfaces together.
pub const PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_SCHEMA: &str =
    "trust-cg.petri.native_successor.producer_bridge_descriptor.v1";

/// Stable numeric schema version for the Petri native producer bridge descriptor.
pub const PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_SCHEMA_VERSION: u32 = 1;

/// Stable descriptor id for the Trust Codegen Petri native producer bridge.
pub const PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_ID: &str =
    "trust-cg.petri.native_successor.producer_bridge";

/// Stable schema tag for Petri native producer bridge descriptor validation.
pub const PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_VALIDATION_SCHEMA: &str =
    "trust-cg.petri.native_successor.producer_bridge_descriptor_validation.v1";

/// Stable numeric schema version for Petri native producer bridge descriptor validation.
pub const PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_VALIDATION_SCHEMA_VERSION: u32 = 1;

/// Stable owner code for trust_ir-owned source evidence.
pub const PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_IR: &str = "trust_ir";

/// Stable owner code for AY-owned solver/model acceptance.
pub const PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_AY: &str = "ay";

/// Stable owner code for Trust Codegen-owned native install/runtime authority.
pub const PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_CG: &str = "trust-cg";

/// Stable validator/helper API names downstreams should call for execution-authority summaries.
pub const PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_REQUIRED_SUMMARY_VALIDATORS: &[&str] = &[
    "PetriNativeSuccessorExecutionAuthoritySummary::to_json_string()",
    "validate_petri_native_successor_execution_authority_summary_rows()",
    "validate_petri_native_successor_execution_authority_summary_key_value_lines()",
    "validate_petri_native_successor_execution_authority_summary_json_value()",
    "validate_petri_native_successor_execution_authority_summary_json_str()",
];

/// Stable validator/helper API names downstreams should call for trust-mc route descriptors.
pub const PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_REQUIRED_ROUTE_VALIDATORS: &[&str] = &[
    "validate_petri_native_successor_trust_mc_admission_route_descriptor_rows()",
    "validate_petri_native_successor_trust_mc_admission_route_descriptor_key_value_lines()",
    "validate_petri_native_successor_trust_mc_admission_route_descriptor_text()",
    "validate_petri_native_successor_trust_mc_admission_route_descriptor_json_value()",
    "validate_petri_native_successor_trust_mc_admission_route_descriptor_json_str()",
];

/// Required inputs for [`petri_native_successor_admission_from_trust_ir_bundle`].
pub const PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_REQUIRED_FIELDS: &[&str] = &[
    "trust_ir_bundle",
    "expected.consumer",
    "expected.surface",
    "expected.native_install_gate_packet",
];

/// Stable dispositions emitted by [`NativeInstallGateAdmissionSummary`] for Petri admission.
pub const PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_STATUS_CODES: &[&str] = &[
    "installable",
    "profile_only",
    "replay_only",
    "shadow_only",
    "rejected",
];

/// Stable rejection codes observed by Petri native successor install-gate admission.
pub const PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_BLOCKER_CODES: &[&str] = &[
    "consumer_admission_denied",
    "evidence_binding_mismatch",
    "inconsistent_action_authority",
    "missing_native_evidence_bundle",
    "missing_native_install_gate_packet",
    "packet_hash_mismatch",
    "petri_trust_ir_bundle_validation_failed",
    "proof_replay_identity_mismatch",
    "target_abi_mismatch",
];

/// Required inputs for [`petri_native_successor_execution_plan_from_trust_ir_bundle`].
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_REQUIRED_FIELDS: &[&str] = &[
    "trust_ir_bundle",
    "expected.admission",
    "expected.entry_function",
    "expected.state_layout",
    "expected.trampoline_contract",
];

/// Stable statuses emitted by [`PetriNativeSuccessorExecutionPlan`].
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_STATUS_CODES: &[&str] =
    &["callable_authorized", "fail_closed"];

/// Stable blocker codes emitted by [`PetriNativeSuccessorExecutionPlan`].
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_BLOCKER_CODES: &[&str] = &[
    "unsupported_expected",
    "invalid_state_layout",
    "missing_entry_function",
    "target_abi_mismatch",
    "bundle_validation_failed",
    "missing_semantic_successor_obligation",
    "missing_semantic_successor_evidence",
    "consumer_admission_denied",
    "missing_native_install_gate_packet",
];

/// Required inputs for [`petri_native_successor_call_packet_from_trust_ir_bundle`].
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_REQUIRED_FIELDS: &[&str] = &[
    "trust_ir_bundle",
    "expected.admission",
    "expected.entry_function",
    "expected.state_layout",
    "expected.native_install_gate_packet",
    "trampoline_contract",
    "callable_pointer",
];

/// Stable statuses represented by [`PetriNativeSuccessorCallPacket`].
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_STATUS_CODES: &[&str] =
    &["callable_authorized", "fail_closed"];

/// Stable statuses emitted by call-packet contract descriptor health reports.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_STATUS_CODES: &[&str] =
    &["healthy", "fail_closed"];

/// Stable reason codes emitted by call-packet contract descriptor health reports.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_REASON_CODES: &[&str] = &[
    "invalid_call_packet_contract_descriptor_line",
    "duplicate_call_packet_contract_descriptor_row",
    "missing_call_packet_contract_descriptor_row",
    "stale_call_packet_contract_descriptor_schema",
    "mismatched_call_packet_contract_required_field",
    "mismatched_call_packet_contract_descriptor_value",
    "unexpected_call_packet_contract_descriptor_row",
];

/// Stable validation statuses emitted for compact call-packet health summaries.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_VALIDATION_STATUS_CODES:
    &[&str] = &["accepted", "fail_closed"];

/// Stable reason codes emitted by compact call-packet health summary validation.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_VALIDATION_REASON_CODES:
    &[&str] = &[
    "invalid_call_packet_contract_health_summary_line",
    "duplicate_call_packet_contract_health_summary_row",
    "missing_call_packet_contract_health_summary_row",
    "stale_call_packet_contract_health_summary_schema",
    "mismatched_call_packet_contract_health_summary_value",
    "unexpected_call_packet_contract_health_summary_row",
];

/// Stable key prefix for missing descriptor rows in call-packet health reports.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_MISSING_KEY_PREFIX: &str =
    "health.missing_key";

/// Stable key prefix for duplicate descriptor rows in call-packet health reports.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_DUPLICATE_KEY_PREFIX: &str =
    "health.duplicate_key";

/// Stable key prefix for stale schema rows in call-packet health reports.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_STALE_SCHEMA_KEY_PREFIX: &str =
    "health.stale_schema_key";

/// Stable key prefix for mismatched required-field rows in call-packet health reports.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_MISMATCHED_REQUIRED_FIELD_KEY_PREFIX:
    &str = "health.mismatched_required_field_key";

/// Stable key prefix for mismatched descriptor rows in call-packet health reports.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_MISMATCHED_KEY_PREFIX: &str =
    "health.mismatched_key";

/// Stable key prefix for unexpected descriptor rows in call-packet health reports.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_UNEXPECTED_KEY_PREFIX: &str =
    "health.unexpected_key";

/// Stable blocker codes for Petri native successor call-packet construction.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_BLOCKER_CODES: &[&str] = &[
    "unsupported_expected",
    "invalid_state_layout",
    "missing_entry_function",
    "target_abi_mismatch",
    "bundle_validation_failed",
    "missing_semantic_successor_obligation",
    "missing_semantic_successor_evidence",
    "consumer_admission_denied",
    "missing_native_install_gate_packet",
    "inconsistent_action_authority",
    "petri_trust_ir_bundle_validation_failed",
];

/// Runtime evidence schemas required before a call packet can execute in production.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_REQUIRED_RUNTIME_EVIDENCE: &[&str] = &[
    PETRI_NATIVE_SUCCESSOR_CALLABLE_LIFETIME_PROOF_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_ABI_PROOF_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTABLE_CALL_EVIDENCE_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA,
];

/// Required inputs for [`petri_native_successor_install_binding_evidence`].
pub const PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_REQUIRED_FIELDS: &[&str] =
    &["native_install_gate_packet", "trampoline_contract"];

/// Stable statuses emitted by [`PetriNativeSuccessorInstallBindingEvidence`].
pub const PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_STATUS_CODES: &[&str] = &["ready", "blocked"];

/// Stable blocker codes emitted by [`PetriNativeSuccessorInstallBindingEvidence`].
pub const PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_BLOCKER_CODES: &[&str] = &[
    "missing_native_install_gate_packet",
    "missing_manifest",
    "packet_hash_mismatch",
    "missing_callable_authority",
    "trampoline_unbound",
    "trampoline_binding_mismatch",
];

/// Required inputs for [`petri_native_successor_runtime_readiness_packet`].
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_REQUIRED_FIELDS: &[&str] = &[
    "call_packet",
    "native_install_gate_packet",
    "trampoline_contract",
    "callable_lifetime_proof",
    "runtime_abi_proof",
    "current_generation",
];

/// Stable statuses emitted by [`PetriNativeSuccessorRuntimeReadinessPacket`].
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_STATUS_CODES: &[&str] =
    &["ready_for_runtime_call", "blocked"];

/// Stable blocker codes emitted by [`PetriNativeSuccessorRuntimeReadinessPacket`].
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_BLOCKER_CODES: &[&str] = &[
    "missing_native_install_gate_packet",
    "unsupported_consumer",
    "unsupported_consumer_mode",
    "unsupported_surface",
    "packet_hash_mismatch",
    "missing_artifact_id",
    "missing_manifest_checksum",
    "missing_source_sha256",
    "missing_trust_ir_sha256",
    "missing_native_payload_sha256",
    "missing_target_checksum",
    "missing_abi_checksum",
    "missing_layout_checksum",
    "missing_proof_policy_checksum",
    "missing_invalidation_checksum",
    "missing_manifest",
    "missing_callable_authority",
    "trampoline_unbound",
    "trampoline_binding_mismatch",
    "missing_callable_pointer",
    "call_packet_binding_mismatch",
    "missing_callable_lifetime_proof",
    "callable_lifetime_proof_mismatch",
    "callable_pointer_mismatch",
    "stale_callable_lifetime_proof",
    "missing_runtime_abi_proof",
    "runtime_abi_proof_mismatch",
    "runtime_abi_mismatch",
];

/// Required inputs for [`petri_native_successor_mock_executable_call_dry_run`].
pub const PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_REQUIRED_FIELDS: &[&str] = &[
    "runtime_readiness_packet",
    "call_packet",
    "mock_executable_call_gate",
    "input_state",
    "output_state",
];

/// Stable statuses emitted by [`PetriNativeSuccessorMockExecutableCallReport`].
pub const PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_STATUS_CODES: &[&str] =
    &["dry_run_accepted", "blocked"];

/// Stable blocker codes emitted by [`PetriNativeSuccessorMockExecutableCallReport`].
pub const PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_BLOCKER_CODES: &[&str] = &[
    "mock_harness_disabled",
    "runtime_readiness_hash_mismatch",
    "runtime_readiness_blocked",
    "call_packet_missing",
    "call_packet_hash_mismatch",
    "call_packet_binding_mismatch",
    "callable_pointer_mismatch",
    "trampoline_abi_mismatch",
    "state_encoding_mismatch",
    "input_state_bytes_mismatch",
    "output_state_bytes_mismatch",
];

/// Required inputs for [`petri_native_successor_call_runtime_entrypoint`].
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_REQUIRED_FIELDS: &[&str] = &[
    "runtime_readiness_packet",
    "execution_authority_decision",
    "call_packet",
    "runtime_callable_entrypoint",
    "input_state",
    "output_state",
];

/// Stable statuses emitted by [`PetriNativeSuccessorRuntimeCallReport`].
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_STATUS_CODES: &[&str] = &["executed", "blocked"];

/// Stable blocker codes emitted by [`PetriNativeSuccessorRuntimeCallReport`].
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_BLOCKER_CODES: &[&str] = &[
    "runtime_readiness_hash_mismatch",
    "runtime_readiness_blocked",
    "execution_authority_hash_mismatch",
    "execution_authority_not_authorized",
    "call_packet_hash_mismatch",
    "call_packet_binding_mismatch",
    "callable_pointer_mismatch",
    "trampoline_abi_mismatch",
    "state_encoding_mismatch",
    "input_state_bytes_mismatch",
    "output_state_bytes_mismatch",
];

/// Required inputs for [`petri_native_successor_compile_artifact_handoff_evidence`].
pub const PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_REQUIRED_FIELDS: &[&str] = &[
    "compiled_artifact.native_payload_sha256",
    "compiled_artifact.entry_symbol",
    "compiled_artifact.callable_pointer",
    "compiled_artifact.executable_region_sha256",
    "compiled_artifact.lifetime_owner",
    "compiled_artifact.current_generation",
];

/// Stable statuses emitted by [`PetriNativeSuccessorCompileArtifactHandoffEvidence`].
pub const PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_STATUS_CODES: &[&str] =
    &["ready", "blocked"];

/// Stable blocker codes emitted by [`PetriNativeSuccessorCompileArtifactHandoffEvidence`].
pub const PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_BLOCKER_CODES: &[&str] = &[
    "missing_native_payload_sha256",
    "missing_entry_symbol",
    "missing_callable_pointer",
    "missing_executable_region_sha256",
    "missing_lifetime_owner",
    "missing_current_generation",
];

/// Required inputs for [`petri_native_successor_execution_authority_decision`].
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REQUIRED_FIELDS: &[&str] =
    &["compile_artifact_handoff", "runtime_readiness_packet"];

/// Stable statuses emitted by [`PetriNativeSuccessorExecutionAuthorityDecision`].
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_STATUS_CODES: &[&str] =
    &["authorized", "fail_closed"];

/// Stable statuses emitted by [`PetriNativeSuccessorProductionSelectionDecision`].
pub const PETRI_NATIVE_SUCCESSOR_PRODUCTION_SELECTION_STATUS_CODES: &[&str] =
    &["selected", "fail_closed"];

/// Stable reason codes emitted by [`PetriNativeSuccessorProductionSelectionDecision`].
pub const PETRI_NATIVE_SUCCESSOR_PRODUCTION_SELECTION_REASON_CODES: &[&str] = &[
    "execution_authority_hash_mismatch",
    "execution_authority_not_authorized",
    "call_packet_missing",
    "call_packet_hash_mismatch",
    "call_packet_binding_mismatch",
    "native_payload_sha256_mismatch",
    "entry_symbol_mismatch",
    "callable_pointer_mismatch",
    "callable_lane_not_authorized",
    "runtime_not_ready",
    "runtime_not_useful_native",
];

/// Stable statuses emitted by execution-authority manifest validation.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_STATUS_CODES: &[&str] =
    &["accepted", "fail_closed"];

/// Stable reason codes emitted by [`PetriNativeSuccessorExecutionAuthorityDecision`].
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_BLOCKER_CODES: &[&str] = &[
    "missing_compile_artifact_handoff",
    "missing_runtime_readiness_packet",
    "missing_compile_artifact_handoff_sha256",
    "compile_artifact_handoff_hash_mismatch",
    "compile_artifact_handoff_blocked",
    "missing_native_payload_sha256",
    "missing_entry_symbol",
    "missing_callable_pointer",
    "missing_executable_region_sha256",
    "missing_lifetime_owner",
    "missing_current_generation",
    "missing_runtime_readiness_packet_sha256",
    "runtime_readiness_packet_hash_mismatch",
    "runtime_readiness_blocked",
    "missing_native_install_gate_packet",
    "unsupported_consumer",
    "unsupported_consumer_mode",
    "unsupported_surface",
    "packet_hash_mismatch",
    "missing_artifact_id",
    "missing_manifest_checksum",
    "missing_source_sha256",
    "missing_trust_ir_sha256",
    "missing_target_checksum",
    "missing_abi_checksum",
    "missing_layout_checksum",
    "missing_proof_policy_checksum",
    "missing_invalidation_checksum",
    "missing_manifest",
    "missing_callable_authority",
    "trampoline_unbound",
    "trampoline_binding_mismatch",
    "call_packet_binding_mismatch",
    "missing_callable_lifetime_proof",
    "callable_lifetime_proof_mismatch",
    "callable_pointer_mismatch",
    "stale_callable_lifetime_proof",
    "missing_runtime_abi_proof",
    "runtime_abi_proof_mismatch",
    "runtime_abi_mismatch",
    "missing_call_packet_sha256",
    "missing_install_packet_hash",
    "missing_persisted_install_packet_hash",
    "install_packet_hash_mismatch",
    "missing_manifest_identity_sha256",
    "native_payload_sha256_mismatch",
    "entry_symbol_mismatch",
    "runtime_readiness_not_authoritative",
];

/// Stable reason codes emitted by execution-authority manifest validation.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_REASON_CODES: &[&str] = &[
    "invalid_authority_manifest_line",
    "duplicate_authority_manifest_key",
    "missing_required_authority_manifest_key",
    "unsupported_authority_manifest_schema",
    "unsupported_authority_manifest_schema_version",
    "unsupported_authority_manifest_surface",
    "unsupported_execution_authority_schema",
    "unsupported_execution_authority_schema_version",
    "unsupported_execution_authority_status",
    "authority_evidence_fail_closed",
    "authorized_authority_reason_present",
    "missing_required_authority_manifest_value",
    "authority_not_authorized",
    "compile_artifact_handoff_hash_not_current",
    "runtime_readiness_packet_hash_not_current",
    "runtime_not_authoritative",
    "native_not_authoritative",
    "authority_manifest_identity_mismatch",
];

/// Required row keys for Petri/MCC native successor execution-authority manifests.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_REQUIRED_KEYS: &[&str] = &[
    "manifest.schema",
    "manifest.schema_version",
    "handoff.surface",
    "evidence.schema",
    "evidence.schema_version",
    "evidence.status",
    "authority.authorized_for_execution",
    "evidence.reason_code",
    "evidence.source_reason_code",
    "evidence.required_field",
    "evidence.required_evidence",
    "handoff.compile_artifact_handoff_sha256",
    "runtime.readiness_packet_sha256",
    "authority.compile_artifact_handoff_hash_current",
    "authority.runtime_readiness_packet_hash_current",
    "compile_artifact.native_payload_sha256",
    "runtime.native_payload_sha256",
    "compile_artifact.entry_symbol",
    "runtime.entry_symbol",
    "compile_artifact.callable_pointer",
    "runtime.callable_pointer",
    "callable.call_packet_sha256",
    "install_gate.packet_hash",
    "install_gate.persisted_packet_hash",
    "install_gate.manifest_identity_sha256",
    "callable.authorized",
    "runtime.ready_for_call",
    "runtime.authorizes_useful_native",
    "native.authorizes_useful_native",
    "authority.execution_authority_sha256",
];

/// Row keys that must be non-empty before an execution-authority manifest can be accepted.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_ACCEPTED_REQUIRED_VALUE_KEYS:
    &[&str] = &[
    "handoff.compile_artifact_handoff_sha256",
    "runtime.readiness_packet_sha256",
    "compile_artifact.native_payload_sha256",
    "runtime.native_payload_sha256",
    "compile_artifact.entry_symbol",
    "runtime.entry_symbol",
    "compile_artifact.callable_pointer",
    "runtime.callable_pointer",
    "callable.call_packet_sha256",
    "install_gate.packet_hash",
    "install_gate.persisted_packet_hash",
    "install_gate.manifest_identity_sha256",
    "authority.execution_authority_sha256",
];

/// Stable typed row kind for Petri/MCC native successor handoff evidence manifests.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PetriNativeSuccessorHandoffManifestRowKind {
    ManifestSchema,
    ManifestSchemaVersion,
    Surface,
    EvidenceSchema,
    EvidenceSchemaVersion,
    Status,
    ReasonCode,
    RequiredField,
    RequiredEvidence,
    NativePayloadSha256,
    EntrySymbol,
    CallablePointer,
    ExecutableRegionSha256,
    CompileArtifactHandoffSha256,
    InstallPacketHash,
    PersistedInstallPacketHash,
    ManifestIdentitySha256,
    ManifestIdentitySource,
    CallPacketSha256,
    CallableAuthorized,
    ReadyForRuntimeCall,
    RuntimeReadinessPacketSha256,
    SourceReasonCode,
    AuthorizedForExecution,
    CompileArtifactNativePayloadSha256,
    RuntimeNativePayloadSha256,
    CompileArtifactEntrySymbol,
    RuntimeEntrySymbol,
    CompileArtifactCallablePointer,
    RuntimeCallablePointer,
    CompileArtifactHandoffHashCurrent,
    RuntimeReadinessPacketHashCurrent,
    RuntimeAuthorizesUsefulNative,
    ExecutionAuthoritySha256,
    AuthorizesUsefulNative,
}

/// Validation status for execution-authority manifest rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PetriNativeSuccessorExecutionAuthorityManifestValidationStatus {
    /// Manifest rows are complete and authorize useful native execution.
    Accepted,
    /// Manifest rows are incomplete, malformed, stale, or explicitly fail-closed.
    FailClosed,
}

impl PetriNativeSuccessorExecutionAuthorityManifestValidationStatus {
    /// Return the stable validation status code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::FailClosed => "fail_closed",
        }
    }
}

impl PetriNativeSuccessorHandoffManifestRowKind {
    /// Return the stable manifest row key for this row kind.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ManifestSchema => "manifest.schema",
            Self::ManifestSchemaVersion => "manifest.schema_version",
            Self::Surface => "handoff.surface",
            Self::EvidenceSchema => "evidence.schema",
            Self::EvidenceSchemaVersion => "evidence.schema_version",
            Self::Status => "evidence.status",
            Self::ReasonCode => "evidence.reason_code",
            Self::RequiredField => "evidence.required_field",
            Self::RequiredEvidence => "evidence.required_evidence",
            Self::NativePayloadSha256 => "artifact.native_payload_sha256",
            Self::EntrySymbol => "artifact.entry_symbol",
            Self::CallablePointer => "callable.pointer",
            Self::ExecutableRegionSha256 => "runtime.executable_region_sha256",
            Self::CompileArtifactHandoffSha256 => "handoff.compile_artifact_handoff_sha256",
            Self::InstallPacketHash => "install_gate.packet_hash",
            Self::PersistedInstallPacketHash => "install_gate.persisted_packet_hash",
            Self::ManifestIdentitySha256 => "install_gate.manifest_identity_sha256",
            Self::ManifestIdentitySource => "install_gate.manifest_identity_source",
            Self::CallPacketSha256 => "callable.call_packet_sha256",
            Self::CallableAuthorized => "callable.authorized",
            Self::ReadyForRuntimeCall => "runtime.ready_for_call",
            Self::RuntimeReadinessPacketSha256 => "runtime.readiness_packet_sha256",
            Self::SourceReasonCode => "evidence.source_reason_code",
            Self::AuthorizedForExecution => "authority.authorized_for_execution",
            Self::CompileArtifactNativePayloadSha256 => "compile_artifact.native_payload_sha256",
            Self::RuntimeNativePayloadSha256 => "runtime.native_payload_sha256",
            Self::CompileArtifactEntrySymbol => "compile_artifact.entry_symbol",
            Self::RuntimeEntrySymbol => "runtime.entry_symbol",
            Self::CompileArtifactCallablePointer => "compile_artifact.callable_pointer",
            Self::RuntimeCallablePointer => "runtime.callable_pointer",
            Self::CompileArtifactHandoffHashCurrent => {
                "authority.compile_artifact_handoff_hash_current"
            }
            Self::RuntimeReadinessPacketHashCurrent => {
                "authority.runtime_readiness_packet_hash_current"
            }
            Self::RuntimeAuthorizesUsefulNative => "runtime.authorizes_useful_native",
            Self::ExecutionAuthoritySha256 => "authority.execution_authority_sha256",
            Self::AuthorizesUsefulNative => "native.authorizes_useful_native",
        }
    }
}

/// Stable key/value row for JSON-free Petri/MCC native successor handoff evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorHandoffManifestRow {
    /// Typed row kind for Rust/TY consumers.
    pub kind: PetriNativeSuccessorHandoffManifestRowKind,
    /// Raw manifest key.
    pub key: &'static str,
    /// Raw manifest value.
    pub value: String,
}

impl PetriNativeSuccessorHandoffManifestRow {
    /// Create a typed handoff evidence manifest row.
    pub fn typed(
        kind: PetriNativeSuccessorHandoffManifestRowKind,
        value: impl Into<String>,
    ) -> Self {
        Self {
            kind,
            key: kind.as_str(),
            value: value.into(),
        }
    }

    /// Stable row-kind code for structured downstream emitters.
    pub const fn kind_code(&self) -> &'static str {
        self.kind.as_str()
    }

    /// Escaped key for line-oriented `key=value` manifest output.
    pub fn escaped_key(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(self.key)
    }

    /// Escaped value for line-oriented `key=value` manifest output.
    pub fn escaped_value(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

/// Fail-closed validation report for execution-authority manifest rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthorityManifestValidationReport {
    /// Validation report schema.
    pub schema: &'static str,
    /// Validation report schema version.
    pub schema_version: u32,
    /// Accepted only when the manifest rows are complete and authorize native execution.
    pub status: PetriNativeSuccessorExecutionAuthorityManifestValidationStatus,
    /// Stable reason code for fail-closed validation.
    pub reason_code: Option<String>,
    /// Status code carried by the authority evidence rows, when present.
    pub evidence_status_code: Option<String>,
    /// Reason code carried by the authority evidence rows, when present.
    pub evidence_reason_code: Option<String>,
    /// Required authority row keys that were absent.
    pub missing_required_keys: Vec<&'static str>,
    /// Duplicate row keys. Any duplicate makes the manifest ambiguous and fail-closed.
    pub duplicate_keys: Vec<String>,
    /// Required accepted-authority value keys that were present but blank.
    pub blank_required_value_keys: Vec<&'static str>,
    /// Number of malformed `key=value` lines seen by the line validator.
    pub invalid_key_value_line_count: usize,
}

impl PetriNativeSuccessorExecutionAuthorityManifestValidationReport {
    /// Return true only when the manifest validates to accepted authority.
    pub fn is_accepted(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::Accepted
        ) && self.reason_code.is_none()
            && self.missing_required_keys.is_empty()
            && self.duplicate_keys.is_empty()
            && self.blank_required_value_keys.is_empty()
            && self.invalid_key_value_line_count == 0
    }

    /// Return true when the manifest validation failed closed.
    pub fn is_fail_closed(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::FailClosed
        )
    }
}

/// Stable replay identity for execution-authority manifest rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthorityReplayIdentity {
    /// Replay identity schema.
    pub schema: &'static str,
    /// Replay identity schema version.
    pub schema_version: u32,
    /// Number of required row keys included in the canonical identity text.
    pub required_key_count: usize,
    /// Number of parsed/emitted rows included in the canonical identity text.
    pub emitted_row_count: usize,
    /// Validation status carried through from the manifest validation report.
    pub validation_status: PetriNativeSuccessorExecutionAuthorityManifestValidationStatus,
    /// Validation reason carried through from the manifest validation report.
    pub validation_reason_code: Option<String>,
    /// Canonical JSON-free replay identity text.
    pub canonical_text: String,
    /// Stable digest of [`Self::canonical_text`].
    pub replay_identity_sha256: String,
    /// Full fail-closed manifest validation report used to build this identity.
    pub validation_report: PetriNativeSuccessorExecutionAuthorityManifestValidationReport,
}

impl PetriNativeSuccessorExecutionAuthorityReplayIdentity {
    /// Return true only when this replay identity validates to accepted authority.
    pub fn is_accepted(&self) -> bool {
        self.validation_report.is_accepted()
            && matches!(
                self.validation_status,
                PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::Accepted
            )
            && self.validation_reason_code.is_none()
    }

    /// Return true when the replay identity is fail-closed.
    pub fn is_fail_closed(&self) -> bool {
        self.validation_report.is_fail_closed()
    }

    /// Return a compact authority summary for downstream sidecar consumers.
    pub fn compact_summary(&self) -> PetriNativeSuccessorExecutionAuthoritySummary {
        PetriNativeSuccessorExecutionAuthoritySummary::from_replay_identity(self, None, None, None)
    }
}

/// Compact sidecar summary for Petri execution-authority manifest validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthoritySummary {
    /// Summary schema.
    pub schema: &'static str,
    /// Summary schema version.
    pub schema_version: u32,
    /// Execution-authority evidence schema.
    pub evidence_schema: &'static str,
    /// Execution-authority evidence schema version.
    pub evidence_schema_version: u32,
    /// Manifest validation schema.
    pub validation_schema: &'static str,
    /// Manifest validation schema version.
    pub validation_schema_version: u32,
    /// Replay identity schema.
    pub replay_identity_schema: &'static str,
    /// Replay identity schema version.
    pub replay_identity_schema_version: u32,
    /// Accepted only when Trust Codegen validated the authority manifest as accepted.
    pub validation_status: PetriNativeSuccessorExecutionAuthorityManifestValidationStatus,
    /// Stable validation reason code.
    pub validation_reason_code: Option<String>,
    /// Evidence status code observed in the authority rows.
    pub evidence_status_code: Option<String>,
    /// Evidence reason code observed in the authority rows.
    pub evidence_reason_code: Option<String>,
    /// True whenever Trust Codegen did not accept the authority rows.
    pub fail_closed: bool,
    /// True when the source rows explicitly authorized execution.
    pub authorized_for_execution: bool,
    /// True when the source rows explicitly authorized useful native execution.
    pub authorizes_useful_native: bool,
    /// Required row key count covered by replay identity.
    pub required_key_count: usize,
    /// Parsed/emitted authority row count covered by replay identity.
    pub emitted_row_count: usize,
    /// Populated diagnostic count from Trust Codegen manifest validation.
    pub diagnostic_count: usize,
    /// Missing required key count.
    pub missing_required_key_count: usize,
    /// Duplicate key count.
    pub duplicate_key_count: usize,
    /// Blank required value key count.
    pub blank_required_value_key_count: usize,
    /// Malformed line count.
    pub invalid_key_value_line_count: usize,
    /// Execution-authority decision digest observed in the source rows.
    pub execution_authority_sha256: Option<String>,
    /// Replay identity digest over the full source rows.
    pub replay_identity_sha256: String,
    /// Stable digest of [`Self::canonical_text`].
    pub summary_sha256: String,
}

impl PetriNativeSuccessorExecutionAuthoritySummary {
    /// Build a summary from an Trust Codegen-owned replay identity and optional source-row fields.
    pub fn from_replay_identity(
        replay: &PetriNativeSuccessorExecutionAuthorityReplayIdentity,
        authorized_for_execution: Option<bool>,
        authorizes_useful_native: Option<bool>,
        execution_authority_sha256: Option<String>,
    ) -> Self {
        let validation_report = &replay.validation_report;
        let replay_accepted = replay.is_accepted();
        let mut summary = Self {
            schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_SCHEMA,
            schema_version: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_SCHEMA_VERSION,
            evidence_schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA,
            evidence_schema_version: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA_VERSION,
            validation_schema:
                PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA,
            validation_schema_version:
                PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA_VERSION,
            replay_identity_schema:
                PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA,
            replay_identity_schema_version:
                PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA_VERSION,
            validation_status: replay.validation_status,
            validation_reason_code: replay.validation_reason_code.clone(),
            evidence_status_code: validation_report.evidence_status_code.clone(),
            evidence_reason_code: validation_report.evidence_reason_code.clone(),
            fail_closed: replay.is_fail_closed(),
            authorized_for_execution: authorized_for_execution.unwrap_or(replay_accepted),
            authorizes_useful_native: authorizes_useful_native.unwrap_or(replay_accepted),
            required_key_count: replay.required_key_count,
            emitted_row_count: replay.emitted_row_count,
            diagnostic_count: petri_native_successor_execution_authority_diagnostic_count(
                validation_report,
            ),
            missing_required_key_count: validation_report.missing_required_keys.len(),
            duplicate_key_count: validation_report.duplicate_keys.len(),
            blank_required_value_key_count: validation_report.blank_required_value_keys.len(),
            invalid_key_value_line_count: validation_report.invalid_key_value_line_count,
            execution_authority_sha256,
            replay_identity_sha256: replay.replay_identity_sha256.clone(),
            summary_sha256: String::new(),
        };
        summary.summary_sha256 =
            format!("sha256:{}", sha256_hex(summary.canonical_text().as_bytes()));
        summary
    }

    /// Return true only when Trust Codegen accepted the source authority manifest.
    pub fn is_accepted(&self) -> bool {
        matches!(
            self.validation_status,
            PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::Accepted
        ) && !self.fail_closed
            && self.validation_reason_code.is_none()
            && self.authorized_for_execution
            && self.authorizes_useful_native
    }

    /// Return true when Trust Codegen failed the source authority manifest closed.
    pub fn is_fail_closed(&self) -> bool {
        self.fail_closed
            || matches!(
                self.validation_status,
                PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::FailClosed
            )
    }

    /// Return stable summary text excluding the digest row itself.
    pub fn canonical_text(&self) -> String {
        let mut out = String::new();
        for row in self.manifest_rows_without_digest() {
            out.push_str(&row.to_key_value_line());
            out.push('\n');
        }
        out
    }

    /// Emit a compact line-oriented summary including its stable digest.
    pub fn summary_text(&self) -> String {
        let mut out = self.canonical_text();
        out.push_str(
            &PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "summary.sha256",
                self.summary_sha256.as_str(),
            )
            .to_key_value_line(),
        );
        out.push('\n');
        out
    }

    /// Emit deterministic summary rows including the digest row.
    pub fn manifest_rows(&self) -> Vec<PetriNativeSuccessorExecutionAuthoritySummaryRow> {
        let mut rows = self.manifest_rows_without_digest();
        rows.push(PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
            "summary.sha256",
            self.summary_sha256.as_str(),
        ));
        rows
    }

    /// Emit stable escaped `key=value` summary lines in [`Self::manifest_rows`] order.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .iter()
            .map(PetriNativeSuccessorExecutionAuthoritySummaryRow::to_key_value_line)
            .collect()
    }

    /// Emit a deterministic JSON object keyed by the stable summary row names.
    pub fn to_json_value(&self) -> serde_json::Value {
        let mut object = serde_json::Map::new();
        for row in self.manifest_rows() {
            object.insert(row.key, serde_json::Value::String(row.value));
        }
        serde_json::Value::Object(object)
    }

    /// Emit deterministic compact JSON for sidecar persistence.
    pub fn to_json_string(&self) -> String {
        self.to_json_value().to_string()
    }

    fn manifest_rows_without_digest(
        &self,
    ) -> Vec<PetriNativeSuccessorExecutionAuthoritySummaryRow> {
        vec![
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new("summary.schema", self.schema),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "summary.schema_version",
                self.schema_version.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "evidence.schema",
                self.evidence_schema,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "evidence.schema_version",
                self.evidence_schema_version.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "validation.schema",
                self.validation_schema,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "validation.schema_version",
                self.validation_schema_version.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "replay_identity.schema",
                self.replay_identity_schema,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "replay_identity.schema_version",
                self.replay_identity_schema_version.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "validation.status",
                self.validation_status.as_str(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "validation.reason_code",
                self.validation_reason_code.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "evidence.status",
                self.evidence_status_code.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "evidence.reason_code",
                self.evidence_reason_code.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "summary.fail_closed",
                petri_native_successor_bool_code(self.fail_closed),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "authority.authorized_for_execution",
                petri_native_successor_bool_code(self.authorized_for_execution),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "native.authorizes_useful_native",
                petri_native_successor_bool_code(self.authorizes_useful_native),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "summary.required_key_count",
                self.required_key_count.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "summary.emitted_row_count",
                self.emitted_row_count.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "summary.diagnostic_count",
                self.diagnostic_count.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "summary.missing_required_key_count",
                self.missing_required_key_count.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "summary.duplicate_key_count",
                self.duplicate_key_count.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "summary.blank_required_value_key_count",
                self.blank_required_value_key_count.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "summary.invalid_key_value_line_count",
                self.invalid_key_value_line_count.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "authority.execution_authority_sha256",
                self.execution_authority_sha256.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "replay_identity.sha256",
                self.replay_identity_sha256.as_str(),
            ),
        ]
    }
}

/// Stable key/value row for compact execution-authority summaries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthoritySummaryRow {
    /// Summary row key.
    pub key: String,
    /// Summary row value.
    pub value: String,
}

impl PetriNativeSuccessorExecutionAuthoritySummaryRow {
    /// Create a compact execution-authority summary row.
    pub fn new(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Escaped key for line-oriented `key=value` summary output.
    pub fn escaped_key(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented `key=value` summary output.
    pub fn escaped_value(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

/// Validation status for compact execution-authority summaries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PetriNativeSuccessorExecutionAuthoritySummaryValidationStatus {
    /// Summary rows exactly match Trust Codegen's source authority rows.
    Accepted,
    /// Summary rows are malformed, stale, incomplete, or mismatched.
    FailClosed,
}

impl PetriNativeSuccessorExecutionAuthoritySummaryValidationStatus {
    /// Return the stable summary validation status code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::FailClosed => "fail_closed",
        }
    }
}

/// Fail-closed validation report for compact execution-authority summaries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthoritySummaryValidationReport {
    /// Summary validation schema.
    pub schema: &'static str,
    /// Summary validation schema version.
    pub schema_version: u32,
    /// Accepted only when summary rows match the source authority manifest.
    pub status: PetriNativeSuccessorExecutionAuthoritySummaryValidationStatus,
    /// Stable reason code for fail-closed validation.
    pub reason_code: Option<String>,
    /// Summary digest expected from Trust Codegen's source authority rows.
    pub expected_summary_sha256: Option<String>,
    /// Summary digest observed in the persisted summary rows.
    pub observed_summary_sha256: Option<String>,
    /// Required summary row keys that were absent.
    pub missing_keys: Vec<String>,
    /// Duplicate summary row keys.
    pub duplicate_keys: Vec<String>,
    /// Schema/version keys whose values are stale.
    pub stale_schema_keys: Vec<String>,
    /// Summary keys whose values no longer match the source authority rows.
    pub mismatched_keys: Vec<String>,
    /// Unexpected summary row keys.
    pub unexpected_keys: Vec<String>,
    /// Number of malformed `key=value` lines seen by the line validator.
    pub invalid_key_value_line_count: usize,
}

impl PetriNativeSuccessorExecutionAuthoritySummaryValidationReport {
    /// Return true only when summary rows match Trust Codegen's source authority rows.
    pub fn is_accepted(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorExecutionAuthoritySummaryValidationStatus::Accepted
        ) && self.reason_code.is_none()
            && self.missing_keys.is_empty()
            && self.duplicate_keys.is_empty()
            && self.stale_schema_keys.is_empty()
            && self.mismatched_keys.is_empty()
            && self.unexpected_keys.is_empty()
            && self.invalid_key_value_line_count == 0
    }

    /// Return true when summary validation failed closed.
    pub fn is_fail_closed(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorExecutionAuthoritySummaryValidationStatus::FailClosed
        )
    }
}

/// Diagnostic/test fixture for Petri execution-authority sidecar replay.
///
/// These fixtures are deterministic reference rows for downstream smoke tests.
/// They are not native-install admission shortcuts and do not authorize runtime
/// execution by themselves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthorityDiagnosticFixture {
    /// Stable fixture name.
    pub fixture_name: &'static str,
    /// Fixture manifest rows.
    pub manifest_rows: Vec<PetriNativeSuccessorHandoffManifestRow>,
    /// Fixture manifest rows encoded as escaped `key=value` lines.
    pub manifest_key_value_lines: Vec<String>,
    /// Trust Codegen-owned validation report for the fixture rows.
    pub validation_report: PetriNativeSuccessorExecutionAuthorityManifestValidationReport,
    /// Trust Codegen-owned replay identity for the fixture rows.
    pub replay_identity: PetriNativeSuccessorExecutionAuthorityReplayIdentity,
}

impl PetriNativeSuccessorExecutionAuthorityDiagnosticFixture {
    /// Return true only when this diagnostic fixture validates as accepted evidence.
    pub fn is_accepted(&self) -> bool {
        self.validation_report.is_accepted() && self.replay_identity.is_accepted()
    }

    /// Return true when this diagnostic fixture validates as fail-closed evidence.
    pub fn is_fail_closed(&self) -> bool {
        self.validation_report.is_fail_closed() && self.replay_identity.is_fail_closed()
    }
}

/// Manifest describing the deterministic execution-authority diagnostic fixtures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifest {
    /// Fixture manifest schema.
    pub schema: &'static str,
    /// Fixture manifest schema version.
    pub schema_version: u32,
    /// Deterministic fixture entries.
    pub entries: Vec<PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestEntry>,
}

/// Expected diagnostic fixture outcome for downstream fixture discovery.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestEntry {
    /// Stable fixture name.
    pub fixture_name: &'static str,
    /// Expected Trust Codegen validation status.
    pub expected_validation_status: PetriNativeSuccessorExecutionAuthorityManifestValidationStatus,
    /// Whether the fixture is expected to validate fail-closed.
    pub expected_fail_closed: bool,
    /// Expected `evidence.status` row value.
    pub expected_evidence_status_code: &'static str,
    /// Expected validation reason code.
    pub expected_reason_code: Option<&'static str>,
    /// Expected `authority.authorized_for_execution` row value.
    pub expected_authorized_for_execution: bool,
    /// Expected `native.authorizes_useful_native` row value.
    pub expected_native_authorizes_useful_native: bool,
    /// Schemas exercised by this fixture's rows, validation report, and replay identity.
    pub exercised_schemas: &'static [&'static str],
}

impl PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifest {
    /// Emit deterministic key/value rows for downstream diagnostic fixture discovery.
    pub fn manifest_rows(
        &self,
    ) -> Vec<PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow> {
        let mut rows = vec![
            PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                "fixture_manifest.schema",
                self.schema,
            ),
            PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                "fixture_manifest.schema_version",
                self.schema_version.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                "fixture_manifest.entry_count",
                self.entries.len().to_string(),
            ),
        ];

        for (entry_index, entry) in self.entries.iter().enumerate() {
            let prefix = format!("fixture.{entry_index}");
            rows.push(
                PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                    format!("{prefix}.name"),
                    entry.fixture_name,
                ),
            );
            rows.push(
                PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                    format!("{prefix}.expected.validation_status"),
                    entry.expected_validation_status.as_str(),
                ),
            );
            rows.push(
                PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                    format!("{prefix}.expected.fail_closed"),
                    petri_native_successor_bool_code(entry.expected_fail_closed),
                ),
            );
            rows.push(
                PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                    format!("{prefix}.expected.evidence_status"),
                    entry.expected_evidence_status_code,
                ),
            );
            rows.push(
                PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                    format!("{prefix}.expected.reason_code"),
                    entry.expected_reason_code.unwrap_or(""),
                ),
            );
            rows.push(
                PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                    format!("{prefix}.expected.authorized_for_execution"),
                    petri_native_successor_bool_code(entry.expected_authorized_for_execution),
                ),
            );
            rows.push(
                PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                    format!("{prefix}.expected.native_authorizes_useful_native"),
                    petri_native_successor_bool_code(
                        entry.expected_native_authorizes_useful_native,
                    ),
                ),
            );
            rows.push(
                PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                    format!("{prefix}.exercised_schema_count"),
                    entry.exercised_schemas.len().to_string(),
                ),
            );
            for (schema_index, schema) in entry.exercised_schemas.iter().enumerate() {
                rows.push(
                    PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::new(
                        format!("{prefix}.exercised_schema.{schema_index}"),
                        *schema,
                    ),
                );
            }
        }

        rows
    }

    /// Emit stable escaped `key=value` rows in [`Self::manifest_rows`] order.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .iter()
            .map(PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow::to_key_value_line)
            .collect()
    }
}

/// Stable key/value row for diagnostic fixture manifest discovery.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow {
    /// Manifest row key.
    pub key: String,
    /// Manifest row value.
    pub value: String,
}

impl PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow {
    /// Create a diagnostic fixture manifest row.
    pub fn new(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Escaped key for line-oriented `key=value` manifest output.
    pub fn escaped_key(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented `key=value` manifest output.
    pub fn escaped_value(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

/// Fail-closed validation report for diagnostic fixture manifest rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestValidationReport {
    /// Validation report schema.
    pub schema: &'static str,
    /// Validation report schema version.
    pub schema_version: u32,
    /// Accepted only when the fixture manifest exactly matches Trust Codegen-owned fixture metadata.
    pub status: PetriNativeSuccessorExecutionAuthorityManifestValidationStatus,
    /// Stable reason code for fail-closed validation.
    pub reason_code: Option<String>,
    /// Expected manifest keys that were absent.
    pub missing_keys: Vec<String>,
    /// Expected fixture entries whose name row was absent.
    pub missing_fixture_names: Vec<&'static str>,
    /// Expected manifest keys whose value did not match.
    pub mismatched_keys: Vec<String>,
    /// Duplicate row keys. Any duplicate makes the manifest ambiguous and fail-closed.
    pub duplicate_keys: Vec<String>,
    /// Unknown row keys. Any unknown key makes the manifest fail-closed.
    pub unexpected_keys: Vec<String>,
    /// Number of malformed `key=value` lines seen by the line validator.
    pub invalid_key_value_line_count: usize,
}

impl PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestValidationReport {
    /// Return true only when the fixture manifest validates to accepted discovery metadata.
    pub fn is_accepted(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::Accepted
        ) && self.reason_code.is_none()
            && self.missing_keys.is_empty()
            && self.missing_fixture_names.is_empty()
            && self.mismatched_keys.is_empty()
            && self.duplicate_keys.is_empty()
            && self.unexpected_keys.is_empty()
            && self.invalid_key_value_line_count == 0
    }

    /// Return true when the fixture manifest validation failed closed.
    pub fn is_fail_closed(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::FailClosed
        )
    }
}

/// Required inputs for [`petri_native_successor_semantic_bridge_evidence_from_trust_ir_bundle`].
pub const PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_REQUIRED_FIELDS: &[&str] = &[
    "trust_ir_bundle",
    "entry_function",
    "semantic_successor_obligation",
    "native_evidence_bundle",
];

/// Stable statuses emitted by [`PetriNativeSuccessorSemanticBridgeEvidence`].
pub const PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_STATUS_CODES: &[&str] = &["ready", "blocked"];

/// Stable blocker codes emitted by [`PetriNativeSuccessorSemanticBridgeEvidence`].
pub const PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_BLOCKER_CODES: &[&str] = &[
    "bundle_validation_failed",
    "missing_entry_function",
    "missing_semantic_successor_obligation",
    "missing_semantic_successor_evidence",
];

/// trust_ir-owned native-bundle identity contract used by Petri/MCC native handoff descriptors.
pub const PETRI_NATIVE_SUCCESSOR_TRUST_IR_BUNDLE_IDENTITY_DESCRIPTOR:
    trust_ir::NativeBundleIdentityContractDescriptor =
    trust_ir::NATIVE_BUNDLE_IDENTITY_CONTRACT_DESCRIPTOR;

/// trust_ir-owned Petri/trust-mc CHC report contract used by Petri/MCC semantic bridge evidence.
pub const PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_CONTRACT_DESCRIPTOR:
    trust_ir::PetriSuccessorTrustMcChcContractDescriptor =
    trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_DESCRIPTOR;

/// trust_ir-owned shared primitive descriptor for Petri/trust-mc model acceptance.
pub const PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR:
    trust_ir::NativeSharedPrimitiveContractDescriptor =
    trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR;

/// Stable state encoding for the first Petri/MCC native successor ABI.
pub const PETRI_NATIVE_SUCCESSOR_STATE_ENCODING_STABLE_BYTES_V1: &str =
    "petri_state_stable_bytes_v1";

/// Stable trampoline ABI for Petri/MCC native successor entrypoints.
pub const PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_ABI_STABLE_BYTES_V1: &str =
    "trust_cg_petri_successor_stable_bytes_v1";

/// Stable schema tag for structured native install gate events.
pub const NATIVE_INSTALL_GATE_EVENT_SCHEMA: &str =
    "trust-cg.phase6.native_install_gate.structured_event.v1";

/// Stable numeric schema version for structured native install gate events.
pub const NATIVE_INSTALL_GATE_EVENT_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for non-promoting product-promotion packets.
pub const NATIVE_INSTALL_GATE_PRODUCT_PROMOTION_PACKET_SCHEMA: &str =
    "trust-cg.phase6.native_install_gate.product_promotion_packet.v1";

/// Stable numeric schema version for non-promoting product-promotion packets.
pub const NATIVE_INSTALL_GATE_PRODUCT_PROMOTION_PACKET_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for replay identity records bound to install packets.
pub const NATIVE_INSTALL_GATE_REPLAY_SCHEMA: &str =
    "trust-cg.phase6.native_install_gate.replay_identity.v1";

/// Stable numeric schema version for replay identity records.
pub const NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION: u32 = 1;

/// Stable TY consumer mode for native fused parent-loop activation.
pub const TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE: &str = "native-fused-parent-loop";

/// Stable TY native fused parent-loop manifest schema.
pub const TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA: &str =
    "trust-cg.ty.native_fused_parent_loop_manifest/v1";

/// Stable TY native fused parent-loop status/deopt contract metadata value.
pub const TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT: &str =
    "ty.native_fused_parent_loop.status_deopt_abi.v1";

/// Stable proof-evidence metadata value for a verified TY proof fact.
pub const TY_NATIVE_FUSED_PROOF_FACT_VERIFIED: &str = "verified";

/// Stable proof-evidence metadata value for a missing TY proof fact.
pub const TY_NATIVE_FUSED_PROOF_FACT_MISSING: &str = "missing";

/// Stable proof-evidence metadata key for the TY manifest checksum.
pub const TY_NATIVE_FUSED_EVIDENCE_MANIFEST_IDENTITY_KEY: &str =
    "ty.native_fused.manifest_identity";

/// Stable proof-evidence metadata key for the TY certificate identity.
pub const TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY: &str =
    "ty.native_fused.certificate_identity";

/// Stable proof-evidence metadata key for the replay root.
pub const TY_NATIVE_FUSED_EVIDENCE_REPLAY_ROOT_KEY: &str = "ty.native_fused.replay_root_sha256";

/// Stable proof-evidence metadata key for the decision telemetry event id.
pub const TY_NATIVE_FUSED_EVIDENCE_TELEMETRY_EVENT_KEY: &str = "ty.native_fused.telemetry_event_id";

/// Stable proof-evidence metadata key for the install/admission gate result.
pub const TY_NATIVE_FUSED_EVIDENCE_GATE_RESULT_KEY: &str = "ty.native_fused.gate_result_sha256";

/// Stable proof-evidence metadata key for the proof or validation report hash.
pub const TY_NATIVE_FUSED_EVIDENCE_VALIDATION_HASH_KEY: &str =
    "ty.native_fused.proof_validation_sha256";

/// Stable proof-evidence metadata key for a typed missing TY proof fact.
pub const TY_NATIVE_FUSED_EVIDENCE_MISSING_FACT_KEY: &str = "ty.native_fused.missing_fact";

/// Stable proof-evidence metadata key for the non-promoting missing-proof disposition.
pub const TY_NATIVE_FUSED_EVIDENCE_MISSING_DISPOSITION_KEY: &str =
    "ty.native_fused.missing_disposition";

/// Stable non-promoting disposition recorded for incomplete TY proof evidence.
pub const TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION: &str =
    "reject_non_promoting_useful_native_false";

/// Stable metadata keys for the proof facts required by TY native fused parent loops.
pub const TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA: &[(&str, &str)] = &[
    (
        "ty.native_fused.fact.state_layout_stability",
        "state_layout_stability",
    ),
    (
        "ty.native_fused.fact.helper_purity_readonly",
        "helper_purity_readonly",
    ),
    (
        "ty.native_fused.fact.action_independence_or_fused_step_equivalence",
        "action_independence_or_fused_step_equivalence",
    ),
    (
        "ty.native_fused.fact.state_vector_bounds",
        "state_vector_bounds",
    ),
    (
        "ty.native_fused.fact.dispatch_panic_deopt_safety",
        "dispatch_panic_deopt_safety",
    ),
];

const TY_NATIVE_FUSED_REQUIRED_EVIDENCE_REF_KEYS: &[&str] = &[
    TY_NATIVE_FUSED_EVIDENCE_MANIFEST_IDENTITY_KEY,
    TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY,
    TY_NATIVE_FUSED_EVIDENCE_REPLAY_ROOT_KEY,
    TY_NATIVE_FUSED_EVIDENCE_TELEMETRY_EVENT_KEY,
    TY_NATIVE_FUSED_EVIDENCE_GATE_RESULT_KEY,
    TY_NATIVE_FUSED_EVIDENCE_VALIDATION_HASH_KEY,
];

const TY_NATIVE_FUSED_MANIFEST_SCHEMA_KEY: &str = "ty_manifest_schema";
const TY_NATIVE_FUSED_STATUS_DEOPT_CONTRACT_KEY: &str = "status_deopt_contract";
const TY_NATIVE_FUSED_KERNEL_IDENTITY_KEY: &str = "native_fused_kernel_identity";
pub const TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY: &str =
    "native_fused_transition_cluster_descriptor_identity";
const TY_NATIVE_FUSED_DEOPT_ROLLBACK_CONDITION_KEY: &str = "deopt_rollback_condition";
const TY_NATIVE_FUSED_DEOPT_ROLLBACK_CONDITION: &str =
    "status_deopt_or_dispatch_panic_before_successor_commit";
const TY_NATIVE_FUSED_MISSING_PROOF_DISPOSITION_KEY: &str = "missing_proof_disposition";
const TY_NATIVE_FUSED_USEFUL_NATIVE_POLICY_KEY: &str = "useful_native";
const TY_NATIVE_FUSED_USEFUL_NATIVE_FALSE_UNTIL_GATE: &str = "false_until_gate_accepts";
const TY_NATIVE_FUSED_PROOF_OPT_TRANSFORM_NAME: &str = "ty-native-fused-parent-loop";
const TY_NATIVE_FUSED_PROOF_OPT_TRANSFORM_VERSION: u32 = 1;
const TY_NATIVE_FUSED_PROOF_OPT_ADMISSION: &str = "proof-annotation+proof-facts";
const TY_NATIVE_FUSED_PROOF_OPT_KIND: &str = "TyNativeFusedParentLoop";

/// Stable native install disposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeInstallGateDisposition {
    /// The candidate has complete evidence and may be installed by the caller.
    Installable,
    /// The candidate can be retained only for profiling/audit data.
    ProfileOnly,
    /// The candidate can be retained only for replay evidence.
    ReplayOnly,
    /// The candidate can run only where baseline remains authoritative.
    ShadowOnly,
    /// The candidate failed closed.
    Rejected,
}

impl NativeInstallGateDisposition {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Installable => "installable",
            Self::ProfileOnly => "profile_only",
            Self::ReplayOnly => "replay_only",
            Self::ShadowOnly => "shadow_only",
            Self::Rejected => "rejected",
        }
    }

    /// Return true only for installable candidates.
    pub const fn is_installable(self) -> bool {
        matches!(self, Self::Installable)
    }
}

/// Stable native install rejection code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeInstallGateRejectionCode {
    /// Required manifest or manifest reference is absent.
    MissingManifest,
    /// A schema name or version is unsupported.
    UnsupportedSchema,
    /// The consumer is outside this slice's ay/TY allowlist.
    UnsupportedConsumer,
    /// Manifest reference and full manifest do not bind the same checksum.
    ManifestChecksumMismatch,
    /// Artifact id or payload hash binding mismatched.
    ArtifactIdentityMismatch,
    /// Target checksum mismatched.
    TargetMismatch,
    /// ABI checksum mismatched.
    AbiMismatch,
    /// Layout checksum or layout evidence mismatched.
    LayoutMismatch,
    /// Required layout evidence is absent.
    MissingLayoutEvidence,
    /// Required proof or translation-validation evidence is absent.
    ProofMissingEvidence,
    /// Proof or translation validation rejected the artifact.
    ProofVerifierFailure,
    /// Proof or translation validation timed out.
    ProofTimeout,
    /// Proof or translation validation returned unknown.
    ProofUnknown,
    /// Proof or translation validation solver execution failed.
    ProofSolverError,
    /// Proof evidence cannot be produced on this compile route.
    ProofUnsupportedRoute,
    /// Proof evidence cannot cover this target or route.
    ProofUnsupportedTarget,
    /// Proof evidence is stale.
    ProofStaleEvidence,
    /// Proof evidence report was malformed.
    ProofMalformedReport,
    /// Proof evidence report omitted required fields.
    ProofMissingRequiredFields,
    /// Current invalidation key or generation is stale.
    StaleInvalidation,
    /// Decision telemetry is absent.
    MissingTelemetry,
    /// Decision telemetry does not bind this decision.
    TelemetryMismatch,
    /// Replay identity metadata is absent.
    MissingReplayIdentity,
    /// Replay identity metadata does not bind this decision.
    ReplayIdentityMismatch,
    /// The artifact or one of its install scopes is revoked.
    RevokedArtifact,
    /// Profile-only candidates are not installable.
    ProfileOnlyNonInstallable,
    /// Replay-only candidates are not installable.
    ReplayOnlyNonInstallable,
    /// Shadow-only candidates are not installable.
    ShadowOnlyNonInstallable,
    /// A packet hash was required but absent.
    MissingPacketHash,
    /// The supplied packet hash does not match the canonical packet hash.
    PacketHashMismatch,
    /// Disposition, authority, and action booleans are internally inconsistent.
    InconsistentActionAuthority,
    /// Persisted replay, consumer verdict, or telemetry binding does not match the packet.
    EvidenceBindingMismatch,
    /// A persisted rejection code was not recognized by this schema.
    UnknownRejectionCode,
    /// A kill switch disabled callable native dispatch for this scope.
    KillSwitchActive,
    /// A Petri trust_ir native successor bundle failed trust_ir validation.
    PetriTrustIrBundleValidationFailed,
    /// A Petri trust_ir native successor bundle did not carry native evidence.
    MissingNativeEvidenceBundle,
    /// No native install-gate packet was available for Petri admission.
    MissingNativeInstallGatePacket,
    /// Petri native successor target ABI identity mismatched the expected ABI.
    TargetAbiMismatch,
    /// Petri proof replay identity did not bind the supplied install packet.
    ProofReplayIdentityMismatch,
    /// Petri native successor consumer admission was denied.
    ConsumerAdmissionDenied,
}

impl NativeInstallGateRejectionCode {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingManifest => "missing_manifest",
            Self::UnsupportedSchema => "unsupported_schema",
            Self::UnsupportedConsumer => "unsupported_consumer",
            Self::ManifestChecksumMismatch => "manifest_checksum_mismatch",
            Self::ArtifactIdentityMismatch => "artifact_identity_mismatch",
            Self::TargetMismatch => "target_mismatch",
            Self::AbiMismatch => "abi_mismatch",
            Self::LayoutMismatch => "layout_mismatch",
            Self::MissingLayoutEvidence => "missing_layout_evidence",
            Self::ProofMissingEvidence => "proof_missing_evidence",
            Self::ProofVerifierFailure => "proof_verifier_failure",
            Self::ProofTimeout => "proof_timeout",
            Self::ProofUnknown => "proof_unknown",
            Self::ProofSolverError => "proof_solver_error",
            Self::ProofUnsupportedRoute => "proof_unsupported_route",
            Self::ProofUnsupportedTarget => "proof_unsupported_target",
            Self::ProofStaleEvidence => "proof_stale_evidence",
            Self::ProofMalformedReport => "proof_malformed_report",
            Self::ProofMissingRequiredFields => "proof_missing_required_fields",
            Self::StaleInvalidation => "stale_invalidation",
            Self::MissingTelemetry => "missing_telemetry",
            Self::TelemetryMismatch => "telemetry_mismatch",
            Self::MissingReplayIdentity => "missing_replay_identity",
            Self::ReplayIdentityMismatch => "replay_identity_mismatch",
            Self::RevokedArtifact => "revoked_artifact",
            Self::ProfileOnlyNonInstallable => "profile_only_non_installable",
            Self::ReplayOnlyNonInstallable => "replay_only_non_installable",
            Self::ShadowOnlyNonInstallable => "shadow_only_non_installable",
            Self::MissingPacketHash => "missing_packet_hash",
            Self::PacketHashMismatch => "packet_hash_mismatch",
            Self::InconsistentActionAuthority => "inconsistent_action_authority",
            Self::EvidenceBindingMismatch => "evidence_binding_mismatch",
            Self::UnknownRejectionCode => "unknown_rejection_code",
            Self::KillSwitchActive => "kill_switch_active",
            Self::PetriTrustIrBundleValidationFailed => "petri_trust_ir_bundle_validation_failed",
            Self::MissingNativeEvidenceBundle => "missing_native_evidence_bundle",
            Self::MissingNativeInstallGatePacket => "missing_native_install_gate_packet",
            Self::TargetAbiMismatch => "target_abi_mismatch",
            Self::ProofReplayIdentityMismatch => "proof_replay_identity_mismatch",
            Self::ConsumerAdmissionDenied => "consumer_admission_denied",
        }
    }

    /// Parse a stable lower-snake-case rejection code.
    ///
    /// Unknown persisted strings are represented as `UnknownRejectionCode` so
    /// packet ingestion can fail closed instead of silently accepting future
    /// schemas it does not understand.
    pub fn parse_stable(value: &str) -> Self {
        match value {
            "missing_manifest" => Self::MissingManifest,
            "unsupported_schema" => Self::UnsupportedSchema,
            "unsupported_consumer" => Self::UnsupportedConsumer,
            "manifest_checksum_mismatch" => Self::ManifestChecksumMismatch,
            "artifact_identity_mismatch" => Self::ArtifactIdentityMismatch,
            "target_mismatch" => Self::TargetMismatch,
            "abi_mismatch" => Self::AbiMismatch,
            "layout_mismatch" => Self::LayoutMismatch,
            "missing_layout_evidence" => Self::MissingLayoutEvidence,
            "proof_missing_evidence" => Self::ProofMissingEvidence,
            "proof_verifier_failure" => Self::ProofVerifierFailure,
            "proof_timeout" => Self::ProofTimeout,
            "proof_unknown" => Self::ProofUnknown,
            "proof_solver_error" => Self::ProofSolverError,
            "proof_unsupported_route" => Self::ProofUnsupportedRoute,
            "proof_unsupported_target" => Self::ProofUnsupportedTarget,
            "proof_stale_evidence" => Self::ProofStaleEvidence,
            "proof_malformed_report" => Self::ProofMalformedReport,
            "proof_missing_required_fields" => Self::ProofMissingRequiredFields,
            "stale_invalidation" => Self::StaleInvalidation,
            "missing_telemetry" => Self::MissingTelemetry,
            "telemetry_mismatch" => Self::TelemetryMismatch,
            "missing_replay_identity" => Self::MissingReplayIdentity,
            "replay_identity_mismatch" => Self::ReplayIdentityMismatch,
            "revoked_artifact" => Self::RevokedArtifact,
            "profile_only_non_installable" => Self::ProfileOnlyNonInstallable,
            "replay_only_non_installable" => Self::ReplayOnlyNonInstallable,
            "shadow_only_non_installable" => Self::ShadowOnlyNonInstallable,
            "missing_packet_hash" => Self::MissingPacketHash,
            "packet_hash_mismatch" => Self::PacketHashMismatch,
            "inconsistent_action_authority" => Self::InconsistentActionAuthority,
            "evidence_binding_mismatch" => Self::EvidenceBindingMismatch,
            "unknown_rejection_code" => Self::UnknownRejectionCode,
            "kill_switch_active" => Self::KillSwitchActive,
            "petri_trust_ir_bundle_validation_failed" => Self::PetriTrustIrBundleValidationFailed,
            "missing_native_evidence_bundle" => Self::MissingNativeEvidenceBundle,
            "missing_native_install_gate_packet" => Self::MissingNativeInstallGatePacket,
            "target_abi_mismatch" => Self::TargetAbiMismatch,
            "proof_replay_identity_mismatch" => Self::ProofReplayIdentityMismatch,
            "consumer_admission_denied" => Self::ConsumerAdmissionDenied,
            _ => Self::UnknownRejectionCode,
        }
    }
}

/// Product surface asking for install authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeInstallGateSurface {
    /// Direct compile response install.
    DirectCompileInstall,
    /// Typed symbol lookup boundary.
    TypedSymbolLookup,
    /// Async poll state publication.
    AsyncPoll,
    /// Installable cache insertion.
    CacheInsert,
    /// Installable cache hit.
    CacheHit,
    /// Release/replay bundle install decision.
    ReleaseBundle,
    /// ay registry insertion.
    AYRegistry,
    /// TY native activation.
    TyActivation,
    /// Petri/MCC native successor admission.
    NativeSuccessor,
}

/// Stable reason a surface does or does not expose a trust_ir shared-primitive contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NativeInstallGateSharedPrimitiveContractReason {
    /// The surface is itself a trust_ir native shared primitive.
    NativeSharedPrimitive,
    /// The surface is a generic direct install boundary, not a typed shared primitive.
    GenericInstallBoundary,
    /// The surface is a typed symbol lookup boundary, not a typed shared primitive.
    TypedSymbolLookupBoundary,
    /// The surface publishes async metadata, not a typed shared primitive.
    AsyncMetadataBoundary,
    /// The surface validates cache insertion, not a typed shared primitive.
    CacheInsertBoundary,
    /// The surface validates cache hits, not a typed shared primitive.
    CacheHitBoundary,
    /// The surface validates release metadata, not a typed shared primitive.
    ReleaseMetadataBoundary,
    /// The surface validates product registry publication, not a typed shared primitive.
    ProductRegistryBoundary,
    /// The surface validates product activation, not a typed shared primitive.
    ProductActivationBoundary,
}

impl NativeInstallGateSharedPrimitiveContractReason {
    /// Return the stable lower-snake-case reason code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NativeSharedPrimitive => "native_shared_primitive",
            Self::GenericInstallBoundary => "generic_install_boundary",
            Self::TypedSymbolLookupBoundary => "typed_symbol_lookup_boundary",
            Self::AsyncMetadataBoundary => "async_metadata_boundary",
            Self::CacheInsertBoundary => "cache_insert_boundary",
            Self::CacheHitBoundary => "cache_hit_boundary",
            Self::ReleaseMetadataBoundary => "release_metadata_boundary",
            Self::ProductRegistryBoundary => "product_registry_boundary",
            Self::ProductActivationBoundary => "product_activation_boundary",
        }
    }
}

impl NativeInstallGateSurface {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DirectCompileInstall => "direct_compile_install",
            Self::TypedSymbolLookup => "typed_symbol_lookup",
            Self::AsyncPoll => "async_poll",
            Self::CacheInsert => "cache_insert",
            Self::CacheHit => "cache_hit",
            Self::ReleaseBundle => "release_bundle",
            Self::AYRegistry => "ay_registry",
            Self::TyActivation => "ty_activation",
            Self::NativeSuccessor => "native_successor",
        }
    }

    /// Return the trust_ir shared-primitive contract owned by this install surface.
    pub const fn shared_primitive_contract(
        self,
    ) -> Option<trust_ir::NativeSharedPrimitiveContractDescriptor> {
        match self {
            Self::NativeSuccessor => {
                Some(PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR)
            }
            Self::DirectCompileInstall
            | Self::TypedSymbolLookup
            | Self::AsyncPoll
            | Self::CacheInsert
            | Self::CacheHit
            | Self::ReleaseBundle
            | Self::AYRegistry
            | Self::TyActivation => None,
        }
    }

    /// Return the stable reason for this surface's shared-primitive contract behavior.
    pub const fn shared_primitive_contract_reason(
        self,
    ) -> NativeInstallGateSharedPrimitiveContractReason {
        match self {
            Self::NativeSuccessor => {
                NativeInstallGateSharedPrimitiveContractReason::NativeSharedPrimitive
            }
            Self::DirectCompileInstall => {
                NativeInstallGateSharedPrimitiveContractReason::GenericInstallBoundary
            }
            Self::TypedSymbolLookup => {
                NativeInstallGateSharedPrimitiveContractReason::TypedSymbolLookupBoundary
            }
            Self::AsyncPoll => {
                NativeInstallGateSharedPrimitiveContractReason::AsyncMetadataBoundary
            }
            Self::CacheInsert => {
                NativeInstallGateSharedPrimitiveContractReason::CacheInsertBoundary
            }
            Self::CacheHit => NativeInstallGateSharedPrimitiveContractReason::CacheHitBoundary,
            Self::ReleaseBundle => {
                NativeInstallGateSharedPrimitiveContractReason::ReleaseMetadataBoundary
            }
            Self::AYRegistry => {
                NativeInstallGateSharedPrimitiveContractReason::ProductRegistryBoundary
            }
            Self::TyActivation => {
                NativeInstallGateSharedPrimitiveContractReason::ProductActivationBoundary
            }
        }
    }
}

/// Stable structured event kind for install-gate telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeInstallGateEventKind {
    /// Accepted event.
    Accepted,
    /// Generic rejected event.
    Rejected,
    /// Persisted packet, binding, or current identity invalidated the event.
    Invalidated,
    /// Native execution was rolled back or fell back before useful-native credit.
    RolledBack,
    /// Shadow execution observed a mismatch.
    ShadowMismatch,
    /// Proof or verifier timed out.
    VerifierTimeout,
    /// Proof or verifier returned unknown.
    ProofUnknown,
    /// Generation or invalidation evidence was stale.
    StaleGeneration,
    /// Artifact or scope revocation was observed.
    Revoked,
    /// Kill switch was active.
    KillSwitch,
}

impl NativeInstallGateEventKind {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
            Self::Invalidated => "invalidated",
            Self::RolledBack => "rolled_back",
            Self::ShadowMismatch => "shadow_mismatch",
            Self::VerifierTimeout => "verifier_timeout",
            Self::ProofUnknown => "proof_unknown",
            Self::StaleGeneration => "stale_generation",
            Self::Revoked => "revoked",
            Self::KillSwitch => "kill_switch",
        }
    }
}

/// Stable runtime outcome for a native dispatch attempt after revalidation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeInstallGateRuntimeOutcome {
    /// A native call completed and may count as useful native.
    NativeUseful,
    /// A callable packet was current, but execution routed back to baseline.
    BaselineFallback,
    /// The packet surface is metadata-only and did not represent a native call.
    MetadataOnly,
    /// Runtime revalidation observed stale freshness or proof evidence.
    StaleDeopt,
    /// Runtime revalidation observed revocation.
    RevokedDeopt,
    /// Runtime revalidation observed an active kill switch.
    KillSwitchDeopt,
    /// Runtime revalidation observed tampered or mismatched packet identity.
    InvalidatedDeopt,
    /// Runtime revalidation rejected for any other fail-closed reason.
    RejectedDeopt,
}

impl NativeInstallGateRuntimeOutcome {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NativeUseful => "native_useful",
            Self::BaselineFallback => "baseline_fallback",
            Self::MetadataOnly => "metadata_only",
            Self::StaleDeopt => "stale_deopt",
            Self::RevokedDeopt => "revoked_deopt",
            Self::KillSwitchDeopt => "kill_switch_deopt",
            Self::InvalidatedDeopt => "invalidated_deopt",
            Self::RejectedDeopt => "rejected_deopt",
        }
    }
}

/// Stable source that emitted a structured native install gate event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeInstallGateEventSource {
    /// Install-gate packet validation.
    InstallDecision,
    /// Runtime native-call revalidation.
    RuntimeCall,
    /// ay/TY consumer admission.
    ConsumerAdmission,
    /// Shadow replay comparison.
    ShadowReplay,
}

impl NativeInstallGateEventSource {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::InstallDecision => "install_decision",
            Self::RuntimeCall => "runtime_call",
            Self::ConsumerAdmission => "consumer_admission",
            Self::ShadowReplay => "shadow_replay",
        }
    }
}

/// Requested or confirmed install authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeInstallGateAuthority {
    /// No native install authority.
    None,
    /// Shadow-only authority.
    ShadowOnly,
    /// Callable canary authority.
    CanaryCallable,
    /// Active callable authority.
    ActiveCallable,
    /// Metadata-only validation authority without callable/native activation.
    ValidationOnly,
}

impl NativeInstallGateAuthority {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::ShadowOnly => "shadow_only",
            Self::CanaryCallable => "canary_callable",
            Self::ActiveCallable => "active_callable",
            Self::ValidationOnly => "validation_only",
        }
    }

    /// Return true when this authority can publish product-callable native dispatch.
    pub const fn is_callable(self) -> bool {
        matches!(self, Self::CanaryCallable | Self::ActiveCallable)
    }
}

/// Stable deny-control reason for freshness/revocation/kill-switch packets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeInstallGateDenyReason {
    /// One or more freshness domains observed a stale generation.
    StaleFreshness,
    /// The artifact or matching scope is revoked.
    Revoked,
    /// A kill switch is active for the matching scope.
    KillSwitch,
}

impl NativeInstallGateDenyReason {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::StaleFreshness => "stale_freshness",
            Self::Revoked => "revoked",
            Self::KillSwitch => "kill_switch",
        }
    }

    /// Return the install-gate rejection code for this deny reason.
    pub const fn rejection_code(self) -> NativeInstallGateRejectionCode {
        match self {
            Self::StaleFreshness => NativeInstallGateRejectionCode::StaleInvalidation,
            Self::Revoked => NativeInstallGateRejectionCode::RevokedArtifact,
            Self::KillSwitch => NativeInstallGateRejectionCode::KillSwitchActive,
        }
    }
}

/// Stable scope for deny-only freshness/revocation/kill-switch packets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeInstallGateDenyScope {
    /// Applies to all consumers, modes, surfaces, and artifacts.
    Global,
    /// Applies to one downstream consumer.
    Consumer,
    /// Applies to one consumer family/mode.
    Family,
    /// Applies to one artifact id.
    Artifact,
    /// Applies to one target/proof-policy tuple.
    TargetProofPolicy,
    /// Applies to one requested authority/mode.
    Mode,
    /// Applies to one install surface.
    Surface,
}

impl NativeInstallGateDenyScope {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Global => "global",
            Self::Consumer => "consumer",
            Self::Family => "family",
            Self::Artifact => "artifact",
            Self::TargetProofPolicy => "target_proof_policy",
            Self::Mode => "mode",
            Self::Surface => "surface",
        }
    }
}

/// Freshness-domain generation observation carried by deny-control prework.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateFreshnessObservation {
    /// Stable freshness domain, such as `ty_runtime` or `ay_solver`.
    pub domain: String,
    /// Generation bound by the candidate packet.
    pub observed_generation: u64,
    /// Current generation observed by the control plane.
    pub current_generation: u64,
}

impl NativeInstallGateFreshnessObservation {
    /// Build one freshness-domain observation.
    pub fn new(
        domain: impl Into<String>,
        observed_generation: u64,
        current_generation: u64,
    ) -> Self {
        Self {
            domain: domain.into(),
            observed_generation,
            current_generation,
        }
    }

    /// Return true when the candidate generation is stale.
    pub const fn is_stale(&self) -> bool {
        self.observed_generation != self.current_generation
    }
}

const SHARED_FRESHNESS_DOMAINS: &[&str] = &[
    "shared_artifact",
    "shared_proof_policy",
    "shared_target_abi",
    "shared_release_bundle",
    "shared_revocation",
    "shared_kill_switch",
];

const TY_FRESHNESS_DOMAINS: &[&str] = &[
    "ty_runtime",
    "ty_action",
    "ty_invariant",
    "ty_liveness",
    "ty_fingerprint",
    "ty_flat_state",
    "ty_helper_abi",
    "ty_library_publication",
];

const AY_FRESHNESS_DOMAINS: &[&str] = &[
    "ay_solver",
    "ay_sparse",
    "ay_basis",
    "ay_watch_list",
    "ay_proof_witness",
    "ay_rollback",
    "ay_registry",
];

/// Deny-only control-plane packet for freshness, revocation, and kill-switch state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateDenyControlPlane {
    /// Whether this control-plane packet currently denies matching requests.
    pub active: bool,
    /// Deny reason.
    pub reason: NativeInstallGateDenyReason,
    /// Deny scope.
    pub scope: NativeInstallGateDenyScope,
    /// Optional matching consumer.
    pub consumer: Option<String>,
    /// Optional matching consumer family or mode.
    pub family: Option<String>,
    /// Optional matching artifact id.
    pub artifact_id: Option<String>,
    /// Optional matching requested authority/mode.
    pub mode: Option<NativeInstallGateAuthority>,
    /// Optional matching surface.
    pub surface: Option<NativeInstallGateSurface>,
    /// Optional matching target checksum.
    pub target_checksum: Option<ArtifactChecksum>,
    /// Optional matching proof-policy checksum.
    pub proof_policy_checksum: Option<ArtifactChecksum>,
    /// Freshness-domain observations bound to this deny packet.
    pub freshness: Vec<NativeInstallGateFreshnessObservation>,
    /// Canonical deny-control packet hash.
    pub deny_sha256: Option<String>,
}

impl NativeInstallGateDenyControlPlane {
    /// Build an active deny-control packet for the given scope and reason.
    pub fn active(scope: NativeInstallGateDenyScope, reason: NativeInstallGateDenyReason) -> Self {
        Self {
            active: true,
            reason,
            scope,
            consumer: None,
            family: None,
            artifact_id: None,
            mode: None,
            surface: None,
            target_checksum: None,
            proof_policy_checksum: None,
            freshness: Vec::new(),
            deny_sha256: None,
        }
    }

    /// Build an inactive deny-control packet for the given scope and reason.
    pub fn inactive(
        scope: NativeInstallGateDenyScope,
        reason: NativeInstallGateDenyReason,
    ) -> Self {
        Self {
            active: false,
            ..Self::active(scope, reason)
        }
    }

    /// Return the stable hash of the deny-control packet.
    pub fn canonical_deny_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, "trust-cg.native_install_gate.deny_control.v1");
        put_bool(&mut out, self.active);
        put_str(&mut out, self.reason.as_str());
        put_str(&mut out, self.scope.as_str());
        put_option_str(&mut out, self.consumer.as_deref());
        put_option_str(&mut out, self.family.as_deref());
        put_option_str(&mut out, self.artifact_id.as_deref());
        put_option_str(&mut out, self.mode.map(NativeInstallGateAuthority::as_str));
        put_option_str(&mut out, self.surface.map(NativeInstallGateSurface::as_str));
        put_option_checksum(&mut out, self.target_checksum);
        put_option_checksum(&mut out, self.proof_policy_checksum);
        put_u64(&mut out, self.freshness.len() as u64);
        for observation in &self.freshness {
            put_str(&mut out, &observation.domain);
            put_u64(&mut out, observation.observed_generation);
            put_u64(&mut out, observation.current_generation);
        }
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return this packet with `deny_sha256` set to the canonical packet hash.
    pub fn with_canonical_deny_sha256(mut self) -> Self {
        self.deny_sha256 = Some(self.canonical_deny_sha256());
        self
    }
}

/// Access/mutability covered by layout evidence for one consumer-owned region.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeInstallGateLayoutAccess {
    /// Native code may only read this region.
    ReadOnly,
    /// Native code may only write this region.
    WriteOnly,
    /// Native code may read and write this region.
    ReadWrite,
}

impl NativeInstallGateLayoutAccess {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ReadOnly => "read_only",
            Self::WriteOnly => "write_only",
            Self::ReadWrite => "read_write",
        }
    }
}

/// Bounds, aliasing, mutability, and freshness coverage for one memory region.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateLayoutRegionEvidence {
    /// Stable region name referenced by entry ABIs.
    pub name: String,
    /// Consumer role, for example `flat_state_buffer` or `fingerprint_buffer`.
    pub role: String,
    /// Covered element size in bytes.
    pub element_size: u64,
    /// Covered region length in bytes.
    pub byte_len: u64,
    /// Native access/mutability contract.
    pub access: Option<NativeInstallGateLayoutAccess>,
    /// Alias group covered by validation.
    pub alias_group: String,
    /// Freshness/generation domain that must be current before install or call.
    pub generation_domain: String,
}

/// Entry ABI coverage for a consumer native wrapper or native entry point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateLayoutEntryAbiEvidence {
    /// Stable entry name.
    pub name: String,
    /// ABI family or wrapper ABI identifier.
    pub abi: String,
    /// ABI checksum covered for this entry.
    pub abi_checksum: ArtifactChecksum,
    /// Region names reachable from this entry.
    pub argument_regions: Vec<String>,
    /// Optional status/deopt callback region name.
    pub status_region: Option<String>,
    /// Freshness/generation domain that controls this entry.
    pub generation_domain: String,
}

/// Layout proof/evidence attached to a candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateLayoutEvidence {
    /// Layout checksum covered by the evidence.
    pub layout_checksum: ArtifactChecksum,
    /// ABI checksum covered by the evidence.
    pub abi_checksum: ArtifactChecksum,
    /// Invalidation checksum covered by the evidence.
    pub invalidation_checksum: ArtifactChecksum,
    /// Validator or adapter identity that produced this evidence.
    pub validation_provenance: String,
    /// Optional persisted report SHA-256.
    pub evidence_sha256: Option<String>,
    /// Optional generated wrapper identity.
    pub wrapper_identity: Option<String>,
    /// Memory regions covered by this evidence.
    pub regions: Vec<NativeInstallGateLayoutRegionEvidence>,
    /// Entry ABIs covered by this evidence.
    pub entry_abis: Vec<NativeInstallGateLayoutEntryAbiEvidence>,
}

impl NativeInstallGateLayoutEvidence {
    /// Build the data-only TY native fused parent-loop layout adapter fixture.
    ///
    /// This helper records the shared prework coverage expected by #747 without
    /// depending on TY runtime types or enabling product activation.
    pub fn ty_fused_parent_loop_prework(
        layout_checksum: ArtifactChecksum,
        abi_checksum: ArtifactChecksum,
        invalidation_checksum: ArtifactChecksum,
        wrapper_identity: impl Into<String>,
    ) -> Self {
        NativeInstallGateTyLayoutAdapter::fused_parent_loop(
            layout_checksum,
            abi_checksum,
            invalidation_checksum,
            wrapper_identity,
        )
        .into_layout_evidence()
    }

    /// Build the data-only ay solver-registry layout adapter fixture.
    ///
    /// This helper records the sparse/basis/watch-list prework coverage expected
    /// by #747 without depending on downstream ay runtime types or enabling
    /// product registry activation.
    pub fn ay_solver_registry_prework(
        layout_checksum: ArtifactChecksum,
        abi_checksum: ArtifactChecksum,
        invalidation_checksum: ArtifactChecksum,
        wrapper_identity: impl Into<String>,
    ) -> Self {
        NativeInstallGateAYLayoutAdapter::solver_registry(
            layout_checksum,
            abi_checksum,
            invalidation_checksum,
            wrapper_identity,
        )
        .into_layout_evidence()
    }

    /// Return the stable hash of the data-only layout evidence coverage.
    pub fn canonical_evidence_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, "trust-cg.native_install_gate.layout_evidence.v1");
        put_checksum(&mut out, self.layout_checksum);
        put_checksum(&mut out, self.abi_checksum);
        put_checksum(&mut out, self.invalidation_checksum);
        put_str(&mut out, &self.validation_provenance);
        put_option_str(&mut out, self.wrapper_identity.as_deref());
        put_u64(&mut out, self.regions.len() as u64);
        for region in &self.regions {
            put_str(&mut out, &region.name);
            put_str(&mut out, &region.role);
            put_u64(&mut out, region.element_size);
            put_u64(&mut out, region.byte_len);
            put_option_str(
                &mut out,
                region.access.map(NativeInstallGateLayoutAccess::as_str),
            );
            put_str(&mut out, &region.alias_group);
            put_str(&mut out, &region.generation_domain);
        }
        put_u64(&mut out, self.entry_abis.len() as u64);
        for entry in &self.entry_abis {
            put_str(&mut out, &entry.name);
            put_str(&mut out, &entry.abi);
            put_checksum(&mut out, entry.abi_checksum);
            put_u64(&mut out, entry.argument_regions.len() as u64);
            for region in &entry.argument_regions {
                put_str(&mut out, region);
            }
            put_option_str(&mut out, entry.status_region.as_deref());
            put_str(&mut out, &entry.generation_domain);
        }
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return this evidence with `evidence_sha256` set to the canonical coverage hash.
    pub fn with_canonical_evidence_sha256(mut self) -> Self {
        self.evidence_sha256 = Some(self.canonical_evidence_sha256());
        self
    }

    /// Convenience region constructor for tests and data-only adapters.
    pub fn region(
        name: impl Into<String>,
        role: impl Into<String>,
        element_size: u64,
        byte_len: u64,
        access: NativeInstallGateLayoutAccess,
        alias_group: impl Into<String>,
        generation_domain: impl Into<String>,
    ) -> NativeInstallGateLayoutRegionEvidence {
        NativeInstallGateLayoutRegionEvidence {
            name: name.into(),
            role: role.into(),
            element_size,
            byte_len,
            access: Some(access),
            alias_group: alias_group.into(),
            generation_domain: generation_domain.into(),
        }
    }

    /// Convenience entry ABI constructor for tests and data-only adapters.
    pub fn entry_abi(
        name: impl Into<String>,
        abi_checksum: ArtifactChecksum,
        argument_regions: &[&str],
        status_region: impl Into<String>,
        generation_domain: impl Into<String>,
    ) -> NativeInstallGateLayoutEntryAbiEvidence {
        NativeInstallGateLayoutEntryAbiEvidence {
            name: name.into(),
            abi: "trust-cg-native-wrapper".to_owned(),
            abi_checksum,
            argument_regions: argument_regions
                .iter()
                .map(|region| (*region).to_owned())
                .collect(),
            status_region: Some(status_region.into()),
            generation_domain: generation_domain.into(),
        }
    }
}

/// TY layout facts normalized into shared native install evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateTyLayoutAdapter {
    /// Layout checksum from the manifest.
    pub layout_checksum: ArtifactChecksum,
    /// ABI checksum from the manifest.
    pub abi_checksum: ArtifactChecksum,
    /// Invalidation checksum bound to this layout proof.
    pub invalidation_checksum: ArtifactChecksum,
    /// Generated wrapper identity.
    pub wrapper_identity: String,
    /// Validator or adapter identity.
    pub validation_provenance: String,
    /// Runtime arena byte bound.
    pub runtime_arena_byte_len: u64,
    /// Flat-state buffer byte bound.
    pub flat_state_buffer_byte_len: u64,
    /// Parent buffer byte bound.
    pub parent_buffer_byte_len: u64,
    /// Successor buffer byte bound.
    pub successor_buffer_byte_len: u64,
    /// Fingerprint buffer byte bound.
    pub fingerprint_buffer_byte_len: u64,
    /// Callback status buffer byte bound.
    pub callback_status_buffer_byte_len: u64,
}

impl NativeInstallGateTyLayoutAdapter {
    /// Build the TY fused parent-loop adapter fixture.
    pub fn fused_parent_loop(
        layout_checksum: ArtifactChecksum,
        abi_checksum: ArtifactChecksum,
        invalidation_checksum: ArtifactChecksum,
        wrapper_identity: impl Into<String>,
    ) -> Self {
        Self {
            layout_checksum,
            abi_checksum,
            invalidation_checksum,
            wrapper_identity: wrapper_identity.into(),
            validation_provenance: "trust-cg.ty.fused_parent_loop.layout_adapter.v1".to_owned(),
            runtime_arena_byte_len: 4096,
            flat_state_buffer_byte_len: 4096,
            parent_buffer_byte_len: 2048,
            successor_buffer_byte_len: 4096,
            fingerprint_buffer_byte_len: 2048,
            callback_status_buffer_byte_len: 256,
        }
    }

    /// Normalize this consumer adapter into shared install-gate layout evidence.
    pub fn into_layout_evidence(self) -> NativeInstallGateLayoutEvidence {
        let regions = vec![
            NativeInstallGateLayoutEvidence::region(
                "runtime_arena",
                "runtime_arena",
                8,
                self.runtime_arena_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ty-runtime-arena",
                "ty_arena",
            ),
            NativeInstallGateLayoutEvidence::region(
                "flat_state_buffer",
                "flat_state_buffer",
                8,
                self.flat_state_buffer_byte_len,
                NativeInstallGateLayoutAccess::ReadOnly,
                "ty-state",
                "ty_arena",
            ),
            NativeInstallGateLayoutEvidence::region(
                "parent_buffer",
                "parent_buffer",
                8,
                self.parent_buffer_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ty-parent-successor",
                "ty_action",
            ),
            NativeInstallGateLayoutEvidence::region(
                "successor_buffer",
                "successor_buffer",
                8,
                self.successor_buffer_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ty-parent-successor",
                "ty_action",
            ),
            NativeInstallGateLayoutEvidence::region(
                "fingerprint_buffer",
                "fingerprint_buffer",
                8,
                self.fingerprint_buffer_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ty-fingerprint",
                "ty_fingerprint",
            ),
            NativeInstallGateLayoutEvidence::region(
                "callback_status_buffer",
                "callback_status_buffer",
                4,
                self.callback_status_buffer_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ty-callback-status",
                "ty_runtime",
            ),
        ];
        let entry_abis = vec![
            NativeInstallGateLayoutEvidence::entry_abi(
                "action",
                self.abi_checksum,
                &[
                    "runtime_arena",
                    "flat_state_buffer",
                    "parent_buffer",
                    "successor_buffer",
                    "callback_status_buffer",
                ],
                "callback_status_buffer",
                "ty_action",
            ),
            NativeInstallGateLayoutEvidence::entry_abi(
                "invariant",
                self.abi_checksum,
                &[
                    "runtime_arena",
                    "flat_state_buffer",
                    "callback_status_buffer",
                ],
                "callback_status_buffer",
                "ty_action",
            ),
            NativeInstallGateLayoutEvidence::entry_abi(
                "liveness",
                self.abi_checksum,
                &[
                    "runtime_arena",
                    "flat_state_buffer",
                    "callback_status_buffer",
                ],
                "callback_status_buffer",
                "ty_action",
            ),
            NativeInstallGateLayoutEvidence::entry_abi(
                "fingerprint",
                self.abi_checksum,
                &[
                    "runtime_arena",
                    "flat_state_buffer",
                    "fingerprint_buffer",
                    "callback_status_buffer",
                ],
                "callback_status_buffer",
                "ty_fingerprint",
            ),
            NativeInstallGateLayoutEvidence::entry_abi(
                "fused_parent_loop",
                self.abi_checksum,
                &[
                    "runtime_arena",
                    "flat_state_buffer",
                    "parent_buffer",
                    "successor_buffer",
                    "fingerprint_buffer",
                    "callback_status_buffer",
                ],
                "callback_status_buffer",
                "ty_runtime",
            ),
        ];
        NativeInstallGateLayoutEvidence {
            layout_checksum: self.layout_checksum,
            abi_checksum: self.abi_checksum,
            invalidation_checksum: self.invalidation_checksum,
            validation_provenance: self.validation_provenance,
            evidence_sha256: None,
            wrapper_identity: Some(self.wrapper_identity),
            regions,
            entry_abis,
        }
        .with_canonical_evidence_sha256()
    }
}

/// ay layout facts normalized into shared native install evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateAYLayoutAdapter {
    /// Layout checksum from the manifest.
    pub layout_checksum: ArtifactChecksum,
    /// ABI checksum from the manifest.
    pub abi_checksum: ArtifactChecksum,
    /// Invalidation checksum bound to this layout proof.
    pub invalidation_checksum: ArtifactChecksum,
    /// Generated wrapper or registry adapter identity.
    pub wrapper_identity: String,
    /// Validator or adapter identity.
    pub validation_provenance: String,
    /// Solver-program state byte bound.
    pub solver_program_state_byte_len: u64,
    /// Sparse substitute rows byte bound.
    pub sparse_substitute_rows_byte_len: u64,
    /// Basis-region state byte bound.
    pub basis_region_state_byte_len: u64,
    /// Tableau buffers byte bound.
    pub tableau_buffer_byte_len: u64,
    /// Watch-list/BCP state byte bound.
    pub watch_list_bcp_state_byte_len: u64,
    /// Rollback state byte bound.
    pub rollback_state_byte_len: u64,
    /// Proof/witness buffer byte bound.
    pub proof_witness_buffer_byte_len: u64,
}

impl NativeInstallGateAYLayoutAdapter {
    /// Build the ay sparse/basis/watch-list registry adapter fixture.
    pub fn solver_registry(
        layout_checksum: ArtifactChecksum,
        abi_checksum: ArtifactChecksum,
        invalidation_checksum: ArtifactChecksum,
        wrapper_identity: impl Into<String>,
    ) -> Self {
        Self {
            layout_checksum,
            abi_checksum,
            invalidation_checksum,
            wrapper_identity: wrapper_identity.into(),
            validation_provenance: "trust-cg.ay.solver_registry.layout_adapter.v1".to_owned(),
            solver_program_state_byte_len: 4096,
            sparse_substitute_rows_byte_len: 8192,
            basis_region_state_byte_len: 4096,
            tableau_buffer_byte_len: 8192,
            watch_list_bcp_state_byte_len: 4096,
            rollback_state_byte_len: 2048,
            proof_witness_buffer_byte_len: 2048,
        }
    }

    /// Normalize this consumer adapter into shared install-gate layout evidence.
    pub fn into_layout_evidence(self) -> NativeInstallGateLayoutEvidence {
        let regions = vec![
            NativeInstallGateLayoutEvidence::region(
                "solver_program_state",
                "solver_program_state",
                8,
                self.solver_program_state_byte_len,
                NativeInstallGateLayoutAccess::ReadOnly,
                "ay-solver-program",
                "ay_solver",
            ),
            NativeInstallGateLayoutEvidence::region(
                "sparse_substitute_rows",
                "sparse_substitute_rows",
                8,
                self.sparse_substitute_rows_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ay-sparse-substitute",
                "ay_sparse_substitute",
            ),
            NativeInstallGateLayoutEvidence::region(
                "basis_region_state",
                "basis_region_state",
                8,
                self.basis_region_state_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ay-basis-region",
                "ay_basis",
            ),
            NativeInstallGateLayoutEvidence::region(
                "tableau_buffer",
                "tableau_buffer",
                8,
                self.tableau_buffer_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ay-tableau",
                "ay_solver",
            ),
            NativeInstallGateLayoutEvidence::region(
                "watch_list_bcp_state",
                "watch_list_bcp_state",
                8,
                self.watch_list_bcp_state_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ay-watch-bcp",
                "ay_watch_list",
            ),
            NativeInstallGateLayoutEvidence::region(
                "rollback_state",
                "rollback_state",
                8,
                self.rollback_state_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ay-rollback",
                "ay_rollback",
            ),
            NativeInstallGateLayoutEvidence::region(
                "proof_witness_buffer",
                "proof_witness_buffer",
                8,
                self.proof_witness_buffer_byte_len,
                NativeInstallGateLayoutAccess::ReadWrite,
                "ay-proof-witness",
                "ay_proof_witness",
            ),
        ];
        let entry_abis = vec![
            NativeInstallGateLayoutEvidence::entry_abi(
                "solver_program",
                self.abi_checksum,
                &[
                    "solver_program_state",
                    "tableau_buffer",
                    "proof_witness_buffer",
                    "rollback_state",
                ],
                "rollback_state",
                "ay_solver",
            ),
            NativeInstallGateLayoutEvidence::entry_abi(
                "sparse_substitute",
                self.abi_checksum,
                &[
                    "solver_program_state",
                    "sparse_substitute_rows",
                    "basis_region_state",
                    "tableau_buffer",
                    "rollback_state",
                    "proof_witness_buffer",
                ],
                "rollback_state",
                "ay_sparse_substitute",
            ),
            NativeInstallGateLayoutEvidence::entry_abi(
                "basis_region",
                self.abi_checksum,
                &[
                    "solver_program_state",
                    "basis_region_state",
                    "tableau_buffer",
                    "rollback_state",
                ],
                "rollback_state",
                "ay_basis",
            ),
            NativeInstallGateLayoutEvidence::entry_abi(
                "watch_list_bcp",
                self.abi_checksum,
                &[
                    "solver_program_state",
                    "watch_list_bcp_state",
                    "rollback_state",
                    "proof_witness_buffer",
                ],
                "rollback_state",
                "ay_watch_list",
            ),
            NativeInstallGateLayoutEvidence::entry_abi(
                "rollback",
                self.abi_checksum,
                &[
                    "rollback_state",
                    "basis_region_state",
                    "sparse_substitute_rows",
                    "tableau_buffer",
                ],
                "rollback_state",
                "ay_rollback",
            ),
            NativeInstallGateLayoutEvidence::entry_abi(
                "proof_witness",
                self.abi_checksum,
                &[
                    "proof_witness_buffer",
                    "solver_program_state",
                    "rollback_state",
                ],
                "rollback_state",
                "ay_proof_witness",
            ),
        ];
        NativeInstallGateLayoutEvidence {
            layout_checksum: self.layout_checksum,
            abi_checksum: self.abi_checksum,
            invalidation_checksum: self.invalidation_checksum,
            validation_provenance: self.validation_provenance,
            evidence_sha256: None,
            wrapper_identity: Some(self.wrapper_identity),
            regions,
            entry_abis,
        }
        .with_canonical_evidence_sha256()
    }
}

/// Proof or translation-validation evidence attached to a candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateProofEvidence {
    /// Existing contract-level proof evidence summary.
    pub summary: ProofEvidenceSummary,
    /// Optional persisted proof report SHA-256.
    pub proof_report_sha256: Option<String>,
    /// Stable obligation set id when known.
    pub obligation_set: Option<String>,
    /// Timeout budget recorded by the proof route.
    pub timeout_ms: Option<u64>,
    /// Native payload checksum bound by the proof route when known.
    pub native_payload_sha256: Option<String>,
}

/// Required payload identity hashes for a candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGatePayloadIdentity {
    /// Consumer source or solver-program SHA-256.
    pub source_sha256: String,
    /// Canonical trust_ir SHA-256.
    pub trust_ir_sha256: String,
    /// Native payload SHA-256.
    pub native_payload_sha256: String,
}

/// Telemetry envelope available at the install decision boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateTelemetryInput {
    /// Telemetry identity schema.
    pub schema: String,
    /// Telemetry identity schema version.
    pub schema_version: u32,
    /// Stable event id.
    pub event_id: String,
    /// Stable useful-native counter scope.
    pub counter_scope: String,
    /// Canonical telemetry record SHA-256.
    pub record_sha256: String,
    /// Artifact id recorded by telemetry.
    pub artifact_id: String,
    /// Manifest checksum recorded by telemetry.
    pub manifest_checksum: ArtifactChecksum,
    /// Proof report SHA-256 recorded by telemetry.
    pub proof_report_sha256: Option<String>,
    /// Layout checksum recorded by telemetry.
    pub layout_checksum: ArtifactChecksum,
    /// Invalidation checksum recorded by telemetry.
    pub invalidation_checksum: ArtifactChecksum,
    /// Disposition recorded by telemetry.
    pub disposition: NativeInstallGateDisposition,
    /// Rejection code recorded by telemetry.
    pub rejection_code: Option<NativeInstallGateRejectionCode>,
    /// Authority recorded by telemetry.
    pub install_authority: NativeInstallGateAuthority,
    /// Useful-native delta recorded by telemetry.
    pub useful_native_delta: u64,
}

impl NativeInstallGateTelemetryInput {
    /// Return the stable hash of the telemetry identity record.
    pub fn canonical_record_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, "trust-cg.native_install_gate.telemetry_record.v1");
        put_str(&mut out, &self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, &self.event_id);
        put_str(&mut out, &self.counter_scope);
        put_str(&mut out, &self.artifact_id);
        put_checksum(&mut out, self.manifest_checksum);
        put_option_str(&mut out, self.proof_report_sha256.as_deref());
        put_checksum(&mut out, self.layout_checksum);
        put_checksum(&mut out, self.invalidation_checksum);
        put_str(&mut out, self.disposition.as_str());
        put_option_str(
            &mut out,
            self.rejection_code
                .map(NativeInstallGateRejectionCode::as_str),
        );
        put_str(&mut out, self.install_authority.as_str());
        put_u64(&mut out, self.useful_native_delta);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return this telemetry record with `record_sha256` set to the canonical hash.
    pub fn with_canonical_record_sha256(mut self) -> Self {
        self.record_sha256 = self.canonical_record_sha256();
        self
    }
}

/// Replay identity available at the install decision boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateReplayIdentity {
    /// Replay identity schema.
    pub schema: String,
    /// Replay identity schema version.
    pub schema_version: u32,
    /// Stable replay root SHA-256.
    pub replay_root_sha256: String,
    /// Consumer that owns the replay identity.
    pub replay_consumer: String,
    /// Consumer family or mode that owns the replay identity.
    pub replay_family: String,
    /// Artifact id bound by replay.
    pub artifact_id: String,
    /// Source SHA-256 bound by replay.
    pub source_sha256: String,
    /// trust_ir SHA-256 bound by replay.
    pub trust_ir_sha256: String,
    /// Native payload SHA-256 bound by replay.
    pub native_payload_sha256: String,
    /// Canonical replay identity SHA-256.
    pub replay_record_sha256: String,
}

impl NativeInstallGateReplayIdentity {
    /// Return the stable hash of the replay identity record.
    pub fn canonical_record_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, "trust-cg.native_install_gate.replay_identity.v1");
        put_str(&mut out, &self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, &self.replay_root_sha256);
        put_str(&mut out, &self.replay_consumer);
        put_str(&mut out, &self.replay_family);
        put_str(&mut out, &self.artifact_id);
        put_str(&mut out, &self.source_sha256);
        put_str(&mut out, &self.trust_ir_sha256);
        put_str(&mut out, &self.native_payload_sha256);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return this replay identity with `replay_record_sha256` set canonically.
    pub fn with_canonical_record_sha256(mut self) -> Self {
        self.replay_record_sha256 = self.canonical_record_sha256();
        self
    }
}

/// Expected current request bindings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateExpectedBindings {
    /// Current artifact id.
    pub artifact_id: String,
    /// Current manifest checksum.
    pub manifest_checksum: ArtifactChecksum,
    /// Current target checksum.
    pub target_checksum: ArtifactChecksum,
    /// Current ABI checksum.
    pub abi_checksum: ArtifactChecksum,
    /// Current layout checksum.
    pub layout_checksum: ArtifactChecksum,
    /// Current proof-policy checksum.
    pub proof_policy_checksum: ArtifactChecksum,
    /// Current invalidation checksum.
    pub invalidation_checksum: ArtifactChecksum,
    /// Current artifact generation.
    pub current_generation: u64,
}

impl NativeInstallGateExpectedBindings {
    /// Build expected bindings from a manifest.
    pub fn from_manifest(manifest: &ArtifactManifestV1) -> Self {
        Self {
            artifact_id: manifest.artifact_id.clone(),
            manifest_checksum: manifest.checksum(),
            target_checksum: manifest.target.checksum(),
            abi_checksum: manifest.abi.checksum(),
            layout_checksum: manifest.layout.checksum(),
            proof_policy_checksum: manifest.proof_policy.checksum(),
            invalidation_checksum: manifest.invalidation.checksum(),
            current_generation: manifest.invalidation.generation,
        }
    }
}

/// Pure validator input for one native install candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateInput {
    /// Downstream consumer name.
    pub consumer: String,
    /// Stable downstream consumer mode.
    pub consumer_mode: String,
    /// Surface requesting a decision.
    pub surface: NativeInstallGateSurface,
    /// Candidate disposition before the gate validates evidence.
    pub candidate_disposition: NativeInstallGateDisposition,
    /// Requested install authority.
    pub requested_authority: NativeInstallGateAuthority,
    /// Full deterministic artifact manifest.
    pub manifest: Option<ArtifactManifestV1>,
    /// Manifest reference from install metadata or release/cache metadata.
    pub manifest_reference: Option<ArtifactManifestReference>,
    /// Expected current request bindings.
    pub expected: NativeInstallGateExpectedBindings,
    /// Payload hashes expected by the current request.
    pub payload_identity: NativeInstallGatePayloadIdentity,
    /// Payload hashes carried by the candidate.
    pub candidate_payload_identity: NativeInstallGatePayloadIdentity,
    /// Layout proof/evidence.
    pub layout_evidence: Option<NativeInstallGateLayoutEvidence>,
    /// Proof or translation-validation evidence.
    pub proof_evidence: Option<NativeInstallGateProofEvidence>,
    /// Current invalidation checksum at install time.
    pub current_invalidation_checksum: ArtifactChecksum,
    /// Candidate artifact generation.
    pub artifact_generation: u64,
    /// Current generation at install time.
    pub current_generation: u64,
    /// Whether this artifact or install scope has been revoked.
    pub revoked: bool,
    /// Optional deny-only freshness/revocation/kill-switch control-plane packet.
    pub deny_control: Option<NativeInstallGateDenyControlPlane>,
    /// Replay identity envelope.
    pub replay_identity: Option<NativeInstallGateReplayIdentity>,
    /// Decision telemetry envelope.
    pub telemetry: Option<NativeInstallGateTelemetryInput>,
}

/// Boolean effects authorized by the gate packet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeInstallGateActions {
    /// Whether a callable handle can be exposed.
    pub expose_callable: bool,
    /// Whether typed symbol lookup can proceed.
    pub typed_symbol_lookup: bool,
    /// Whether an installable cache entry can be inserted.
    pub insert_installable_cache: bool,
    /// Whether an installable cache hit can be accepted.
    pub accept_installable_cache_hit: bool,
    /// Whether release metadata can mark the artifact installable.
    pub release_installable: bool,
    /// Whether a ay registry entry can be inserted.
    pub ay_registry_insert: bool,
    /// Whether TY native activation can proceed.
    pub ty_native_activate: bool,
    /// Whether later successful native calls may count as useful native.
    pub useful_native_eligible: bool,
}

impl NativeInstallGateActions {
    /// Actions for an installable candidate on the requested surface.
    pub fn for_surface(surface: NativeInstallGateSurface) -> Self {
        let mut actions = Self::none();
        actions.useful_native_eligible = true;
        match surface {
            NativeInstallGateSurface::DirectCompileInstall => {
                actions.expose_callable = true;
            }
            NativeInstallGateSurface::TypedSymbolLookup => {
                actions.expose_callable = true;
                actions.typed_symbol_lookup = true;
            }
            NativeInstallGateSurface::AsyncPoll => {}
            NativeInstallGateSurface::CacheInsert => {
                actions.insert_installable_cache = true;
            }
            NativeInstallGateSurface::CacheHit => {
                actions.accept_installable_cache_hit = true;
                actions.expose_callable = true;
            }
            NativeInstallGateSurface::ReleaseBundle => {
                actions.release_installable = true;
            }
            NativeInstallGateSurface::AYRegistry => {
                actions.ay_registry_insert = true;
            }
            NativeInstallGateSurface::TyActivation => {
                actions.ty_native_activate = true;
            }
            NativeInstallGateSurface::NativeSuccessor => {
                actions.expose_callable = true;
            }
        }
        actions
    }

    /// No install-authorizing actions.
    pub const fn none() -> Self {
        Self {
            expose_callable: false,
            typed_symbol_lookup: false,
            insert_installable_cache: false,
            accept_installable_cache_hit: false,
            release_installable: false,
            ay_registry_insert: false,
            ty_native_activate: false,
            useful_native_eligible: false,
        }
    }

    /// Return true when no install-authorizing action is enabled.
    pub const fn all_install_authority_blocked(self) -> bool {
        !self.expose_callable
            && !self.typed_symbol_lookup
            && !self.insert_installable_cache
            && !self.accept_installable_cache_hit
            && !self.release_installable
            && !self.ay_registry_insert
            && !self.ty_native_activate
            && !self.useful_native_eligible
    }
}

/// Artifact identity copied into a gate packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateArtifactPacket {
    /// Artifact id.
    pub artifact_id: String,
    /// Manifest schema.
    pub manifest_schema: String,
    /// Manifest schema version.
    pub manifest_schema_version: u32,
    /// Manifest checksum.
    pub manifest_checksum: ArtifactChecksum,
    /// Source SHA-256.
    pub source_sha256: String,
    /// trust_ir SHA-256.
    pub trust_ir_sha256: String,
    /// Native payload SHA-256.
    pub native_payload_sha256: String,
    /// Target checksum.
    pub target_checksum: ArtifactChecksum,
    /// ABI checksum.
    pub abi_checksum: ArtifactChecksum,
    /// Layout checksum.
    pub layout_checksum: ArtifactChecksum,
    /// Proof-policy checksum.
    pub proof_policy_checksum: ArtifactChecksum,
    /// Invalidation checksum.
    pub invalidation_checksum: ArtifactChecksum,
    /// Deterministic manifest metadata copied into the install packet.
    pub manifest_metadata: BTreeMap<String, String>,
}

/// Validation evidence copied into a gate packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateValidationPacket {
    /// Layout evidence status.
    pub layout_status: &'static str,
    /// Layout evidence SHA-256.
    pub layout_evidence_sha256: Option<String>,
    /// Generated wrapper identity covered by layout evidence.
    pub layout_wrapper_identity: Option<String>,
    /// Validator or adapter identity covered by layout evidence.
    pub layout_validation_provenance: Option<String>,
    /// Invalidation checksum covered by layout evidence.
    pub layout_invalidation_checksum: Option<ArtifactChecksum>,
    /// Generation domains covered by layout evidence.
    pub layout_generation_domains: Vec<String>,
    /// Proof verdict.
    pub proof_verdict: &'static str,
    /// Proof reject code.
    pub proof_reject_code: Option<&'static str>,
    /// Proof verifier.
    pub proof_verifier: Option<String>,
    /// Proof report SHA-256.
    pub proof_report_sha256: Option<String>,
    /// Obligation set.
    pub obligation_set: Option<String>,
    /// Timeout budget.
    pub timeout_ms: Option<u64>,
}

/// Freshness fields copied into a gate packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateFreshnessPacket {
    /// Artifact generation.
    pub artifact_generation: u64,
    /// Current generation.
    pub current_generation: u64,
    /// Freshness domains bound to this packet.
    pub freshness_domains: Vec<NativeInstallGateFreshnessObservation>,
    /// Whether the artifact was revoked.
    pub revoked: bool,
    /// Optional deny-only freshness/revocation/kill-switch packet.
    pub deny_control: Option<NativeInstallGateDenyControlPlane>,
}

/// Runtime freshness context for revalidating an already persisted gate packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateRevalidationInput {
    /// Current invalidation checksum observed by the caller.
    pub current_invalidation_checksum: ArtifactChecksum,
    /// Current generation observed by the caller.
    pub current_generation: u64,
    /// Current freshness-domain observations observed by the caller.
    pub freshness_domains: Vec<NativeInstallGateFreshnessObservation>,
    /// Whether this artifact or install scope is currently revoked.
    pub revoked: bool,
    /// Optional live deny-only freshness/revocation/kill-switch control packet.
    pub deny_control: Option<NativeInstallGateDenyControlPlane>,
}

impl NativeInstallGateRevalidationInput {
    /// Build revalidation context from the packet's persisted freshness.
    pub fn from_packet(packet: &NativeInstallGatePacket) -> Self {
        Self {
            current_invalidation_checksum: packet.artifact.invalidation_checksum,
            current_generation: packet.freshness.current_generation,
            freshness_domains: packet.freshness.freshness_domains.clone(),
            revoked: packet.freshness.revoked,
            deny_control: packet.freshness.deny_control.clone(),
        }
    }

    /// Build revalidation context from the current full artifact manifest.
    pub fn from_manifest(manifest: &ArtifactManifestV1) -> Self {
        Self {
            current_invalidation_checksum: manifest.invalidation.checksum(),
            current_generation: manifest.invalidation.generation,
            freshness_domains: Vec::new(),
            revoked: false,
            deny_control: None,
        }
    }
}

/// Decision telemetry copied into a gate packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateTelemetryPacket {
    /// Telemetry identity schema.
    pub schema: String,
    /// Telemetry identity schema version.
    pub schema_version: u32,
    /// Stable event id.
    pub event_id: String,
    /// Stable useful-native counter scope.
    pub counter_scope: String,
    /// Canonical telemetry record SHA-256.
    pub record_sha256: String,
    /// Artifact id recorded by telemetry.
    pub artifact_id: String,
    /// Manifest checksum recorded by telemetry.
    pub manifest_checksum: ArtifactChecksum,
    /// Proof report SHA-256 recorded by telemetry.
    pub proof_report_sha256: Option<String>,
    /// Layout checksum recorded by telemetry.
    pub layout_checksum: ArtifactChecksum,
    /// Invalidation checksum recorded by telemetry.
    pub invalidation_checksum: ArtifactChecksum,
    /// Disposition recorded by telemetry.
    pub disposition: NativeInstallGateDisposition,
    /// Rejection code recorded by telemetry.
    pub rejection_code: Option<NativeInstallGateRejectionCode>,
    /// Authority recorded by telemetry.
    pub install_authority: NativeInstallGateAuthority,
    /// Useful-native counter delta.
    pub useful_native_delta: u64,
}

impl NativeInstallGateTelemetryPacket {
    /// Return the stable hash of the copied telemetry identity record.
    pub fn canonical_record_sha256(&self) -> String {
        let input = NativeInstallGateTelemetryInput {
            schema: self.schema.clone(),
            schema_version: self.schema_version,
            event_id: self.event_id.clone(),
            counter_scope: self.counter_scope.clone(),
            record_sha256: String::new(),
            artifact_id: self.artifact_id.clone(),
            manifest_checksum: self.manifest_checksum,
            proof_report_sha256: self.proof_report_sha256.clone(),
            layout_checksum: self.layout_checksum,
            invalidation_checksum: self.invalidation_checksum,
            disposition: self.disposition,
            rejection_code: self.rejection_code,
            install_authority: self.install_authority,
            useful_native_delta: self.useful_native_delta,
        };
        input.canonical_record_sha256()
    }

    /// Return this packet with `record_sha256` set to the canonical hash.
    pub fn with_canonical_record_sha256(mut self) -> Self {
        self.record_sha256 = self.canonical_record_sha256();
        self
    }
}

/// Replay binding derived from the canonical install gate packet hash.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateReplayBinding {
    /// Canonical packet hash consumed by replay/release evidence.
    pub packet_hash: ArtifactChecksum,
    /// Stable replay root derived from the packet identity.
    pub replay_root_sha256: String,
}

/// Consumer verdict binding derived from the canonical install gate packet hash.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateConsumerVerdictBinding {
    /// Consumer that owns the verdict.
    pub consumer: String,
    /// Consumer mode that owns the verdict.
    pub consumer_mode: String,
    /// Surface covered by the verdict.
    pub surface: NativeInstallGateSurface,
    /// Stable verdict id for telemetry and diagnostics.
    pub verdict_id: String,
    /// Stable verdict hash for cache/release/replay identity.
    pub verdict_sha256: String,
}

/// Consumer-side evidence required before publishing ay/TY callable admission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateConsumerAdmissionEvidence {
    /// Consumer that owns the admission decision.
    pub consumer: String,
    /// Consumer family or mode covered by the admission decision.
    pub consumer_mode: String,
    /// Product surface covered by the admission decision.
    pub surface: NativeInstallGateSurface,
    /// Exact allowlist tuple key for this consumer/family/surface.
    pub allowlist_key: String,
    /// Target checksum accepted by the consumer gate.
    pub target_checksum: ArtifactChecksum,
    /// Proof-policy checksum accepted by the consumer gate.
    pub proof_policy_checksum: ArtifactChecksum,
    /// Layout checksum accepted by the consumer gate.
    pub layout_checksum: ArtifactChecksum,
    /// Invalidation checksum accepted by the consumer gate.
    pub invalidation_checksum: ArtifactChecksum,
    /// Runtime generation accepted by the consumer gate.
    pub runtime_generation: u64,
    /// Consumer rollback readiness or equivalent rollback guard.
    pub rollback_ready: bool,
    /// TY status readiness or equivalent status guard.
    pub status_ready: bool,
    /// Consumer deopt/fallback readiness.
    pub deopt_ready: bool,
    /// Telemetry event id observed by the consumer gate.
    pub telemetry_event_id: String,
    /// Useful-native counter scope observed by the consumer gate.
    pub telemetry_counter_scope: String,
    /// Telemetry record hash observed by the consumer gate.
    pub telemetry_record_sha256: String,
    /// Replay root observed by the consumer gate.
    pub replay_root_sha256: String,
    /// Shared install-gate consumer verdict hash observed by the consumer gate.
    pub install_consumer_verdict_sha256: String,
    /// Canonical hash of this consumer admission evidence.
    pub evidence_sha256: String,
}

impl NativeInstallGateConsumerAdmissionEvidence {
    /// Build consumer admission evidence from an already persisted packet.
    pub fn from_packet(
        packet: &NativeInstallGatePacket,
        current: &NativeInstallGateRevalidationInput,
        allowlist_key: String,
        rollback_ready: bool,
        status_ready: bool,
        deopt_ready: bool,
    ) -> Self {
        let telemetry = packet.telemetry.as_ref();
        Self {
            consumer: packet.consumer.clone(),
            consumer_mode: packet.consumer_mode.clone(),
            surface: packet.surface,
            allowlist_key,
            target_checksum: packet.artifact.target_checksum,
            proof_policy_checksum: packet.artifact.proof_policy_checksum,
            layout_checksum: packet.artifact.layout_checksum,
            invalidation_checksum: packet.artifact.invalidation_checksum,
            runtime_generation: current.current_generation,
            rollback_ready,
            status_ready,
            deopt_ready,
            telemetry_event_id: telemetry
                .map(|telemetry| telemetry.event_id.clone())
                .unwrap_or_default(),
            telemetry_counter_scope: telemetry
                .map(|telemetry| telemetry.counter_scope.clone())
                .unwrap_or_default(),
            telemetry_record_sha256: telemetry
                .map(|telemetry| telemetry.record_sha256.clone())
                .unwrap_or_default(),
            replay_root_sha256: packet.replay_binding.replay_root_sha256.clone(),
            install_consumer_verdict_sha256: packet.consumer_verdict.verdict_sha256.clone(),
            evidence_sha256: String::new(),
        }
        .with_canonical_evidence_sha256()
    }

    /// Return the stable hash of this consumer admission evidence.
    pub fn canonical_evidence_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA);
        put_u32(
            &mut out,
            NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA_VERSION,
        );
        put_str(&mut out, &self.consumer);
        put_str(&mut out, &self.consumer_mode);
        put_str(&mut out, self.surface.as_str());
        put_str(&mut out, &self.allowlist_key);
        put_checksum(&mut out, self.target_checksum);
        put_checksum(&mut out, self.proof_policy_checksum);
        put_checksum(&mut out, self.layout_checksum);
        put_checksum(&mut out, self.invalidation_checksum);
        put_u64(&mut out, self.runtime_generation);
        put_bool(&mut out, self.rollback_ready);
        put_bool(&mut out, self.status_ready);
        put_bool(&mut out, self.deopt_ready);
        put_str(&mut out, &self.telemetry_event_id);
        put_str(&mut out, &self.telemetry_counter_scope);
        put_str(&mut out, &self.telemetry_record_sha256);
        put_str(&mut out, &self.replay_root_sha256);
        put_str(&mut out, &self.install_consumer_verdict_sha256);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return this evidence with `evidence_sha256` set to the canonical hash.
    pub fn with_canonical_evidence_sha256(mut self) -> Self {
        self.evidence_sha256 = self.canonical_evidence_sha256();
        self
    }
}

/// Consumer-admission telemetry produced before ay registry or TY activation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateConsumerAdmissionTelemetryPacket {
    /// Consumer admission telemetry schema.
    pub schema: &'static str,
    /// Consumer admission telemetry schema version.
    pub schema_version: u32,
    /// Canonical packet hash consumed by admission.
    pub packet_hash: ArtifactChecksum,
    /// Telemetry event id bound before callable exposure.
    pub telemetry_event_id: Option<String>,
    /// Telemetry identity record hash bound into the gate packet.
    pub telemetry_record_sha256: Option<String>,
    /// Stable useful-native counter scope.
    pub counter_scope: String,
    /// Replay root hash bound to this packet.
    pub replay_root_sha256: Option<String>,
    /// Shared install-gate consumer verdict hash.
    pub install_consumer_verdict_sha256: Option<String>,
    /// Consumer admission evidence hash.
    pub admission_evidence_sha256: Option<String>,
    /// Admission disposition after call-time revalidation.
    pub disposition: NativeInstallGateDisposition,
    /// Admission rejection code after call-time revalidation.
    pub rejection_code: Option<NativeInstallGateRejectionCode>,
    /// Whether artifact revocation was observed at admission time.
    pub revoked: bool,
    /// Deny-only control-plane packet observed at admission time.
    pub deny_control: Option<NativeInstallGateDenyControlPlane>,
    /// Boolean effects authorized after consumer admission.
    pub actions: NativeInstallGateActions,
    /// Consumer admission never increments useful-native counters.
    pub useful_native_delta: u64,
}

/// Consumer-admission decision for ay registry insertion or TY activation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateConsumerAdmissionDecision {
    /// Final admission disposition.
    pub disposition: NativeInstallGateDisposition,
    /// Stable admission rejection code.
    pub rejection_code: Option<NativeInstallGateRejectionCode>,
    /// Authority requested by the candidate path.
    pub requested_authority: NativeInstallGateAuthority,
    /// Authority granted after consumer admission.
    pub install_authority: NativeInstallGateAuthority,
    /// Canonical hash of the gate packet consumed by admission.
    pub packet_hash: ArtifactChecksum,
    /// Consumer.
    pub consumer: String,
    /// Consumer family or mode.
    pub consumer_mode: String,
    /// Product surface.
    pub surface: NativeInstallGateSurface,
    /// Boolean effects authorized by this admission decision.
    pub actions: NativeInstallGateActions,
    /// Admission telemetry record.
    pub telemetry: NativeInstallGateConsumerAdmissionTelemetryPacket,
}

/// Compact native admission summary for product consumers.
///
/// This view carries the upstream packet/admission artifact and digest facts
/// that ay/TY product code should consume instead of reconstructing locally.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateAdmissionSummary {
    /// Admission summary schema.
    pub schema: &'static str,
    /// Admission summary schema version.
    pub schema_version: u32,
    /// Canonical packet hash from the evaluated verdict/admission.
    pub packet_hash: ArtifactChecksum,
    /// Packet hash persisted with the packet.
    pub persisted_packet_hash: ArtifactChecksum,
    /// Consumer.
    pub consumer: String,
    /// Consumer family or mode.
    pub consumer_mode: String,
    /// Product surface.
    pub surface: &'static str,
    /// Artifact id.
    pub artifact_id: String,
    /// Manifest checksum.
    pub manifest_checksum: ArtifactChecksum,
    /// Source SHA-256.
    pub source_sha256: String,
    /// trust_ir SHA-256.
    pub trust_ir_sha256: String,
    /// Native payload SHA-256.
    pub native_payload_sha256: String,
    /// Target checksum.
    pub target_checksum: ArtifactChecksum,
    /// ABI checksum.
    pub abi_checksum: ArtifactChecksum,
    /// Layout checksum.
    pub layout_checksum: ArtifactChecksum,
    /// Proof-policy checksum.
    pub proof_policy_checksum: ArtifactChecksum,
    /// Invalidation checksum.
    pub invalidation_checksum: ArtifactChecksum,
    /// Proof report SHA-256.
    pub proof_report_sha256: Option<String>,
    /// Stable useful-native counter scope.
    pub counter_scope: String,
    /// Stable disposition string.
    pub disposition: &'static str,
    /// Stable rejection reason code string.
    pub reason_code: Option<&'static str>,
    /// Requested authority string.
    pub requested_authority: &'static str,
    /// Granted authority string.
    pub install_authority: &'static str,
    /// Boolean effects authorized by this summary.
    pub actions: NativeInstallGateActions,
    /// Telemetry event id bound before callable exposure.
    pub telemetry_event_id: Option<String>,
    /// Telemetry identity record hash bound into the gate packet.
    pub telemetry_record_sha256: Option<String>,
    /// Replay root hash bound to this packet.
    pub replay_root_sha256: Option<String>,
    /// Shared install-gate consumer verdict hash.
    pub install_consumer_verdict_sha256: Option<String>,
    /// Consumer admission evidence hash, when summarizing admission.
    pub admission_evidence_sha256: Option<String>,
    /// Useful-native counter delta for this admission boundary.
    pub useful_native_delta: u64,
}

impl NativeInstallGateAdmissionSummary {
    /// Summarize a persisted gate packet using its upstream verdict view.
    pub fn from_packet(packet: &NativeInstallGatePacket) -> Self {
        let verdict = packet.verdict();
        Self::from_parts(
            packet,
            verdict.packet_hash,
            verdict.disposition,
            verdict.rejection_code,
            verdict.requested_authority,
            verdict.install_authority,
            verdict.actions,
            None,
            packet
                .telemetry
                .as_ref()
                .map(|telemetry| telemetry.useful_native_delta)
                .unwrap_or(0),
        )
    }

    /// Summarize a ay/TY consumer admission decision.
    pub fn from_consumer_admission(
        packet: &NativeInstallGatePacket,
        admission: &NativeInstallGateConsumerAdmissionDecision,
    ) -> Self {
        Self::from_parts(
            packet,
            admission.packet_hash,
            admission.disposition,
            admission.rejection_code,
            admission.requested_authority,
            admission.install_authority,
            admission.actions,
            admission.telemetry.admission_evidence_sha256.clone(),
            admission.telemetry.useful_native_delta,
        )
    }

    fn from_parts(
        packet: &NativeInstallGatePacket,
        packet_hash: ArtifactChecksum,
        disposition: NativeInstallGateDisposition,
        rejection_code: Option<NativeInstallGateRejectionCode>,
        requested_authority: NativeInstallGateAuthority,
        install_authority: NativeInstallGateAuthority,
        actions: NativeInstallGateActions,
        admission_evidence_sha256: Option<String>,
        useful_native_delta: u64,
    ) -> Self {
        let telemetry = packet.telemetry.as_ref();
        Self {
            schema: NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA,
            schema_version: NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA_VERSION,
            packet_hash,
            persisted_packet_hash: packet.packet_hash,
            consumer: packet.consumer.clone(),
            consumer_mode: packet.consumer_mode.clone(),
            surface: packet.surface.as_str(),
            artifact_id: packet.artifact.artifact_id.clone(),
            manifest_checksum: packet.artifact.manifest_checksum,
            source_sha256: packet.artifact.source_sha256.clone(),
            trust_ir_sha256: packet.artifact.trust_ir_sha256.clone(),
            native_payload_sha256: packet.artifact.native_payload_sha256.clone(),
            target_checksum: packet.artifact.target_checksum,
            abi_checksum: packet.artifact.abi_checksum,
            layout_checksum: packet.artifact.layout_checksum,
            proof_policy_checksum: packet.artifact.proof_policy_checksum,
            invalidation_checksum: packet.artifact.invalidation_checksum,
            proof_report_sha256: packet.validation.proof_report_sha256.clone(),
            counter_scope: telemetry
                .map(|telemetry| telemetry.counter_scope.clone())
                .unwrap_or_else(|| native_install_gate_counter_scope(packet)),
            disposition: disposition.as_str(),
            reason_code: rejection_code.map(NativeInstallGateRejectionCode::as_str),
            requested_authority: requested_authority.as_str(),
            install_authority: install_authority.as_str(),
            actions,
            telemetry_event_id: telemetry.map(|telemetry| telemetry.event_id.clone()),
            telemetry_record_sha256: telemetry.map(|telemetry| telemetry.record_sha256.clone()),
            replay_root_sha256: Some(packet.replay_binding.replay_root_sha256.clone()),
            install_consumer_verdict_sha256: Some(packet.consumer_verdict.verdict_sha256.clone()),
            admission_evidence_sha256,
            useful_native_delta,
        }
    }
}

impl NativeInstallGateConsumerAdmissionDecision {
    /// Return the stable admission rejection reason code.
    pub fn reason_code(&self) -> Option<&'static str> {
        self.rejection_code
            .map(NativeInstallGateRejectionCode::as_str)
    }

    /// Return a compact admission summary bound to the consumed packet.
    pub fn admission_summary(
        &self,
        packet: &NativeInstallGatePacket,
    ) -> NativeInstallGateAdmissionSummary {
        NativeInstallGateAdmissionSummary::from_consumer_admission(packet, self)
    }
}

impl NativeInstallGateConsumerAdmissionTelemetryPacket {
    /// Return the stable telemetry rejection reason code.
    pub fn reason_code(&self) -> Option<&'static str> {
        self.rejection_code
            .map(NativeInstallGateRejectionCode::as_str)
    }
}

/// Install verdict derived from an install gate packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateVerdict {
    /// Final disposition.
    pub disposition: NativeInstallGateDisposition,
    /// Stable rejection code.
    pub rejection_code: Option<NativeInstallGateRejectionCode>,
    /// Authority requested by the candidate path.
    pub requested_authority: NativeInstallGateAuthority,
    /// Authority granted by the gate.
    pub install_authority: NativeInstallGateAuthority,
    /// Canonical hash of the gate packet.
    pub packet_hash: ArtifactChecksum,
    /// Telemetry event id bound to the verdict.
    pub telemetry_event_id: Option<String>,
    /// Stable counter scope for useful-native accounting.
    pub counter_scope: String,
    /// Replay identity bound before callable exposure.
    pub replay_identity: Option<NativeInstallGateReplayIdentity>,
    /// Replay binding for this packet.
    pub replay_binding: NativeInstallGateReplayBinding,
    /// Consumer verdict binding for this packet.
    pub consumer_verdict: NativeInstallGateConsumerVerdictBinding,
    /// Optional deny-only freshness/revocation/kill-switch packet.
    pub deny_control: Option<NativeInstallGateDenyControlPlane>,
    /// Boolean effects authorized by this verdict.
    pub actions: NativeInstallGateActions,
}

/// Runtime telemetry produced after a native dispatch attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateRuntimeTelemetryPacket {
    /// Runtime telemetry schema.
    pub schema: &'static str,
    /// Runtime telemetry schema version.
    pub schema_version: u32,
    /// Canonical packet hash observed at runtime.
    pub packet_hash: ArtifactChecksum,
    /// Current invalidation checksum observed at runtime.
    pub current_invalidation_checksum: ArtifactChecksum,
    /// Current generation observed at runtime.
    pub current_generation: u64,
    /// Telemetry event id bound before callable exposure.
    pub telemetry_event_id: Option<String>,
    /// Telemetry identity record hash bound into the gate packet.
    pub telemetry_record_sha256: Option<String>,
    /// Stable useful-native counter scope.
    pub counter_scope: String,
    /// Replay root hash bound to this packet.
    pub replay_root_sha256: Option<String>,
    /// Replay identity record hash bound into this packet.
    pub replay_record_sha256: Option<String>,
    /// Replay binding derived from the packet hash.
    pub replay_binding: NativeInstallGateReplayBinding,
    /// Consumer verdict binding derived from the packet hash.
    pub consumer_verdict: NativeInstallGateConsumerVerdictBinding,
    /// Runtime gate disposition after revalidation.
    pub disposition: NativeInstallGateDisposition,
    /// Runtime gate rejection code after revalidation.
    pub rejection_code: Option<NativeInstallGateRejectionCode>,
    /// Whether artifact revocation was observed at runtime.
    pub revoked: bool,
    /// Deny-only control-plane packet observed at runtime.
    pub deny_control: Option<NativeInstallGateDenyControlPlane>,
    /// Authority requested by the candidate path.
    pub requested_authority: NativeInstallGateAuthority,
    /// Authority granted after runtime revalidation.
    pub install_authority: NativeInstallGateAuthority,
    /// Boolean effects authorized after runtime revalidation.
    pub actions: NativeInstallGateActions,
    /// Whether the native call completed successfully.
    pub native_call_succeeded: bool,
    /// Typed runtime outcome after revalidation and any fallback/deopt.
    pub runtime_outcome: NativeInstallGateRuntimeOutcome,
    /// Useful-native counter delta for this runtime attempt.
    pub useful_native_delta: u64,
}

/// Structured install-gate event emitted from packet, runtime, admission, or shadow paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateStructuredEvent {
    /// Structured event schema.
    pub schema: &'static str,
    /// Structured event schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Event source.
    pub source: NativeInstallGateEventSource,
    /// Event kind.
    pub kind: NativeInstallGateEventKind,
    /// Canonical packet hash bound to this event.
    pub packet_hash: ArtifactChecksum,
    /// Telemetry event id bound before callable exposure.
    pub telemetry_event_id: Option<String>,
    /// Telemetry identity record hash bound into the gate packet.
    pub telemetry_record_sha256: Option<String>,
    /// Stable useful-native counter scope.
    pub counter_scope: String,
    /// Replay root hash bound to this packet.
    pub replay_root_sha256: Option<String>,
    /// Replay identity record hash bound into this packet when available.
    pub replay_record_sha256: Option<String>,
    /// Shared install-gate consumer verdict hash.
    pub install_consumer_verdict_sha256: Option<String>,
    /// Artifact id.
    pub artifact_id: String,
    /// Manifest checksum.
    pub manifest_checksum: ArtifactChecksum,
    /// Source SHA-256.
    pub source_sha256: String,
    /// trust_ir SHA-256.
    pub trust_ir_sha256: String,
    /// Native payload SHA-256.
    pub native_payload_sha256: String,
    /// Target checksum.
    pub target_checksum: ArtifactChecksum,
    /// ABI checksum.
    pub abi_checksum: ArtifactChecksum,
    /// Layout checksum.
    pub layout_checksum: ArtifactChecksum,
    /// Proof-policy checksum.
    pub proof_policy_checksum: ArtifactChecksum,
    /// Invalidation checksum.
    pub invalidation_checksum: ArtifactChecksum,
    /// Proof report SHA-256.
    pub proof_report_sha256: Option<String>,
    /// Requested authority.
    pub requested_authority: NativeInstallGateAuthority,
    /// Granted authority.
    pub install_authority: NativeInstallGateAuthority,
    /// Final disposition.
    pub disposition: NativeInstallGateDisposition,
    /// Stable rejection code.
    pub rejection_code: Option<NativeInstallGateRejectionCode>,
    /// Boolean effects authorized by this event.
    pub actions: NativeInstallGateActions,
    /// Whether a runtime native call completed successfully.
    pub native_call_succeeded: Option<bool>,
    /// Useful-native counter delta for this event.
    pub useful_native_delta: u64,
    /// Optional diagnostic hash for shadow mismatch or rollback evidence.
    pub diagnostic_sha256: Option<String>,
    /// Canonical event hash.
    pub event_sha256: String,
}

impl NativeInstallGateStructuredEvent {
    /// Return the stable hash of this structured event.
    pub fn canonical_event_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_u64(&mut out, self.issue);
        put_str(&mut out, self.source.as_str());
        put_str(&mut out, self.kind.as_str());
        put_checksum(&mut out, self.packet_hash);
        put_option_str(&mut out, self.telemetry_event_id.as_deref());
        put_option_str(&mut out, self.telemetry_record_sha256.as_deref());
        put_str(&mut out, &self.counter_scope);
        put_option_str(&mut out, self.replay_root_sha256.as_deref());
        put_option_str(&mut out, self.replay_record_sha256.as_deref());
        put_option_str(&mut out, self.install_consumer_verdict_sha256.as_deref());
        put_str(&mut out, &self.artifact_id);
        put_checksum(&mut out, self.manifest_checksum);
        put_str(&mut out, &self.source_sha256);
        put_str(&mut out, &self.trust_ir_sha256);
        put_str(&mut out, &self.native_payload_sha256);
        put_checksum(&mut out, self.target_checksum);
        put_checksum(&mut out, self.abi_checksum);
        put_checksum(&mut out, self.layout_checksum);
        put_checksum(&mut out, self.proof_policy_checksum);
        put_checksum(&mut out, self.invalidation_checksum);
        put_option_str(&mut out, self.proof_report_sha256.as_deref());
        put_str(&mut out, self.requested_authority.as_str());
        put_str(&mut out, self.install_authority.as_str());
        put_str(&mut out, self.disposition.as_str());
        put_option_str(
            &mut out,
            self.rejection_code
                .map(NativeInstallGateRejectionCode::as_str),
        );
        put_actions(&mut out, self.actions);
        put_option_bool(&mut out, self.native_call_succeeded);
        put_u64(&mut out, self.useful_native_delta);
        put_option_str(&mut out, self.diagnostic_sha256.as_deref());
        format!("sha256:{}", sha256_hex(&out))
    }
}

/// Metadata-only gate packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGatePacket {
    /// Packet schema.
    pub schema: &'static str,
    /// Packet schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub gate_issue: u64,
    /// Design issue.
    pub design_issue: u64,
    /// Consumer.
    pub consumer: String,
    /// Consumer mode.
    pub consumer_mode: String,
    /// Product surface.
    pub surface: NativeInstallGateSurface,
    /// Artifact packet fields.
    pub artifact: NativeInstallGateArtifactPacket,
    /// Validation packet fields.
    pub validation: NativeInstallGateValidationPacket,
    /// Freshness packet fields.
    pub freshness: NativeInstallGateFreshnessPacket,
    /// Telemetry packet fields.
    pub telemetry: Option<NativeInstallGateTelemetryPacket>,
    /// Replay identity packet fields.
    pub replay_identity: Option<NativeInstallGateReplayIdentity>,
    /// Authority originally requested by the candidate path.
    pub requested_authority: NativeInstallGateAuthority,
    /// Final disposition.
    pub disposition: NativeInstallGateDisposition,
    /// Stable rejection code.
    pub rejection_code: Option<NativeInstallGateRejectionCode>,
    /// Confirmed install authority.
    pub install_authority: NativeInstallGateAuthority,
    /// Canonical packet hash persisted with this packet.
    pub packet_hash: ArtifactChecksum,
    /// Replay binding persisted with this packet.
    pub replay_binding: NativeInstallGateReplayBinding,
    /// Consumer verdict binding persisted with this packet.
    pub consumer_verdict: NativeInstallGateConsumerVerdictBinding,
    /// Boolean effects authorized by this decision.
    pub actions: NativeInstallGateActions,
}

impl NativeInstallGatePacket {
    /// Return true when the packet authorizes install on this surface.
    pub const fn is_installable(&self) -> bool {
        self.disposition.is_installable()
    }

    /// Return a verdict using the persisted requested authority.
    pub fn verdict(&self) -> NativeInstallGateVerdict {
        NativeInstallGateVerdict::from_packet(self)
    }

    /// Return a compact upstream admission summary for this packet.
    pub fn admission_summary(&self) -> NativeInstallGateAdmissionSummary {
        NativeInstallGateAdmissionSummary::from_packet(self)
    }

    /// Return the trust_ir shared-primitive contract owned by this packet's surface.
    pub const fn shared_primitive_contract(
        &self,
    ) -> Option<trust_ir::NativeSharedPrimitiveContractDescriptor> {
        self.surface.shared_primitive_contract()
    }

    /// Return the stable reason for this packet's shared-primitive contract behavior.
    pub const fn shared_primitive_contract_reason(
        &self,
    ) -> NativeInstallGateSharedPrimitiveContractReason {
        self.surface.shared_primitive_contract_reason()
    }
}

/// Typed reason for refusing to build a non-promoting product-promotion packet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NativeInstallGateProductPromotionRejectionReason {
    /// The proof-optimization citation itself is absent or has no identity.
    MissingProofOptimizationCitation,
    /// The proof-optimization citation does not bind this TY native-fused artifact.
    ProofOptimizationCitationMismatch,
    /// The proof-validation hash is absent from either the gate packet or citation.
    MissingValidationHash,
    /// Replay identity evidence is absent.
    MissingReplayIdentity,
    /// Replay identity evidence does not match the gate packet.
    ReplayIdentityMismatch,
    /// Replay binding evidence is absent.
    MissingReplayBinding,
    /// Replay binding evidence does not match the canonical gate packet.
    ReplayBindingMismatch,
    /// Decision telemetry evidence is absent.
    MissingTelemetry,
    /// Decision telemetry evidence does not match the gate packet or manifest.
    TelemetryMismatch,
    /// Useful-native telemetry already recorded a nonzero delta.
    UsefulNativeDeltaNonzero,
    /// The manifest is not the TY native-fused parent-loop schema.
    ManifestMissingTyFusedSchema,
    /// Required TY native-fused proof-fact metadata is missing.
    ManifestMissingRequiredFacts,
    /// Status/deopt contract metadata is missing or inconsistent.
    ManifestMissingStatusDeoptContract,
    /// Rollback/deopt condition metadata is missing or inconsistent.
    ManifestMissingRollbackMetadata,
    /// The gate packet is not an installable TY native-fused activation packet.
    GateNotTyNativeFusedActivation,
    /// The input already requests approved product promotion.
    ProductPromotionRequestedApproved,
    /// Local reducer evidence schema/hash/family metadata is absent.
    MissingReducerEvidenceBinding,
    /// Local reducer evidence metadata does not match the current reducer summary.
    ReducerEvidenceBindingMismatch,
    /// Local reducer evidence does not cover every required reducer family with green rows.
    ReducerEvidenceCoverageIncomplete,
}

impl NativeInstallGateProductPromotionRejectionReason {
    /// Return the stable lower-snake-case reason id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingProofOptimizationCitation => "missing_proof_optimization_citation",
            Self::ProofOptimizationCitationMismatch => "proof_optimization_citation_mismatch",
            Self::MissingValidationHash => "missing_validation_hash",
            Self::MissingReplayIdentity => "missing_replay_identity",
            Self::ReplayIdentityMismatch => "replay_identity_mismatch",
            Self::MissingReplayBinding => "missing_replay_binding",
            Self::ReplayBindingMismatch => "replay_binding_mismatch",
            Self::MissingTelemetry => "missing_telemetry",
            Self::TelemetryMismatch => "telemetry_mismatch",
            Self::UsefulNativeDeltaNonzero => "useful_native_delta_nonzero",
            Self::ManifestMissingTyFusedSchema => "manifest_missing_ty_fused_schema",
            Self::ManifestMissingRequiredFacts => "manifest_missing_required_facts",
            Self::ManifestMissingStatusDeoptContract => "manifest_missing_status_deopt_contract",
            Self::ManifestMissingRollbackMetadata => "manifest_missing_rollback_metadata",
            Self::GateNotTyNativeFusedActivation => "gate_not_ty_native_fused_activation",
            Self::ProductPromotionRequestedApproved => "product_promotion_requested_approved",
            Self::MissingReducerEvidenceBinding => "missing_reducer_evidence_binding",
            Self::ReducerEvidenceBindingMismatch => "reducer_evidence_binding_mismatch",
            Self::ReducerEvidenceCoverageIncomplete => "reducer_evidence_coverage_incomplete",
        }
    }
}

/// One required TY native-fused fact binding serialized into a product packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateProductPromotionRequiredFactBinding {
    /// Stable proof-evidence metadata key.
    pub evidence_metadata_key: &'static str,
    /// Required fact id.
    pub fact: &'static str,
    /// Manifest metadata value for this fact.
    pub manifest_metadata_value: String,
    /// Invalidation metadata value for this fact.
    pub invalidation_metadata_value: String,
}

/// Data-only product-promotion packet for TY native-fused parent loops.
///
/// This packet intentionally denies product promotion and useful-native credit.
/// It exists only to serialize and bind the parent gate, replay, telemetry,
/// manifest rollback/deopt, and proof-optimization citation evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeInstallGateProductPromotionPacket {
    /// Packet schema.
    pub schema: &'static str,
    /// Packet schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Artifact id.
    pub artifact_id: String,
    /// Manifest checksum.
    pub manifest_checksum: ArtifactChecksum,
    /// Gate packet hash consumed by this packet.
    pub gate_packet_hash: ArtifactChecksum,
    /// Consumer.
    pub consumer: String,
    /// Consumer mode.
    pub consumer_mode: String,
    /// Product surface.
    pub surface: NativeInstallGateSurface,
    /// Product promotion is explicitly denied by this slice.
    pub product_promotion_allowed: bool,
    /// Stable non-promoting disposition.
    pub product_promotion_disposition: &'static str,
    /// Useful-native credit is explicitly denied by this slice.
    pub promotion_useful_native_credit_allowed: bool,
    /// TY native-fused manifest schema value.
    pub ty_manifest_schema: String,
    /// Status/deopt contract bound by the manifest, layout, and invalidation key.
    pub status_deopt_contract: String,
    /// Rollback/deopt condition bound by the manifest.
    pub deopt_rollback_condition: String,
    /// Missing-proof disposition bound by the manifest.
    pub missing_proof_disposition: String,
    /// Manifest useful-native policy.
    pub useful_native_manifest_policy: String,
    /// Local reducer evidence packet schema.
    pub reducer_evidence_schema: String,
    /// Local reducer evidence packet schema version.
    pub reducer_evidence_schema_version: u32,
    /// Canonical local reducer evidence packet hash.
    pub reducer_evidence_packet_sha256: String,
    /// Sorted local reducer family coverage bound by the packet.
    pub reducer_evidence_families: Vec<String>,
    /// Required proof-fact bindings copied from manifest and invalidation metadata.
    pub required_fact_bindings: Vec<NativeInstallGateProductPromotionRequiredFactBinding>,
    /// Parent proof certificate identity named by TY evidence metadata.
    pub parent_proof_certificate_identity: String,
    /// #795 proof-optimization function name.
    pub proof_optimization_function_name: String,
    /// #795 proof-optimization certificate id.
    pub proof_optimization_certificate_id: String,
    /// #795 proof-optimization proof hash.
    pub proof_optimization_proof_hash: String,
    /// #795 proof-optimization validation hash.
    pub proof_optimization_validation_hash: String,
    /// #795 proof-optimization source-region hash.
    pub proof_optimization_source_region_hash: String,
    /// #795 proof-optimization target-region hash.
    pub proof_optimization_target_region_hash: String,
    /// #795 proof-optimization transform name.
    pub proof_optimization_transform_name: String,
    /// #795 proof-optimization transform version.
    pub proof_optimization_transform_version: u32,
    /// #795 proof-optimization admission route.
    pub proof_optimization_admission: String,
    /// #795 proof-optimization certificate kind.
    pub proof_optimization_kind: String,
    /// #795 proof-optimization application status.
    pub proof_optimization_status: String,
    /// Gate/proof validation hash from the install-gate validation packet.
    pub gate_proof_validation_hash: String,
    /// Replay identity record hash.
    pub replay_identity_sha256: String,
    /// Replay root bound by proof metadata and replay identity.
    pub replay_root_sha256: String,
    /// Replay binding packet hash.
    pub replay_binding_packet_hash: ArtifactChecksum,
    /// Replay binding root derived from the canonical gate packet.
    pub replay_binding_replay_root_sha256: String,
    /// Shared install-gate consumer verdict hash.
    pub install_consumer_verdict_sha256: String,
    /// Telemetry event id.
    pub telemetry_event_id: String,
    /// Telemetry record hash.
    pub telemetry_record_sha256: String,
    /// Telemetry counter scope.
    pub telemetry_counter_scope: String,
    /// Telemetry useful-native delta, required to remain zero.
    pub telemetry_useful_native_delta: u64,
    /// Whether the parent gate considered useful-native accounting eligible.
    pub gate_useful_native_eligible: bool,
    /// Whether the parent gate authorized TY native activation.
    pub gate_ty_native_activate: bool,
    /// Canonical hash over this non-promoting product packet.
    pub packet_sha256: String,
}

impl NativeInstallGateProductPromotionPacket {
    /// Return the stable hash of this product packet.
    pub fn canonical_packet_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_u64(&mut out, self.issue);
        put_str(&mut out, &self.artifact_id);
        put_checksum(&mut out, self.manifest_checksum);
        put_checksum(&mut out, self.gate_packet_hash);
        put_str(&mut out, &self.consumer);
        put_str(&mut out, &self.consumer_mode);
        put_str(&mut out, self.surface.as_str());
        put_bool(&mut out, self.product_promotion_allowed);
        put_str(&mut out, self.product_promotion_disposition);
        put_bool(&mut out, self.promotion_useful_native_credit_allowed);
        put_str(&mut out, &self.ty_manifest_schema);
        put_str(&mut out, &self.status_deopt_contract);
        put_str(&mut out, &self.deopt_rollback_condition);
        put_str(&mut out, &self.missing_proof_disposition);
        put_str(&mut out, &self.useful_native_manifest_policy);
        put_str(&mut out, &self.reducer_evidence_schema);
        put_u32(&mut out, self.reducer_evidence_schema_version);
        put_str(&mut out, &self.reducer_evidence_packet_sha256);
        put_u64(&mut out, self.reducer_evidence_families.len() as u64);
        for family in &self.reducer_evidence_families {
            put_str(&mut out, family);
        }
        put_u64(&mut out, self.required_fact_bindings.len() as u64);
        for fact in &self.required_fact_bindings {
            put_str(&mut out, fact.evidence_metadata_key);
            put_str(&mut out, fact.fact);
            put_str(&mut out, &fact.manifest_metadata_value);
            put_str(&mut out, &fact.invalidation_metadata_value);
        }
        put_str(&mut out, &self.parent_proof_certificate_identity);
        put_str(&mut out, &self.proof_optimization_function_name);
        put_str(&mut out, &self.proof_optimization_certificate_id);
        put_str(&mut out, &self.proof_optimization_proof_hash);
        put_str(&mut out, &self.proof_optimization_validation_hash);
        put_str(&mut out, &self.proof_optimization_source_region_hash);
        put_str(&mut out, &self.proof_optimization_target_region_hash);
        put_str(&mut out, &self.proof_optimization_transform_name);
        put_u32(&mut out, self.proof_optimization_transform_version);
        put_str(&mut out, &self.proof_optimization_admission);
        put_str(&mut out, &self.proof_optimization_kind);
        put_str(&mut out, &self.proof_optimization_status);
        put_str(&mut out, &self.gate_proof_validation_hash);
        put_str(&mut out, &self.replay_identity_sha256);
        put_str(&mut out, &self.replay_root_sha256);
        put_checksum(&mut out, self.replay_binding_packet_hash);
        put_str(&mut out, &self.replay_binding_replay_root_sha256);
        put_str(&mut out, &self.install_consumer_verdict_sha256);
        put_str(&mut out, &self.telemetry_event_id);
        put_str(&mut out, &self.telemetry_record_sha256);
        put_str(&mut out, &self.telemetry_counter_scope);
        put_u64(&mut out, self.telemetry_useful_native_delta);
        put_bool(&mut out, self.gate_useful_native_eligible);
        put_bool(&mut out, self.gate_ty_native_activate);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return this packet with `packet_sha256` set canonically.
    pub fn with_canonical_packet_sha256(mut self) -> Self {
        self.packet_sha256 = self.canonical_packet_sha256();
        self
    }
}

/// Validate a native install candidate and return a metadata-only packet.
pub fn validate_native_install_gate(input: &NativeInstallGateInput) -> NativeInstallGatePacket {
    let decision = validate_decision(input);
    build_packet(input, decision.0, decision.1)
}

/// Validate a native install candidate and return the install verdict API.
pub fn validate_native_install_gate_verdict(
    input: &NativeInstallGateInput,
) -> NativeInstallGateVerdict {
    let packet = validate_native_install_gate(input);
    NativeInstallGateVerdict::from_packet(&packet)
}

/// Compute the canonical packet hash used by cache, release, replay, and telemetry evidence.
pub fn native_install_gate_packet_hash(packet: &NativeInstallGatePacket) -> ArtifactChecksum {
    let mut out = Vec::new();
    put_str(&mut out, "trust-cg.native_install_gate.packet_hash.v1");
    put_str(&mut out, packet.schema);
    put_u32(&mut out, packet.schema_version);
    put_u64(&mut out, packet.gate_issue);
    put_u64(&mut out, packet.design_issue);
    put_str(&mut out, &packet.consumer);
    put_str(&mut out, &packet.consumer_mode);
    put_str(&mut out, packet.surface.as_str());
    put_str(&mut out, packet.requested_authority.as_str());

    put_str(&mut out, &packet.artifact.artifact_id);
    put_str(&mut out, &packet.artifact.manifest_schema);
    put_u32(&mut out, packet.artifact.manifest_schema_version);
    put_checksum(&mut out, packet.artifact.manifest_checksum);
    put_str(&mut out, &packet.artifact.source_sha256);
    put_str(&mut out, &packet.artifact.trust_ir_sha256);
    put_str(&mut out, &packet.artifact.native_payload_sha256);
    put_checksum(&mut out, packet.artifact.target_checksum);
    put_checksum(&mut out, packet.artifact.abi_checksum);
    put_checksum(&mut out, packet.artifact.layout_checksum);
    put_checksum(&mut out, packet.artifact.proof_policy_checksum);
    put_checksum(&mut out, packet.artifact.invalidation_checksum);
    put_str_map(&mut out, &packet.artifact.manifest_metadata);

    put_str(&mut out, packet.validation.layout_status);
    put_option_str(
        &mut out,
        packet.validation.layout_evidence_sha256.as_deref(),
    );
    put_option_str(
        &mut out,
        packet.validation.layout_wrapper_identity.as_deref(),
    );
    put_option_str(
        &mut out,
        packet.validation.layout_validation_provenance.as_deref(),
    );
    put_option_checksum(&mut out, packet.validation.layout_invalidation_checksum);
    put_u64(
        &mut out,
        packet.validation.layout_generation_domains.len() as u64,
    );
    for domain in &packet.validation.layout_generation_domains {
        put_str(&mut out, domain);
    }
    put_str(&mut out, packet.validation.proof_verdict);
    put_option_str(&mut out, packet.validation.proof_reject_code);
    put_option_str(&mut out, packet.validation.proof_verifier.as_deref());
    put_option_str(&mut out, packet.validation.proof_report_sha256.as_deref());
    put_option_str(&mut out, packet.validation.obligation_set.as_deref());
    put_option_u64(&mut out, packet.validation.timeout_ms);

    put_u64(&mut out, packet.freshness.artifact_generation);
    put_u64(&mut out, packet.freshness.current_generation);
    put_u64(&mut out, packet.freshness.freshness_domains.len() as u64);
    for observation in &packet.freshness.freshness_domains {
        put_str(&mut out, &observation.domain);
        put_u64(&mut out, observation.observed_generation);
        put_u64(&mut out, observation.current_generation);
    }
    put_bool(&mut out, packet.freshness.revoked);
    put_option_deny_control(&mut out, packet.freshness.deny_control.as_ref());
    put_option_replay_identity(&mut out, packet.replay_identity.as_ref());

    if let Some(telemetry) = &packet.telemetry {
        put_bool(&mut out, true);
        put_str(&mut out, &telemetry.schema);
        put_u32(&mut out, telemetry.schema_version);
        put_str(&mut out, &telemetry.event_id);
        put_str(&mut out, &telemetry.counter_scope);
        put_str(&mut out, &telemetry.record_sha256);
        put_str(&mut out, &telemetry.artifact_id);
        put_checksum(&mut out, telemetry.manifest_checksum);
        put_option_str(&mut out, telemetry.proof_report_sha256.as_deref());
        put_checksum(&mut out, telemetry.layout_checksum);
        put_checksum(&mut out, telemetry.invalidation_checksum);
        put_str(&mut out, telemetry.disposition.as_str());
        put_option_str(
            &mut out,
            telemetry
                .rejection_code
                .map(NativeInstallGateRejectionCode::as_str),
        );
        put_str(&mut out, telemetry.install_authority.as_str());
        put_u64(&mut out, telemetry.useful_native_delta);
    } else {
        put_bool(&mut out, false);
    }

    put_str(&mut out, packet.disposition.as_str());
    put_option_str(
        &mut out,
        packet
            .rejection_code
            .map(NativeInstallGateRejectionCode::as_str),
    );
    put_str(&mut out, packet.install_authority.as_str());
    put_actions(&mut out, packet.actions);
    ArtifactChecksum::for_bytes(&out)
}

/// Expected Petri/MCC native successor admission context.
#[derive(Debug, Clone, Copy)]
pub struct PetriNativeSuccessorAdmissionExpected<'a> {
    /// Downstream consumer name.
    pub consumer: &'a str,
    /// Downstream consumer mode.
    pub consumer_mode: &'a str,
    /// Stable native request kind.
    pub kind: &'a str,
    /// Product surface.
    pub surface: NativeInstallGateSurface,
    /// Requested authority. Defaults to validation-only.
    pub requested_authority: NativeInstallGateAuthority,
    /// Optional target ABI digest the caller expects from the trust_ir bundle.
    pub target_abi_digest: Option<trust_ir::ProofDigest>,
    /// Optional compiled native payload identity expected by an install packet.
    pub native_payload_sha256: Option<&'a str>,
    /// Optional persisted native install-gate packet to bind to the trust_ir bundle.
    pub native_install_gate_packet: Option<&'a NativeInstallGatePacket>,
}

impl<'a> PetriNativeSuccessorAdmissionExpected<'a> {
    /// Return the fail-closed validation-only MCC/Petri native successor expectation.
    pub const fn validation_only() -> Self {
        Self {
            consumer: PETRI_NATIVE_SUCCESSOR_CONSUMER,
            consumer_mode: PETRI_NATIVE_SUCCESSOR_CONSUMER_MODE,
            kind: PETRI_NATIVE_SUCCESSOR_KIND,
            surface: NativeInstallGateSurface::NativeSuccessor,
            requested_authority: NativeInstallGateAuthority::ValidationOnly,
            target_abi_digest: None,
            native_payload_sha256: None,
            native_install_gate_packet: None,
        }
    }

    /// Return an explicit callable MCC/Petri native successor expectation.
    pub const fn canary_callable() -> Self {
        Self {
            consumer: PETRI_NATIVE_SUCCESSOR_CONSUMER,
            consumer_mode: PETRI_NATIVE_SUCCESSOR_CONSUMER_MODE,
            kind: PETRI_NATIVE_SUCCESSOR_KIND,
            surface: NativeInstallGateSurface::NativeSuccessor,
            requested_authority: NativeInstallGateAuthority::CanaryCallable,
            target_abi_digest: None,
            native_payload_sha256: None,
            native_install_gate_packet: None,
        }
    }

    /// Bind an expected trust_ir target ABI digest.
    pub fn with_target_abi_digest(mut self, digest: trust_ir::ProofDigest) -> Self {
        self.target_abi_digest = Some(digest);
        self
    }

    /// Bind an expected compiled native payload identity.
    pub fn with_native_payload_sha256(mut self, native_payload_sha256: &'a str) -> Self {
        self.native_payload_sha256 = Some(native_payload_sha256);
        self
    }

    /// Bind an existing install-gate packet to the trust_ir bundle.
    pub fn with_native_install_gate_packet(mut self, packet: &'a NativeInstallGatePacket) -> Self {
        self.native_install_gate_packet = Some(packet);
        self
    }
}

impl<'a> Default for PetriNativeSuccessorAdmissionExpected<'a> {
    fn default() -> Self {
        Self::validation_only()
    }
}

/// Expected Petri/MCC native successor callable execution context.
#[derive(Debug, Clone, Copy)]
pub struct PetriNativeSuccessorExecutionExpected<'a> {
    /// Admission evidence expectation.
    pub admission: PetriNativeSuccessorAdmissionExpected<'a>,
    /// trust_ir function name for one native successor step.
    pub entry_function: &'a str,
    /// Input state byte width consumed by the callable ABI.
    pub input_state_bytes: u64,
    /// Output state byte width produced by the callable ABI.
    pub output_state_bytes: u64,
    /// Required byte alignment for input and output state buffers.
    pub state_alignment_bytes: u32,
    /// Optional compiled trampoline contract expected by the execution plan.
    pub trampoline_contract: Option<&'a PetriNativeSuccessorTrampolineContract>,
}

impl<'a> PetriNativeSuccessorExecutionExpected<'a> {
    /// Return the fail-closed validation-only MCC/Petri native successor execution expectation.
    pub const fn validation_only(entry_function: &'a str, state_bytes: u64) -> Self {
        Self {
            admission: PetriNativeSuccessorAdmissionExpected::validation_only(),
            entry_function,
            input_state_bytes: state_bytes,
            output_state_bytes: state_bytes,
            state_alignment_bytes: 8,
            trampoline_contract: None,
        }
    }

    /// Return an explicit callable MCC/Petri native successor execution expectation.
    pub const fn canary_callable(entry_function: &'a str, state_bytes: u64) -> Self {
        Self {
            admission: PetriNativeSuccessorAdmissionExpected::canary_callable(),
            entry_function,
            input_state_bytes: state_bytes,
            output_state_bytes: state_bytes,
            state_alignment_bytes: 8,
            trampoline_contract: None,
        }
    }

    /// Bind an expected trust_ir target ABI digest.
    pub fn with_target_abi_digest(mut self, digest: trust_ir::ProofDigest) -> Self {
        self.admission = self.admission.with_target_abi_digest(digest);
        self
    }

    /// Bind an expected compiled native payload identity.
    pub fn with_native_payload_sha256(mut self, native_payload_sha256: &'a str) -> Self {
        self.admission = self
            .admission
            .with_native_payload_sha256(native_payload_sha256);
        self
    }

    /// Bind an expected compiled trampoline contract.
    pub fn with_trampoline_contract(
        mut self,
        trampoline_contract: &'a PetriNativeSuccessorTrampolineContract,
    ) -> Self {
        self.trampoline_contract = Some(trampoline_contract);
        self
    }

    /// Bind an existing install-gate packet to the trust_ir bundle.
    pub fn with_native_install_gate_packet(mut self, packet: &'a NativeInstallGatePacket) -> Self {
        self.admission = self.admission.with_native_install_gate_packet(packet);
        self
    }

    /// Override the input/output state buffer layout.
    pub const fn with_state_layout(
        mut self,
        input_state_bytes: u64,
        output_state_bytes: u64,
        state_alignment_bytes: u32,
    ) -> Self {
        self.input_state_bytes = input_state_bytes;
        self.output_state_bytes = output_state_bytes;
        self.state_alignment_bytes = state_alignment_bytes;
        self
    }
}

/// Stable callable ABI contract for a Petri/MCC native successor entrypoint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorCallableContract {
    /// Callable contract schema.
    pub schema: &'static str,
    /// Callable contract schema version.
    pub schema_version: u32,
    /// Consumer.
    pub consumer: String,
    /// Consumer family or mode.
    pub consumer_mode: String,
    /// Native request kind.
    pub kind: String,
    /// Product surface.
    pub surface: &'static str,
    /// trust_ir function name for one native successor step.
    pub entry_function: String,
    /// Stable state encoding.
    pub state_encoding: &'static str,
    /// Input state byte width.
    pub input_state_bytes: u64,
    /// Output state byte width.
    pub output_state_bytes: u64,
    /// Required input/output byte alignment.
    pub state_alignment_bytes: u32,
    /// Artifact id bound to the admission packet namespace.
    pub artifact_id: String,
    /// Consumer source SHA-256.
    pub source_sha256: String,
    /// Canonical trust_ir SHA-256.
    pub trust_ir_sha256: String,
    /// Native payload SHA-256.
    pub native_payload_sha256: String,
    /// trust_ir transport identity digest.
    pub transport_digest: String,
    /// trust_ir bundle digest.
    pub bundle_digest: String,
    /// trust_ir target ABI digest.
    pub target_abi_digest: Option<String>,
    /// Canonical callable contract hash.
    pub callable_contract_sha256: String,
}

impl PetriNativeSuccessorCallableContract {
    /// Return the stable hash of this callable contract.
    pub fn canonical_contract_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, &self.consumer);
        put_str(&mut out, &self.consumer_mode);
        put_str(&mut out, &self.kind);
        put_str(&mut out, self.surface);
        put_str(&mut out, &self.entry_function);
        put_str(&mut out, self.state_encoding);
        put_u64(&mut out, self.input_state_bytes);
        put_u64(&mut out, self.output_state_bytes);
        put_u32(&mut out, self.state_alignment_bytes);
        put_str(&mut out, &self.artifact_id);
        put_str(&mut out, &self.source_sha256);
        put_str(&mut out, &self.trust_ir_sha256);
        put_str(&mut out, &self.native_payload_sha256);
        put_str(&mut out, &self.transport_digest);
        put_str(&mut out, &self.bundle_digest);
        put_option_str(&mut out, self.target_abi_digest.as_deref());
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_contract_sha256(mut self) -> Self {
        self.callable_contract_sha256 = self.canonical_contract_sha256();
        self
    }
}

/// Stable compiled trampoline contract for a Petri/MCC native successor entrypoint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorTrampolineContract {
    /// Trampoline contract schema.
    pub schema: &'static str,
    /// Trampoline contract schema version.
    pub schema_version: u32,
    /// Native symbol that hosts the Petri successor trampoline.
    pub entry_symbol: String,
    /// Stable trampoline ABI.
    pub trampoline_abi: &'static str,
    /// Callable contract hash this trampoline implements.
    pub callable_contract_sha256: String,
    /// Compiled native payload identity.
    pub native_payload_sha256: String,
    /// Canonical trampoline contract hash.
    pub trampoline_sha256: String,
}

impl PetriNativeSuccessorTrampolineContract {
    /// Return the stable hash of this trampoline contract.
    pub fn canonical_trampoline_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, &self.entry_symbol);
        put_str(&mut out, self.trampoline_abi);
        put_str(&mut out, &self.callable_contract_sha256);
        put_str(&mut out, &self.native_payload_sha256);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_trampoline_sha256(mut self) -> Self {
        self.trampoline_sha256 = self.canonical_trampoline_sha256();
        self
    }

    fn binds_callable_contract(&self, contract: &PetriNativeSuccessorCallableContract) -> bool {
        self.schema == PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA
            && self.schema_version == PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA_VERSION
            && self.trampoline_abi == PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_ABI_STABLE_BYTES_V1
            && !missing_required_text(&self.entry_symbol)
            && self.callable_contract_sha256 == contract.callable_contract_sha256
            && self.native_payload_sha256 == contract.native_payload_sha256
            && self.trampoline_sha256 == self.canonical_trampoline_sha256()
    }
}

/// Build a stable compiled trampoline contract for a Petri/MCC successor callable.
pub fn petri_native_successor_trampoline_contract(
    callable_contract: &PetriNativeSuccessorCallableContract,
    entry_symbol: impl Into<String>,
    native_payload_sha256: impl Into<String>,
) -> Option<PetriNativeSuccessorTrampolineContract> {
    let entry_symbol = entry_symbol.into();
    let native_payload_sha256 = native_payload_sha256.into();
    if missing_required_text(&entry_symbol)
        || missing_required_text(&native_payload_sha256)
        || native_payload_sha256 != callable_contract.native_payload_sha256
    {
        return None;
    }

    Some(
        PetriNativeSuccessorTrampolineContract {
            schema: PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA,
            schema_version: PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA_VERSION,
            entry_symbol,
            trampoline_abi: PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_ABI_STABLE_BYTES_V1,
            callable_contract_sha256: callable_contract.callable_contract_sha256.clone(),
            native_payload_sha256,
            trampoline_sha256: String::new(),
        }
        .with_canonical_trampoline_sha256(),
    )
}

/// Petri/MCC native successor execution plan.
///
/// A callable contract may be present before Trust Codegen grants callable authority.
/// Callers must require `callable_authorized == true` before publishing or
/// invoking native code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionPlan {
    /// Execution plan schema.
    pub schema: &'static str,
    /// Execution plan schema version.
    pub schema_version: u32,
    /// Existing native install-gate admission summary.
    pub admission_summary: NativeInstallGateAdmissionSummary,
    /// Stable callable ABI contract when the trust_ir bundle can identify one.
    pub callable_contract: Option<PetriNativeSuccessorCallableContract>,
    /// Stable blocker that explains why the callable ABI contract is absent.
    pub callable_contract_blocker: Option<PetriNativeSuccessorCallableContractBlocker>,
    /// Readiness stage that produced the callable contract blocker.
    pub callable_contract_blocker_stage: Option<&'static str>,
    /// Stable reason code for the missing callable ABI contract.
    pub callable_contract_reason_code: Option<&'static str>,
    /// Exact field required to clear the callable contract blocker, when applicable.
    pub callable_contract_required_field: Option<&'static str>,
    /// Exact evidence schema required to clear the callable contract blocker, when applicable.
    pub callable_contract_required_evidence: Option<&'static str>,
    /// Stable compiled trampoline contract when available.
    pub trampoline_contract: Option<PetriNativeSuccessorTrampolineContract>,
    /// Whether admission authorizes publishing/invoking the native callable.
    pub callable_authorized: bool,
    /// Whether the plan must remain on the non-native fallback path.
    pub fail_closed: bool,
    /// Stable fail-closed reason code from admission.
    pub reason_code: Option<&'static str>,
}

/// Stable blocker for constructing a Petri/MCC native successor callable contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorCallableContractBlocker {
    /// The requested consumer/surface/authority is not supported by the Petri native lane.
    UnsupportedExpected,
    /// The requested state-buffer ABI is invalid.
    InvalidStateLayout,
    /// The requested trust_ir entry function is absent or empty.
    MissingEntryFunction,
    /// The requested target ABI digest does not match the trust_ir bundle.
    TargetAbiMismatch,
    /// The trust_ir semantic bridge is not ready.
    SemanticBridge(PetriNativeSuccessorSemanticBridgeBlocker),
}

impl PetriNativeSuccessorCallableContractBlocker {
    /// Return the readiness stage that produced this blocker.
    pub const fn stage(self) -> &'static str {
        match self {
            Self::UnsupportedExpected => "expected",
            Self::InvalidStateLayout => "state_layout",
            Self::MissingEntryFunction => "module",
            Self::TargetAbiMismatch => "target_abi",
            Self::SemanticBridge(_) => "semantic_bridge",
        }
    }

    /// Return the stable lower-snake-case blocker string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnsupportedExpected => "unsupported_expected",
            Self::InvalidStateLayout => "invalid_state_layout",
            Self::MissingEntryFunction => "missing_entry_function",
            Self::TargetAbiMismatch => "target_abi_mismatch",
            Self::SemanticBridge(blocker) => blocker.as_str(),
        }
    }

    /// Return the exact field required to clear this blocker.
    pub const fn required_field(self) -> &'static str {
        match self {
            Self::UnsupportedExpected => "expected",
            Self::InvalidStateLayout => "state_layout",
            Self::MissingEntryFunction => "entry_function",
            Self::TargetAbiMismatch => "target_abi_digest",
            Self::SemanticBridge(blocker) => blocker.required_field(),
        }
    }

    /// Return the exact evidence schema required to clear this blocker.
    pub const fn required_evidence(self) -> &'static str {
        match self {
            Self::UnsupportedExpected
            | Self::InvalidStateLayout
            | Self::MissingEntryFunction
            | Self::TargetAbiMismatch => PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_SCHEMA,
            Self::SemanticBridge(blocker) => blocker.required_evidence(),
        }
    }
}

/// Non-null host callable pointer identity for a Petri/MCC native successor trampoline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PetriNativeSuccessorCallablePointer {
    addr: NonZeroUsize,
}

impl PetriNativeSuccessorCallablePointer {
    /// Construct a callable pointer identity from an already non-null address.
    pub const fn new(addr: NonZeroUsize) -> Self {
        Self { addr }
    }

    /// Construct a callable pointer identity from a raw address.
    pub fn from_usize(addr: usize) -> Option<Self> {
        NonZeroUsize::new(addr).map(Self::new)
    }

    /// Construct a callable pointer identity from a raw non-null pointer.
    pub fn from_ptr<T>(ptr: *const T) -> Option<Self> {
        Self::from_usize(ptr.cast::<()>() as usize)
    }

    /// Return the non-null callable address.
    pub const fn addr(self) -> NonZeroUsize {
        self.addr
    }

    /// Return the callable address as a machine word for host-side lookup tables.
    pub fn addr_usize(self) -> usize {
        self.addr.get()
    }
}

/// Authorized host call handoff for a Petri/MCC native successor trampoline.
///
/// This packet binds an explicit non-null host pointer to an already accepted
/// native install-gate packet plus the Petri callable/trampoline identities. It
/// is still canary-callable evidence: callers must not infer TY production
/// activation from this packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorCallPacket {
    /// Call packet schema.
    pub schema: &'static str,
    /// Call packet schema version.
    pub schema_version: u32,
    /// Canonical install-gate packet hash that authorized callable exposure.
    pub install_packet_hash: ArtifactChecksum,
    /// Persisted install-gate packet hash.
    pub persisted_install_packet_hash: ArtifactChecksum,
    /// Existing install-gate admission summary.
    pub admission_summary: NativeInstallGateAdmissionSummary,
    /// Non-null host callable pointer identity.
    pub callable_pointer: PetriNativeSuccessorCallablePointer,
    /// Petri callable contract hash.
    pub callable_contract_sha256: String,
    /// Compiled trampoline contract hash.
    pub trampoline_sha256: String,
    /// Compiled native payload identity.
    pub native_payload_sha256: String,
    /// Native symbol that hosts the trampoline.
    pub entry_symbol: String,
    /// Stable trampoline ABI.
    pub trampoline_abi: &'static str,
    /// trust_ir function name for one native successor step.
    pub entry_function: String,
    /// Stable state encoding.
    pub state_encoding: &'static str,
    /// Input state byte width.
    pub input_state_bytes: u64,
    /// Output state byte width.
    pub output_state_bytes: u64,
    /// Required input/output byte alignment.
    pub state_alignment_bytes: u32,
    /// Whether install-gate admission authorized callable exposure.
    pub callable_authorized: bool,
    /// Whether the call packet is fail-closed.
    pub fail_closed: bool,
    /// Stable fail-closed reason code, if any.
    pub reason_code: Option<&'static str>,
    /// Canonical call-packet hash.
    pub call_packet_sha256: String,
}

impl PetriNativeSuccessorCallPacket {
    /// Return the stable hash of this host call handoff packet.
    pub fn canonical_call_packet_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.call_packet_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_checksum(&mut out, self.install_packet_hash);
        put_checksum(&mut out, self.persisted_install_packet_hash);
        put_str(&mut out, &self.admission_summary.consumer);
        put_str(&mut out, &self.admission_summary.consumer_mode);
        put_str(&mut out, self.admission_summary.surface);
        put_str(&mut out, &self.admission_summary.artifact_id);
        put_checksum(&mut out, self.admission_summary.manifest_checksum);
        put_checksum(&mut out, self.admission_summary.target_checksum);
        put_checksum(&mut out, self.admission_summary.abi_checksum);
        put_checksum(&mut out, self.admission_summary.layout_checksum);
        put_checksum(&mut out, self.admission_summary.proof_policy_checksum);
        put_checksum(&mut out, self.admission_summary.invalidation_checksum);
        put_option_str(
            &mut out,
            self.admission_summary.proof_report_sha256.as_deref(),
        );
        put_str(&mut out, self.admission_summary.disposition);
        put_option_str(&mut out, self.admission_summary.reason_code);
        put_str(&mut out, self.admission_summary.requested_authority);
        put_str(&mut out, self.admission_summary.install_authority);
        put_actions(&mut out, self.admission_summary.actions);
        put_u64(&mut out, self.admission_summary.useful_native_delta);
        put_u64(&mut out, self.callable_pointer.addr_usize() as u64);
        put_str(&mut out, &self.callable_contract_sha256);
        put_str(&mut out, &self.trampoline_sha256);
        put_str(&mut out, &self.native_payload_sha256);
        put_str(&mut out, &self.entry_symbol);
        put_str(&mut out, self.trampoline_abi);
        put_str(&mut out, &self.entry_function);
        put_str(&mut out, self.state_encoding);
        put_u64(&mut out, self.input_state_bytes);
        put_u64(&mut out, self.output_state_bytes);
        put_u32(&mut out, self.state_alignment_bytes);
        put_bool(&mut out, self.callable_authorized);
        put_bool(&mut out, self.fail_closed);
        put_option_str(&mut out, self.reason_code);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_call_packet_sha256(mut self) -> Self {
        self.call_packet_sha256 = self.canonical_call_packet_sha256();
        self
    }
}

/// Stable source for a Petri/MCC native successor manifest identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorManifestIdentitySource {
    /// Identity came from a full native artifact manifest.
    ArtifactManifest,
    /// Identity was derived from the trust_ir transport/native install packet fields.
    PetriTransportIdentity,
}

impl PetriNativeSuccessorManifestIdentitySource {
    /// Return the stable lower-snake-case source string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ArtifactManifest => "artifact_manifest",
            Self::PetriTransportIdentity => "petri_transport_identity",
        }
    }

    fn from_packet(packet: &NativeInstallGatePacket) -> Self {
        if missing_required_text(&packet.artifact.manifest_schema) {
            Self::PetriTransportIdentity
        } else {
            Self::ArtifactManifest
        }
    }
}

/// Stable fail-closed blocker for deriving a Petri/MCC native successor manifest identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorManifestIdentityBlocker {
    /// No native install-gate packet was supplied.
    MissingNativeInstallGatePacket,
    /// The supplied packet belongs to a different consumer.
    UnsupportedConsumer,
    /// The supplied packet belongs to a different consumer mode.
    UnsupportedConsumerMode,
    /// The supplied packet belongs to a different native install surface.
    UnsupportedSurface,
    /// The packet hash no longer matches the packet content.
    PacketHashMismatch,
    /// The packet is missing its artifact id.
    MissingArtifactId,
    /// The packet is missing its manifest checksum.
    MissingManifestChecksum,
    /// The packet is missing its source SHA-256.
    MissingSourceSha256,
    /// The packet is missing its trust_ir SHA-256.
    MissingTrustIrSha256,
    /// The packet is missing its native payload SHA-256.
    MissingNativePayloadSha256,
    /// The packet is missing its target checksum.
    MissingTargetChecksum,
    /// The packet is missing its ABI checksum.
    MissingAbiChecksum,
    /// The packet is missing its layout checksum.
    MissingLayoutChecksum,
    /// The packet is missing its proof-policy checksum.
    MissingProofPolicyChecksum,
    /// The packet is missing its invalidation checksum.
    MissingInvalidationChecksum,
}

impl PetriNativeSuccessorManifestIdentityBlocker {
    /// Return the stable lower-snake-case blocker string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingNativeInstallGatePacket => "missing_native_install_gate_packet",
            Self::UnsupportedConsumer => "unsupported_consumer",
            Self::UnsupportedConsumerMode => "unsupported_consumer_mode",
            Self::UnsupportedSurface => "unsupported_surface",
            Self::PacketHashMismatch => "packet_hash_mismatch",
            Self::MissingArtifactId => "missing_artifact_id",
            Self::MissingManifestChecksum => "missing_manifest_checksum",
            Self::MissingSourceSha256 => "missing_source_sha256",
            Self::MissingTrustIrSha256 => "missing_trust_ir_sha256",
            Self::MissingNativePayloadSha256 => "missing_native_payload_sha256",
            Self::MissingTargetChecksum => "missing_target_checksum",
            Self::MissingAbiChecksum => "missing_abi_checksum",
            Self::MissingLayoutChecksum => "missing_layout_checksum",
            Self::MissingProofPolicyChecksum => "missing_proof_policy_checksum",
            Self::MissingInvalidationChecksum => "missing_invalidation_checksum",
        }
    }

    /// Return the exact install-packet field that must be supplied or corrected.
    pub const fn required_field(self) -> &'static str {
        match self {
            Self::MissingNativeInstallGatePacket => "native_install_gate_packet",
            Self::UnsupportedConsumer => "consumer",
            Self::UnsupportedConsumerMode => "consumer_mode",
            Self::UnsupportedSurface => "surface",
            Self::PacketHashMismatch => "packet_hash",
            Self::MissingArtifactId => "artifact.artifact_id",
            Self::MissingManifestChecksum => "artifact.manifest_checksum",
            Self::MissingSourceSha256 => "artifact.source_sha256",
            Self::MissingTrustIrSha256 => "artifact.trust_ir_sha256",
            Self::MissingNativePayloadSha256 => "artifact.native_payload_sha256",
            Self::MissingTargetChecksum => "artifact.target_checksum",
            Self::MissingAbiChecksum => "artifact.abi_checksum",
            Self::MissingLayoutChecksum => "artifact.layout_checksum",
            Self::MissingProofPolicyChecksum => "artifact.proof_policy_checksum",
            Self::MissingInvalidationChecksum => "artifact.invalidation_checksum",
        }
    }

    /// Return the evidence schema required to clear this blocker.
    pub const fn required_evidence(self) -> &'static str {
        NATIVE_INSTALL_GATE_PACKET_SCHEMA
    }
}

/// Concrete Petri/MCC native successor manifest identity derived by Trust Codegen.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorManifestIdentity {
    /// Manifest identity schema.
    pub schema: &'static str,
    /// Manifest identity schema version.
    pub schema_version: u32,
    /// Source of the manifest identity.
    pub source: PetriNativeSuccessorManifestIdentitySource,
    /// Canonical packet hash observed from the supplied install packet.
    pub packet_hash: ArtifactChecksum,
    /// Persisted packet hash copied from the supplied install packet.
    pub persisted_packet_hash: ArtifactChecksum,
    /// Consumer bound by the packet.
    pub consumer: String,
    /// Consumer mode bound by the packet.
    pub consumer_mode: String,
    /// Native install surface bound by the packet.
    pub surface: NativeInstallGateSurface,
    /// Artifact id bound by the packet.
    pub artifact_id: String,
    /// Manifest checksum bound by the packet.
    pub manifest_checksum: ArtifactChecksum,
    /// Source SHA-256 bound by the packet.
    pub source_sha256: String,
    /// trust_ir SHA-256 bound by the packet.
    pub trust_ir_sha256: String,
    /// Native payload SHA-256 bound by the packet.
    pub native_payload_sha256: String,
    /// Target checksum bound by the packet.
    pub target_checksum: ArtifactChecksum,
    /// ABI checksum bound by the packet.
    pub abi_checksum: ArtifactChecksum,
    /// Layout checksum bound by the packet.
    pub layout_checksum: ArtifactChecksum,
    /// Proof-policy checksum bound by the packet.
    pub proof_policy_checksum: ArtifactChecksum,
    /// Invalidation checksum bound by the packet.
    pub invalidation_checksum: ArtifactChecksum,
    /// Canonical manifest identity hash.
    pub manifest_identity_sha256: String,
}

impl PetriNativeSuccessorManifestIdentity {
    /// Return the stable source name for this manifest identity.
    pub const fn source_name(&self) -> &'static str {
        self.source.as_str()
    }

    /// Return the stable hash of this concrete manifest identity.
    pub fn canonical_manifest_identity_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.manifest_identity_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, self.source.as_str());
        put_str(&mut out, &self.consumer);
        put_str(&mut out, &self.consumer_mode);
        put_str(&mut out, self.surface.as_str());
        put_str(&mut out, &self.artifact_id);
        put_checksum(&mut out, self.manifest_checksum);
        put_str(&mut out, &self.source_sha256);
        put_str(&mut out, &self.trust_ir_sha256);
        put_str(&mut out, &self.native_payload_sha256);
        put_checksum(&mut out, self.target_checksum);
        put_checksum(&mut out, self.abi_checksum);
        put_checksum(&mut out, self.layout_checksum);
        put_checksum(&mut out, self.proof_policy_checksum);
        put_checksum(&mut out, self.invalidation_checksum);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_manifest_identity_sha256(mut self) -> Self {
        self.manifest_identity_sha256 = self.canonical_manifest_identity_sha256();
        self
    }
}

/// Stable blocker for Petri/MCC native successor install binding readiness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorInstallBindingBlocker {
    /// No native install-gate packet was supplied.
    MissingNativeInstallGatePacket,
    /// The packet did not carry a complete Petri manifest identity.
    MissingManifest,
    /// The packet hash or persisted packet identity did not validate.
    PacketHashMismatch,
    /// The packet does not authorize Petri native successor callable exposure.
    MissingCallableAuthority,
    /// No trampoline contract was supplied or bound in layout evidence.
    TrampolineUnbound,
    /// The supplied trampoline contract does not bind the packet layout/payload.
    TrampolineBindingMismatch,
}

impl PetriNativeSuccessorInstallBindingBlocker {
    /// Return the stable lower-snake-case blocker string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingNativeInstallGatePacket => "missing_native_install_gate_packet",
            Self::MissingManifest => "missing_manifest",
            Self::PacketHashMismatch => "packet_hash_mismatch",
            Self::MissingCallableAuthority => "missing_callable_authority",
            Self::TrampolineUnbound => "trampoline_unbound",
            Self::TrampolineBindingMismatch => "trampoline_binding_mismatch",
        }
    }

    /// Return the exact evidence schema required to clear this blocker, when applicable.
    pub const fn required_evidence(self) -> &'static str {
        match self {
            Self::MissingNativeInstallGatePacket
            | Self::PacketHashMismatch
            | Self::MissingCallableAuthority => NATIVE_INSTALL_GATE_PACKET_SCHEMA,
            Self::MissingManifest => PETRI_NATIVE_SUCCESSOR_MANIFEST_IDENTITY_SCHEMA,
            Self::TrampolineUnbound | Self::TrampolineBindingMismatch => {
                PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA
            }
        }
    }
}

/// Typed manifest/trampoline binding evidence for a Petri/MCC native successor install.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorInstallBindingEvidence {
    /// Install binding evidence schema.
    pub schema: &'static str,
    /// Install binding evidence schema version.
    pub schema_version: u32,
    /// Ready or blocked status.
    pub status: PetriNativeSuccessorExecutableCallStatus,
    /// Stable fail-closed blocker.
    pub blocker: Option<PetriNativeSuccessorInstallBindingBlocker>,
    /// Exact evidence schema required to clear this blocker, when applicable.
    pub required_evidence: Option<&'static str>,
    /// Canonical packet hash observed from the supplied install packet.
    pub packet_hash: Option<ArtifactChecksum>,
    /// Persisted packet hash copied from the supplied install packet.
    pub persisted_packet_hash: Option<ArtifactChecksum>,
    /// Manifest identity schema used for Petri transport-derived manifest evidence.
    pub manifest_identity_schema: &'static str,
    /// Manifest identity schema version.
    pub manifest_identity_schema_version: u32,
    /// Whether the manifest identity came from a full artifact manifest or Petri transport identity.
    pub manifest_source: Option<&'static str>,
    /// Canonical Petri manifest identity hash.
    pub manifest_identity_sha256: Option<String>,
    /// Artifact id bound by the packet.
    pub artifact_id: Option<String>,
    /// Manifest checksum bound by the packet.
    pub manifest_checksum: Option<ArtifactChecksum>,
    /// Source SHA-256 bound by the packet.
    pub source_sha256: Option<String>,
    /// trust_ir SHA-256 bound by the packet.
    pub trust_ir_sha256: Option<String>,
    /// Native payload SHA-256 bound by the packet.
    pub native_payload_sha256: Option<String>,
    /// Target checksum bound by the packet.
    pub target_checksum: Option<ArtifactChecksum>,
    /// ABI checksum bound by the packet.
    pub abi_checksum: Option<ArtifactChecksum>,
    /// Layout checksum bound by the packet.
    pub layout_checksum: Option<ArtifactChecksum>,
    /// Proof-policy checksum bound by the packet.
    pub proof_policy_checksum: Option<ArtifactChecksum>,
    /// Invalidation checksum bound by the packet.
    pub invalidation_checksum: Option<ArtifactChecksum>,
    /// Trampoline hash supplied by the caller.
    pub trampoline_sha256: Option<String>,
    /// Trampoline hash bound into layout evidence.
    pub layout_wrapper_identity: Option<String>,
    /// Native symbol that hosts the trampoline.
    pub entry_symbol: Option<String>,
    /// Stable trampoline ABI.
    pub trampoline_abi: Option<&'static str>,
    /// Canonical install binding evidence hash.
    pub install_binding_evidence_sha256: String,
}

impl PetriNativeSuccessorInstallBindingEvidence {
    /// Return true only when manifest identity and trampoline binding are both ready.
    pub const fn is_ready(&self) -> bool {
        matches!(self.status, PetriNativeSuccessorExecutableCallStatus::Ready)
            && self.blocker.is_none()
    }

    /// Return the stable hash of this manifest/trampoline binding evidence.
    pub fn canonical_install_binding_evidence_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.install_binding_evidence_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, self.status.as_str());
        put_option_str(&mut out, self.blocker.map(|blocker| blocker.as_str()));
        put_option_str(&mut out, self.required_evidence);
        put_option_checksum(&mut out, self.packet_hash);
        put_option_checksum(&mut out, self.persisted_packet_hash);
        put_str(&mut out, self.manifest_identity_schema);
        put_u32(&mut out, self.manifest_identity_schema_version);
        put_option_str(&mut out, self.manifest_source);
        put_option_str(&mut out, self.manifest_identity_sha256.as_deref());
        put_option_str(&mut out, self.artifact_id.as_deref());
        put_option_checksum(&mut out, self.manifest_checksum);
        put_option_str(&mut out, self.source_sha256.as_deref());
        put_option_str(&mut out, self.trust_ir_sha256.as_deref());
        put_option_str(&mut out, self.native_payload_sha256.as_deref());
        put_option_checksum(&mut out, self.target_checksum);
        put_option_checksum(&mut out, self.abi_checksum);
        put_option_checksum(&mut out, self.layout_checksum);
        put_option_checksum(&mut out, self.proof_policy_checksum);
        put_option_checksum(&mut out, self.invalidation_checksum);
        put_option_str(&mut out, self.trampoline_sha256.as_deref());
        put_option_str(&mut out, self.layout_wrapper_identity.as_deref());
        put_option_str(&mut out, self.entry_symbol.as_deref());
        put_option_str(&mut out, self.trampoline_abi);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_install_binding_evidence_sha256(mut self) -> Self {
        self.install_binding_evidence_sha256 = self.canonical_install_binding_evidence_sha256();
        self
    }
}

/// Readiness status for a Petri/MCC native successor host call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorExecutableCallStatus {
    /// All current executable-call evidence is present and binds the call packet.
    Ready,
    /// The callable must remain fail-closed.
    Blocked,
}

impl PetriNativeSuccessorExecutableCallStatus {
    /// Return the stable lower-snake-case status string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ready => "ready",
            Self::Blocked => "blocked",
        }
    }
}

/// Caller-supplied semantic bridge expectations for Petri/MCC successor trust_ir bundles.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PetriNativeSuccessorSemanticBridgeExpected<'a> {
    /// trust_ir entry function expected to implement the Petri successor step.
    pub entry_function: &'a str,
    /// Formula schema identifying the semantic-successor proof obligation.
    pub formula_schema: &'a str,
}

impl<'a> PetriNativeSuccessorSemanticBridgeExpected<'a> {
    /// Build a semantic bridge expectation for the standard Petri successor formula schema.
    pub const fn new(entry_function: &'a str) -> Self {
        Self {
            entry_function,
            formula_schema: PETRI_NATIVE_SUCCESSOR_SEMANTIC_FORMULA_SCHEMA,
        }
    }

    /// Override the expected semantic-successor formula schema.
    pub const fn with_formula_schema(mut self, formula_schema: &'a str) -> Self {
        self.formula_schema = formula_schema;
        self
    }
}

/// Stable blocker for Petri/MCC native successor semantic bridge evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorSemanticBridgeBlocker {
    /// The trust_ir bundle failed validation before semantic evidence could be consumed.
    BundleValidationFailed,
    /// The requested trust_ir entry function is absent.
    MissingEntryFunction,
    /// No trust_ir obligation binds the entry function to Petri successor semantics.
    MissingSemanticSuccessorObligation,
    /// The semantic-successor obligation has no matching native evidence bundle.
    MissingSemanticSuccessorEvidence,
}

impl PetriNativeSuccessorSemanticBridgeBlocker {
    /// Return the stable lower-snake-case blocker string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::BundleValidationFailed => "bundle_validation_failed",
            Self::MissingEntryFunction => "missing_entry_function",
            Self::MissingSemanticSuccessorObligation => "missing_semantic_successor_obligation",
            Self::MissingSemanticSuccessorEvidence => "missing_semantic_successor_evidence",
        }
    }

    /// Return the exact field required to clear this blocker.
    pub const fn required_field(self) -> &'static str {
        match self {
            Self::BundleValidationFailed => "trust_ir_bundle",
            Self::MissingEntryFunction => "entry_function",
            Self::MissingSemanticSuccessorObligation => "semantic_successor_obligation",
            Self::MissingSemanticSuccessorEvidence => "native_evidence_bundle",
        }
    }

    /// Return the exact evidence schema required to clear this blocker.
    pub const fn required_evidence(self) -> &'static str {
        match self {
            Self::BundleValidationFailed | Self::MissingEntryFunction => {
                PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA
            }
            Self::MissingSemanticSuccessorObligation | Self::MissingSemanticSuccessorEvidence => {
                PETRI_NATIVE_SUCCESSOR_SEMANTIC_FORMULA_SCHEMA
            }
        }
    }
}

/// Fail-closed evidence that a trust_ir bundle carries Petri successor semantic authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorSemanticBridgeEvidence {
    /// Semantic bridge schema.
    pub schema: &'static str,
    /// Semantic bridge schema version.
    pub schema_version: u32,
    /// Ready or blocked status.
    pub status: PetriNativeSuccessorExecutableCallStatus,
    /// Stable fail-closed blocker.
    pub blocker: Option<PetriNativeSuccessorSemanticBridgeBlocker>,
    /// Stable fail-closed reason code.
    pub reason_code: Option<&'static str>,
    /// Exact field required to clear this blocker, when applicable.
    pub required_field: Option<&'static str>,
    /// Exact evidence schema required to clear this blocker, when applicable.
    pub required_evidence: Option<&'static str>,
    /// Formula schema matched in trust_ir proof obligations.
    pub formula_schema: String,
    /// trust_ir function expected to implement the successor.
    pub entry_function: String,
    /// Whether the bundle validated through trust_ir's native evidence consumer.
    pub bundle_validated: bool,
    /// trust_ir transport identity digest.
    pub transport_digest: String,
    /// trust_ir bundle digest.
    pub bundle_digest: String,
    /// trust_ir module digest.
    pub trust_ir_module_digest: String,
    /// trust_ir target ABI digest.
    pub target_abi_digest: Option<String>,
    /// Number of native evidence report entries after validation.
    pub native_evidence_report_entries: u64,
    /// Number of entry-bound semantic-successor obligations found.
    pub semantic_obligation_count: u64,
    /// Number of native evidence entries that cover those obligations.
    pub semantic_evidence_entry_count: u64,
    /// Number of consumed certificates attached to semantic evidence entries.
    pub consumed_certificate_count: u64,
    /// Number of native verifier artifacts attached to semantic evidence entries.
    pub artifact_count: u64,
    /// Whether a Petri successor relation is represented by consumed evidence.
    pub successor_relation_represented: bool,
    /// Whether Trust Codegen grants semantic authority for Petri callable construction.
    pub semantic_successor_authority: bool,
    /// trust_ir-owned semantic bridge status code, when a function-scoped bridge report exists.
    pub trust_ir_semantic_bridge_status_code: Option<&'static str>,
    /// trust_ir-owned semantic bridge reason code, when a function-scoped bridge report exists.
    pub trust_ir_semantic_bridge_reason_code: Option<&'static str>,
    /// trust_ir-owned semantic bridge evidence status code, when a function-scoped bridge report exists.
    pub trust_ir_semantic_bridge_evidence_status_code: Option<&'static str>,
    /// trust_ir-owned semantic bridge proof/evidence identity digest.
    pub trust_ir_semantic_bridge_proof_identity_digest: Option<String>,
    /// trust_ir-owned trust-mc CHC binding report schema.
    pub trust_ir_trust_mc_chc_binding_schema: Option<&'static str>,
    /// trust_ir-owned trust-mc CHC binding report schema version.
    pub trust_ir_trust_mc_chc_binding_schema_version: Option<u32>,
    /// trust_ir function id covered by the trust-mc CHC binding report.
    pub trust_ir_trust_mc_chc_binding_function_id: Option<String>,
    /// trust_ir-owned trust-mc CHC binding status code for the Petri successor bridge.
    pub trust_ir_trust_mc_chc_binding_status_code: Option<&'static str>,
    /// trust_ir-owned trust-mc CHC binding reason code for the Petri successor bridge.
    pub trust_ir_trust_mc_chc_binding_reason_code: Option<&'static str>,
    /// Whether trust_ir reports the trust-mc CHC binding as bound.
    pub trust_ir_trust_mc_chc_binding_bound: Option<bool>,
    /// Whether trust_ir reports the trust-mc CHC binding as fail-closed.
    pub trust_ir_trust_mc_chc_binding_fail_closed: Option<bool>,
    /// trust_ir-owned trust-mc CHC request id bound to the Petri successor bridge.
    pub trust_ir_trust_mc_chc_binding_request_id: Option<String>,
    /// Stable trust_ir digest of the trust-mc CHC request bound to the bridge.
    pub trust_ir_trust_mc_chc_binding_request_digest: Option<String>,
    /// Stable trust_ir digest of the supplied trust-mc CHC evidence bundle.
    pub trust_ir_trust_mc_chc_binding_evidence_digest: Option<String>,
    /// Stable trust_ir digest expected for the supplied trust-mc CHC evidence bundle.
    pub trust_ir_trust_mc_chc_binding_expected_evidence_digest: Option<String>,
    /// Name of the trust_ir-owned trust-mc Horn-clause artifact bound to the bridge.
    pub trust_ir_trust_mc_chc_binding_horn_clause_artifact: Option<String>,
    /// Kind of the trust_ir-owned trust-mc Horn-clause artifact bound to the bridge.
    pub trust_ir_trust_mc_chc_binding_horn_clause_artifact_kind: Option<String>,
    /// Digest of the trust_ir-owned trust-mc Horn-clause artifact bound to the bridge.
    pub trust_ir_trust_mc_chc_binding_horn_clause_digest: Option<String>,
    /// trust_ir-owned trust-mc CHC proof-handoff report schema.
    pub trust_ir_trust_mc_chc_proof_handoff_schema: Option<&'static str>,
    /// trust_ir-owned trust-mc CHC proof-handoff report schema version.
    pub trust_ir_trust_mc_chc_proof_handoff_schema_version: Option<u32>,
    /// trust_ir function id covered by the trust-mc CHC proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_function_id: Option<String>,
    /// trust_ir-owned trust-mc CHC proof-handoff status code.
    pub trust_ir_trust_mc_chc_proof_handoff_status_code: Option<&'static str>,
    /// trust_ir-owned trust-mc CHC proof-handoff reason code.
    pub trust_ir_trust_mc_chc_proof_handoff_reason_code: Option<&'static str>,
    /// Whether trust_ir reports the trust-mc CHC proof handoff as ready.
    pub trust_ir_trust_mc_chc_proof_handoff_ready: Option<bool>,
    /// Whether trust_ir reports the trust-mc CHC proof handoff as fail-closed.
    pub trust_ir_trust_mc_chc_proof_handoff_fail_closed: Option<bool>,
    /// trust_ir proof identity digest consumed by the trust-mc CHC proof handoff.
    pub trust_ir_trust_mc_chc_proof_handoff_proof_identity_digest: Option<String>,
    /// trust-mc replay engine recorded by the trust_ir proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_replay_engine: Option<String>,
    /// trust-mc replay invocation recorded by the trust_ir proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_replay_invocation: Option<String>,
    /// Replay transcript digest recorded by the trust_ir proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_replay_transcript_digest: Option<String>,
    /// Replay transcript artifact recorded by the trust_ir proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact: Option<String>,
    /// Replay transcript artifact kind recorded by the trust_ir proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_kind: Option<String>,
    /// Replay transcript artifact digest recorded by the trust_ir proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_digest: Option<String>,
    /// Optional model artifact recorded by the trust_ir proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_model_artifact: Option<String>,
    /// Optional model artifact kind recorded by the trust_ir proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_model_artifact_kind: Option<String>,
    /// Optional model artifact digest recorded by the trust_ir proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_model_artifact_digest: Option<String>,
    /// Solver identities recorded by the trust_ir proof-handoff report.
    pub trust_ir_trust_mc_chc_proof_handoff_solver_identities: Vec<String>,
    /// trust_ir-owned trust-mc CHC model-validation readiness report schema.
    pub trust_ir_trust_mc_chc_model_validation_schema: Option<&'static str>,
    /// trust_ir-owned trust-mc CHC model-validation readiness report schema version.
    pub trust_ir_trust_mc_chc_model_validation_schema_version: Option<u32>,
    /// trust_ir function id covered by the trust-mc CHC model-validation readiness report.
    pub trust_ir_trust_mc_chc_model_validation_function_id: Option<String>,
    /// trust_ir-owned trust-mc CHC model-validation readiness status code.
    pub trust_ir_trust_mc_chc_model_validation_status_code: Option<&'static str>,
    /// trust_ir-owned trust-mc CHC model-validation readiness reason code.
    pub trust_ir_trust_mc_chc_model_validation_reason_code: Option<&'static str>,
    /// Whether trust_ir reports the handoff as ready for solver-owned validation.
    pub trust_ir_trust_mc_chc_model_validation_ready_for_solver_validation: Option<bool>,
    /// Whether trust_ir reports the model-validation path as fail-closed.
    pub trust_ir_trust_mc_chc_model_validation_fail_closed: Option<bool>,
    /// Whether downstream solver-owned model validation has already occurred.
    pub trust_ir_trust_mc_chc_model_validated: Option<bool>,
    /// Model artifact recorded by the trust_ir model-validation readiness report.
    pub trust_ir_trust_mc_chc_model_validation_model_artifact: Option<String>,
    /// Model artifact kind recorded by the trust_ir model-validation readiness report.
    pub trust_ir_trust_mc_chc_model_validation_model_artifact_kind: Option<String>,
    /// Model artifact digest recorded by the trust_ir model-validation readiness report.
    pub trust_ir_trust_mc_chc_model_validation_model_artifact_digest: Option<String>,
    /// Solver identities recorded by the trust_ir model-validation readiness report.
    pub trust_ir_trust_mc_chc_model_validation_solver_identities: Vec<String>,
    /// trust_ir-owned Petri semantic bridge proof-admission report schema.
    pub trust_ir_semantic_bridge_proof_admission_schema: Option<String>,
    /// trust_ir-owned Petri semantic bridge proof-admission report schema version.
    pub trust_ir_semantic_bridge_proof_admission_schema_version: Option<u32>,
    /// trust_ir function id covered by the proof-admission report.
    pub trust_ir_semantic_bridge_proof_admission_function_id: Option<String>,
    /// trust_ir-owned proof-admission status code.
    pub trust_ir_semantic_bridge_proof_admission_status_code: Option<&'static str>,
    /// trust_ir-owned proof-admission reason code.
    pub trust_ir_semantic_bridge_proof_admission_reason_code: Option<&'static str>,
    /// Whether trust_ir admitted the byte-backed semantic bridge proof artifacts.
    pub trust_ir_semantic_bridge_proof_admission_admitted: Option<bool>,
    /// Whether trust_ir failed the proof-admission report closed.
    pub trust_ir_semantic_bridge_proof_admission_fail_closed: Option<bool>,
    /// trust_ir-owned required production-acceptance artifact kind codes.
    pub trust_ir_semantic_bridge_proof_admission_required_artifact_kinds: Vec<String>,
    /// Number of trust_ir artifact resolutions included in the proof-admission report.
    pub trust_ir_semantic_bridge_proof_admission_artifact_resolution_count: u64,
    /// Number of authoritative artifact resolutions according to trust_ir.
    pub trust_ir_semantic_bridge_proof_admission_authoritative_artifact_count: u64,
    /// First trust_ir-blocked artifact kind, when proof admission fails on artifact bytes.
    pub trust_ir_semantic_bridge_proof_admission_blocked_artifact_kind: Option<String>,
    /// trust_ir-owned reason code for the first blocked artifact, when present.
    pub trust_ir_semantic_bridge_proof_admission_blocked_artifact_reason_code: Option<&'static str>,
    /// Flat trust_ir-owned authority rows for artifact resolutions.
    pub trust_ir_semantic_bridge_proof_admission_artifact_authority_lines: Vec<String>,
    /// Canonical semantic bridge evidence hash.
    pub semantic_bridge_sha256: String,
}

impl PetriNativeSuccessorSemanticBridgeEvidence {
    /// Return true only when semantic successor authority is proven by consumed trust_ir evidence.
    pub const fn is_ready(&self) -> bool {
        matches!(self.status, PetriNativeSuccessorExecutableCallStatus::Ready)
            && self.blocker.is_none()
            && self.successor_relation_represented
            && self.semantic_successor_authority
    }

    /// Return the stable hash of this semantic bridge evidence.
    pub fn canonical_semantic_bridge_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.semantic_bridge_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, self.status.as_str());
        put_option_str(&mut out, self.blocker.map(|blocker| blocker.as_str()));
        put_option_str(&mut out, self.required_field);
        put_option_str(&mut out, self.required_evidence);
        put_str(&mut out, &self.formula_schema);
        put_str(&mut out, &self.entry_function);
        put_bool(&mut out, self.bundle_validated);
        put_str(&mut out, &self.transport_digest);
        put_str(&mut out, &self.bundle_digest);
        put_str(&mut out, &self.trust_ir_module_digest);
        put_option_str(&mut out, self.target_abi_digest.as_deref());
        put_u64(&mut out, self.native_evidence_report_entries);
        put_u64(&mut out, self.semantic_obligation_count);
        put_u64(&mut out, self.semantic_evidence_entry_count);
        put_u64(&mut out, self.consumed_certificate_count);
        put_u64(&mut out, self.artifact_count);
        put_bool(&mut out, self.successor_relation_represented);
        put_bool(&mut out, self.semantic_successor_authority);
        put_option_str(&mut out, self.trust_ir_semantic_bridge_status_code);
        put_option_str(&mut out, self.trust_ir_semantic_bridge_reason_code);
        put_option_str(&mut out, self.trust_ir_semantic_bridge_evidence_status_code);
        put_option_str(
            &mut out,
            self.trust_ir_semantic_bridge_proof_identity_digest
                .as_deref(),
        );
        put_option_str(&mut out, self.trust_ir_trust_mc_chc_binding_schema);
        put_option_u64(
            &mut out,
            self.trust_ir_trust_mc_chc_binding_schema_version
                .map(u64::from),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_binding_function_id.as_deref(),
        );
        put_option_str(&mut out, self.trust_ir_trust_mc_chc_binding_status_code);
        put_option_str(&mut out, self.trust_ir_trust_mc_chc_binding_reason_code);
        put_option_bool(&mut out, self.trust_ir_trust_mc_chc_binding_bound);
        put_option_bool(&mut out, self.trust_ir_trust_mc_chc_binding_fail_closed);
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_binding_request_id.as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_binding_request_digest.as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_binding_evidence_digest
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_binding_expected_evidence_digest
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_binding_horn_clause_artifact
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_binding_horn_clause_artifact_kind
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_binding_horn_clause_digest
                .as_deref(),
        );
        put_option_str(&mut out, self.trust_ir_trust_mc_chc_proof_handoff_schema);
        put_option_u64(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_schema_version
                .map(u64::from),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_function_id
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_status_code,
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_reason_code,
        );
        put_option_bool(&mut out, self.trust_ir_trust_mc_chc_proof_handoff_ready);
        put_option_bool(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_fail_closed,
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_proof_identity_digest
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_replay_engine
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_replay_invocation
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_replay_transcript_digest
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_kind
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_digest
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_model_artifact
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_model_artifact_kind
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_proof_handoff_model_artifact_digest
                .as_deref(),
        );
        put_str_vec(
            &mut out,
            &self.trust_ir_trust_mc_chc_proof_handoff_solver_identities,
        );
        put_option_str(&mut out, self.trust_ir_trust_mc_chc_model_validation_schema);
        put_option_u64(
            &mut out,
            self.trust_ir_trust_mc_chc_model_validation_schema_version
                .map(u64::from),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_model_validation_function_id
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_model_validation_status_code,
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_model_validation_reason_code,
        );
        put_option_bool(
            &mut out,
            self.trust_ir_trust_mc_chc_model_validation_ready_for_solver_validation,
        );
        put_option_bool(
            &mut out,
            self.trust_ir_trust_mc_chc_model_validation_fail_closed,
        );
        put_option_bool(&mut out, self.trust_ir_trust_mc_chc_model_validated);
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_model_validation_model_artifact
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_model_validation_model_artifact_kind
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_trust_mc_chc_model_validation_model_artifact_digest
                .as_deref(),
        );
        put_str_vec(
            &mut out,
            &self.trust_ir_trust_mc_chc_model_validation_solver_identities,
        );
        put_option_str(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_schema
                .as_deref(),
        );
        put_option_u64(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_schema_version
                .map(u64::from),
        );
        put_option_str(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_function_id
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_status_code,
        );
        put_option_str(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_reason_code,
        );
        put_option_bool(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_admitted,
        );
        put_option_bool(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_fail_closed,
        );
        put_str_vec(
            &mut out,
            &self.trust_ir_semantic_bridge_proof_admission_required_artifact_kinds,
        );
        put_u64(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_artifact_resolution_count,
        );
        put_u64(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_authoritative_artifact_count,
        );
        put_option_str(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_blocked_artifact_kind
                .as_deref(),
        );
        put_option_str(
            &mut out,
            self.trust_ir_semantic_bridge_proof_admission_blocked_artifact_reason_code,
        );
        put_str_vec(
            &mut out,
            &self.trust_ir_semantic_bridge_proof_admission_artifact_authority_lines,
        );
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_semantic_bridge_sha256(mut self) -> Self {
        self.semantic_bridge_sha256 = self.canonical_semantic_bridge_sha256();
        self
    }
}

/// Stable blocker for Petri/MCC native successor compile-artifact handoff evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorCompileArtifactHandoffBlocker {
    /// The compiled artifact did not provide a native payload digest.
    MissingNativePayloadSha256,
    /// The compiled artifact did not name the entry/trampoline symbol.
    MissingEntrySymbol,
    /// No non-null callable pointer was bound to the compiled artifact.
    MissingCallablePointer,
    /// No executable region identity was supplied for lifetime proof construction.
    MissingExecutableRegionSha256,
    /// No runtime owner was supplied for lifetime proof construction.
    MissingLifetimeOwner,
    /// No current runtime generation was supplied for lifetime proof construction.
    MissingCurrentGeneration,
}

impl PetriNativeSuccessorCompileArtifactHandoffBlocker {
    /// Return the stable lower-snake-case blocker string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingNativePayloadSha256 => "missing_native_payload_sha256",
            Self::MissingEntrySymbol => "missing_entry_symbol",
            Self::MissingCallablePointer => "missing_callable_pointer",
            Self::MissingExecutableRegionSha256 => "missing_executable_region_sha256",
            Self::MissingLifetimeOwner => "missing_lifetime_owner",
            Self::MissingCurrentGeneration => "missing_current_generation",
        }
    }

    /// Return the exact compile-artifact handoff field required to clear this blocker.
    pub const fn required_field(self) -> &'static str {
        match self {
            Self::MissingNativePayloadSha256 => "compiled_artifact.native_payload_sha256",
            Self::MissingEntrySymbol => "compiled_artifact.entry_symbol",
            Self::MissingCallablePointer => "compiled_artifact.callable_pointer",
            Self::MissingExecutableRegionSha256 => "compiled_artifact.executable_region_sha256",
            Self::MissingLifetimeOwner => "compiled_artifact.lifetime_owner",
            Self::MissingCurrentGeneration => "compiled_artifact.current_generation",
        }
    }

    /// Return the exact evidence schema required to clear this blocker.
    pub const fn required_evidence(self) -> &'static str {
        PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA
    }
}

/// Caller-supplied native compile artifact handoff inputs for Petri/MCC successor JIT.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PetriNativeSuccessorCompileArtifactHandoffInput<'a> {
    /// Native payload digest produced by Trust Codegen's native compile artifact.
    pub native_payload_sha256: Option<&'a str>,
    /// Entry/trampoline symbol for the compiled successor callable.
    pub entry_symbol: Option<&'a str>,
    /// Non-null host callable pointer bound by the runtime/JIT.
    pub callable_pointer: Option<PetriNativeSuccessorCallablePointer>,
    /// Executable region identity that owns the callable pointer.
    pub executable_region_sha256: Option<&'a str>,
    /// Runtime owner responsible for keeping the executable region alive.
    pub lifetime_owner: Option<&'a str>,
    /// Runtime generation used to validate the lifetime proof.
    pub current_generation: Option<u64>,
}

impl<'a> PetriNativeSuccessorCompileArtifactHandoffInput<'a> {
    /// Attach the compiled native payload digest.
    pub const fn with_native_payload_sha256(mut self, value: &'a str) -> Self {
        self.native_payload_sha256 = Some(value);
        self
    }

    /// Attach the compiled entry/trampoline symbol.
    pub const fn with_entry_symbol(mut self, value: &'a str) -> Self {
        self.entry_symbol = Some(value);
        self
    }

    /// Attach the non-null callable pointer.
    pub const fn with_callable_pointer(
        mut self,
        value: PetriNativeSuccessorCallablePointer,
    ) -> Self {
        self.callable_pointer = Some(value);
        self
    }

    /// Attach the executable memory region identity.
    pub const fn with_executable_region_sha256(mut self, value: &'a str) -> Self {
        self.executable_region_sha256 = Some(value);
        self
    }

    /// Attach the runtime lifetime owner.
    pub const fn with_lifetime_owner(mut self, value: &'a str) -> Self {
        self.lifetime_owner = Some(value);
        self
    }

    /// Attach the runtime generation observed by the caller.
    pub const fn with_current_generation(mut self, value: u64) -> Self {
        self.current_generation = Some(value);
        self
    }
}

/// Fail-closed evidence for binding a native compile artifact to Petri successor packets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorCompileArtifactHandoffEvidence {
    /// Compile-artifact handoff schema.
    pub schema: &'static str,
    /// Compile-artifact handoff schema version.
    pub schema_version: u32,
    /// Ready or blocked status.
    pub status: PetriNativeSuccessorExecutableCallStatus,
    /// Stable fail-closed blocker.
    pub blocker: Option<PetriNativeSuccessorCompileArtifactHandoffBlocker>,
    /// Stable fail-closed reason code.
    pub reason_code: Option<&'static str>,
    /// Exact field required to clear this blocker, when applicable.
    pub required_field: Option<&'static str>,
    /// Exact evidence schema required to clear this blocker, when applicable.
    pub required_evidence: Option<&'static str>,
    /// Native payload digest produced by Trust Codegen's native compile artifact.
    pub native_payload_sha256: Option<String>,
    /// Entry/trampoline symbol for the compiled successor callable.
    pub entry_symbol: Option<String>,
    /// Non-null host callable pointer bound by the runtime/JIT.
    pub callable_pointer: Option<PetriNativeSuccessorCallablePointer>,
    /// Executable region identity that owns the callable pointer.
    pub executable_region_sha256: Option<String>,
    /// Runtime owner responsible for keeping the executable region alive.
    pub lifetime_owner: Option<String>,
    /// Runtime generation used to validate the lifetime proof.
    pub current_generation: Option<u64>,
    /// Canonical compile-artifact handoff evidence hash.
    pub compile_artifact_handoff_sha256: String,
}

impl PetriNativeSuccessorCompileArtifactHandoffEvidence {
    /// Return true only when the native compile artifact handoff is complete.
    pub const fn is_ready(&self) -> bool {
        matches!(self.status, PetriNativeSuccessorExecutableCallStatus::Ready)
            && self.blocker.is_none()
    }

    /// Return whether this compile-artifact handoff authorizes useful native execution.
    ///
    /// Compile handoff evidence only proves that Trust Codegen can name a compiled
    /// artifact and host pointer. Runtime/MCC callers must still require an
    /// authoritative install-gate call packet and runtime readiness proof.
    pub const fn authorizes_useful_native(&self) -> bool {
        false
    }

    /// Emit stable JSON-free key/value rows for MCC sidecar consumers.
    pub fn manifest_rows(&self) -> Vec<PetriNativeSuccessorHandoffManifestRow> {
        let mut rows = Vec::new();
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ManifestSchema,
            PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA,
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ManifestSchemaVersion,
            PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA_VERSION.to_string(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::Surface,
            "compile_artifact_handoff",
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::EvidenceSchema,
            self.schema,
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::EvidenceSchemaVersion,
            self.schema_version.to_string(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::Status,
            self.status.as_str(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ReasonCode,
            self.reason_code.unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RequiredField,
            self.required_field.unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RequiredEvidence,
            self.required_evidence.unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::NativePayloadSha256,
            self.native_payload_sha256.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::EntrySymbol,
            self.entry_symbol.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CallablePointer,
            option_callable_pointer_manifest_value(self.callable_pointer),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ExecutableRegionSha256,
            self.executable_region_sha256.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactHandoffSha256,
            self.compile_artifact_handoff_sha256.as_str(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CallableAuthorized,
            "false",
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ReadyForRuntimeCall,
            "false",
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::AuthorizesUsefulNative,
            petri_native_successor_bool_code(self.authorizes_useful_native()),
        );
        rows
    }

    /// Emit stable escaped `key=value` manifest lines in [`Self::manifest_rows`] order.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Return the stable hash of this compile-artifact handoff evidence.
    pub fn canonical_compile_artifact_handoff_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.compile_artifact_handoff_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, self.status.as_str());
        put_option_str(&mut out, self.blocker.map(|blocker| blocker.as_str()));
        put_option_str(&mut out, self.required_field);
        put_option_str(&mut out, self.native_payload_sha256.as_deref());
        put_option_str(&mut out, self.entry_symbol.as_deref());
        put_option_callable_pointer(&mut out, self.callable_pointer);
        put_option_str(&mut out, self.executable_region_sha256.as_deref());
        put_option_str(&mut out, self.lifetime_owner.as_deref());
        put_option_u64(&mut out, self.current_generation);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_compile_artifact_handoff_sha256(mut self) -> Self {
        self.compile_artifact_handoff_sha256 = self.canonical_compile_artifact_handoff_sha256();
        self
    }
}

/// Stable blocker for Petri/MCC native successor executable-call readiness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorExecutableCallBlocker {
    /// The call packet itself did not authorize callable exposure.
    MissingCallableAuthority,
    /// No callable lifetime proof was supplied.
    MissingCallableLifetimeProof,
    /// The callable lifetime proof schema or hash was invalid.
    CallableLifetimeProofMismatch,
    /// The callable lifetime proof bound a different host pointer.
    CallablePointerMismatch,
    /// The callable lifetime proof expired before the current runtime generation.
    StaleCallableLifetimeProof,
    /// No runtime ABI proof was supplied.
    MissingRuntimeAbiProof,
    /// The runtime ABI proof schema or hash was invalid.
    RuntimeAbiProofMismatch,
    /// The runtime ABI proof did not match the call packet ABI and state layout.
    RuntimeAbiMismatch,
}

impl PetriNativeSuccessorExecutableCallBlocker {
    /// Return the stable lower-snake-case blocker string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingCallableAuthority => "missing_callable_authority",
            Self::MissingCallableLifetimeProof => "missing_callable_lifetime_proof",
            Self::CallableLifetimeProofMismatch => "callable_lifetime_proof_mismatch",
            Self::CallablePointerMismatch => "callable_pointer_mismatch",
            Self::StaleCallableLifetimeProof => "stale_callable_lifetime_proof",
            Self::MissingRuntimeAbiProof => "missing_runtime_abi_proof",
            Self::RuntimeAbiProofMismatch => "runtime_abi_proof_mismatch",
            Self::RuntimeAbiMismatch => "runtime_abi_mismatch",
        }
    }

    /// Return the exact evidence schema required to clear this blocker, when applicable.
    pub const fn required_evidence(self) -> Option<&'static str> {
        match self {
            Self::MissingCallableAuthority => Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
            Self::MissingCallableLifetimeProof
            | Self::CallableLifetimeProofMismatch
            | Self::CallablePointerMismatch
            | Self::StaleCallableLifetimeProof => {
                Some(PETRI_NATIVE_SUCCESSOR_CALLABLE_LIFETIME_PROOF_SCHEMA)
            }
            Self::MissingRuntimeAbiProof
            | Self::RuntimeAbiProofMismatch
            | Self::RuntimeAbiMismatch => Some(PETRI_NATIVE_SUCCESSOR_RUNTIME_ABI_PROOF_SCHEMA),
        }
    }
}

/// Runtime evidence that a Petri/MCC native successor callable pointer is live.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorCallableLifetimeProof {
    /// Callable lifetime proof schema.
    pub schema: &'static str,
    /// Callable lifetime proof schema version.
    pub schema_version: u32,
    /// Non-null host callable pointer identity.
    pub callable_pointer: PetriNativeSuccessorCallablePointer,
    /// Executable memory region identity that owns the pointer.
    pub executable_region_sha256: String,
    /// Runtime owner responsible for keeping the executable region alive.
    pub lifetime_owner: String,
    /// Runtime generation that observed the pointer live.
    pub observed_generation: u64,
    /// Last runtime generation where this proof remains live.
    pub expires_after_generation: Option<u64>,
    /// Canonical lifetime proof hash.
    pub lifetime_proof_sha256: String,
}

impl PetriNativeSuccessorCallableLifetimeProof {
    /// Build a callable lifetime proof if the executable region and owner identities are present.
    pub fn new(
        callable_pointer: PetriNativeSuccessorCallablePointer,
        executable_region_sha256: impl Into<String>,
        lifetime_owner: impl Into<String>,
        observed_generation: u64,
        expires_after_generation: Option<u64>,
    ) -> Option<Self> {
        let executable_region_sha256 = executable_region_sha256.into();
        let lifetime_owner = lifetime_owner.into();
        if missing_required_text(&executable_region_sha256)
            || missing_required_text(&lifetime_owner)
        {
            return None;
        }

        Some(
            Self {
                schema: PETRI_NATIVE_SUCCESSOR_CALLABLE_LIFETIME_PROOF_SCHEMA,
                schema_version: PETRI_NATIVE_SUCCESSOR_CALLABLE_LIFETIME_PROOF_SCHEMA_VERSION,
                callable_pointer,
                executable_region_sha256,
                lifetime_owner,
                observed_generation,
                expires_after_generation,
                lifetime_proof_sha256: String::new(),
            }
            .with_canonical_lifetime_proof_sha256(),
        )
    }

    /// Return the stable hash of this callable lifetime proof.
    pub fn canonical_lifetime_proof_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.callable_lifetime_proof_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_u64(&mut out, self.callable_pointer.addr_usize() as u64);
        put_str(&mut out, &self.executable_region_sha256);
        put_str(&mut out, &self.lifetime_owner);
        put_u64(&mut out, self.observed_generation);
        put_option_u64(&mut out, self.expires_after_generation);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_lifetime_proof_sha256(mut self) -> Self {
        self.lifetime_proof_sha256 = self.canonical_lifetime_proof_sha256();
        self
    }

    fn binds_call_packet(
        &self,
        packet: &PetriNativeSuccessorCallPacket,
        current_generation: u64,
    ) -> Result<(), PetriNativeSuccessorExecutableCallBlocker> {
        if self.schema != PETRI_NATIVE_SUCCESSOR_CALLABLE_LIFETIME_PROOF_SCHEMA
            || self.schema_version != PETRI_NATIVE_SUCCESSOR_CALLABLE_LIFETIME_PROOF_SCHEMA_VERSION
            || self.lifetime_proof_sha256 != self.canonical_lifetime_proof_sha256()
        {
            return Err(PetriNativeSuccessorExecutableCallBlocker::CallableLifetimeProofMismatch);
        }
        if self.callable_pointer != packet.callable_pointer {
            return Err(PetriNativeSuccessorExecutableCallBlocker::CallablePointerMismatch);
        }
        if self
            .expires_after_generation
            .is_some_and(|expires| current_generation > expires)
        {
            return Err(PetriNativeSuccessorExecutableCallBlocker::StaleCallableLifetimeProof);
        }
        Ok(())
    }
}

/// Runtime ABI proof for a Petri/MCC native successor host callable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorRuntimeAbiProof {
    /// Runtime ABI proof schema.
    pub schema: &'static str,
    /// Runtime ABI proof schema version.
    pub schema_version: u32,
    /// Petri callable contract hash.
    pub callable_contract_sha256: String,
    /// Compiled trampoline contract hash.
    pub trampoline_sha256: String,
    /// Stable trampoline ABI.
    pub trampoline_abi: &'static str,
    /// Stable state encoding.
    pub state_encoding: &'static str,
    /// Input state byte width.
    pub input_state_bytes: u64,
    /// Output state byte width.
    pub output_state_bytes: u64,
    /// Required input/output byte alignment.
    pub state_alignment_bytes: u32,
    /// Status slot byte width written by the trampoline.
    pub status_slot_bytes: u32,
    /// Runtime ABI proof identity.
    pub runtime_abi_proof_sha256: String,
}

impl PetriNativeSuccessorRuntimeAbiProof {
    /// Build a runtime ABI proof that matches a call packet's first stable ABI.
    pub fn for_call_packet(packet: &PetriNativeSuccessorCallPacket) -> Self {
        Self {
            schema: PETRI_NATIVE_SUCCESSOR_RUNTIME_ABI_PROOF_SCHEMA,
            schema_version: PETRI_NATIVE_SUCCESSOR_RUNTIME_ABI_PROOF_SCHEMA_VERSION,
            callable_contract_sha256: packet.callable_contract_sha256.clone(),
            trampoline_sha256: packet.trampoline_sha256.clone(),
            trampoline_abi: packet.trampoline_abi,
            state_encoding: packet.state_encoding,
            input_state_bytes: packet.input_state_bytes,
            output_state_bytes: packet.output_state_bytes,
            state_alignment_bytes: packet.state_alignment_bytes,
            status_slot_bytes: 4,
            runtime_abi_proof_sha256: String::new(),
        }
        .with_canonical_runtime_abi_proof_sha256()
    }

    /// Return the stable hash of this runtime ABI proof.
    pub fn canonical_runtime_abi_proof_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.runtime_abi_proof_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, &self.callable_contract_sha256);
        put_str(&mut out, &self.trampoline_sha256);
        put_str(&mut out, self.trampoline_abi);
        put_str(&mut out, self.state_encoding);
        put_u64(&mut out, self.input_state_bytes);
        put_u64(&mut out, self.output_state_bytes);
        put_u32(&mut out, self.state_alignment_bytes);
        put_u32(&mut out, self.status_slot_bytes);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_runtime_abi_proof_sha256(mut self) -> Self {
        self.runtime_abi_proof_sha256 = self.canonical_runtime_abi_proof_sha256();
        self
    }

    fn binds_call_packet(
        &self,
        packet: &PetriNativeSuccessorCallPacket,
    ) -> Result<(), PetriNativeSuccessorExecutableCallBlocker> {
        if self.schema != PETRI_NATIVE_SUCCESSOR_RUNTIME_ABI_PROOF_SCHEMA
            || self.schema_version != PETRI_NATIVE_SUCCESSOR_RUNTIME_ABI_PROOF_SCHEMA_VERSION
            || self.runtime_abi_proof_sha256 != self.canonical_runtime_abi_proof_sha256()
        {
            return Err(PetriNativeSuccessorExecutableCallBlocker::RuntimeAbiProofMismatch);
        }
        if self.callable_contract_sha256 != packet.callable_contract_sha256
            || self.trampoline_sha256 != packet.trampoline_sha256
            || self.trampoline_abi != packet.trampoline_abi
            || self.state_encoding != packet.state_encoding
            || self.input_state_bytes != packet.input_state_bytes
            || self.output_state_bytes != packet.output_state_bytes
            || self.state_alignment_bytes != packet.state_alignment_bytes
            || self.status_slot_bytes != 4
        {
            return Err(PetriNativeSuccessorExecutableCallBlocker::RuntimeAbiMismatch);
        }
        Ok(())
    }
}

/// Fail-closed executable-call readiness evidence for a Petri/MCC native successor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutableCallEvidence {
    /// Executable-call evidence schema.
    pub schema: &'static str,
    /// Executable-call evidence schema version.
    pub schema_version: u32,
    /// Call-packet identity being evaluated.
    pub call_packet_sha256: String,
    /// Non-null host callable pointer identity.
    pub callable_pointer: PetriNativeSuccessorCallablePointer,
    /// Callable lifetime proof hash, when supplied.
    pub lifetime_proof_sha256: Option<String>,
    /// Runtime ABI proof hash, when supplied.
    pub runtime_abi_proof_sha256: Option<String>,
    /// Executable memory region identity, when supplied.
    pub executable_region_sha256: Option<String>,
    /// Runtime generation used for lifetime validation.
    pub current_generation: u64,
    /// Ready or blocked status.
    pub status: PetriNativeSuccessorExecutableCallStatus,
    /// Stable fail-closed blocker.
    pub blocker: Option<PetriNativeSuccessorExecutableCallBlocker>,
    /// Exact evidence schema required to clear this blocker, when applicable.
    pub required_evidence: Option<&'static str>,
    /// Canonical executable-call evidence hash.
    pub executable_call_evidence_sha256: String,
}

impl PetriNativeSuccessorExecutableCallEvidence {
    /// Return true only when executable-call evidence is ready and unblocked.
    pub const fn is_ready(&self) -> bool {
        matches!(self.status, PetriNativeSuccessorExecutableCallStatus::Ready)
            && self.blocker.is_none()
    }

    /// Return the stable hash of this executable-call readiness evidence.
    pub fn canonical_executable_call_evidence_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.executable_call_evidence_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, &self.call_packet_sha256);
        put_u64(&mut out, self.callable_pointer.addr_usize() as u64);
        put_option_str(&mut out, self.lifetime_proof_sha256.as_deref());
        put_option_str(&mut out, self.runtime_abi_proof_sha256.as_deref());
        put_option_str(&mut out, self.executable_region_sha256.as_deref());
        put_u64(&mut out, self.current_generation);
        put_str(&mut out, self.status.as_str());
        put_option_str(&mut out, self.blocker.map(|blocker| blocker.as_str()));
        put_option_str(&mut out, self.required_evidence);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_executable_call_evidence_sha256(mut self) -> Self {
        self.executable_call_evidence_sha256 = self.canonical_executable_call_evidence_sha256();
        self
    }
}

/// Final readiness status for a Petri/MCC native successor runtime handoff.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorRuntimeReadinessStatus {
    /// The handoff has all evidence needed before a runtime may call the pointer.
    ReadyForRuntimeCall,
    /// The handoff must remain fail-closed.
    Blocked,
}

impl PetriNativeSuccessorRuntimeReadinessStatus {
    /// Return the stable lower-snake-case status string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ReadyForRuntimeCall => "ready_for_runtime_call",
            Self::Blocked => "blocked",
        }
    }
}

/// Top-level fail-closed blocker for Petri/MCC native successor runtime readiness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorRuntimeReadinessBlocker {
    /// Manifest identity derivation failed.
    ManifestIdentity(PetriNativeSuccessorManifestIdentityBlocker),
    /// Install packet and trampoline binding failed.
    InstallBinding(PetriNativeSuccessorInstallBindingBlocker),
    /// No callable pointer/call packet was supplied.
    MissingCallablePointer,
    /// The call packet did not bind the supplied install packet and trampoline.
    CallPacketBindingMismatch,
    /// Executable-call readiness failed.
    ExecutableCall(PetriNativeSuccessorExecutableCallBlocker),
}

impl PetriNativeSuccessorRuntimeReadinessBlocker {
    /// Return the readiness stage that produced this blocker.
    pub const fn stage(self) -> &'static str {
        match self {
            Self::ManifestIdentity(_) => "manifest_identity",
            Self::InstallBinding(_) => "install_binding",
            Self::MissingCallablePointer | Self::CallPacketBindingMismatch => "call_packet",
            Self::ExecutableCall(_) => "executable_call",
        }
    }

    /// Return the stable lower-snake-case blocker string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ManifestIdentity(blocker) => blocker.as_str(),
            Self::InstallBinding(blocker) => blocker.as_str(),
            Self::MissingCallablePointer => "missing_callable_pointer",
            Self::CallPacketBindingMismatch => "call_packet_binding_mismatch",
            Self::ExecutableCall(blocker) => blocker.as_str(),
        }
    }

    /// Return the exact evidence schema required to clear this blocker, when applicable.
    pub const fn required_evidence(self) -> Option<&'static str> {
        match self {
            Self::ManifestIdentity(blocker) => Some(blocker.required_evidence()),
            Self::InstallBinding(blocker) => Some(blocker.required_evidence()),
            Self::MissingCallablePointer | Self::CallPacketBindingMismatch => {
                Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA)
            }
            Self::ExecutableCall(blocker) => blocker.required_evidence(),
        }
    }
}

/// Top-level Petri/MCC native successor runtime readiness packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorRuntimeReadinessPacket {
    /// Runtime readiness packet schema.
    pub schema: &'static str,
    /// Runtime readiness packet schema version.
    pub schema_version: u32,
    /// Final readiness status.
    pub status: PetriNativeSuccessorRuntimeReadinessStatus,
    /// True only when all lower-level evidence is ready for a host runtime call.
    pub ready_for_runtime_call: bool,
    /// Stable fail-closed blocker.
    pub blocker: Option<PetriNativeSuccessorRuntimeReadinessBlocker>,
    /// Readiness stage that produced the blocker.
    pub blocker_stage: Option<&'static str>,
    /// Stable fail-closed reason code.
    pub reason_code: Option<&'static str>,
    /// Exact evidence schema required to clear this blocker, when applicable.
    pub required_evidence: Option<&'static str>,
    /// Runtime generation used for lifetime validation.
    pub current_generation: u64,
    /// Whether a host call packet was supplied.
    pub call_packet_available: bool,
    /// Call-packet identity, when supplied.
    pub call_packet_sha256: Option<String>,
    /// Non-null host callable pointer identity, when supplied.
    pub callable_pointer: Option<PetriNativeSuccessorCallablePointer>,
    /// Compiled native payload identity, when a call packet is supplied.
    pub native_payload_sha256: Option<String>,
    /// Native symbol that hosts the trampoline, when a call packet is supplied.
    pub entry_symbol: Option<String>,
    /// Whether the supplied call packet carries callable authority.
    pub callable_authorized: bool,
    /// Canonical install-gate packet hash observed from the supplied install packet.
    pub install_packet_hash: Option<ArtifactChecksum>,
    /// Persisted install-gate packet hash copied from the supplied install packet.
    pub persisted_install_packet_hash: Option<ArtifactChecksum>,
    /// Whether manifest identity derivation was ready.
    pub manifest_identity_ready: bool,
    /// Canonical Petri manifest identity hash.
    pub manifest_identity_sha256: Option<String>,
    /// Manifest identity source.
    pub manifest_identity_source: Option<PetriNativeSuccessorManifestIdentitySource>,
    /// Manifest identity blocker, when derivation failed.
    pub manifest_identity_blocker: Option<PetriNativeSuccessorManifestIdentityBlocker>,
    /// Whether install/trampoline binding evidence was ready.
    pub install_binding_ready: bool,
    /// Canonical install binding evidence hash.
    pub install_binding_evidence_sha256: String,
    /// Install/trampoline binding blocker.
    pub install_binding_blocker: Option<PetriNativeSuccessorInstallBindingBlocker>,
    /// Trampoline hash supplied by the caller.
    pub trampoline_sha256: Option<String>,
    /// Whether executable call evidence was ready.
    pub executable_call_ready: bool,
    /// Canonical executable-call evidence hash, when a call packet was supplied.
    pub executable_call_evidence_sha256: Option<String>,
    /// Executable-call blocker.
    pub executable_call_blocker: Option<PetriNativeSuccessorExecutableCallBlocker>,
    /// Callable lifetime proof hash, when supplied.
    pub lifetime_proof_sha256: Option<String>,
    /// Runtime ABI proof hash, when supplied.
    pub runtime_abi_proof_sha256: Option<String>,
    /// Executable memory region identity, when supplied.
    pub executable_region_sha256: Option<String>,
    /// Canonical runtime readiness packet hash.
    pub runtime_readiness_packet_sha256: String,
}

impl PetriNativeSuccessorRuntimeReadinessPacket {
    /// Return true only when the handoff is ready for a runtime call.
    pub const fn is_ready_for_runtime_call(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorRuntimeReadinessStatus::ReadyForRuntimeCall
        ) && self.ready_for_runtime_call
            && self.blocker.is_none()
    }

    /// Return true only when the readiness packet proves useful native execution authority.
    pub fn authorizes_useful_native(&self) -> bool {
        self.is_ready_for_runtime_call()
            && self.callable_authorized
            && self.manifest_identity_ready
            && self.install_binding_ready
            && self.executable_call_ready
            && self.install_packet_hash.is_some()
            && self.install_packet_hash == self.persisted_install_packet_hash
    }

    /// Emit stable JSON-free key/value rows for MCC sidecar consumers.
    pub fn manifest_rows(&self) -> Vec<PetriNativeSuccessorHandoffManifestRow> {
        let mut rows = Vec::new();
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ManifestSchema,
            PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA,
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ManifestSchemaVersion,
            PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA_VERSION.to_string(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::Surface,
            "runtime_readiness",
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::EvidenceSchema,
            self.schema,
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::EvidenceSchemaVersion,
            self.schema_version.to_string(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::Status,
            self.status.as_str(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ReasonCode,
            self.reason_code.unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RequiredField,
            "",
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RequiredEvidence,
            self.required_evidence.unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::NativePayloadSha256,
            self.native_payload_sha256.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::EntrySymbol,
            self.entry_symbol.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CallablePointer,
            option_callable_pointer_manifest_value(self.callable_pointer),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ExecutableRegionSha256,
            self.executable_region_sha256.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::InstallPacketHash,
            option_checksum_manifest_value(self.install_packet_hash),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::PersistedInstallPacketHash,
            option_checksum_manifest_value(self.persisted_install_packet_hash),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ManifestIdentitySha256,
            self.manifest_identity_sha256.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ManifestIdentitySource,
            self.manifest_identity_source
                .map(PetriNativeSuccessorManifestIdentitySource::as_str)
                .unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CallPacketSha256,
            self.call_packet_sha256.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CallableAuthorized,
            petri_native_successor_bool_code(self.callable_authorized),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ReadyForRuntimeCall,
            petri_native_successor_bool_code(self.ready_for_runtime_call),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeReadinessPacketSha256,
            self.runtime_readiness_packet_sha256.as_str(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::AuthorizesUsefulNative,
            petri_native_successor_bool_code(self.authorizes_useful_native()),
        );
        rows
    }

    /// Emit stable escaped `key=value` manifest lines in [`Self::manifest_rows`] order.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Return the stable hash of this runtime readiness packet.
    pub fn canonical_runtime_readiness_packet_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.runtime_readiness_packet_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, self.status.as_str());
        put_bool(&mut out, self.ready_for_runtime_call);
        put_option_str(&mut out, self.blocker.map(|blocker| blocker.stage()));
        put_option_str(&mut out, self.blocker.map(|blocker| blocker.as_str()));
        put_option_str(&mut out, self.required_evidence);
        put_u64(&mut out, self.current_generation);
        put_bool(&mut out, self.call_packet_available);
        put_option_str(&mut out, self.call_packet_sha256.as_deref());
        put_option_callable_pointer(&mut out, self.callable_pointer);
        put_option_str(&mut out, self.native_payload_sha256.as_deref());
        put_option_str(&mut out, self.entry_symbol.as_deref());
        put_bool(&mut out, self.callable_authorized);
        put_option_checksum(&mut out, self.install_packet_hash);
        put_option_checksum(&mut out, self.persisted_install_packet_hash);
        put_bool(&mut out, self.manifest_identity_ready);
        put_option_str(&mut out, self.manifest_identity_sha256.as_deref());
        put_option_str(
            &mut out,
            self.manifest_identity_source.map(|source| source.as_str()),
        );
        put_option_str(
            &mut out,
            self.manifest_identity_blocker
                .map(|blocker| blocker.as_str()),
        );
        put_bool(&mut out, self.install_binding_ready);
        put_str(&mut out, &self.install_binding_evidence_sha256);
        put_option_str(
            &mut out,
            self.install_binding_blocker.map(|blocker| blocker.as_str()),
        );
        put_option_str(&mut out, self.trampoline_sha256.as_deref());
        put_bool(&mut out, self.executable_call_ready);
        put_option_str(&mut out, self.executable_call_evidence_sha256.as_deref());
        put_option_str(
            &mut out,
            self.executable_call_blocker.map(|blocker| blocker.as_str()),
        );
        put_option_str(&mut out, self.lifetime_proof_sha256.as_deref());
        put_option_str(&mut out, self.runtime_abi_proof_sha256.as_deref());
        put_option_str(&mut out, self.executable_region_sha256.as_deref());
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_runtime_readiness_packet_sha256(mut self) -> Self {
        self.runtime_readiness_packet_sha256 = self.canonical_runtime_readiness_packet_sha256();
        self
    }
}

/// Final authority status for a Petri/MCC native successor artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorExecutionAuthorityStatus {
    /// The compile handoff and runtime/install-gate evidence authorize execution.
    Authorized,
    /// The artifact must remain fail-closed.
    FailClosed,
}

impl PetriNativeSuccessorExecutionAuthorityStatus {
    /// Return the stable lower-snake-case status string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Authorized => "authorized",
            Self::FailClosed => "fail_closed",
        }
    }
}

/// Inputs for [`petri_native_successor_execution_authority_decision`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthorityInput<'a> {
    /// Compile-artifact handoff evidence emitted by Trust Codegen's native/JIT boundary.
    pub compile_artifact_handoff: Option<&'a PetriNativeSuccessorCompileArtifactHandoffEvidence>,
    /// Runtime readiness packet emitted from the install-gate/callable boundary.
    pub runtime_readiness: Option<&'a PetriNativeSuccessorRuntimeReadinessPacket>,
}

impl<'a> PetriNativeSuccessorExecutionAuthorityInput<'a> {
    /// Attach compile-artifact handoff evidence.
    pub const fn with_compile_artifact_handoff(
        mut self,
        value: &'a PetriNativeSuccessorCompileArtifactHandoffEvidence,
    ) -> Self {
        self.compile_artifact_handoff = Some(value);
        self
    }

    /// Attach runtime readiness evidence.
    pub const fn with_runtime_readiness(
        mut self,
        value: &'a PetriNativeSuccessorRuntimeReadinessPacket,
    ) -> Self {
        self.runtime_readiness = Some(value);
        self
    }
}

/// Typed fail-closed authority decision for a Petri/MCC native successor artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorExecutionAuthorityDecision {
    /// Execution-authority schema.
    pub schema: &'static str,
    /// Execution-authority schema version.
    pub schema_version: u32,
    /// Authorized or fail-closed status.
    pub status: PetriNativeSuccessorExecutionAuthorityStatus,
    /// True only when all evidence authorizes a native runtime call.
    pub authorized_for_execution: bool,
    /// Stable fail-closed reason code.
    pub reason_code: Option<&'static str>,
    /// Lower-level handoff/readiness reason code that caused the decision, if applicable.
    pub source_reason_code: Option<&'static str>,
    /// Exact field required to clear this decision, when applicable.
    pub required_field: Option<&'static str>,
    /// Exact evidence schema required to clear this decision, when applicable.
    pub required_evidence: Option<&'static str>,
    /// Compile-artifact handoff evidence hash.
    pub compile_artifact_handoff_sha256: Option<String>,
    /// Runtime readiness packet hash.
    pub runtime_readiness_packet_sha256: Option<String>,
    /// Whether compile-artifact handoff evidence carried its current canonical hash.
    pub compile_artifact_handoff_hash_current: bool,
    /// Whether runtime readiness evidence carried its current canonical hash.
    pub runtime_readiness_packet_hash_current: bool,
    /// Native payload digest from compile-artifact handoff evidence.
    pub compile_artifact_native_payload_sha256: Option<String>,
    /// Native payload digest from runtime/install-gate evidence.
    pub runtime_native_payload_sha256: Option<String>,
    /// Entry symbol from compile-artifact handoff evidence.
    pub compile_artifact_entry_symbol: Option<String>,
    /// Entry symbol from runtime/install-gate evidence.
    pub runtime_entry_symbol: Option<String>,
    /// Callable pointer from compile-artifact handoff evidence.
    pub compile_artifact_callable_pointer: Option<PetriNativeSuccessorCallablePointer>,
    /// Callable pointer from runtime/install-gate evidence.
    pub runtime_callable_pointer: Option<PetriNativeSuccessorCallablePointer>,
    /// Whether the runtime call packet was available.
    pub call_packet_available: bool,
    /// Runtime call-packet hash.
    pub call_packet_sha256: Option<String>,
    /// Canonical install-gate packet hash observed by runtime readiness.
    pub install_packet_hash: Option<ArtifactChecksum>,
    /// Persisted install-gate packet hash copied by runtime readiness.
    pub persisted_install_packet_hash: Option<ArtifactChecksum>,
    /// Runtime manifest identity hash.
    pub manifest_identity_sha256: Option<String>,
    /// Whether runtime readiness observed callable authorization.
    pub callable_authorized: bool,
    /// Whether runtime readiness accepted a runtime call.
    pub ready_for_runtime_call: bool,
    /// Whether runtime readiness itself authorized useful native execution.
    pub runtime_authorizes_useful_native: bool,
    /// Canonical execution authority decision hash.
    pub execution_authority_sha256: String,
}

impl PetriNativeSuccessorExecutionAuthorityDecision {
    /// Return true only when this decision authorizes native successor execution.
    pub const fn is_authorized_for_execution(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorExecutionAuthorityStatus::Authorized
        ) && self.authorized_for_execution
            && self.reason_code.is_none()
    }

    /// Emit stable JSON-free key/value rows for MCC sidecar consumers.
    pub fn manifest_rows(&self) -> Vec<PetriNativeSuccessorHandoffManifestRow> {
        let mut rows = Vec::new();
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ManifestSchema,
            PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA,
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ManifestSchemaVersion,
            PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA_VERSION.to_string(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::Surface,
            "execution_authority",
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::EvidenceSchema,
            self.schema,
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::EvidenceSchemaVersion,
            self.schema_version.to_string(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::Status,
            self.status.as_str(),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::AuthorizedForExecution,
            petri_native_successor_bool_code(self.authorized_for_execution),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ReasonCode,
            self.reason_code.unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::SourceReasonCode,
            self.source_reason_code.unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RequiredField,
            self.required_field.unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RequiredEvidence,
            self.required_evidence.unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactHandoffSha256,
            self.compile_artifact_handoff_sha256
                .as_deref()
                .unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeReadinessPacketSha256,
            self.runtime_readiness_packet_sha256
                .as_deref()
                .unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactHandoffHashCurrent,
            petri_native_successor_bool_code(self.compile_artifact_handoff_hash_current),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeReadinessPacketHashCurrent,
            petri_native_successor_bool_code(self.runtime_readiness_packet_hash_current),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactNativePayloadSha256,
            self.compile_artifact_native_payload_sha256
                .as_deref()
                .unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeNativePayloadSha256,
            self.runtime_native_payload_sha256.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactEntrySymbol,
            self.compile_artifact_entry_symbol.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeEntrySymbol,
            self.runtime_entry_symbol.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactCallablePointer,
            option_callable_pointer_manifest_value(self.compile_artifact_callable_pointer),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeCallablePointer,
            option_callable_pointer_manifest_value(self.runtime_callable_pointer),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CallPacketSha256,
            self.call_packet_sha256.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::InstallPacketHash,
            option_checksum_manifest_value(self.install_packet_hash),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::PersistedInstallPacketHash,
            option_checksum_manifest_value(self.persisted_install_packet_hash),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ManifestIdentitySha256,
            self.manifest_identity_sha256.as_deref().unwrap_or(""),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::CallableAuthorized,
            petri_native_successor_bool_code(self.callable_authorized),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ReadyForRuntimeCall,
            petri_native_successor_bool_code(self.ready_for_runtime_call),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeAuthorizesUsefulNative,
            petri_native_successor_bool_code(self.runtime_authorizes_useful_native),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::AuthorizesUsefulNative,
            petri_native_successor_bool_code(self.is_authorized_for_execution()),
        );
        push_petri_native_successor_handoff_manifest_row(
            &mut rows,
            PetriNativeSuccessorHandoffManifestRowKind::ExecutionAuthoritySha256,
            self.execution_authority_sha256.as_str(),
        );
        rows
    }

    /// Emit stable escaped `key=value` manifest lines in [`Self::manifest_rows`] order.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Validate this decision's emitted manifest rows with the shared fail-closed helper.
    pub fn manifest_validation_report(
        &self,
    ) -> PetriNativeSuccessorExecutionAuthorityManifestValidationReport {
        let rows = self.manifest_rows();
        validate_petri_native_successor_execution_authority_manifest_rows(&rows)
    }

    /// Return a stable replay identity for this decision's emitted manifest rows.
    pub fn manifest_replay_identity(&self) -> PetriNativeSuccessorExecutionAuthorityReplayIdentity {
        let rows = self.manifest_rows();
        petri_native_successor_execution_authority_replay_identity_for_manifest_rows(&rows)
    }

    /// Return a compact authority summary for this decision's emitted manifest rows.
    pub fn compact_authority_summary(&self) -> PetriNativeSuccessorExecutionAuthoritySummary {
        let rows = self.manifest_rows();
        petri_native_successor_execution_authority_summary_for_manifest_rows(&rows)
    }

    /// Return the stable hash of this execution authority decision.
    pub fn canonical_execution_authority_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.execution_authority_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, self.status.as_str());
        put_bool(&mut out, self.authorized_for_execution);
        put_option_str(&mut out, self.reason_code);
        put_option_str(&mut out, self.source_reason_code);
        put_option_str(&mut out, self.required_field);
        put_option_str(&mut out, self.required_evidence);
        put_option_str(&mut out, self.compile_artifact_handoff_sha256.as_deref());
        put_option_str(&mut out, self.runtime_readiness_packet_sha256.as_deref());
        put_bool(&mut out, self.compile_artifact_handoff_hash_current);
        put_bool(&mut out, self.runtime_readiness_packet_hash_current);
        put_option_str(
            &mut out,
            self.compile_artifact_native_payload_sha256.as_deref(),
        );
        put_option_str(&mut out, self.runtime_native_payload_sha256.as_deref());
        put_option_str(&mut out, self.compile_artifact_entry_symbol.as_deref());
        put_option_str(&mut out, self.runtime_entry_symbol.as_deref());
        put_option_callable_pointer(&mut out, self.compile_artifact_callable_pointer);
        put_option_callable_pointer(&mut out, self.runtime_callable_pointer);
        put_bool(&mut out, self.call_packet_available);
        put_option_str(&mut out, self.call_packet_sha256.as_deref());
        put_option_checksum(&mut out, self.install_packet_hash);
        put_option_checksum(&mut out, self.persisted_install_packet_hash);
        put_option_str(&mut out, self.manifest_identity_sha256.as_deref());
        put_bool(&mut out, self.callable_authorized);
        put_bool(&mut out, self.ready_for_runtime_call);
        put_bool(&mut out, self.runtime_authorizes_useful_native);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_execution_authority_sha256(mut self) -> Self {
        self.execution_authority_sha256 = self.canonical_execution_authority_sha256();
        self
    }
}

/// Production selection status for a Petri/MCC native successor artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorProductionSelectionStatus {
    /// Trust Codegen selected the native successor lane for production execution.
    Selected,
    /// Trust Codegen failed the native successor lane closed.
    FailClosed,
}

impl PetriNativeSuccessorProductionSelectionStatus {
    /// Return the stable lower-snake-case status string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Selected => "selected",
            Self::FailClosed => "fail_closed",
        }
    }
}

/// Typed pre-runtime production-selection decision for Petri/MCC native successors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorProductionSelectionDecision {
    /// Production-selection schema.
    pub schema: &'static str,
    /// Production-selection schema version.
    pub schema_version: u32,
    /// Selected or fail-closed status.
    pub status: PetriNativeSuccessorProductionSelectionStatus,
    /// True only when Trust Codegen selected the native lane for production execution.
    pub selected_for_native_execution: bool,
    /// True when the native lane must remain fail-closed.
    pub fail_closed: bool,
    /// Stable fail-closed reason code.
    pub reason_code: Option<&'static str>,
    /// Source reason code from execution authority or call-packet evidence.
    pub source_reason_code: Option<&'static str>,
    /// Exact evidence schema required to clear the blocker, when applicable.
    pub required_evidence: Option<&'static str>,
    /// Execution authority decision hash.
    pub execution_authority_sha256: String,
    /// Whether the execution authority hash matches its current canonical value.
    pub execution_authority_hash_current: bool,
    /// Runtime call-packet hash.
    pub call_packet_sha256: Option<String>,
    /// Whether the supplied call packet hash matches its current canonical value.
    pub call_packet_hash_current: bool,
    /// Compile-artifact handoff evidence hash.
    pub compile_artifact_handoff_sha256: Option<String>,
    /// Runtime readiness packet hash.
    pub runtime_readiness_packet_sha256: Option<String>,
    /// Native payload digest from compile-artifact handoff evidence.
    pub compile_artifact_native_payload_sha256: Option<String>,
    /// Native payload digest from runtime/install-gate evidence.
    pub runtime_native_payload_sha256: Option<String>,
    /// Native payload digest from the runtime call packet.
    pub call_packet_native_payload_sha256: Option<String>,
    /// Entry symbol from compile-artifact handoff evidence.
    pub compile_artifact_entry_symbol: Option<String>,
    /// Entry symbol from runtime/install-gate evidence.
    pub runtime_entry_symbol: Option<String>,
    /// Entry symbol from the runtime call packet.
    pub call_packet_entry_symbol: Option<String>,
    /// Callable pointer from compile-artifact handoff evidence.
    pub compile_artifact_callable_pointer: Option<PetriNativeSuccessorCallablePointer>,
    /// Callable pointer from runtime/install-gate evidence.
    pub runtime_callable_pointer: Option<PetriNativeSuccessorCallablePointer>,
    /// Callable pointer from the runtime call packet.
    pub call_packet_callable_pointer: Option<PetriNativeSuccessorCallablePointer>,
    /// Canonical install-gate packet hash.
    pub install_packet_hash: Option<ArtifactChecksum>,
    /// Persisted install-gate packet hash copied by runtime readiness.
    pub persisted_install_packet_hash: Option<ArtifactChecksum>,
    /// Runtime manifest identity hash.
    pub manifest_identity_sha256: Option<String>,
    /// Whether callable-lane admission was present and accepted.
    pub callable_lane_admitted: bool,
    /// Whether runtime readiness accepted a runtime call.
    pub runtime_ready_for_call: bool,
    /// Whether runtime readiness authorized useful native execution.
    pub runtime_authorizes_useful_native: bool,
    /// Whether Trust Codegen lowerer support for trust_ir vector constants is available to this lane.
    pub vector_constant_lowering_supported: bool,
    /// Stable vector-constant lowering evidence schema.
    pub vector_constant_lowering_evidence_schema: &'static str,
    /// Stable vector-constant lowering evidence schema version.
    pub vector_constant_lowering_evidence_schema_version: u32,
    /// Stable vector-constant lowering status code.
    pub vector_constant_lowering_status_code: &'static str,
    /// trust_ir shared-primitive contract manifest schema carried by this readiness packet.
    pub trust_ir_shared_primitive_contract_manifest_schema: &'static str,
    /// trust_ir shared-primitive contract manifest schema version.
    pub trust_ir_shared_primitive_contract_manifest_schema_version: u32,
    /// Number of rows in the trust_ir shared-primitive contract manifest.
    pub trust_ir_shared_primitive_contract_manifest_row_count: usize,
    /// Stable digest of the trust_ir shared-primitive contract manifest rows.
    pub trust_ir_shared_primitive_contract_manifest_sha256: String,
    /// trust_ir shared-primitive contract schema.
    pub trust_ir_shared_primitive_contract_schema: &'static str,
    /// trust_ir solver/model readiness report schema for the Petri/trust-mc primitive.
    pub trust_ir_shared_primitive_readiness_report_schema: &'static str,
    /// Trust Codegen/AY route descriptor id carried by this readiness packet.
    pub trust_mc_admission_route_descriptor_id: &'static str,
    /// Trust Codegen/AY route descriptor schema carried by this readiness packet.
    pub trust_mc_admission_route_descriptor_schema: &'static str,
    /// Stable digest of the Trust Codegen/AY route readiness descriptor.
    pub trust_mc_admission_route_readiness_identity_sha256: String,
    /// AY/trust_ir model acceptance report API required by this route.
    pub trust_mc_admission_route_model_acceptance_report_api: &'static str,
    /// Consumer acceptance API required before downstream production promotion.
    pub trust_mc_admission_route_consumer_acceptance_api: &'static str,
    /// Canonical production-selection decision hash.
    pub production_selection_sha256: String,
}

impl PetriNativeSuccessorProductionSelectionDecision {
    /// Return true only when the native lane is selected for production execution.
    pub const fn is_selected_for_native_execution(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorProductionSelectionStatus::Selected
        ) && self.selected_for_native_execution
            && !self.fail_closed
            && self.reason_code.is_none()
    }

    /// Emit deterministic key/value rows for downstream production-selection consumers.
    pub fn manifest_rows(&self) -> Vec<PetriNativeSuccessorExecutionAuthoritySummaryRow> {
        vec![
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new("selection.schema", self.schema),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "selection.schema_version",
                self.schema_version.to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "selection.status",
                self.status.as_str(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "selection.selected_for_native_execution",
                petri_native_successor_bool_code(self.selected_for_native_execution),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "selection.fail_closed",
                petri_native_successor_bool_code(self.fail_closed),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "selection.reason_code",
                self.reason_code.unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "selection.source_reason_code",
                self.source_reason_code.unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "selection.required_evidence",
                self.required_evidence.unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "authority.execution_authority_sha256",
                self.execution_authority_sha256.as_str(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "authority.execution_authority_hash_current",
                petri_native_successor_bool_code(self.execution_authority_hash_current),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "callable.call_packet_sha256",
                self.call_packet_sha256.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "callable.call_packet_hash_current",
                petri_native_successor_bool_code(self.call_packet_hash_current),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "handoff.compile_artifact_handoff_sha256",
                self.compile_artifact_handoff_sha256
                    .as_deref()
                    .unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "runtime.readiness_packet_sha256",
                self.runtime_readiness_packet_sha256
                    .as_deref()
                    .unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "compile_artifact.native_payload_sha256",
                self.compile_artifact_native_payload_sha256
                    .as_deref()
                    .unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "runtime.native_payload_sha256",
                self.runtime_native_payload_sha256.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "call_packet.native_payload_sha256",
                self.call_packet_native_payload_sha256
                    .as_deref()
                    .unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "compile_artifact.entry_symbol",
                self.compile_artifact_entry_symbol.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "runtime.entry_symbol",
                self.runtime_entry_symbol.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "call_packet.entry_symbol",
                self.call_packet_entry_symbol.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "compile_artifact.callable_pointer",
                option_callable_pointer_manifest_value(self.compile_artifact_callable_pointer),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "runtime.callable_pointer",
                option_callable_pointer_manifest_value(self.runtime_callable_pointer),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "call_packet.callable_pointer",
                option_callable_pointer_manifest_value(self.call_packet_callable_pointer),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "install_gate.packet_hash",
                option_checksum_manifest_value(self.install_packet_hash),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "install_gate.persisted_packet_hash",
                option_checksum_manifest_value(self.persisted_install_packet_hash),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "install_gate.manifest_identity_sha256",
                self.manifest_identity_sha256.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "callable.lane_admitted",
                petri_native_successor_bool_code(self.callable_lane_admitted),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "runtime.ready_for_call",
                petri_native_successor_bool_code(self.runtime_ready_for_call),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "runtime.authorizes_useful_native",
                petri_native_successor_bool_code(self.runtime_authorizes_useful_native),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust-cg.vector_constant_lowering.schema",
                self.vector_constant_lowering_evidence_schema,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust-cg.vector_constant_lowering.schema_version",
                self.vector_constant_lowering_evidence_schema_version
                    .to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust-cg.vector_constant_lowering.status",
                self.vector_constant_lowering_status_code,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust-cg.vector_constant_lowering.supported",
                petri_native_successor_bool_code(self.vector_constant_lowering_supported),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_ir.shared_primitive_contract.manifest_schema",
                self.trust_ir_shared_primitive_contract_manifest_schema,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_ir.shared_primitive_contract.manifest_schema_version",
                self.trust_ir_shared_primitive_contract_manifest_schema_version
                    .to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_ir.shared_primitive_contract.manifest_row_count",
                self.trust_ir_shared_primitive_contract_manifest_row_count
                    .to_string(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_ir.shared_primitive_contract.manifest_sha256",
                self.trust_ir_shared_primitive_contract_manifest_sha256
                    .as_str(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_ir.shared_primitive_contract.schema",
                self.trust_ir_shared_primitive_contract_schema,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_ir.shared_primitive_contract.readiness_report_schema",
                self.trust_ir_shared_primitive_readiness_report_schema,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_mc_admission_route.descriptor_id",
                self.trust_mc_admission_route_descriptor_id,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_mc_admission_route.descriptor_schema",
                self.trust_mc_admission_route_descriptor_schema,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_mc_admission_route.readiness_identity_sha256",
                self.trust_mc_admission_route_readiness_identity_sha256
                    .as_str(),
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_mc_admission_route.model_acceptance_report_api",
                self.trust_mc_admission_route_model_acceptance_report_api,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "trust_mc_admission_route.consumer_acceptance_api",
                self.trust_mc_admission_route_consumer_acceptance_api,
            ),
            PetriNativeSuccessorExecutionAuthoritySummaryRow::new(
                "selection.production_selection_sha256",
                self.production_selection_sha256.as_str(),
            ),
        ]
    }

    /// Emit stable escaped `key=value` manifest lines in [`Self::manifest_rows`] order.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Return the stable hash of this production-selection decision.
    pub fn canonical_production_selection_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.production_selection_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, self.status.as_str());
        put_bool(&mut out, self.selected_for_native_execution);
        put_bool(&mut out, self.fail_closed);
        put_option_str(&mut out, self.reason_code);
        put_option_str(&mut out, self.source_reason_code);
        put_option_str(&mut out, self.required_evidence);
        put_str(&mut out, &self.execution_authority_sha256);
        put_bool(&mut out, self.execution_authority_hash_current);
        put_option_str(&mut out, self.call_packet_sha256.as_deref());
        put_bool(&mut out, self.call_packet_hash_current);
        put_option_str(&mut out, self.compile_artifact_handoff_sha256.as_deref());
        put_option_str(&mut out, self.runtime_readiness_packet_sha256.as_deref());
        put_option_str(
            &mut out,
            self.compile_artifact_native_payload_sha256.as_deref(),
        );
        put_option_str(&mut out, self.runtime_native_payload_sha256.as_deref());
        put_option_str(&mut out, self.call_packet_native_payload_sha256.as_deref());
        put_option_str(&mut out, self.compile_artifact_entry_symbol.as_deref());
        put_option_str(&mut out, self.runtime_entry_symbol.as_deref());
        put_option_str(&mut out, self.call_packet_entry_symbol.as_deref());
        put_option_callable_pointer(&mut out, self.compile_artifact_callable_pointer);
        put_option_callable_pointer(&mut out, self.runtime_callable_pointer);
        put_option_callable_pointer(&mut out, self.call_packet_callable_pointer);
        put_option_checksum(&mut out, self.install_packet_hash);
        put_option_checksum(&mut out, self.persisted_install_packet_hash);
        put_option_str(&mut out, self.manifest_identity_sha256.as_deref());
        put_bool(&mut out, self.callable_lane_admitted);
        put_bool(&mut out, self.runtime_ready_for_call);
        put_bool(&mut out, self.runtime_authorizes_useful_native);
        put_bool(&mut out, self.vector_constant_lowering_supported);
        put_str(&mut out, self.vector_constant_lowering_evidence_schema);
        put_u32(
            &mut out,
            self.vector_constant_lowering_evidence_schema_version,
        );
        put_str(&mut out, self.vector_constant_lowering_status_code);
        put_str(
            &mut out,
            self.trust_ir_shared_primitive_contract_manifest_schema,
        );
        put_u32(
            &mut out,
            self.trust_ir_shared_primitive_contract_manifest_schema_version,
        );
        put_u64(
            &mut out,
            self.trust_ir_shared_primitive_contract_manifest_row_count as u64,
        );
        put_str(
            &mut out,
            &self.trust_ir_shared_primitive_contract_manifest_sha256,
        );
        put_str(&mut out, self.trust_ir_shared_primitive_contract_schema);
        put_str(
            &mut out,
            self.trust_ir_shared_primitive_readiness_report_schema,
        );
        put_str(&mut out, self.trust_mc_admission_route_descriptor_id);
        put_str(&mut out, self.trust_mc_admission_route_descriptor_schema);
        put_str(
            &mut out,
            &self.trust_mc_admission_route_readiness_identity_sha256,
        );
        put_str(
            &mut out,
            self.trust_mc_admission_route_model_acceptance_report_api,
        );
        put_str(
            &mut out,
            self.trust_mc_admission_route_consumer_acceptance_api,
        );
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_production_selection_sha256(mut self) -> Self {
        self.production_selection_sha256 = self.canonical_production_selection_sha256();
        self
    }
}

/// Explicit gate for the Petri/MCC mock executable-call dry-run harness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorMockExecutableCallGate {
    /// Mock executable-call schema.
    pub schema: &'static str,
    /// Mock executable-call schema version.
    pub schema_version: u32,
    /// Whether this test-only dry-run gate is enabled.
    pub enabled: bool,
    /// Stable gate kind.
    pub gate_kind: &'static str,
    /// Runtime owner asking for the dry-run boundary.
    pub runtime_owner: String,
}

impl PetriNativeSuccessorMockExecutableCallGate {
    /// Return a production-default disabled gate.
    pub fn disabled_for_production() -> Self {
        Self {
            schema: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA,
            schema_version: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA_VERSION,
            enabled: false,
            gate_kind: "production_fail_closed",
            runtime_owner: "production".to_owned(),
        }
    }

    /// Return an explicit test-only dry-run gate.
    pub fn test_only(runtime_owner: impl Into<String>) -> Option<Self> {
        let runtime_owner = runtime_owner.into();
        if missing_required_text(&runtime_owner) {
            return None;
        }

        Some(Self {
            schema: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA,
            schema_version: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA_VERSION,
            enabled: true,
            gate_kind: "test_only_mock_executable_call",
            runtime_owner,
        })
    }
}

/// Mock executable-call dry-run status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorMockExecutableCallStatus {
    /// The dry-run reached the typed callable boundary without invoking native code.
    DryRunAccepted,
    /// The dry-run remained fail-closed.
    Blocked,
}

impl PetriNativeSuccessorMockExecutableCallStatus {
    /// Return the stable lower-snake-case status string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DryRunAccepted => "dry_run_accepted",
            Self::Blocked => "blocked",
        }
    }
}

/// Stable blocker for the Petri/MCC mock executable-call dry-run harness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorMockExecutableCallBlocker {
    /// The explicit mock dry-run gate was not enabled.
    MockHarnessDisabled,
    /// The readiness packet hash was stale or tampered.
    RuntimeReadinessHashMismatch,
    /// The readiness packet was not ready for a runtime call.
    RuntimeReadinessBlocked,
    /// No call packet was supplied.
    CallPacketMissing,
    /// The call packet hash was stale or tampered.
    CallPacketHashMismatch,
    /// The supplied call packet did not match the readiness packet.
    CallPacketBindingMismatch,
    /// The readiness packet and call packet disagree on the callable pointer.
    CallablePointerMismatch,
    /// The call packet did not use the stable Petri native successor trampoline ABI.
    TrampolineAbiMismatch,
    /// The call packet did not use the stable Petri native successor state encoding.
    StateEncodingMismatch,
    /// The input buffer did not match the call packet ABI.
    InputStateBytesMismatch,
    /// The output buffer did not match the call packet ABI.
    OutputStateBytesMismatch,
}

impl PetriNativeSuccessorMockExecutableCallBlocker {
    /// Return the stable lower-snake-case blocker string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MockHarnessDisabled => "mock_harness_disabled",
            Self::RuntimeReadinessHashMismatch => "runtime_readiness_hash_mismatch",
            Self::RuntimeReadinessBlocked => "runtime_readiness_blocked",
            Self::CallPacketMissing => "call_packet_missing",
            Self::CallPacketHashMismatch => "call_packet_hash_mismatch",
            Self::CallPacketBindingMismatch => "call_packet_binding_mismatch",
            Self::CallablePointerMismatch => "callable_pointer_mismatch",
            Self::TrampolineAbiMismatch => "trampoline_abi_mismatch",
            Self::StateEncodingMismatch => "state_encoding_mismatch",
            Self::InputStateBytesMismatch => "input_state_bytes_mismatch",
            Self::OutputStateBytesMismatch => "output_state_bytes_mismatch",
        }
    }

    /// Return the exact evidence schema required to clear this blocker.
    pub const fn required_evidence(self) -> &'static str {
        match self {
            Self::MockHarnessDisabled => PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA,
            Self::RuntimeReadinessHashMismatch | Self::RuntimeReadinessBlocked => {
                PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA
            }
            Self::CallPacketMissing
            | Self::CallPacketHashMismatch
            | Self::CallPacketBindingMismatch
            | Self::CallablePointerMismatch
            | Self::TrampolineAbiMismatch
            | Self::StateEncodingMismatch
            | Self::InputStateBytesMismatch
            | Self::OutputStateBytesMismatch => PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA,
        }
    }
}

/// Test-only dry-run report for carrying a ready packet to a callable boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorMockExecutableCallReport {
    /// Mock executable-call schema.
    pub schema: &'static str,
    /// Mock executable-call schema version.
    pub schema_version: u32,
    /// Dry-run status.
    pub status: PetriNativeSuccessorMockExecutableCallStatus,
    /// Whether the dry-run reached the typed callable boundary.
    pub callable_boundary_reached: bool,
    /// Stable fail-closed blocker.
    pub blocker: Option<PetriNativeSuccessorMockExecutableCallBlocker>,
    /// Stable fail-closed reason code.
    pub reason_code: Option<&'static str>,
    /// Exact evidence schema required to clear this blocker, when applicable.
    pub required_evidence: Option<&'static str>,
    /// Whether the explicit mock gate was enabled.
    pub gate_enabled: bool,
    /// Stable mock gate kind.
    pub gate_kind: &'static str,
    /// Runtime owner asking for the dry-run boundary.
    pub runtime_owner: String,
    /// Runtime readiness packet hash.
    pub runtime_readiness_packet_sha256: String,
    /// Call-packet identity, when supplied.
    pub call_packet_sha256: Option<String>,
    /// Non-null host callable pointer identity, when supplied.
    pub callable_pointer: Option<PetriNativeSuccessorCallablePointer>,
    /// Observed input state byte length.
    pub input_state_bytes: u64,
    /// Expected input state byte length from the call packet.
    pub expected_input_state_bytes: Option<u64>,
    /// Observed output state byte length.
    pub output_state_bytes: u64,
    /// Expected output state byte length from the call packet.
    pub expected_output_state_bytes: Option<u64>,
    /// Stable state encoding from the call packet.
    pub state_encoding: Option<&'static str>,
    /// Stable trampoline ABI from the call packet.
    pub trampoline_abi: Option<&'static str>,
    /// Canonical mock executable-call report hash.
    pub mock_executable_call_report_sha256: String,
}

impl PetriNativeSuccessorMockExecutableCallReport {
    /// Return true only when the dry-run reached the typed callable boundary.
    pub const fn is_dry_run_accepted(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorMockExecutableCallStatus::DryRunAccepted
        ) && self.callable_boundary_reached
            && self.blocker.is_none()
    }

    /// Return the stable hash of this mock executable-call report.
    pub fn canonical_mock_executable_call_report_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.mock_executable_call_report_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, self.status.as_str());
        put_bool(&mut out, self.callable_boundary_reached);
        put_option_str(&mut out, self.blocker.map(|blocker| blocker.as_str()));
        put_option_str(&mut out, self.required_evidence);
        put_bool(&mut out, self.gate_enabled);
        put_str(&mut out, self.gate_kind);
        put_str(&mut out, &self.runtime_owner);
        put_str(&mut out, &self.runtime_readiness_packet_sha256);
        put_option_str(&mut out, self.call_packet_sha256.as_deref());
        put_option_callable_pointer(&mut out, self.callable_pointer);
        put_u64(&mut out, self.input_state_bytes);
        put_option_u64(&mut out, self.expected_input_state_bytes);
        put_u64(&mut out, self.output_state_bytes);
        put_option_u64(&mut out, self.expected_output_state_bytes);
        put_option_str(&mut out, self.state_encoding);
        put_option_str(&mut out, self.trampoline_abi);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_mock_executable_call_report_sha256(mut self) -> Self {
        self.mock_executable_call_report_sha256 =
            self.canonical_mock_executable_call_report_sha256();
        self
    }
}

/// Stable Petri native successor runtime-call entrypoint ABI.
pub type PetriNativeSuccessorRuntimeCallableFn = extern "C" fn(
    input_state: *const u8,
    input_state_len: u64,
    output_state: *mut u8,
    output_state_len: u64,
    status_slot: *mut u32,
) -> i32;

/// Typed host entrypoint for a Petri/MCC native successor trampoline.
#[derive(Clone, Copy)]
pub struct PetriNativeSuccessorRuntimeCallableEntrypoint {
    callable_pointer: PetriNativeSuccessorCallablePointer,
    function: PetriNativeSuccessorRuntimeCallableFn,
}

impl std::fmt::Debug for PetriNativeSuccessorRuntimeCallableEntrypoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PetriNativeSuccessorRuntimeCallableEntrypoint")
            .field("callable_pointer", &self.callable_pointer)
            .finish_non_exhaustive()
    }
}

impl PetriNativeSuccessorRuntimeCallableEntrypoint {
    /// Bind a concrete typed host function to the stable Petri successor runtime ABI.
    pub fn new(function: PetriNativeSuccessorRuntimeCallableFn) -> Option<Self> {
        let callable_pointer = PetriNativeSuccessorCallablePointer::from_ptr(function as *const ());
        callable_pointer.map(|callable_pointer| Self {
            callable_pointer,
            function,
        })
    }

    /// Return the non-null callable pointer identity for this entrypoint.
    pub const fn callable_pointer(self) -> PetriNativeSuccessorCallablePointer {
        self.callable_pointer
    }
}

/// Runtime callable invocation status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorRuntimeCallStatus {
    /// Trust Codegen validated the handoff and invoked the native entrypoint.
    Executed,
    /// The handoff failed closed before native code was invoked.
    Blocked,
}

impl PetriNativeSuccessorRuntimeCallStatus {
    /// Return the stable lower-snake-case status string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Executed => "executed",
            Self::Blocked => "blocked",
        }
    }
}

/// Stable blocker for real Petri/MCC native successor runtime calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeSuccessorRuntimeCallBlocker {
    /// The readiness packet hash was stale or tampered.
    RuntimeReadinessHashMismatch,
    /// Runtime readiness was not ready for a host call.
    RuntimeReadinessBlocked,
    /// The execution authority decision hash was stale or tampered.
    ExecutionAuthorityHashMismatch,
    /// Execution authority did not authorize a native call.
    ExecutionAuthorityNotAuthorized,
    /// The call packet hash was stale or tampered.
    CallPacketHashMismatch,
    /// The call packet did not match readiness and authority evidence.
    CallPacketBindingMismatch,
    /// The concrete typed entrypoint did not match the call packet pointer.
    CallablePointerMismatch,
    /// The call packet did not use the stable Petri native successor trampoline ABI.
    TrampolineAbiMismatch,
    /// The call packet did not use the stable Petri native successor state encoding.
    StateEncodingMismatch,
    /// The input buffer did not match the call packet ABI.
    InputStateBytesMismatch,
    /// The output buffer did not match the call packet ABI.
    OutputStateBytesMismatch,
}

impl PetriNativeSuccessorRuntimeCallBlocker {
    /// Return the stable lower-snake-case blocker string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RuntimeReadinessHashMismatch => "runtime_readiness_hash_mismatch",
            Self::RuntimeReadinessBlocked => "runtime_readiness_blocked",
            Self::ExecutionAuthorityHashMismatch => "execution_authority_hash_mismatch",
            Self::ExecutionAuthorityNotAuthorized => "execution_authority_not_authorized",
            Self::CallPacketHashMismatch => "call_packet_hash_mismatch",
            Self::CallPacketBindingMismatch => "call_packet_binding_mismatch",
            Self::CallablePointerMismatch => "callable_pointer_mismatch",
            Self::TrampolineAbiMismatch => "trampoline_abi_mismatch",
            Self::StateEncodingMismatch => "state_encoding_mismatch",
            Self::InputStateBytesMismatch => "input_state_bytes_mismatch",
            Self::OutputStateBytesMismatch => "output_state_bytes_mismatch",
        }
    }

    /// Return the exact evidence schema required to clear this blocker.
    pub const fn required_evidence(self) -> &'static str {
        match self {
            Self::RuntimeReadinessHashMismatch | Self::RuntimeReadinessBlocked => {
                PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA
            }
            Self::ExecutionAuthorityHashMismatch | Self::ExecutionAuthorityNotAuthorized => {
                PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA
            }
            Self::CallPacketHashMismatch
            | Self::CallPacketBindingMismatch
            | Self::CallablePointerMismatch
            | Self::TrampolineAbiMismatch
            | Self::StateEncodingMismatch
            | Self::InputStateBytesMismatch
            | Self::OutputStateBytesMismatch => PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA,
        }
    }
}

/// Report from a real Petri/MCC native successor runtime callable invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorRuntimeCallReport {
    /// Runtime-call schema.
    pub schema: &'static str,
    /// Runtime-call schema version.
    pub schema_version: u32,
    /// Runtime-call status.
    pub status: PetriNativeSuccessorRuntimeCallStatus,
    /// True only when Trust Codegen actually invoked the native entrypoint.
    pub callable_invoked: bool,
    /// Stable fail-closed blocker.
    pub blocker: Option<PetriNativeSuccessorRuntimeCallBlocker>,
    /// Stable fail-closed reason code.
    pub reason_code: Option<&'static str>,
    /// Exact evidence schema required to clear this blocker, when applicable.
    pub required_evidence: Option<&'static str>,
    /// Runtime readiness packet hash.
    pub runtime_readiness_packet_sha256: String,
    /// Execution authority decision hash.
    pub execution_authority_sha256: String,
    /// Call-packet identity.
    pub call_packet_sha256: String,
    /// Non-null host callable pointer identity.
    pub callable_pointer: PetriNativeSuccessorCallablePointer,
    /// Observed input state byte length.
    pub input_state_bytes: u64,
    /// Expected input state byte length from the call packet.
    pub expected_input_state_bytes: u64,
    /// Observed output state byte length.
    pub output_state_bytes: u64,
    /// Expected output state byte length from the call packet.
    pub expected_output_state_bytes: u64,
    /// Stable input-state digest captured before the call.
    pub input_state_sha256: String,
    /// Stable output-state digest captured after the call, or at rejection time.
    pub output_state_sha256: String,
    /// Return code from the native entrypoint, if invoked.
    pub entrypoint_return_code: Option<i32>,
    /// Status slot written by the native entrypoint, if invoked.
    pub entrypoint_status_slot: Option<u32>,
    /// Stable state encoding from the call packet.
    pub state_encoding: &'static str,
    /// Stable trampoline ABI from the call packet.
    pub trampoline_abi: &'static str,
    /// Canonical runtime-call report hash.
    pub runtime_call_report_sha256: String,
}

impl PetriNativeSuccessorRuntimeCallReport {
    /// Return true only when the native callable was invoked.
    pub const fn is_executed(&self) -> bool {
        matches!(self.status, PetriNativeSuccessorRuntimeCallStatus::Executed)
            && self.callable_invoked
            && self.blocker.is_none()
    }

    /// Return the stable hash of this runtime-call report.
    pub fn canonical_runtime_call_report_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.petri.native_successor.runtime_call_report_hash.v1",
        );
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_str(&mut out, self.status.as_str());
        put_bool(&mut out, self.callable_invoked);
        put_option_str(&mut out, self.blocker.map(|blocker| blocker.as_str()));
        put_option_str(&mut out, self.required_evidence);
        put_str(&mut out, &self.runtime_readiness_packet_sha256);
        put_str(&mut out, &self.execution_authority_sha256);
        put_str(&mut out, &self.call_packet_sha256);
        put_u64(&mut out, self.callable_pointer.addr_usize() as u64);
        put_u64(&mut out, self.input_state_bytes);
        put_u64(&mut out, self.expected_input_state_bytes);
        put_u64(&mut out, self.output_state_bytes);
        put_u64(&mut out, self.expected_output_state_bytes);
        put_str(&mut out, &self.input_state_sha256);
        put_str(&mut out, &self.output_state_sha256);
        put_option_i32(&mut out, self.entrypoint_return_code);
        put_option_u32(&mut out, self.entrypoint_status_slot);
        put_str(&mut out, self.state_encoding);
        put_str(&mut out, self.trampoline_abi);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn with_canonical_runtime_call_report_sha256(mut self) -> Self {
        self.runtime_call_report_sha256 = self.canonical_runtime_call_report_sha256();
        self
    }
}

/// Compact schema descriptor for one Petri native successor evidence surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PetriNativeSuccessorEvidenceSurfaceDescriptor {
    /// Stable local surface name.
    pub name: &'static str,
    /// Public schema emitted by this surface.
    pub schema: &'static str,
    /// Public schema version emitted by this surface.
    pub schema_version: u32,
    /// Required caller-supplied field names for this surface.
    pub required_fields: &'static [&'static str],
    /// Stable status-code vocabulary emitted by this surface.
    pub status_codes: &'static [&'static str],
    /// Stable blocker-code vocabulary emitted by this surface.
    pub blocker_codes: &'static [&'static str],
    /// trust_ir shared primitive contract applicable to this production surface.
    pub shared_primitive_contract: Option<trust_ir::NativeSharedPrimitiveContractDescriptor>,
}

/// Authoritative descriptor for the Petri native successor call-packet surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PetriNativeSuccessorCallPacketContractDescriptor {
    /// Descriptor schema.
    pub schema: &'static str,
    /// Descriptor schema version.
    pub schema_version: u32,
    /// Stable descriptor identity.
    pub descriptor_id: &'static str,
    /// Stable descriptor status.
    pub status_code: &'static str,
    /// Stable production posture for this surface.
    pub production_status_code: &'static str,
    /// Stable local surface name.
    pub surface_name: &'static str,
    /// Public schema emitted by call packets.
    pub evidence_schema: &'static str,
    /// Public schema version emitted by call packets.
    pub evidence_schema_version: u32,
    /// Required caller-supplied field names for this surface.
    pub required_fields: &'static [&'static str],
    /// Stable status-code vocabulary represented by this surface.
    pub status_codes: &'static [&'static str],
    /// Stable blocker-code vocabulary represented by this surface.
    pub blocker_codes: &'static [&'static str],
    /// Runtime evidence required before production code may dereference the pointer.
    pub required_runtime_evidence: &'static [&'static str],
    /// True when Trust Codegen owns this descriptor and no upstream placeholder is needed.
    pub authoritative: bool,
    /// True only if downstreams still need an upstream descriptor placeholder.
    pub upstream_pending: bool,
    /// True when the descriptor is safe to publish in production metadata.
    pub production_safe: bool,
    /// True only when the call-packet surface alone authorizes host execution.
    pub authorizes_runtime_execution: bool,
    /// True when production must also validate runtime readiness.
    pub production_runtime_gate_required: bool,
    /// trust_ir shared primitive contract applicable to the call packet producer.
    pub shared_primitive_contract: Option<trust_ir::NativeSharedPrimitiveContractDescriptor>,
}

impl PetriNativeSuccessorCallPacketContractDescriptor {
    /// Return true only for the Trust Codegen-owned authoritative call-packet descriptor.
    pub const fn is_authoritative(self) -> bool {
        self.authoritative && !self.upstream_pending
    }

    /// Return true when the call packet must remain fail-closed for runtime use.
    pub const fn fails_closed_for_runtime_execution(self) -> bool {
        !self.authorizes_runtime_execution && self.production_runtime_gate_required
    }

    /// Emit deterministic key/value rows for downstream descriptor validation.
    pub fn manifest_rows(&self) -> Vec<PetriNativeSuccessorCallPacketContractDescriptorRow> {
        let mut rows = vec![
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.schema",
                self.schema,
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.schema_version",
                self.schema_version.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.id",
                self.descriptor_id,
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.status",
                self.status_code,
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.production_status",
                self.production_status_code,
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.authoritative",
                petri_native_successor_bool_code(self.authoritative),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.upstream_pending",
                petri_native_successor_bool_code(self.upstream_pending),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.production_safe",
                petri_native_successor_bool_code(self.production_safe),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.authorizes_runtime_execution",
                petri_native_successor_bool_code(self.authorizes_runtime_execution),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.production_runtime_gate_required",
                petri_native_successor_bool_code(self.production_runtime_gate_required),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "surface.name",
                self.surface_name,
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "surface.schema",
                self.evidence_schema,
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "surface.schema_version",
                self.evidence_schema_version.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "required_field_count",
                self.required_fields.len().to_string(),
            ),
        ];

        for (index, field) in self.required_fields.iter().enumerate() {
            rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                format!("required_field.{index}"),
                *field,
            ));
        }
        rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
            "status_code_count",
            self.status_codes.len().to_string(),
        ));
        for (index, code) in self.status_codes.iter().enumerate() {
            rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                format!("status_code.{index}"),
                *code,
            ));
        }
        rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
            "blocker_code_count",
            self.blocker_codes.len().to_string(),
        ));
        for (index, code) in self.blocker_codes.iter().enumerate() {
            rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                format!("blocker_code.{index}"),
                *code,
            ));
        }
        rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
            "required_runtime_evidence_count",
            self.required_runtime_evidence.len().to_string(),
        ));
        for (index, schema) in self.required_runtime_evidence.iter().enumerate() {
            rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                format!("required_runtime_evidence.{index}"),
                *schema,
            ));
        }
        rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
            "shared_primitive.contract_schema",
            self.shared_primitive_contract
                .map(|contract| contract.contract_schema)
                .unwrap_or(""),
        ));
        rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
            "shared_primitive.consumer_acceptance_api",
            self.shared_primitive_contract
                .map(|contract| contract.consumer_acceptance_api_name)
                .unwrap_or(""),
        ));

        rows
    }

    /// Emit stable escaped `key=value` descriptor lines in [`Self::manifest_rows`] order.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .iter()
            .map(PetriNativeSuccessorCallPacketContractDescriptorRow::to_key_value_line)
            .collect()
    }
}

/// Stable key/value row for call-packet contract descriptors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorCallPacketContractDescriptorRow {
    /// Manifest row key.
    pub key: String,
    /// Manifest row value.
    pub value: String,
}

impl PetriNativeSuccessorCallPacketContractDescriptorRow {
    /// Create a call-packet contract descriptor row.
    pub fn new(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Escaped key for line-oriented `key=value` descriptor output.
    pub fn escaped_key(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented `key=value` descriptor output.
    pub fn escaped_value(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

/// Validation status for call-packet contract descriptor health reports.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PetriNativeSuccessorCallPacketContractHealthStatus {
    /// Descriptor rows exactly match Trust Codegen's authoritative call-packet contract.
    Healthy,
    /// Descriptor rows are malformed, stale, incomplete, or mismatched.
    FailClosed,
}

impl PetriNativeSuccessorCallPacketContractHealthStatus {
    /// Return the stable health status code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Healthy => "healthy",
            Self::FailClosed => "fail_closed",
        }
    }
}

/// Fail-closed health report for Petri call-packet contract descriptor rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorCallPacketContractHealthReport {
    /// Health report schema.
    pub schema: &'static str,
    /// Health report schema version.
    pub schema_version: u32,
    /// Healthy only when descriptor rows exactly match Trust Codegen-owned metadata.
    pub status: PetriNativeSuccessorCallPacketContractHealthStatus,
    /// Stable reason code for fail-closed validation.
    pub reason_code: Option<String>,
    /// Observed descriptor id, when present.
    pub descriptor_id: Option<String>,
    /// Observed descriptor schema, when present.
    pub descriptor_schema: Option<String>,
    /// Observed descriptor schema version, when present.
    pub descriptor_schema_version: Option<String>,
    /// Observed descriptor status, when present.
    pub descriptor_status: Option<String>,
    /// Number of rows Trust Codegen expects for the authoritative descriptor.
    pub expected_row_count: usize,
    /// Number of rows observed before duplicate collapsing, including malformed lines.
    pub observed_row_count: usize,
    /// Required descriptor row keys that were absent.
    pub missing_keys: Vec<String>,
    /// Duplicate descriptor row keys.
    pub duplicate_keys: Vec<String>,
    /// Schema/version keys whose values are stale.
    pub stale_schema_keys: Vec<String>,
    /// Required-field keys whose values no longer match Trust Codegen's contract.
    pub mismatched_required_field_keys: Vec<String>,
    /// Non-required-field descriptor keys whose values no longer match Trust Codegen's contract.
    pub mismatched_keys: Vec<String>,
    /// Unexpected descriptor row keys.
    pub unexpected_keys: Vec<String>,
    /// Number of malformed `key=value` lines seen by the line validator.
    pub invalid_key_value_line_count: usize,
}

impl PetriNativeSuccessorCallPacketContractHealthReport {
    /// Return true only when descriptor rows exactly match Trust Codegen's call-packet contract.
    pub fn is_healthy(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorCallPacketContractHealthStatus::Healthy
        ) && self.reason_code.is_none()
            && self.missing_keys.is_empty()
            && self.duplicate_keys.is_empty()
            && self.stale_schema_keys.is_empty()
            && self.mismatched_required_field_keys.is_empty()
            && self.mismatched_keys.is_empty()
            && self.unexpected_keys.is_empty()
            && self.invalid_key_value_line_count == 0
            && self.expected_row_count == self.observed_row_count
    }

    /// Return true when descriptor health validation failed closed.
    pub fn is_fail_closed(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorCallPacketContractHealthStatus::FailClosed
        )
    }

    /// Return the number of diagnostic categories populated by validation.
    pub fn diagnostic_count(&self) -> usize {
        self.invalid_key_value_line_count
            + self.missing_keys.len()
            + self.duplicate_keys.len()
            + self.stale_schema_keys.len()
            + self.mismatched_required_field_keys.len()
            + self.mismatched_keys.len()
            + self.unexpected_keys.len()
    }

    /// Return a compact summary suitable for sidecar persistence beside full rows.
    pub fn compact_summary(&self) -> PetriNativeSuccessorCallPacketContractHealthSummary {
        PetriNativeSuccessorCallPacketContractHealthSummary::from_health_report(self)
    }

    /// Emit deterministic key/value health report rows for downstream consumers.
    pub fn manifest_rows(&self) -> Vec<PetriNativeSuccessorCallPacketContractDescriptorRow> {
        let mut rows = vec![
            PetriNativeSuccessorCallPacketContractDescriptorRow::new("health.schema", self.schema),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "health.schema_version",
                self.schema_version.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "health.status",
                self.status.as_str(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "health.reason_code",
                self.reason_code.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.id",
                self.descriptor_id.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.schema",
                self.descriptor_schema.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.schema_version",
                self.descriptor_schema_version.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.status",
                self.descriptor_status.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "health.expected_row_count",
                self.expected_row_count.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "health.observed_row_count",
                self.observed_row_count.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "health.diagnostic_count",
                self.diagnostic_count().to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "health.invalid_key_value_line_count",
                self.invalid_key_value_line_count.to_string(),
            ),
        ];
        push_call_packet_contract_health_list_rows(
            &mut rows,
            PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_MISSING_KEY_PREFIX,
            &self.missing_keys,
        );
        push_call_packet_contract_health_list_rows(
            &mut rows,
            PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_DUPLICATE_KEY_PREFIX,
            &self.duplicate_keys,
        );
        push_call_packet_contract_health_list_rows(
            &mut rows,
            PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_STALE_SCHEMA_KEY_PREFIX,
            &self.stale_schema_keys,
        );
        push_call_packet_contract_health_list_rows(
            &mut rows,
            PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_MISMATCHED_REQUIRED_FIELD_KEY_PREFIX,
            &self.mismatched_required_field_keys,
        );
        push_call_packet_contract_health_list_rows(
            &mut rows,
            PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_MISMATCHED_KEY_PREFIX,
            &self.mismatched_keys,
        );
        push_call_packet_contract_health_list_rows(
            &mut rows,
            PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_UNEXPECTED_KEY_PREFIX,
            &self.unexpected_keys,
        );
        rows
    }

    /// Emit stable escaped `key=value` health report lines in [`Self::manifest_rows`] order.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .iter()
            .map(PetriNativeSuccessorCallPacketContractDescriptorRow::to_key_value_line)
            .collect()
    }
}

/// Compact sidecar summary for Petri call-packet contract health reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorCallPacketContractHealthSummary {
    /// Summary schema.
    pub schema: &'static str,
    /// Summary schema version.
    pub schema_version: u32,
    /// Descriptor id observed in the source health report.
    pub descriptor_id: Option<String>,
    /// Descriptor schema observed in the source health report.
    pub descriptor_schema: Option<String>,
    /// Descriptor schema version observed in the source health report.
    pub descriptor_schema_version: Option<String>,
    /// Descriptor status observed in the source health report.
    pub descriptor_status: Option<String>,
    /// Health status copied from the source health report.
    pub health_status: PetriNativeSuccessorCallPacketContractHealthStatus,
    /// Health reason code copied from the source health report.
    pub reason_code: Option<String>,
    /// True whenever the health gate did not accept the descriptor as healthy.
    pub fail_closed: bool,
    /// Number of rows Trust Codegen expected for the authoritative descriptor.
    pub expected_row_count: usize,
    /// Number of source rows observed, including malformed lines.
    pub observed_row_count: usize,
    /// Number of populated diagnostics in the source health report.
    pub diagnostic_count: usize,
    /// Stable digest of [`Self::canonical_text`].
    pub summary_sha256: String,
}

impl PetriNativeSuccessorCallPacketContractHealthSummary {
    /// Build a compact summary from a full Trust Codegen-owned health report.
    pub fn from_health_report(report: &PetriNativeSuccessorCallPacketContractHealthReport) -> Self {
        let mut summary = Self {
            schema: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_SCHEMA,
            schema_version:
                PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_SCHEMA_VERSION,
            descriptor_id: report.descriptor_id.clone(),
            descriptor_schema: report.descriptor_schema.clone(),
            descriptor_schema_version: report.descriptor_schema_version.clone(),
            descriptor_status: report.descriptor_status.clone(),
            health_status: report.status,
            reason_code: report.reason_code.clone(),
            fail_closed: report.is_fail_closed(),
            expected_row_count: report.expected_row_count,
            observed_row_count: report.observed_row_count,
            diagnostic_count: report.diagnostic_count(),
            summary_sha256: String::new(),
        };
        summary.summary_sha256 =
            format!("sha256:{}", sha256_hex(summary.canonical_text().as_bytes()));
        summary
    }

    /// Return stable summary text excluding the digest row itself.
    pub fn canonical_text(&self) -> String {
        let mut out = String::new();
        for row in self.manifest_rows_without_digest() {
            out.push_str(&row.to_key_value_line());
            out.push('\n');
        }
        out
    }

    /// Emit a compact line-oriented summary including its stable digest.
    pub fn summary_text(&self) -> String {
        let mut out = self.canonical_text();
        out.push_str(
            &PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "summary.sha256",
                self.summary_sha256.as_str(),
            )
            .to_key_value_line(),
        );
        out.push('\n');
        out
    }

    /// Emit deterministic summary rows including the digest row.
    pub fn manifest_rows(&self) -> Vec<PetriNativeSuccessorCallPacketContractDescriptorRow> {
        let mut rows = self.manifest_rows_without_digest();
        rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
            "summary.sha256",
            self.summary_sha256.as_str(),
        ));
        rows
    }

    /// Emit stable escaped `key=value` summary lines in [`Self::manifest_rows`] order.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .iter()
            .map(PetriNativeSuccessorCallPacketContractDescriptorRow::to_key_value_line)
            .collect()
    }

    fn manifest_rows_without_digest(
        &self,
    ) -> Vec<PetriNativeSuccessorCallPacketContractDescriptorRow> {
        let mut rows = vec![
            PetriNativeSuccessorCallPacketContractDescriptorRow::new("summary.schema", self.schema),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "summary.schema_version",
                self.schema_version.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "health.schema",
                PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SCHEMA,
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "health.schema_version",
                PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SCHEMA_VERSION.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.id",
                self.descriptor_id.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.schema",
                self.descriptor_schema.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.schema_version",
                self.descriptor_schema_version.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "descriptor.status",
                self.descriptor_status.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "summary.status",
                self.health_status.as_str(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "summary.reason_code",
                self.reason_code.as_deref().unwrap_or(""),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "summary.fail_closed",
                self.fail_closed.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "summary.expected_row_count",
                self.expected_row_count.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "summary.observed_row_count",
                self.observed_row_count.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "summary.diagnostic_count",
                self.diagnostic_count.to_string(),
            ),
            PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                "summary.stable_reason_code_count",
                PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_REASON_CODES
                    .len()
                    .to_string(),
            ),
        ];
        for (index, code) in PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_REASON_CODES
            .iter()
            .copied()
            .enumerate()
        {
            rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
                format!("summary.stable_reason_code.{index}"),
                code,
            ));
        }
        rows
    }
}

/// Validation status for compact call-packet contract health summaries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PetriNativeSuccessorCallPacketContractHealthSummaryValidationStatus {
    /// Summary rows exactly match the Trust Codegen-owned source health report.
    Accepted,
    /// Summary rows are malformed, stale, incomplete, or mismatched.
    FailClosed,
}

impl PetriNativeSuccessorCallPacketContractHealthSummaryValidationStatus {
    /// Return the stable summary validation status code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::FailClosed => "fail_closed",
        }
    }
}

/// Fail-closed validation report for compact call-packet contract health summaries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorCallPacketContractHealthSummaryValidationReport {
    /// Summary validation schema.
    pub schema: &'static str,
    /// Summary validation schema version.
    pub schema_version: u32,
    /// Accepted only when summary rows match the source health report.
    pub status: PetriNativeSuccessorCallPacketContractHealthSummaryValidationStatus,
    /// Stable reason code for fail-closed validation.
    pub reason_code: Option<String>,
    /// Summary digest expected from the source health report.
    pub expected_summary_sha256: Option<String>,
    /// Summary digest observed in the summary rows.
    pub observed_summary_sha256: Option<String>,
    /// Required summary row keys that were absent.
    pub missing_keys: Vec<String>,
    /// Duplicate summary row keys.
    pub duplicate_keys: Vec<String>,
    /// Schema/version keys whose values are stale.
    pub stale_schema_keys: Vec<String>,
    /// Summary keys whose values no longer match the source health report.
    pub mismatched_keys: Vec<String>,
    /// Unexpected summary row keys.
    pub unexpected_keys: Vec<String>,
    /// Number of malformed `key=value` lines seen by the line validator.
    pub invalid_key_value_line_count: usize,
}

impl PetriNativeSuccessorCallPacketContractHealthSummaryValidationReport {
    /// Return true only when summary rows match the source health report.
    pub fn is_accepted(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorCallPacketContractHealthSummaryValidationStatus::Accepted
        ) && self.reason_code.is_none()
            && self.missing_keys.is_empty()
            && self.duplicate_keys.is_empty()
            && self.stale_schema_keys.is_empty()
            && self.mismatched_keys.is_empty()
            && self.unexpected_keys.is_empty()
            && self.invalid_key_value_line_count == 0
    }

    /// Return true when summary validation failed closed.
    pub fn is_fail_closed(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorCallPacketContractHealthSummaryValidationStatus::FailClosed
        )
    }
}

/// Compact route/source-authority descriptor for trust-mc-backed Petri native admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PetriNativeSuccessorTrustMcAdmissionRouteDescriptor {
    /// Route descriptor schema.
    pub schema: &'static str,
    /// Route descriptor schema version.
    pub schema_version: u32,
    /// Stable descriptor id.
    pub descriptor_id: &'static str,
    /// Stable route name.
    pub route_name: &'static str,
    /// Descriptor status code.
    pub status_code: &'static str,
    /// Whether this route relies on AY-owned solver/model acceptance.
    pub ay_backed: bool,
    /// Whether the route descriptor is safe to persist in production sidecars.
    pub production_safe: bool,
    /// Whether production acceptance must fail closed unless AY accepts the model.
    pub fail_closed_without_solver_acceptance: bool,
    /// Source authority for native bundle identity.
    pub native_bundle_identity_owner: &'static str,
    /// Source authority for Petri/trust-mc CHC contract metadata.
    pub trust_mc_chc_contract_owner: &'static str,
    /// Source authority for model acceptance.
    pub model_acceptance_owner: &'static str,
    /// Source authority for install-gate admission summaries.
    pub install_admission_owner: &'static str,
    /// Source authority for runtime execution summaries.
    pub execution_authority_owner: &'static str,
    /// trust_ir native bundle identity schema.
    pub trust_ir_native_bundle_identity_schema: &'static str,
    /// trust_ir native bundle identity schema version.
    pub trust_ir_native_bundle_identity_schema_version: u32,
    /// trust_ir Petri/trust-mc CHC contract schema.
    pub trust_ir_trust_mc_chc_contract_schema: &'static str,
    /// trust_ir Petri/trust-mc CHC contract schema version.
    pub trust_ir_trust_mc_chc_contract_schema_version: u32,
    /// trust_ir shared primitive contract schema.
    pub trust_ir_shared_primitive_contract_schema: &'static str,
    /// trust_ir shared primitive contract schema version.
    pub trust_ir_shared_primitive_contract_schema_version: u32,
    /// trust_ir readiness report schema used for solver-owned model validation.
    pub trust_ir_readiness_report_schema: &'static str,
    /// trust_ir readiness report schema version.
    pub trust_ir_readiness_report_schema_version: u32,
    /// AY/trust_ir model acceptance report API.
    pub model_acceptance_report_api_name: &'static str,
    /// Consumer acceptance API that must be called before production promotion.
    pub consumer_acceptance_api_name: &'static str,
    /// Solver suite that owns production acceptance.
    pub production_acceptance_owner_suite: trust_ir::NativeVerifierSuite,
    /// Whether production acceptance requires solver-owned acceptance.
    pub production_acceptance_requires_solver: bool,
    /// Whether production acceptance requires emitted solver artifacts.
    pub production_requires_emitted_solver_artifacts: bool,
    /// Trust Codegen native install-gate admission summary schema.
    pub admission_summary_schema: &'static str,
    /// Trust Codegen native install-gate admission summary schema version.
    pub admission_summary_schema_version: u32,
    /// Trust Codegen execution-authority decision schema.
    pub execution_authority_schema: &'static str,
    /// Trust Codegen execution-authority decision schema version.
    pub execution_authority_schema_version: u32,
    /// Trust Codegen compact execution-authority summary schema.
    pub execution_authority_summary_schema: &'static str,
    /// Trust Codegen compact execution-authority summary schema version.
    pub execution_authority_summary_schema_version: u32,
    /// Trust Codegen compact execution-authority summary validation schema.
    pub execution_authority_summary_validation_schema: &'static str,
    /// Trust Codegen compact execution-authority summary validation schema version.
    pub execution_authority_summary_validation_schema_version: u32,
    /// Required Trust Codegen summary helpers for downstream validation.
    pub required_summary_validators: &'static [&'static str],
}

impl PetriNativeSuccessorTrustMcAdmissionRouteDescriptor {
    /// Return true when this route descriptor identifies the AY-backed Petri admission route.
    pub const fn is_authoritative(&self) -> bool {
        self.ay_backed
            && self.production_safe
            && self.fail_closed_without_solver_acceptance
            && self.production_acceptance_requires_solver
            && self.production_requires_emitted_solver_artifacts
    }

    /// Return stable descriptor text excluding the digest row.
    pub fn canonical_text(&self) -> String {
        let mut out = String::new();
        for row in self.manifest_rows_without_digest() {
            out.push_str(&row.to_key_value_line());
            out.push('\n');
        }
        out
    }

    /// Return a stable digest over [`Self::canonical_text`].
    pub fn descriptor_sha256(&self) -> String {
        format!("sha256:{}", sha256_hex(self.canonical_text().as_bytes()))
    }

    /// Emit deterministic descriptor rows including the descriptor digest.
    pub fn manifest_rows(&self) -> Vec<PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow> {
        let mut rows = self.manifest_rows_without_digest();
        rows.push(PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
            "descriptor.sha256",
            self.descriptor_sha256(),
        ));
        rows
    }

    /// Emit stable escaped `key=value` descriptor lines.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .iter()
            .map(PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::to_key_value_line)
            .collect()
    }

    /// Emit a deterministic JSON object keyed by stable descriptor row names.
    pub fn to_json_value(&self) -> serde_json::Value {
        let mut object = serde_json::Map::new();
        for row in self.manifest_rows() {
            object.insert(row.key, serde_json::Value::String(row.value));
        }
        serde_json::Value::Object(object)
    }

    /// Emit deterministic compact JSON for downstream route-descriptor sidecars.
    pub fn to_json_string(&self) -> String {
        self.to_json_value().to_string()
    }

    fn manifest_rows_without_digest(
        &self,
    ) -> Vec<PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow> {
        let mut rows = vec![
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "descriptor.schema",
                self.schema,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "descriptor.schema_version",
                self.schema_version.to_string(),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "descriptor.id",
                self.descriptor_id,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "route.name",
                self.route_name,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "route.status",
                self.status_code,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "route.ay_backed",
                petri_native_successor_bool_code(self.ay_backed),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "route.production_safe",
                petri_native_successor_bool_code(self.production_safe),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "route.fail_closed_without_solver_acceptance",
                petri_native_successor_bool_code(self.fail_closed_without_solver_acceptance),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "source_authority.native_bundle_identity",
                self.native_bundle_identity_owner,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "source_authority.trust_mc_chc_contract",
                self.trust_mc_chc_contract_owner,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "source_authority.model_acceptance",
                self.model_acceptance_owner,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "source_authority.install_admission",
                self.install_admission_owner,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "source_authority.execution_authority",
                self.execution_authority_owner,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust_ir.native_bundle_identity.schema",
                self.trust_ir_native_bundle_identity_schema,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust_ir.native_bundle_identity.schema_version",
                self.trust_ir_native_bundle_identity_schema_version
                    .to_string(),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust_ir.trust_mc_chc.contract_schema",
                self.trust_ir_trust_mc_chc_contract_schema,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust_ir.trust_mc_chc.contract_schema_version",
                self.trust_ir_trust_mc_chc_contract_schema_version
                    .to_string(),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust_ir.shared_primitive.schema",
                self.trust_ir_shared_primitive_contract_schema,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust_ir.shared_primitive.schema_version",
                self.trust_ir_shared_primitive_contract_schema_version
                    .to_string(),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust_ir.readiness_report.schema",
                self.trust_ir_readiness_report_schema,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust_ir.readiness_report.schema_version",
                self.trust_ir_readiness_report_schema_version.to_string(),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "acceptance.model_report_api",
                self.model_acceptance_report_api_name,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "acceptance.consumer_api",
                self.consumer_acceptance_api_name,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "acceptance.owner_suite",
                self.production_acceptance_owner_suite.code(),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "acceptance.requires_solver",
                petri_native_successor_bool_code(self.production_acceptance_requires_solver),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "acceptance.requires_emitted_solver_artifacts",
                petri_native_successor_bool_code(self.production_requires_emitted_solver_artifacts),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust-cg.admission.summary_schema",
                self.admission_summary_schema,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust-cg.admission.summary_schema_version",
                self.admission_summary_schema_version.to_string(),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust-cg.execution_authority.schema",
                self.execution_authority_schema,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust-cg.execution_authority.schema_version",
                self.execution_authority_schema_version.to_string(),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust-cg.execution_authority.summary_schema",
                self.execution_authority_summary_schema,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust-cg.execution_authority.summary_schema_version",
                self.execution_authority_summary_schema_version.to_string(),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust-cg.execution_authority.summary_validation_schema",
                self.execution_authority_summary_validation_schema,
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "trust-cg.execution_authority.summary_validation_schema_version",
                self.execution_authority_summary_validation_schema_version
                    .to_string(),
            ),
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                "validator.count",
                self.required_summary_validators.len().to_string(),
            ),
        ];
        for (index, validator) in self.required_summary_validators.iter().enumerate() {
            rows.push(PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow::new(
                format!("validator.{index}.api"),
                *validator,
            ));
        }
        rows
    }
}

/// Stable key/value row for trust-mc-backed Petri native admission route descriptors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow {
    /// Descriptor row key.
    pub key: String,
    /// Descriptor row value.
    pub value: String,
}

impl PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow {
    /// Create a trust-mc admission route descriptor row.
    pub fn new(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Escaped key for line-oriented `key=value` descriptor output.
    pub fn escaped_key(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented `key=value` descriptor output.
    pub fn escaped_value(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

/// Validation status for compact trust-mc admission route descriptors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationStatus {
    /// Descriptor rows exactly match Trust Codegen's route/source-authority descriptor.
    Accepted,
    /// Descriptor rows are malformed, stale, incomplete, or mismatched.
    FailClosed,
}

impl PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationStatus {
    /// Return the stable route descriptor validation status code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::FailClosed => "fail_closed",
        }
    }
}

/// Fail-closed validation report for compact trust-mc admission route descriptors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationReport {
    /// Route descriptor validation schema.
    pub schema: &'static str,
    /// Route descriptor validation schema version.
    pub schema_version: u32,
    /// Accepted only when descriptor rows match Trust Codegen's source route descriptor.
    pub status: PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationStatus,
    /// Stable reason code for fail-closed validation.
    pub reason_code: Option<String>,
    /// Descriptor digest expected from Trust Codegen's source descriptor.
    pub expected_descriptor_sha256: Option<String>,
    /// Descriptor digest observed in persisted descriptor rows.
    pub observed_descriptor_sha256: Option<String>,
    /// Required descriptor row keys that were absent.
    pub missing_keys: Vec<String>,
    /// Duplicate descriptor row keys.
    pub duplicate_keys: Vec<String>,
    /// Schema/version keys whose values are stale.
    pub stale_schema_keys: Vec<String>,
    /// Descriptor keys whose values no longer match Trust Codegen's source descriptor.
    pub mismatched_keys: Vec<String>,
    /// Unexpected descriptor row keys.
    pub unexpected_keys: Vec<String>,
    /// Number of malformed `key=value` lines seen by the line validator.
    pub invalid_key_value_line_count: usize,
}

impl PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationReport {
    /// Return true only when descriptor rows match Trust Codegen's source descriptor.
    pub fn is_accepted(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationStatus::Accepted
        ) && self.reason_code.is_none()
            && self.missing_keys.is_empty()
            && self.duplicate_keys.is_empty()
            && self.stale_schema_keys.is_empty()
            && self.mismatched_keys.is_empty()
            && self.unexpected_keys.is_empty()
            && self.invalid_key_value_line_count == 0
    }

    /// Return true when route descriptor validation failed closed.
    pub fn is_fail_closed(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationStatus::FailClosed
        )
    }
}

/// Trust Codegen-owned producer bridge descriptor for shared Petri native/JIT primitives.
///
/// This gives TY/MCC/AY a single stable descriptor to re-export when they
/// need to explain which upstream owns each promotion fact. It deliberately
/// points to existing trust_ir/AY/Trust Codegen surfaces instead of re-stating solver logic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PetriNativeSuccessorProducerBridgeDescriptor {
    /// Descriptor schema.
    pub schema: &'static str,
    /// Descriptor schema version.
    pub schema_version: u32,
    /// Stable descriptor id.
    pub descriptor_id: &'static str,
    /// Stable descriptor status.
    pub status_code: &'static str,
    /// Whether this descriptor can be persisted in production sidecars.
    pub production_safe: bool,
    /// Whether production must fail closed without solver-owned acceptance.
    pub fail_closed_without_solver_acceptance: bool,
    /// Whether this bridge alone authorizes runtime execution.
    pub authorizes_runtime_execution_without_authority: bool,
    /// trust_ir owns native bundle identity and Petri/trust-mc request metadata.
    pub native_bundle_identity_owner: &'static str,
    /// trust_ir owns the Petri/trust-mc CHC contract metadata.
    pub trust_mc_chc_contract_owner: &'static str,
    /// AY owns solver/model acceptance.
    pub model_acceptance_owner: &'static str,
    /// Trust Codegen owns install-gate admission summaries.
    pub install_admission_owner: &'static str,
    /// Trust Codegen owns compile artifact handoff facts.
    pub compile_artifact_handoff_owner: &'static str,
    /// Trust Codegen owns call-packet descriptor and packet binding facts.
    pub call_packet_owner: &'static str,
    /// Trust Codegen owns runtime readiness packet facts.
    pub runtime_readiness_owner: &'static str,
    /// Trust Codegen owns execution-authority decisions and summaries.
    pub execution_authority_owner: &'static str,
    /// Downstream contract schema covered by this bridge.
    pub downstream_contract_schema: &'static str,
    /// Downstream contract schema version covered by this bridge.
    pub downstream_contract_schema_version: u32,
    /// trust-mc admission route descriptor id covered by this bridge.
    pub trust_mc_admission_route_descriptor_id: &'static str,
    /// trust-mc admission route descriptor schema covered by this bridge.
    pub trust_mc_admission_route_descriptor_schema: &'static str,
    /// trust-mc admission route descriptor schema version covered by this bridge.
    pub trust_mc_admission_route_descriptor_schema_version: u32,
    /// Call-packet contract descriptor id covered by this bridge.
    pub call_packet_contract_descriptor_id: &'static str,
    /// Call-packet contract descriptor schema covered by this bridge.
    pub call_packet_contract_descriptor_schema: &'static str,
    /// Call-packet contract descriptor schema version covered by this bridge.
    pub call_packet_contract_descriptor_schema_version: u32,
    /// Compile artifact handoff evidence schema.
    pub compile_artifact_handoff_schema: &'static str,
    /// Compile artifact handoff evidence schema version.
    pub compile_artifact_handoff_schema_version: u32,
    /// Runtime readiness packet schema.
    pub runtime_readiness_schema: &'static str,
    /// Runtime readiness packet schema version.
    pub runtime_readiness_schema_version: u32,
    /// Execution-authority decision schema.
    pub execution_authority_schema: &'static str,
    /// Execution-authority decision schema version.
    pub execution_authority_schema_version: u32,
    /// Compact execution-authority summary schema.
    pub execution_authority_summary_schema: &'static str,
    /// Compact execution-authority summary schema version.
    pub execution_authority_summary_schema_version: u32,
    /// Compact execution-authority summary validation schema.
    pub execution_authority_summary_validation_schema: &'static str,
    /// Compact execution-authority summary validation schema version.
    pub execution_authority_summary_validation_schema_version: u32,
    /// Runtime-call evidence schema.
    pub runtime_call_schema: &'static str,
    /// Runtime-call evidence schema version.
    pub runtime_call_schema_version: u32,
    /// Required route descriptor validator APIs downstreams should reuse.
    pub required_route_validators: &'static [&'static str],
    /// Required execution-authority summary validator APIs downstreams should reuse.
    pub required_authority_summary_validators: &'static [&'static str],
}

impl PetriNativeSuccessorProducerBridgeDescriptor {
    /// Return true only when this descriptor represents the current fail-closed producer bridge.
    pub const fn is_authoritative(&self) -> bool {
        self.production_safe
            && self.fail_closed_without_solver_acceptance
            && !self.authorizes_runtime_execution_without_authority
    }

    /// Return stable descriptor text excluding the digest row.
    pub fn canonical_text(&self) -> String {
        let mut out = String::new();
        for row in self.manifest_rows_without_digest() {
            out.push_str(&row.to_key_value_line());
            out.push('\n');
        }
        out
    }

    /// Return a stable digest over [`Self::canonical_text`].
    pub fn descriptor_sha256(&self) -> String {
        format!("sha256:{}", sha256_hex(self.canonical_text().as_bytes()))
    }

    /// Emit deterministic producer bridge descriptor rows including the descriptor digest.
    pub fn manifest_rows(&self) -> Vec<PetriNativeSuccessorProducerBridgeDescriptorRow> {
        let mut rows = self.manifest_rows_without_digest();
        rows.push(PetriNativeSuccessorProducerBridgeDescriptorRow::new(
            "descriptor.sha256",
            self.descriptor_sha256(),
        ));
        rows
    }

    /// Emit stable escaped `key=value` descriptor lines.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .iter()
            .map(PetriNativeSuccessorProducerBridgeDescriptorRow::to_key_value_line)
            .collect()
    }

    fn manifest_rows_without_digest(&self) -> Vec<PetriNativeSuccessorProducerBridgeDescriptorRow> {
        let mut rows = vec![
            PetriNativeSuccessorProducerBridgeDescriptorRow::new("descriptor.schema", self.schema),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "descriptor.schema_version",
                self.schema_version.to_string(),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "descriptor.id",
                self.descriptor_id,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "descriptor.status",
                self.status_code,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "descriptor.production_safe",
                petri_native_successor_bool_code(self.production_safe),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "descriptor.fail_closed_without_solver_acceptance",
                petri_native_successor_bool_code(self.fail_closed_without_solver_acceptance),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "descriptor.authorizes_runtime_execution_without_authority",
                petri_native_successor_bool_code(
                    self.authorizes_runtime_execution_without_authority,
                ),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "source_authority.native_bundle_identity",
                self.native_bundle_identity_owner,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "source_authority.trust_mc_chc_contract",
                self.trust_mc_chc_contract_owner,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "source_authority.model_acceptance",
                self.model_acceptance_owner,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "source_authority.install_admission",
                self.install_admission_owner,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "source_authority.compile_artifact_handoff",
                self.compile_artifact_handoff_owner,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "source_authority.call_packet",
                self.call_packet_owner,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "source_authority.runtime_readiness",
                self.runtime_readiness_owner,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "source_authority.execution_authority",
                self.execution_authority_owner,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "downstream_contract.schema",
                self.downstream_contract_schema,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "downstream_contract.schema_version",
                self.downstream_contract_schema_version.to_string(),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "trust_mc_admission_route.descriptor_id",
                self.trust_mc_admission_route_descriptor_id,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "trust_mc_admission_route.schema",
                self.trust_mc_admission_route_descriptor_schema,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "trust_mc_admission_route.schema_version",
                self.trust_mc_admission_route_descriptor_schema_version
                    .to_string(),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "call_packet_contract.descriptor_id",
                self.call_packet_contract_descriptor_id,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "call_packet_contract.schema",
                self.call_packet_contract_descriptor_schema,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "call_packet_contract.schema_version",
                self.call_packet_contract_descriptor_schema_version
                    .to_string(),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "compile_artifact_handoff.schema",
                self.compile_artifact_handoff_schema,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "compile_artifact_handoff.schema_version",
                self.compile_artifact_handoff_schema_version.to_string(),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "runtime_readiness.schema",
                self.runtime_readiness_schema,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "runtime_readiness.schema_version",
                self.runtime_readiness_schema_version.to_string(),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "execution_authority.schema",
                self.execution_authority_schema,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "execution_authority.schema_version",
                self.execution_authority_schema_version.to_string(),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "execution_authority.summary_schema",
                self.execution_authority_summary_schema,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "execution_authority.summary_schema_version",
                self.execution_authority_summary_schema_version.to_string(),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "execution_authority.summary_validation_schema",
                self.execution_authority_summary_validation_schema,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "execution_authority.summary_validation_schema_version",
                self.execution_authority_summary_validation_schema_version
                    .to_string(),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "runtime_call.schema",
                self.runtime_call_schema,
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "runtime_call.schema_version",
                self.runtime_call_schema_version.to_string(),
            ),
            PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                "route_validator.count",
                self.required_route_validators.len().to_string(),
            ),
        ];
        for (index, validator) in self.required_route_validators.iter().enumerate() {
            rows.push(PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                format!("route_validator.{index}.api"),
                *validator,
            ));
        }
        rows.push(PetriNativeSuccessorProducerBridgeDescriptorRow::new(
            "authority_summary_validator.count",
            self.required_authority_summary_validators.len().to_string(),
        ));
        for (index, validator) in self
            .required_authority_summary_validators
            .iter()
            .enumerate()
        {
            rows.push(PetriNativeSuccessorProducerBridgeDescriptorRow::new(
                format!("authority_summary_validator.{index}.api"),
                *validator,
            ));
        }
        rows
    }
}

/// Stable key/value row for Petri native producer bridge descriptors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorProducerBridgeDescriptorRow {
    /// Descriptor row key.
    pub key: String,
    /// Descriptor row value.
    pub value: String,
}

impl PetriNativeSuccessorProducerBridgeDescriptorRow {
    /// Create a producer bridge descriptor row.
    pub fn new(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Escaped key for line-oriented `key=value` descriptor output.
    pub fn escaped_key(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented `key=value` descriptor output.
    pub fn escaped_value(&self) -> String {
        escape_petri_native_successor_handoff_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

/// Validation status for compact Petri native producer bridge descriptors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PetriNativeSuccessorProducerBridgeDescriptorValidationStatus {
    /// Descriptor rows exactly match Trust Codegen's producer bridge descriptor.
    Accepted,
    /// Descriptor rows are malformed, stale, incomplete, or mismatched.
    FailClosed,
}

impl PetriNativeSuccessorProducerBridgeDescriptorValidationStatus {
    /// Return the stable producer bridge validation status code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::FailClosed => "fail_closed",
        }
    }
}

/// Fail-closed validation report for Petri native producer bridge descriptors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeSuccessorProducerBridgeDescriptorValidationReport {
    /// Producer bridge descriptor validation schema.
    pub schema: &'static str,
    /// Producer bridge descriptor validation schema version.
    pub schema_version: u32,
    /// Accepted only when descriptor rows match Trust Codegen's source descriptor.
    pub status: PetriNativeSuccessorProducerBridgeDescriptorValidationStatus,
    /// Stable reason code for fail-closed validation.
    pub reason_code: Option<String>,
    /// Descriptor digest expected from Trust Codegen's source descriptor.
    pub expected_descriptor_sha256: Option<String>,
    /// Descriptor digest observed in persisted descriptor rows.
    pub observed_descriptor_sha256: Option<String>,
    /// Required descriptor row keys that were absent.
    pub missing_keys: Vec<String>,
    /// Duplicate descriptor row keys.
    pub duplicate_keys: Vec<String>,
    /// Schema/version keys whose values are stale.
    pub stale_schema_keys: Vec<String>,
    /// Descriptor keys whose values no longer match Trust Codegen's source descriptor.
    pub mismatched_keys: Vec<String>,
    /// Unexpected descriptor row keys.
    pub unexpected_keys: Vec<String>,
    /// Number of malformed `key=value` lines seen by the line validator.
    pub invalid_key_value_line_count: usize,
}

impl PetriNativeSuccessorProducerBridgeDescriptorValidationReport {
    /// Return true only when descriptor rows match Trust Codegen's source descriptor.
    pub fn is_accepted(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorProducerBridgeDescriptorValidationStatus::Accepted
        ) && self.reason_code.is_none()
            && self.missing_keys.is_empty()
            && self.duplicate_keys.is_empty()
            && self.stale_schema_keys.is_empty()
            && self.mismatched_keys.is_empty()
            && self.unexpected_keys.is_empty()
            && self.invalid_key_value_line_count == 0
    }

    /// Return true when producer bridge validation failed closed.
    pub fn is_fail_closed(&self) -> bool {
        matches!(
            self.status,
            PetriNativeSuccessorProducerBridgeDescriptorValidationStatus::FailClosed
        )
    }
}

/// Downstream TY/MCC contract descriptor for Petri native successor evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PetriNativeSuccessorDownstreamContractDescriptor {
    /// Descriptor schema.
    pub schema: &'static str,
    /// Descriptor schema version.
    pub schema_version: u32,
    /// trust_ir-owned native bundle identity contract consumed by the Trust Codegen Petri handoff.
    pub trust_ir_native_bundle_identity: trust_ir::NativeBundleIdentityContractDescriptor,
    /// trust_ir-owned Petri/trust-mc CHC report contract consumed by the Trust Codegen Petri handoff.
    pub trust_ir_petri_trust_mc_chc_contract: trust_ir::PetriSuccessorTrustMcChcContractDescriptor,
    /// trust_ir-owned shared primitive contract for Petri/trust-mc production acceptance.
    pub trust_ir_petri_trust_mc_chc_shared_primitive_contract:
        trust_ir::NativeSharedPrimitiveContractDescriptor,
    /// Compact trust-mc-backed route/source-authority descriptor for Petri admission.
    pub trust_mc_admission_route: PetriNativeSuccessorTrustMcAdmissionRouteDescriptor,
    /// Trust Codegen-owned producer bridge descriptor tying Petri native surfaces together.
    pub producer_bridge: PetriNativeSuccessorProducerBridgeDescriptor,
    /// Petri install-gate admission summary surface descriptor.
    pub install_gate_admission: PetriNativeSuccessorEvidenceSurfaceDescriptor,
    /// Petri native successor execution plan surface descriptor.
    pub execution_plan: PetriNativeSuccessorEvidenceSurfaceDescriptor,
    /// Petri native successor call-packet surface descriptor.
    pub call_packet: PetriNativeSuccessorCallPacketContractDescriptor,
    /// Semantic successor bridge evidence surface descriptor.
    pub semantic_bridge: PetriNativeSuccessorEvidenceSurfaceDescriptor,
    /// Native compile-artifact handoff evidence surface descriptor.
    pub compile_artifact_handoff: PetriNativeSuccessorEvidenceSurfaceDescriptor,
    /// Petri install/trampoline binding evidence surface descriptor.
    pub install_binding: PetriNativeSuccessorEvidenceSurfaceDescriptor,
    /// Runtime readiness evidence surface descriptor.
    pub runtime_readiness: PetriNativeSuccessorEvidenceSurfaceDescriptor,
    /// Execution authority decision surface descriptor.
    pub execution_authority: PetriNativeSuccessorEvidenceSurfaceDescriptor,
    /// Real runtime callable invocation surface descriptor.
    pub runtime_call: PetriNativeSuccessorEvidenceSurfaceDescriptor,
    /// Mock executable-call dry-run evidence surface descriptor.
    pub mock_executable_call: PetriNativeSuccessorEvidenceSurfaceDescriptor,
}

/// Native compile-artifact handoff evidence surface descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_DESCRIPTOR:
    PetriNativeSuccessorEvidenceSurfaceDescriptor = PetriNativeSuccessorEvidenceSurfaceDescriptor {
    name: "petri_native_successor_compile_artifact_handoff",
    schema: PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA,
    schema_version: PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA_VERSION,
    required_fields: PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_REQUIRED_FIELDS,
    status_codes: PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_STATUS_CODES,
    blocker_codes: PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_BLOCKER_CODES,
    shared_primitive_contract: None,
};

/// Petri install-gate admission summary surface descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_DESCRIPTOR:
    PetriNativeSuccessorEvidenceSurfaceDescriptor = PetriNativeSuccessorEvidenceSurfaceDescriptor {
    name: "petri_native_successor_install_gate_admission",
    schema: NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA,
    schema_version: NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA_VERSION,
    required_fields: PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_REQUIRED_FIELDS,
    status_codes: PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_STATUS_CODES,
    blocker_codes: PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_BLOCKER_CODES,
    shared_primitive_contract: Some(
        PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR,
    ),
};

/// Petri native successor execution plan surface descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_DESCRIPTOR:
    PetriNativeSuccessorEvidenceSurfaceDescriptor = PetriNativeSuccessorEvidenceSurfaceDescriptor {
    name: "petri_native_successor_execution_plan",
    schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_SCHEMA,
    schema_version: PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_SCHEMA_VERSION,
    required_fields: PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_REQUIRED_FIELDS,
    status_codes: PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_STATUS_CODES,
    blocker_codes: PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_BLOCKER_CODES,
    shared_primitive_contract: Some(
        PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR,
    ),
};

/// Petri native successor call-packet descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR:
    PetriNativeSuccessorCallPacketContractDescriptor =
    PetriNativeSuccessorCallPacketContractDescriptor {
        schema: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_SCHEMA_VERSION,
        descriptor_id: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_ID,
        status_code: "authoritative",
        production_status_code: "runtime_readiness_required",
        surface_name: "petri_native_successor_call_packet",
        evidence_schema: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA,
        evidence_schema_version: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA_VERSION,
        required_fields: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_REQUIRED_FIELDS,
        status_codes: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_STATUS_CODES,
        blocker_codes: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_BLOCKER_CODES,
        required_runtime_evidence: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_REQUIRED_RUNTIME_EVIDENCE,
        authoritative: true,
        upstream_pending: false,
        production_safe: true,
        authorizes_runtime_execution: false,
        production_runtime_gate_required: true,
        shared_primitive_contract: Some(
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR,
        ),
    };

/// Compact trust-mc-backed admission route/source-authority descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR:
    PetriNativeSuccessorTrustMcAdmissionRouteDescriptor =
    PetriNativeSuccessorTrustMcAdmissionRouteDescriptor {
        schema: PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_SCHEMA_VERSION,
        descriptor_id: PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_ID,
        route_name: "petri_native_successor_trust_mc_chc_admission",
        status_code: "authoritative",
        ay_backed: true,
        production_safe: true,
        fail_closed_without_solver_acceptance: true,
        native_bundle_identity_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_IR,
        trust_mc_chc_contract_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_IR,
        model_acceptance_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_AY,
        install_admission_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_CG,
        execution_authority_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_CG,
        trust_ir_native_bundle_identity_schema: trust_ir::NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA,
        trust_ir_native_bundle_identity_schema_version:
            trust_ir::NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA_VERSION,
        trust_ir_trust_mc_chc_contract_schema:
            trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA,
        trust_ir_trust_mc_chc_contract_schema_version:
            trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA_VERSION,
        trust_ir_shared_primitive_contract_schema:
            trust_ir::NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA,
        trust_ir_shared_primitive_contract_schema_version:
            trust_ir::NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA_VERSION,
        trust_ir_readiness_report_schema:
            trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA,
        trust_ir_readiness_report_schema_version:
            trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA_VERSION,
        model_acceptance_report_api_name:
            trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME,
        consumer_acceptance_api_name:
            trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME,
        production_acceptance_owner_suite:
            trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OWNER_SUITE,
        production_acceptance_requires_solver:
            trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_REQUIRES_SOLVER_ACCEPTANCE,
        production_requires_emitted_solver_artifacts:
            trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_REQUIRES_EMITTED_SOLVER_ARTIFACTS,
        admission_summary_schema: NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA,
        admission_summary_schema_version: NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA_VERSION,
        execution_authority_schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA,
        execution_authority_schema_version:
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA_VERSION,
        execution_authority_summary_schema:
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_SCHEMA,
        execution_authority_summary_schema_version:
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_SCHEMA_VERSION,
        execution_authority_summary_validation_schema:
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_VALIDATION_SCHEMA,
        execution_authority_summary_validation_schema_version:
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_VALIDATION_SCHEMA_VERSION,
        required_summary_validators:
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_REQUIRED_SUMMARY_VALIDATORS,
    };

/// Trust Codegen producer bridge descriptor for Petri native shared primitives.
pub const PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR:
    PetriNativeSuccessorProducerBridgeDescriptor = PetriNativeSuccessorProducerBridgeDescriptor {
    schema: PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_SCHEMA,
    schema_version: PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_SCHEMA_VERSION,
    descriptor_id: PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_ID,
    status_code: "authoritative",
    production_safe: true,
    fail_closed_without_solver_acceptance: true,
    authorizes_runtime_execution_without_authority: false,
    native_bundle_identity_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_IR,
    trust_mc_chc_contract_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_IR,
    model_acceptance_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_AY,
    install_admission_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_CG,
    compile_artifact_handoff_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_CG,
    call_packet_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_CG,
    runtime_readiness_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_CG,
    execution_authority_owner: PETRI_NATIVE_SUCCESSOR_SOURCE_AUTHORITY_TRUST_CG,
    downstream_contract_schema: PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_SCHEMA,
    downstream_contract_schema_version: PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_SCHEMA_VERSION,
    trust_mc_admission_route_descriptor_id:
        PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_ID,
    trust_mc_admission_route_descriptor_schema:
        PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_SCHEMA,
    trust_mc_admission_route_descriptor_schema_version:
        PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_SCHEMA_VERSION,
    call_packet_contract_descriptor_id: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_ID,
    call_packet_contract_descriptor_schema:
        PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_SCHEMA,
    call_packet_contract_descriptor_schema_version:
        PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR_SCHEMA_VERSION,
    compile_artifact_handoff_schema: PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA,
    compile_artifact_handoff_schema_version:
        PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA_VERSION,
    runtime_readiness_schema: PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA,
    runtime_readiness_schema_version:
        PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA_VERSION,
    execution_authority_schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA,
    execution_authority_schema_version: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA_VERSION,
    execution_authority_summary_schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_SCHEMA,
    execution_authority_summary_schema_version:
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_SCHEMA_VERSION,
    execution_authority_summary_validation_schema:
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_VALIDATION_SCHEMA,
    execution_authority_summary_validation_schema_version:
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_VALIDATION_SCHEMA_VERSION,
    runtime_call_schema: PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_SCHEMA,
    runtime_call_schema_version: PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_SCHEMA_VERSION,
    required_route_validators: PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_REQUIRED_ROUTE_VALIDATORS,
    required_authority_summary_validators:
        PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_REQUIRED_SUMMARY_VALIDATORS,
};

/// Petri install/trampoline binding evidence surface descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_DESCRIPTOR:
    PetriNativeSuccessorEvidenceSurfaceDescriptor = PetriNativeSuccessorEvidenceSurfaceDescriptor {
    name: "petri_native_successor_install_binding_evidence",
    schema: PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_EVIDENCE_SCHEMA,
    schema_version: PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_EVIDENCE_SCHEMA_VERSION,
    required_fields: PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_REQUIRED_FIELDS,
    status_codes: PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_STATUS_CODES,
    blocker_codes: PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_BLOCKER_CODES,
    shared_primitive_contract: Some(
        PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR,
    ),
};

/// Semantic bridge evidence surface descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_DESCRIPTOR:
    PetriNativeSuccessorEvidenceSurfaceDescriptor = PetriNativeSuccessorEvidenceSurfaceDescriptor {
    name: "petri_native_successor_semantic_bridge",
    schema: PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA,
    schema_version: PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA_VERSION,
    required_fields: PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_REQUIRED_FIELDS,
    status_codes: PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_STATUS_CODES,
    blocker_codes: PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_BLOCKER_CODES,
    shared_primitive_contract: None,
};

/// Runtime readiness evidence surface descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_DESCRIPTOR:
    PetriNativeSuccessorEvidenceSurfaceDescriptor = PetriNativeSuccessorEvidenceSurfaceDescriptor {
    name: "petri_native_successor_runtime_readiness_packet",
    schema: PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA,
    schema_version: PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA_VERSION,
    required_fields: PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_REQUIRED_FIELDS,
    status_codes: PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_STATUS_CODES,
    blocker_codes: PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_BLOCKER_CODES,
    shared_primitive_contract: None,
};

/// Execution authority decision surface descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DESCRIPTOR:
    PetriNativeSuccessorEvidenceSurfaceDescriptor = PetriNativeSuccessorEvidenceSurfaceDescriptor {
    name: "petri_native_successor_execution_authority",
    schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA,
    schema_version: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA_VERSION,
    required_fields: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REQUIRED_FIELDS,
    status_codes: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_STATUS_CODES,
    blocker_codes: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_BLOCKER_CODES,
    shared_primitive_contract: None,
};

/// Runtime callable invocation evidence surface descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_DESCRIPTOR:
    PetriNativeSuccessorEvidenceSurfaceDescriptor = PetriNativeSuccessorEvidenceSurfaceDescriptor {
    name: "petri_native_successor_call_runtime_entrypoint",
    schema: PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_SCHEMA,
    schema_version: PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_SCHEMA_VERSION,
    required_fields: PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_REQUIRED_FIELDS,
    status_codes: PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_STATUS_CODES,
    blocker_codes: PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_BLOCKER_CODES,
    shared_primitive_contract: None,
};

/// Mock executable-call dry-run evidence surface descriptor for downstream consumers.
pub const PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_DESCRIPTOR:
    PetriNativeSuccessorEvidenceSurfaceDescriptor = PetriNativeSuccessorEvidenceSurfaceDescriptor {
    name: "petri_native_successor_mock_executable_call_dry_run",
    schema: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA,
    schema_version: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA_VERSION,
    required_fields: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_REQUIRED_FIELDS,
    status_codes: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_STATUS_CODES,
    blocker_codes: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_BLOCKER_CODES,
    shared_primitive_contract: None,
};

/// Complete TY/MCC Petri native successor downstream evidence contract.
pub const PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_DESCRIPTOR:
    PetriNativeSuccessorDownstreamContractDescriptor =
    PetriNativeSuccessorDownstreamContractDescriptor {
        schema: PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_SCHEMA_VERSION,
        trust_ir_native_bundle_identity: PETRI_NATIVE_SUCCESSOR_TRUST_IR_BUNDLE_IDENTITY_DESCRIPTOR,
        trust_ir_petri_trust_mc_chc_contract:
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_CONTRACT_DESCRIPTOR,
        trust_ir_petri_trust_mc_chc_shared_primitive_contract:
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR,
        trust_mc_admission_route: PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR,
        producer_bridge: PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR,
        install_gate_admission: PETRI_NATIVE_SUCCESSOR_INSTALL_GATE_ADMISSION_DESCRIPTOR,
        execution_plan: PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_DESCRIPTOR,
        call_packet: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR,
        semantic_bridge: PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_DESCRIPTOR,
        compile_artifact_handoff: PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_DESCRIPTOR,
        install_binding: PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_DESCRIPTOR,
        runtime_readiness: PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_DESCRIPTOR,
        execution_authority: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DESCRIPTOR,
        runtime_call: PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_DESCRIPTOR,
        mock_executable_call: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_DESCRIPTOR,
    };

/// Return the trust_ir-owned native-bundle identity contract consumed by Petri native handoff.
pub const fn petri_native_successor_trust_ir_bundle_identity_descriptor()
-> trust_ir::NativeBundleIdentityContractDescriptor {
    PETRI_NATIVE_SUCCESSOR_TRUST_IR_BUNDLE_IDENTITY_DESCRIPTOR
}

/// Return the trust_ir-owned Petri/trust-mc CHC report contract consumed by Petri native handoff.
pub const fn petri_native_successor_trust_mc_chc_contract_descriptor()
-> trust_ir::PetriSuccessorTrustMcChcContractDescriptor {
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_CONTRACT_DESCRIPTOR
}

/// Return the trust_ir-owned Petri/trust-mc shared primitive contract consumed by Petri native handoff.
pub const fn petri_native_successor_trust_mc_chc_shared_primitive_contract_descriptor()
-> trust_ir::NativeSharedPrimitiveContractDescriptor {
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR
}

/// Return trust_ir-owned shared-primitive contract manifest lines for the Petri/trust-mc route.
pub fn petri_native_successor_trust_ir_shared_primitive_contract_manifest_key_value_lines()
-> Vec<String> {
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR
        .manifest_key_value_lines()
}

/// Return a stable digest over the trust_ir shared-primitive contract manifest lines.
pub fn petri_native_successor_trust_ir_shared_primitive_contract_manifest_sha256() -> String {
    let lines =
        petri_native_successor_trust_ir_shared_primitive_contract_manifest_key_value_lines();
    let mut text = lines.join("\n");
    text.push('\n');
    format!("sha256:{}", sha256_hex(text.as_bytes()))
}

/// Return the current trust_ir shared-primitive contract manifest row count.
pub fn petri_native_successor_trust_ir_shared_primitive_contract_manifest_row_count() -> usize {
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR
        .manifest_rows()
        .len()
}

/// Return the trust-mc admission route readiness identity digest used by production selection.
pub fn petri_native_successor_trust_mc_admission_route_readiness_identity_sha256() -> String {
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR.descriptor_sha256()
}

/// Return the compact trust-mc-backed route/source-authority descriptor for Petri admission.
pub const fn petri_native_successor_trust_mc_admission_route_descriptor()
-> PetriNativeSuccessorTrustMcAdmissionRouteDescriptor {
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR
}

/// Return the Trust Codegen-owned producer bridge descriptor for Petri native shared primitives.
pub const fn petri_native_successor_producer_bridge_descriptor()
-> PetriNativeSuccessorProducerBridgeDescriptor {
    PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR
}

/// Return the complete TY/MCC Petri native successor downstream evidence contract.
pub const fn petri_native_successor_downstream_contract_descriptor()
-> PetriNativeSuccessorDownstreamContractDescriptor {
    PETRI_NATIVE_SUCCESSOR_DOWNSTREAM_CONTRACT_DESCRIPTOR
}

/// Return the authoritative Petri native successor call-packet contract descriptor.
pub const fn petri_native_successor_call_packet_contract_descriptor()
-> PetriNativeSuccessorCallPacketContractDescriptor {
    PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_DESCRIPTOR
}

/// Evaluate whether trust_ir admits a Petri successor semantic bridge for this bundle.
///
/// This helper delegates semantic relation selection to trust_ir's typed
/// `NativeSemanticBridgeReport` instead of reconstructing Petri proof
/// obligation matching locally. Trust Codegen still keeps its downstream evidence row so
/// Petri/MCC callers get a stable fail-closed surface.
pub fn petri_native_successor_semantic_bridge_evidence_from_trust_ir_bundle(
    bundle: &trust_ir::NativeVerificationBundle,
    expected: PetriNativeSuccessorSemanticBridgeExpected<'_>,
) -> PetriNativeSuccessorSemanticBridgeEvidence {
    petri_native_successor_semantic_bridge_evidence_from_trust_ir_bundle_with_artifact_attachments(
        bundle,
        expected,
        &[],
    )
}

/// Evaluate Petri successor semantic evidence while forwarding trust_ir-owned
/// proof-admission and artifact authority rows.
pub fn petri_native_successor_semantic_bridge_evidence_from_trust_ir_bundle_with_artifact_attachments(
    bundle: &trust_ir::NativeVerificationBundle,
    expected: PetriNativeSuccessorSemanticBridgeExpected<'_>,
    artifact_attachments: &[trust_ir::NativeEvidenceArtifactAttachment],
) -> PetriNativeSuccessorSemanticBridgeEvidence {
    let identity = bundle.transport_identity();
    let transport_digest = identity.stable_digest().to_string();
    let bundle_digest = identity.bundle_digest.to_string();
    let trust_ir_module_digest = identity.trust_ir_module_digest.to_string();
    let target_abi_digest = identity
        .target_abi
        .as_ref()
        .map(|target| target.digest.to_string());
    let mut bundle_validated = false;
    let mut native_evidence_report_entries = 0_u64;
    let mut semantic_obligation_count = 0_u64;
    let mut semantic_evidence_entry_count = 0_u64;
    let mut consumed_certificate_count = 0_u64;
    let mut artifact_count = 0_u64;
    let mut trust_ir_semantic_bridge_status_code = None;
    let mut trust_ir_semantic_bridge_reason_code = None;
    let mut trust_ir_semantic_bridge_evidence_status_code = None;
    let mut trust_ir_semantic_bridge_proof_identity_digest = None;
    let mut trust_ir_trust_mc_chc_binding_schema = None;
    let mut trust_ir_trust_mc_chc_binding_schema_version = None;
    let mut trust_ir_trust_mc_chc_binding_function_id = None;
    let mut trust_ir_trust_mc_chc_binding_status_code = None;
    let mut trust_ir_trust_mc_chc_binding_reason_code = None;
    let mut trust_ir_trust_mc_chc_binding_bound = None;
    let mut trust_ir_trust_mc_chc_binding_fail_closed = None;
    let mut trust_ir_trust_mc_chc_binding_request_id = None;
    let mut trust_ir_trust_mc_chc_binding_request_digest = None;
    let mut trust_ir_trust_mc_chc_binding_evidence_digest = None;
    let mut trust_ir_trust_mc_chc_binding_expected_evidence_digest = None;
    let mut trust_ir_trust_mc_chc_binding_horn_clause_artifact = None;
    let mut trust_ir_trust_mc_chc_binding_horn_clause_artifact_kind = None;
    let mut trust_ir_trust_mc_chc_binding_horn_clause_digest = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_schema = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_schema_version = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_function_id = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_status_code = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_reason_code = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_ready = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_fail_closed = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_proof_identity_digest = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_replay_engine = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_replay_invocation = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_replay_transcript_digest = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_kind = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_digest = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_model_artifact = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_model_artifact_kind = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_model_artifact_digest = None;
    let mut trust_ir_trust_mc_chc_proof_handoff_solver_identities = Vec::new();
    let mut trust_ir_trust_mc_chc_model_validation_schema = None;
    let mut trust_ir_trust_mc_chc_model_validation_schema_version = None;
    let mut trust_ir_trust_mc_chc_model_validation_function_id = None;
    let mut trust_ir_trust_mc_chc_model_validation_status_code = None;
    let mut trust_ir_trust_mc_chc_model_validation_reason_code = None;
    let mut trust_ir_trust_mc_chc_model_validation_ready_for_solver_validation = None;
    let mut trust_ir_trust_mc_chc_model_validation_fail_closed = None;
    let mut trust_ir_trust_mc_chc_model_validated = None;
    let mut trust_ir_trust_mc_chc_model_validation_model_artifact = None;
    let mut trust_ir_trust_mc_chc_model_validation_model_artifact_kind = None;
    let mut trust_ir_trust_mc_chc_model_validation_model_artifact_digest = None;
    let mut trust_ir_trust_mc_chc_model_validation_solver_identities = Vec::new();
    let mut trust_ir_semantic_bridge_proof_admission_schema = None;
    let mut trust_ir_semantic_bridge_proof_admission_schema_version = None;
    let mut trust_ir_semantic_bridge_proof_admission_function_id = None;
    let mut trust_ir_semantic_bridge_proof_admission_status_code = None;
    let mut trust_ir_semantic_bridge_proof_admission_reason_code = None;
    let mut trust_ir_semantic_bridge_proof_admission_admitted = None;
    let mut trust_ir_semantic_bridge_proof_admission_fail_closed = None;
    let mut trust_ir_semantic_bridge_proof_admission_required_artifact_kinds = Vec::new();
    let mut trust_ir_semantic_bridge_proof_admission_artifact_resolution_count = 0_u64;
    let mut trust_ir_semantic_bridge_proof_admission_authoritative_artifact_count = 0_u64;
    let mut trust_ir_semantic_bridge_proof_admission_blocked_artifact_kind = None;
    let mut trust_ir_semantic_bridge_proof_admission_blocked_artifact_reason_code = None;
    let mut trust_ir_semantic_bridge_proof_admission_artifact_authority_lines = Vec::new();

    let blocker = if missing_required_text(expected.entry_function) {
        Some(PetriNativeSuccessorSemanticBridgeBlocker::MissingEntryFunction)
    } else {
        let entry_function = bundle
            .module
            .functions
            .iter()
            .find(|function| function.name == expected.entry_function);
        let Some(entry_function) = entry_function else {
            return PetriNativeSuccessorSemanticBridgeEvidence {
                schema: PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA,
                schema_version: PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA_VERSION,
                status: PetriNativeSuccessorExecutableCallStatus::Blocked,
                blocker: Some(PetriNativeSuccessorSemanticBridgeBlocker::MissingEntryFunction),
                reason_code: Some(
                    PetriNativeSuccessorSemanticBridgeBlocker::MissingEntryFunction.as_str(),
                ),
                required_field: Some(
                    PetriNativeSuccessorSemanticBridgeBlocker::MissingEntryFunction
                        .required_field(),
                ),
                required_evidence: Some(
                    PetriNativeSuccessorSemanticBridgeBlocker::MissingEntryFunction
                        .required_evidence(),
                ),
                formula_schema: expected.formula_schema.to_owned(),
                entry_function: expected.entry_function.to_owned(),
                bundle_validated,
                transport_digest,
                bundle_digest,
                trust_ir_module_digest,
                target_abi_digest,
                native_evidence_report_entries,
                semantic_obligation_count,
                semantic_evidence_entry_count,
                consumed_certificate_count,
                artifact_count,
                successor_relation_represented: false,
                semantic_successor_authority: false,
                trust_ir_semantic_bridge_status_code,
                trust_ir_semantic_bridge_reason_code,
                trust_ir_semantic_bridge_evidence_status_code,
                trust_ir_semantic_bridge_proof_identity_digest,
                trust_ir_trust_mc_chc_binding_schema,
                trust_ir_trust_mc_chc_binding_schema_version,
                trust_ir_trust_mc_chc_binding_function_id,
                trust_ir_trust_mc_chc_binding_status_code,
                trust_ir_trust_mc_chc_binding_reason_code,
                trust_ir_trust_mc_chc_binding_bound,
                trust_ir_trust_mc_chc_binding_fail_closed,
                trust_ir_trust_mc_chc_binding_request_id,
                trust_ir_trust_mc_chc_binding_request_digest,
                trust_ir_trust_mc_chc_binding_evidence_digest,
                trust_ir_trust_mc_chc_binding_expected_evidence_digest,
                trust_ir_trust_mc_chc_binding_horn_clause_artifact,
                trust_ir_trust_mc_chc_binding_horn_clause_artifact_kind,
                trust_ir_trust_mc_chc_binding_horn_clause_digest,
                trust_ir_trust_mc_chc_proof_handoff_schema,
                trust_ir_trust_mc_chc_proof_handoff_schema_version,
                trust_ir_trust_mc_chc_proof_handoff_function_id,
                trust_ir_trust_mc_chc_proof_handoff_status_code,
                trust_ir_trust_mc_chc_proof_handoff_reason_code,
                trust_ir_trust_mc_chc_proof_handoff_ready,
                trust_ir_trust_mc_chc_proof_handoff_fail_closed,
                trust_ir_trust_mc_chc_proof_handoff_proof_identity_digest,
                trust_ir_trust_mc_chc_proof_handoff_replay_engine,
                trust_ir_trust_mc_chc_proof_handoff_replay_invocation,
                trust_ir_trust_mc_chc_proof_handoff_replay_transcript_digest,
                trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact,
                trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_kind,
                trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_digest,
                trust_ir_trust_mc_chc_proof_handoff_model_artifact,
                trust_ir_trust_mc_chc_proof_handoff_model_artifact_kind,
                trust_ir_trust_mc_chc_proof_handoff_model_artifact_digest,
                trust_ir_trust_mc_chc_proof_handoff_solver_identities,
                trust_ir_trust_mc_chc_model_validation_schema,
                trust_ir_trust_mc_chc_model_validation_schema_version,
                trust_ir_trust_mc_chc_model_validation_function_id,
                trust_ir_trust_mc_chc_model_validation_status_code,
                trust_ir_trust_mc_chc_model_validation_reason_code,
                trust_ir_trust_mc_chc_model_validation_ready_for_solver_validation,
                trust_ir_trust_mc_chc_model_validation_fail_closed,
                trust_ir_trust_mc_chc_model_validated,
                trust_ir_trust_mc_chc_model_validation_model_artifact,
                trust_ir_trust_mc_chc_model_validation_model_artifact_kind,
                trust_ir_trust_mc_chc_model_validation_model_artifact_digest,
                trust_ir_trust_mc_chc_model_validation_solver_identities,
                trust_ir_semantic_bridge_proof_admission_schema,
                trust_ir_semantic_bridge_proof_admission_schema_version,
                trust_ir_semantic_bridge_proof_admission_function_id,
                trust_ir_semantic_bridge_proof_admission_status_code,
                trust_ir_semantic_bridge_proof_admission_reason_code,
                trust_ir_semantic_bridge_proof_admission_admitted,
                trust_ir_semantic_bridge_proof_admission_fail_closed,
                trust_ir_semantic_bridge_proof_admission_required_artifact_kinds,
                trust_ir_semantic_bridge_proof_admission_artifact_resolution_count,
                trust_ir_semantic_bridge_proof_admission_authoritative_artifact_count,
                trust_ir_semantic_bridge_proof_admission_blocked_artifact_kind,
                trust_ir_semantic_bridge_proof_admission_blocked_artifact_reason_code,
                trust_ir_semantic_bridge_proof_admission_artifact_authority_lines,
                semantic_bridge_sha256: String::new(),
            }
            .with_canonical_semantic_bridge_sha256();
        };

        let semantic_bridge_report =
            if expected.formula_schema == trust_ir::PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA {
                bundle.petri_successor_semantic_bridge_report(entry_function.id)
            } else {
                bundle.native_semantic_bridge_report(trust_ir::NativeSemanticBridge::new(
                    trust_ir::NativeSemanticRelationKind::PetriSuccessor,
                    entry_function.id,
                    expected.formula_schema,
                ))
            };

        bundle_validated =
            semantic_bridge_report.reason != trust_ir::NativeSemanticBridgeReason::BundleInvalid;
        trust_ir_semantic_bridge_status_code = Some(semantic_bridge_report.status_code());
        trust_ir_semantic_bridge_reason_code = Some(semantic_bridge_report.reason_code());
        trust_ir_semantic_bridge_evidence_status_code =
            Some(semantic_bridge_report.evidence_status_code());
        trust_ir_semantic_bridge_proof_identity_digest =
            Some(semantic_bridge_report.proof_identity_digest().to_string());
        semantic_obligation_count = u64::from(semantic_bridge_report.proof_obligation.is_some());

        if expected.formula_schema == trust_ir::PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA {
            let trust_mc_binding_report =
                bundle.petri_successor_trust_mc_chc_binding_report(entry_function.id);
            trust_ir_trust_mc_chc_binding_schema =
                Some(trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA);
            trust_ir_trust_mc_chc_binding_schema_version =
                Some(trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA_VERSION);
            trust_ir_trust_mc_chc_binding_function_id =
                Some(trust_mc_binding_report.function.to_string());
            trust_ir_trust_mc_chc_binding_status_code = Some(trust_mc_binding_report.status_code());
            trust_ir_trust_mc_chc_binding_reason_code = Some(trust_mc_binding_report.reason_code());
            trust_ir_trust_mc_chc_binding_bound = Some(trust_mc_binding_report.is_bound());
            trust_ir_trust_mc_chc_binding_fail_closed = Some(trust_mc_binding_report.fail_closed());
            trust_ir_trust_mc_chc_binding_request_id = trust_mc_binding_report
                .request
                .map(|request| request.to_string());
            trust_ir_trust_mc_chc_binding_request_digest = trust_mc_binding_report
                .request_digest
                .map(|digest| digest.to_string());
            trust_ir_trust_mc_chc_binding_evidence_digest = trust_mc_binding_report
                .evidence_digest
                .map(|digest| digest.to_string());
            trust_ir_trust_mc_chc_binding_expected_evidence_digest = trust_mc_binding_report
                .expected_evidence_digest
                .map(|digest| digest.to_string());
            if let Some(artifact) = trust_mc_binding_report.horn_clause_artifact {
                trust_ir_trust_mc_chc_binding_horn_clause_artifact = Some(artifact.name);
                trust_ir_trust_mc_chc_binding_horn_clause_artifact_kind =
                    Some(format!("{:?}", artifact.kind));
                trust_ir_trust_mc_chc_binding_horn_clause_digest =
                    Some(artifact.digest.to_string());
            }

            let trust_mc_proof_handoff_report =
                bundle.petri_successor_trust_mc_chc_proof_handoff_report(entry_function.id);
            trust_ir_trust_mc_chc_proof_handoff_schema =
                Some(trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA);
            trust_ir_trust_mc_chc_proof_handoff_schema_version =
                Some(trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA_VERSION);
            trust_ir_trust_mc_chc_proof_handoff_function_id =
                Some(trust_mc_proof_handoff_report.function.to_string());
            trust_ir_trust_mc_chc_proof_handoff_status_code =
                Some(trust_mc_proof_handoff_report.status_code());
            trust_ir_trust_mc_chc_proof_handoff_reason_code =
                Some(trust_mc_proof_handoff_report.reason_code());
            trust_ir_trust_mc_chc_proof_handoff_ready =
                Some(trust_mc_proof_handoff_report.is_ready());
            trust_ir_trust_mc_chc_proof_handoff_fail_closed =
                Some(trust_mc_proof_handoff_report.fail_closed());
            trust_ir_trust_mc_chc_proof_handoff_proof_identity_digest =
                trust_mc_proof_handoff_report
                    .proof_identity_digest
                    .map(|digest| digest.to_string());
            if let Some(replay) = trust_mc_proof_handoff_report.replay {
                trust_ir_trust_mc_chc_proof_handoff_replay_engine = Some(replay.engine);
                trust_ir_trust_mc_chc_proof_handoff_replay_invocation = Some(replay.invocation);
                trust_ir_trust_mc_chc_proof_handoff_replay_transcript_digest =
                    replay.transcript_digest.map(|digest| digest.to_string());
            }
            if let Some(artifact) = trust_mc_proof_handoff_report.replay_transcript_artifact {
                trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact =
                    Some(artifact.name);
                trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_kind =
                    Some(format!("{:?}", artifact.kind));
                trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_digest =
                    Some(artifact.digest.to_string());
            }
            if let Some(artifact) = trust_mc_proof_handoff_report.model_artifact {
                trust_ir_trust_mc_chc_proof_handoff_model_artifact = Some(artifact.name);
                trust_ir_trust_mc_chc_proof_handoff_model_artifact_kind =
                    Some(format!("{:?}", artifact.kind));
                trust_ir_trust_mc_chc_proof_handoff_model_artifact_digest =
                    Some(artifact.digest.to_string());
            }
            trust_ir_trust_mc_chc_proof_handoff_solver_identities = trust_mc_proof_handoff_report
                .solver_identities
                .iter()
                .map(trust_ir_native_tool_identity_evidence_label)
                .collect();

            let trust_mc_model_validation_report = bundle
                .petri_successor_trust_mc_chc_model_validation_readiness_report(entry_function.id);
            trust_ir_trust_mc_chc_model_validation_schema =
                Some(trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA);
            trust_ir_trust_mc_chc_model_validation_schema_version = Some(
                trust_ir::PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA_VERSION,
            );
            trust_ir_trust_mc_chc_model_validation_function_id =
                Some(trust_mc_model_validation_report.function.to_string());
            trust_ir_trust_mc_chc_model_validation_status_code =
                Some(trust_mc_model_validation_report.status_code());
            trust_ir_trust_mc_chc_model_validation_reason_code =
                Some(trust_mc_model_validation_report.reason_code());
            trust_ir_trust_mc_chc_model_validation_ready_for_solver_validation =
                Some(trust_mc_model_validation_report.is_ready_for_solver_validation());
            trust_ir_trust_mc_chc_model_validation_fail_closed =
                Some(trust_mc_model_validation_report.fail_closed());
            trust_ir_trust_mc_chc_model_validated =
                Some(trust_mc_model_validation_report.model_validated);
            if let Some(artifact) = trust_mc_model_validation_report.model_artifact {
                trust_ir_trust_mc_chc_model_validation_model_artifact = Some(artifact.name);
                trust_ir_trust_mc_chc_model_validation_model_artifact_kind =
                    Some(format!("{:?}", artifact.kind));
            }
            trust_ir_trust_mc_chc_model_validation_model_artifact_digest =
                trust_mc_model_validation_report
                    .model_artifact_digest
                    .map(|digest| digest.to_string());
            trust_ir_trust_mc_chc_model_validation_solver_identities =
                trust_mc_model_validation_report
                    .solver_identities
                    .iter()
                    .map(trust_ir_native_tool_identity_evidence_label)
                    .collect();

            let proof_admission_report = bundle
                .petri_successor_semantic_bridge_proof_admission_report(
                    entry_function.id,
                    artifact_attachments,
                );
            trust_ir_semantic_bridge_proof_admission_schema =
                Some(proof_admission_report.schema.clone());
            trust_ir_semantic_bridge_proof_admission_schema_version =
                Some(proof_admission_report.schema_version);
            trust_ir_semantic_bridge_proof_admission_function_id =
                Some(proof_admission_report.function.to_string());
            trust_ir_semantic_bridge_proof_admission_status_code =
                Some(proof_admission_report.status_code());
            trust_ir_semantic_bridge_proof_admission_reason_code =
                Some(proof_admission_report.reason_code());
            trust_ir_semantic_bridge_proof_admission_admitted =
                Some(proof_admission_report.is_admitted());
            trust_ir_semantic_bridge_proof_admission_fail_closed =
                Some(proof_admission_report.fail_closed());
            trust_ir_semantic_bridge_proof_admission_required_artifact_kinds =
                proof_admission_report
                    .required_artifact_kinds
                    .iter()
                    .map(|kind| kind.code().to_owned())
                    .collect();
            trust_ir_semantic_bridge_proof_admission_artifact_resolution_count =
                proof_admission_report.artifact_resolutions.len() as u64;
            trust_ir_semantic_bridge_proof_admission_authoritative_artifact_count =
                proof_admission_report
                    .artifact_resolutions
                    .iter()
                    .filter(|resolution| resolution.is_authoritative())
                    .count() as u64;
            trust_ir_semantic_bridge_proof_admission_blocked_artifact_kind = proof_admission_report
                .blocked_artifact_kind
                .map(|kind| kind.code().to_owned());
            trust_ir_semantic_bridge_proof_admission_blocked_artifact_reason_code =
                proof_admission_report.blocked_artifact_reason_code();
            trust_ir_semantic_bridge_proof_admission_artifact_authority_lines =
                trust_ir_semantic_bridge_proof_admission_authority_lines(&proof_admission_report);
        }

        if bundle_validated && let Ok(report) = bundle.native_evidence_consumption_report() {
            native_evidence_report_entries = report.entries.len() as u64;
            if let Some(proof_obligation) = semantic_bridge_report.proof_obligation {
                for entry in &report.entries {
                    if entry.obligations.contains(&proof_obligation) {
                        semantic_evidence_entry_count += 1;
                        consumed_certificate_count += entry.consumed_certificates.len() as u64;
                        artifact_count += entry.artifacts.len() as u64;
                    }
                }
            }
        }

        petri_native_successor_semantic_bridge_blocker_from_trust_ir_report(&semantic_bridge_report)
    };

    let status = if blocker.is_some() {
        PetriNativeSuccessorExecutableCallStatus::Blocked
    } else {
        PetriNativeSuccessorExecutableCallStatus::Ready
    };
    let successor_relation_represented =
        status == PetriNativeSuccessorExecutableCallStatus::Ready && semantic_obligation_count > 0;
    let semantic_successor_authority =
        successor_relation_represented && semantic_evidence_entry_count > 0;

    PetriNativeSuccessorSemanticBridgeEvidence {
        schema: PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_SEMANTIC_BRIDGE_SCHEMA_VERSION,
        status,
        blocker,
        reason_code: blocker.map(|blocker| blocker.as_str()),
        required_field: blocker.map(|blocker| blocker.required_field()),
        required_evidence: blocker.map(|blocker| blocker.required_evidence()),
        formula_schema: expected.formula_schema.to_owned(),
        entry_function: expected.entry_function.to_owned(),
        bundle_validated,
        transport_digest,
        bundle_digest,
        trust_ir_module_digest,
        target_abi_digest,
        native_evidence_report_entries,
        semantic_obligation_count,
        semantic_evidence_entry_count,
        consumed_certificate_count,
        artifact_count,
        successor_relation_represented,
        semantic_successor_authority,
        trust_ir_semantic_bridge_status_code,
        trust_ir_semantic_bridge_reason_code,
        trust_ir_semantic_bridge_evidence_status_code,
        trust_ir_semantic_bridge_proof_identity_digest,
        trust_ir_trust_mc_chc_binding_schema,
        trust_ir_trust_mc_chc_binding_schema_version,
        trust_ir_trust_mc_chc_binding_function_id,
        trust_ir_trust_mc_chc_binding_status_code,
        trust_ir_trust_mc_chc_binding_reason_code,
        trust_ir_trust_mc_chc_binding_bound,
        trust_ir_trust_mc_chc_binding_fail_closed,
        trust_ir_trust_mc_chc_binding_request_id,
        trust_ir_trust_mc_chc_binding_request_digest,
        trust_ir_trust_mc_chc_binding_evidence_digest,
        trust_ir_trust_mc_chc_binding_expected_evidence_digest,
        trust_ir_trust_mc_chc_binding_horn_clause_artifact,
        trust_ir_trust_mc_chc_binding_horn_clause_artifact_kind,
        trust_ir_trust_mc_chc_binding_horn_clause_digest,
        trust_ir_trust_mc_chc_proof_handoff_schema,
        trust_ir_trust_mc_chc_proof_handoff_schema_version,
        trust_ir_trust_mc_chc_proof_handoff_function_id,
        trust_ir_trust_mc_chc_proof_handoff_status_code,
        trust_ir_trust_mc_chc_proof_handoff_reason_code,
        trust_ir_trust_mc_chc_proof_handoff_ready,
        trust_ir_trust_mc_chc_proof_handoff_fail_closed,
        trust_ir_trust_mc_chc_proof_handoff_proof_identity_digest,
        trust_ir_trust_mc_chc_proof_handoff_replay_engine,
        trust_ir_trust_mc_chc_proof_handoff_replay_invocation,
        trust_ir_trust_mc_chc_proof_handoff_replay_transcript_digest,
        trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact,
        trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_kind,
        trust_ir_trust_mc_chc_proof_handoff_replay_transcript_artifact_digest,
        trust_ir_trust_mc_chc_proof_handoff_model_artifact,
        trust_ir_trust_mc_chc_proof_handoff_model_artifact_kind,
        trust_ir_trust_mc_chc_proof_handoff_model_artifact_digest,
        trust_ir_trust_mc_chc_proof_handoff_solver_identities,
        trust_ir_trust_mc_chc_model_validation_schema,
        trust_ir_trust_mc_chc_model_validation_schema_version,
        trust_ir_trust_mc_chc_model_validation_function_id,
        trust_ir_trust_mc_chc_model_validation_status_code,
        trust_ir_trust_mc_chc_model_validation_reason_code,
        trust_ir_trust_mc_chc_model_validation_ready_for_solver_validation,
        trust_ir_trust_mc_chc_model_validation_fail_closed,
        trust_ir_trust_mc_chc_model_validated,
        trust_ir_trust_mc_chc_model_validation_model_artifact,
        trust_ir_trust_mc_chc_model_validation_model_artifact_kind,
        trust_ir_trust_mc_chc_model_validation_model_artifact_digest,
        trust_ir_trust_mc_chc_model_validation_solver_identities,
        trust_ir_semantic_bridge_proof_admission_schema,
        trust_ir_semantic_bridge_proof_admission_schema_version,
        trust_ir_semantic_bridge_proof_admission_function_id,
        trust_ir_semantic_bridge_proof_admission_status_code,
        trust_ir_semantic_bridge_proof_admission_reason_code,
        trust_ir_semantic_bridge_proof_admission_admitted,
        trust_ir_semantic_bridge_proof_admission_fail_closed,
        trust_ir_semantic_bridge_proof_admission_required_artifact_kinds,
        trust_ir_semantic_bridge_proof_admission_artifact_resolution_count,
        trust_ir_semantic_bridge_proof_admission_authoritative_artifact_count,
        trust_ir_semantic_bridge_proof_admission_blocked_artifact_kind,
        trust_ir_semantic_bridge_proof_admission_blocked_artifact_reason_code,
        trust_ir_semantic_bridge_proof_admission_artifact_authority_lines,
        semantic_bridge_sha256: String::new(),
    }
    .with_canonical_semantic_bridge_sha256()
}

fn petri_native_successor_semantic_bridge_blocker_from_trust_ir_report(
    report: &trust_ir::NativeSemanticBridgeReport,
) -> Option<PetriNativeSuccessorSemanticBridgeBlocker> {
    match report.reason {
        trust_ir::NativeSemanticBridgeReason::Represented
            if report.represents_petri_successor_plan_cache_equivalence()
                || report.bridge.relation
                    == trust_ir::NativeSemanticRelationKind::PetriSuccessor =>
        {
            None
        }
        trust_ir::NativeSemanticBridgeReason::Represented => {
            Some(PetriNativeSuccessorSemanticBridgeBlocker::MissingSemanticSuccessorObligation)
        }
        trust_ir::NativeSemanticBridgeReason::BundleInvalid => {
            Some(PetriNativeSuccessorSemanticBridgeBlocker::BundleValidationFailed)
        }
        trust_ir::NativeSemanticBridgeReason::MissingFunction => {
            Some(PetriNativeSuccessorSemanticBridgeBlocker::MissingEntryFunction)
        }
        trust_ir::NativeSemanticBridgeReason::MissingEvidence => {
            Some(PetriNativeSuccessorSemanticBridgeBlocker::MissingSemanticSuccessorEvidence)
        }
        trust_ir::NativeSemanticBridgeReason::MissingProofObligation
        | trust_ir::NativeSemanticBridgeReason::MissingObligationSource
        | trust_ir::NativeSemanticBridgeReason::FunctionMismatch
        | trust_ir::NativeSemanticBridgeReason::UnsupportedObligationKind
        | trust_ir::NativeSemanticBridgeReason::ProofPending
        | trust_ir::NativeSemanticBridgeReason::ProofFailed
        | trust_ir::NativeSemanticBridgeReason::TrustedProofNotAdmitted => {
            Some(PetriNativeSuccessorSemanticBridgeBlocker::MissingSemanticSuccessorObligation)
        }
    }
}

fn trust_ir_semantic_bridge_proof_admission_authority_lines(
    report: &trust_ir::PetriSuccessorSemanticBridgeProofAdmissionReport<'_>,
) -> Vec<String> {
    let mut lines = Vec::new();
    for (index, resolution) in report.artifact_resolutions.iter().enumerate() {
        lines.push(format!(
            "artifact_resolution.{index}.required_kind={}",
            resolution.required_kind.code()
        ));
        lines.push(format!(
            "artifact_resolution.{index}.status={}",
            resolution.status_code()
        ));
        lines.push(format!(
            "artifact_resolution.{index}.reason={}",
            resolution.reason_code()
        ));
        lines.push(format!(
            "artifact_resolution.{index}.is_authoritative={}",
            petri_native_successor_bool_code(resolution.is_authoritative())
        ));
        if let Some(artifact_digest) = resolution.artifact_digest() {
            lines.push(format!(
                "artifact_resolution.{index}.artifact_digest={artifact_digest}"
            ));
        }
        if let Some(actual_digest) = resolution.actual_digest() {
            lines.push(format!(
                "artifact_resolution.{index}.actual_digest={actual_digest}"
            ));
        }
        if let Some(byte_len) = resolution.byte_len() {
            lines.push(format!("artifact_resolution.{index}.byte_len={byte_len}"));
        }
        if let Some(source_identity) = resolution.byte_source_identity() {
            lines.push(format!(
                "artifact_resolution.{index}.byte_source_identity={source_identity}"
            ));
        }
        if let Some(authority_lines) = resolution.authority_evidence_key_value_lines() {
            for line in authority_lines {
                lines.push(format!("artifact_resolution.{index}.authority.{line}"));
            }
        }
    }
    lines
}

fn trust_ir_native_tool_identity_evidence_label(identity: &trust_ir::NativeToolIdentity) -> String {
    format!(
        "name={};version={};revision={};digest={}",
        identity.name,
        identity.version.as_deref().unwrap_or(""),
        identity.revision.as_deref().unwrap_or(""),
        identity
            .digest
            .as_ref()
            .map(ToString::to_string)
            .unwrap_or_default()
    )
}

/// Evaluate whether a native compile artifact has the explicit handoff inputs needed for Petri JIT.
///
/// This is a typed evidence boundary for the production runtime bridge from
/// Trust Codegen native compile artifacts into Petri install/call packets. It does not
/// install or invoke code. Missing native payload, symbol, pointer, or lifetime
/// inputs remain fail-closed with field-level blocker codes.
pub fn petri_native_successor_compile_artifact_handoff_evidence(
    input: PetriNativeSuccessorCompileArtifactHandoffInput<'_>,
) -> PetriNativeSuccessorCompileArtifactHandoffEvidence {
    let blocker = petri_native_successor_compile_artifact_handoff_blocker(input);
    let status = if blocker.is_some() {
        PetriNativeSuccessorExecutableCallStatus::Blocked
    } else {
        PetriNativeSuccessorExecutableCallStatus::Ready
    };

    PetriNativeSuccessorCompileArtifactHandoffEvidence {
        schema: PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA_VERSION,
        status,
        blocker,
        reason_code: blocker.map(|blocker| blocker.as_str()),
        required_field: blocker.map(|blocker| blocker.required_field()),
        required_evidence: blocker.map(|blocker| blocker.required_evidence()),
        native_payload_sha256: input.native_payload_sha256.map(str::to_owned),
        entry_symbol: input.entry_symbol.map(str::to_owned),
        callable_pointer: input.callable_pointer,
        executable_region_sha256: input.executable_region_sha256.map(str::to_owned),
        lifetime_owner: input.lifetime_owner.map(str::to_owned),
        current_generation: input.current_generation,
        compile_artifact_handoff_sha256: String::new(),
    }
    .with_canonical_compile_artifact_handoff_sha256()
}

/// Admit a Petri/MCC native successor bundle through Trust Codegen's native install-gate summary schema.
///
/// This bridge is intentionally validation-only for now. It consumes trust_ir's
/// typed bundle validation and native evidence consumption report, then emits
/// the existing `NativeInstallGateAdmissionSummary` reason-code vocabulary. It
/// never grants callable/native activation authority for Petri successor JIT.
pub fn petri_native_successor_admission_from_trust_ir_bundle(
    bundle: &trust_ir::NativeVerificationBundle,
    expected: PetriNativeSuccessorAdmissionExpected<'_>,
) -> NativeInstallGateAdmissionSummary {
    let identity = bundle.transport_identity();

    if !petri_native_successor_expected_supported(expected) {
        return petri_native_successor_rejected_summary(
            &identity,
            expected,
            NativeInstallGateRejectionCode::ConsumerAdmissionDenied,
        );
    }

    let report = match bundle.native_evidence_consumption_report() {
        Ok(report) => report,
        Err(_) => {
            return petri_native_successor_rejected_summary(
                &identity,
                expected,
                NativeInstallGateRejectionCode::PetriTrustIrBundleValidationFailed,
            );
        }
    };
    if report.is_empty() {
        return petri_native_successor_rejected_summary(
            &identity,
            expected,
            NativeInstallGateRejectionCode::MissingNativeEvidenceBundle,
        );
    }

    if expected
        .target_abi_digest
        .is_some_and(|digest| identity.target_abi.as_ref().map(|abi| abi.digest) != Some(digest))
    {
        return petri_native_successor_rejected_summary(
            &identity,
            expected,
            NativeInstallGateRejectionCode::TargetAbiMismatch,
        );
    }

    let Some(packet) = expected.native_install_gate_packet else {
        return petri_native_successor_rejected_summary(
            &identity,
            expected,
            NativeInstallGateRejectionCode::MissingNativeInstallGatePacket,
        );
    };

    let persisted_verdict = validate_native_install_gate_packet(packet, Some(packet.packet_hash));
    if persisted_verdict.rejection_code.is_some()
        || persisted_verdict.disposition != packet.disposition
        || persisted_verdict.install_authority != packet.install_authority
        || persisted_verdict.actions != packet.actions
    {
        return petri_native_successor_rejected_summary(
            &identity,
            expected,
            persisted_verdict
                .rejection_code
                .unwrap_or(NativeInstallGateRejectionCode::ConsumerAdmissionDenied),
        );
    }

    if !petri_native_successor_packet_binds_identity(packet, &identity, expected) {
        return petri_native_successor_rejected_summary(
            &identity,
            expected,
            NativeInstallGateRejectionCode::ProofReplayIdentityMismatch,
        );
    }

    if expected.requested_authority == NativeInstallGateAuthority::ValidationOnly
        && (packet.disposition.is_installable()
            || packet.install_authority != NativeInstallGateAuthority::None
            || !packet.actions.all_install_authority_blocked())
    {
        return petri_native_successor_rejected_summary(
            &identity,
            expected,
            NativeInstallGateRejectionCode::ConsumerAdmissionDenied,
        );
    }

    if expected.requested_authority.is_callable()
        && (!packet.disposition.is_installable()
            || packet.install_authority != expected.requested_authority
            || !packet.actions.expose_callable)
    {
        return petri_native_successor_rejected_summary(
            &identity,
            expected,
            NativeInstallGateRejectionCode::ConsumerAdmissionDenied,
        );
    }

    packet.admission_summary()
}

/// Build a Petri/MCC native successor execution plan from a trust_ir native bundle.
///
/// This is a concrete lower-level callable boundary: it binds a requested trust_ir
/// successor entrypoint and state-buffer ABI to trust_ir transport/native evidence.
/// It still fails closed through native install-gate admission until a real
/// native install packet authorizes the callable.
pub fn petri_native_successor_execution_plan_from_trust_ir_bundle(
    bundle: &trust_ir::NativeVerificationBundle,
    expected: PetriNativeSuccessorExecutionExpected<'_>,
) -> PetriNativeSuccessorExecutionPlan {
    let identity = bundle.transport_identity();
    let admission_summary =
        petri_native_successor_admission_from_trust_ir_bundle(bundle, expected.admission);
    let callable_contract_blocker =
        petri_native_successor_callable_contract_blocker_from_trust_ir_bundle(
            bundle, &identity, expected,
        );
    let callable_contract = if callable_contract_blocker.is_none() {
        Some(petri_native_successor_callable_contract_from_identity(
            &identity, expected,
        ))
    } else {
        None
    };
    let trampoline_contract = callable_contract.as_ref().and_then(|contract| {
        expected
            .trampoline_contract
            .filter(|trampoline| trampoline.binds_callable_contract(contract))
            .cloned()
    });
    let callable_authorized = callable_contract.is_some()
        && trampoline_contract.is_some()
        && admission_summary.disposition == NativeInstallGateDisposition::Installable.as_str()
        && admission_summary.actions.expose_callable;

    PetriNativeSuccessorExecutionPlan {
        schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_EXECUTION_PLAN_SCHEMA_VERSION,
        reason_code: admission_summary.reason_code,
        admission_summary,
        callable_contract,
        callable_contract_blocker,
        callable_contract_blocker_stage: callable_contract_blocker.map(|blocker| blocker.stage()),
        callable_contract_reason_code: callable_contract_blocker.map(|blocker| blocker.as_str()),
        callable_contract_required_field: callable_contract_blocker
            .map(|blocker| blocker.required_field()),
        callable_contract_required_evidence: callable_contract_blocker
            .map(|blocker| blocker.required_evidence()),
        trampoline_contract,
        callable_authorized,
        fail_closed: !callable_authorized,
    }
}

/// Build a native-successor install packet for a validated Petri/MCC trust_ir bundle.
///
/// The returned packet is still just evidence: callers must validate it with
/// `validate_native_install_gate_packet` and pass it back through
/// `petri_native_successor_execution_plan_from_trust_ir_bundle` before publishing a
/// callable.
pub fn petri_native_successor_install_packet_from_trust_ir_bundle(
    bundle: &trust_ir::NativeVerificationBundle,
    expected: PetriNativeSuccessorExecutionExpected<'_>,
    trampoline: &PetriNativeSuccessorTrampolineContract,
) -> Result<NativeInstallGatePacket, NativeInstallGateRejectionCode> {
    let identity = bundle.transport_identity();
    if !petri_native_successor_expected_supported(expected.admission)
        || !expected.admission.requested_authority.is_callable()
    {
        return Err(NativeInstallGateRejectionCode::InconsistentActionAuthority);
    }

    let report = bundle
        .native_evidence_consumption_report()
        .map_err(|_| NativeInstallGateRejectionCode::PetriTrustIrBundleValidationFailed)?;
    if report.is_empty() {
        return Err(NativeInstallGateRejectionCode::MissingNativeEvidenceBundle);
    }
    if expected.admission.target_abi_digest.is_some_and(|digest| {
        identity.target_abi.as_ref().map(|target| target.digest) != Some(digest)
    }) {
        return Err(NativeInstallGateRejectionCode::TargetAbiMismatch);
    }

    let Some(contract) =
        petri_native_successor_callable_contract_from_trust_ir_bundle(bundle, &identity, expected)
    else {
        return Err(NativeInstallGateRejectionCode::ConsumerAdmissionDenied);
    };
    if !trampoline.binds_callable_contract(&contract)
        || expected
            .trampoline_contract
            .is_some_and(|expected_trampoline| expected_trampoline != trampoline)
    {
        return Err(NativeInstallGateRejectionCode::ConsumerAdmissionDenied);
    }

    let mut input = petri_native_successor_gate_input(&identity, expected.admission);
    input.candidate_disposition = NativeInstallGateDisposition::Installable;
    input.layout_evidence = Some(petri_native_successor_layout_evidence(
        &contract,
        trampoline,
        &input.expected,
    ));
    input.proof_evidence = Some(petri_native_successor_proof_evidence(
        &contract,
        trampoline,
        &input.expected,
    ));
    input.replay_identity = Some(petri_native_successor_replay_identity(
        &contract,
        trampoline,
        &input.expected,
        &input.payload_identity,
    ));
    input.telemetry = Some(petri_native_successor_telemetry(
        &contract,
        trampoline,
        &input.expected,
        &input.proof_evidence,
        expected.admission.requested_authority,
    ));

    Ok(build_packet(
        &input,
        NativeInstallGateDisposition::Installable,
        None,
    ))
}

/// Build an authorized Petri/MCC native successor host call handoff packet.
///
/// The caller must provide an explicit non-null host callable pointer and the
/// trampoline identity that compiled pointer implements. The returned packet is
/// available only after the existing native install gate has accepted a
/// callable packet and the execution plan has re-bound that packet to the trust_ir
/// bundle; validation-only and unbound paths return a typed rejection code.
pub fn petri_native_successor_call_packet_from_trust_ir_bundle(
    bundle: &trust_ir::NativeVerificationBundle,
    expected: PetriNativeSuccessorExecutionExpected<'_>,
    trampoline: &PetriNativeSuccessorTrampolineContract,
    callable_pointer: PetriNativeSuccessorCallablePointer,
) -> Result<PetriNativeSuccessorCallPacket, NativeInstallGateRejectionCode> {
    if expected
        .trampoline_contract
        .is_some_and(|expected_trampoline| expected_trampoline != trampoline)
    {
        return Err(NativeInstallGateRejectionCode::ConsumerAdmissionDenied);
    }

    let expected = expected.with_trampoline_contract(trampoline);
    let plan = petri_native_successor_execution_plan_from_trust_ir_bundle(bundle, expected);
    if !plan.callable_authorized {
        return Err(petri_native_successor_execution_plan_rejection_code(&plan));
    }
    if plan.admission_summary.actions.ty_native_activate {
        return Err(NativeInstallGateRejectionCode::InconsistentActionAuthority);
    }

    let contract = plan
        .callable_contract
        .as_ref()
        .ok_or(NativeInstallGateRejectionCode::ConsumerAdmissionDenied)?;
    let plan_trampoline = plan
        .trampoline_contract
        .as_ref()
        .ok_or(NativeInstallGateRejectionCode::ConsumerAdmissionDenied)?;
    if plan_trampoline != trampoline || !trampoline.binds_callable_contract(contract) {
        return Err(NativeInstallGateRejectionCode::ConsumerAdmissionDenied);
    }

    Ok(PetriNativeSuccessorCallPacket {
        schema: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA_VERSION,
        install_packet_hash: plan.admission_summary.packet_hash,
        persisted_install_packet_hash: plan.admission_summary.persisted_packet_hash,
        admission_summary: plan.admission_summary.clone(),
        callable_pointer,
        callable_contract_sha256: contract.callable_contract_sha256.clone(),
        trampoline_sha256: trampoline.trampoline_sha256.clone(),
        native_payload_sha256: trampoline.native_payload_sha256.clone(),
        entry_symbol: trampoline.entry_symbol.clone(),
        trampoline_abi: trampoline.trampoline_abi,
        entry_function: contract.entry_function.clone(),
        state_encoding: contract.state_encoding,
        input_state_bytes: contract.input_state_bytes,
        output_state_bytes: contract.output_state_bytes,
        state_alignment_bytes: contract.state_alignment_bytes,
        callable_authorized: true,
        fail_closed: false,
        reason_code: None,
        call_packet_sha256: String::new(),
    }
    .with_canonical_call_packet_sha256())
}

/// Derive a concrete Petri/MCC native successor install manifest identity.
///
/// This is a pure evidence boundary: it does not install or invoke native code.
/// It fails closed unless the supplied packet is a Petri native-successor packet
/// with complete transport/manifest digest fields and a current packet hash.
pub fn petri_native_successor_manifest_identity(
    packet: Option<&NativeInstallGatePacket>,
) -> Result<PetriNativeSuccessorManifestIdentity, PetriNativeSuccessorManifestIdentityBlocker> {
    let packet = packet
        .ok_or(PetriNativeSuccessorManifestIdentityBlocker::MissingNativeInstallGatePacket)?;
    if let Some(blocker) = petri_native_successor_manifest_identity_blocker(packet) {
        return Err(blocker);
    }

    Ok(PetriNativeSuccessorManifestIdentity {
        schema: PETRI_NATIVE_SUCCESSOR_MANIFEST_IDENTITY_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_MANIFEST_IDENTITY_SCHEMA_VERSION,
        source: PetriNativeSuccessorManifestIdentitySource::from_packet(packet),
        packet_hash: native_install_gate_packet_hash(packet),
        persisted_packet_hash: packet.packet_hash,
        consumer: packet.consumer.clone(),
        consumer_mode: packet.consumer_mode.clone(),
        surface: packet.surface,
        artifact_id: packet.artifact.artifact_id.clone(),
        manifest_checksum: packet.artifact.manifest_checksum,
        source_sha256: packet.artifact.source_sha256.clone(),
        trust_ir_sha256: packet.artifact.trust_ir_sha256.clone(),
        native_payload_sha256: packet.artifact.native_payload_sha256.clone(),
        target_checksum: packet.artifact.target_checksum,
        abi_checksum: packet.artifact.abi_checksum,
        layout_checksum: packet.artifact.layout_checksum,
        proof_policy_checksum: packet.artifact.proof_policy_checksum,
        invalidation_checksum: packet.artifact.invalidation_checksum,
        manifest_identity_sha256: String::new(),
    }
    .with_canonical_manifest_identity_sha256())
}

/// Evaluate Petri/MCC native successor install manifest and trampoline binding evidence.
///
/// This is a metadata-only readiness boundary. It does not require a full
/// generic artifact manifest for Petri: when an install packet was produced
/// from trust_ir transport identity, it emits a typed Petri manifest identity hash
/// from the packet's existing digest fields. Missing packets, missing manifest
/// identity, and unbound trampolines remain explicit fail-closed blockers.
pub fn petri_native_successor_install_binding_evidence(
    packet: Option<&NativeInstallGatePacket>,
    trampoline: Option<&PetriNativeSuccessorTrampolineContract>,
) -> PetriNativeSuccessorInstallBindingEvidence {
    let blocker = petri_native_successor_install_binding_blocker(packet, trampoline);
    let manifest_identity = petri_native_successor_manifest_identity(packet).ok();
    let status = if blocker.is_some() {
        PetriNativeSuccessorExecutableCallStatus::Blocked
    } else {
        PetriNativeSuccessorExecutableCallStatus::Ready
    };

    PetriNativeSuccessorInstallBindingEvidence {
        schema: PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_EVIDENCE_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_INSTALL_BINDING_EVIDENCE_SCHEMA_VERSION,
        status,
        blocker,
        required_evidence: blocker.map(|blocker| blocker.required_evidence()),
        packet_hash: packet.map(native_install_gate_packet_hash),
        persisted_packet_hash: packet.map(|packet| packet.packet_hash),
        manifest_identity_schema: PETRI_NATIVE_SUCCESSOR_MANIFEST_IDENTITY_SCHEMA,
        manifest_identity_schema_version: PETRI_NATIVE_SUCCESSOR_MANIFEST_IDENTITY_SCHEMA_VERSION,
        manifest_source: packet.map(petri_native_successor_manifest_source),
        manifest_identity_sha256: manifest_identity
            .as_ref()
            .map(|identity| identity.manifest_identity_sha256.clone()),
        artifact_id: packet.map(|packet| packet.artifact.artifact_id.clone()),
        manifest_checksum: packet.map(|packet| packet.artifact.manifest_checksum),
        source_sha256: packet.map(|packet| packet.artifact.source_sha256.clone()),
        trust_ir_sha256: packet.map(|packet| packet.artifact.trust_ir_sha256.clone()),
        native_payload_sha256: packet.map(|packet| packet.artifact.native_payload_sha256.clone()),
        target_checksum: packet.map(|packet| packet.artifact.target_checksum),
        abi_checksum: packet.map(|packet| packet.artifact.abi_checksum),
        layout_checksum: packet.map(|packet| packet.artifact.layout_checksum),
        proof_policy_checksum: packet.map(|packet| packet.artifact.proof_policy_checksum),
        invalidation_checksum: packet.map(|packet| packet.artifact.invalidation_checksum),
        trampoline_sha256: trampoline.map(|trampoline| trampoline.trampoline_sha256.clone()),
        layout_wrapper_identity: packet
            .and_then(|packet| packet.validation.layout_wrapper_identity.clone()),
        entry_symbol: trampoline.map(|trampoline| trampoline.entry_symbol.clone()),
        trampoline_abi: trampoline.map(|trampoline| trampoline.trampoline_abi),
        install_binding_evidence_sha256: String::new(),
    }
    .with_canonical_install_binding_evidence_sha256()
}

/// Evaluate whether a Petri/MCC native successor call packet is executable-ready.
///
/// This function does not invoke native code. It records whether the existing
/// call packet has callable authority and whether the caller supplied the
/// additional runtime evidence needed before a host JIT may safely dereference
/// the pointer: executable lifetime ownership and the stable runtime ABI proof.
pub fn petri_native_successor_executable_call_evidence(
    packet: &PetriNativeSuccessorCallPacket,
    lifetime_proof: Option<&PetriNativeSuccessorCallableLifetimeProof>,
    runtime_abi_proof: Option<&PetriNativeSuccessorRuntimeAbiProof>,
    current_generation: u64,
) -> PetriNativeSuccessorExecutableCallEvidence {
    let blocker = petri_native_successor_executable_call_blocker(
        packet,
        lifetime_proof,
        runtime_abi_proof,
        current_generation,
    );
    let status = if blocker.is_some() {
        PetriNativeSuccessorExecutableCallStatus::Blocked
    } else {
        PetriNativeSuccessorExecutableCallStatus::Ready
    };

    PetriNativeSuccessorExecutableCallEvidence {
        schema: PETRI_NATIVE_SUCCESSOR_EXECUTABLE_CALL_EVIDENCE_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_EXECUTABLE_CALL_EVIDENCE_SCHEMA_VERSION,
        call_packet_sha256: packet.call_packet_sha256.clone(),
        callable_pointer: packet.callable_pointer,
        lifetime_proof_sha256: lifetime_proof.map(|proof| proof.lifetime_proof_sha256.clone()),
        runtime_abi_proof_sha256: runtime_abi_proof
            .map(|proof| proof.runtime_abi_proof_sha256.clone()),
        executable_region_sha256: lifetime_proof
            .map(|proof| proof.executable_region_sha256.clone()),
        current_generation,
        status,
        blocker,
        required_evidence: blocker.and_then(|blocker| blocker.required_evidence()),
        executable_call_evidence_sha256: String::new(),
    }
    .with_canonical_executable_call_evidence_sha256()
}

/// Join all Petri/MCC native successor handoff surfaces into one readiness packet.
///
/// This function deliberately composes the existing Trust Codegen primitives instead of
/// revalidating them with a parallel schema. Downstream consumers can inspect a
/// single typed packet and still see the exact lower-level blocker family that
/// keeps runtime calls fail-closed.
pub fn petri_native_successor_runtime_readiness_packet(
    call_packet: Option<&PetriNativeSuccessorCallPacket>,
    install_packet: Option<&NativeInstallGatePacket>,
    trampoline: Option<&PetriNativeSuccessorTrampolineContract>,
    lifetime_proof: Option<&PetriNativeSuccessorCallableLifetimeProof>,
    runtime_abi_proof: Option<&PetriNativeSuccessorRuntimeAbiProof>,
    current_generation: u64,
) -> PetriNativeSuccessorRuntimeReadinessPacket {
    let manifest_identity = petri_native_successor_manifest_identity(install_packet);
    let manifest_identity_blocker = manifest_identity.as_ref().err().copied();
    let install_binding_evidence =
        petri_native_successor_install_binding_evidence(install_packet, trampoline);
    let executable_call_evidence = call_packet.map(|packet| {
        petri_native_successor_executable_call_evidence(
            packet,
            lifetime_proof,
            runtime_abi_proof,
            current_generation,
        )
    });

    let blocker = if let Some(blocker) = manifest_identity_blocker {
        Some(PetriNativeSuccessorRuntimeReadinessBlocker::ManifestIdentity(blocker))
    } else if let Some(blocker) = install_binding_evidence.blocker {
        Some(PetriNativeSuccessorRuntimeReadinessBlocker::InstallBinding(
            blocker,
        ))
    } else if let Some(call_packet) = call_packet {
        if petri_native_successor_call_packet_binds_readiness_inputs(
            call_packet,
            install_packet,
            trampoline,
        ) {
            executable_call_evidence
                .as_ref()
                .and_then(|evidence| evidence.blocker)
                .map(PetriNativeSuccessorRuntimeReadinessBlocker::ExecutableCall)
        } else {
            Some(PetriNativeSuccessorRuntimeReadinessBlocker::CallPacketBindingMismatch)
        }
    } else {
        Some(PetriNativeSuccessorRuntimeReadinessBlocker::MissingCallablePointer)
    };
    let ready_for_runtime_call = blocker.is_none();
    let status = if ready_for_runtime_call {
        PetriNativeSuccessorRuntimeReadinessStatus::ReadyForRuntimeCall
    } else {
        PetriNativeSuccessorRuntimeReadinessStatus::Blocked
    };

    PetriNativeSuccessorRuntimeReadinessPacket {
        schema: PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA_VERSION,
        status,
        ready_for_runtime_call,
        blocker,
        blocker_stage: blocker.map(|blocker| blocker.stage()),
        reason_code: blocker.map(|blocker| blocker.as_str()),
        required_evidence: blocker.and_then(|blocker| blocker.required_evidence()),
        current_generation,
        call_packet_available: call_packet.is_some(),
        call_packet_sha256: call_packet.map(|packet| packet.call_packet_sha256.clone()),
        callable_pointer: call_packet.map(|packet| packet.callable_pointer),
        native_payload_sha256: call_packet.map(|packet| packet.native_payload_sha256.clone()),
        entry_symbol: call_packet.map(|packet| packet.entry_symbol.clone()),
        callable_authorized: call_packet.is_some_and(|packet| packet.callable_authorized),
        install_packet_hash: install_packet.map(native_install_gate_packet_hash),
        persisted_install_packet_hash: install_packet.map(|packet| packet.packet_hash),
        manifest_identity_ready: manifest_identity.is_ok(),
        manifest_identity_sha256: manifest_identity
            .as_ref()
            .ok()
            .map(|identity| identity.manifest_identity_sha256.clone()),
        manifest_identity_source: manifest_identity
            .as_ref()
            .ok()
            .map(|identity| identity.source),
        manifest_identity_blocker,
        install_binding_ready: install_binding_evidence.is_ready(),
        install_binding_evidence_sha256: install_binding_evidence.install_binding_evidence_sha256,
        install_binding_blocker: install_binding_evidence.blocker,
        trampoline_sha256: trampoline.map(|trampoline| trampoline.trampoline_sha256.clone()),
        executable_call_ready: executable_call_evidence
            .as_ref()
            .is_some_and(PetriNativeSuccessorExecutableCallEvidence::is_ready),
        executable_call_evidence_sha256: executable_call_evidence
            .as_ref()
            .map(|evidence| evidence.executable_call_evidence_sha256.clone()),
        executable_call_blocker: executable_call_evidence
            .as_ref()
            .and_then(|evidence| evidence.blocker),
        lifetime_proof_sha256: lifetime_proof.map(|proof| proof.lifetime_proof_sha256.clone()),
        runtime_abi_proof_sha256: runtime_abi_proof
            .map(|proof| proof.runtime_abi_proof_sha256.clone()),
        executable_region_sha256: lifetime_proof
            .map(|proof| proof.executable_region_sha256.clone()),
        runtime_readiness_packet_sha256: String::new(),
    }
    .with_canonical_runtime_readiness_packet_sha256()
}

/// Decide whether a Petri/MCC native successor artifact is authorized for execution.
///
/// This helper consumes the compile-artifact handoff and runtime readiness
/// evidence emitted by Trust Codegen's native install-gate path. It does not invoke code
/// or infer authority from strings: missing packet/hash/callable/runtime fields
/// remain fail-closed with stable reason codes that downstream MCC/TY
/// consumers can publish directly.
pub fn petri_native_successor_execution_authority_decision(
    input: PetriNativeSuccessorExecutionAuthorityInput<'_>,
) -> PetriNativeSuccessorExecutionAuthorityDecision {
    let Some(handoff) = input.compile_artifact_handoff else {
        return petri_native_successor_execution_authority_fail_closed(
            petri_native_successor_execution_authority_decision_base(None, input.runtime_readiness),
            "missing_compile_artifact_handoff",
            None,
            Some("compile_artifact_handoff"),
            Some(PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA),
        );
    };
    let Some(readiness) = input.runtime_readiness else {
        return petri_native_successor_execution_authority_fail_closed(
            petri_native_successor_execution_authority_decision_base(Some(handoff), None),
            "missing_runtime_readiness_packet",
            None,
            Some("runtime_readiness_packet"),
            Some(PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA),
        );
    };

    let decision =
        petri_native_successor_execution_authority_decision_base(Some(handoff), Some(readiness));

    if missing_required_text(&handoff.compile_artifact_handoff_sha256) {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "missing_compile_artifact_handoff_sha256",
            None,
            Some("compile_artifact_handoff.compile_artifact_handoff_sha256"),
            Some(PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA),
        );
    }
    if handoff.compile_artifact_handoff_sha256
        != handoff.canonical_compile_artifact_handoff_sha256()
    {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "compile_artifact_handoff_hash_mismatch",
            None,
            Some("compile_artifact_handoff.compile_artifact_handoff_sha256"),
            Some(PETRI_NATIVE_SUCCESSOR_COMPILE_ARTIFACT_HANDOFF_SCHEMA),
        );
    }
    if !handoff.is_ready() {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            handoff
                .reason_code
                .unwrap_or("compile_artifact_handoff_blocked"),
            handoff.reason_code,
            handoff.required_field,
            handoff.required_evidence,
        );
    }

    if missing_required_text(&readiness.runtime_readiness_packet_sha256) {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "missing_runtime_readiness_packet_sha256",
            None,
            Some("runtime_readiness_packet.runtime_readiness_packet_sha256"),
            Some(PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA),
        );
    }
    if readiness.runtime_readiness_packet_sha256
        != readiness.canonical_runtime_readiness_packet_sha256()
    {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "runtime_readiness_packet_hash_mismatch",
            None,
            Some("runtime_readiness_packet.runtime_readiness_packet_sha256"),
            Some(PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA),
        );
    }
    if !readiness.is_ready_for_runtime_call() {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            readiness.reason_code.unwrap_or("runtime_readiness_blocked"),
            readiness.reason_code,
            None,
            readiness.required_evidence,
        );
    }
    if missing_optional_text(readiness.call_packet_sha256.as_deref()) {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "missing_call_packet_sha256",
            None,
            Some("runtime_readiness_packet.call_packet_sha256"),
            Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
        );
    }
    if readiness
        .install_packet_hash
        .map(missing_checksum)
        .unwrap_or(true)
    {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "missing_install_packet_hash",
            None,
            Some("runtime_readiness_packet.install_packet_hash"),
            Some(NATIVE_INSTALL_GATE_PACKET_SCHEMA),
        );
    }
    if readiness
        .persisted_install_packet_hash
        .map(missing_checksum)
        .unwrap_or(true)
    {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "missing_persisted_install_packet_hash",
            None,
            Some("runtime_readiness_packet.persisted_install_packet_hash"),
            Some(NATIVE_INSTALL_GATE_PACKET_SCHEMA),
        );
    }
    if readiness.install_packet_hash != readiness.persisted_install_packet_hash {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "install_packet_hash_mismatch",
            None,
            Some("runtime_readiness_packet.install_packet_hash"),
            Some(NATIVE_INSTALL_GATE_PACKET_SCHEMA),
        );
    }
    if missing_optional_text(readiness.manifest_identity_sha256.as_deref()) {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "missing_manifest_identity_sha256",
            None,
            Some("runtime_readiness_packet.manifest_identity_sha256"),
            Some(PETRI_NATIVE_SUCCESSOR_MANIFEST_IDENTITY_SCHEMA),
        );
    }
    if !readiness.callable_authorized {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "missing_callable_authority",
            None,
            Some("runtime_readiness_packet.callable_authorized"),
            Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
        );
    }
    if missing_optional_text(readiness.native_payload_sha256.as_deref()) {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "missing_native_payload_sha256",
            None,
            Some("runtime_readiness_packet.native_payload_sha256"),
            Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
        );
    }
    if missing_optional_text(readiness.entry_symbol.as_deref()) {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "missing_entry_symbol",
            None,
            Some("runtime_readiness_packet.entry_symbol"),
            Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
        );
    }
    if readiness.callable_pointer.is_none() {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "missing_callable_pointer",
            None,
            Some("runtime_readiness_packet.callable_pointer"),
            Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
        );
    }
    if handoff.native_payload_sha256 != readiness.native_payload_sha256 {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "native_payload_sha256_mismatch",
            None,
            Some("runtime_readiness_packet.native_payload_sha256"),
            Some(PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA),
        );
    }
    if handoff.entry_symbol != readiness.entry_symbol {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "entry_symbol_mismatch",
            None,
            Some("runtime_readiness_packet.entry_symbol"),
            Some(PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA),
        );
    }
    if handoff.callable_pointer != readiness.callable_pointer {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "callable_pointer_mismatch",
            None,
            Some("runtime_readiness_packet.callable_pointer"),
            Some(PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA),
        );
    }
    if !readiness.authorizes_useful_native() {
        return petri_native_successor_execution_authority_fail_closed(
            decision,
            "runtime_readiness_not_authoritative",
            None,
            Some("runtime_readiness_packet"),
            Some(PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA),
        );
    }

    petri_native_successor_execution_authority_authorized(decision)
}

/// Select a Petri/MCC native successor artifact for production execution.
///
/// This is a pre-runtime decision boundary. It does not dereference the callable
/// pointer. It consumes Trust Codegen-owned execution authority and call-packet evidence
/// and fails closed unless install/compile artifact identity, callable-lane
/// admission, and runtime readiness all bind to one current native artifact.
pub fn petri_native_successor_production_selection_decision(
    authority: &PetriNativeSuccessorExecutionAuthorityDecision,
    call_packet: Option<&PetriNativeSuccessorCallPacket>,
) -> PetriNativeSuccessorProductionSelectionDecision {
    let execution_authority_hash_current =
        authority.execution_authority_sha256 == authority.canonical_execution_authority_sha256();
    let call_packet_hash_current = call_packet
        .is_some_and(|packet| packet.call_packet_sha256 == packet.canonical_call_packet_sha256());
    let callable_lane_admitted = authority.call_packet_available
        && authority.callable_authorized
        && call_packet.is_some_and(|packet| {
            packet.callable_authorized && !packet.fail_closed && packet.reason_code.is_none()
        });

    let mut decision = PetriNativeSuccessorProductionSelectionDecision {
        schema: PETRI_NATIVE_SUCCESSOR_PRODUCTION_SELECTION_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_PRODUCTION_SELECTION_SCHEMA_VERSION,
        status: PetriNativeSuccessorProductionSelectionStatus::FailClosed,
        selected_for_native_execution: false,
        fail_closed: true,
        reason_code: None,
        source_reason_code: None,
        required_evidence: None,
        execution_authority_sha256: authority.execution_authority_sha256.clone(),
        execution_authority_hash_current,
        call_packet_sha256: call_packet.map(|packet| packet.call_packet_sha256.clone()),
        call_packet_hash_current,
        compile_artifact_handoff_sha256: authority.compile_artifact_handoff_sha256.clone(),
        runtime_readiness_packet_sha256: authority.runtime_readiness_packet_sha256.clone(),
        compile_artifact_native_payload_sha256: authority
            .compile_artifact_native_payload_sha256
            .clone(),
        runtime_native_payload_sha256: authority.runtime_native_payload_sha256.clone(),
        call_packet_native_payload_sha256: call_packet
            .map(|packet| packet.native_payload_sha256.clone()),
        compile_artifact_entry_symbol: authority.compile_artifact_entry_symbol.clone(),
        runtime_entry_symbol: authority.runtime_entry_symbol.clone(),
        call_packet_entry_symbol: call_packet.map(|packet| packet.entry_symbol.clone()),
        compile_artifact_callable_pointer: authority.compile_artifact_callable_pointer,
        runtime_callable_pointer: authority.runtime_callable_pointer,
        call_packet_callable_pointer: call_packet.map(|packet| packet.callable_pointer),
        install_packet_hash: authority.install_packet_hash,
        persisted_install_packet_hash: authority.persisted_install_packet_hash,
        manifest_identity_sha256: authority.manifest_identity_sha256.clone(),
        callable_lane_admitted,
        runtime_ready_for_call: authority.ready_for_runtime_call,
        runtime_authorizes_useful_native: authority.runtime_authorizes_useful_native,
        vector_constant_lowering_supported: true,
        vector_constant_lowering_evidence_schema:
            PETRI_NATIVE_SUCCESSOR_VECTOR_CONSTANT_LOWERING_EVIDENCE_SCHEMA,
        vector_constant_lowering_evidence_schema_version:
            PETRI_NATIVE_SUCCESSOR_VECTOR_CONSTANT_LOWERING_EVIDENCE_SCHEMA_VERSION,
        vector_constant_lowering_status_code: "supported",
        trust_ir_shared_primitive_contract_manifest_schema:
            trust_ir::NATIVE_SHARED_PRIMITIVE_CONTRACT_MANIFEST_SCHEMA,
        trust_ir_shared_primitive_contract_manifest_schema_version:
            trust_ir::NATIVE_SHARED_PRIMITIVE_CONTRACT_MANIFEST_SCHEMA_VERSION,
        trust_ir_shared_primitive_contract_manifest_row_count:
            petri_native_successor_trust_ir_shared_primitive_contract_manifest_row_count(),
        trust_ir_shared_primitive_contract_manifest_sha256:
            petri_native_successor_trust_ir_shared_primitive_contract_manifest_sha256(),
        trust_ir_shared_primitive_contract_schema:
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR.schema,
        trust_ir_shared_primitive_readiness_report_schema:
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR
                .readiness_report_schema,
        trust_mc_admission_route_descriptor_id:
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_ID,
        trust_mc_admission_route_descriptor_schema:
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_SCHEMA,
        trust_mc_admission_route_readiness_identity_sha256:
            petri_native_successor_trust_mc_admission_route_readiness_identity_sha256(),
        trust_mc_admission_route_model_acceptance_report_api:
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR
                .model_acceptance_report_api_name,
        trust_mc_admission_route_consumer_acceptance_api:
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR.consumer_acceptance_api_name,
        production_selection_sha256: String::new(),
    };

    let fail_closed = if !execution_authority_hash_current {
        Some((
            "execution_authority_hash_mismatch",
            None,
            Some(PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA),
        ))
    } else if !authority.is_authorized_for_execution() {
        Some((
            "execution_authority_not_authorized",
            authority.reason_code,
            authority
                .required_evidence
                .or(Some(PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA)),
        ))
    } else {
        let Some(packet) = call_packet else {
            decision.required_evidence = Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA);
            return petri_native_successor_production_selection_fail_closed(
                decision,
                "call_packet_missing",
                None,
                Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
            );
        };

        if !call_packet_hash_current {
            Some((
                "call_packet_hash_mismatch",
                None,
                Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
            ))
        } else if authority.call_packet_sha256.as_deref()
            != Some(packet.call_packet_sha256.as_str())
        {
            Some((
                "call_packet_binding_mismatch",
                None,
                Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
            ))
        } else if authority.compile_artifact_native_payload_sha256.as_deref()
            != Some(packet.native_payload_sha256.as_str())
            || authority.runtime_native_payload_sha256.as_deref()
                != Some(packet.native_payload_sha256.as_str())
        {
            Some((
                "native_payload_sha256_mismatch",
                None,
                Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
            ))
        } else if authority.compile_artifact_entry_symbol.as_deref()
            != Some(packet.entry_symbol.as_str())
            || authority.runtime_entry_symbol.as_deref() != Some(packet.entry_symbol.as_str())
        {
            Some((
                "entry_symbol_mismatch",
                None,
                Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
            ))
        } else if authority.compile_artifact_callable_pointer != Some(packet.callable_pointer)
            || authority.runtime_callable_pointer != Some(packet.callable_pointer)
        {
            Some((
                "callable_pointer_mismatch",
                None,
                Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
            ))
        } else if !callable_lane_admitted {
            Some((
                "callable_lane_not_authorized",
                packet.reason_code,
                Some(PETRI_NATIVE_SUCCESSOR_CALL_PACKET_SCHEMA),
            ))
        } else if !authority.ready_for_runtime_call {
            Some((
                "runtime_not_ready",
                authority.reason_code,
                Some(PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA),
            ))
        } else if !authority.runtime_authorizes_useful_native {
            Some((
                "runtime_not_useful_native",
                authority.reason_code,
                Some(PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA),
            ))
        } else {
            None
        }
    };

    if let Some((reason_code, source_reason_code, required_evidence)) = fail_closed {
        petri_native_successor_production_selection_fail_closed(
            decision,
            reason_code,
            source_reason_code,
            required_evidence,
        )
    } else {
        decision.status = PetriNativeSuccessorProductionSelectionStatus::Selected;
        decision.selected_for_native_execution = true;
        decision.fail_closed = false;
        decision.reason_code = None;
        decision.source_reason_code = None;
        decision.required_evidence = None;
        decision.with_canonical_production_selection_sha256()
    }
}

/// Validate execution-authority manifest rows without reimplementing authority policy downstream.
pub fn validate_petri_native_successor_execution_authority_manifest_rows(
    rows: &[PetriNativeSuccessorHandoffManifestRow],
) -> PetriNativeSuccessorExecutionAuthorityManifestValidationReport {
    let entries: Vec<_> = rows
        .iter()
        .map(|row| PetriNativeSuccessorExecutionAuthorityManifestEntry {
            key: row.key,
            value: row.value.as_str(),
        })
        .collect();
    validate_petri_native_successor_execution_authority_manifest_entries(&entries, 0)
}

/// Build a stable replay identity from execution-authority manifest rows.
pub fn petri_native_successor_execution_authority_replay_identity_for_manifest_rows(
    rows: &[PetriNativeSuccessorHandoffManifestRow],
) -> PetriNativeSuccessorExecutionAuthorityReplayIdentity {
    let entries: Vec<_> = rows
        .iter()
        .map(|row| PetriNativeSuccessorExecutionAuthorityManifestEntry {
            key: row.key,
            value: row.value.as_str(),
        })
        .collect();
    petri_native_successor_execution_authority_replay_identity_from_entries(&entries, &[])
}

/// Build a compact authority summary from execution-authority manifest rows.
pub fn petri_native_successor_execution_authority_summary_for_manifest_rows(
    rows: &[PetriNativeSuccessorHandoffManifestRow],
) -> PetriNativeSuccessorExecutionAuthoritySummary {
    let entries: Vec<_> = rows
        .iter()
        .map(|row| PetriNativeSuccessorExecutionAuthorityManifestEntry {
            key: row.key,
            value: row.value.as_str(),
        })
        .collect();
    petri_native_successor_execution_authority_summary_from_entries(&entries, &[])
}

/// Validate line-oriented execution-authority `key=value` manifest evidence.
pub fn validate_petri_native_successor_execution_authority_manifest_key_value_lines<
    T: AsRef<str>,
>(
    lines: &[T],
) -> PetriNativeSuccessorExecutionAuthorityManifestValidationReport {
    let (parsed_lines, invalid_lines) =
        parse_petri_native_successor_handoff_manifest_key_value_lines(lines);
    let entries: Vec<_> = parsed_lines
        .iter()
        .map(
            |(key, value)| PetriNativeSuccessorExecutionAuthorityManifestEntry {
                key: key.as_str(),
                value: value.as_str(),
            },
        )
        .collect();
    validate_petri_native_successor_execution_authority_manifest_entries(
        &entries,
        invalid_lines.len(),
    )
}

/// Build a stable replay identity from line-oriented execution-authority manifest evidence.
pub fn petri_native_successor_execution_authority_replay_identity_for_manifest_key_value_lines<
    T: AsRef<str>,
>(
    lines: &[T],
) -> PetriNativeSuccessorExecutionAuthorityReplayIdentity {
    let (parsed_lines, invalid_lines) =
        parse_petri_native_successor_handoff_manifest_key_value_lines(lines);
    let entries: Vec<_> = parsed_lines
        .iter()
        .map(
            |(key, value)| PetriNativeSuccessorExecutionAuthorityManifestEntry {
                key: key.as_str(),
                value: value.as_str(),
            },
        )
        .collect();
    petri_native_successor_execution_authority_replay_identity_from_entries(
        &entries,
        &invalid_lines,
    )
}

/// Build a compact authority summary from line-oriented execution-authority evidence.
pub fn petri_native_successor_execution_authority_summary_for_manifest_key_value_lines<
    T: AsRef<str>,
>(
    lines: &[T],
) -> PetriNativeSuccessorExecutionAuthoritySummary {
    let (parsed_lines, invalid_lines) =
        parse_petri_native_successor_handoff_manifest_key_value_lines(lines);
    let entries: Vec<_> = parsed_lines
        .iter()
        .map(
            |(key, value)| PetriNativeSuccessorExecutionAuthorityManifestEntry {
                key: key.as_str(),
                value: value.as_str(),
            },
        )
        .collect();
    petri_native_successor_execution_authority_summary_from_entries(&entries, &invalid_lines)
}

/// Validate compact execution-authority summary rows against source authority rows.
pub fn validate_petri_native_successor_execution_authority_summary_rows(
    summary_rows: &[PetriNativeSuccessorExecutionAuthoritySummaryRow],
    authority_rows: &[PetriNativeSuccessorHandoffManifestRow],
) -> PetriNativeSuccessorExecutionAuthoritySummaryValidationReport {
    let entries = summary_rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    validate_petri_native_successor_execution_authority_summary_entries(
        entries,
        authority_rows,
        0,
        None,
    )
}

/// Validate compact line-oriented execution-authority summary `key=value` rows.
pub fn validate_petri_native_successor_execution_authority_summary_key_value_lines<
    T: AsRef<str>,
>(
    lines: &[T],
    authority_rows: &[PetriNativeSuccessorHandoffManifestRow],
) -> PetriNativeSuccessorExecutionAuthoritySummaryValidationReport {
    let (parsed_rows, invalid_lines) =
        parse_petri_native_successor_handoff_manifest_key_value_lines(lines);
    validate_petri_native_successor_execution_authority_summary_entries(
        parsed_rows,
        authority_rows,
        invalid_lines.len(),
        None,
    )
}

/// Validate a newline-delimited execution-authority summary text block.
pub fn validate_petri_native_successor_execution_authority_summary_text(
    text: &str,
    authority_rows: &[PetriNativeSuccessorHandoffManifestRow],
) -> PetriNativeSuccessorExecutionAuthoritySummaryValidationReport {
    let lines: Vec<_> = text.lines().collect();
    validate_petri_native_successor_execution_authority_summary_key_value_lines(
        &lines,
        authority_rows,
    )
}

/// Validate a compact JSON execution-authority summary object.
pub fn validate_petri_native_successor_execution_authority_summary_json_value(
    value: &serde_json::Value,
    authority_rows: &[PetriNativeSuccessorHandoffManifestRow],
) -> PetriNativeSuccessorExecutionAuthoritySummaryValidationReport {
    match petri_native_successor_execution_authority_summary_json_entries(value) {
        Ok(entries) => validate_petri_native_successor_execution_authority_summary_entries(
            entries,
            authority_rows,
            0,
            None,
        ),
        Err(reason_code) => validate_petri_native_successor_execution_authority_summary_entries(
            Vec::new(),
            authority_rows,
            0,
            Some(reason_code),
        ),
    }
}

/// Validate a compact JSON execution-authority summary string.
pub fn validate_petri_native_successor_execution_authority_summary_json_str(
    json: &str,
    authority_rows: &[PetriNativeSuccessorHandoffManifestRow],
) -> PetriNativeSuccessorExecutionAuthoritySummaryValidationReport {
    match serde_json::from_str::<serde_json::Value>(json) {
        Ok(value) => validate_petri_native_successor_execution_authority_summary_json_value(
            &value,
            authority_rows,
        ),
        Err(_) => validate_petri_native_successor_execution_authority_summary_entries(
            Vec::new(),
            authority_rows,
            0,
            Some("invalid_execution_authority_summary_json".to_owned()),
        ),
    }
}

/// Validate trust-mc admission route descriptor rows against Trust Codegen's source descriptor.
pub fn validate_petri_native_successor_trust_mc_admission_route_descriptor_rows(
    rows: &[PetriNativeSuccessorTrustMcAdmissionRouteDescriptorRow],
) -> PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationReport {
    let entries = rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    validate_petri_native_successor_trust_mc_admission_route_descriptor_entries(entries, 0, None)
}

/// Validate line-oriented trust-mc admission route descriptor `key=value` rows.
pub fn validate_petri_native_successor_trust_mc_admission_route_descriptor_key_value_lines<
    T: AsRef<str>,
>(
    lines: &[T],
) -> PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationReport {
    let (parsed_rows, invalid_lines) =
        parse_petri_native_successor_handoff_manifest_key_value_lines(lines);
    validate_petri_native_successor_trust_mc_admission_route_descriptor_entries(
        parsed_rows,
        invalid_lines.len(),
        None,
    )
}

/// Validate a newline-delimited trust-mc admission route descriptor text block.
pub fn validate_petri_native_successor_trust_mc_admission_route_descriptor_text(
    text: &str,
) -> PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationReport {
    let lines: Vec<_> = text.lines().collect();
    validate_petri_native_successor_trust_mc_admission_route_descriptor_key_value_lines(&lines)
}

/// Validate a compact JSON trust-mc admission route descriptor object.
pub fn validate_petri_native_successor_trust_mc_admission_route_descriptor_json_value(
    value: &serde_json::Value,
) -> PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationReport {
    match petri_native_successor_trust_mc_admission_route_descriptor_json_entries(value) {
        Ok(entries) => validate_petri_native_successor_trust_mc_admission_route_descriptor_entries(
            entries, 0, None,
        ),
        Err(reason_code) => {
            validate_petri_native_successor_trust_mc_admission_route_descriptor_entries(
                Vec::new(),
                0,
                Some(reason_code),
            )
        }
    }
}

/// Validate a compact JSON trust-mc admission route descriptor string.
pub fn validate_petri_native_successor_trust_mc_admission_route_descriptor_json_str(
    json: &str,
) -> PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationReport {
    match serde_json::from_str::<serde_json::Value>(json) {
        Ok(value) => {
            validate_petri_native_successor_trust_mc_admission_route_descriptor_json_value(&value)
        }
        Err(_) => validate_petri_native_successor_trust_mc_admission_route_descriptor_entries(
            Vec::new(),
            0,
            Some("invalid_trust_mc_admission_route_descriptor_json".to_owned()),
        ),
    }
}

/// Validate producer bridge descriptor rows against Trust Codegen's source descriptor.
pub fn validate_petri_native_successor_producer_bridge_descriptor_rows(
    rows: &[PetriNativeSuccessorProducerBridgeDescriptorRow],
) -> PetriNativeSuccessorProducerBridgeDescriptorValidationReport {
    let entries = rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    validate_petri_native_successor_producer_bridge_descriptor_entries(entries, 0)
}

/// Validate line-oriented producer bridge descriptor `key=value` rows.
pub fn validate_petri_native_successor_producer_bridge_descriptor_key_value_lines<T: AsRef<str>>(
    lines: &[T],
) -> PetriNativeSuccessorProducerBridgeDescriptorValidationReport {
    let (parsed_rows, invalid_lines) =
        parse_petri_native_successor_handoff_manifest_key_value_lines(lines);
    validate_petri_native_successor_producer_bridge_descriptor_entries(
        parsed_rows,
        invalid_lines.len(),
    )
}

/// Return a deterministic healthy diagnostic fixture for Petri execution-authority replay.
pub fn petri_native_successor_execution_authority_healthy_diagnostic_fixture()
-> PetriNativeSuccessorExecutionAuthorityDiagnosticFixture {
    petri_native_successor_execution_authority_diagnostic_fixture(
        "healthy",
        petri_native_successor_execution_authority_healthy_diagnostic_rows(),
    )
}

/// Return a deterministic missing-key diagnostic fixture for fail-closed replay tests.
pub fn petri_native_successor_execution_authority_incomplete_diagnostic_fixture()
-> PetriNativeSuccessorExecutionAuthorityDiagnosticFixture {
    let mut rows = petri_native_successor_execution_authority_healthy_diagnostic_rows();
    rows.retain(|row| {
        row.key
            != PetriNativeSuccessorHandoffManifestRowKind::RuntimeReadinessPacketHashCurrent
                .as_str()
    });
    petri_native_successor_execution_authority_diagnostic_fixture("incomplete", rows)
}

/// Return a deterministic stale-readiness diagnostic fixture for fail-closed replay tests.
pub fn petri_native_successor_execution_authority_stale_diagnostic_fixture()
-> PetriNativeSuccessorExecutionAuthorityDiagnosticFixture {
    let mut rows = petri_native_successor_execution_authority_healthy_diagnostic_rows();
    set_petri_native_successor_diagnostic_row(
        &mut rows,
        PetriNativeSuccessorHandoffManifestRowKind::Status,
        "fail_closed",
    );
    set_petri_native_successor_diagnostic_row(
        &mut rows,
        PetriNativeSuccessorHandoffManifestRowKind::AuthorizedForExecution,
        "false",
    );
    set_petri_native_successor_diagnostic_row(
        &mut rows,
        PetriNativeSuccessorHandoffManifestRowKind::ReasonCode,
        "runtime_readiness_packet_hash_mismatch",
    );
    set_petri_native_successor_diagnostic_row(
        &mut rows,
        PetriNativeSuccessorHandoffManifestRowKind::RequiredField,
        "runtime_readiness_packet.runtime_readiness_packet_sha256",
    );
    set_petri_native_successor_diagnostic_row(
        &mut rows,
        PetriNativeSuccessorHandoffManifestRowKind::RequiredEvidence,
        PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA,
    );
    set_petri_native_successor_diagnostic_row(
        &mut rows,
        PetriNativeSuccessorHandoffManifestRowKind::RuntimeReadinessPacketHashCurrent,
        "false",
    );
    set_petri_native_successor_diagnostic_row(
        &mut rows,
        PetriNativeSuccessorHandoffManifestRowKind::RuntimeReadinessPacketSha256,
        "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    );
    set_petri_native_successor_diagnostic_row(
        &mut rows,
        PetriNativeSuccessorHandoffManifestRowKind::AuthorizesUsefulNative,
        "false",
    );
    set_petri_native_successor_diagnostic_row(
        &mut rows,
        PetriNativeSuccessorHandoffManifestRowKind::ExecutionAuthoritySha256,
        "sha256:2020202020202020202020202020202020202020202020202020202020202020",
    );
    petri_native_successor_execution_authority_diagnostic_fixture("stale", rows)
}

/// Return the deterministic manifest for Petri execution-authority diagnostic fixtures.
pub fn petri_native_successor_execution_authority_diagnostic_fixture_manifest()
-> PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifest {
    PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifest {
        schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA,
        schema_version:
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA_VERSION,
        entries: vec![
            PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestEntry {
                fixture_name: "healthy",
                expected_validation_status:
                    PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::Accepted,
                expected_fail_closed: false,
                expected_evidence_status_code: "authorized",
                expected_reason_code: None,
                expected_authorized_for_execution: true,
                expected_native_authorizes_useful_native: true,
                exercised_schemas:
                    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_BASE_SCHEMAS,
            },
            PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestEntry {
                fixture_name: "incomplete",
                expected_validation_status:
                    PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::FailClosed,
                expected_fail_closed: true,
                expected_evidence_status_code: "authorized",
                expected_reason_code: Some("missing_required_authority_manifest_key"),
                expected_authorized_for_execution: true,
                expected_native_authorizes_useful_native: true,
                exercised_schemas:
                    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_BASE_SCHEMAS,
            },
            PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestEntry {
                fixture_name: "stale",
                expected_validation_status:
                    PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::FailClosed,
                expected_fail_closed: true,
                expected_evidence_status_code: "fail_closed",
                expected_reason_code: Some("runtime_readiness_packet_hash_mismatch"),
                expected_authorized_for_execution: false,
                expected_native_authorizes_useful_native: false,
                exercised_schemas:
                    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_STALE_SCHEMAS,
            },
        ],
    }
}

/// Validate typed diagnostic fixture manifest rows against the Trust Codegen-owned manifest.
pub fn validate_petri_native_successor_execution_authority_diagnostic_fixture_manifest_rows(
    rows: &[PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestRow],
) -> PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestValidationReport {
    let parsed_rows = rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    validate_petri_native_successor_execution_authority_diagnostic_fixture_manifest_entries(
        parsed_rows,
        0,
    )
}

/// Validate line-oriented diagnostic fixture manifest `key=value` rows.
pub fn validate_petri_native_successor_execution_authority_diagnostic_fixture_manifest_key_value_lines<
    T: AsRef<str>,
>(
    lines: &[T],
) -> PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestValidationReport {
    let (parsed_rows, invalid_lines) =
        parse_petri_native_successor_handoff_manifest_key_value_lines(lines);
    validate_petri_native_successor_execution_authority_diagnostic_fixture_manifest_entries(
        parsed_rows,
        invalid_lines.len(),
    )
}

/// Validate typed call-packet contract descriptor rows against Trust Codegen-owned metadata.
pub fn validate_petri_native_successor_call_packet_contract_descriptor_rows(
    rows: &[PetriNativeSuccessorCallPacketContractDescriptorRow],
) -> PetriNativeSuccessorCallPacketContractHealthReport {
    let parsed_rows = rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    validate_petri_native_successor_call_packet_contract_descriptor_entries(parsed_rows, 0)
}

/// Validate line-oriented call-packet contract descriptor `key=value` rows.
pub fn validate_petri_native_successor_call_packet_contract_descriptor_key_value_lines<
    T: AsRef<str>,
>(
    lines: &[T],
) -> PetriNativeSuccessorCallPacketContractHealthReport {
    let (parsed_rows, invalid_lines) =
        parse_petri_native_successor_handoff_manifest_key_value_lines(lines);
    validate_petri_native_successor_call_packet_contract_descriptor_entries(
        parsed_rows,
        invalid_lines.len(),
    )
}

/// Validate compact summary rows against a source call-packet contract health report.
pub fn validate_petri_native_successor_call_packet_contract_health_summary_rows(
    rows: &[PetriNativeSuccessorCallPacketContractDescriptorRow],
    report: &PetriNativeSuccessorCallPacketContractHealthReport,
) -> PetriNativeSuccessorCallPacketContractHealthSummaryValidationReport {
    let parsed_rows = rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    validate_petri_native_successor_call_packet_contract_health_summary_entries(
        parsed_rows,
        report,
        0,
    )
}

/// Validate compact line-oriented summary `key=value` rows against a source health report.
pub fn validate_petri_native_successor_call_packet_contract_health_summary_key_value_lines<
    T: AsRef<str>,
>(
    lines: &[T],
    report: &PetriNativeSuccessorCallPacketContractHealthReport,
) -> PetriNativeSuccessorCallPacketContractHealthSummaryValidationReport {
    let (parsed_rows, invalid_lines) =
        parse_petri_native_successor_handoff_manifest_key_value_lines(lines);
    validate_petri_native_successor_call_packet_contract_health_summary_entries(
        parsed_rows,
        report,
        invalid_lines.len(),
    )
}

/// Carry a ready Petri/MCC runtime readiness packet to a typed mock callable boundary.
///
/// This is an explicitly gated dry-run harness. It never dereferences or invokes
/// the host callable pointer. It only proves that the ready packet can be
/// carried to the call boundary with a matching call packet and first stable
/// Petri ABI buffer shape.
pub fn petri_native_successor_mock_executable_call_dry_run(
    readiness: &PetriNativeSuccessorRuntimeReadinessPacket,
    call_packet: Option<&PetriNativeSuccessorCallPacket>,
    gate: &PetriNativeSuccessorMockExecutableCallGate,
    input_state: &[u8],
    output_state: &[u8],
) -> PetriNativeSuccessorMockExecutableCallReport {
    let blocker = petri_native_successor_mock_executable_call_blocker(
        readiness,
        call_packet,
        gate,
        input_state,
        output_state,
    );
    let status = if blocker.is_some() {
        PetriNativeSuccessorMockExecutableCallStatus::Blocked
    } else {
        PetriNativeSuccessorMockExecutableCallStatus::DryRunAccepted
    };
    let callable_boundary_reached = blocker.is_none();

    PetriNativeSuccessorMockExecutableCallReport {
        schema: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA_VERSION,
        status,
        callable_boundary_reached,
        blocker,
        reason_code: blocker.map(|blocker| blocker.as_str()),
        required_evidence: blocker.map(|blocker| blocker.required_evidence()),
        gate_enabled: gate.enabled,
        gate_kind: gate.gate_kind,
        runtime_owner: gate.runtime_owner.clone(),
        runtime_readiness_packet_sha256: readiness.runtime_readiness_packet_sha256.clone(),
        call_packet_sha256: call_packet.map(|packet| packet.call_packet_sha256.clone()),
        callable_pointer: call_packet.map(|packet| packet.callable_pointer),
        input_state_bytes: input_state.len() as u64,
        expected_input_state_bytes: call_packet.map(|packet| packet.input_state_bytes),
        output_state_bytes: output_state.len() as u64,
        expected_output_state_bytes: call_packet.map(|packet| packet.output_state_bytes),
        state_encoding: call_packet.map(|packet| packet.state_encoding),
        trampoline_abi: call_packet.map(|packet| packet.trampoline_abi),
        mock_executable_call_report_sha256: String::new(),
    }
    .with_canonical_mock_executable_call_report_sha256()
}

/// Invoke a Petri/MCC native successor runtime entrypoint after Trust Codegen authority checks.
///
/// This is the real callable handoff boundary. Unlike
/// [`petri_native_successor_mock_executable_call_dry_run`], an accepted call
/// dereferences the supplied typed entrypoint and calls native code. All packet
/// hashes, pointer identities, ABI names, and state-buffer sizes must match the
/// already-authorized runtime readiness and execution authority evidence before
/// the entrypoint is invoked.
///
/// # Safety
///
/// The caller must ensure the typed entrypoint points to live executable code
/// that implements [`PetriNativeSuccessorRuntimeCallableFn`] for the whole
/// duration of this call. Trust Codegen validates the packet/evidence identity before
/// invocation, but it cannot prove the foreign function's memory safety.
pub unsafe fn petri_native_successor_call_runtime_entrypoint(
    readiness: &PetriNativeSuccessorRuntimeReadinessPacket,
    authority: &PetriNativeSuccessorExecutionAuthorityDecision,
    call_packet: &PetriNativeSuccessorCallPacket,
    entrypoint: PetriNativeSuccessorRuntimeCallableEntrypoint,
    input_state: &[u8],
    output_state: &mut [u8],
) -> PetriNativeSuccessorRuntimeCallReport {
    let blocker = petri_native_successor_runtime_call_blocker(
        readiness,
        authority,
        call_packet,
        entrypoint,
        input_state,
        output_state,
    );
    let input_state_sha256 = format!("sha256:{}", sha256_hex(input_state));
    let mut entrypoint_return_code = None;
    let mut entrypoint_status_slot = None;

    if blocker.is_none() {
        let mut status_slot = 0_u32;
        let return_code = (entrypoint.function)(
            input_state.as_ptr(),
            input_state.len() as u64,
            output_state.as_mut_ptr(),
            output_state.len() as u64,
            &mut status_slot as *mut u32,
        );
        entrypoint_return_code = Some(return_code);
        entrypoint_status_slot = Some(status_slot);
    }

    let output_state_sha256 = format!("sha256:{}", sha256_hex(output_state));
    let status = if blocker.is_some() {
        PetriNativeSuccessorRuntimeCallStatus::Blocked
    } else {
        PetriNativeSuccessorRuntimeCallStatus::Executed
    };

    PetriNativeSuccessorRuntimeCallReport {
        schema: PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_RUNTIME_CALL_SCHEMA_VERSION,
        status,
        callable_invoked: blocker.is_none(),
        blocker,
        reason_code: blocker.map(|blocker| blocker.as_str()),
        required_evidence: blocker.map(|blocker| blocker.required_evidence()),
        runtime_readiness_packet_sha256: readiness.runtime_readiness_packet_sha256.clone(),
        execution_authority_sha256: authority.execution_authority_sha256.clone(),
        call_packet_sha256: call_packet.call_packet_sha256.clone(),
        callable_pointer: entrypoint.callable_pointer,
        input_state_bytes: input_state.len() as u64,
        expected_input_state_bytes: call_packet.input_state_bytes,
        output_state_bytes: output_state.len() as u64,
        expected_output_state_bytes: call_packet.output_state_bytes,
        input_state_sha256,
        output_state_sha256,
        entrypoint_return_code,
        entrypoint_status_slot,
        state_encoding: call_packet.state_encoding,
        trampoline_abi: call_packet.trampoline_abi,
        runtime_call_report_sha256: String::new(),
    }
    .with_canonical_runtime_call_report_sha256()
}

fn petri_native_successor_runtime_call_blocker(
    readiness: &PetriNativeSuccessorRuntimeReadinessPacket,
    authority: &PetriNativeSuccessorExecutionAuthorityDecision,
    call_packet: &PetriNativeSuccessorCallPacket,
    entrypoint: PetriNativeSuccessorRuntimeCallableEntrypoint,
    input_state: &[u8],
    output_state: &[u8],
) -> Option<PetriNativeSuccessorRuntimeCallBlocker> {
    if readiness.runtime_readiness_packet_sha256
        != readiness.canonical_runtime_readiness_packet_sha256()
    {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::RuntimeReadinessHashMismatch);
    }
    if !readiness.is_ready_for_runtime_call() || !readiness.authorizes_useful_native() {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::RuntimeReadinessBlocked);
    }
    if authority.execution_authority_sha256 != authority.canonical_execution_authority_sha256() {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::ExecutionAuthorityHashMismatch);
    }
    if !authority.is_authorized_for_execution() {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::ExecutionAuthorityNotAuthorized);
    }
    if call_packet.call_packet_sha256 != call_packet.canonical_call_packet_sha256() {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::CallPacketHashMismatch);
    }
    if readiness.call_packet_sha256.as_deref() != Some(call_packet.call_packet_sha256.as_str())
        || readiness.callable_pointer != Some(call_packet.callable_pointer)
        || authority.runtime_readiness_packet_sha256.as_deref()
            != Some(readiness.runtime_readiness_packet_sha256.as_str())
        || authority.call_packet_sha256.as_deref() != Some(call_packet.call_packet_sha256.as_str())
        || authority.runtime_callable_pointer != Some(call_packet.callable_pointer)
        || authority.compile_artifact_callable_pointer != Some(call_packet.callable_pointer)
    {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::CallPacketBindingMismatch);
    }
    if entrypoint.callable_pointer != call_packet.callable_pointer {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::CallablePointerMismatch);
    }
    if call_packet.trampoline_abi != PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_ABI_STABLE_BYTES_V1 {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::TrampolineAbiMismatch);
    }
    if call_packet.state_encoding != PETRI_NATIVE_SUCCESSOR_STATE_ENCODING_STABLE_BYTES_V1 {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::StateEncodingMismatch);
    }
    if input_state.len() as u64 != call_packet.input_state_bytes {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::InputStateBytesMismatch);
    }
    if output_state.len() as u64 != call_packet.output_state_bytes {
        return Some(PetriNativeSuccessorRuntimeCallBlocker::OutputStateBytesMismatch);
    }
    None
}

fn petri_native_successor_mock_executable_call_blocker(
    readiness: &PetriNativeSuccessorRuntimeReadinessPacket,
    call_packet: Option<&PetriNativeSuccessorCallPacket>,
    gate: &PetriNativeSuccessorMockExecutableCallGate,
    input_state: &[u8],
    output_state: &[u8],
) -> Option<PetriNativeSuccessorMockExecutableCallBlocker> {
    if gate.schema != PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA
        || gate.schema_version != PETRI_NATIVE_SUCCESSOR_MOCK_EXECUTABLE_CALL_SCHEMA_VERSION
        || !gate.enabled
        || gate.gate_kind != "test_only_mock_executable_call"
        || missing_required_text(&gate.runtime_owner)
    {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::MockHarnessDisabled);
    }
    if readiness.runtime_readiness_packet_sha256
        != readiness.canonical_runtime_readiness_packet_sha256()
    {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::RuntimeReadinessHashMismatch);
    }
    if !readiness.is_ready_for_runtime_call() {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::RuntimeReadinessBlocked);
    }

    let Some(call_packet) = call_packet else {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::CallPacketMissing);
    };
    if call_packet.call_packet_sha256 != call_packet.canonical_call_packet_sha256() {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::CallPacketHashMismatch);
    }
    if readiness.call_packet_sha256.as_deref() != Some(call_packet.call_packet_sha256.as_str()) {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::CallPacketBindingMismatch);
    }
    if readiness.callable_pointer != Some(call_packet.callable_pointer) {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::CallablePointerMismatch);
    }
    if call_packet.trampoline_abi != PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_ABI_STABLE_BYTES_V1 {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::TrampolineAbiMismatch);
    }
    if call_packet.state_encoding != PETRI_NATIVE_SUCCESSOR_STATE_ENCODING_STABLE_BYTES_V1 {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::StateEncodingMismatch);
    }
    if input_state.len() as u64 != call_packet.input_state_bytes {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::InputStateBytesMismatch);
    }
    if output_state.len() as u64 != call_packet.output_state_bytes {
        return Some(PetriNativeSuccessorMockExecutableCallBlocker::OutputStateBytesMismatch);
    }
    None
}

fn petri_native_successor_executable_call_blocker(
    packet: &PetriNativeSuccessorCallPacket,
    lifetime_proof: Option<&PetriNativeSuccessorCallableLifetimeProof>,
    runtime_abi_proof: Option<&PetriNativeSuccessorRuntimeAbiProof>,
    current_generation: u64,
) -> Option<PetriNativeSuccessorExecutableCallBlocker> {
    if !packet.callable_authorized
        || packet.fail_closed
        || packet.reason_code.is_some()
        || packet.call_packet_sha256 != packet.canonical_call_packet_sha256()
        || !packet.admission_summary.actions.expose_callable
        || packet.admission_summary.actions.ty_native_activate
    {
        return Some(PetriNativeSuccessorExecutableCallBlocker::MissingCallableAuthority);
    }

    let Some(lifetime_proof) = lifetime_proof else {
        return Some(PetriNativeSuccessorExecutableCallBlocker::MissingCallableLifetimeProof);
    };
    if let Err(blocker) = lifetime_proof.binds_call_packet(packet, current_generation) {
        return Some(blocker);
    }

    let Some(runtime_abi_proof) = runtime_abi_proof else {
        return Some(PetriNativeSuccessorExecutableCallBlocker::MissingRuntimeAbiProof);
    };
    runtime_abi_proof.binds_call_packet(packet).err()
}

fn petri_native_successor_compile_artifact_handoff_blocker(
    input: PetriNativeSuccessorCompileArtifactHandoffInput<'_>,
) -> Option<PetriNativeSuccessorCompileArtifactHandoffBlocker> {
    if missing_optional_text(input.native_payload_sha256) {
        return Some(PetriNativeSuccessorCompileArtifactHandoffBlocker::MissingNativePayloadSha256);
    }
    if missing_optional_text(input.entry_symbol) {
        return Some(PetriNativeSuccessorCompileArtifactHandoffBlocker::MissingEntrySymbol);
    }
    if input.callable_pointer.is_none() {
        return Some(PetriNativeSuccessorCompileArtifactHandoffBlocker::MissingCallablePointer);
    }
    if missing_optional_text(input.executable_region_sha256) {
        return Some(
            PetriNativeSuccessorCompileArtifactHandoffBlocker::MissingExecutableRegionSha256,
        );
    }
    if missing_optional_text(input.lifetime_owner) {
        return Some(PetriNativeSuccessorCompileArtifactHandoffBlocker::MissingLifetimeOwner);
    }
    if input.current_generation.is_none() {
        return Some(PetriNativeSuccessorCompileArtifactHandoffBlocker::MissingCurrentGeneration);
    }
    None
}

fn petri_native_successor_call_packet_binds_readiness_inputs(
    call_packet: &PetriNativeSuccessorCallPacket,
    install_packet: Option<&NativeInstallGatePacket>,
    trampoline: Option<&PetriNativeSuccessorTrampolineContract>,
) -> bool {
    let (Some(install_packet), Some(trampoline)) = (install_packet, trampoline) else {
        return false;
    };

    call_packet.install_packet_hash == native_install_gate_packet_hash(install_packet)
        && call_packet.persisted_install_packet_hash == install_packet.packet_hash
        && call_packet.admission_summary.packet_hash == install_packet.packet_hash
        && call_packet.admission_summary.persisted_packet_hash == install_packet.packet_hash
        && call_packet.trampoline_sha256 == trampoline.trampoline_sha256
        && call_packet.native_payload_sha256 == trampoline.native_payload_sha256
        && call_packet.native_payload_sha256 == install_packet.artifact.native_payload_sha256
}

fn petri_native_successor_install_binding_blocker(
    packet: Option<&NativeInstallGatePacket>,
    trampoline: Option<&PetriNativeSuccessorTrampolineContract>,
) -> Option<PetriNativeSuccessorInstallBindingBlocker> {
    let Some(packet) = packet else {
        return Some(PetriNativeSuccessorInstallBindingBlocker::MissingNativeInstallGatePacket);
    };
    if let Err(blocker) = petri_native_successor_manifest_identity(Some(packet)) {
        return match blocker {
            PetriNativeSuccessorManifestIdentityBlocker::PacketHashMismatch => {
                Some(PetriNativeSuccessorInstallBindingBlocker::PacketHashMismatch)
            }
            _ => Some(PetriNativeSuccessorInstallBindingBlocker::MissingManifest),
        };
    }

    let verdict = validate_native_install_gate_packet(packet, Some(packet.packet_hash));
    if verdict.rejection_code.is_some()
        || verdict.disposition != NativeInstallGateDisposition::Installable
        || verdict.install_authority != NativeInstallGateAuthority::CanaryCallable
        || !verdict.actions.expose_callable
        || verdict.actions.ty_native_activate
        || packet.consumer != PETRI_NATIVE_SUCCESSOR_CONSUMER
        || packet.consumer_mode != PETRI_NATIVE_SUCCESSOR_CONSUMER_MODE
        || packet.surface != NativeInstallGateSurface::NativeSuccessor
    {
        return Some(PetriNativeSuccessorInstallBindingBlocker::MissingCallableAuthority);
    }

    let Some(trampoline) = trampoline else {
        return Some(PetriNativeSuccessorInstallBindingBlocker::TrampolineUnbound);
    };
    if packet
        .validation
        .layout_wrapper_identity
        .as_deref()
        .is_none()
    {
        return Some(PetriNativeSuccessorInstallBindingBlocker::TrampolineUnbound);
    }
    if !petri_native_successor_packet_binds_trampoline(packet, trampoline) {
        return Some(PetriNativeSuccessorInstallBindingBlocker::TrampolineBindingMismatch);
    }
    None
}

fn petri_native_successor_packet_binds_trampoline(
    packet: &NativeInstallGatePacket,
    trampoline: &PetriNativeSuccessorTrampolineContract,
) -> bool {
    packet.validation.layout_status == "accepted"
        && packet.validation.layout_wrapper_identity.as_deref()
            == Some(trampoline.trampoline_sha256.as_str())
        && packet.validation.layout_validation_provenance.as_deref()
            == Some("trust-cg.petri.native_successor.trampoline.v1")
        && trampoline.schema == PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA
        && trampoline.schema_version == PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_CONTRACT_SCHEMA_VERSION
        && trampoline.trampoline_abi == PETRI_NATIVE_SUCCESSOR_TRAMPOLINE_ABI_STABLE_BYTES_V1
        && trampoline.native_payload_sha256 == packet.artifact.native_payload_sha256
        && trampoline.trampoline_sha256 == trampoline.canonical_trampoline_sha256()
}

fn petri_native_successor_manifest_source(packet: &NativeInstallGatePacket) -> &'static str {
    PetriNativeSuccessorManifestIdentitySource::from_packet(packet).as_str()
}

fn petri_native_successor_manifest_identity_blocker(
    packet: &NativeInstallGatePacket,
) -> Option<PetriNativeSuccessorManifestIdentityBlocker> {
    if packet.consumer != PETRI_NATIVE_SUCCESSOR_CONSUMER {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::UnsupportedConsumer);
    }
    if packet.consumer_mode != PETRI_NATIVE_SUCCESSOR_CONSUMER_MODE {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::UnsupportedConsumerMode);
    }
    if packet.surface != NativeInstallGateSurface::NativeSuccessor {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::UnsupportedSurface);
    }
    if missing_required_text(&packet.artifact.artifact_id) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::MissingArtifactId);
    }
    if missing_checksum(packet.artifact.manifest_checksum) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::MissingManifestChecksum);
    }
    if missing_required_text(&packet.artifact.source_sha256) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::MissingSourceSha256);
    }
    if missing_required_text(&packet.artifact.trust_ir_sha256) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::MissingTrustIrSha256);
    }
    if missing_required_text(&packet.artifact.native_payload_sha256) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::MissingNativePayloadSha256);
    }
    if missing_checksum(packet.artifact.target_checksum) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::MissingTargetChecksum);
    }
    if missing_checksum(packet.artifact.abi_checksum) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::MissingAbiChecksum);
    }
    if missing_checksum(packet.artifact.layout_checksum) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::MissingLayoutChecksum);
    }
    if missing_checksum(packet.artifact.proof_policy_checksum) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::MissingProofPolicyChecksum);
    }
    if missing_checksum(packet.artifact.invalidation_checksum) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::MissingInvalidationChecksum);
    }
    if packet.packet_hash != native_install_gate_packet_hash(packet) {
        return Some(PetriNativeSuccessorManifestIdentityBlocker::PacketHashMismatch);
    }
    None
}

fn petri_native_successor_execution_plan_rejection_code(
    plan: &PetriNativeSuccessorExecutionPlan,
) -> NativeInstallGateRejectionCode {
    plan.reason_code
        .map(NativeInstallGateRejectionCode::parse_stable)
        .unwrap_or(NativeInstallGateRejectionCode::ConsumerAdmissionDenied)
}

fn petri_native_successor_expected_supported(
    expected: PetriNativeSuccessorAdmissionExpected<'_>,
) -> bool {
    expected.consumer == PETRI_NATIVE_SUCCESSOR_CONSUMER
        && expected.consumer_mode == PETRI_NATIVE_SUCCESSOR_CONSUMER_MODE
        && expected.kind == PETRI_NATIVE_SUCCESSOR_KIND
        && expected.surface == NativeInstallGateSurface::NativeSuccessor
        && (expected.requested_authority == NativeInstallGateAuthority::ValidationOnly
            || expected.requested_authority.is_callable())
}

fn petri_native_successor_rejected_summary(
    identity: &trust_ir::NativeTransportIdentity,
    expected: PetriNativeSuccessorAdmissionExpected<'_>,
    rejection_code: NativeInstallGateRejectionCode,
) -> NativeInstallGateAdmissionSummary {
    let input = petri_native_successor_gate_input(identity, expected);
    build_packet(
        &input,
        NativeInstallGateDisposition::Rejected,
        Some(rejection_code),
    )
    .admission_summary()
}

fn petri_native_successor_gate_input(
    identity: &trust_ir::NativeTransportIdentity,
    expected: PetriNativeSuccessorAdmissionExpected<'_>,
) -> NativeInstallGateInput {
    let source_digest = identity
        .source_digest
        .unwrap_or(identity.trust_ir_module_digest);
    let target_abi_digest = identity
        .target_abi
        .as_ref()
        .map(|target_abi| target_abi.digest)
        .unwrap_or(identity.bundle_digest);
    let manifest_checksum =
        petri_native_successor_checksum("petri.native_successor.manifest", identity.bundle_digest);
    let target_checksum =
        petri_native_successor_checksum("petri.native_successor.target", target_abi_digest);
    let abi_checksum =
        petri_native_successor_checksum("petri.native_successor.abi", target_abi_digest);
    let layout_checksum = petri_native_successor_checksum(
        "petri.native_successor.compiler_facts",
        identity.compiler_facts_digest,
    );
    let proof_policy_checksum =
        petri_native_successor_checksum("petri.native_successor.lineage", identity.lineage_digest);
    let invalidation_checksum = petri_native_successor_checksum(
        "petri.native_successor.transport",
        identity.stable_digest(),
    );
    let payload_identity = NativeInstallGatePayloadIdentity {
        source_sha256: petri_native_successor_sha256(
            "petri.native_successor.source",
            source_digest,
        ),
        trust_ir_sha256: petri_native_successor_sha256(
            "petri.native_successor.trust_ir_module",
            identity.trust_ir_module_digest,
        ),
        native_payload_sha256: expected
            .native_payload_sha256
            .map(str::to_owned)
            .unwrap_or_else(|| {
                petri_native_successor_sha256(
                    "petri.native_successor.bundle",
                    identity.bundle_digest,
                )
            }),
    };

    NativeInstallGateInput {
        consumer: expected.consumer.to_string(),
        consumer_mode: expected.consumer_mode.to_string(),
        surface: expected.surface,
        candidate_disposition: NativeInstallGateDisposition::Rejected,
        requested_authority: expected.requested_authority,
        manifest: None,
        manifest_reference: None,
        expected: NativeInstallGateExpectedBindings {
            artifact_id: format!("{}:{}", expected.kind, identity.bundle_digest),
            manifest_checksum,
            target_checksum,
            abi_checksum,
            layout_checksum,
            proof_policy_checksum,
            invalidation_checksum,
            current_generation: 0,
        },
        payload_identity: payload_identity.clone(),
        candidate_payload_identity: payload_identity,
        layout_evidence: None,
        proof_evidence: None,
        current_invalidation_checksum: invalidation_checksum,
        artifact_generation: 0,
        current_generation: 0,
        revoked: false,
        deny_control: None,
        replay_identity: None,
        telemetry: None,
    }
}

fn petri_native_successor_packet_binds_identity(
    packet: &NativeInstallGatePacket,
    identity: &trust_ir::NativeTransportIdentity,
    expected: PetriNativeSuccessorAdmissionExpected<'_>,
) -> bool {
    if packet.consumer != expected.consumer
        || packet.consumer_mode != expected.consumer_mode
        || packet.surface != expected.surface
        || packet.requested_authority != expected.requested_authority
    {
        return false;
    }

    let input = petri_native_successor_gate_input(identity, expected);
    let expected_artifact = artifact_packet(&input);
    packet.artifact.artifact_id == expected_artifact.artifact_id
        && packet.artifact.source_sha256 == expected_artifact.source_sha256
        && packet.artifact.trust_ir_sha256 == expected_artifact.trust_ir_sha256
        && packet.artifact.native_payload_sha256 == expected_artifact.native_payload_sha256
        && packet.artifact.target_checksum == expected_artifact.target_checksum
        && packet.artifact.abi_checksum == expected_artifact.abi_checksum
        && packet.artifact.layout_checksum == expected_artifact.layout_checksum
        && packet.artifact.proof_policy_checksum == expected_artifact.proof_policy_checksum
        && packet.artifact.invalidation_checksum == expected_artifact.invalidation_checksum
}

fn petri_native_successor_sha256(domain: &str, digest: trust_ir::ProofDigest) -> String {
    let mut out = Vec::new();
    put_str(&mut out, domain);
    put_str(&mut out, &digest.to_string());
    format!("sha256:{}", sha256_hex(&out))
}

fn petri_native_successor_checksum(
    domain: &str,
    digest: trust_ir::ProofDigest,
) -> ArtifactChecksum {
    let mut out = Vec::new();
    put_str(&mut out, domain);
    put_str(&mut out, &digest.to_string());
    ArtifactChecksum::for_bytes(&out)
}

fn petri_native_successor_sha256_parts(domain: &str, parts: &[&str]) -> String {
    let mut out = Vec::new();
    put_str(&mut out, domain);
    for part in parts {
        put_str(&mut out, part);
    }
    format!("sha256:{}", sha256_hex(&out))
}

fn petri_native_successor_layout_evidence(
    contract: &PetriNativeSuccessorCallableContract,
    trampoline: &PetriNativeSuccessorTrampolineContract,
    expected: &NativeInstallGateExpectedBindings,
) -> NativeInstallGateLayoutEvidence {
    NativeInstallGateLayoutEvidence {
        layout_checksum: expected.layout_checksum,
        abi_checksum: expected.abi_checksum,
        invalidation_checksum: expected.invalidation_checksum,
        validation_provenance: "trust-cg.petri.native_successor.trampoline.v1".to_owned(),
        evidence_sha256: None,
        wrapper_identity: Some(trampoline.trampoline_sha256.clone()),
        regions: vec![
            NativeInstallGateLayoutEvidence::region(
                "input_state",
                "petri_successor_input_state",
                1,
                contract.input_state_bytes,
                NativeInstallGateLayoutAccess::ReadOnly,
                "petri-successor-input",
                "petri_native_successor",
            ),
            NativeInstallGateLayoutEvidence::region(
                "output_state",
                "petri_successor_output_state",
                1,
                contract.output_state_bytes,
                NativeInstallGateLayoutAccess::WriteOnly,
                "petri-successor-output",
                "petri_native_successor",
            ),
            NativeInstallGateLayoutEvidence::region(
                "status",
                "petri_successor_status",
                4,
                4,
                NativeInstallGateLayoutAccess::WriteOnly,
                "petri-successor-status",
                "petri_native_successor",
            ),
        ],
        entry_abis: vec![NativeInstallGateLayoutEntryAbiEvidence {
            name: contract.entry_function.clone(),
            abi: trampoline.trampoline_abi.to_owned(),
            abi_checksum: expected.abi_checksum,
            argument_regions: vec![
                "input_state".to_owned(),
                "output_state".to_owned(),
                "status".to_owned(),
            ],
            status_region: Some("status".to_owned()),
            generation_domain: "petri_native_successor".to_owned(),
        }],
    }
    .with_canonical_evidence_sha256()
}

fn petri_native_successor_proof_evidence(
    contract: &PetriNativeSuccessorCallableContract,
    trampoline: &PetriNativeSuccessorTrampolineContract,
    expected: &NativeInstallGateExpectedBindings,
) -> NativeInstallGateProofEvidence {
    let mut summary = ProofEvidenceSummary::verified(
        "trust_ir-native-evidence-consumption",
        expected.target_checksum,
        expected.abi_checksum,
        expected.layout_checksum,
        expected.invalidation_checksum,
        expected.proof_policy_checksum,
    );
    summary.metadata.insert(
        "petri_callable_contract_sha256".to_owned(),
        contract.callable_contract_sha256.clone(),
    );
    summary.metadata.insert(
        "petri_trampoline_sha256".to_owned(),
        trampoline.trampoline_sha256.clone(),
    );
    summary.metadata.insert(
        "petri_native_payload_sha256".to_owned(),
        trampoline.native_payload_sha256.clone(),
    );

    NativeInstallGateProofEvidence {
        summary,
        proof_report_sha256: Some(petri_native_successor_sha256_parts(
            "petri.native_successor.proof_report",
            &[
                &contract.callable_contract_sha256,
                &trampoline.trampoline_sha256,
            ],
        )),
        obligation_set: Some("petri_native_successor".to_owned()),
        timeout_ms: None,
        native_payload_sha256: Some(trampoline.native_payload_sha256.clone()),
    }
}

fn petri_native_successor_replay_identity(
    contract: &PetriNativeSuccessorCallableContract,
    trampoline: &PetriNativeSuccessorTrampolineContract,
    expected: &NativeInstallGateExpectedBindings,
    payload_identity: &NativeInstallGatePayloadIdentity,
) -> NativeInstallGateReplayIdentity {
    NativeInstallGateReplayIdentity {
        schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
        replay_root_sha256: petri_native_successor_sha256_parts(
            "petri.native_successor.replay_root",
            &[
                &contract.callable_contract_sha256,
                &trampoline.trampoline_sha256,
                &expected.artifact_id,
            ],
        ),
        replay_consumer: PETRI_NATIVE_SUCCESSOR_CONSUMER.to_owned(),
        replay_family: PETRI_NATIVE_SUCCESSOR_CONSUMER_MODE.to_owned(),
        artifact_id: expected.artifact_id.clone(),
        source_sha256: payload_identity.source_sha256.clone(),
        trust_ir_sha256: payload_identity.trust_ir_sha256.clone(),
        native_payload_sha256: payload_identity.native_payload_sha256.clone(),
        replay_record_sha256: String::new(),
    }
    .with_canonical_record_sha256()
}

fn petri_native_successor_telemetry(
    contract: &PetriNativeSuccessorCallableContract,
    trampoline: &PetriNativeSuccessorTrampolineContract,
    expected: &NativeInstallGateExpectedBindings,
    proof_evidence: &Option<NativeInstallGateProofEvidence>,
    install_authority: NativeInstallGateAuthority,
) -> NativeInstallGateTelemetryInput {
    NativeInstallGateTelemetryInput {
        schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
        event_id: petri_native_successor_sha256_parts(
            "petri.native_successor.telemetry_event",
            &[
                &contract.callable_contract_sha256,
                &trampoline.trampoline_sha256,
                &expected.artifact_id,
            ],
        ),
        counter_scope: String::new(),
        record_sha256: String::new(),
        artifact_id: expected.artifact_id.clone(),
        manifest_checksum: expected.manifest_checksum,
        proof_report_sha256: proof_evidence
            .as_ref()
            .and_then(|proof| proof.proof_report_sha256.clone()),
        layout_checksum: expected.layout_checksum,
        invalidation_checksum: expected.invalidation_checksum,
        disposition: NativeInstallGateDisposition::Installable,
        rejection_code: None,
        install_authority,
        useful_native_delta: 0,
    }
    .with_canonical_record_sha256()
}

fn petri_native_successor_callable_contract_from_trust_ir_bundle(
    bundle: &trust_ir::NativeVerificationBundle,
    identity: &trust_ir::NativeTransportIdentity,
    expected: PetriNativeSuccessorExecutionExpected<'_>,
) -> Option<PetriNativeSuccessorCallableContract> {
    if petri_native_successor_callable_contract_blocker_from_trust_ir_bundle(
        bundle, identity, expected,
    )
    .is_some()
    {
        return None;
    }

    Some(petri_native_successor_callable_contract_from_identity(
        identity, expected,
    ))
}

fn petri_native_successor_callable_contract_blocker_from_trust_ir_bundle(
    bundle: &trust_ir::NativeVerificationBundle,
    identity: &trust_ir::NativeTransportIdentity,
    expected: PetriNativeSuccessorExecutionExpected<'_>,
) -> Option<PetriNativeSuccessorCallableContractBlocker> {
    if !petri_native_successor_expected_supported(expected.admission) {
        return Some(PetriNativeSuccessorCallableContractBlocker::UnsupportedExpected);
    }
    if expected.input_state_bytes == 0
        || expected.output_state_bytes == 0
        || expected.state_alignment_bytes == 0
        || !expected.state_alignment_bytes.is_power_of_two()
    {
        return Some(PetriNativeSuccessorCallableContractBlocker::InvalidStateLayout);
    }
    if missing_required_text(expected.entry_function) {
        return Some(PetriNativeSuccessorCallableContractBlocker::MissingEntryFunction);
    }

    if expected.admission.target_abi_digest.is_some_and(|digest| {
        identity.target_abi.as_ref().map(|target| target.digest) != Some(digest)
    }) {
        return Some(PetriNativeSuccessorCallableContractBlocker::TargetAbiMismatch);
    }
    if !bundle
        .module
        .functions
        .iter()
        .any(|function| function.name == expected.entry_function)
    {
        return Some(PetriNativeSuccessorCallableContractBlocker::MissingEntryFunction);
    }
    let semantic_bridge = petri_native_successor_semantic_bridge_evidence_from_trust_ir_bundle(
        bundle,
        PetriNativeSuccessorSemanticBridgeExpected::new(expected.entry_function),
    );
    if !semantic_bridge.is_ready() {
        return Some(PetriNativeSuccessorCallableContractBlocker::SemanticBridge(
            semantic_bridge.blocker.unwrap_or(
                PetriNativeSuccessorSemanticBridgeBlocker::MissingSemanticSuccessorEvidence,
            ),
        ));
    }

    None
}

fn petri_native_successor_callable_contract_from_identity(
    identity: &trust_ir::NativeTransportIdentity,
    expected: PetriNativeSuccessorExecutionExpected<'_>,
) -> PetriNativeSuccessorCallableContract {
    let input = petri_native_successor_gate_input(identity, expected.admission);
    let artifact = artifact_packet(&input);
    PetriNativeSuccessorCallableContract {
        schema: PETRI_NATIVE_SUCCESSOR_CALLABLE_CONTRACT_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_CALLABLE_CONTRACT_SCHEMA_VERSION,
        consumer: expected.admission.consumer.to_string(),
        consumer_mode: expected.admission.consumer_mode.to_string(),
        kind: expected.admission.kind.to_string(),
        surface: expected.admission.surface.as_str(),
        entry_function: expected.entry_function.to_string(),
        state_encoding: PETRI_NATIVE_SUCCESSOR_STATE_ENCODING_STABLE_BYTES_V1,
        input_state_bytes: expected.input_state_bytes,
        output_state_bytes: expected.output_state_bytes,
        state_alignment_bytes: expected.state_alignment_bytes,
        artifact_id: artifact.artifact_id,
        source_sha256: artifact.source_sha256,
        trust_ir_sha256: artifact.trust_ir_sha256,
        native_payload_sha256: artifact.native_payload_sha256,
        transport_digest: identity.stable_digest().to_string(),
        bundle_digest: identity.bundle_digest.to_string(),
        target_abi_digest: identity
            .target_abi
            .as_ref()
            .map(|target| target.digest.to_string()),
        callable_contract_sha256: String::new(),
    }
    .with_canonical_contract_sha256()
}

/// Build a non-promoting product-promotion packet for TY native-fused parent loops.
///
/// The returned packet never approves product promotion and never allows
/// useful-native credit. Any missing or mismatched parent evidence fails closed
/// with a typed reason and no packet.
pub fn native_install_gate_non_promoting_product_promotion_packet<'a, 'b>(
    manifest: &ArtifactManifestV1,
    packet: &NativeInstallGatePacket,
    citation: impl Into<Option<&'a ProofOptimizationCertificateCitation>>,
    reducer_evidence: impl Into<Option<&'b TyReducerEvidenceCoverageSummary>>,
) -> Result<NativeInstallGateProductPromotionPacket, NativeInstallGateProductPromotionRejectionReason>
{
    let Some(citation) = citation.into() else {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::MissingProofOptimizationCitation,
        );
    };
    let Some(reducer_evidence) = reducer_evidence.into() else {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::MissingReducerEvidenceBinding,
        );
    };
    validate_ty_native_fused_reducer_evidence_binding(manifest, reducer_evidence)?;
    if missing_proof_optimization_identity(&citation.validation_hash) {
        return Err(NativeInstallGateProductPromotionRejectionReason::MissingValidationHash);
    }
    if proof_optimization_citation_identity_missing(citation) {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::MissingProofOptimizationCitation,
        );
    }
    if manifest_product_promotion_requested_approved(manifest) {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::ProductPromotionRequestedApproved,
        );
    }
    validate_ty_native_fused_product_manifest(manifest)?;
    if !gate_packet_is_ty_native_fused_activation(packet, manifest) {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::GateNotTyNativeFusedActivation,
        );
    }

    let Some(gate_proof_validation_hash) = packet.validation.proof_report_sha256.as_deref() else {
        return Err(NativeInstallGateProductPromotionRejectionReason::MissingValidationHash);
    };
    if missing_required_text(gate_proof_validation_hash)
        || missing_required_text(&citation.validation_hash)
    {
        return Err(NativeInstallGateProductPromotionRejectionReason::MissingValidationHash);
    }
    if !proof_optimization_citation_matches(manifest, gate_proof_validation_hash, citation) {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::ProofOptimizationCitationMismatch,
        );
    }

    let Some(replay_identity) = packet.replay_identity.as_ref() else {
        return Err(NativeInstallGateProductPromotionRejectionReason::MissingReplayIdentity);
    };
    if missing_required_text(&replay_identity.replay_root_sha256)
        || missing_required_text(&replay_identity.replay_record_sha256)
    {
        return Err(NativeInstallGateProductPromotionRejectionReason::MissingReplayIdentity);
    }
    if !replay_identity_packet_matches(packet, replay_identity) {
        return Err(NativeInstallGateProductPromotionRejectionReason::ReplayIdentityMismatch);
    }
    if missing_checksum(packet.replay_binding.packet_hash)
        || missing_required_text(&packet.replay_binding.replay_root_sha256)
        || missing_required_text(&packet.consumer_verdict.verdict_sha256)
    {
        return Err(NativeInstallGateProductPromotionRejectionReason::MissingReplayBinding);
    }

    let Some(telemetry) = packet.telemetry.as_ref() else {
        return Err(NativeInstallGateProductPromotionRejectionReason::MissingTelemetry);
    };
    if missing_required_text(&telemetry.event_id)
        || missing_required_text(&telemetry.record_sha256)
        || missing_required_text(&telemetry.counter_scope)
    {
        return Err(NativeInstallGateProductPromotionRejectionReason::MissingTelemetry);
    }
    if telemetry.useful_native_delta != 0 {
        return Err(NativeInstallGateProductPromotionRejectionReason::UsefulNativeDeltaNonzero);
    }
    if !telemetry_packet_matches(packet, telemetry)
        || telemetry.manifest_checksum != manifest.checksum()
        || telemetry.layout_checksum != manifest.layout.checksum()
        || telemetry.invalidation_checksum != manifest.invalidation.checksum()
        || telemetry.proof_report_sha256.as_deref() != Some(gate_proof_validation_hash)
    {
        return Err(NativeInstallGateProductPromotionRejectionReason::TelemetryMismatch);
    }

    let actual_packet_hash = native_install_gate_packet_hash(packet);
    if packet.packet_hash != actual_packet_hash
        || packet.replay_binding != native_install_gate_replay_binding(packet, actual_packet_hash)
        || packet.consumer_verdict
            != native_install_gate_consumer_verdict(packet, actual_packet_hash)
    {
        return Err(NativeInstallGateProductPromotionRejectionReason::ReplayBindingMismatch);
    }

    let required_fact_bindings = ty_native_fused_product_required_fact_bindings(manifest)?;
    let mut product_packet = NativeInstallGateProductPromotionPacket {
        schema: NATIVE_INSTALL_GATE_PRODUCT_PROMOTION_PACKET_SCHEMA,
        schema_version: NATIVE_INSTALL_GATE_PRODUCT_PROMOTION_PACKET_SCHEMA_VERSION,
        issue: 800,
        artifact_id: manifest.artifact_id.clone(),
        manifest_checksum: manifest.checksum(),
        gate_packet_hash: packet.packet_hash,
        consumer: packet.consumer.clone(),
        consumer_mode: packet.consumer_mode.clone(),
        surface: packet.surface,
        product_promotion_allowed: false,
        product_promotion_disposition: TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION,
        promotion_useful_native_credit_allowed: false,
        ty_manifest_schema: manifest
            .metadata
            .get(TY_NATIVE_FUSED_MANIFEST_SCHEMA_KEY)
            .cloned()
            .unwrap_or_default(),
        status_deopt_contract: manifest
            .metadata
            .get(TY_NATIVE_FUSED_STATUS_DEOPT_CONTRACT_KEY)
            .cloned()
            .unwrap_or_default(),
        deopt_rollback_condition: manifest
            .metadata
            .get(TY_NATIVE_FUSED_DEOPT_ROLLBACK_CONDITION_KEY)
            .cloned()
            .unwrap_or_default(),
        missing_proof_disposition: manifest
            .metadata
            .get(TY_NATIVE_FUSED_MISSING_PROOF_DISPOSITION_KEY)
            .cloned()
            .unwrap_or_default(),
        useful_native_manifest_policy: manifest
            .metadata
            .get(TY_NATIVE_FUSED_USEFUL_NATIVE_POLICY_KEY)
            .cloned()
            .unwrap_or_default(),
        reducer_evidence_schema: reducer_evidence.schema.clone(),
        reducer_evidence_schema_version: reducer_evidence.schema_version,
        reducer_evidence_packet_sha256: reducer_evidence.packet_sha256.clone(),
        reducer_evidence_families: reducer_evidence.reducer_families.clone(),
        required_fact_bindings,
        parent_proof_certificate_identity: manifest
            .metadata
            .get(TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY)
            .cloned()
            .unwrap_or_default(),
        proof_optimization_function_name: citation.function_name.clone(),
        proof_optimization_certificate_id: citation.certificate_id.clone(),
        proof_optimization_proof_hash: citation.proof_hash.clone(),
        proof_optimization_validation_hash: citation.validation_hash.clone(),
        proof_optimization_source_region_hash: citation.source_region_hash.clone(),
        proof_optimization_target_region_hash: citation.target_region_hash.clone(),
        proof_optimization_transform_name: citation.transform_name.clone(),
        proof_optimization_transform_version: citation.transform_version,
        proof_optimization_admission: citation.admission.clone(),
        proof_optimization_kind: citation.kind.clone(),
        proof_optimization_status: citation.status.clone(),
        gate_proof_validation_hash: gate_proof_validation_hash.to_owned(),
        replay_identity_sha256: replay_identity.replay_record_sha256.clone(),
        replay_root_sha256: replay_identity.replay_root_sha256.clone(),
        replay_binding_packet_hash: packet.replay_binding.packet_hash,
        replay_binding_replay_root_sha256: packet.replay_binding.replay_root_sha256.clone(),
        install_consumer_verdict_sha256: packet.consumer_verdict.verdict_sha256.clone(),
        telemetry_event_id: telemetry.event_id.clone(),
        telemetry_record_sha256: telemetry.record_sha256.clone(),
        telemetry_counter_scope: telemetry.counter_scope.clone(),
        telemetry_useful_native_delta: telemetry.useful_native_delta,
        gate_useful_native_eligible: packet.actions.useful_native_eligible,
        gate_ty_native_activate: packet.actions.ty_native_activate,
        packet_sha256: String::new(),
    };
    product_packet.packet_sha256 = product_packet.canonical_packet_sha256();
    Ok(product_packet)
}

/// Validate a persisted packet against an externally stored canonical packet hash.
pub fn validate_native_install_gate_packet(
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
) -> NativeInstallGateVerdict {
    let current = NativeInstallGateRevalidationInput::from_packet(packet);
    validate_native_install_gate_packet_with_current(packet, expected_packet_hash, &current)
}

/// Validate a persisted packet against the caller's current freshness context.
pub fn validate_native_install_gate_packet_with_current(
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    current: &NativeInstallGateRevalidationInput,
) -> NativeInstallGateVerdict {
    let actual_hash = native_install_gate_packet_hash(packet);
    let mut verdict = NativeInstallGateVerdict::from_packet(packet);
    let expected_replay = native_install_gate_replay_binding(packet, actual_hash);
    let expected_consumer_verdict = native_install_gate_consumer_verdict(packet, actual_hash);

    let rejection = if packet.schema != NATIVE_INSTALL_GATE_PACKET_SCHEMA
        || packet.schema_version != NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION
    {
        Some(NativeInstallGateRejectionCode::UnsupportedSchema)
    } else if expected_packet_hash.is_none() {
        Some(NativeInstallGateRejectionCode::MissingPacketHash)
    } else if packet.packet_hash != actual_hash || expected_packet_hash != Some(actual_hash) {
        Some(NativeInstallGateRejectionCode::PacketHashMismatch)
    } else if packet.freshness.deny_control.as_ref().is_some_and(|deny| {
        !deny_control_hash_valid(deny)
            || (deny.active
                && (packet.disposition.is_installable()
                    || packet.rejection_code != Some(deny.reason.rejection_code())))
    }) {
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    } else if packet.disposition.is_installable()
        && packet
            .telemetry
            .as_ref()
            .map(|telemetry| missing_required_text(&telemetry.event_id))
            .unwrap_or(true)
    {
        Some(NativeInstallGateRejectionCode::MissingTelemetry)
    } else if !packet_actions_consistent(packet) {
        Some(NativeInstallGateRejectionCode::InconsistentActionAuthority)
    } else if packet.disposition.is_installable()
        && packet
            .telemetry
            .as_ref()
            .is_some_and(|telemetry| !telemetry_packet_matches(packet, telemetry))
    {
        Some(NativeInstallGateRejectionCode::TelemetryMismatch)
    } else if let Some(code) = ay_lra_registry_consumer_mode_rejection(
        &packet.consumer,
        packet.surface,
        &packet.consumer_mode,
    ) {
        Some(code)
    } else if packet.disposition.is_installable() && packet.replay_identity.is_none() {
        Some(NativeInstallGateRejectionCode::MissingReplayIdentity)
    } else if packet.disposition.is_installable()
        && packet
            .replay_identity
            .as_ref()
            .is_some_and(|replay| !replay_identity_packet_matches(packet, replay))
    {
        Some(NativeInstallGateRejectionCode::ReplayIdentityMismatch)
    } else if let Some(code) = persisted_packet_layout_rejection(packet, current) {
        Some(code)
    } else if let Some(code) = packet_freshness_rejection(packet, current) {
        Some(code)
    } else if persisted_packet_bindings_missing(packet)
        || packet.replay_binding != expected_replay
        || packet.consumer_verdict != expected_consumer_verdict
        || packet.telemetry.as_ref().is_some_and(|telemetry| {
            telemetry.counter_scope != native_install_gate_counter_scope(packet)
        })
    {
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    } else {
        None
    };

    if let Some(code) = rejection {
        verdict.disposition = NativeInstallGateDisposition::Rejected;
        verdict.rejection_code = Some(code);
        verdict.install_authority = NativeInstallGateAuthority::None;
        if current.deny_control.is_some() {
            verdict.deny_control = current.deny_control.clone();
        }
        verdict.actions = NativeInstallGateActions::none();
    }

    verdict
}

/// Return true only for a canonical persisted packet that carries rejection
/// telemetry without retaining any install or callable authority.
///
/// This crate-internal predicate is intentionally stricter than ordinary
/// runtime revalidation: metadata-only reporting paths have no executable
/// payload against which to re-derive positive authority, so they may retain
/// only an already canonical, fully blocked negative decision.
pub(crate) fn native_install_gate_packet_is_canonical_blocked_reporting_evidence(
    packet: &NativeInstallGatePacket,
) -> bool {
    if packet.schema != NATIVE_INSTALL_GATE_PACKET_SCHEMA
        || packet.schema_version != NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION
        || packet.disposition.is_installable()
        || packet.rejection_code.is_none()
        || packet.install_authority != NativeInstallGateAuthority::None
        || !packet.actions.all_install_authority_blocked()
        || !packet_actions_consistent(packet)
    {
        return false;
    }

    let packet_hash = native_install_gate_packet_hash(packet);
    if packet.packet_hash != packet_hash
        || persisted_packet_bindings_missing(packet)
        || packet.replay_binding != native_install_gate_replay_binding(packet, packet_hash)
        || packet.consumer_verdict != native_install_gate_consumer_verdict(packet, packet_hash)
        || packet.telemetry.as_ref().is_some_and(|telemetry| {
            !telemetry_packet_matches(packet, telemetry)
                || telemetry.counter_scope != native_install_gate_counter_scope(packet)
        })
        || packet
            .replay_identity
            .as_ref()
            .is_some_and(|replay| !replay_identity_packet_matches(packet, replay))
        || packet.freshness.deny_control.as_ref().is_some_and(|deny| {
            !deny_control_hash_valid(deny)
                || (deny.active && packet.rejection_code != Some(deny.reason.rejection_code()))
        })
    {
        return false;
    }

    validate_native_install_gate_packet(packet, Some(packet_hash))
        == NativeInstallGateVerdict::from_packet(packet)
}

/// Record runtime telemetry for a native dispatch attempt under a gate packet.
///
/// The useful-native delta is one only after a successful native call under an
/// installable verdict whose packet hash, telemetry identity, and replay
/// identity revalidate exactly. All rejected, stale, revoked, kill-switch,
/// fallback, and failed-call cases return a zero delta.
pub fn native_install_gate_runtime_telemetry(
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    current: &NativeInstallGateRevalidationInput,
    native_call_succeeded: bool,
) -> NativeInstallGateRuntimeTelemetryPacket {
    let verdict =
        validate_native_install_gate_packet_with_current(packet, expected_packet_hash, current);
    let telemetry = packet.telemetry.as_ref();
    let replay_identity = packet.replay_identity.as_ref();
    let exact_packet_identity = expected_packet_hash == Some(verdict.packet_hash)
        && packet.packet_hash == verdict.packet_hash
        && packet.replay_binding.packet_hash == verdict.packet_hash
        && verdict.replay_binding.packet_hash == verdict.packet_hash;
    let native_call_authorized = verdict.actions.expose_callable
        || verdict.actions.ay_registry_insert
        || verdict.actions.ty_native_activate;
    let useful_native_delta = u64::from(
        native_call_succeeded
            && exact_packet_identity
            && native_call_authorized
            && verdict.disposition.is_installable()
            && verdict.rejection_code.is_none()
            && verdict.actions.useful_native_eligible
            && telemetry.is_some()
            && replay_identity.is_some(),
    );
    let runtime_outcome = runtime_outcome(
        verdict.disposition,
        verdict.rejection_code,
        verdict.actions,
        native_call_succeeded,
        useful_native_delta,
    );

    NativeInstallGateRuntimeTelemetryPacket {
        schema: NATIVE_INSTALL_GATE_RUNTIME_TELEMETRY_SCHEMA,
        schema_version: NATIVE_INSTALL_GATE_RUNTIME_TELEMETRY_SCHEMA_VERSION,
        packet_hash: verdict.packet_hash,
        current_invalidation_checksum: current.current_invalidation_checksum,
        current_generation: current.current_generation,
        telemetry_event_id: verdict.telemetry_event_id.clone(),
        telemetry_record_sha256: telemetry.map(|telemetry| telemetry.record_sha256.clone()),
        counter_scope: verdict.counter_scope.clone(),
        replay_root_sha256: Some(verdict.replay_binding.replay_root_sha256.clone()),
        replay_record_sha256: replay_identity.map(|replay| replay.replay_record_sha256.clone()),
        replay_binding: verdict.replay_binding.clone(),
        consumer_verdict: verdict.consumer_verdict.clone(),
        disposition: verdict.disposition,
        rejection_code: verdict.rejection_code,
        revoked: packet.freshness.revoked || current.revoked,
        deny_control: verdict.deny_control.clone(),
        requested_authority: verdict.requested_authority,
        install_authority: verdict.install_authority,
        actions: verdict.actions,
        native_call_succeeded,
        runtime_outcome,
        useful_native_delta,
    }
}

/// Emit a structured event from an install-gate packet.
pub fn native_install_gate_structured_event(
    packet: &NativeInstallGatePacket,
) -> NativeInstallGateStructuredEvent {
    let replay_record_sha256 = packet
        .replay_identity
        .as_ref()
        .map(|replay| replay.replay_record_sha256.clone());
    build_structured_event(
        packet,
        NativeInstallGateEventSource::InstallDecision,
        structured_event_kind(
            packet.disposition,
            packet.rejection_code,
            packet.actions,
            None,
        ),
        packet.disposition,
        packet.rejection_code,
        packet.install_authority,
        packet.actions,
        None,
        packet
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.useful_native_delta)
            .unwrap_or(0),
        replay_record_sha256,
        None,
    )
}

/// Emit a structured event from a runtime native dispatch attempt.
pub fn native_install_gate_runtime_structured_event(
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    current: &NativeInstallGateRevalidationInput,
    native_call_succeeded: bool,
) -> NativeInstallGateStructuredEvent {
    let runtime = native_install_gate_runtime_telemetry(
        packet,
        expected_packet_hash,
        current,
        native_call_succeeded,
    );
    build_structured_event(
        packet,
        NativeInstallGateEventSource::RuntimeCall,
        structured_event_kind(
            runtime.disposition,
            runtime.rejection_code,
            runtime.actions,
            Some(runtime.native_call_succeeded),
        ),
        runtime.disposition,
        runtime.rejection_code,
        runtime.install_authority,
        runtime.actions,
        Some(runtime.native_call_succeeded),
        runtime.useful_native_delta,
        runtime.replay_record_sha256,
        None,
    )
}

/// Emit a structured event from ay/TY consumer admission.
pub fn native_install_gate_consumer_admission_structured_event(
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    current: &NativeInstallGateRevalidationInput,
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
) -> NativeInstallGateStructuredEvent {
    let admission =
        native_install_gate_consumer_admission(packet, expected_packet_hash, current, evidence);
    let replay_record_sha256 = packet
        .replay_identity
        .as_ref()
        .map(|replay| replay.replay_record_sha256.clone());
    build_structured_event(
        packet,
        NativeInstallGateEventSource::ConsumerAdmission,
        structured_event_kind(
            admission.disposition,
            admission.rejection_code,
            admission.actions,
            None,
        ),
        admission.disposition,
        admission.rejection_code,
        admission.install_authority,
        admission.actions,
        None,
        admission.telemetry.useful_native_delta,
        replay_record_sha256,
        admission.telemetry.admission_evidence_sha256,
    )
}

/// Emit a fail-closed structured event for a shadow replay mismatch.
pub fn native_install_gate_shadow_mismatch_event(
    packet: &NativeInstallGatePacket,
    mismatch_sha256: impl Into<String>,
) -> NativeInstallGateStructuredEvent {
    let replay_record_sha256 = packet
        .replay_identity
        .as_ref()
        .map(|replay| replay.replay_record_sha256.clone());
    build_structured_event(
        packet,
        NativeInstallGateEventSource::ShadowReplay,
        NativeInstallGateEventKind::ShadowMismatch,
        NativeInstallGateDisposition::Rejected,
        Some(NativeInstallGateRejectionCode::ShadowOnlyNonInstallable),
        NativeInstallGateAuthority::None,
        NativeInstallGateActions::none(),
        Some(false),
        0,
        replay_record_sha256,
        Some(mismatch_sha256.into()),
    )
}

/// Return the exact consumer allowlist tuple key for a packet admission surface.
pub fn native_install_gate_consumer_allowlist_key(
    packet: &NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
) -> Option<String> {
    match (packet.consumer.as_str(), packet.surface) {
        ("ay", NativeInstallGateSurface::AYRegistry) => Some(format!(
            "ay:{}:{}:{}:{}:{}:{}",
            packet.consumer_mode,
            packet.artifact.target_checksum,
            packet.artifact.proof_policy_checksum,
            packet.artifact.layout_checksum,
            packet.artifact.invalidation_checksum,
            current.current_generation
        )),
        ("ty", NativeInstallGateSurface::TyActivation) => Some(format!(
            "ty:{}:{}:{}:{}:{}:{}",
            packet.consumer_mode,
            packet.artifact.artifact_id,
            packet.artifact.target_checksum,
            packet.artifact.layout_checksum,
            packet.artifact.invalidation_checksum,
            current.current_generation
        )),
        _ => None,
    }
}

/// Validate consumer admission before ay registry insertion or TY activation.
///
/// This call consumes a persisted shared install-gate packet, the caller's live
/// freshness context, and a consumer-side verdict. It authorizes only the two
/// consumer admission surfaces and keeps useful-native accounting at zero; a
/// successful native call must still be recorded through runtime telemetry.
pub fn native_install_gate_consumer_admission(
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    current: &NativeInstallGateRevalidationInput,
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
) -> NativeInstallGateConsumerAdmissionDecision {
    let packet_verdict =
        validate_native_install_gate_packet_with_current(packet, expected_packet_hash, current);
    let admission_rejection =
        consumer_admission_rejection(packet, current, evidence, &packet_verdict);
    let mut disposition = packet_verdict.disposition;
    let mut rejection_code = packet_verdict.rejection_code;
    let mut install_authority = packet_verdict.install_authority;
    let mut actions = packet_verdict.actions;

    if let Some(code) = admission_rejection {
        disposition = NativeInstallGateDisposition::Rejected;
        rejection_code = Some(code);
        install_authority = NativeInstallGateAuthority::None;
        actions = NativeInstallGateActions::none();
    }

    if !disposition.is_installable() {
        install_authority = NativeInstallGateAuthority::None;
        actions = NativeInstallGateActions::none();
    }

    let telemetry = consumer_admission_telemetry(
        packet,
        current,
        evidence,
        &packet_verdict,
        disposition,
        rejection_code,
        actions,
    );

    NativeInstallGateConsumerAdmissionDecision {
        disposition,
        rejection_code,
        requested_authority: packet_verdict.requested_authority,
        install_authority,
        packet_hash: packet_verdict.packet_hash,
        consumer: packet.consumer.clone(),
        consumer_mode: packet.consumer_mode.clone(),
        surface: packet.surface,
        actions,
        telemetry,
    }
}

fn consumer_admission_rejection(
    packet: &NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
    packet_verdict: &NativeInstallGateVerdict,
) -> Option<NativeInstallGateRejectionCode> {
    if !packet_verdict.disposition.is_installable() || packet_verdict.rejection_code.is_some() {
        return None;
    }
    let expected_actions = NativeInstallGateActions::for_surface(packet.surface);
    if packet_verdict.actions != expected_actions
        || !matches!(
            (packet.consumer.as_str(), packet.surface),
            ("ay", NativeInstallGateSurface::AYRegistry)
                | ("ty", NativeInstallGateSurface::TyActivation)
        )
    {
        return Some(NativeInstallGateRejectionCode::UnsupportedConsumer);
    }
    let Some(expected_allowlist_key) = native_install_gate_consumer_allowlist_key(packet, current)
    else {
        return Some(NativeInstallGateRejectionCode::UnsupportedConsumer);
    };
    if evidence.consumer != packet.consumer
        || evidence.consumer_mode != packet.consumer_mode
        || evidence.surface != packet.surface
    {
        return Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
    }
    if consumer_admission_evidence_missing(evidence)
        || evidence.evidence_sha256 != evidence.canonical_evidence_sha256()
    {
        return Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
    }
    if evidence.allowlist_key != expected_allowlist_key {
        return Some(NativeInstallGateRejectionCode::UnsupportedConsumer);
    }
    if evidence.target_checksum != packet.artifact.target_checksum {
        return Some(NativeInstallGateRejectionCode::TargetMismatch);
    }
    if evidence.proof_policy_checksum != packet.artifact.proof_policy_checksum {
        return Some(NativeInstallGateRejectionCode::ProofMissingEvidence);
    }
    if evidence.layout_checksum != packet.artifact.layout_checksum {
        return Some(NativeInstallGateRejectionCode::LayoutMismatch);
    }
    if evidence.invalidation_checksum != packet.artifact.invalidation_checksum
        || evidence.invalidation_checksum != current.current_invalidation_checksum
        || evidence.runtime_generation != current.current_generation
        || evidence.runtime_generation != packet.freshness.current_generation
    {
        return Some(NativeInstallGateRejectionCode::StaleInvalidation);
    }

    let Some(telemetry) = packet.telemetry.as_ref() else {
        return Some(NativeInstallGateRejectionCode::MissingTelemetry);
    };
    if evidence.telemetry_event_id != telemetry.event_id
        || evidence.telemetry_counter_scope != telemetry.counter_scope
        || evidence.telemetry_record_sha256 != telemetry.record_sha256
    {
        return Some(NativeInstallGateRejectionCode::TelemetryMismatch);
    }
    if evidence.replay_root_sha256 != packet.replay_binding.replay_root_sha256 {
        return Some(NativeInstallGateRejectionCode::ReplayIdentityMismatch);
    }
    if evidence.install_consumer_verdict_sha256 != packet.consumer_verdict.verdict_sha256 {
        return Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
    }

    match (packet.consumer.as_str(), packet.surface) {
        ("ay", NativeInstallGateSurface::AYRegistry)
            if !evidence.rollback_ready || !evidence.deopt_ready =>
        {
            Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
        }
        ("ty", NativeInstallGateSurface::TyActivation)
            if !evidence.rollback_ready || !evidence.status_ready || !evidence.deopt_ready =>
        {
            Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
        }
        _ => None,
    }
}

fn consumer_admission_evidence_missing(
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
) -> bool {
    missing_required_text(&evidence.consumer)
        || missing_required_text(&evidence.consumer_mode)
        || missing_required_text(&evidence.allowlist_key)
        || missing_required_text(&evidence.telemetry_event_id)
        || missing_required_text(&evidence.telemetry_counter_scope)
        || missing_required_text(&evidence.telemetry_record_sha256)
        || missing_required_text(&evidence.replay_root_sha256)
        || missing_required_text(&evidence.install_consumer_verdict_sha256)
        || missing_required_text(&evidence.evidence_sha256)
        || missing_checksum(evidence.target_checksum)
        || missing_checksum(evidence.proof_policy_checksum)
        || missing_checksum(evidence.layout_checksum)
        || missing_checksum(evidence.invalidation_checksum)
}

fn consumer_admission_telemetry(
    packet: &NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
    packet_verdict: &NativeInstallGateVerdict,
    disposition: NativeInstallGateDisposition,
    rejection_code: Option<NativeInstallGateRejectionCode>,
    actions: NativeInstallGateActions,
) -> NativeInstallGateConsumerAdmissionTelemetryPacket {
    let telemetry = packet.telemetry.as_ref();
    NativeInstallGateConsumerAdmissionTelemetryPacket {
        schema: NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA,
        schema_version: NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA_VERSION,
        packet_hash: native_install_gate_packet_hash(packet),
        telemetry_event_id: telemetry.map(|telemetry| telemetry.event_id.clone()),
        telemetry_record_sha256: telemetry.map(|telemetry| telemetry.record_sha256.clone()),
        counter_scope: telemetry
            .map(|telemetry| telemetry.counter_scope.clone())
            .unwrap_or_else(|| native_install_gate_counter_scope(packet)),
        replay_root_sha256: Some(packet.replay_binding.replay_root_sha256.clone()),
        install_consumer_verdict_sha256: Some(packet.consumer_verdict.verdict_sha256.clone()),
        admission_evidence_sha256: Some(evidence.evidence_sha256.clone()),
        disposition,
        rejection_code,
        revoked: packet.freshness.revoked || current.revoked,
        deny_control: packet_verdict.deny_control.clone(),
        actions,
        useful_native_delta: 0,
    }
}

/// Refresh packet hash, replay binding, consumer verdict, and telemetry counter scope.
///
/// This is useful for tests and data-only fixture builders that construct
/// `NativeInstallGatePacket` values directly. Production validators still
/// fail closed if any persisted binding is missing, stale, or inconsistent.
pub fn persist_native_install_gate_packet_bindings(packet: &mut NativeInstallGatePacket) {
    let counter_scope = native_install_gate_counter_scope(packet);
    if let Some(telemetry) = &mut packet.telemetry {
        telemetry.counter_scope = counter_scope;
        telemetry.record_sha256 = telemetry.canonical_record_sha256();
    }
    if let Some(replay_identity) = &mut packet.replay_identity {
        replay_identity.replay_record_sha256 = replay_identity.canonical_record_sha256();
    }
    let packet_hash = native_install_gate_packet_hash(packet);
    packet.packet_hash = packet_hash;
    packet.replay_binding = native_install_gate_replay_binding(packet, packet_hash);
    packet.consumer_verdict = native_install_gate_consumer_verdict(packet, packet_hash);
}

fn validate_ty_native_fused_product_manifest(
    manifest: &ArtifactManifestV1,
) -> Result<(), NativeInstallGateProductPromotionRejectionReason> {
    if !is_ty_native_fused_manifest(manifest) {
        return Err(NativeInstallGateProductPromotionRejectionReason::ManifestMissingTyFusedSchema);
    }
    if manifest
        .metadata
        .get(TY_NATIVE_FUSED_STATUS_DEOPT_CONTRACT_KEY)
        .map(String::as_str)
        != Some(TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT)
        || manifest
            .layout
            .metadata
            .get(TY_NATIVE_FUSED_STATUS_DEOPT_CONTRACT_KEY)
            .map(String::as_str)
            != Some(TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT)
        || manifest
            .invalidation
            .extra
            .get(TY_NATIVE_FUSED_STATUS_DEOPT_CONTRACT_KEY)
            .map(String::as_str)
            != Some(TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT)
    {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::ManifestMissingStatusDeoptContract,
        );
    }
    if manifest
        .metadata
        .get(TY_NATIVE_FUSED_DEOPT_ROLLBACK_CONDITION_KEY)
        .map(String::as_str)
        != Some(TY_NATIVE_FUSED_DEOPT_ROLLBACK_CONDITION)
        || manifest
            .metadata
            .get(TY_NATIVE_FUSED_MISSING_PROOF_DISPOSITION_KEY)
            .map(String::as_str)
            != Some(TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION)
        || manifest
            .metadata
            .get(TY_NATIVE_FUSED_USEFUL_NATIVE_POLICY_KEY)
            .map(String::as_str)
            != Some(TY_NATIVE_FUSED_USEFUL_NATIVE_FALSE_UNTIL_GATE)
    {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::ManifestMissingRollbackMetadata,
        );
    }
    let Some(kernel_identity) = manifest
        .metadata
        .get(TY_NATIVE_FUSED_KERNEL_IDENTITY_KEY)
        .map(String::as_str)
    else {
        return Err(NativeInstallGateProductPromotionRejectionReason::ManifestMissingTyFusedSchema);
    };
    if missing_required_text(kernel_identity)
        || manifest
            .layout
            .metadata
            .get(TY_NATIVE_FUSED_KERNEL_IDENTITY_KEY)
            .map(String::as_str)
            != Some(kernel_identity)
        || manifest
            .invalidation
            .extra
            .get(TY_NATIVE_FUSED_KERNEL_IDENTITY_KEY)
            .map(String::as_str)
            != Some(kernel_identity)
    {
        return Err(NativeInstallGateProductPromotionRejectionReason::ManifestMissingTyFusedSchema);
    }
    ty_native_fused_product_required_fact_bindings(manifest).map(|_| ())
}

fn validate_ty_native_fused_reducer_evidence_binding(
    manifest: &ArtifactManifestV1,
    summary: &TyReducerEvidenceCoverageSummary,
) -> Result<(), NativeInstallGateProductPromotionRejectionReason> {
    if summary.schema != TY_REDUCER_EVIDENCE_PACKET_SCHEMA
        || summary.schema_version != TY_REDUCER_EVIDENCE_PACKET_SCHEMA_VERSION
        || missing_required_text(&summary.packet_sha256)
    {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::MissingReducerEvidenceBinding,
        );
    }
    if !summary.packet_sha256.starts_with("sha256:") {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::ReducerEvidenceBindingMismatch,
        );
    }

    let mut families = summary.reducer_families.clone();
    families.sort();
    families.dedup();
    let expected = TY_REDUCER_REQUIRED_EVIDENCE_FAMILIES
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if families.len() != expected.len()
        || !expected.iter().all(|family| {
            families
                .binary_search_by(|candidate| candidate.as_str().cmp(family))
                .is_ok()
        })
    {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::ReducerEvidenceCoverageIncomplete,
        );
    }

    let Some(manifest_schema) = manifest
        .metadata
        .get(TY_REDUCER_EVIDENCE_SCHEMA_METADATA_KEY)
        .map(String::as_str)
    else {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::MissingReducerEvidenceBinding,
        );
    };
    let Some(manifest_schema_version) = manifest
        .metadata
        .get(TY_REDUCER_EVIDENCE_SCHEMA_VERSION_METADATA_KEY)
        .map(String::as_str)
    else {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::MissingReducerEvidenceBinding,
        );
    };
    let Some(manifest_packet_sha256) = manifest
        .metadata
        .get(TY_REDUCER_EVIDENCE_PACKET_SHA256_METADATA_KEY)
        .map(String::as_str)
    else {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::MissingReducerEvidenceBinding,
        );
    };
    let Some(manifest_families) = manifest
        .metadata
        .get(TY_REDUCER_EVIDENCE_FAMILIES_METADATA_KEY)
        .map(String::as_str)
    else {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::MissingReducerEvidenceBinding,
        );
    };
    let Ok(manifest_schema_version) = manifest_schema_version.parse::<u32>() else {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::MissingReducerEvidenceBinding,
        );
    };
    if manifest_schema != summary.schema
        || manifest_schema_version != summary.schema_version
        || manifest_packet_sha256 != summary.packet_sha256
        || manifest_families != families.join(",")
    {
        return Err(
            NativeInstallGateProductPromotionRejectionReason::ReducerEvidenceBindingMismatch,
        );
    }

    Ok(())
}

fn ty_native_fused_product_required_fact_bindings(
    manifest: &ArtifactManifestV1,
) -> Result<
    Vec<NativeInstallGateProductPromotionRequiredFactBinding>,
    NativeInstallGateProductPromotionRejectionReason,
> {
    let mut bindings = Vec::with_capacity(TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA.len());
    for (evidence_key, fact) in TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA {
        let manifest_key = format!("required_fact.{fact}");
        let manifest_metadata_value = manifest.metadata.get(&manifest_key).cloned().ok_or(
            NativeInstallGateProductPromotionRejectionReason::ManifestMissingRequiredFacts,
        )?;
        let invalidation_metadata_value = manifest
            .invalidation
            .extra
            .get(&manifest_key)
            .cloned()
            .ok_or(
            NativeInstallGateProductPromotionRejectionReason::ManifestMissingRequiredFacts,
        )?;
        if manifest_metadata_value != *evidence_key || invalidation_metadata_value != *evidence_key
        {
            return Err(
                NativeInstallGateProductPromotionRejectionReason::ManifestMissingRequiredFacts,
            );
        }
        bindings.push(NativeInstallGateProductPromotionRequiredFactBinding {
            evidence_metadata_key: evidence_key,
            fact,
            manifest_metadata_value,
            invalidation_metadata_value,
        });
    }
    Ok(bindings)
}

fn gate_packet_is_ty_native_fused_activation(
    packet: &NativeInstallGatePacket,
    manifest: &ArtifactManifestV1,
) -> bool {
    packet.schema == NATIVE_INSTALL_GATE_PACKET_SCHEMA
        && packet.schema_version == NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION
        && packet.consumer == "ty"
        && packet.consumer_mode == TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE
        && packet.surface == NativeInstallGateSurface::TyActivation
        && packet.disposition == NativeInstallGateDisposition::Installable
        && packet.rejection_code.is_none()
        && packet.install_authority == packet.requested_authority
        && packet.install_authority.is_callable()
        && packet.actions.ty_native_activate
        && packet.actions.useful_native_eligible
        && packet.artifact.artifact_id == manifest.artifact_id
        && packet.artifact.manifest_checksum == manifest.checksum()
        && packet.artifact.target_checksum == manifest.target.checksum()
        && packet.artifact.abi_checksum == manifest.abi.checksum()
        && packet.artifact.layout_checksum == manifest.layout.checksum()
        && packet.artifact.proof_policy_checksum == manifest.proof_policy.checksum()
        && packet.artifact.invalidation_checksum == manifest.invalidation.checksum()
}

fn proof_optimization_citation_matches(
    manifest: &ArtifactManifestV1,
    gate_proof_validation_hash: &str,
    citation: &ProofOptimizationCertificateCitation,
) -> bool {
    if citation.validation_hash != gate_proof_validation_hash {
        return false;
    }
    if citation.status != "applied"
        || citation.rejection_code.is_some()
        || citation.rejection_fact.is_some()
        || citation.rejection_detail.is_some()
        || citation.transform_name != TY_NATIVE_FUSED_PROOF_OPT_TRANSFORM_NAME
        || citation.transform_version != TY_NATIVE_FUSED_PROOF_OPT_TRANSFORM_VERSION
        || citation.admission != TY_NATIVE_FUSED_PROOF_OPT_ADMISSION
        || citation.kind != TY_NATIVE_FUSED_PROOF_OPT_KIND
        || !proof_optimization_citation_consumes_ty_required_facts(citation)
    {
        return false;
    }
    let Some(canonical_certificate_identity) =
        ty_native_fused_canonical_certificate_identity(manifest)
    else {
        return false;
    };
    let Some(parent_certificate_identity) = manifest
        .metadata
        .get(TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY)
        .map(String::as_str)
    else {
        return false;
    };
    if missing_required_text(parent_certificate_identity)
        || parent_certificate_identity != canonical_certificate_identity.as_str()
        || citation.certificate_id.as_str() != canonical_certificate_identity.as_str()
    {
        return false;
    }
    let Some(kernel_identity) = manifest
        .metadata
        .get(TY_NATIVE_FUSED_KERNEL_IDENTITY_KEY)
        .map(String::as_str)
    else {
        return false;
    };
    citation.function_name == kernel_identity
        || manifest
            .symbols
            .iter()
            .any(|symbol| symbol.name == citation.function_name)
}

fn proof_optimization_citation_identity_missing(
    citation: &ProofOptimizationCertificateCitation,
) -> bool {
    missing_required_text(&citation.function_name)
        || missing_proof_optimization_identity(&citation.certificate_id)
        || missing_proof_optimization_identity(&citation.proof_hash)
        || missing_proof_optimization_identity(&citation.validation_hash)
        || missing_proof_optimization_identity(&citation.source_region_hash)
        || missing_proof_optimization_identity(&citation.target_region_hash)
        || missing_required_text(&citation.transform_name)
        || missing_required_text(&citation.status)
}

fn missing_proof_optimization_identity(value: &str) -> bool {
    let value = value.trim();
    value.is_empty() || value.chars().all(|ch| ch == '0')
}

fn proof_optimization_citation_consumes_ty_required_facts(
    citation: &ProofOptimizationCertificateCitation,
) -> bool {
    TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA
        .iter()
        .all(|(metadata_key, fact)| {
            citation.consumed_facts.iter().any(|consumed| {
                consumed.name == *fact && consumed.payload.as_deref() == Some(*metadata_key)
            })
        })
}

fn manifest_product_promotion_requested_approved(manifest: &ArtifactManifestV1) -> bool {
    [
        "product_promotion_approved",
        "product_promotion_requested_approved",
        "product_promotion",
        "promotion_disposition",
    ]
    .iter()
    .any(|key| {
        manifest
            .metadata
            .get(*key)
            .is_some_and(|value| product_promotion_value_is_approved(value))
    })
}

fn product_promotion_value_is_approved(value: &str) -> bool {
    let value = value.trim().to_ascii_lowercase();
    matches!(
        value.as_str(),
        "true" | "approved" | "promoted" | "useful_native_promoted" | "product_promotion_approved"
    )
}

fn validate_decision(
    input: &NativeInstallGateInput,
) -> (
    NativeInstallGateDisposition,
    Option<NativeInstallGateRejectionCode>,
) {
    if !matches!(input.consumer.as_str(), "ay" | "ty") {
        return reject(NativeInstallGateRejectionCode::UnsupportedConsumer);
    }
    if let Some(code) = ay_lra_registry_consumer_mode_rejection(
        &input.consumer,
        input.surface,
        &input.consumer_mode,
    ) {
        return reject(code);
    }

    if let Some(deny_control) = &input.deny_control {
        match validate_deny_control(input, deny_control) {
            Ok(Some(code)) => return reject(code),
            Ok(None) => {}
            Err(code) => return reject(code),
        }
    }

    match input.candidate_disposition {
        NativeInstallGateDisposition::Installable => {}
        NativeInstallGateDisposition::ProfileOnly => {
            return (
                NativeInstallGateDisposition::ProfileOnly,
                Some(NativeInstallGateRejectionCode::ProfileOnlyNonInstallable),
            );
        }
        NativeInstallGateDisposition::ReplayOnly => {
            return (
                NativeInstallGateDisposition::ReplayOnly,
                Some(NativeInstallGateRejectionCode::ReplayOnlyNonInstallable),
            );
        }
        NativeInstallGateDisposition::ShadowOnly => {
            return (
                NativeInstallGateDisposition::ShadowOnly,
                Some(NativeInstallGateRejectionCode::ShadowOnlyNonInstallable),
            );
        }
        NativeInstallGateDisposition::Rejected => {
            return reject(NativeInstallGateRejectionCode::ArtifactIdentityMismatch);
        }
    }

    if !input.requested_authority.is_callable() {
        return reject(NativeInstallGateRejectionCode::InconsistentActionAuthority);
    }

    let Some(manifest) = &input.manifest else {
        return reject(NativeInstallGateRejectionCode::MissingManifest);
    };
    let Some(reference) = &input.manifest_reference else {
        return reject(NativeInstallGateRejectionCode::MissingManifest);
    };

    if let Err(code) = validate_required_manifest_fields(input, manifest, reference) {
        return reject(code);
    }

    if manifest.schema != JIT_ARTIFACT_MANIFEST_SCHEMA
        || manifest.schema_version != JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION
        || reference.schema != JIT_ARTIFACT_MANIFEST_SCHEMA
        || reference.schema_version != JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION
    {
        return reject(NativeInstallGateRejectionCode::UnsupportedSchema);
    }

    if reference.artifact_id != manifest.artifact_id
        || manifest.artifact_id != input.expected.artifact_id
    {
        return reject(NativeInstallGateRejectionCode::ArtifactIdentityMismatch);
    }

    let manifest_checksum = manifest.checksum();
    if reference.manifest_checksum != manifest_checksum
        || manifest_checksum != input.expected.manifest_checksum
    {
        return reject(NativeInstallGateRejectionCode::ManifestChecksumMismatch);
    }
    if reference.target_checksum != manifest.target.checksum()
        || reference.target_checksum != input.expected.target_checksum
    {
        return reject(NativeInstallGateRejectionCode::TargetMismatch);
    }
    if reference.abi_checksum != manifest.abi.checksum()
        || reference.abi_checksum != input.expected.abi_checksum
    {
        return reject(NativeInstallGateRejectionCode::AbiMismatch);
    }
    if reference.layout_checksum != manifest.layout.checksum()
        || reference.layout_checksum != input.expected.layout_checksum
    {
        return reject(NativeInstallGateRejectionCode::LayoutMismatch);
    }
    if reference.proof_policy_checksum != manifest.proof_policy.checksum()
        || reference.proof_policy_checksum != input.expected.proof_policy_checksum
    {
        return reject(NativeInstallGateRejectionCode::ProofMissingEvidence);
    }
    if reference.invalidation_checksum != manifest.invalidation.checksum()
        || reference.invalidation_checksum != input.expected.invalidation_checksum
    {
        return reject(NativeInstallGateRejectionCode::StaleInvalidation);
    }

    if input.payload_identity != input.candidate_payload_identity {
        return reject(NativeInstallGateRejectionCode::ArtifactIdentityMismatch);
    }

    let Some(layout_evidence) = &input.layout_evidence else {
        return reject(NativeInstallGateRejectionCode::MissingLayoutEvidence);
    };
    if let Err(code) = validate_layout_evidence(input, layout_evidence) {
        return reject(code);
    }

    let Some(proof_evidence) = &input.proof_evidence else {
        return reject(NativeInstallGateRejectionCode::ProofMissingEvidence);
    };
    if proof_evidence_required_fields_missing(proof_evidence) {
        return reject(NativeInstallGateRejectionCode::ProofMissingEvidence);
    }
    match validate_proof(manifest, proof_evidence) {
        Ok(()) => {}
        Err(code) => return reject(code),
    }
    match validate_ty_native_fused_proof_metadata(input, manifest, proof_evidence) {
        Ok(()) => {}
        Err(code) => return reject(code),
    }
    match validate_ay_lra_registry_proof_metadata(input, proof_evidence) {
        Ok(()) => {}
        Err(code) => return reject(code),
    }
    if proof_evidence
        .native_payload_sha256
        .as_ref()
        .is_some_and(|hash| {
            hash != &input.candidate_payload_identity.native_payload_sha256
                || hash != &input.payload_identity.native_payload_sha256
        })
    {
        return reject(NativeInstallGateRejectionCode::ArtifactIdentityMismatch);
    }

    if input.current_invalidation_checksum != input.expected.invalidation_checksum
        || input.current_generation != input.expected.current_generation
        || input.artifact_generation != input.current_generation
    {
        return reject(NativeInstallGateRejectionCode::StaleInvalidation);
    }

    if input.revoked {
        return reject(NativeInstallGateRejectionCode::RevokedArtifact);
    }

    let Some(replay_identity) = &input.replay_identity else {
        return reject(NativeInstallGateRejectionCode::MissingReplayIdentity);
    };
    if !replay_identity_matches(input, replay_identity) {
        return reject(NativeInstallGateRejectionCode::ReplayIdentityMismatch);
    }

    let Some(telemetry) = &input.telemetry else {
        return reject(NativeInstallGateRejectionCode::MissingTelemetry);
    };
    if missing_required_text(&telemetry.event_id) {
        return reject(NativeInstallGateRejectionCode::MissingTelemetry);
    }
    if !telemetry_matches(
        telemetry,
        input,
        NativeInstallGateDisposition::Installable,
        None,
    ) {
        return reject(NativeInstallGateRejectionCode::TelemetryMismatch);
    }

    (NativeInstallGateDisposition::Installable, None)
}

fn validate_required_manifest_fields(
    input: &NativeInstallGateInput,
    manifest: &ArtifactManifestV1,
    reference: &ArtifactManifestReference,
) -> Result<(), NativeInstallGateRejectionCode> {
    if missing_required_text(&manifest.artifact_id)
        || missing_required_text(&reference.artifact_id)
        || missing_required_text(&input.expected.artifact_id)
        || missing_required_text(&manifest.invalidation.source_fingerprint)
        || missing_required_text(&input.payload_identity.source_sha256)
        || missing_required_text(&input.payload_identity.trust_ir_sha256)
        || missing_required_text(&input.payload_identity.native_payload_sha256)
        || missing_required_text(&input.candidate_payload_identity.source_sha256)
        || missing_required_text(&input.candidate_payload_identity.trust_ir_sha256)
        || missing_required_text(&input.candidate_payload_identity.native_payload_sha256)
    {
        return Err(NativeInstallGateRejectionCode::ArtifactIdentityMismatch);
    }

    if missing_required_text(&manifest.invalidation.compiler_fingerprint) {
        return Err(NativeInstallGateRejectionCode::StaleInvalidation);
    }

    if missing_checksum(reference.manifest_checksum)
        || missing_checksum(input.expected.manifest_checksum)
    {
        return Err(NativeInstallGateRejectionCode::ManifestChecksumMismatch);
    }
    if missing_checksum(reference.target_checksum)
        || missing_checksum(input.expected.target_checksum)
        || missing_checksum(manifest.invalidation.target_checksum)
    {
        return Err(NativeInstallGateRejectionCode::TargetMismatch);
    }
    if missing_checksum(reference.abi_checksum)
        || missing_checksum(input.expected.abi_checksum)
        || missing_checksum(manifest.invalidation.abi_checksum)
    {
        return Err(NativeInstallGateRejectionCode::AbiMismatch);
    }
    if missing_checksum(reference.layout_checksum)
        || missing_checksum(input.expected.layout_checksum)
        || missing_checksum(manifest.invalidation.layout_checksum)
    {
        return Err(NativeInstallGateRejectionCode::LayoutMismatch);
    }
    if missing_checksum(reference.proof_policy_checksum)
        || missing_checksum(input.expected.proof_policy_checksum)
        || missing_checksum(manifest.invalidation.proof_policy_checksum)
    {
        return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
    }
    if missing_checksum(reference.invalidation_checksum)
        || missing_checksum(input.expected.invalidation_checksum)
        || missing_checksum(input.current_invalidation_checksum)
    {
        return Err(NativeInstallGateRejectionCode::StaleInvalidation);
    }

    validate_ty_native_fused_manifest_completeness(manifest)?;

    Ok(())
}

fn is_ty_native_fused_manifest(manifest: &ArtifactManifestV1) -> bool {
    manifest
        .metadata
        .get(TY_NATIVE_FUSED_MANIFEST_SCHEMA_KEY)
        .map(String::as_str)
        == Some(TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA)
}

fn validate_ty_native_fused_manifest_completeness(
    manifest: &ArtifactManifestV1,
) -> Result<(), NativeInstallGateRejectionCode> {
    if !is_ty_native_fused_manifest(manifest) {
        return Ok(());
    }

    let Some(kernel_identity) = manifest
        .metadata
        .get(TY_NATIVE_FUSED_KERNEL_IDENTITY_KEY)
        .map(String::as_str)
    else {
        return Err(NativeInstallGateRejectionCode::MissingManifest);
    };
    if missing_required_text(kernel_identity) {
        return Err(NativeInstallGateRejectionCode::MissingManifest);
    }
    let Some(descriptor_identity) = manifest
        .metadata
        .get(TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY)
        .map(String::as_str)
    else {
        return Err(NativeInstallGateRejectionCode::MissingManifest);
    };
    if missing_required_text(descriptor_identity) {
        return Err(NativeInstallGateRejectionCode::MissingManifest);
    }
    if manifest
        .metadata
        .get(TY_NATIVE_FUSED_STATUS_DEOPT_CONTRACT_KEY)
        .map(String::as_str)
        != Some(TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT)
    {
        return Err(NativeInstallGateRejectionCode::MissingManifest);
    }
    if manifest
        .layout
        .metadata
        .get(TY_NATIVE_FUSED_STATUS_DEOPT_CONTRACT_KEY)
        .map(String::as_str)
        != Some(TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT)
        || manifest
            .layout
            .metadata
            .get(TY_NATIVE_FUSED_KERNEL_IDENTITY_KEY)
            .map(String::as_str)
            != Some(kernel_identity)
        || manifest
            .layout
            .metadata
            .get(TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY)
            .map(String::as_str)
            != Some(descriptor_identity)
        || manifest
            .invalidation
            .extra
            .get(TY_NATIVE_FUSED_STATUS_DEOPT_CONTRACT_KEY)
            .map(String::as_str)
            != Some(TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT)
        || manifest
            .invalidation
            .extra
            .get(TY_NATIVE_FUSED_KERNEL_IDENTITY_KEY)
            .map(String::as_str)
            != Some(kernel_identity)
        || manifest
            .invalidation
            .extra
            .get(TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY)
            .map(String::as_str)
            != Some(descriptor_identity)
    {
        return Err(NativeInstallGateRejectionCode::MissingManifest);
    }

    for (evidence_key, fact) in TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA {
        let manifest_key = format!("required_fact.{fact}");
        if manifest.metadata.get(&manifest_key).map(String::as_str) != Some(*evidence_key)
            || manifest
                .invalidation
                .extra
                .get(&manifest_key)
                .map(String::as_str)
                != Some(*evidence_key)
        {
            return Err(NativeInstallGateRejectionCode::MissingManifest);
        }
    }

    Ok(())
}

fn validate_deny_control(
    input: &NativeInstallGateInput,
    deny: &NativeInstallGateDenyControlPlane,
) -> Result<Option<NativeInstallGateRejectionCode>, NativeInstallGateRejectionCode> {
    if !deny_control_hash_valid(deny) {
        return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
    }
    if !deny.active {
        return Ok(None);
    }
    if !deny_scope_applies(input, deny)? {
        return Ok(None);
    }
    if deny.reason == NativeInstallGateDenyReason::StaleFreshness
        && (deny.freshness.is_empty()
            || !deny
                .freshness
                .iter()
                .any(NativeInstallGateFreshnessObservation::is_stale))
    {
        return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
    }
    Ok(Some(deny.reason.rejection_code()))
}

fn packet_freshness_rejection(
    packet: &NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
) -> Option<NativeInstallGateRejectionCode> {
    if !packet.disposition.is_installable() {
        return None;
    }
    if let Some(deny_control) = &current.deny_control {
        match validate_packet_deny_control(packet, deny_control) {
            Ok(Some(code)) => return Some(code),
            Ok(None) => {}
            Err(code) => return Some(code),
        }
    }
    if packet.freshness.artifact_generation != packet.freshness.current_generation
        || current.current_generation != packet.freshness.current_generation
        || current.current_generation != packet.freshness.artifact_generation
        || current.current_invalidation_checksum != packet.artifact.invalidation_checksum
    {
        return Some(NativeInstallGateRejectionCode::StaleInvalidation);
    }
    if let Some(code) = packet_freshness_domains_rejection(packet, current) {
        return Some(code);
    }
    if packet.freshness.revoked || current.revoked {
        return Some(NativeInstallGateRejectionCode::RevokedArtifact);
    }
    None
}

fn packet_freshness_domains_rejection(
    packet: &NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
) -> Option<NativeInstallGateRejectionCode> {
    let mut packet_domains = BTreeSet::new();
    for observation in &packet.freshness.freshness_domains {
        if missing_required_text(&observation.domain)
            || !packet_domains.insert(observation.domain.as_str())
        {
            return Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
        }
        if observation.is_stale() {
            return Some(NativeInstallGateRejectionCode::StaleInvalidation);
        }
        if observation.observed_generation != packet.freshness.artifact_generation
            || observation.current_generation != packet.freshness.current_generation
        {
            return Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
        }
    }

    let mut current_domains = BTreeSet::new();
    for observation in &current.freshness_domains {
        if missing_required_text(&observation.domain)
            || !current_domains.insert(observation.domain.as_str())
        {
            return Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
        }
        if observation.is_stale() {
            return Some(NativeInstallGateRejectionCode::StaleInvalidation);
        }
        if observation.current_generation != current.current_generation {
            return Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
        }
    }

    for required in required_freshness_domains(packet.consumer.as_str(), packet.surface) {
        let Some(packet_observation) = packet
            .freshness
            .freshness_domains
            .iter()
            .find(|observation| observation.domain == required)
        else {
            return Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
        };
        if let Some(current_observation) = current
            .freshness_domains
            .iter()
            .find(|observation| observation.domain == required)
        {
            if current_observation.observed_generation != packet_observation.observed_generation
                || current_observation.current_generation != packet_observation.current_generation
            {
                return Some(NativeInstallGateRejectionCode::StaleInvalidation);
            }
        } else if current.current_generation != packet_observation.current_generation {
            return Some(NativeInstallGateRejectionCode::StaleInvalidation);
        }
    }

    None
}

fn validate_packet_deny_control(
    packet: &NativeInstallGatePacket,
    deny: &NativeInstallGateDenyControlPlane,
) -> Result<Option<NativeInstallGateRejectionCode>, NativeInstallGateRejectionCode> {
    if !deny_control_hash_valid(deny) {
        return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
    }
    if !deny.active {
        return Ok(None);
    }
    if !deny_scope_applies_to_packet(packet, deny)? {
        return Ok(None);
    }
    if deny.reason == NativeInstallGateDenyReason::StaleFreshness
        && (deny.freshness.is_empty()
            || !deny
                .freshness
                .iter()
                .any(NativeInstallGateFreshnessObservation::is_stale))
    {
        return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
    }
    Ok(Some(deny.reason.rejection_code()))
}

fn deny_control_hash_valid(deny: &NativeInstallGateDenyControlPlane) -> bool {
    let canonical = deny.canonical_deny_sha256();
    !missing_optional_text(deny.deny_sha256.as_deref())
        && deny.deny_sha256.as_deref() == Some(canonical.as_str())
}

fn deny_scope_applies(
    input: &NativeInstallGateInput,
    deny: &NativeInstallGateDenyControlPlane,
) -> Result<bool, NativeInstallGateRejectionCode> {
    match deny.scope {
        NativeInstallGateDenyScope::Global => Ok(true),
        NativeInstallGateDenyScope::Consumer => {
            let Some(consumer) = deny.consumer.as_deref() else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            if missing_required_text(consumer) {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            }
            Ok(consumer == input.consumer)
        }
        NativeInstallGateDenyScope::Family => {
            let Some(family) = deny.family.as_deref() else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            if missing_required_text(family) {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            }
            Ok(family == input.consumer_mode)
        }
        NativeInstallGateDenyScope::Artifact => {
            let Some(artifact_id) = deny.artifact_id.as_deref() else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            if missing_required_text(artifact_id) {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            }
            Ok(artifact_id == input.expected.artifact_id)
        }
        NativeInstallGateDenyScope::TargetProofPolicy => {
            let (Some(target_checksum), Some(proof_policy_checksum)) =
                (deny.target_checksum, deny.proof_policy_checksum)
            else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            if missing_checksum(target_checksum) || missing_checksum(proof_policy_checksum) {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            }
            Ok(target_checksum == input.expected.target_checksum
                && proof_policy_checksum == input.expected.proof_policy_checksum)
        }
        NativeInstallGateDenyScope::Mode => {
            let Some(mode) = deny.mode else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            Ok(mode == input.requested_authority)
        }
        NativeInstallGateDenyScope::Surface => {
            let Some(surface) = deny.surface else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            Ok(surface == input.surface)
        }
    }
}

fn deny_scope_applies_to_packet(
    packet: &NativeInstallGatePacket,
    deny: &NativeInstallGateDenyControlPlane,
) -> Result<bool, NativeInstallGateRejectionCode> {
    match deny.scope {
        NativeInstallGateDenyScope::Global => Ok(true),
        NativeInstallGateDenyScope::Consumer => {
            let Some(consumer) = deny.consumer.as_deref() else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            if missing_required_text(consumer) {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            }
            Ok(consumer == packet.consumer)
        }
        NativeInstallGateDenyScope::Family => {
            let Some(family) = deny.family.as_deref() else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            if missing_required_text(family) {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            }
            Ok(family == packet.consumer_mode)
        }
        NativeInstallGateDenyScope::Artifact => {
            let Some(artifact_id) = deny.artifact_id.as_deref() else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            if missing_required_text(artifact_id) {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            }
            Ok(artifact_id == packet.artifact.artifact_id)
        }
        NativeInstallGateDenyScope::TargetProofPolicy => {
            let (Some(target_checksum), Some(proof_policy_checksum)) =
                (deny.target_checksum, deny.proof_policy_checksum)
            else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            if missing_checksum(target_checksum) || missing_checksum(proof_policy_checksum) {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            }
            Ok(target_checksum == packet.artifact.target_checksum
                && proof_policy_checksum == packet.artifact.proof_policy_checksum)
        }
        NativeInstallGateDenyScope::Mode => {
            let Some(mode) = deny.mode else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            Ok(mode == packet.requested_authority)
        }
        NativeInstallGateDenyScope::Surface => {
            let Some(surface) = deny.surface else {
                return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
            };
            Ok(surface == packet.surface)
        }
    }
}

fn validate_layout_evidence(
    input: &NativeInstallGateInput,
    layout: &NativeInstallGateLayoutEvidence,
) -> Result<(), NativeInstallGateRejectionCode> {
    if missing_checksum(layout.layout_checksum) {
        return Err(NativeInstallGateRejectionCode::LayoutMismatch);
    }
    if missing_checksum(layout.abi_checksum) {
        return Err(NativeInstallGateRejectionCode::AbiMismatch);
    }
    if missing_checksum(layout.invalidation_checksum) {
        return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
    }
    if missing_optional_text(layout.evidence_sha256.as_deref())
        || missing_optional_text(layout.wrapper_identity.as_deref())
        || missing_required_text(&layout.validation_provenance)
        || layout.regions.is_empty()
        || layout.entry_abis.is_empty()
    {
        return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
    }
    if layout.layout_checksum != input.expected.layout_checksum {
        return Err(NativeInstallGateRejectionCode::LayoutMismatch);
    }
    if layout.abi_checksum != input.expected.abi_checksum {
        return Err(NativeInstallGateRejectionCode::AbiMismatch);
    }
    if layout.invalidation_checksum != input.expected.invalidation_checksum {
        return Err(NativeInstallGateRejectionCode::StaleInvalidation);
    }
    let mut region_names = BTreeSet::new();
    let mut generation_domains = BTreeSet::new();
    for region in &layout.regions {
        if missing_required_text(&region.name)
            || missing_required_text(&region.role)
            || region.element_size == 0
            || region.byte_len == 0
            || region.access.is_none()
            || missing_required_text(&region.alias_group)
            || missing_required_text(&region.generation_domain)
        {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        }
        if !region_names.insert(region.name.as_str()) {
            return Err(NativeInstallGateRejectionCode::LayoutMismatch);
        }
        generation_domains.insert(region.generation_domain.as_str());
    }

    for entry in &layout.entry_abis {
        if missing_required_text(&entry.name)
            || missing_required_text(&entry.abi)
            || missing_required_text(&entry.generation_domain)
            || entry.argument_regions.is_empty()
        {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        }
        if missing_checksum(entry.abi_checksum) || entry.abi_checksum != input.expected.abi_checksum
        {
            return Err(NativeInstallGateRejectionCode::AbiMismatch);
        }
        if !generation_domains.contains(entry.generation_domain.as_str()) {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        }
        for region in &entry.argument_regions {
            if missing_required_text(region) || !region_names.contains(region.as_str()) {
                return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
            }
        }
        if let Some(status_region) = &entry.status_region
            && (missing_required_text(status_region)
                || !region_names.contains(status_region.as_str()))
        {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        }
    }

    if input.consumer == "ty" && input.surface == NativeInstallGateSurface::TyActivation {
        validate_ty_layout_evidence(layout)?;
    }
    if input.consumer == "ay" && input.surface == NativeInstallGateSurface::AYRegistry {
        validate_ay_layout_evidence(&input.consumer_mode, layout)?;
    }

    let canonical_hash = layout.canonical_evidence_sha256();
    if layout.evidence_sha256.as_deref() != Some(canonical_hash.as_str()) {
        return Err(NativeInstallGateRejectionCode::LayoutMismatch);
    }

    Ok(())
}

fn validate_ty_layout_evidence(
    layout: &NativeInstallGateLayoutEvidence,
) -> Result<(), NativeInstallGateRejectionCode> {
    let required_regions = [
        (
            "runtime_arena",
            "runtime_arena",
            "ty_arena",
            NativeInstallGateLayoutAccess::ReadWrite,
        ),
        (
            "flat_state_buffer",
            "flat_state_buffer",
            "ty_arena",
            NativeInstallGateLayoutAccess::ReadOnly,
        ),
        (
            "parent_buffer",
            "parent_buffer",
            "ty_action",
            NativeInstallGateLayoutAccess::ReadWrite,
        ),
        (
            "successor_buffer",
            "successor_buffer",
            "ty_action",
            NativeInstallGateLayoutAccess::ReadWrite,
        ),
        (
            "fingerprint_buffer",
            "fingerprint_buffer",
            "ty_fingerprint",
            NativeInstallGateLayoutAccess::ReadWrite,
        ),
        (
            "callback_status_buffer",
            "callback_status_buffer",
            "ty_runtime",
            NativeInstallGateLayoutAccess::ReadWrite,
        ),
    ];
    for (name, role, generation_domain, access) in required_regions {
        let Some(region) = layout.regions.iter().find(|region| region.name == name) else {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        };
        if region.role != role
            || region.generation_domain != generation_domain
            || region.access != Some(access)
        {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        }
    }

    let required_entries: [(&str, &str, &[&str]); 5] = [
        (
            "action",
            "ty_action",
            &[
                "runtime_arena",
                "flat_state_buffer",
                "parent_buffer",
                "successor_buffer",
                "callback_status_buffer",
            ],
        ),
        (
            "invariant",
            "ty_action",
            &[
                "runtime_arena",
                "flat_state_buffer",
                "callback_status_buffer",
            ],
        ),
        (
            "liveness",
            "ty_action",
            &[
                "runtime_arena",
                "flat_state_buffer",
                "callback_status_buffer",
            ],
        ),
        (
            "fingerprint",
            "ty_fingerprint",
            &[
                "runtime_arena",
                "flat_state_buffer",
                "fingerprint_buffer",
                "callback_status_buffer",
            ],
        ),
        (
            "fused_parent_loop",
            "ty_runtime",
            &[
                "runtime_arena",
                "flat_state_buffer",
                "parent_buffer",
                "successor_buffer",
                "fingerprint_buffer",
                "callback_status_buffer",
            ],
        ),
    ];
    for (name, generation_domain, required_regions) in required_entries {
        let Some(entry) = layout.entry_abis.iter().find(|entry| entry.name == name) else {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        };
        if entry.generation_domain != generation_domain
            || entry.status_region.as_deref() != Some("callback_status_buffer")
        {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        }
        for required_region in required_regions {
            if !entry
                .argument_regions
                .iter()
                .any(|region| region == required_region)
            {
                return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
            }
        }
    }

    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AYInstallGateLayoutMode {
    SparseSubstitute,
    BasisRegion,
    WatchListBcp,
    FullRegistry,
}

fn ay_install_gate_layout_mode(consumer_mode: &str) -> AYInstallGateLayoutMode {
    match consumer_mode {
        mode if mode == AYLraKernelFamily::SparseSubstitute.as_str() => {
            AYInstallGateLayoutMode::SparseSubstitute
        }
        "sparse_substitute" | "ay_sparse_substitute" | "lra_sparse_substitute" => {
            AYInstallGateLayoutMode::SparseSubstitute
        }
        mode if mode == AYLraKernelFamily::SparseAffectedRowBatch.as_str() => {
            AYInstallGateLayoutMode::SparseSubstitute
        }
        "lra_sparse_affected_row_batch" => AYInstallGateLayoutMode::SparseSubstitute,
        mode if mode == AYLraKernelFamily::BasisUpdate.as_str() => {
            AYInstallGateLayoutMode::BasisRegion
        }
        "basis_region"
        | "basis_row_batch"
        | "ay_basis"
        | "ay_lra_basis_row_batch"
        | "ay_lra_basis_update" => AYInstallGateLayoutMode::BasisRegion,
        "watch_list_bcp" | "ay_watch_list" | "ay_lra_watch_list_bcp" => {
            AYInstallGateLayoutMode::WatchListBcp
        }
        _ => AYInstallGateLayoutMode::FullRegistry,
    }
}

fn ay_lra_registry_consumer_mode_rejection(
    consumer: &str,
    surface: NativeInstallGateSurface,
    consumer_mode: &str,
) -> Option<NativeInstallGateRejectionCode> {
    if consumer != "ay" || surface != NativeInstallGateSurface::AYRegistry {
        return None;
    }
    if !ay_lra_namespaced_consumer_mode(consumer_mode)
        || ay_lra_registry_consumer_mode_admitted(consumer_mode)
    {
        return None;
    }
    Some(NativeInstallGateRejectionCode::UnsupportedConsumer)
}

fn ay_lra_namespaced_consumer_mode(consumer_mode: &str) -> bool {
    consumer_mode.starts_with("ay_lra_") || consumer_mode.starts_with("lra_")
}

fn ay_lra_registry_consumer_mode_admitted(consumer_mode: &str) -> bool {
    match consumer_mode {
        mode if mode == AYLraKernelFamily::SparseSubstitute.as_str() => true,
        mode if mode == AYLraKernelFamily::SparseAffectedRowBatch.as_str() => true,
        "lra_sparse_substitute"
        | "lra_sparse_affected_row_batch"
        | "ay_lra_basis_row_batch"
        | "ay_lra_basis_update"
        | "ay_lra_watch_list_bcp" => true,
        _ => false,
    }
}

fn validate_ay_layout_evidence(
    consumer_mode: &str,
    layout: &NativeInstallGateLayoutEvidence,
) -> Result<(), NativeInstallGateRejectionCode> {
    let mode = ay_install_gate_layout_mode(consumer_mode);
    let required_regions = [
        (
            "solver_program_state",
            "solver_program_state",
            "ay_solver",
            NativeInstallGateLayoutAccess::ReadOnly,
            &[
                AYInstallGateLayoutMode::SparseSubstitute,
                AYInstallGateLayoutMode::BasisRegion,
                AYInstallGateLayoutMode::WatchListBcp,
                AYInstallGateLayoutMode::FullRegistry,
            ][..],
        ),
        (
            "sparse_substitute_rows",
            "sparse_substitute_rows",
            "ay_sparse_substitute",
            NativeInstallGateLayoutAccess::ReadWrite,
            &[
                AYInstallGateLayoutMode::SparseSubstitute,
                AYInstallGateLayoutMode::FullRegistry,
            ],
        ),
        (
            "basis_region_state",
            "basis_region_state",
            "ay_basis",
            NativeInstallGateLayoutAccess::ReadWrite,
            &[
                AYInstallGateLayoutMode::SparseSubstitute,
                AYInstallGateLayoutMode::BasisRegion,
                AYInstallGateLayoutMode::FullRegistry,
            ],
        ),
        (
            "tableau_buffer",
            "tableau_buffer",
            "ay_solver",
            NativeInstallGateLayoutAccess::ReadWrite,
            &[
                AYInstallGateLayoutMode::SparseSubstitute,
                AYInstallGateLayoutMode::BasisRegion,
                AYInstallGateLayoutMode::FullRegistry,
            ],
        ),
        (
            "watch_list_bcp_state",
            "watch_list_bcp_state",
            "ay_watch_list",
            NativeInstallGateLayoutAccess::ReadWrite,
            &[
                AYInstallGateLayoutMode::WatchListBcp,
                AYInstallGateLayoutMode::FullRegistry,
            ],
        ),
        (
            "rollback_state",
            "rollback_state",
            "ay_rollback",
            NativeInstallGateLayoutAccess::ReadWrite,
            &[
                AYInstallGateLayoutMode::SparseSubstitute,
                AYInstallGateLayoutMode::BasisRegion,
                AYInstallGateLayoutMode::WatchListBcp,
                AYInstallGateLayoutMode::FullRegistry,
            ],
        ),
        (
            "proof_witness_buffer",
            "proof_witness_buffer",
            "ay_proof_witness",
            NativeInstallGateLayoutAccess::ReadWrite,
            &[
                AYInstallGateLayoutMode::WatchListBcp,
                AYInstallGateLayoutMode::FullRegistry,
            ],
        ),
    ];
    for (name, role, generation_domain, access, modes) in required_regions {
        if !modes.contains(&mode) {
            continue;
        }
        let Some(region) = layout.regions.iter().find(|region| region.name == name) else {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        };
        if region.role != role
            || region.generation_domain != generation_domain
            || region.access != Some(access)
        {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        }
    }

    let required_entries: [(&str, &str, &[&str], &[AYInstallGateLayoutMode]); 6] = [
        (
            "solver_program",
            "ay_solver",
            &[
                "solver_program_state",
                "tableau_buffer",
                "proof_witness_buffer",
                "rollback_state",
            ],
            &[AYInstallGateLayoutMode::FullRegistry],
        ),
        (
            "sparse_substitute",
            "ay_sparse_substitute",
            &[
                "solver_program_state",
                "sparse_substitute_rows",
                "basis_region_state",
                "tableau_buffer",
                "rollback_state",
            ],
            &[
                AYInstallGateLayoutMode::SparseSubstitute,
                AYInstallGateLayoutMode::FullRegistry,
            ],
        ),
        (
            "basis_region",
            "ay_basis",
            &[
                "solver_program_state",
                "basis_region_state",
                "tableau_buffer",
                "rollback_state",
            ],
            &[
                AYInstallGateLayoutMode::BasisRegion,
                AYInstallGateLayoutMode::FullRegistry,
            ],
        ),
        (
            "watch_list_bcp",
            "ay_watch_list",
            &[
                "solver_program_state",
                "watch_list_bcp_state",
                "rollback_state",
                "proof_witness_buffer",
            ],
            &[
                AYInstallGateLayoutMode::WatchListBcp,
                AYInstallGateLayoutMode::FullRegistry,
            ],
        ),
        (
            "rollback",
            "ay_rollback",
            &[
                "rollback_state",
                "basis_region_state",
                "sparse_substitute_rows",
                "tableau_buffer",
            ],
            &[AYInstallGateLayoutMode::FullRegistry],
        ),
        (
            "proof_witness",
            "ay_proof_witness",
            &[
                "proof_witness_buffer",
                "solver_program_state",
                "rollback_state",
            ],
            &[AYInstallGateLayoutMode::FullRegistry],
        ),
    ];
    for (name, generation_domain, required_regions, modes) in required_entries {
        if !modes.contains(&mode) {
            continue;
        }
        let Some(entry) = layout.entry_abis.iter().find(|entry| entry.name == name) else {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        };
        if entry.generation_domain != generation_domain
            || entry.status_region.as_deref() != Some("rollback_state")
        {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        }
        for required_region in required_regions {
            if !entry
                .argument_regions
                .iter()
                .any(|region| region == required_region)
            {
                return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
            }
        }
    }
    if mode == AYInstallGateLayoutMode::FullRegistry {
        let Some(entry) = layout
            .entry_abis
            .iter()
            .find(|entry| entry.name == "sparse_substitute")
        else {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        };
        if !entry
            .argument_regions
            .iter()
            .any(|region| region == "proof_witness_buffer")
        {
            return Err(NativeInstallGateRejectionCode::MissingLayoutEvidence);
        }
    }

    Ok(())
}

fn proof_evidence_required_fields_missing(proof: &NativeInstallGateProofEvidence) -> bool {
    missing_required_text(&proof.summary.verifier)
        || missing_optional_text(proof.proof_report_sha256.as_deref())
        || missing_optional_text(proof.obligation_set.as_deref())
        || proof.timeout_ms.is_none()
        || missing_optional_text(proof.native_payload_sha256.as_deref())
}

fn validate_proof(
    manifest: &ArtifactManifestV1,
    proof: &NativeInstallGateProofEvidence,
) -> Result<(), NativeInstallGateRejectionCode> {
    let evidence = &proof.summary;
    if evidence.schema != JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA
        || evidence.schema_version != JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA_VERSION
    {
        return Err(NativeInstallGateRejectionCode::UnsupportedSchema);
    }
    match evidence.verdict {
        ProofEvidenceVerdict::Verified if evidence.rejection_code.is_none() => {}
        ProofEvidenceVerdict::MissingEvidence => {
            return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
        }
        ProofEvidenceVerdict::VerifierFailure => {
            return Err(NativeInstallGateRejectionCode::ProofVerifierFailure);
        }
        ProofEvidenceVerdict::Timeout => return Err(NativeInstallGateRejectionCode::ProofTimeout),
        ProofEvidenceVerdict::Unknown => return Err(NativeInstallGateRejectionCode::ProofUnknown),
        ProofEvidenceVerdict::SolverError => {
            return Err(NativeInstallGateRejectionCode::ProofSolverError);
        }
        ProofEvidenceVerdict::UnsupportedRoute => {
            return Err(NativeInstallGateRejectionCode::ProofUnsupportedRoute);
        }
        ProofEvidenceVerdict::UnsupportedTarget => {
            return Err(NativeInstallGateRejectionCode::ProofUnsupportedTarget);
        }
        ProofEvidenceVerdict::StaleEvidence => {
            return Err(NativeInstallGateRejectionCode::ProofStaleEvidence);
        }
        ProofEvidenceVerdict::MalformedReport => {
            return Err(NativeInstallGateRejectionCode::ProofMalformedReport);
        }
        ProofEvidenceVerdict::MissingRequiredFields => {
            return Err(NativeInstallGateRejectionCode::ProofMissingRequiredFields);
        }
        ProofEvidenceVerdict::UnknownSolverError => {
            return Err(NativeInstallGateRejectionCode::ProofUnknown);
        }
        ProofEvidenceVerdict::Verified => {
            let code = evidence
                .rejection_code
                .as_ref()
                .ok_or(NativeInstallGateRejectionCode::ProofUnknown)?;
            return Err(proof_rejection_code(code));
        }
    }
    if evidence.target_checksum != manifest.target.checksum()
        || evidence.abi_checksum != manifest.abi.checksum()
        || evidence.proof_policy_checksum != manifest.proof_policy.checksum()
    {
        return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
    }
    if evidence.layout_checksum != manifest.layout.checksum() {
        return Err(NativeInstallGateRejectionCode::LayoutMismatch);
    }
    if evidence.invalidation_checksum != manifest.invalidation.checksum() {
        return Err(NativeInstallGateRejectionCode::ProofStaleEvidence);
    }
    Ok(())
}

fn validate_ty_native_fused_proof_metadata(
    input: &NativeInstallGateInput,
    manifest: &ArtifactManifestV1,
    proof: &NativeInstallGateProofEvidence,
) -> Result<(), NativeInstallGateRejectionCode> {
    if input.consumer != "ty"
        || input.surface != NativeInstallGateSurface::TyActivation
        || input.consumer_mode != TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE
        || !is_ty_native_fused_manifest(manifest)
    {
        return Ok(());
    }

    validate_ty_native_fused_manifest_completeness(manifest)?;

    let metadata = &proof.summary.metadata;
    if ty_native_fused_missing_fact(metadata, manifest).is_some() {
        return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
    }
    for key in TY_NATIVE_FUSED_REQUIRED_EVIDENCE_REF_KEYS {
        let Some(value) = metadata.get(*key).map(String::as_str) else {
            return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
        };
        if missing_required_text(value) {
            return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
        }
    }
    let manifest_identity = manifest.checksum().to_string();
    if metadata
        .get(TY_NATIVE_FUSED_EVIDENCE_MANIFEST_IDENTITY_KEY)
        .map(String::as_str)
        != Some(manifest_identity.as_str())
    {
        return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
    }

    let replay_root = metadata
        .get(TY_NATIVE_FUSED_EVIDENCE_REPLAY_ROOT_KEY)
        .map(String::as_str)
        .ok_or(NativeInstallGateRejectionCode::ProofMissingEvidence)?;
    let Some(replay_identity) = input.replay_identity.as_ref() else {
        return Err(NativeInstallGateRejectionCode::MissingReplayIdentity);
    };
    if !replay_root.starts_with("sha256:")
        || replay_root != replay_identity.replay_root_sha256.as_str()
    {
        return Err(NativeInstallGateRejectionCode::ReplayIdentityMismatch);
    }

    let telemetry_event = metadata
        .get(TY_NATIVE_FUSED_EVIDENCE_TELEMETRY_EVENT_KEY)
        .map(String::as_str)
        .ok_or(NativeInstallGateRejectionCode::ProofMissingEvidence)?;
    let gate_result = metadata
        .get(TY_NATIVE_FUSED_EVIDENCE_GATE_RESULT_KEY)
        .map(String::as_str)
        .ok_or(NativeInstallGateRejectionCode::ProofMissingEvidence)?;
    let Some(telemetry) = input.telemetry.as_ref() else {
        return Err(NativeInstallGateRejectionCode::MissingTelemetry);
    };
    if telemetry_event != telemetry.event_id.as_str() {
        return Err(NativeInstallGateRejectionCode::TelemetryMismatch);
    }
    if gate_result != telemetry.record_sha256.as_str() {
        return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
    }

    let certificate_identity = metadata
        .get(TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY)
        .map(String::as_str)
        .ok_or(NativeInstallGateRejectionCode::ProofMissingEvidence)?;
    if !ty_native_fused_certificate_identity_matches(manifest, certificate_identity) {
        return Err(NativeInstallGateRejectionCode::EvidenceBindingMismatch);
    }

    if proof.proof_report_sha256.as_deref()
        != metadata
            .get(TY_NATIVE_FUSED_EVIDENCE_VALIDATION_HASH_KEY)
            .map(String::as_str)
    {
        return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
    }

    Ok(())
}

fn ay_lra_install_gate_proof_manifest(
    consumer_mode: &str,
) -> Option<AYLraKernelProofConsumptionManifest> {
    if consumer_mode == AYLraKernelFamily::SparseAffectedRowBatch.as_str()
        || consumer_mode == "lra_sparse_affected_row_batch"
    {
        return Some(ay_lra_sparse_affected_row_batch_proof_manifest());
    }

    match ay_install_gate_layout_mode(consumer_mode) {
        AYInstallGateLayoutMode::SparseSubstitute => {
            Some(ay_lra_sparse_substitute_proof_manifest())
        }
        AYInstallGateLayoutMode::BasisRegion => Some(ay_lra_basis_update_proof_manifest()),
        AYInstallGateLayoutMode::WatchListBcp | AYInstallGateLayoutMode::FullRegistry => None,
    }
}

fn validate_ay_lra_registry_proof_metadata(
    input: &NativeInstallGateInput,
    proof: &NativeInstallGateProofEvidence,
) -> Result<(), NativeInstallGateRejectionCode> {
    if input.consumer != "ay" || input.surface != NativeInstallGateSurface::AYRegistry {
        return Ok(());
    }
    let Some(proof_manifest) = ay_lra_install_gate_proof_manifest(&input.consumer_mode) else {
        return Ok(());
    };

    for (key, expected_value) in ay_lra_manifest_proof_metadata(&proof_manifest) {
        if proof.summary.metadata.get(key).map(String::as_str) != Some(expected_value.as_str()) {
            return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
        }
    }

    for requirement in &proof_manifest.required_facts {
        let key = ay_lra_proof_fact_metadata_key(requirement.fact);
        if proof.summary.metadata.get(&key).map(String::as_str) != Some(requirement.lemma_id) {
            return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
        }
    }

    validate_ay_lra_registry_source_metadata(input, proof)?;

    Ok(())
}

fn validate_ay_lra_registry_source_metadata(
    input: &NativeInstallGateInput,
    proof: &NativeInstallGateProofEvidence,
) -> Result<(), NativeInstallGateRejectionCode> {
    const SOURCE_METADATA_KEYS: [&str; 4] = [
        "source_policy",
        "trust_ir_source_identity",
        "trust_cg_source_lock",
        "trust_ir_source_lock",
    ];

    let Some(manifest) = input.manifest.as_ref() else {
        return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
    };

    for key in SOURCE_METADATA_KEYS {
        let Some(manifest_value) = manifest.metadata.get(key).map(String::as_str) else {
            return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
        };
        if missing_required_text(manifest_value)
            || proof.summary.metadata.get(key).map(String::as_str) != Some(manifest_value)
        {
            return Err(NativeInstallGateRejectionCode::ProofMissingEvidence);
        }
    }

    Ok(())
}

fn ay_lra_manifest_proof_metadata(
    manifest: &AYLraKernelProofConsumptionManifest,
) -> Vec<(&'static str, String)> {
    vec![
        (
            "proof_consumption_manifest_schema",
            manifest.schema.to_owned(),
        ),
        (
            "proof_consumption_manifest_issue",
            format!("#{}", manifest.issue),
        ),
        ("kernel_family", manifest.kernel_family.as_str().to_owned()),
        ("required_proof_facts", manifest.required_fact_csv()),
        (
            "required_certificate_dependencies",
            manifest.required_certificate_csv(),
        ),
        (
            "future_proof_status",
            ay_lra_manifest_future_proof_status(manifest),
        ),
        (
            "product_gate_fields",
            manifest.product_gate.required_parent_gates.join(","),
        ),
    ]
}

fn ay_lra_manifest_future_proof_status(manifest: &AYLraKernelProofConsumptionManifest) -> String {
    let mut statuses: Vec<_> = manifest
        .future_facts
        .iter()
        .map(|requirement| requirement.availability.as_str())
        .collect();
    statuses.sort_unstable();
    statuses.dedup();
    statuses.join(",")
}

fn ty_native_fused_certificate_identity_matches(
    manifest: &ArtifactManifestV1,
    certificate_identity: &str,
) -> bool {
    if missing_required_text(certificate_identity) {
        return false;
    }
    let Some(canonical_certificate_identity) =
        ty_native_fused_canonical_certificate_identity(manifest)
    else {
        return false;
    };
    if let Some(bound_certificate_identity) = manifest
        .metadata
        .get(TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY)
        .map(String::as_str)
        && (missing_required_text(bound_certificate_identity)
            || bound_certificate_identity != canonical_certificate_identity.as_str())
    {
        return false;
    }
    certificate_identity == canonical_certificate_identity.as_str()
}

fn ty_native_fused_canonical_certificate_identity(manifest: &ArtifactManifestV1) -> Option<String> {
    let kernel_identity = manifest
        .metadata
        .get(TY_NATIVE_FUSED_KERNEL_IDENTITY_KEY)
        .map(String::as_str)?;
    if missing_required_text(kernel_identity) {
        return None;
    }
    Some(format!(
        "{TY_NATIVE_FUSED_PROOF_OPT_TRANSFORM_NAME}:{kernel_identity}:cert-v1"
    ))
}

fn ty_native_fused_missing_fact(
    metadata: &BTreeMap<String, String>,
    manifest: &ArtifactManifestV1,
) -> Option<&'static str> {
    if !is_ty_native_fused_manifest(manifest) {
        return None;
    }
    if let Some(fact) = ty_native_fused_declared_missing_fact(metadata) {
        return Some(fact);
    }
    for (key, fact) in TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA {
        if metadata.get(*key).map(String::as_str) != Some(TY_NATIVE_FUSED_PROOF_FACT_VERIFIED) {
            return Some(*fact);
        }
    }
    None
}

fn ty_native_fused_declared_missing_fact(
    metadata: &BTreeMap<String, String>,
) -> Option<&'static str> {
    let fact = metadata
        .get(TY_NATIVE_FUSED_EVIDENCE_MISSING_FACT_KEY)
        .map(String::as_str)?;
    TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA
        .iter()
        .find_map(|(_, required_fact)| (*required_fact == fact).then_some(*required_fact))
}

fn proof_rejection_code(code: &ProofEvidenceRejectionCode) -> NativeInstallGateRejectionCode {
    match code {
        ProofEvidenceRejectionCode::MissingEvidence => {
            NativeInstallGateRejectionCode::ProofMissingEvidence
        }
        ProofEvidenceRejectionCode::VerifierFailure => {
            NativeInstallGateRejectionCode::ProofVerifierFailure
        }
        ProofEvidenceRejectionCode::Timeout => NativeInstallGateRejectionCode::ProofTimeout,
        ProofEvidenceRejectionCode::Unknown => NativeInstallGateRejectionCode::ProofUnknown,
        ProofEvidenceRejectionCode::SolverError => NativeInstallGateRejectionCode::ProofSolverError,
        ProofEvidenceRejectionCode::UnsupportedRoute => {
            NativeInstallGateRejectionCode::ProofUnsupportedRoute
        }
        ProofEvidenceRejectionCode::UnsupportedTarget => {
            NativeInstallGateRejectionCode::ProofUnsupportedTarget
        }
        ProofEvidenceRejectionCode::StaleEvidence => {
            NativeInstallGateRejectionCode::ProofStaleEvidence
        }
        ProofEvidenceRejectionCode::MalformedReport => {
            NativeInstallGateRejectionCode::ProofMalformedReport
        }
        ProofEvidenceRejectionCode::MissingRequiredFields => {
            NativeInstallGateRejectionCode::ProofMissingRequiredFields
        }
        ProofEvidenceRejectionCode::UnknownSolverError => {
            NativeInstallGateRejectionCode::ProofUnknown
        }
    }
}

fn telemetry_matches(
    telemetry: &NativeInstallGateTelemetryInput,
    input: &NativeInstallGateInput,
    disposition: NativeInstallGateDisposition,
    rejection_code: Option<NativeInstallGateRejectionCode>,
) -> bool {
    telemetry.schema == NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA
        && telemetry.schema_version == NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION
        && !missing_required_text(&telemetry.event_id)
        && telemetry.counter_scope
            == native_install_gate_counter_scope_parts(
                &input.consumer,
                &input.consumer_mode,
                input.surface,
                &input.expected.artifact_id,
            )
        && telemetry.record_sha256 == telemetry.canonical_record_sha256()
        && telemetry.artifact_id == input.expected.artifact_id
        && telemetry.manifest_checksum == input.expected.manifest_checksum
        && telemetry.proof_report_sha256 == proof_report_sha256(input)
        && telemetry.layout_checksum == input.expected.layout_checksum
        && telemetry.invalidation_checksum == input.expected.invalidation_checksum
        && telemetry.disposition == disposition
        && telemetry.rejection_code == rejection_code
        && telemetry.install_authority == input.requested_authority
        && telemetry.useful_native_delta == 0
}

fn replay_identity_matches(
    input: &NativeInstallGateInput,
    replay: &NativeInstallGateReplayIdentity,
) -> bool {
    replay.schema == NATIVE_INSTALL_GATE_REPLAY_SCHEMA
        && replay.schema_version == NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION
        && !missing_required_text(&replay.replay_root_sha256)
        && replay.replay_root_sha256.starts_with("sha256:")
        && replay.replay_consumer == input.consumer
        && replay.replay_family == input.consumer_mode
        && replay.artifact_id == input.expected.artifact_id
        && replay.source_sha256.as_str() == input.candidate_payload_identity.source_sha256.as_str()
        && replay.trust_ir_sha256.as_str()
            == input.candidate_payload_identity.trust_ir_sha256.as_str()
        && replay.native_payload_sha256.as_str()
            == input
                .candidate_payload_identity
                .native_payload_sha256
                .as_str()
        && replay.replay_record_sha256 == replay.canonical_record_sha256()
}

fn telemetry_packet_matches(
    packet: &NativeInstallGatePacket,
    telemetry: &NativeInstallGateTelemetryPacket,
) -> bool {
    telemetry.schema == NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA
        && telemetry.schema_version == NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION
        && !missing_required_text(&telemetry.event_id)
        && telemetry.counter_scope == native_install_gate_counter_scope(packet)
        && telemetry.record_sha256 == telemetry.canonical_record_sha256()
        && telemetry.artifact_id == packet.artifact.artifact_id
        && telemetry.manifest_checksum == packet.artifact.manifest_checksum
        && telemetry.proof_report_sha256 == packet.validation.proof_report_sha256
        && telemetry.layout_checksum == packet.artifact.layout_checksum
        && telemetry.invalidation_checksum == packet.artifact.invalidation_checksum
        && telemetry.disposition == packet.disposition
        && telemetry.rejection_code == packet.rejection_code
        && telemetry.install_authority == packet.install_authority
        && telemetry.useful_native_delta == 0
}

fn replay_identity_packet_matches(
    packet: &NativeInstallGatePacket,
    replay: &NativeInstallGateReplayIdentity,
) -> bool {
    replay.schema == NATIVE_INSTALL_GATE_REPLAY_SCHEMA
        && replay.schema_version == NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION
        && !missing_required_text(&replay.replay_root_sha256)
        && replay.replay_root_sha256.starts_with("sha256:")
        && replay.replay_consumer == packet.consumer
        && replay.replay_family == packet.consumer_mode
        && replay.artifact_id == packet.artifact.artifact_id
        && replay.source_sha256.as_str() == packet.artifact.source_sha256.as_str()
        && replay.trust_ir_sha256.as_str() == packet.artifact.trust_ir_sha256.as_str()
        && replay.native_payload_sha256.as_str() == packet.artifact.native_payload_sha256.as_str()
        && replay.replay_record_sha256 == replay.canonical_record_sha256()
}

fn proof_report_sha256(input: &NativeInstallGateInput) -> Option<String> {
    input
        .proof_evidence
        .as_ref()
        .and_then(|proof| proof.proof_report_sha256.clone())
}

fn proof_reject_code_for_packet(
    input: &NativeInstallGateInput,
    proof: &NativeInstallGateProofEvidence,
) -> Option<&'static str> {
    input
        .manifest
        .as_ref()
        .and_then(|manifest| ty_native_fused_missing_fact(&proof.summary.metadata, manifest))
        .or_else(|| ty_native_fused_declared_missing_fact(&proof.summary.metadata))
        .or_else(|| {
            proof
                .summary
                .rejection_code
                .as_ref()
                .map(|code| code.as_str())
        })
}

fn reject(
    code: NativeInstallGateRejectionCode,
) -> (
    NativeInstallGateDisposition,
    Option<NativeInstallGateRejectionCode>,
) {
    (NativeInstallGateDisposition::Rejected, Some(code))
}

fn build_packet(
    input: &NativeInstallGateInput,
    disposition: NativeInstallGateDisposition,
    rejection_code: Option<NativeInstallGateRejectionCode>,
) -> NativeInstallGatePacket {
    let authority = if disposition.is_installable() {
        input.requested_authority
    } else {
        NativeInstallGateAuthority::None
    };
    let actions = if disposition.is_installable() && authority.is_callable() {
        NativeInstallGateActions::for_surface(input.surface)
    } else {
        NativeInstallGateActions::none()
    };
    let artifact = artifact_packet(input);
    let validation = validation_packet(input);
    let counter_scope = native_install_gate_counter_scope_parts(
        &input.consumer,
        &input.consumer_mode,
        input.surface,
        &artifact.artifact_id,
    );
    let telemetry = input
        .telemetry
        .as_ref()
        .map(|telemetry| NativeInstallGateTelemetryPacket {
            schema: telemetry.schema.clone(),
            schema_version: telemetry.schema_version,
            event_id: telemetry.event_id.clone(),
            counter_scope: counter_scope.clone(),
            record_sha256: telemetry.record_sha256.clone(),
            artifact_id: telemetry.artifact_id.clone(),
            manifest_checksum: telemetry.manifest_checksum,
            proof_report_sha256: telemetry.proof_report_sha256.clone(),
            layout_checksum: telemetry.layout_checksum,
            invalidation_checksum: telemetry.invalidation_checksum,
            disposition,
            rejection_code,
            install_authority: authority,
            useful_native_delta: if disposition.is_installable() {
                telemetry.useful_native_delta
            } else {
                0
            },
        });

    let mut packet = NativeInstallGatePacket {
        schema: NATIVE_INSTALL_GATE_PACKET_SCHEMA,
        schema_version: NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION,
        gate_issue: 681,
        design_issue: 682,
        consumer: input.consumer.clone(),
        consumer_mode: input.consumer_mode.clone(),
        surface: input.surface,
        artifact,
        validation,
        freshness: NativeInstallGateFreshnessPacket {
            artifact_generation: input.artifact_generation,
            current_generation: input.current_generation,
            freshness_domains: freshness_domain_observations(
                input.consumer.as_str(),
                input.surface,
                input.artifact_generation,
                input.current_generation,
            ),
            revoked: input.revoked,
            deny_control: input.deny_control.clone(),
        },
        telemetry,
        replay_identity: input.replay_identity.clone(),
        requested_authority: input.requested_authority,
        disposition,
        rejection_code,
        install_authority: authority,
        packet_hash: ArtifactChecksum::new(0),
        replay_binding: NativeInstallGateReplayBinding {
            packet_hash: ArtifactChecksum::new(0),
            replay_root_sha256: String::new(),
        },
        consumer_verdict: NativeInstallGateConsumerVerdictBinding {
            consumer: String::new(),
            consumer_mode: String::new(),
            surface: input.surface,
            verdict_id: String::new(),
            verdict_sha256: String::new(),
        },
        actions,
    };
    persist_native_install_gate_packet_bindings(&mut packet);
    packet
}

fn required_freshness_domains(
    consumer: &str,
    _surface: NativeInstallGateSurface,
) -> Vec<&'static str> {
    let mut domains = Vec::with_capacity(
        SHARED_FRESHNESS_DOMAINS.len() + TY_FRESHNESS_DOMAINS.len() + AY_FRESHNESS_DOMAINS.len(),
    );
    domains.extend(SHARED_FRESHNESS_DOMAINS.iter().copied());
    match consumer {
        "ty" => {
            domains.extend(TY_FRESHNESS_DOMAINS.iter().copied());
        }
        "ay" => {
            domains.extend(AY_FRESHNESS_DOMAINS.iter().copied());
        }
        _ => {}
    }
    domains
}

fn freshness_domain_observations(
    consumer: &str,
    surface: NativeInstallGateSurface,
    artifact_generation: u64,
    current_generation: u64,
) -> Vec<NativeInstallGateFreshnessObservation> {
    required_freshness_domains(consumer, surface)
        .into_iter()
        .map(|domain| {
            NativeInstallGateFreshnessObservation::new(
                domain,
                artifact_generation,
                current_generation,
            )
        })
        .collect()
}

impl NativeInstallGateVerdict {
    /// Return the stable verdict rejection reason code.
    pub fn reason_code(&self) -> Option<&'static str> {
        self.rejection_code
            .map(NativeInstallGateRejectionCode::as_str)
    }

    fn from_packet(packet: &NativeInstallGatePacket) -> Self {
        Self {
            disposition: packet.disposition,
            rejection_code: packet.rejection_code,
            requested_authority: packet.requested_authority,
            install_authority: packet.install_authority,
            packet_hash: native_install_gate_packet_hash(packet),
            telemetry_event_id: packet
                .telemetry
                .as_ref()
                .map(|telemetry| telemetry.event_id.clone()),
            counter_scope: packet
                .telemetry
                .as_ref()
                .map(|telemetry| telemetry.counter_scope.clone())
                .unwrap_or_else(|| native_install_gate_counter_scope(packet)),
            replay_identity: packet.replay_identity.clone(),
            replay_binding: packet.replay_binding.clone(),
            consumer_verdict: packet.consumer_verdict.clone(),
            deny_control: packet.freshness.deny_control.clone(),
            actions: packet.actions,
        }
    }
}

fn packet_actions_consistent(packet: &NativeInstallGatePacket) -> bool {
    if packet.disposition.is_installable()
        && packet.rejection_code.is_none()
        && packet.requested_authority.is_callable()
        && packet.install_authority.is_callable()
    {
        packet.install_authority == packet.requested_authority
            && packet.actions == NativeInstallGateActions::for_surface(packet.surface)
    } else if packet.disposition.is_installable() {
        false
    } else {
        packet.install_authority == NativeInstallGateAuthority::None
            && packet.actions == NativeInstallGateActions::none()
    }
}

fn persisted_packet_layout_rejection(
    packet: &NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
) -> Option<NativeInstallGateRejectionCode> {
    if !packet.disposition.is_installable() {
        return None;
    }
    match packet.validation.layout_status {
        "accepted" => {}
        "mismatch" => return Some(NativeInstallGateRejectionCode::LayoutMismatch),
        "missing" => return Some(NativeInstallGateRejectionCode::MissingLayoutEvidence),
        _ => return Some(NativeInstallGateRejectionCode::MissingLayoutEvidence),
    }
    if missing_optional_text(packet.validation.layout_evidence_sha256.as_deref())
        || missing_optional_text(packet.validation.layout_wrapper_identity.as_deref())
        || missing_optional_text(packet.validation.layout_validation_provenance.as_deref())
        || packet.validation.layout_generation_domains.is_empty()
        || packet
            .validation
            .layout_generation_domains
            .iter()
            .any(|domain| missing_required_text(domain))
    {
        return Some(NativeInstallGateRejectionCode::MissingLayoutEvidence);
    }
    let Some(layout_invalidation_checksum) = packet.validation.layout_invalidation_checksum else {
        return Some(NativeInstallGateRejectionCode::MissingLayoutEvidence);
    };
    if missing_checksum(layout_invalidation_checksum)
        || layout_invalidation_checksum != packet.artifact.invalidation_checksum
        || layout_invalidation_checksum != current.current_invalidation_checksum
    {
        return Some(NativeInstallGateRejectionCode::StaleInvalidation);
    }
    if let Some(code) = consumer_layout_domains_rejection(packet) {
        return Some(code);
    }
    None
}

fn consumer_layout_domains_rejection(
    packet: &NativeInstallGatePacket,
) -> Option<NativeInstallGateRejectionCode> {
    let required_domains: &[&str] = match (packet.consumer.as_str(), packet.surface) {
        ("ty", NativeInstallGateSurface::TyActivation) => {
            &["ty_action", "ty_arena", "ty_fingerprint", "ty_runtime"]
        }
        ("ay", NativeInstallGateSurface::AYRegistry) => {
            match ay_install_gate_layout_mode(&packet.consumer_mode) {
                AYInstallGateLayoutMode::SparseSubstitute => &[
                    "ay_basis",
                    "ay_rollback",
                    "ay_solver",
                    "ay_sparse_substitute",
                ],
                AYInstallGateLayoutMode::BasisRegion => &["ay_basis", "ay_rollback", "ay_solver"],
                AYInstallGateLayoutMode::WatchListBcp => &[
                    "ay_proof_witness",
                    "ay_rollback",
                    "ay_solver",
                    "ay_watch_list",
                ],
                AYInstallGateLayoutMode::FullRegistry => &[
                    "ay_basis",
                    "ay_proof_witness",
                    "ay_rollback",
                    "ay_solver",
                    "ay_sparse_substitute",
                    "ay_watch_list",
                ],
            }
        }
        _ => return None,
    };
    if required_domains.iter().all(|required| {
        packet
            .validation
            .layout_generation_domains
            .iter()
            .any(|domain| domain == required)
    }) {
        None
    } else {
        Some(NativeInstallGateRejectionCode::MissingLayoutEvidence)
    }
}

fn native_install_gate_counter_scope(packet: &NativeInstallGatePacket) -> String {
    native_install_gate_counter_scope_parts(
        &packet.consumer,
        &packet.consumer_mode,
        packet.surface,
        &packet.artifact.artifact_id,
    )
}

fn native_install_gate_counter_scope_parts(
    consumer: &str,
    consumer_mode: &str,
    surface: NativeInstallGateSurface,
    artifact_id: &str,
) -> String {
    let consumer_mode =
        native_install_gate_counter_scope_consumer_mode(consumer, consumer_mode, surface);
    format!(
        "{}:{}:{}:{}",
        consumer,
        consumer_mode,
        surface.as_str(),
        artifact_id
    )
}

fn native_install_gate_counter_scope_consumer_mode<'a>(
    consumer: &str,
    consumer_mode: &'a str,
    surface: NativeInstallGateSurface,
) -> &'a str {
    // Canonicalization is intentionally limited to the ay registry surface.
    if consumer != "ay" || surface != NativeInstallGateSurface::AYRegistry {
        return consumer_mode;
    }

    match consumer_mode {
        mode if mode == AYLraKernelFamily::SparseSubstitute.as_str() => {
            AYLraKernelFamily::SparseSubstitute.as_str()
        }
        "lra_sparse_substitute" | "sparse_substitute" => {
            AYLraKernelFamily::SparseSubstitute.as_str()
        }
        mode if mode == AYLraKernelFamily::SparseAffectedRowBatch.as_str() => {
            AYLraKernelFamily::SparseAffectedRowBatch.as_str()
        }
        "lra_sparse_affected_row_batch" => AYLraKernelFamily::SparseAffectedRowBatch.as_str(),
        mode if mode == AYLraKernelFamily::BasisUpdate.as_str() => {
            AYLraKernelFamily::BasisUpdate.as_str()
        }
        "ay_lra_basis_row_batch" | "basis_row_batch" => AYLraKernelFamily::BasisUpdate.as_str(),
        _ => consumer_mode,
    }
}

fn structured_event_kind(
    disposition: NativeInstallGateDisposition,
    rejection_code: Option<NativeInstallGateRejectionCode>,
    actions: NativeInstallGateActions,
    native_call_succeeded: Option<bool>,
) -> NativeInstallGateEventKind {
    if let Some(code) = rejection_code {
        return match code {
            NativeInstallGateRejectionCode::ProofTimeout => {
                NativeInstallGateEventKind::VerifierTimeout
            }
            NativeInstallGateRejectionCode::ProofUnknown => {
                NativeInstallGateEventKind::ProofUnknown
            }
            NativeInstallGateRejectionCode::StaleInvalidation
            | NativeInstallGateRejectionCode::ProofStaleEvidence => {
                NativeInstallGateEventKind::StaleGeneration
            }
            NativeInstallGateRejectionCode::RevokedArtifact => NativeInstallGateEventKind::Revoked,
            NativeInstallGateRejectionCode::KillSwitchActive => {
                NativeInstallGateEventKind::KillSwitch
            }
            NativeInstallGateRejectionCode::PacketHashMismatch
            | NativeInstallGateRejectionCode::EvidenceBindingMismatch
            | NativeInstallGateRejectionCode::ReplayIdentityMismatch
            | NativeInstallGateRejectionCode::ProofReplayIdentityMismatch
            | NativeInstallGateRejectionCode::TelemetryMismatch
            | NativeInstallGateRejectionCode::ManifestChecksumMismatch
            | NativeInstallGateRejectionCode::ArtifactIdentityMismatch
            | NativeInstallGateRejectionCode::TargetMismatch
            | NativeInstallGateRejectionCode::TargetAbiMismatch
            | NativeInstallGateRejectionCode::AbiMismatch
            | NativeInstallGateRejectionCode::LayoutMismatch => {
                NativeInstallGateEventKind::Invalidated
            }
            _ => NativeInstallGateEventKind::Rejected,
        };
    }

    if disposition.is_installable()
        && native_call_succeeded == Some(false)
        && native_call_authorized(actions)
    {
        NativeInstallGateEventKind::RolledBack
    } else if disposition.is_installable() {
        NativeInstallGateEventKind::Accepted
    } else {
        NativeInstallGateEventKind::Rejected
    }
}

fn native_call_authorized(actions: NativeInstallGateActions) -> bool {
    actions.expose_callable || actions.ay_registry_insert || actions.ty_native_activate
}

fn runtime_outcome(
    disposition: NativeInstallGateDisposition,
    rejection_code: Option<NativeInstallGateRejectionCode>,
    actions: NativeInstallGateActions,
    native_call_succeeded: bool,
    useful_native_delta: u64,
) -> NativeInstallGateRuntimeOutcome {
    if useful_native_delta > 0 {
        return NativeInstallGateRuntimeOutcome::NativeUseful;
    }

    if let Some(code) = rejection_code {
        return match code {
            NativeInstallGateRejectionCode::StaleInvalidation
            | NativeInstallGateRejectionCode::ProofStaleEvidence => {
                NativeInstallGateRuntimeOutcome::StaleDeopt
            }
            NativeInstallGateRejectionCode::RevokedArtifact => {
                NativeInstallGateRuntimeOutcome::RevokedDeopt
            }
            NativeInstallGateRejectionCode::KillSwitchActive => {
                NativeInstallGateRuntimeOutcome::KillSwitchDeopt
            }
            NativeInstallGateRejectionCode::PacketHashMismatch
            | NativeInstallGateRejectionCode::EvidenceBindingMismatch
            | NativeInstallGateRejectionCode::ReplayIdentityMismatch
            | NativeInstallGateRejectionCode::ProofReplayIdentityMismatch
            | NativeInstallGateRejectionCode::TelemetryMismatch
            | NativeInstallGateRejectionCode::ManifestChecksumMismatch
            | NativeInstallGateRejectionCode::ArtifactIdentityMismatch
            | NativeInstallGateRejectionCode::TargetMismatch
            | NativeInstallGateRejectionCode::TargetAbiMismatch
            | NativeInstallGateRejectionCode::AbiMismatch
            | NativeInstallGateRejectionCode::LayoutMismatch => {
                NativeInstallGateRuntimeOutcome::InvalidatedDeopt
            }
            _ => NativeInstallGateRuntimeOutcome::RejectedDeopt,
        };
    }

    if disposition.is_installable() && native_call_authorized(actions) && !native_call_succeeded {
        NativeInstallGateRuntimeOutcome::BaselineFallback
    } else if disposition.is_installable() {
        NativeInstallGateRuntimeOutcome::MetadataOnly
    } else {
        NativeInstallGateRuntimeOutcome::RejectedDeopt
    }
}

fn build_structured_event(
    packet: &NativeInstallGatePacket,
    source: NativeInstallGateEventSource,
    kind: NativeInstallGateEventKind,
    disposition: NativeInstallGateDisposition,
    rejection_code: Option<NativeInstallGateRejectionCode>,
    install_authority: NativeInstallGateAuthority,
    actions: NativeInstallGateActions,
    native_call_succeeded: Option<bool>,
    useful_native_delta: u64,
    replay_record_sha256: Option<String>,
    diagnostic_sha256: Option<String>,
) -> NativeInstallGateStructuredEvent {
    let telemetry = packet.telemetry.as_ref();
    let mut event = NativeInstallGateStructuredEvent {
        schema: NATIVE_INSTALL_GATE_EVENT_SCHEMA,
        schema_version: NATIVE_INSTALL_GATE_EVENT_SCHEMA_VERSION,
        issue: 749,
        source,
        kind,
        packet_hash: packet.packet_hash,
        telemetry_event_id: telemetry.map(|telemetry| telemetry.event_id.clone()),
        telemetry_record_sha256: telemetry.map(|telemetry| telemetry.record_sha256.clone()),
        counter_scope: telemetry
            .map(|telemetry| telemetry.counter_scope.clone())
            .unwrap_or_else(|| native_install_gate_counter_scope(packet)),
        replay_root_sha256: Some(packet.replay_binding.replay_root_sha256.clone()),
        replay_record_sha256,
        install_consumer_verdict_sha256: Some(packet.consumer_verdict.verdict_sha256.clone()),
        artifact_id: packet.artifact.artifact_id.clone(),
        manifest_checksum: packet.artifact.manifest_checksum,
        source_sha256: packet.artifact.source_sha256.clone(),
        trust_ir_sha256: packet.artifact.trust_ir_sha256.clone(),
        native_payload_sha256: packet.artifact.native_payload_sha256.clone(),
        target_checksum: packet.artifact.target_checksum,
        abi_checksum: packet.artifact.abi_checksum,
        layout_checksum: packet.artifact.layout_checksum,
        proof_policy_checksum: packet.artifact.proof_policy_checksum,
        invalidation_checksum: packet.artifact.invalidation_checksum,
        proof_report_sha256: packet.validation.proof_report_sha256.clone(),
        requested_authority: packet.requested_authority,
        install_authority,
        disposition,
        rejection_code,
        actions,
        native_call_succeeded,
        useful_native_delta,
        diagnostic_sha256,
        event_sha256: String::new(),
    };
    event.event_sha256 = event.canonical_event_sha256();
    event
}

fn native_install_gate_replay_binding(
    packet: &NativeInstallGatePacket,
    packet_hash: ArtifactChecksum,
) -> NativeInstallGateReplayBinding {
    let mut out = Vec::new();
    put_str(&mut out, "trust-cg.native_install_gate.replay_binding.v1");
    put_checksum(&mut out, packet_hash);
    put_str(&mut out, &packet.artifact.artifact_id);
    put_str(&mut out, &packet.consumer);
    put_str(&mut out, &packet.consumer_mode);
    NativeInstallGateReplayBinding {
        packet_hash,
        replay_root_sha256: format!("sha256:{}", sha256_hex(&out)),
    }
}

fn native_install_gate_consumer_verdict(
    packet: &NativeInstallGatePacket,
    packet_hash: ArtifactChecksum,
) -> NativeInstallGateConsumerVerdictBinding {
    let verdict_id = format!(
        "{}:{}:{}:{}:{}",
        packet.consumer,
        packet.consumer_mode,
        packet.surface.as_str(),
        packet.disposition.as_str(),
        packet
            .rejection_code
            .map(NativeInstallGateRejectionCode::as_str)
            .unwrap_or("accepted")
    );
    let mut out = Vec::new();
    put_str(&mut out, "trust-cg.native_install_gate.consumer_verdict.v1");
    put_checksum(&mut out, packet_hash);
    put_str(&mut out, &verdict_id);
    NativeInstallGateConsumerVerdictBinding {
        consumer: packet.consumer.clone(),
        consumer_mode: packet.consumer_mode.clone(),
        surface: packet.surface,
        verdict_id,
        verdict_sha256: format!("sha256:{}", sha256_hex(&out)),
    }
}

const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_BASE_SCHEMAS: &[&str] = &[
    PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA,
];

const PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_STALE_SCHEMAS: &[&str] = &[
    PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_RUNTIME_READINESS_PACKET_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA,
    PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA,
];

fn validate_petri_native_successor_execution_authority_diagnostic_fixture_manifest_entries(
    entries: Vec<(String, String)>,
    invalid_key_value_line_count: usize,
) -> PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestValidationReport {
    let expected_rows =
        petri_native_successor_execution_authority_diagnostic_fixture_manifest().manifest_rows();
    let expected_values: BTreeMap<_, _> = expected_rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    let expected_fixture_name_keys: Vec<_> =
        petri_native_successor_execution_authority_diagnostic_fixture_manifest()
            .entries
            .iter()
            .enumerate()
            .map(|(index, entry)| (format!("fixture.{index}.name"), entry.fixture_name))
            .collect();

    let mut values = BTreeMap::new();
    let mut duplicate_key_set = BTreeSet::new();
    for (key, value) in entries {
        if values.insert(key.clone(), value).is_some() {
            duplicate_key_set.insert(key);
        }
    }

    let missing_keys: Vec<_> = expected_values
        .keys()
        .filter(|key| !values.contains_key(*key))
        .cloned()
        .collect();
    let missing_fixture_names = expected_fixture_name_keys
        .iter()
        .filter(|(key, _)| !values.contains_key(key))
        .map(|(_, name)| *name)
        .collect();
    let mismatched_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| values.get(*key).is_some_and(|actual| actual != *expected))
        .map(|(key, _)| key.clone())
        .collect();
    let duplicate_keys = duplicate_key_set.into_iter().collect();
    let unexpected_keys: Vec<_> = values
        .keys()
        .filter(|key| !expected_values.contains_key(*key))
        .cloned()
        .collect();

    let mut report = PetriNativeSuccessorExecutionAuthorityDiagnosticFixtureManifestValidationReport {
        schema:
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_VALIDATION_SCHEMA,
        schema_version:
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_DIAGNOSTIC_FIXTURE_MANIFEST_VALIDATION_SCHEMA_VERSION,
        status: PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::FailClosed,
        reason_code: None,
        missing_keys,
        missing_fixture_names,
        mismatched_keys,
        duplicate_keys,
        unexpected_keys,
        invalid_key_value_line_count,
    };

    report.reason_code = if invalid_key_value_line_count != 0 {
        Some("invalid_diagnostic_fixture_manifest_line".to_owned())
    } else if !report.duplicate_keys.is_empty() {
        Some("duplicate_diagnostic_fixture_manifest_key".to_owned())
    } else if !report.missing_keys.is_empty() {
        Some("missing_diagnostic_fixture_manifest_key".to_owned())
    } else if !report.unexpected_keys.is_empty() {
        Some("unexpected_diagnostic_fixture_manifest_key".to_owned())
    } else if !report.mismatched_keys.is_empty() {
        Some("mismatched_diagnostic_fixture_manifest_value".to_owned())
    } else {
        report.status = PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::Accepted;
        None
    };

    report
}

fn validate_petri_native_successor_call_packet_contract_descriptor_entries(
    entries: Vec<(String, String)>,
    invalid_key_value_line_count: usize,
) -> PetriNativeSuccessorCallPacketContractHealthReport {
    let expected_rows = petri_native_successor_call_packet_contract_descriptor().manifest_rows();
    let expected_row_count = expected_rows.len();
    let observed_row_count = entries.len() + invalid_key_value_line_count;
    let expected_values: BTreeMap<_, _> = expected_rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();

    let mut values = BTreeMap::new();
    let mut duplicate_key_set = BTreeSet::new();
    for (key, value) in entries {
        if values.insert(key.clone(), value).is_some() {
            duplicate_key_set.insert(key);
        }
    }

    let missing_keys: Vec<_> = expected_values
        .keys()
        .filter(|key| !values.contains_key(*key))
        .cloned()
        .collect();
    let duplicate_keys = duplicate_key_set.into_iter().collect();
    let stale_schema_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            is_petri_native_successor_call_packet_contract_schema_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let mismatched_required_field_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            is_petri_native_successor_call_packet_contract_required_field_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let mismatched_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            !is_petri_native_successor_call_packet_contract_schema_key(key)
                && !is_petri_native_successor_call_packet_contract_required_field_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let unexpected_keys: Vec<_> = values
        .keys()
        .filter(|key| !expected_values.contains_key(*key))
        .cloned()
        .collect();

    let mut report = PetriNativeSuccessorCallPacketContractHealthReport {
        schema: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SCHEMA_VERSION,
        status: PetriNativeSuccessorCallPacketContractHealthStatus::FailClosed,
        reason_code: None,
        descriptor_id: values.get("descriptor.id").cloned(),
        descriptor_schema: values.get("descriptor.schema").cloned(),
        descriptor_schema_version: values.get("descriptor.schema_version").cloned(),
        descriptor_status: values.get("descriptor.status").cloned(),
        expected_row_count,
        observed_row_count,
        missing_keys,
        duplicate_keys,
        stale_schema_keys,
        mismatched_required_field_keys,
        mismatched_keys,
        unexpected_keys,
        invalid_key_value_line_count,
    };

    report.reason_code = if invalid_key_value_line_count != 0 {
        Some("invalid_call_packet_contract_descriptor_line".to_owned())
    } else if !report.duplicate_keys.is_empty() {
        Some("duplicate_call_packet_contract_descriptor_row".to_owned())
    } else if !report.missing_keys.is_empty() {
        Some("missing_call_packet_contract_descriptor_row".to_owned())
    } else if !report.stale_schema_keys.is_empty() {
        Some("stale_call_packet_contract_descriptor_schema".to_owned())
    } else if !report.mismatched_required_field_keys.is_empty() {
        Some("mismatched_call_packet_contract_required_field".to_owned())
    } else if !report.mismatched_keys.is_empty() {
        Some("mismatched_call_packet_contract_descriptor_value".to_owned())
    } else if !report.unexpected_keys.is_empty() {
        Some("unexpected_call_packet_contract_descriptor_row".to_owned())
    } else {
        report.status = PetriNativeSuccessorCallPacketContractHealthStatus::Healthy;
        None
    };

    report
}

fn validate_petri_native_successor_call_packet_contract_health_summary_entries(
    entries: Vec<(String, String)>,
    report: &PetriNativeSuccessorCallPacketContractHealthReport,
    invalid_key_value_line_count: usize,
) -> PetriNativeSuccessorCallPacketContractHealthSummaryValidationReport {
    let expected_summary = report.compact_summary();
    let expected_rows = expected_summary.manifest_rows();
    let expected_values: BTreeMap<_, _> = expected_rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();

    let mut values = BTreeMap::new();
    let mut duplicate_key_set = BTreeSet::new();
    for (key, value) in entries {
        if values.insert(key.clone(), value).is_some() {
            duplicate_key_set.insert(key);
        }
    }

    let missing_keys: Vec<_> = expected_values
        .keys()
        .filter(|key| !values.contains_key(*key))
        .cloned()
        .collect();
    let duplicate_keys = duplicate_key_set.into_iter().collect();
    let stale_schema_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            is_petri_native_successor_call_packet_contract_health_summary_schema_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let mismatched_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            !is_petri_native_successor_call_packet_contract_health_summary_schema_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let unexpected_keys: Vec<_> = values
        .keys()
        .filter(|key| !expected_values.contains_key(*key))
        .cloned()
        .collect();

    let mut validation = PetriNativeSuccessorCallPacketContractHealthSummaryValidationReport {
        schema: PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_VALIDATION_SCHEMA,
        schema_version:
            PETRI_NATIVE_SUCCESSOR_CALL_PACKET_CONTRACT_HEALTH_SUMMARY_VALIDATION_SCHEMA_VERSION,
        status: PetriNativeSuccessorCallPacketContractHealthSummaryValidationStatus::FailClosed,
        reason_code: None,
        expected_summary_sha256: Some(expected_summary.summary_sha256),
        observed_summary_sha256: values.get("summary.sha256").cloned(),
        missing_keys,
        duplicate_keys,
        stale_schema_keys,
        mismatched_keys,
        unexpected_keys,
        invalid_key_value_line_count,
    };

    validation.reason_code = if invalid_key_value_line_count != 0 {
        Some("invalid_call_packet_contract_health_summary_line".to_owned())
    } else if !validation.duplicate_keys.is_empty() {
        Some("duplicate_call_packet_contract_health_summary_row".to_owned())
    } else if !validation.missing_keys.is_empty() {
        Some("missing_call_packet_contract_health_summary_row".to_owned())
    } else if !validation.stale_schema_keys.is_empty() {
        Some("stale_call_packet_contract_health_summary_schema".to_owned())
    } else if !validation.mismatched_keys.is_empty() {
        Some("mismatched_call_packet_contract_health_summary_value".to_owned())
    } else if !validation.unexpected_keys.is_empty() {
        Some("unexpected_call_packet_contract_health_summary_row".to_owned())
    } else {
        validation.status =
            PetriNativeSuccessorCallPacketContractHealthSummaryValidationStatus::Accepted;
        None
    };

    validation
}

fn is_petri_native_successor_call_packet_contract_schema_key(key: &str) -> bool {
    matches!(key, "descriptor.schema" | "descriptor.schema_version")
}

fn is_petri_native_successor_call_packet_contract_required_field_key(key: &str) -> bool {
    key == "required_field_count" || key.starts_with("required_field.")
}

fn is_petri_native_successor_call_packet_contract_health_summary_schema_key(key: &str) -> bool {
    matches!(
        key,
        "summary.schema" | "summary.schema_version" | "health.schema" | "health.schema_version"
    )
}

fn push_call_packet_contract_health_list_rows(
    rows: &mut Vec<PetriNativeSuccessorCallPacketContractDescriptorRow>,
    key_prefix: &str,
    values: &[String],
) {
    rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
        format!("{key_prefix}_count"),
        values.len().to_string(),
    ));
    for (index, value) in values.iter().enumerate() {
        rows.push(PetriNativeSuccessorCallPacketContractDescriptorRow::new(
            format!("{key_prefix}.{index}"),
            value.as_str(),
        ));
    }
}

fn put_actions(out: &mut Vec<u8>, actions: NativeInstallGateActions) {
    put_bool(out, actions.expose_callable);
    put_bool(out, actions.typed_symbol_lookup);
    put_bool(out, actions.insert_installable_cache);
    put_bool(out, actions.accept_installable_cache_hit);
    put_bool(out, actions.release_installable);
    put_bool(out, actions.ay_registry_insert);
    put_bool(out, actions.ty_native_activate);
    put_bool(out, actions.useful_native_eligible);
}

#[derive(Debug, Clone, Copy)]
struct PetriNativeSuccessorExecutionAuthorityManifestEntry<'a> {
    key: &'a str,
    value: &'a str,
}

fn petri_native_successor_execution_authority_replay_identity_from_entries(
    entries: &[PetriNativeSuccessorExecutionAuthorityManifestEntry<'_>],
    invalid_lines: &[String],
) -> PetriNativeSuccessorExecutionAuthorityReplayIdentity {
    let validation_report = validate_petri_native_successor_execution_authority_manifest_entries(
        entries,
        invalid_lines.len(),
    );
    let canonical_text = petri_native_successor_execution_authority_replay_identity_canonical_text(
        entries,
        invalid_lines,
        &validation_report,
    );
    let replay_identity_sha256 = format!("sha256:{}", sha256_hex(canonical_text.as_bytes()));
    PetriNativeSuccessorExecutionAuthorityReplayIdentity {
        schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA_VERSION,
        required_key_count: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_REQUIRED_KEYS.len(),
        emitted_row_count: entries.len(),
        validation_status: validation_report.status,
        validation_reason_code: validation_report.reason_code.clone(),
        canonical_text,
        replay_identity_sha256,
        validation_report,
    }
}

fn petri_native_successor_execution_authority_summary_from_entries(
    entries: &[PetriNativeSuccessorExecutionAuthorityManifestEntry<'_>],
    invalid_lines: &[String],
) -> PetriNativeSuccessorExecutionAuthoritySummary {
    let replay = petri_native_successor_execution_authority_replay_identity_from_entries(
        entries,
        invalid_lines,
    );
    let mut values = BTreeMap::new();
    for entry in entries {
        values.entry(entry.key).or_insert(entry.value);
    }
    PetriNativeSuccessorExecutionAuthoritySummary::from_replay_identity(
        &replay,
        petri_native_successor_manifest_entry_value(
            &values,
            PetriNativeSuccessorHandoffManifestRowKind::AuthorizedForExecution.as_str(),
        )
        .map(|value| value == "true"),
        petri_native_successor_manifest_entry_value(
            &values,
            PetriNativeSuccessorHandoffManifestRowKind::AuthorizesUsefulNative.as_str(),
        )
        .map(|value| value == "true"),
        petri_native_successor_manifest_entry_value(
            &values,
            PetriNativeSuccessorHandoffManifestRowKind::ExecutionAuthoritySha256.as_str(),
        )
        .filter(|value| !missing_required_text(value))
        .map(str::to_owned),
    )
}

fn petri_native_successor_execution_authority_diagnostic_count(
    report: &PetriNativeSuccessorExecutionAuthorityManifestValidationReport,
) -> usize {
    let structural_count = report.invalid_key_value_line_count
        + report.missing_required_keys.len()
        + report.duplicate_keys.len()
        + report.blank_required_value_keys.len();
    if structural_count == 0 && report.reason_code.is_some() {
        1
    } else {
        structural_count
    }
}

fn validate_petri_native_successor_execution_authority_summary_entries(
    entries: Vec<(String, String)>,
    authority_rows: &[PetriNativeSuccessorHandoffManifestRow],
    invalid_key_value_line_count: usize,
    invalid_json_reason_code: Option<String>,
) -> PetriNativeSuccessorExecutionAuthoritySummaryValidationReport {
    let expected_summary =
        petri_native_successor_execution_authority_summary_for_manifest_rows(authority_rows);
    let expected_rows = expected_summary.manifest_rows();
    let expected_values: BTreeMap<_, _> = expected_rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();

    let mut values = BTreeMap::new();
    let mut duplicate_key_set = BTreeSet::new();
    for (key, value) in entries {
        if values.insert(key.clone(), value).is_some() {
            duplicate_key_set.insert(key);
        }
    }

    let missing_keys: Vec<_> = expected_values
        .keys()
        .filter(|key| !values.contains_key(*key))
        .cloned()
        .collect();
    let duplicate_keys = duplicate_key_set.into_iter().collect();
    let stale_schema_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            is_petri_native_successor_execution_authority_summary_schema_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let mismatched_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            !is_petri_native_successor_execution_authority_summary_schema_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let unexpected_keys: Vec<_> = values
        .keys()
        .filter(|key| !expected_values.contains_key(*key))
        .cloned()
        .collect();

    let mut validation = PetriNativeSuccessorExecutionAuthoritySummaryValidationReport {
        schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_VALIDATION_SCHEMA,
        schema_version:
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SUMMARY_VALIDATION_SCHEMA_VERSION,
        status: PetriNativeSuccessorExecutionAuthoritySummaryValidationStatus::FailClosed,
        reason_code: invalid_json_reason_code,
        expected_summary_sha256: Some(expected_summary.summary_sha256),
        observed_summary_sha256: values.get("summary.sha256").cloned(),
        missing_keys,
        duplicate_keys,
        stale_schema_keys,
        mismatched_keys,
        unexpected_keys,
        invalid_key_value_line_count,
    };

    if validation.reason_code.is_some() {
        return validation;
    }

    validation.reason_code = if invalid_key_value_line_count != 0 {
        Some("invalid_execution_authority_summary_line".to_owned())
    } else if !validation.duplicate_keys.is_empty() {
        Some("duplicate_execution_authority_summary_row".to_owned())
    } else if !validation.missing_keys.is_empty() {
        Some("missing_execution_authority_summary_row".to_owned())
    } else if !validation.stale_schema_keys.is_empty() {
        Some("stale_execution_authority_summary_schema".to_owned())
    } else if !validation.mismatched_keys.is_empty() {
        Some("mismatched_execution_authority_summary_value".to_owned())
    } else if !validation.unexpected_keys.is_empty() {
        Some("unexpected_execution_authority_summary_row".to_owned())
    } else {
        validation.status = PetriNativeSuccessorExecutionAuthoritySummaryValidationStatus::Accepted;
        None
    };

    validation
}

fn petri_native_successor_execution_authority_summary_json_entries(
    value: &serde_json::Value,
) -> Result<Vec<(String, String)>, String> {
    let Some(object) = value.as_object() else {
        return Err("invalid_execution_authority_summary_json_shape".to_owned());
    };
    let mut entries = Vec::with_capacity(object.len());
    for (key, value) in object {
        let Some(value) = value.as_str() else {
            return Err("invalid_execution_authority_summary_json_value".to_owned());
        };
        entries.push((key.clone(), value.to_owned()));
    }
    Ok(entries)
}

fn is_petri_native_successor_execution_authority_summary_schema_key(key: &str) -> bool {
    matches!(
        key,
        "summary.schema"
            | "summary.schema_version"
            | "evidence.schema"
            | "evidence.schema_version"
            | "validation.schema"
            | "validation.schema_version"
            | "replay_identity.schema"
            | "replay_identity.schema_version"
    )
}

fn validate_petri_native_successor_trust_mc_admission_route_descriptor_entries(
    entries: Vec<(String, String)>,
    invalid_key_value_line_count: usize,
    invalid_json_reason_code: Option<String>,
) -> PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationReport {
    let expected_descriptor = petri_native_successor_trust_mc_admission_route_descriptor();
    let expected_rows = expected_descriptor.manifest_rows();
    let expected_values: BTreeMap<_, _> = expected_rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();

    let mut values = BTreeMap::new();
    let mut duplicate_key_set = BTreeSet::new();
    for (key, value) in entries {
        if values.insert(key.clone(), value).is_some() {
            duplicate_key_set.insert(key);
        }
    }

    let missing_keys: Vec<_> = expected_values
        .keys()
        .filter(|key| !values.contains_key(*key))
        .cloned()
        .collect();
    let duplicate_keys = duplicate_key_set.into_iter().collect();
    let stale_schema_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            is_petri_native_successor_trust_mc_admission_route_descriptor_schema_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let mismatched_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            !is_petri_native_successor_trust_mc_admission_route_descriptor_schema_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let unexpected_keys: Vec<_> = values
        .keys()
        .filter(|key| !expected_values.contains_key(*key))
        .cloned()
        .collect();

    let mut validation = PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationReport {
        schema: PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_VALIDATION_SCHEMA,
        schema_version:
            PETRI_NATIVE_SUCCESSOR_TRUST_MC_ADMISSION_ROUTE_DESCRIPTOR_VALIDATION_SCHEMA_VERSION,
        status: PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationStatus::FailClosed,
        reason_code: invalid_json_reason_code,
        expected_descriptor_sha256: Some(expected_descriptor.descriptor_sha256()),
        observed_descriptor_sha256: values.get("descriptor.sha256").cloned(),
        missing_keys,
        duplicate_keys,
        stale_schema_keys,
        mismatched_keys,
        unexpected_keys,
        invalid_key_value_line_count,
    };

    if validation.reason_code.is_some() {
        return validation;
    }

    validation.reason_code = if invalid_key_value_line_count != 0 {
        Some("invalid_trust_mc_admission_route_descriptor_line".to_owned())
    } else if !validation.duplicate_keys.is_empty() {
        Some("duplicate_trust_mc_admission_route_descriptor_row".to_owned())
    } else if !validation.missing_keys.is_empty() {
        Some("missing_trust_mc_admission_route_descriptor_row".to_owned())
    } else if !validation.stale_schema_keys.is_empty() {
        Some("stale_trust_mc_admission_route_descriptor_schema".to_owned())
    } else if !validation.mismatched_keys.is_empty() {
        Some("mismatched_trust_mc_admission_route_descriptor_value".to_owned())
    } else if !validation.unexpected_keys.is_empty() {
        Some("unexpected_trust_mc_admission_route_descriptor_row".to_owned())
    } else {
        validation.status =
            PetriNativeSuccessorTrustMcAdmissionRouteDescriptorValidationStatus::Accepted;
        None
    };

    validation
}

fn validate_petri_native_successor_producer_bridge_descriptor_entries(
    entries: Vec<(String, String)>,
    invalid_key_value_line_count: usize,
) -> PetriNativeSuccessorProducerBridgeDescriptorValidationReport {
    let expected_descriptor = petri_native_successor_producer_bridge_descriptor();
    let expected_rows = expected_descriptor.manifest_rows();
    let expected_values: BTreeMap<_, _> = expected_rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();

    let mut values = BTreeMap::new();
    let mut duplicate_key_set = BTreeSet::new();
    for (key, value) in entries {
        if values.insert(key.clone(), value).is_some() {
            duplicate_key_set.insert(key);
        }
    }

    let missing_keys: Vec<_> = expected_values
        .keys()
        .filter(|key| !values.contains_key(*key))
        .cloned()
        .collect();
    let duplicate_keys = duplicate_key_set.into_iter().collect();
    let stale_schema_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            is_petri_native_successor_producer_bridge_descriptor_schema_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let mismatched_keys: Vec<_> = expected_values
        .iter()
        .filter(|(key, expected)| {
            !is_petri_native_successor_producer_bridge_descriptor_schema_key(key)
                && values.get(*key).is_some_and(|actual| actual != *expected)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let unexpected_keys: Vec<_> = values
        .keys()
        .filter(|key| !expected_values.contains_key(*key))
        .cloned()
        .collect();

    let mut validation = PetriNativeSuccessorProducerBridgeDescriptorValidationReport {
        schema: PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_VALIDATION_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_PRODUCER_BRIDGE_DESCRIPTOR_VALIDATION_SCHEMA_VERSION,
        status: PetriNativeSuccessorProducerBridgeDescriptorValidationStatus::FailClosed,
        reason_code: None,
        expected_descriptor_sha256: Some(expected_descriptor.descriptor_sha256()),
        observed_descriptor_sha256: values.get("descriptor.sha256").cloned(),
        missing_keys,
        duplicate_keys,
        stale_schema_keys,
        mismatched_keys,
        unexpected_keys,
        invalid_key_value_line_count,
    };

    validation.reason_code = if invalid_key_value_line_count != 0 {
        Some("invalid_producer_bridge_descriptor_line".to_owned())
    } else if !validation.duplicate_keys.is_empty() {
        Some("duplicate_producer_bridge_descriptor_row".to_owned())
    } else if !validation.missing_keys.is_empty() {
        Some("missing_producer_bridge_descriptor_row".to_owned())
    } else if !validation.stale_schema_keys.is_empty() {
        Some("stale_producer_bridge_descriptor_schema".to_owned())
    } else if !validation.mismatched_keys.is_empty() {
        Some("mismatched_producer_bridge_descriptor_value".to_owned())
    } else if !validation.unexpected_keys.is_empty() {
        Some("unexpected_producer_bridge_descriptor_row".to_owned())
    } else {
        validation.status = PetriNativeSuccessorProducerBridgeDescriptorValidationStatus::Accepted;
        None
    };

    validation
}

fn petri_native_successor_trust_mc_admission_route_descriptor_json_entries(
    value: &serde_json::Value,
) -> Result<Vec<(String, String)>, String> {
    let Some(object) = value.as_object() else {
        return Err("invalid_trust_mc_admission_route_descriptor_json_shape".to_owned());
    };
    let mut entries = Vec::with_capacity(object.len());
    for (key, value) in object {
        let Some(value) = value.as_str() else {
            return Err("invalid_trust_mc_admission_route_descriptor_json_value".to_owned());
        };
        entries.push((key.clone(), value.to_owned()));
    }
    Ok(entries)
}

fn is_petri_native_successor_trust_mc_admission_route_descriptor_schema_key(key: &str) -> bool {
    matches!(
        key,
        "descriptor.schema"
            | "descriptor.schema_version"
            | "trust_ir.native_bundle_identity.schema"
            | "trust_ir.native_bundle_identity.schema_version"
            | "trust_ir.trust_mc_chc.contract_schema"
            | "trust_ir.trust_mc_chc.contract_schema_version"
            | "trust_ir.shared_primitive.schema"
            | "trust_ir.shared_primitive.schema_version"
            | "trust_ir.readiness_report.schema"
            | "trust_ir.readiness_report.schema_version"
            | "trust-cg.admission.summary_schema"
            | "trust-cg.admission.summary_schema_version"
            | "trust-cg.execution_authority.schema"
            | "trust-cg.execution_authority.schema_version"
            | "trust-cg.execution_authority.summary_schema"
            | "trust-cg.execution_authority.summary_schema_version"
            | "trust-cg.execution_authority.summary_validation_schema"
            | "trust-cg.execution_authority.summary_validation_schema_version"
    )
}

fn is_petri_native_successor_producer_bridge_descriptor_schema_key(key: &str) -> bool {
    matches!(
        key,
        "descriptor.schema"
            | "descriptor.schema_version"
            | "downstream_contract.schema"
            | "downstream_contract.schema_version"
            | "trust_mc_admission_route.schema"
            | "trust_mc_admission_route.schema_version"
            | "call_packet_contract.schema"
            | "call_packet_contract.schema_version"
            | "compile_artifact_handoff.schema"
            | "compile_artifact_handoff.schema_version"
            | "runtime_readiness.schema"
            | "runtime_readiness.schema_version"
            | "execution_authority.schema"
            | "execution_authority.schema_version"
            | "execution_authority.summary_schema"
            | "execution_authority.summary_schema_version"
            | "execution_authority.summary_validation_schema"
            | "execution_authority.summary_validation_schema_version"
            | "runtime_call.schema"
            | "runtime_call.schema_version"
    )
}

fn petri_native_successor_execution_authority_diagnostic_fixture(
    fixture_name: &'static str,
    manifest_rows: Vec<PetriNativeSuccessorHandoffManifestRow>,
) -> PetriNativeSuccessorExecutionAuthorityDiagnosticFixture {
    let manifest_key_value_lines = manifest_rows
        .iter()
        .map(PetriNativeSuccessorHandoffManifestRow::to_key_value_line)
        .collect();
    let validation_report =
        validate_petri_native_successor_execution_authority_manifest_rows(&manifest_rows);
    let replay_identity =
        petri_native_successor_execution_authority_replay_identity_for_manifest_rows(
            &manifest_rows,
        );
    PetriNativeSuccessorExecutionAuthorityDiagnosticFixture {
        fixture_name,
        manifest_rows,
        manifest_key_value_lines,
        validation_report,
        replay_identity,
    }
}

fn petri_native_successor_execution_authority_healthy_diagnostic_rows()
-> Vec<PetriNativeSuccessorHandoffManifestRow> {
    vec![
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::ManifestSchema,
            PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA,
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::ManifestSchemaVersion,
            PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA_VERSION.to_string(),
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::Surface,
            "execution_authority",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::EvidenceSchema,
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA,
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::EvidenceSchemaVersion,
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA_VERSION.to_string(),
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::Status,
            "authorized",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::AuthorizedForExecution,
            "true",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::ReasonCode,
            "",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::SourceReasonCode,
            "",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::RequiredField,
            "",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::RequiredEvidence,
            "",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactHandoffSha256,
            "sha256:1111111111111111111111111111111111111111111111111111111111111111",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeReadinessPacketSha256,
            "sha256:2222222222222222222222222222222222222222222222222222222222222222",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactHandoffHashCurrent,
            "true",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeReadinessPacketHashCurrent,
            "true",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactNativePayloadSha256,
            "sha256:3333333333333333333333333333333333333333333333333333333333333333",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeNativePayloadSha256,
            "sha256:3333333333333333333333333333333333333333333333333333333333333333",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactEntrySymbol,
            "petri_successor_entry",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeEntrySymbol,
            "petri_successor_entry",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactCallablePointer,
            "0x1000",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeCallablePointer,
            "0x1000",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::CallPacketSha256,
            "sha256:4444444444444444444444444444444444444444444444444444444444444444",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::InstallPacketHash,
            "trust-cg-stable128:55555555555555555555555555555555",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::PersistedInstallPacketHash,
            "trust-cg-stable128:55555555555555555555555555555555",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::ManifestIdentitySha256,
            "sha256:6666666666666666666666666666666666666666666666666666666666666666",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::CallableAuthorized,
            "true",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::ReadyForRuntimeCall,
            "true",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::RuntimeAuthorizesUsefulNative,
            "true",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::AuthorizesUsefulNative,
            "true",
        ),
        PetriNativeSuccessorHandoffManifestRow::typed(
            PetriNativeSuccessorHandoffManifestRowKind::ExecutionAuthoritySha256,
            "sha256:7777777777777777777777777777777777777777777777777777777777777777",
        ),
    ]
}

fn set_petri_native_successor_diagnostic_row(
    rows: &mut [PetriNativeSuccessorHandoffManifestRow],
    kind: PetriNativeSuccessorHandoffManifestRowKind,
    value: impl Into<String>,
) {
    let key = kind.as_str();
    if let Some(row) = rows.iter_mut().find(|row| row.key == key) {
        row.value = value.into();
    }
}

fn petri_native_successor_execution_authority_replay_identity_canonical_text(
    entries: &[PetriNativeSuccessorExecutionAuthorityManifestEntry<'_>],
    invalid_lines: &[String],
    validation_report: &PetriNativeSuccessorExecutionAuthorityManifestValidationReport,
) -> String {
    let mut out = String::new();
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "identity.schema",
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA,
    );
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "identity.schema_version",
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_REPLAY_IDENTITY_SCHEMA_VERSION.to_string(),
    );
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "manifest.required_key_schema",
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA,
    );
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "manifest.required_key_schema_version",
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA_VERSION.to_string(),
    );
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "validation.status",
        validation_report.status.as_str(),
    );
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "validation.reason_code",
        validation_report.reason_code.as_deref().unwrap_or(""),
    );
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "validation.evidence_status_code",
        validation_report
            .evidence_status_code
            .as_deref()
            .unwrap_or(""),
    );
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "validation.evidence_reason_code",
        validation_report
            .evidence_reason_code
            .as_deref()
            .unwrap_or(""),
    );
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "validation.invalid_key_value_line_count",
        validation_report.invalid_key_value_line_count.to_string(),
    );
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "manifest.required_key_count",
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_REQUIRED_KEYS
            .len()
            .to_string(),
    );
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "manifest.emitted_row_count",
        entries.len().to_string(),
    );

    let mut values_by_key: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for entry in entries {
        values_by_key
            .entry(entry.key)
            .or_default()
            .push(entry.value);
    }
    for values in values_by_key.values_mut() {
        values.sort_unstable();
    }

    for (index, key) in PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_REQUIRED_KEYS
        .iter()
        .copied()
        .enumerate()
    {
        push_petri_native_successor_replay_identity_line(
            &mut out,
            format!("required_key.{index}.name"),
            key,
        );
        let values = values_by_key.get(key).map(Vec::as_slice).unwrap_or(&[]);
        push_petri_native_successor_replay_identity_line(
            &mut out,
            format!("required_key.{index}.value_count"),
            values.len().to_string(),
        );
        for (value_index, value) in values.iter().copied().enumerate() {
            push_petri_native_successor_replay_identity_line(
                &mut out,
                format!("required_key.{index}.value.{value_index}"),
                value,
            );
        }
    }

    let required_keys: BTreeSet<_> =
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_REQUIRED_KEYS
            .iter()
            .copied()
            .collect();
    let mut extra_rows = Vec::new();
    for entry in entries {
        if !required_keys.contains(entry.key) {
            extra_rows.push((entry.key, entry.value));
        }
    }
    extra_rows.sort_unstable();
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "manifest.extra_row_count",
        extra_rows.len().to_string(),
    );
    for (index, (key, value)) in extra_rows.into_iter().enumerate() {
        push_petri_native_successor_replay_identity_line(
            &mut out,
            format!("extra_row.{index}.key"),
            key,
        );
        push_petri_native_successor_replay_identity_line(
            &mut out,
            format!("extra_row.{index}.value"),
            value,
        );
    }

    push_petri_native_successor_replay_identity_line(
        &mut out,
        "validation.missing_required_key_count",
        validation_report.missing_required_keys.len().to_string(),
    );
    for (index, key) in validation_report
        .missing_required_keys
        .iter()
        .copied()
        .enumerate()
    {
        push_petri_native_successor_replay_identity_line(
            &mut out,
            format!("validation.missing_required_key.{index}"),
            key,
        );
    }
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "validation.duplicate_key_count",
        validation_report.duplicate_keys.len().to_string(),
    );
    for (index, key) in validation_report.duplicate_keys.iter().enumerate() {
        push_petri_native_successor_replay_identity_line(
            &mut out,
            format!("validation.duplicate_key.{index}"),
            key,
        );
    }
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "validation.blank_required_value_key_count",
        validation_report
            .blank_required_value_keys
            .len()
            .to_string(),
    );
    for (index, key) in validation_report
        .blank_required_value_keys
        .iter()
        .copied()
        .enumerate()
    {
        push_petri_native_successor_replay_identity_line(
            &mut out,
            format!("validation.blank_required_value_key.{index}"),
            key,
        );
    }
    push_petri_native_successor_replay_identity_line(
        &mut out,
        "manifest.invalid_line_count",
        invalid_lines.len().to_string(),
    );
    let mut sorted_invalid_lines = invalid_lines.to_vec();
    sorted_invalid_lines.sort_unstable();
    for (index, line) in sorted_invalid_lines.iter().enumerate() {
        push_petri_native_successor_replay_identity_line(
            &mut out,
            format!("manifest.invalid_line.{index}"),
            line,
        );
    }
    out
}

fn push_petri_native_successor_replay_identity_line(
    out: &mut String,
    key: impl AsRef<str>,
    value: impl AsRef<str>,
) {
    out.push_str(&escape_petri_native_successor_handoff_manifest_component(
        key.as_ref(),
    ));
    out.push('=');
    out.push_str(&escape_petri_native_successor_handoff_manifest_component(
        value.as_ref(),
    ));
    out.push('\n');
}

fn validate_petri_native_successor_execution_authority_manifest_entries(
    entries: &[PetriNativeSuccessorExecutionAuthorityManifestEntry<'_>],
    invalid_key_value_line_count: usize,
) -> PetriNativeSuccessorExecutionAuthorityManifestValidationReport {
    let mut values = BTreeMap::new();
    let mut duplicate_key_set = BTreeSet::new();
    for entry in entries {
        if values.insert(entry.key, entry.value).is_some() {
            duplicate_key_set.insert(entry.key.to_owned());
        }
    }

    let missing_required_keys = PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_REQUIRED_KEYS
        .iter()
        .copied()
        .filter(|key| !values.contains_key(key))
        .collect();
    let duplicate_keys = duplicate_key_set.into_iter().collect();
    let evidence_status_code = petri_native_successor_manifest_entry_value(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::Status.as_str(),
    )
    .map(str::to_owned);
    let evidence_reason_code = petri_native_successor_manifest_entry_value(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::ReasonCode.as_str(),
    )
    .filter(|reason| !missing_required_text(reason))
    .map(str::to_owned);
    let mut report = PetriNativeSuccessorExecutionAuthorityManifestValidationReport {
        schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA,
        schema_version:
            PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_VALIDATION_SCHEMA_VERSION,
        status: PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::FailClosed,
        reason_code: None,
        evidence_status_code,
        evidence_reason_code,
        missing_required_keys,
        duplicate_keys,
        blank_required_value_keys: Vec::new(),
        invalid_key_value_line_count,
    };

    if invalid_key_value_line_count != 0 {
        report.reason_code = Some("invalid_authority_manifest_line".to_owned());
        return report;
    }
    if !report.duplicate_keys.is_empty() {
        report.reason_code = Some("duplicate_authority_manifest_key".to_owned());
        return report;
    }
    if !report.missing_required_keys.is_empty() {
        report.reason_code = Some("missing_required_authority_manifest_key".to_owned());
        return report;
    }

    if petri_native_successor_manifest_entry_value(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::ManifestSchema.as_str(),
    ) != Some(PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA)
    {
        report.reason_code = Some("unsupported_authority_manifest_schema".to_owned());
        return report;
    }
    if !petri_native_successor_manifest_entry_matches_u32(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::ManifestSchemaVersion.as_str(),
        PETRI_NATIVE_SUCCESSOR_HANDOFF_EVIDENCE_MANIFEST_SCHEMA_VERSION,
    ) {
        report.reason_code = Some("unsupported_authority_manifest_schema_version".to_owned());
        return report;
    }
    if petri_native_successor_manifest_entry_value(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::Surface.as_str(),
    ) != Some("execution_authority")
    {
        report.reason_code = Some("unsupported_authority_manifest_surface".to_owned());
        return report;
    }
    if petri_native_successor_manifest_entry_value(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::EvidenceSchema.as_str(),
    ) != Some(PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA)
    {
        report.reason_code = Some("unsupported_execution_authority_schema".to_owned());
        return report;
    }
    if !petri_native_successor_manifest_entry_matches_u32(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::EvidenceSchemaVersion.as_str(),
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA_VERSION,
    ) {
        report.reason_code = Some("unsupported_execution_authority_schema_version".to_owned());
        return report;
    }

    match petri_native_successor_manifest_entry_value(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::Status.as_str(),
    ) {
        Some("authorized") => {}
        Some("fail_closed") => {
            report.reason_code = report
                .evidence_reason_code
                .clone()
                .or_else(|| Some("authority_evidence_fail_closed".to_owned()));
            return report;
        }
        _ => {
            report.reason_code = Some("unsupported_execution_authority_status".to_owned());
            return report;
        }
    }

    if report.evidence_reason_code.is_some()
        || !matches!(
            petri_native_successor_manifest_entry_value(
                &values,
                PetriNativeSuccessorHandoffManifestRowKind::SourceReasonCode.as_str(),
            ),
            Some("")
        )
        || !matches!(
            petri_native_successor_manifest_entry_value(
                &values,
                PetriNativeSuccessorHandoffManifestRowKind::RequiredField.as_str(),
            ),
            Some("")
        )
        || !matches!(
            petri_native_successor_manifest_entry_value(
                &values,
                PetriNativeSuccessorHandoffManifestRowKind::RequiredEvidence.as_str(),
            ),
            Some("")
        )
    {
        report.reason_code = Some("authorized_authority_reason_present".to_owned());
        return report;
    }

    report.blank_required_value_keys =
        PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_MANIFEST_ACCEPTED_REQUIRED_VALUE_KEYS
            .iter()
            .copied()
            .filter(|key| {
                petri_native_successor_manifest_entry_value(&values, key)
                    .map(missing_required_text)
                    .unwrap_or(true)
            })
            .collect();
    if !report.blank_required_value_keys.is_empty() {
        report.reason_code = Some("missing_required_authority_manifest_value".to_owned());
        return report;
    }

    if !petri_native_successor_manifest_entry_is_true(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::AuthorizedForExecution.as_str(),
    ) {
        report.reason_code = Some("authority_not_authorized".to_owned());
        return report;
    }
    if !petri_native_successor_manifest_entry_is_true(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactHandoffHashCurrent.as_str(),
    ) {
        report.reason_code = Some("compile_artifact_handoff_hash_not_current".to_owned());
        return report;
    }
    if !petri_native_successor_manifest_entry_is_true(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::RuntimeReadinessPacketHashCurrent.as_str(),
    ) {
        report.reason_code = Some("runtime_readiness_packet_hash_not_current".to_owned());
        return report;
    }
    if !petri_native_successor_manifest_entry_is_true(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::CallableAuthorized.as_str(),
    ) || !petri_native_successor_manifest_entry_is_true(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::ReadyForRuntimeCall.as_str(),
    ) || !petri_native_successor_manifest_entry_is_true(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::RuntimeAuthorizesUsefulNative.as_str(),
    ) {
        report.reason_code = Some("runtime_not_authoritative".to_owned());
        return report;
    }
    if !petri_native_successor_manifest_entry_is_true(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::AuthorizesUsefulNative.as_str(),
    ) {
        report.reason_code = Some("native_not_authoritative".to_owned());
        return report;
    }

    if !petri_native_successor_manifest_entries_match(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactNativePayloadSha256.as_str(),
        PetriNativeSuccessorHandoffManifestRowKind::RuntimeNativePayloadSha256.as_str(),
    ) || !petri_native_successor_manifest_entries_match(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactEntrySymbol.as_str(),
        PetriNativeSuccessorHandoffManifestRowKind::RuntimeEntrySymbol.as_str(),
    ) || !petri_native_successor_manifest_entries_match(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::CompileArtifactCallablePointer.as_str(),
        PetriNativeSuccessorHandoffManifestRowKind::RuntimeCallablePointer.as_str(),
    ) || !petri_native_successor_manifest_entries_match(
        &values,
        PetriNativeSuccessorHandoffManifestRowKind::InstallPacketHash.as_str(),
        PetriNativeSuccessorHandoffManifestRowKind::PersistedInstallPacketHash.as_str(),
    ) {
        report.reason_code = Some("authority_manifest_identity_mismatch".to_owned());
        return report;
    }

    report.status = PetriNativeSuccessorExecutionAuthorityManifestValidationStatus::Accepted;
    report.reason_code = None;
    report
}

fn petri_native_successor_manifest_entry_value<'a>(
    values: &BTreeMap<&'a str, &'a str>,
    key: &str,
) -> Option<&'a str> {
    values.get(key).copied()
}

fn petri_native_successor_manifest_entry_matches_u32(
    values: &BTreeMap<&str, &str>,
    key: &str,
    expected: u32,
) -> bool {
    petri_native_successor_manifest_entry_value(values, key)
        .and_then(|value| value.parse::<u32>().ok())
        == Some(expected)
}

fn petri_native_successor_manifest_entry_is_true(values: &BTreeMap<&str, &str>, key: &str) -> bool {
    petri_native_successor_manifest_entry_value(values, key) == Some("true")
}

fn petri_native_successor_manifest_entries_match(
    values: &BTreeMap<&str, &str>,
    left: &str,
    right: &str,
) -> bool {
    match (
        petri_native_successor_manifest_entry_value(values, left),
        petri_native_successor_manifest_entry_value(values, right),
    ) {
        (Some(left), Some(right)) => left == right,
        _ => false,
    }
}

fn parse_petri_native_successor_handoff_manifest_key_value_lines<T: AsRef<str>>(
    lines: &[T],
) -> (Vec<(String, String)>, Vec<String>) {
    let mut parsed_lines = Vec::new();
    let mut invalid_lines = Vec::new();
    for line in lines {
        let line = line.as_ref();
        if let Some((key, value)) =
            split_petri_native_successor_handoff_manifest_key_value_line(line)
        {
            parsed_lines.push((key, value));
        } else {
            invalid_lines.push(line.to_owned());
        }
    }
    (parsed_lines, invalid_lines)
}

fn split_petri_native_successor_handoff_manifest_key_value_line(
    line: &str,
) -> Option<(String, String)> {
    let mut escaped = false;
    for (index, ch) in line.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        match ch {
            '\\' => escaped = true,
            '=' => {
                return Some((
                    unescape_petri_native_successor_handoff_manifest_component(&line[..index]),
                    unescape_petri_native_successor_handoff_manifest_component(
                        &line[index + ch.len_utf8()..],
                    ),
                ));
            }
            _ => {}
        }
    }
    None
}

fn unescape_petri_native_successor_handoff_manifest_component(value: &str) -> String {
    let mut unescaped = String::new();
    let mut escaped = false;
    for ch in value.chars() {
        if escaped {
            match ch {
                '\\' => unescaped.push('\\'),
                'n' => unescaped.push('\n'),
                'r' => unescaped.push('\r'),
                't' => unescaped.push('\t'),
                '=' => unescaped.push('='),
                _ => {
                    unescaped.push('\\');
                    unescaped.push(ch);
                }
            }
            escaped = false;
        } else if ch == '\\' {
            escaped = true;
        } else {
            unescaped.push(ch);
        }
    }
    if escaped {
        unescaped.push('\\');
    }
    unescaped
}

fn petri_native_successor_execution_authority_decision_base(
    handoff: Option<&PetriNativeSuccessorCompileArtifactHandoffEvidence>,
    readiness: Option<&PetriNativeSuccessorRuntimeReadinessPacket>,
) -> PetriNativeSuccessorExecutionAuthorityDecision {
    PetriNativeSuccessorExecutionAuthorityDecision {
        schema: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA,
        schema_version: PETRI_NATIVE_SUCCESSOR_EXECUTION_AUTHORITY_SCHEMA_VERSION,
        status: PetriNativeSuccessorExecutionAuthorityStatus::FailClosed,
        authorized_for_execution: false,
        reason_code: None,
        source_reason_code: None,
        required_field: None,
        required_evidence: None,
        compile_artifact_handoff_sha256: handoff
            .map(|evidence| evidence.compile_artifact_handoff_sha256.clone()),
        runtime_readiness_packet_sha256: readiness
            .map(|packet| packet.runtime_readiness_packet_sha256.clone()),
        compile_artifact_handoff_hash_current: handoff.is_some_and(|evidence| {
            !missing_required_text(&evidence.compile_artifact_handoff_sha256)
                && evidence.compile_artifact_handoff_sha256
                    == evidence.canonical_compile_artifact_handoff_sha256()
        }),
        runtime_readiness_packet_hash_current: readiness.is_some_and(|packet| {
            !missing_required_text(&packet.runtime_readiness_packet_sha256)
                && packet.runtime_readiness_packet_sha256
                    == packet.canonical_runtime_readiness_packet_sha256()
        }),
        compile_artifact_native_payload_sha256: handoff
            .and_then(|evidence| evidence.native_payload_sha256.clone()),
        runtime_native_payload_sha256: readiness
            .and_then(|packet| packet.native_payload_sha256.clone()),
        compile_artifact_entry_symbol: handoff.and_then(|evidence| evidence.entry_symbol.clone()),
        runtime_entry_symbol: readiness.and_then(|packet| packet.entry_symbol.clone()),
        compile_artifact_callable_pointer: handoff.and_then(|evidence| evidence.callable_pointer),
        runtime_callable_pointer: readiness.and_then(|packet| packet.callable_pointer),
        call_packet_available: readiness.is_some_and(|packet| packet.call_packet_available),
        call_packet_sha256: readiness.and_then(|packet| packet.call_packet_sha256.clone()),
        install_packet_hash: readiness.and_then(|packet| packet.install_packet_hash),
        persisted_install_packet_hash: readiness
            .and_then(|packet| packet.persisted_install_packet_hash),
        manifest_identity_sha256: readiness
            .and_then(|packet| packet.manifest_identity_sha256.clone()),
        callable_authorized: readiness.is_some_and(|packet| packet.callable_authorized),
        ready_for_runtime_call: readiness.is_some_and(|packet| packet.ready_for_runtime_call),
        runtime_authorizes_useful_native: readiness
            .is_some_and(PetriNativeSuccessorRuntimeReadinessPacket::authorizes_useful_native),
        execution_authority_sha256: String::new(),
    }
}

fn petri_native_successor_execution_authority_authorized(
    mut decision: PetriNativeSuccessorExecutionAuthorityDecision,
) -> PetriNativeSuccessorExecutionAuthorityDecision {
    decision.status = PetriNativeSuccessorExecutionAuthorityStatus::Authorized;
    decision.authorized_for_execution = true;
    decision.reason_code = None;
    decision.source_reason_code = None;
    decision.required_field = None;
    decision.required_evidence = None;
    decision.with_canonical_execution_authority_sha256()
}

fn petri_native_successor_execution_authority_fail_closed(
    mut decision: PetriNativeSuccessorExecutionAuthorityDecision,
    reason_code: &'static str,
    source_reason_code: Option<&'static str>,
    required_field: Option<&'static str>,
    required_evidence: Option<&'static str>,
) -> PetriNativeSuccessorExecutionAuthorityDecision {
    decision.status = PetriNativeSuccessorExecutionAuthorityStatus::FailClosed;
    decision.authorized_for_execution = false;
    decision.reason_code = Some(reason_code);
    decision.source_reason_code = source_reason_code;
    decision.required_field = required_field;
    decision.required_evidence = required_evidence;
    decision.with_canonical_execution_authority_sha256()
}

fn petri_native_successor_production_selection_fail_closed(
    mut decision: PetriNativeSuccessorProductionSelectionDecision,
    reason_code: &'static str,
    source_reason_code: Option<&'static str>,
    required_evidence: Option<&'static str>,
) -> PetriNativeSuccessorProductionSelectionDecision {
    decision.status = PetriNativeSuccessorProductionSelectionStatus::FailClosed;
    decision.selected_for_native_execution = false;
    decision.fail_closed = true;
    decision.reason_code = Some(reason_code);
    decision.source_reason_code = source_reason_code;
    decision.required_evidence = required_evidence;
    decision.with_canonical_production_selection_sha256()
}

fn push_petri_native_successor_handoff_manifest_row(
    rows: &mut Vec<PetriNativeSuccessorHandoffManifestRow>,
    kind: PetriNativeSuccessorHandoffManifestRowKind,
    value: impl Into<String>,
) {
    rows.push(PetriNativeSuccessorHandoffManifestRow::typed(kind, value));
}

const fn petri_native_successor_bool_code(value: bool) -> &'static str {
    if value { "true" } else { "false" }
}

fn option_checksum_manifest_value(value: Option<ArtifactChecksum>) -> String {
    value
        .map(|checksum| checksum.to_string())
        .unwrap_or_default()
}

fn option_callable_pointer_manifest_value(
    value: Option<PetriNativeSuccessorCallablePointer>,
) -> String {
    value
        .map(|pointer| format!("0x{:x}", pointer.addr_usize()))
        .unwrap_or_default()
}

fn escape_petri_native_successor_handoff_manifest_component(value: &str) -> String {
    let mut escaped = String::new();
    for ch in value.chars() {
        match ch {
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            '=' => escaped.push_str("\\="),
            _ => escaped.push(ch),
        }
    }
    escaped
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

fn put_str_vec(out: &mut Vec<u8>, values: &[String]) {
    put_u64(out, values.len() as u64);
    for value in values {
        put_str(out, value);
    }
}

fn put_str_map(out: &mut Vec<u8>, values: &BTreeMap<String, String>) {
    put_u64(out, values.len() as u64);
    for (key, value) in values {
        put_str(out, key);
        put_str(out, value);
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

fn put_option_u32(out: &mut Vec<u8>, value: Option<u32>) {
    if let Some(value) = value {
        put_bool(out, true);
        put_u32(out, value);
    } else {
        put_bool(out, false);
    }
}

fn put_option_i32(out: &mut Vec<u8>, value: Option<i32>) {
    if let Some(value) = value {
        put_bool(out, true);
        put_i32(out, value);
    } else {
        put_bool(out, false);
    }
}

fn put_option_bool(out: &mut Vec<u8>, value: Option<bool>) {
    if let Some(value) = value {
        put_bool(out, true);
        put_bool(out, value);
    } else {
        put_bool(out, false);
    }
}

fn put_option_checksum(out: &mut Vec<u8>, value: Option<ArtifactChecksum>) {
    if let Some(value) = value {
        put_bool(out, true);
        put_checksum(out, value);
    } else {
        put_bool(out, false);
    }
}

fn put_option_callable_pointer(
    out: &mut Vec<u8>,
    value: Option<PetriNativeSuccessorCallablePointer>,
) {
    if let Some(value) = value {
        put_bool(out, true);
        put_u64(out, value.addr_usize() as u64);
    } else {
        put_bool(out, false);
    }
}

fn put_option_deny_control(
    out: &mut Vec<u8>,
    deny_control: Option<&NativeInstallGateDenyControlPlane>,
) {
    if let Some(deny_control) = deny_control {
        put_bool(out, true);
        put_bool(out, deny_control.active);
        put_str(out, deny_control.reason.as_str());
        put_str(out, deny_control.scope.as_str());
        put_option_str(out, deny_control.consumer.as_deref());
        put_option_str(out, deny_control.family.as_deref());
        put_option_str(out, deny_control.artifact_id.as_deref());
        put_option_str(
            out,
            deny_control.mode.map(NativeInstallGateAuthority::as_str),
        );
        put_option_str(
            out,
            deny_control.surface.map(NativeInstallGateSurface::as_str),
        );
        put_option_checksum(out, deny_control.target_checksum);
        put_option_checksum(out, deny_control.proof_policy_checksum);
        put_u64(out, deny_control.freshness.len() as u64);
        for observation in &deny_control.freshness {
            put_str(out, &observation.domain);
            put_u64(out, observation.observed_generation);
            put_u64(out, observation.current_generation);
        }
        put_option_str(out, deny_control.deny_sha256.as_deref());
    } else {
        put_bool(out, false);
    }
}

fn put_option_replay_identity(
    out: &mut Vec<u8>,
    replay_identity: Option<&NativeInstallGateReplayIdentity>,
) {
    if let Some(replay_identity) = replay_identity {
        put_bool(out, true);
        put_str(out, &replay_identity.schema);
        put_u32(out, replay_identity.schema_version);
        put_str(out, &replay_identity.replay_root_sha256);
        put_str(out, &replay_identity.replay_consumer);
        put_str(out, &replay_identity.replay_family);
        put_str(out, &replay_identity.artifact_id);
        put_str(out, &replay_identity.source_sha256);
        put_str(out, &replay_identity.trust_ir_sha256);
        put_str(out, &replay_identity.native_payload_sha256);
        put_str(out, &replay_identity.replay_record_sha256);
    } else {
        put_bool(out, false);
    }
}

fn put_checksum(out: &mut Vec<u8>, value: ArtifactChecksum) {
    out.extend_from_slice(&value.get().to_le_bytes());
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_i32(out: &mut Vec<u8>, value: i32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn persisted_packet_bindings_missing(packet: &NativeInstallGatePacket) -> bool {
    missing_checksum(packet.replay_binding.packet_hash)
        || missing_required_text(&packet.replay_binding.replay_root_sha256)
        || missing_required_text(&packet.consumer_verdict.consumer)
        || missing_required_text(&packet.consumer_verdict.consumer_mode)
        || missing_required_text(&packet.consumer_verdict.verdict_id)
        || missing_required_text(&packet.consumer_verdict.verdict_sha256)
}

fn missing_optional_text(value: Option<&str>) -> bool {
    value.map(missing_required_text).unwrap_or(true)
}

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}

fn missing_checksum(value: ArtifactChecksum) -> bool {
    value == ArtifactChecksum::new(0)
}

fn artifact_packet(input: &NativeInstallGateInput) -> NativeInstallGateArtifactPacket {
    if let Some(manifest) = &input.manifest {
        NativeInstallGateArtifactPacket {
            artifact_id: manifest.artifact_id.clone(),
            manifest_schema: manifest.schema.clone(),
            manifest_schema_version: manifest.schema_version,
            manifest_checksum: manifest.checksum(),
            source_sha256: input.candidate_payload_identity.source_sha256.clone(),
            trust_ir_sha256: input.candidate_payload_identity.trust_ir_sha256.clone(),
            native_payload_sha256: input
                .candidate_payload_identity
                .native_payload_sha256
                .clone(),
            target_checksum: manifest.target.checksum(),
            abi_checksum: manifest.abi.checksum(),
            layout_checksum: manifest.layout.checksum(),
            proof_policy_checksum: manifest.proof_policy.checksum(),
            invalidation_checksum: manifest.invalidation.checksum(),
            manifest_metadata: manifest.metadata.clone(),
        }
    } else {
        NativeInstallGateArtifactPacket {
            artifact_id: input.expected.artifact_id.clone(),
            manifest_schema: String::new(),
            manifest_schema_version: 0,
            manifest_checksum: input.expected.manifest_checksum,
            source_sha256: input.candidate_payload_identity.source_sha256.clone(),
            trust_ir_sha256: input.candidate_payload_identity.trust_ir_sha256.clone(),
            native_payload_sha256: input
                .candidate_payload_identity
                .native_payload_sha256
                .clone(),
            target_checksum: input.expected.target_checksum,
            abi_checksum: input.expected.abi_checksum,
            layout_checksum: input.expected.layout_checksum,
            proof_policy_checksum: input.expected.proof_policy_checksum,
            invalidation_checksum: input.expected.invalidation_checksum,
            manifest_metadata: BTreeMap::new(),
        }
    }
}

fn layout_generation_domains(layout: &NativeInstallGateLayoutEvidence) -> Vec<String> {
    let mut domains = BTreeSet::new();
    for region in &layout.regions {
        if !missing_required_text(&region.generation_domain) {
            domains.insert(region.generation_domain.clone());
        }
    }
    for entry in &layout.entry_abis {
        if !missing_required_text(&entry.generation_domain) {
            domains.insert(entry.generation_domain.clone());
        }
    }
    domains.into_iter().collect()
}

fn validation_packet(input: &NativeInstallGateInput) -> NativeInstallGateValidationPacket {
    let layout_status = if let Some(layout) = &input.layout_evidence {
        match validate_layout_evidence(input, layout) {
            Ok(()) => "accepted",
            Err(
                NativeInstallGateRejectionCode::AbiMismatch
                | NativeInstallGateRejectionCode::LayoutMismatch
                | NativeInstallGateRejectionCode::StaleInvalidation,
            ) => "mismatch",
            Err(_) => "missing",
        }
    } else {
        "missing"
    };
    let (proof_verdict, proof_reject_code, proof_verifier) =
        if let Some(proof) = &input.proof_evidence {
            (
                proof.summary.verdict.as_str(),
                proof_reject_code_for_packet(input, proof),
                Some(proof.summary.verifier.clone()),
            )
        } else {
            ("missing_evidence", Some("proof_missing_evidence"), None)
        };
    NativeInstallGateValidationPacket {
        layout_status,
        layout_evidence_sha256: input
            .layout_evidence
            .as_ref()
            .and_then(|layout| layout.evidence_sha256.clone()),
        layout_wrapper_identity: input
            .layout_evidence
            .as_ref()
            .and_then(|layout| layout.wrapper_identity.clone()),
        layout_validation_provenance: input
            .layout_evidence
            .as_ref()
            .map(|layout| layout.validation_provenance.clone()),
        layout_invalidation_checksum: input
            .layout_evidence
            .as_ref()
            .map(|layout| layout.invalidation_checksum),
        layout_generation_domains: input
            .layout_evidence
            .as_ref()
            .map(layout_generation_domains)
            .unwrap_or_default(),
        proof_verdict,
        proof_reject_code,
        proof_verifier,
        proof_report_sha256: proof_report_sha256(input),
        obligation_set: input
            .proof_evidence
            .as_ref()
            .and_then(|proof| proof.obligation_set.clone()),
        timeout_ms: input
            .proof_evidence
            .as_ref()
            .and_then(|proof| proof.timeout_ms),
    }
}
