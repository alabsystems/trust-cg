// trust-cg-codegen/ay_pb_pbo_checked_arithmetic_contract.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only artifact contract helpers for the ay PB/PBO checked arithmetic slice.
//!
//! This module binds the manifest, ABI/layout records, signature, proof-policy,
//! and invalidation shape used by the PB/PBO checked-objective status probe. It
//! intentionally keeps native install and useful-native promotion disabled.

use std::collections::BTreeMap;

use crate::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, ArtifactSection, ArtifactSectionKind, ArtifactSymbol,
    DeterministicArtifactManifest, Endianness, FieldLayout, InvalidationKey, JitArtifactKind,
    LayoutManifest, ProofPolicy, RecordLayout, SymbolLayout, SymbolLookupContract, SymbolSignature,
    SymbolVisibility, TargetDescriptor, TargetOperatingSystem,
};
use crate::target::Target;

/// Stable schema tag for PB/PBO checked arithmetic contract helper output.
pub const AY_PB_PBO_CHECKED_ARITHMETIC_ARTIFACT_CONTRACT_SCHEMA: &str =
    "trust-cg.ay_pb_pbo_checked_arithmetic.artifact_contract.v1";

/// Stable numeric schema version for PB/PBO checked arithmetic contract helpers.
pub const AY_PB_PBO_CHECKED_ARITHMETIC_ARTIFACT_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Callable status-probe symbol named by the PB/PBO checked arithmetic contract.
pub const AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL: &str = "ay_pb_pbo_checked_objective_status";

/// Artifact id for the canonical PB/PBO checked-objective status-probe manifest.
pub const AY_PB_PBO_CHECKED_OBJECTIVE_ARTIFACT_ID: &str =
    "ay-pb-pbo-checked-objective-status-probe";

/// PB/PBO checked arithmetic kernel metadata id.
pub const AY_PB_PBO_CHECKED_ARITHMETIC_KERNEL: &str = "ay_pb_pbo_checked_objective";

/// Consumer metadata id.
pub const AY_PB_PBO_CHECKED_ARITHMETIC_CONSUMER: &str = "ay";

/// Domain metadata id.
pub const AY_PB_PBO_CHECKED_ARITHMETIC_DOMAIN: &str = "pb_pbo";

/// Rust wrapper/layout identity for the LP64 checked-objective status probe.
pub const AY_PB_PBO_CHECKED_OBJECTIVE_WRAPPER_IDENTITY: &str =
    "ay::pb_pbo::CheckedObjectiveStatus:v1";

/// Reference oracle used for PB/PBO checked-objective differential evidence.
pub const AY_PB_PBO_CHECKED_OBJECTIVE_REFERENCE_ORACLE: &str = "i128_checked_objective_reference";

/// Status ABI record name.
pub const AY_PB_PBO_OBJECTIVE_STATUS_RECORD: &str = "AYPbPboObjectiveStatusAbi";

/// Stable result/status ABI metadata id.
pub const AY_PB_PBO_OBJECTIVE_STATUS_ABI: &str = "ay_pb_pbo_objective_status_abi_v1";

/// Source invalidation fingerprint for the canonical PB/PBO checked arithmetic contract.
pub const AY_PB_PBO_CHECKED_OBJECTIVE_SOURCE_FINGERPRINT: &str = "ay:pb-pbo:checked-objective:v1";

/// Compiler/profile invalidation fingerprint for the canonical contract.
pub const AY_PB_PBO_CHECKED_OBJECTIVE_COMPILER_FINGERPRINT: &str = "trust-cg:phase7:pb-pbo:o0-o2";

/// Default pre-product generation used by the contract fixture.
pub const AY_PB_PBO_CHECKED_OBJECTIVE_DEFAULT_GENERATION: u64 = 686;

/// Canonical pre-product text size used by the manifest contract.
pub const AY_PB_PBO_CHECKED_OBJECTIVE_TEXT_SIZE_BYTES: u64 = 256;

/// Objective status ABI record size.
pub const AY_PB_PBO_OBJECTIVE_STATUS_SIZE_BYTES: u64 = 24;

/// Objective status ABI record alignment.
pub const AY_PB_PBO_OBJECTIVE_STATUS_ALIGNMENT_BYTES: u32 = 8;

/// Build the canonical PB/PBO checked-objective `extern "C"` status signature.
pub fn ay_pb_pbo_checked_objective_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            AbiValue::new(AbiValueKind::Ptr),
            AbiValue::new(AbiValueKind::Ptr),
            AbiValue::new(AbiValueKind::I64),
            AbiValue::new(AbiValueKind::Ptr),
        ],
        vec![],
    )
}

/// Build the host-OS AArch64 target descriptor for this contract.
pub fn ay_pb_pbo_checked_objective_aarch64_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target(Target::Aarch64, target_os_descriptor())
        .with_cpu("aarch64-ay-test")
        .with_features(["fp", "simd"])
}

/// Build the canonical AAPCS64/LP64 ABI descriptor for this contract.
pub fn ay_pb_pbo_checked_objective_aarch64_abi() -> AbiDescriptor {
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ay-pb-pbo-aapcs64-lp64".to_owned();
    abi
}

/// Build the checked-objective status ABI record layout.
pub fn ay_pb_pbo_objective_status_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_PB_PBO_OBJECTIVE_STATUS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: AY_PB_PBO_OBJECTIVE_STATUS_SIZE_BYTES,
        alignment_bytes: AY_PB_PBO_OBJECTIVE_STATUS_ALIGNMENT_BYTES,
        fields: vec![
            field("status", 0, 1, 1),
            field("deopt", 1, 1, 1),
            field("reserved", 2, 6, 1),
            field("objective", 8, 8, 8),
            field("detail", 16, 8, 8),
        ],
    }
}

/// Build the canonical LP64 layout manifest.
pub fn ay_pb_pbo_checked_objective_layout() -> LayoutManifest {
    ay_pb_pbo_checked_objective_layout_with_text_size(
        16,
        AY_PB_PBO_CHECKED_OBJECTIVE_TEXT_SIZE_BYTES,
    )
}

/// Build an LP64 layout manifest with caller-specified stack alignment and text size.
pub fn ay_pb_pbo_checked_objective_layout_with_text_size(
    stack_alignment_bytes: u16,
    text_size_bytes: u64,
) -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, stack_alignment_bytes);
    layout.wrapper_identity = Some(AY_PB_PBO_CHECKED_OBJECTIVE_WRAPPER_IDENTITY.to_owned());
    layout
        .records
        .push(ay_pb_pbo_objective_status_record_layout());
    layout.symbols.push(SymbolLayout {
        name: AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: text_size_bytes,
        alignment_bytes: 16,
    });
    insert_ay_pb_pbo_checked_objective_layout_metadata(&mut layout.metadata);
    layout
}

/// Build the disabled proof policy for the current non-native PB/PBO contract.
pub fn ay_pb_pbo_checked_objective_proof_policy() -> ProofPolicy {
    ProofPolicy::disabled()
}

/// Build the default invalidation key for the canonical AArch64 contract.
pub fn ay_pb_pbo_checked_objective_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    ay_pb_pbo_checked_objective_invalidation_with_generation(
        target,
        abi,
        layout,
        proof_policy,
        AY_PB_PBO_CHECKED_OBJECTIVE_DEFAULT_GENERATION,
    )
}

/// Build an invalidation key for a caller-specified generation.
pub fn ay_pb_pbo_checked_objective_invalidation_with_generation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
    generation: u64,
) -> InvalidationKey {
    let mut invalidation = InvalidationKey::new(
        AY_PB_PBO_CHECKED_OBJECTIVE_SOURCE_FINGERPRINT,
        AY_PB_PBO_CHECKED_OBJECTIVE_COMPILER_FINGERPRINT,
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        generation,
    );
    insert_ay_pb_pbo_checked_objective_invalidation_metadata(&mut invalidation.extra);
    invalidation
}

/// Build the canonical pre-product AArch64 artifact manifest.
pub fn ay_pb_pbo_checked_objective_manifest() -> DeterministicArtifactManifest {
    ay_pb_pbo_checked_objective_manifest_with_generation(
        AY_PB_PBO_CHECKED_OBJECTIVE_DEFAULT_GENERATION,
    )
}

/// Build the canonical AArch64 artifact manifest for a caller-specified generation.
pub fn ay_pb_pbo_checked_objective_manifest_with_generation(
    generation: u64,
) -> DeterministicArtifactManifest {
    let target = ay_pb_pbo_checked_objective_aarch64_target();
    let abi = ay_pb_pbo_checked_objective_aarch64_abi();
    let layout = ay_pb_pbo_checked_objective_layout();
    let proof_policy = ay_pb_pbo_checked_objective_proof_policy();
    ay_pb_pbo_checked_objective_manifest_for_parts(
        target,
        abi,
        layout,
        proof_policy,
        generation,
        AY_PB_PBO_CHECKED_OBJECTIVE_TEXT_SIZE_BYTES,
    )
}

/// Build a manifest from explicit contract parts.
pub fn ay_pb_pbo_checked_objective_manifest_for_parts(
    target: TargetDescriptor,
    abi: AbiDescriptor,
    layout: LayoutManifest,
    proof_policy: ProofPolicy,
    generation: u64,
    text_size_bytes: u64,
) -> DeterministicArtifactManifest {
    let text_size_bytes =
        ay_pb_pbo_checked_objective_layout_text_size_bytes(&layout, text_size_bytes);
    let invalidation = ay_pb_pbo_checked_objective_invalidation_with_generation(
        &target,
        &abi,
        &layout,
        &proof_policy,
        generation,
    );
    let mut manifest = DeterministicArtifactManifest::new(
        AY_PB_PBO_CHECKED_OBJECTIVE_ARTIFACT_ID,
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_pb_pbo_checked_objective_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: text_size_bytes,
        alignment_bytes: 16,
        checksum: None,
    });
    insert_ay_pb_pbo_checked_objective_manifest_metadata(&mut manifest.metadata);
    manifest
}

fn ay_pb_pbo_checked_objective_layout_text_size_bytes(
    layout: &LayoutManifest,
    fallback: u64,
) -> u64 {
    layout
        .symbols
        .iter()
        .find(|symbol| {
            symbol.name == AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL && symbol.section == ".text"
        })
        .map(|symbol| symbol.size_bytes)
        .unwrap_or(fallback)
}

/// Build the symbol lookup contract for the PB/PBO checked-objective status probe.
pub fn ay_pb_pbo_checked_objective_symbol_lookup_contract(
    manifest: &DeterministicArtifactManifest,
) -> SymbolLookupContract {
    SymbolLookupContract::new(
        AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL,
        ay_pb_pbo_checked_objective_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
}

fn target_os_descriptor() -> TargetOperatingSystem {
    if cfg!(target_os = "macos") {
        TargetOperatingSystem::Macos
    } else if cfg!(target_os = "linux") {
        TargetOperatingSystem::Linux
    } else {
        TargetOperatingSystem::Unknown
    }
}

fn insert_ay_pb_pbo_checked_objective_layout_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "kernel".to_owned(),
        AY_PB_PBO_CHECKED_ARITHMETIC_KERNEL.to_owned(),
    );
    metadata.insert(
        "status_abi".to_owned(),
        AY_PB_PBO_OBJECTIVE_STATUS_ABI.to_owned(),
    );
}

fn insert_ay_pb_pbo_checked_objective_manifest_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "consumer".to_owned(),
        AY_PB_PBO_CHECKED_ARITHMETIC_CONSUMER.to_owned(),
    );
    metadata.insert(
        "domain".to_owned(),
        AY_PB_PBO_CHECKED_ARITHMETIC_DOMAIN.to_owned(),
    );
    metadata.insert(
        "kernel".to_owned(),
        AY_PB_PBO_CHECKED_ARITHMETIC_KERNEL.to_owned(),
    );
    metadata.insert(
        "status_abi".to_owned(),
        AY_PB_PBO_OBJECTIVE_STATUS_ABI.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema".to_owned(),
        AY_PB_PBO_CHECKED_ARITHMETIC_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema_version".to_owned(),
        AY_PB_PBO_CHECKED_ARITHMETIC_ARTIFACT_CONTRACT_SCHEMA_VERSION.to_string(),
    );
    metadata.insert("native_install".to_owned(), "disabled".to_owned());
    metadata.insert("useful_native".to_owned(), "0".to_owned());
    metadata.insert(
        "promotion_disposition".to_owned(),
        "manifest_backed_test_probe".to_owned(),
    );
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_PB_PBO_CHECKED_OBJECTIVE_REFERENCE_ORACLE.to_owned(),
    );
}

fn insert_ay_pb_pbo_checked_objective_invalidation_metadata(
    metadata: &mut BTreeMap<String, String>,
) {
    metadata.insert(
        "checked_arithmetic".to_owned(),
        "i64_mul_add_overflow_deopts".to_owned(),
    );
    metadata.insert("native_install".to_owned(), "disabled".to_owned());
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_PB_PBO_CHECKED_OBJECTIVE_REFERENCE_ORACLE.to_owned(),
    );
    metadata.insert(
        "status_abi".to_owned(),
        AY_PB_PBO_OBJECTIVE_STATUS_ABI.to_owned(),
    );
    metadata.insert("useful_native".to_owned(), "0".to_owned());
}

fn field(name: &str, offset_bytes: u64, size_bytes: u64, alignment_bytes: u32) -> FieldLayout {
    FieldLayout {
        name: name.to_owned(),
        offset_bytes,
        size_bytes,
        alignment_bytes,
    }
}
