// trust-cg-codegen/tests/jit_contract_artifact.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::Target;
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, ArtifactChecksum, ArtifactContractError,
    ArtifactSection, ArtifactSectionKind, ArtifactSymbol, DeterministicArtifactManifest,
    Endianness, HOST_JIT_TARGET_FEATURE_PROFILE_CURRENT_POLICY_KEY,
    HOST_JIT_TARGET_FEATURE_PROFILE_DETECTED_HOST_FEATURES_KEY,
    HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA, HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_KEY,
    HOST_JIT_TARGET_FEATURE_PROFILE_SHA256_KEY,
    HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_FEATURES_KEY,
    HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_TRIPLE_KEY, InvalidationKey,
    JIT_ARTIFACT_MANIFEST_SCHEMA, JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION, JitArtifactKind,
    KERNEL_ARTIFACT_CONTRACT_SCHEMA, KERNEL_ARTIFACT_CONTRACT_SCHEMA_VERSION,
    KernelArtifactContract, KernelArtifactKind, KernelStateDomain, LayoutManifest,
    ProofEvidenceRejectionCode, ProofEvidenceSummary, ProofEvidenceVerdict, ProofMode, ProofPolicy,
    SymbolLookupContract, SymbolSignature, SymbolVisibility, TargetDescriptor,
    TargetOperatingSystem, target_descriptor_is_x86_64_host_jit,
};

extern "C" fn identity_i64(value: i64) -> i64 {
    value
}

const TEST_NATIVE_PAYLOAD_SHA256: &str =
    "sha256:native-payload-1111111111111111111111111111111111111111111111111111";
const TEST_PROOF_REPORT_SHA256: &str =
    "sha256:proof-report-2222222222222222222222222222222222222222222222222222";

fn bind_native_payload_metadata(manifest: &mut DeterministicArtifactManifest) {
    manifest.metadata.insert(
        "native_payload_sha256".to_owned(),
        TEST_NATIVE_PAYLOAD_SHA256.to_owned(),
    );
}

fn i64_to_i64_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![AbiValue::new(AbiValueKind::I64)],
        vec![AbiValue::new(AbiValueKind::I64)],
    )
}

fn i32_to_i64_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![AbiValue::new(AbiValueKind::I32)],
        vec![AbiValue::new(AbiValueKind::I64)],
    )
}

fn base_manifest() -> DeterministicArtifactManifest {
    let target =
        TargetDescriptor::for_trust_cg_target(Target::Aarch64, TargetOperatingSystem::Macos)
            .with_cpu("apple-m")
            .with_features(["fp", "simd"]);
    let abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let proof_policy = ProofPolicy::require_certificates(["ay", "trust-cg-verify"]);
    let invalidation = InvalidationKey::new(
        "source:abc",
        "compiler:o1",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        7,
    );

    let mut manifest = DeterministicArtifactManifest::new(
        "artifact-1",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    bind_native_payload_metadata(&mut manifest);
    manifest
}

fn manifest_with_entry() -> DeterministicArtifactManifest {
    let mut manifest = base_manifest();
    manifest.symbols.push(ArtifactSymbol {
        name: "entry".to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: i64_to_i64_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    bind_native_payload_metadata(&mut manifest);
    manifest
}

fn disabled_manifest_with_entry() -> DeterministicArtifactManifest {
    manifest_with_entry_for_policy("artifact-disabled", ProofPolicy::disabled())
}

fn audit_only_manifest_with_entry() -> DeterministicArtifactManifest {
    let mut proof_policy = ProofPolicy::disabled();
    proof_policy.mode = ProofMode::AuditOnly;
    proof_policy.require_jit_certificate = true;
    proof_policy.require_layout_evidence = true;
    proof_policy.require_abi_evidence = true;
    proof_policy.accepted_solvers = vec!["trust-cg-verify".to_owned()];
    manifest_with_entry_for_policy("artifact-audit", proof_policy)
}

fn disabled_manifest_with_public_requirement_flags() -> DeterministicArtifactManifest {
    let mut proof_policy = ProofPolicy::disabled();
    proof_policy.require_jit_certificate = true;
    proof_policy.require_layout_evidence = true;
    proof_policy.require_abi_evidence = true;
    proof_policy.accepted_solvers = vec!["trust-cg-verify".to_owned()];
    manifest_with_entry_for_policy("artifact-disabled-flags", proof_policy)
}

fn manifest_with_entry_for_policy(
    artifact_id: &str,
    proof_policy: ProofPolicy,
) -> DeterministicArtifactManifest {
    let target =
        TargetDescriptor::for_trust_cg_target(Target::Aarch64, TargetOperatingSystem::Macos);
    let abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let invalidation = InvalidationKey::new(
        "source:abc",
        "compiler:o1",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        7,
    );

    let mut manifest = DeterministicArtifactManifest::new(
        artifact_id,
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: "entry".to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: i64_to_i64_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    bind_native_payload_metadata(&mut manifest);
    manifest
}

fn x86_64_host_manifest_with_features() -> DeterministicArtifactManifest {
    let target =
        TargetDescriptor::for_trust_cg_target(Target::X86_64, TargetOperatingSystem::host())
            .with_cpu("host")
            .with_features(["sse4.2", "sse2"]);
    let abi = AbiDescriptor::for_trust_cg_target_os(Target::X86_64, TargetOperatingSystem::host());
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let proof_policy = ProofPolicy::require_certificates(["trust-cg-verify"]);
    let invalidation = InvalidationKey::new(
        "source:x86-host",
        "compiler:o2",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        11,
    );

    DeterministicArtifactManifest::new(
        "artifact-x86-host",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    )
}

fn verified_evidence(manifest: &DeterministicArtifactManifest) -> ProofEvidenceSummary {
    ProofEvidenceSummary::verified_for_artifact(
        "trust-cg-verify",
        manifest,
        TEST_NATIVE_PAYLOAD_SHA256,
        TEST_PROOF_REPORT_SHA256,
    )
}

fn entry_lookup_contract(manifest: &DeterministicArtifactManifest) -> SymbolLookupContract {
    SymbolLookupContract::new(
        "entry",
        i64_to_i64_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
}

fn entry_lookup_contract_with_evidence(
    manifest: &DeterministicArtifactManifest,
) -> SymbolLookupContract {
    entry_lookup_contract(manifest).with_proof_evidence(verified_evidence(manifest))
}

#[test]
fn x86_64_host_manifest_binds_machine_readable_target_feature_profile() {
    let manifest = x86_64_host_manifest_with_features();

    if !target_descriptor_is_x86_64_host_jit(&manifest.target) {
        assert!(
            !manifest
                .metadata
                .contains_key(HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_KEY)
        );
        return;
    }

    assert_eq!(
        manifest
            .metadata
            .get(HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_KEY)
            .map(String::as_str),
        Some(HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA)
    );
    assert_eq!(
        manifest
            .metadata
            .get(HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_TRIPLE_KEY)
            .map(String::as_str),
        Some(manifest.target.triple.as_str())
    );
    assert_eq!(
        manifest
            .metadata
            .get(HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_FEATURES_KEY)
            .map(String::as_str),
        Some("sse2,sse4.2")
    );
    assert_eq!(
        manifest
            .metadata
            .get(HOST_JIT_TARGET_FEATURE_PROFILE_CURRENT_POLICY_KEY)
            .map(String::as_str),
        Some("manifest-target-features")
    );
    assert!(
        manifest
            .metadata
            .contains_key(HOST_JIT_TARGET_FEATURE_PROFILE_DETECTED_HOST_FEATURES_KEY)
    );
    assert!(
        manifest
            .metadata
            .get(HOST_JIT_TARGET_FEATURE_PROFILE_SHA256_KEY)
            .expect("profile digest is bound")
            .starts_with("sha256:")
    );
}

fn assert_evidence_checksum_mismatch(
    manifest: &DeterministicArtifactManifest,
    component: &'static str,
    wrong_checksum: ArtifactChecksum,
    mutate: impl FnOnce(&mut ProofEvidenceSummary),
) {
    let ptr = identity_i64 as *const () as *const u8;
    let mut evidence = verified_evidence(manifest);
    mutate(&mut evidence);
    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &entry_lookup_contract(manifest).with_proof_evidence(evidence),
            ptr,
        )
        .expect_err("mismatched evidence checksum must be rejected");

    match err {
        ArtifactContractError::ProofEvidenceChecksumMismatch {
            component: err_component,
            expected,
            actual,
        } => {
            let expected_actual = match component {
                "target" => manifest.target.checksum(),
                "abi" => manifest.abi.checksum(),
                "invalidation" => manifest.invalidation.checksum(),
                "proof_policy" => manifest.proof_policy.checksum(),
                "artifact_manifest" => manifest.checksum(),
                "symbol_manifest" => manifest.symbol_manifest_checksum(),
                other => panic!("unexpected component {other}"),
            };
            assert_eq!(err_component, component);
            assert_eq!(expected, wrong_checksum);
            assert_eq!(actual, expected_actual);
        }
        other => panic!("expected proof evidence checksum mismatch, got {other:?}"),
    }
}

#[test]
fn manifest_schema_is_named_versioned_and_validated() {
    let manifest = base_manifest();

    assert_eq!(manifest.schema, JIT_ARTIFACT_MANIFEST_SCHEMA);
    assert_eq!(
        manifest.schema_version,
        JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION
    );
    manifest
        .verify_schema()
        .expect("base schema should validate");

    let mut changed = manifest.clone();
    changed.schema = "trust-cg.artifact/v0".to_owned();
    changed.schema_version = 0;
    let err = changed
        .verify_schema()
        .expect_err("changed schema must be rejected");

    match err {
        ArtifactContractError::SchemaMismatch {
            expected_schema,
            expected_version,
            actual_schema,
            actual_version,
        } => {
            assert_eq!(expected_schema, JIT_ARTIFACT_MANIFEST_SCHEMA);
            assert_eq!(expected_version, JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION);
            assert_eq!(actual_schema, "trust-cg.artifact/v0");
            assert_eq!(actual_version, 0);
        }
        other => panic!("expected schema mismatch, got {other:?}"),
    }
}

#[test]
fn manifest_canonical_bytes_and_checksum_are_order_stable() {
    let mut left = base_manifest();
    left.symbols = vec![
        ArtifactSymbol {
            name: "helper".to_owned(),
            visibility: SymbolVisibility::Internal,
            signature: i64_to_i64_signature(),
            offset_bytes: Some(64),
            checksum: None,
        },
        ArtifactSymbol {
            name: "entry".to_owned(),
            visibility: SymbolVisibility::Exported,
            signature: i64_to_i64_signature(),
            offset_bytes: Some(0),
            checksum: None,
        },
    ];
    left.sections = vec![
        ArtifactSection {
            name: ".rodata".to_owned(),
            kind: ArtifactSectionKind::Rodata,
            size_bytes: 8,
            alignment_bytes: 8,
            checksum: None,
        },
        ArtifactSection {
            name: ".text".to_owned(),
            kind: ArtifactSectionKind::Text,
            size_bytes: 96,
            alignment_bytes: 16,
            checksum: None,
        },
    ];
    left.metadata.insert("consumer".to_owned(), "ay".to_owned());
    left.metadata.insert("profile".to_owned(), "o1".to_owned());

    let mut right = base_manifest();
    right.symbols = left.symbols.iter().cloned().rev().collect();
    right.sections = left.sections.iter().cloned().rev().collect();
    right.metadata.insert("profile".to_owned(), "o1".to_owned());
    right
        .metadata
        .insert("consumer".to_owned(), "ay".to_owned());

    assert_eq!(left.canonical_bytes(), right.canonical_bytes());
    assert_eq!(left.checksum(), right.checksum());
    assert_eq!(
        left.checksum().to_string().len(),
        "trust-cg-stable128:".len() + 32
    );
}

#[test]
fn manifest_checksum_changes_when_signature_changes() {
    let mut left = base_manifest();
    left.symbols.push(ArtifactSymbol {
        name: "entry".to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: i64_to_i64_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });

    let mut right = left.clone();
    right.symbols[0].signature = i32_to_i64_signature();

    assert_ne!(left.canonical_bytes(), right.canonical_bytes());
    assert_ne!(left.checksum(), right.checksum());
}

#[test]
fn checksum_mismatch_is_typed_by_component() {
    let manifest = base_manifest();
    let expected = manifest.checksum();

    let mut changed = manifest.clone();
    changed.artifact_id = "artifact-2".to_owned();

    let err = changed
        .verify_checksum(expected)
        .expect_err("changed manifest must fail checksum validation");

    match err {
        ArtifactContractError::ChecksumMismatch {
            component,
            expected: err_expected,
            actual,
        } => {
            assert_eq!(component, "artifact_manifest");
            assert_eq!(err_expected, expected);
            assert_eq!(actual, changed.checksum());
        }
        other => panic!("expected checksum mismatch, got {other:?}"),
    }
}

#[test]
fn abi_and_layout_checksum_mismatches_are_typed_by_component() {
    let manifest = base_manifest();
    let expected_abi = manifest.abi.checksum();
    let expected_layout = manifest.layout.checksum();

    let mut changed_abi = manifest.clone();
    changed_abi.abi.calling_convention = "wrong_cc".to_owned();

    let err = changed_abi
        .verify_abi_checksum(expected_abi)
        .expect_err("changed ABI must fail checksum validation");
    match err {
        ArtifactContractError::ChecksumMismatch {
            component,
            expected,
            actual,
        } => {
            assert_eq!(component, "abi");
            assert_eq!(expected, expected_abi);
            assert_eq!(actual, changed_abi.abi.checksum());
        }
        other => panic!("expected ABI checksum mismatch, got {other:?}"),
    }

    let mut changed_layout = manifest.clone();
    changed_layout.layout.pointer_alignment_bytes = 16;

    let err = changed_layout
        .verify_layout_checksum(expected_layout)
        .expect_err("changed layout must fail checksum validation");
    match err {
        ArtifactContractError::ChecksumMismatch {
            component,
            expected,
            actual,
        } => {
            assert_eq!(component, "layout");
            assert_eq!(expected, expected_layout);
            assert_eq!(actual, changed_layout.layout.checksum());
        }
        other => panic!("expected layout checksum mismatch, got {other:?}"),
    }
}

#[test]
fn stale_invalidation_checksum_mismatch_is_typed_by_component() {
    let manifest = base_manifest();
    let expected_invalidation = manifest.invalidation.checksum();

    let mut changed = manifest.clone();
    changed.invalidation.generation += 1;

    let err = changed
        .verify_invalidation_checksum(expected_invalidation)
        .expect_err("changed invalidation key must fail checksum validation");
    match err {
        ArtifactContractError::ChecksumMismatch {
            component,
            expected,
            actual,
        } => {
            assert_eq!(component, "invalidation");
            assert_eq!(expected, expected_invalidation);
            assert_eq!(actual, changed.invalidation.checksum());
        }
        other => panic!("expected invalidation checksum mismatch, got {other:?}"),
    }
}

#[test]
fn symbol_signature_mismatch_is_typed() {
    let manifest = manifest_with_entry();
    let expected = i32_to_i64_signature();
    let err = manifest
        .verify_symbol_signature("entry", &expected)
        .expect_err("typed wrapper signature must be rejected");

    match err {
        ArtifactContractError::SignatureMismatch {
            symbol,
            expected: err_expected,
            actual,
        } => {
            assert_eq!(symbol, "entry");
            assert_eq!(err_expected, expected);
            assert_eq!(actual, Some(i64_to_i64_signature()));
        }
        other => panic!("expected signature mismatch, got {other:?}"),
    }
}

#[test]
fn typed_symbol_lookup_validates_schema_descriptors_and_signature_before_handle() {
    let manifest = manifest_with_entry();
    let contract = entry_lookup_contract_with_evidence(&manifest);
    let ptr = identity_i64 as *const () as *const u8;

    let typed = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(&contract, ptr)
        .expect("matching manifest contract should expose typed symbol");
    assert_eq!(typed.symbol(), "entry");
    assert_eq!(typed.signature(), &i64_to_i64_signature());
    assert_eq!(typed.artifact_checksum(), manifest.checksum());
    let callable = unsafe { typed.into_fn() };
    assert_eq!(callable(42), 42);

    let mut wrong_abi = contract.clone();
    wrong_abi.abi_checksum = ArtifactChecksum::new(1);
    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(&wrong_abi, ptr)
        .expect_err("ABI checksum mismatch must reject handle construction");
    match err {
        ArtifactContractError::ChecksumMismatch { component, .. } => {
            assert_eq!(component, "abi");
        }
        other => panic!("expected ABI checksum mismatch, got {other:?}"),
    }

    let mut wrong_layout = contract.clone();
    wrong_layout.layout_checksum = ArtifactChecksum::new(2);
    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(&wrong_layout, ptr)
        .expect_err("layout checksum mismatch must reject handle construction");
    match err {
        ArtifactContractError::ChecksumMismatch { component, .. } => {
            assert_eq!(component, "layout");
        }
        other => panic!("expected layout checksum mismatch, got {other:?}"),
    }

    let mut wrong_signature = contract.clone();
    wrong_signature.signature = i32_to_i64_signature();
    let err = manifest
        .typed_symbol::<extern "C" fn(i32) -> i64>(&wrong_signature, ptr)
        .expect_err("signature mismatch must reject handle construction");
    match err {
        ArtifactContractError::SignatureMismatch { symbol, .. } => {
            assert_eq!(symbol, "entry");
        }
        other => panic!("expected signature mismatch, got {other:?}"),
    }

    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(&contract, std::ptr::null())
        .expect_err("null pointer must not become a typed symbol");
    match err {
        ArtifactContractError::NullSymbolPointer { symbol } => {
            assert_eq!(symbol, "entry");
        }
        other => panic!("expected null symbol pointer, got {other:?}"),
    }
}

#[test]
fn successor_kernel_contract_binds_manifest_symbol_and_finite_domain() {
    let mut manifest = manifest_with_entry();
    manifest.metadata.insert(
        "ty.successor_kernel.evidence".to_owned(),
        "finite-domain-v1".to_owned(),
    );
    let transition_checksum = ArtifactChecksum::for_bytes(b"ty:next-state-relation:v1");

    let contract = KernelArtifactContract::successor_kernel(
        "ty",
        "entry",
        i64_to_i64_signature(),
        &manifest,
        KernelStateDomain::Finite {
            variable_count: 3,
            max_state_count: Some(1024),
        },
        transition_checksum,
    )
    .with_required_manifest_metadata("ty.successor_kernel.evidence");

    assert_eq!(contract.schema, KERNEL_ARTIFACT_CONTRACT_SCHEMA);
    assert_eq!(
        contract.schema_version,
        KERNEL_ARTIFACT_CONTRACT_SCHEMA_VERSION
    );
    assert_eq!(contract.kind, KernelArtifactKind::SuccessorKernel);
    assert_eq!(contract.kind.as_str(), "successor_kernel");
    assert_eq!(contract.semantic_checksum, transition_checksum);
    assert_ne!(contract.checksum(), ArtifactChecksum::new(0));
    contract
        .validate_manifest(&manifest)
        .expect("matching successor kernel contract should validate");

    let mut missing_metadata_manifest = manifest.clone();
    missing_metadata_manifest
        .metadata
        .remove("ty.successor_kernel.evidence");
    let err = contract
        .validate_manifest(&missing_metadata_manifest)
        .expect_err("required metadata must be present before adoption");
    match err {
        ArtifactContractError::MissingManifestMetadata { key } => {
            assert_eq!(key, "ty.successor_kernel.evidence");
        }
        other => panic!("expected missing manifest metadata, got {other:?}"),
    }
}

#[test]
fn predicate_kernel_contract_rejects_signature_drift() {
    let manifest = manifest_with_entry();
    let contract = KernelArtifactContract::predicate_kernel(
        "ty",
        "entry",
        i32_to_i64_signature(),
        &manifest,
        KernelStateDomain::BoundedByInvariant {
            invariant: "TypeOK".to_owned(),
        },
        ArtifactChecksum::for_bytes(b"ty:predicate:TypeOK:v1"),
    );

    let err = contract
        .validate_manifest(&manifest)
        .expect_err("predicate contract must reject symbol signature drift");
    match err {
        ArtifactContractError::SignatureMismatch { symbol, .. } => {
            assert_eq!(symbol, "entry");
        }
        other => panic!("expected signature mismatch, got {other:?}"),
    }
}

#[test]
fn required_proof_policy_rejects_typed_symbol_without_evidence() {
    let manifest = manifest_with_entry();
    let contract = entry_lookup_contract(&manifest);
    let ptr = identity_i64 as *const () as *const u8;

    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(&contract, ptr)
        .expect_err("required proof policy must reject missing evidence");

    match err {
        ArtifactContractError::MissingProofEvidence { rejection_code } => {
            assert_eq!(rejection_code, ProofEvidenceRejectionCode::MissingEvidence);
            assert_eq!(rejection_code.as_str(), "proof_missing_evidence");
        }
        other => panic!("expected missing proof evidence, got {other:?}"),
    }
}

#[test]
fn required_proof_policy_rejects_contract_without_manifest_checksum() {
    let manifest = manifest_with_entry();
    let contract = SymbolLookupContract::new(
        "entry",
        i64_to_i64_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_proof_evidence(verified_evidence(&manifest));
    let ptr = identity_i64 as *const () as *const u8;

    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(&contract, ptr)
        .expect_err("proof-required typed lookup must bind the manifest checksum");

    match err {
        ArtifactContractError::MissingProofEvidence { rejection_code } => {
            assert_eq!(
                rejection_code,
                ProofEvidenceRejectionCode::MissingRequiredFields
            );
        }
        other => panic!("expected missing manifest checksum rejection, got {other:?}"),
    }
}

#[test]
fn required_proof_policy_rejects_evidence_without_artifact_identity() {
    let manifest = manifest_with_entry();
    let legacy_evidence = ProofEvidenceSummary::verified(
        "trust-cg-verify",
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
        manifest.invalidation.checksum(),
        manifest.proof_policy.checksum(),
    );
    let ptr = identity_i64 as *const () as *const u8;

    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &entry_lookup_contract(&manifest).with_proof_evidence(legacy_evidence),
            ptr,
        )
        .expect_err("legacy evidence without artifact identity must be rejected");

    match err {
        ArtifactContractError::ProofEvidenceRejected {
            rejection_code,
            detail,
            ..
        } => {
            assert_eq!(
                rejection_code,
                Some(ProofEvidenceRejectionCode::MissingRequiredFields)
            );
            assert!(detail.contains("artifact identity"));
        }
        other => panic!("expected missing artifact identity rejection, got {other:?}"),
    }
}

#[test]
fn required_proof_policy_rejects_mismatched_or_failed_evidence() {
    let manifest = manifest_with_entry();
    let ptr = identity_i64 as *const () as *const u8;

    let mut mismatched = verified_evidence(&manifest);
    mismatched.layout_checksum = ArtifactChecksum::new(99);
    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &entry_lookup_contract(&manifest).with_proof_evidence(mismatched),
            ptr,
        )
        .expect_err("evidence for a different layout must be rejected");
    match err {
        ArtifactContractError::ProofEvidenceChecksumMismatch {
            component,
            expected,
            actual,
        } => {
            assert_eq!(component, "layout");
            assert_eq!(expected, ArtifactChecksum::new(99));
            assert_eq!(actual, manifest.layout.checksum());
        }
        other => panic!("expected proof evidence checksum mismatch, got {other:?}"),
    }

    let rejected = ProofEvidenceSummary::rejected_for_artifact(
        "trust-cg-verify",
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
        &manifest,
        TEST_NATIVE_PAYLOAD_SHA256,
        TEST_PROOF_REPORT_SHA256,
    );
    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &entry_lookup_contract(&manifest).with_proof_evidence(rejected),
            ptr,
        )
        .expect_err("failed proof evidence must be rejected");
    match err {
        ArtifactContractError::ProofEvidenceRejected {
            verdict,
            rejection_code,
            ..
        } => {
            assert_eq!(verdict, ProofEvidenceVerdict::VerifierFailure);
            assert_eq!(
                rejection_code,
                Some(ProofEvidenceRejectionCode::VerifierFailure)
            );
        }
        other => panic!("expected proof evidence rejection, got {other:?}"),
    }
}

#[test]
fn required_proof_policy_rejects_evidence_identity_mismatches_by_component() {
    let manifest = manifest_with_entry();

    assert_evidence_checksum_mismatch(
        &manifest,
        "artifact_manifest",
        ArtifactChecksum::new(95),
        |evidence| {
            evidence.manifest_checksum = ArtifactChecksum::new(95);
        },
    );
    assert_evidence_checksum_mismatch(
        &manifest,
        "symbol_manifest",
        ArtifactChecksum::new(96),
        |evidence| {
            evidence.symbol_manifest_checksum = ArtifactChecksum::new(96);
        },
    );

    let mut artifact_id_mismatch = verified_evidence(&manifest);
    artifact_id_mismatch.artifact_id = "other-artifact".to_owned();
    let err = manifest
        .validate_symbol_lookup(
            &entry_lookup_contract(&manifest).with_proof_evidence(artifact_id_mismatch),
        )
        .expect_err("artifact id mismatch must reject evidence");
    match err {
        ArtifactContractError::ProofEvidenceRejected {
            rejection_code,
            detail,
            ..
        } => {
            assert_eq!(
                rejection_code,
                Some(ProofEvidenceRejectionCode::StaleEvidence)
            );
            assert!(detail.contains("artifact id mismatch"));
        }
        other => panic!("expected artifact id mismatch rejection, got {other:?}"),
    }

    let mut native_mismatch = verified_evidence(&manifest);
    native_mismatch.native_payload_sha256 = "sha256:other-native".to_owned();
    let err = manifest
        .validate_symbol_lookup(
            &entry_lookup_contract(&manifest).with_proof_evidence(native_mismatch),
        )
        .expect_err("native payload digest mismatch must reject evidence");
    match err {
        ArtifactContractError::ProofEvidenceRejected {
            rejection_code,
            detail,
            ..
        } => {
            assert_eq!(
                rejection_code,
                Some(ProofEvidenceRejectionCode::StaleEvidence)
            );
            assert!(detail.contains("native payload digest mismatch"));
        }
        other => panic!("expected native payload mismatch rejection, got {other:?}"),
    }
}

#[test]
fn required_proof_policy_rejects_missing_native_payload_digest() {
    let mut manifest = manifest_with_entry();
    manifest.metadata.remove("native_payload_sha256");
    let ptr = identity_i64 as *const () as *const u8;

    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &entry_lookup_contract(&manifest).with_proof_evidence(verified_evidence(&manifest)),
            ptr,
        )
        .expect_err("manifest without native payload digest must reject proof evidence");

    match err {
        ArtifactContractError::MissingManifestMetadata { key } => {
            assert_eq!(key, "native_payload_sha256");
        }
        other => panic!("expected missing native payload metadata, got {other:?}"),
    }
}

#[test]
fn required_proof_policy_rejects_missing_proof_report_digest() {
    let manifest = manifest_with_entry();
    let mut evidence = verified_evidence(&manifest);
    evidence.proof_report_sha256.clear();
    let ptr = identity_i64 as *const () as *const u8;

    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &entry_lookup_contract(&manifest).with_proof_evidence(evidence),
            ptr,
        )
        .expect_err("proof evidence without proof report digest must reject");

    match err {
        ArtifactContractError::ProofEvidenceRejected {
            rejection_code,
            detail,
            ..
        } => {
            assert_eq!(
                rejection_code,
                Some(ProofEvidenceRejectionCode::MissingRequiredFields)
            );
            assert!(detail.contains("artifact identity"));
        }
        other => panic!("expected missing proof report digest rejection, got {other:?}"),
    }
}

#[test]
fn symbol_manifest_checksum_is_order_stable_and_tracks_symbol_changes() {
    let manifest = manifest_with_entry();
    let mut reordered = manifest.clone();
    reordered.symbols.push(ArtifactSymbol {
        name: "alpha".to_owned(),
        visibility: SymbolVisibility::Internal,
        signature: i64_to_i64_signature(),
        offset_bytes: Some(16),
        checksum: None,
    });
    let mut opposite = reordered.clone();
    opposite.symbols.reverse();

    assert_eq!(
        reordered.symbol_manifest_checksum(),
        opposite.symbol_manifest_checksum()
    );

    let mut changed = reordered.clone();
    changed.symbols[0].signature = i32_to_i64_signature();
    assert_ne!(
        reordered.symbol_manifest_checksum(),
        changed.symbol_manifest_checksum()
    );
    assert_ne!(
        manifest.symbol_manifest_checksum(),
        reordered.symbol_manifest_checksum()
    );
}

#[test]
fn required_proof_policy_rejects_unaccepted_verified_evidence_verifier() {
    let manifest = manifest_with_entry();
    let ptr = identity_i64 as *const () as *const u8;

    let mut evidence = verified_evidence(&manifest);
    evidence.verifier = "unaccepted-solver".to_owned();

    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &entry_lookup_contract(&manifest).with_proof_evidence(evidence),
            ptr,
        )
        .expect_err("verified evidence from an unaccepted verifier must be rejected");

    match err {
        ArtifactContractError::ProofEvidenceRejected {
            verifier,
            verdict,
            rejection_code,
            detail,
        } => {
            assert_eq!(verifier, "unaccepted-solver");
            assert_eq!(verdict, ProofEvidenceVerdict::UnknownSolverError);
            assert_eq!(
                rejection_code,
                Some(ProofEvidenceRejectionCode::UnknownSolverError)
            );
            assert!(detail.contains("not accepted by policy"));
        }
        other => panic!("expected proof evidence verifier rejection, got {other:?}"),
    }
}

#[test]
fn required_proof_policy_rejects_evidence_schema_mismatch() {
    let manifest = manifest_with_entry();
    let ptr = identity_i64 as *const () as *const u8;

    let mut evidence = verified_evidence(&manifest);
    evidence.schema = "trust-cg.proof_evidence_summary/v0".to_owned();
    evidence.schema_version = 0;

    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &entry_lookup_contract(&manifest).with_proof_evidence(evidence),
            ptr,
        )
        .expect_err("evidence schema mismatch must be rejected");

    match err {
        ArtifactContractError::ProofEvidenceRejected { detail, .. } => {
            assert!(detail.contains("schema mismatch"));
            assert!(detail.contains("trust-cg.proof_evidence_summary/v0"));
        }
        other => panic!("expected proof evidence schema rejection, got {other:?}"),
    }
}

#[test]
fn required_proof_policy_rejects_evidence_checksum_mismatches_by_component() {
    let manifest = manifest_with_entry();

    assert_evidence_checksum_mismatch(&manifest, "target", ArtifactChecksum::new(91), |evidence| {
        evidence.target_checksum = ArtifactChecksum::new(91);
    });
    assert_evidence_checksum_mismatch(&manifest, "abi", ArtifactChecksum::new(92), |evidence| {
        evidence.abi_checksum = ArtifactChecksum::new(92);
    });
    assert_evidence_checksum_mismatch(
        &manifest,
        "invalidation",
        ArtifactChecksum::new(93),
        |evidence| {
            evidence.invalidation_checksum = ArtifactChecksum::new(93);
        },
    );
    assert_evidence_checksum_mismatch(
        &manifest,
        "proof_policy",
        ArtifactChecksum::new(94),
        |evidence| {
            evidence.proof_policy_checksum = ArtifactChecksum::new(94);
        },
    );
}

#[test]
fn required_proof_policy_exposes_typed_symbol_with_verified_matching_evidence() {
    let manifest = manifest_with_entry();
    let contract = entry_lookup_contract_with_evidence(&manifest);
    let ptr = identity_i64 as *const () as *const u8;

    let typed = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(&contract, ptr)
        .expect("verified matching evidence must expose typed symbol");

    assert_eq!(typed.symbol(), "entry");
    assert_eq!(typed.artifact_checksum(), manifest.checksum());
}

#[test]
fn disabled_policy_exposes_symbol_without_evidence_unless_caller_requires_it() {
    let manifest = disabled_manifest_with_entry();
    let contract = entry_lookup_contract(&manifest);
    let ptr = identity_i64 as *const () as *const u8;

    manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(&contract, ptr)
        .expect("disabled proof policy should preserve no-evidence typed lookup");

    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &contract.clone().with_required_proof_evidence(),
            ptr,
        )
        .expect_err("explicit caller requirement must reject missing evidence");
    match err {
        ArtifactContractError::MissingProofEvidence { rejection_code } => {
            assert_eq!(rejection_code.as_str(), "proof_missing_evidence");
        }
        other => panic!("expected missing proof evidence, got {other:?}"),
    }

    manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &contract
                .with_required_proof_evidence()
                .with_proof_evidence(verified_evidence(&manifest)),
            ptr,
        )
        .expect("explicit caller requirement should accept matching evidence");
}

#[test]
fn audit_only_policy_exposes_symbol_without_evidence_unless_caller_requires_it() {
    let manifest = audit_only_manifest_with_entry();
    let contract = entry_lookup_contract(&manifest);
    let ptr = identity_i64 as *const () as *const u8;

    manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(&contract, ptr)
        .expect("audit-only proof policy should preserve no-evidence typed lookup");

    let err = manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(
            &contract.clone().with_required_proof_evidence(),
            ptr,
        )
        .expect_err("explicit caller requirement must reject missing evidence");
    match err {
        ArtifactContractError::MissingProofEvidence { rejection_code } => {
            assert_eq!(rejection_code, ProofEvidenceRejectionCode::MissingEvidence);
        }
        other => panic!("expected missing proof evidence, got {other:?}"),
    }
}

#[test]
fn disabled_mode_remains_non_enforcing_even_with_public_requirement_flags() {
    let manifest = disabled_manifest_with_public_requirement_flags();
    let contract = entry_lookup_contract(&manifest);
    let ptr = identity_i64 as *const () as *const u8;

    manifest
        .typed_symbol::<extern "C" fn(i64) -> i64>(&contract, ptr)
        .expect("disabled proof mode should be authoritative over public requirement flags");
}
