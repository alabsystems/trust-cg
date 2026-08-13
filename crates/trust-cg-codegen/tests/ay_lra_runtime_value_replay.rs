// trust-cg-codegen/tests/ay_lra_runtime_value_replay.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::ay_lra_proof_manifest::{
    AYLraAarch64LoweringDecision, AYLraBasisEpochEvidence, AYLraEvidenceAvailability,
    AYLraKernelProofConsumptionManifest, AYLraManifestDisposition, AYLraManifestRejectionReason,
    AYLraProductGateEvidence, AYLraProofConsumptionEvidence, AYLraProofFact, AYLraReplayComparison,
    AYLraRequirementAvailability, ay_lra_basis_update_proof_manifest,
    ay_lra_proof_fact_metadata_key, select_ay_lra_aarch64_lowering,
};
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, AliasPolicy, ArtifactSection, ArtifactSectionKind,
    ArtifactSymbol, DeterministicArtifactManifest, Endianness, FieldLayout, InvalidationKey,
    JitArtifactKind, LayoutManifest, Mutability, PointerBounds, PointerLayout,
    ProofEvidenceSummary, ProofMode, ProofPolicy, RecordLayout, SliceLayout, SymbolLayout,
    SymbolSignature, SymbolVisibility, TargetDescriptor, TargetOperatingSystem,
};

const BATCH_STATUS_SYMBOL: &str = "ay_lra_basis_row_batch";
const BATCH_STATUS_RECORD: &str = "AYLraBasisRowBatchStatusAbi";
const RUNTIME_VALUE_FACTS: [AYLraProofFact; 4] = [
    AYLraProofFact::OutputCapacityBounds,
    AYLraProofFact::CoefficientOverflow,
    AYLraProofFact::BasisEpochFreshness,
    AYLraProofFact::BatchPrefixCommitRollback,
];
const CANONICAL_REPLAY_ROOT_SHA256: &str =
    "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const CANONICAL_BEHAVIOR_SHA256: &str =
    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const CANONICAL_INSTALL_GATE_SHA256: &str =
    "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
const CANONICAL_CONSUMER_ADMISSION_SHA256: &str =
    "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
const CANONICAL_REPLAY_IDENTITY_SHA256: &str =
    "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
const CANONICAL_TELEMETRY_SHA256: &str =
    "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
const CANONICAL_NATIVE_PAYLOAD_SHA256: &str = "sha256:ay-lra-runtime-native-payload";
const CANONICAL_PROOF_REPORT_SHA256: &str = "sha256:ay-lra-runtime-proof-report";
const BASIS_ROW_BATCH_TRUST_CG_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-cg:ay-lra-basis-row-batch:v1";
const BASIS_ROW_BATCH_TRUST_IR_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-ir:ay-lra-basis-row-batch:v1";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RuntimeReplayValues {
    output_capacity: u64,
    coefficient_lhs: i64,
    coefficient_rhs: i64,
    current_basis_epoch: u64,
    expected_basis_epoch: u64,
    committed_prefix_rows: u64,
}

impl RuntimeReplayValues {
    fn for_generation(generation: u64) -> Self {
        Self {
            output_capacity: 32,
            coefficient_lhs: 7,
            coefficient_rhs: -3,
            current_basis_epoch: generation,
            expected_basis_epoch: generation,
            committed_prefix_rows: 2,
        }
    }

    fn replay_digest(self) -> String {
        format!(
            "sha256:ay-lra-runtime-values:v1:capacity={}:coefficients={},{}:basis_epoch={},{}:committed_prefix_rows={}",
            self.output_capacity,
            self.coefficient_lhs,
            self.coefficient_rhs,
            self.current_basis_epoch,
            self.expected_basis_epoch,
            self.committed_prefix_rows
        )
    }

    fn proof_payload(self, fact: AYLraProofFact) -> String {
        match fact {
            AYLraProofFact::OutputCapacityBounds => {
                format!("output_capacity={}", self.output_capacity)
            }
            AYLraProofFact::CoefficientOverflow => format!(
                "coefficient_lhs={},coefficient_rhs={}",
                self.coefficient_lhs, self.coefficient_rhs
            ),
            AYLraProofFact::BasisEpochFreshness => format!(
                "current_basis_epoch={},expected_basis_epoch={}",
                self.current_basis_epoch, self.expected_basis_epoch
            ),
            AYLraProofFact::BatchPrefixCommitRollback => {
                format!("committed_prefix_rows={}", self.committed_prefix_rows)
            }
            other => panic!("runtime replay test must not source non-runtime fact {other:?}"),
        }
    }
}

fn runtime_fact_csv() -> String {
    RUNTIME_VALUE_FACTS
        .iter()
        .map(|fact| fact.as_str())
        .collect::<Vec<_>>()
        .join(",")
}

fn runtime_fact_key(fact: AYLraProofFact) -> String {
    format!("ay_lra.runtime_value.{}", fact.as_str())
}

fn i64_value() -> AbiValue {
    AbiValue::new(AbiValueKind::I64)
}

fn ptr_value() -> AbiValue {
    AbiValue::new(AbiValueKind::Ptr)
}

fn ay_lra_batch_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            ptr_value(),
            ptr_value(),
            i64_value(),
            ptr_value(),
            ptr_value(),
            i64_value(),
            ptr_value(),
            ptr_value(),
        ],
        vec![],
    )
}

fn ay_lra_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target(Target::Aarch64, TargetOperatingSystem::Macos)
        .with_cpu("apple-m")
        .with_features(["fp", "simd"])
}

fn ay_lra_abi() -> AbiDescriptor {
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ay-lra-aapcs64-lp64".to_owned();
    abi
}

fn ay_lra_batch_status_record_layout() -> RecordLayout {
    RecordLayout {
        name: BATCH_STATUS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: 24,
        alignment_bytes: 8,
        fields: vec![
            FieldLayout {
                name: "status".to_owned(),
                offset_bytes: 0,
                size_bytes: 1,
                alignment_bytes: 1,
            },
            FieldLayout {
                name: "deopt".to_owned(),
                offset_bytes: 1,
                size_bytes: 1,
                alignment_bytes: 1,
            },
            FieldLayout {
                name: "reserved".to_owned(),
                offset_bytes: 2,
                size_bytes: 6,
                alignment_bytes: 1,
            },
            FieldLayout {
                name: "rows_completed".to_owned(),
                offset_bytes: 8,
                size_bytes: 8,
                alignment_bytes: 8,
            },
            FieldLayout {
                name: "first_failed_row".to_owned(),
                offset_bytes: 16,
                size_bytes: 8,
                alignment_bytes: 8,
            },
        ],
    }
}

fn batch_row_i64_slice(name: &str, mutability: Mutability) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes: 8,
        element_alignment_bytes: 8,
        stride_bytes: 8,
        length: None,
        bounds: PointerBounds::Symbol("affected_row_count".to_owned()),
        mutability,
        alias_policy: match mutability {
            Mutability::Immutable => AliasPolicy::SharedReadOnly,
            Mutability::Mutable => AliasPolicy::Exclusive,
        },
    }
}

fn fixed_i64_slice(name: &str, length: u64, mutability: Mutability) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes: 8,
        element_alignment_bytes: 8,
        stride_bytes: 8,
        length: Some(length),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: length * 8,
        },
        mutability,
        alias_policy: match mutability {
            Mutability::Immutable => AliasPolicy::SharedReadOnly,
            Mutability::Mutable => AliasPolicy::Exclusive,
        },
    }
}

fn ay_lra_batch_layout() -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some("ay::lra::BasisRowBatchKernel::lp64:v1".to_owned());
    layout.records.push(ay_lra_batch_status_record_layout());
    layout
        .slices
        .push(batch_row_i64_slice("tableau_row_ptrs", Mutability::Mutable));
    layout
        .slices
        .push(batch_row_i64_slice("row_scales", Mutability::Immutable));
    layout
        .slices
        .push(fixed_i64_slice("basis_epochs", 2, Mutability::Immutable));
    layout.slices.push(batch_row_i64_slice(
        "row_output_offsets",
        Mutability::Immutable,
    ));
    layout.slices.push(batch_row_i64_slice(
        "row_output_lengths",
        Mutability::Mutable,
    ));
    layout.pointers.push(PointerLayout {
        name: "batch_status_out".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: 24,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.symbols.push(SymbolLayout {
        name: BATCH_STATUS_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: 256,
        alignment_bytes: 16,
    });
    layout
        .metadata
        .insert("kernel".to_owned(), "ay_lra_basis_row_batch".to_owned());
    layout.metadata.insert(
        "tableau_row_layout".to_owned(),
        "ptrs_to_i64_rows_len5_stride40".to_owned(),
    );
    layout.metadata.insert(
        "basis_row_layout".to_owned(),
        "basis_epoch_pair_current_expected".to_owned(),
    );
    layout.metadata.insert(
        "row_region_hash".to_owned(),
        "pre_post_tableau_digest".to_owned(),
    );
    layout.metadata.insert(
        "scratch_rollback".to_owned(),
        "row_lengths_as_commit_log_no_failed_row_rollback".to_owned(),
    );
    layout.metadata.insert(
        "rollback_failure_disposition".to_owned(),
        "non_promoting_deopt_failed_row_left_uncommitted".to_owned(),
    );
    layout.metadata.insert(
        "alias_policy".to_owned(),
        "exclusive_tableau_rows_shared_inputs".to_owned(),
    );
    layout
        .metadata
        .insert("output_capacity".to_owned(), "runtime_i64".to_owned());
    layout
        .metadata
        .insert("commit_policy".to_owned(), "partial_row_deopt".to_owned());
    layout
        .metadata
        .insert("status_value".to_owned(), "rows_completed".to_owned());
    layout
        .metadata
        .insert("status_detail".to_owned(), "first_failed_row".to_owned());
    layout.metadata.insert(
        "status_abi".to_owned(),
        "ay_lra_basis_row_batch_status_abi_v1".to_owned(),
    );
    layout
}

fn ay_lra_replay_policy() -> ProofPolicy {
    let mut proof_policy = ProofPolicy::require_certificates(["trust-cg-verify", "ay-replay"]);
    proof_policy.mode = ProofMode::RequireReplay;
    proof_policy.max_replay_age_generations = Some(0);
    proof_policy
}

fn ay_lra_batch_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    let mut invalidation = InvalidationKey::new(
        "ay:lra:basis-row-batch:kernel-v1",
        "trust-cg:phase5:lra:o2",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        45,
    );
    invalidation
        .extra
        .insert("tableau_row_ptrs".to_owned(), "runtime".to_owned());
    invalidation
        .extra
        .insert("row_scales".to_owned(), "runtime".to_owned());
    invalidation
        .extra
        .insert("basis_epoch".to_owned(), "runtime".to_owned());
    invalidation.extra.insert(
        "basis_row_layout".to_owned(),
        "basis_epoch_pair_current_expected".to_owned(),
    );
    invalidation.extra.insert(
        "tableau_row_layout".to_owned(),
        "ptrs_to_i64_rows_len5_stride40".to_owned(),
    );
    invalidation.extra.insert(
        "row_region_hash".to_owned(),
        "runtime_tableau_digest".to_owned(),
    );
    invalidation
        .extra
        .insert("commit_policy".to_owned(), "partial_row_deopt".to_owned());
    invalidation.extra.insert(
        "scratch_rollback".to_owned(),
        "row_lengths_as_commit_log_no_failed_row_rollback".to_owned(),
    );
    invalidation.extra.insert(
        "rollback_failure_disposition".to_owned(),
        "non_promoting_deopt_failed_row_left_uncommitted".to_owned(),
    );
    invalidation.extra.insert(
        "row_output_lengths".to_owned(),
        "mutable_runtime".to_owned(),
    );
    invalidation
        .extra
        .insert("row_output_offsets".to_owned(), "runtime".to_owned());
    invalidation
        .extra
        .insert("output_capacity".to_owned(), "runtime_i64".to_owned());
    invalidation.extra.insert(
        "status_abi".to_owned(),
        "ay_lra_basis_row_batch_status_abi_v1".to_owned(),
    );
    invalidation
        .extra
        .insert("status_detail".to_owned(), "first_failed_row".to_owned());
    invalidation
        .extra
        .insert("status_value".to_owned(), "rows_completed".to_owned());
    invalidation
}

fn attach_ay_lra_proof_consumption_metadata(
    manifest: &mut DeterministicArtifactManifest,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) {
    manifest.metadata.insert(
        "proof_consumption_manifest_schema".to_owned(),
        proof_manifest.schema.to_owned(),
    );
    manifest.metadata.insert(
        "proof_consumption_manifest_issue".to_owned(),
        format!("#{}", proof_manifest.issue),
    );
    manifest.metadata.insert(
        "product_gate_surface".to_owned(),
        proof_manifest.product_gate.surface.to_owned(),
    );
    manifest.metadata.insert(
        "product_gate_allowlist_family".to_owned(),
        proof_manifest.product_gate.allowlist_family.to_owned(),
    );
    manifest.metadata.insert(
        "trust_ir_source_identity".to_owned(),
        "trust_ir:ay:lra:basis-row-batch:v1".to_owned(),
    );
    manifest.metadata.insert(
        "source_policy".to_owned(),
        "approved_private_source".to_owned(),
    );
    manifest.metadata.insert(
        "approved_private_source_policy".to_owned(),
        "issue_663_runtime_value_replay_lock_v1".to_owned(),
    );
    manifest.metadata.insert(
        "trust_cg_source_lock".to_owned(),
        BASIS_ROW_BATCH_TRUST_CG_SOURCE_LOCK.to_owned(),
    );
    manifest.metadata.insert(
        "trust_ir_source_lock".to_owned(),
        BASIS_ROW_BATCH_TRUST_IR_SOURCE_LOCK.to_owned(),
    );
    manifest.metadata.insert(
        "target_abi_layout".to_owned(),
        "aarch64-macos-aapcs64-lp64".to_owned(),
    );
    manifest.metadata.insert(
        "status_signature_checksum".to_owned(),
        manifest.symbols[0].signature.checksum().to_string(),
    );
    manifest.metadata.insert(
        "proof_policy_checksum".to_owned(),
        manifest.proof_policy.checksum().to_string(),
    );
    manifest.metadata.insert(
        "invalidation_checksum".to_owned(),
        manifest.invalidation.checksum().to_string(),
    );
    manifest.metadata.insert(
        "required_proof_facts".to_owned(),
        proof_manifest.required_fact_csv(),
    );
    manifest.metadata.insert(
        "required_proof_lemmas".to_owned(),
        proof_manifest.required_lemma_csv(),
    );
    manifest.metadata.insert(
        "required_certificate_dependencies".to_owned(),
        proof_manifest.required_certificate_csv(),
    );
    manifest.metadata.insert(
        "future_proof_families".to_owned(),
        proof_manifest.future_family_csv(),
    );
    manifest.metadata.insert(
        "future_proof_status".to_owned(),
        "missing_future".to_owned(),
    );
    manifest.metadata.insert(
        "replay_compare".to_owned(),
        "generic_specialized_reference_manifest_identity".to_owned(),
    );
    manifest.metadata.insert(
        "product_gate_fields".to_owned(),
        proof_manifest.product_gate.required_parent_gates.join(","),
    );
    manifest.metadata.insert(
        "baseline_authoritative_until_product_gate".to_owned(),
        proof_manifest
            .product_gate
            .baseline_authoritative_until_product_gate
            .to_string(),
    );
    manifest.metadata.insert(
        "telemetry_counter_policy".to_owned(),
        proof_manifest
            .product_gate
            .telemetry_counter_policy
            .to_owned(),
    );
    manifest
        .metadata
        .insert("useful_native".to_owned(), "false".to_owned());
}

fn ay_lra_batch_manifest() -> DeterministicArtifactManifest {
    let target = ay_lra_target();
    let abi = ay_lra_abi();
    let layout = ay_lra_batch_layout();
    let proof_policy = ay_lra_replay_policy();
    let invalidation = ay_lra_batch_invalidation(&target, &abi, &layout, &proof_policy);
    let mut manifest = DeterministicArtifactManifest::new(
        "ay-lra-basis-row-batch-runtime-replay",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: BATCH_STATUS_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_lra_batch_status_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: 256,
        alignment_bytes: 16,
        checksum: None,
    });
    manifest
        .metadata
        .insert("consumer".to_owned(), "ay".to_owned());
    manifest
        .metadata
        .insert("kernel".to_owned(), "ay_lra_basis_row_batch".to_owned());
    manifest.metadata.insert(
        "tableau_row_layout".to_owned(),
        "ptrs_to_i64_rows_len5_stride40".to_owned(),
    );
    manifest.metadata.insert(
        "basis_row_layout".to_owned(),
        "basis_epoch_pair_current_expected".to_owned(),
    );
    manifest.metadata.insert(
        "row_region_hash".to_owned(),
        "pre_post_tableau_digest".to_owned(),
    );
    manifest.metadata.insert(
        "scratch_rollback".to_owned(),
        "row_lengths_as_commit_log_no_failed_row_rollback".to_owned(),
    );
    manifest.metadata.insert(
        "rollback_failure_disposition".to_owned(),
        "non_promoting_deopt_failed_row_left_uncommitted".to_owned(),
    );
    manifest.metadata.insert(
        "alias_policy".to_owned(),
        "exclusive_tableau_rows_shared_inputs".to_owned(),
    );
    manifest
        .metadata
        .insert("output_capacity".to_owned(), "runtime_i64".to_owned());
    manifest
        .metadata
        .insert("commit_policy".to_owned(), "partial_row_deopt".to_owned());
    manifest
        .metadata
        .insert("status_value".to_owned(), "rows_completed".to_owned());
    manifest
        .metadata
        .insert("status_detail".to_owned(), "first_failed_row".to_owned());
    manifest.metadata.insert(
        "native_payload_sha256".to_owned(),
        CANONICAL_NATIVE_PAYLOAD_SHA256.to_owned(),
    );
    attach_ay_lra_proof_consumption_metadata(&mut manifest, &ay_lra_basis_update_proof_manifest());
    manifest
}

fn ay_lra_verified_evidence(
    manifest: &DeterministicArtifactManifest,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::verified_for_artifact(
        "trust-cg-verify",
        manifest,
        CANONICAL_NATIVE_PAYLOAD_SHA256,
        CANONICAL_PROOF_REPORT_SHA256,
    );
    evidence.metadata.insert(
        "proof_consumption_manifest_schema".to_owned(),
        proof_manifest.schema.to_owned(),
    );
    evidence.metadata.insert(
        "proof_consumption_manifest_issue".to_owned(),
        format!("#{}", proof_manifest.issue),
    );
    evidence.metadata.insert(
        "kernel_family".to_owned(),
        proof_manifest.kernel_family.as_str().to_owned(),
    );
    evidence.metadata.insert(
        "required_proof_facts".to_owned(),
        proof_manifest.required_fact_csv(),
    );
    for requirement in &proof_manifest.required_facts {
        evidence.metadata.insert(
            ay_lra_proof_fact_metadata_key(requirement.fact),
            requirement.lemma_id.to_owned(),
        );
    }
    evidence.metadata.insert(
        "required_certificate_dependencies".to_owned(),
        proof_manifest.required_certificate_csv(),
    );
    evidence.metadata.insert(
        "future_proof_status".to_owned(),
        "missing_future".to_owned(),
    );
    evidence.metadata.insert(
        "product_gate_fields".to_owned(),
        proof_manifest.product_gate.required_parent_gates.join(","),
    );
    evidence.metadata.insert(
        "trust_ir_source_identity".to_owned(),
        "trust_ir:ay:lra:basis-row-batch:v1".to_owned(),
    );
    evidence.metadata.insert(
        "source_policy".to_owned(),
        "approved_private_source".to_owned(),
    );
    evidence.metadata.insert(
        "trust_cg_source_lock".to_owned(),
        BASIS_ROW_BATCH_TRUST_CG_SOURCE_LOCK.to_owned(),
    );
    evidence.metadata.insert(
        "trust_ir_source_lock".to_owned(),
        BASIS_ROW_BATCH_TRUST_IR_SOURCE_LOCK.to_owned(),
    );
    evidence
}

fn complete_ay_lra_replay_evidence(
    manifest: &DeterministicArtifactManifest,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
    values: RuntimeReplayValues,
) -> AYLraProofConsumptionEvidence {
    let mut facts = BTreeMap::new();
    for requirement in &proof_manifest.required_facts {
        facts.insert(requirement.fact, AYLraEvidenceAvailability::Available);
    }
    for requirement in &proof_manifest.future_facts {
        facts.insert(requirement.fact, AYLraEvidenceAvailability::Future);
    }

    let mut certificates = BTreeMap::new();
    for dependency in &proof_manifest.certificate_dependencies {
        certificates.insert(
            dependency.id.to_owned(),
            match dependency.availability {
                AYLraRequirementAvailability::RequiredForAdmission => {
                    AYLraEvidenceAvailability::Available
                }
                AYLraRequirementAvailability::MissingFuture => AYLraEvidenceAvailability::Future,
            },
        );
    }

    let runtime_digest = values.replay_digest();
    let mut proof_evidence = ay_lra_verified_evidence(manifest, proof_manifest);
    proof_evidence
        .metadata
        .insert("ay_lra.runtime_value_facts".to_owned(), runtime_fact_csv());
    proof_evidence.metadata.insert(
        "ay_lra.runtime_replay_digest".to_owned(),
        runtime_digest.clone(),
    );
    for fact in RUNTIME_VALUE_FACTS {
        proof_evidence
            .metadata
            .insert(runtime_fact_key(fact), values.proof_payload(fact));
    }

    AYLraProofConsumptionEvidence {
        proof_evidence: Some(proof_evidence),
        facts,
        certificates,
        basis_epoch: AYLraBasisEpochEvidence {
            current_epoch: values.current_basis_epoch,
            expected_epoch: values.expected_basis_epoch,
        },
        replay: AYLraReplayComparison {
            manifest_checksum: manifest.checksum(),
            replay_root_sha256: CANONICAL_REPLAY_ROOT_SHA256.to_owned(),
            generic_behavior_sha256: CANONICAL_BEHAVIOR_SHA256.to_owned(),
            specialized_behavior_sha256: CANONICAL_BEHAVIOR_SHA256.to_owned(),
            reference_behavior_sha256: CANONICAL_BEHAVIOR_SHA256.to_owned(),
        },
        product_gate: AYLraProductGateEvidence {
            install_gate_packet_sha256: CANONICAL_INSTALL_GATE_SHA256.to_owned(),
            consumer_admission_sha256: CANONICAL_CONSUMER_ADMISSION_SHA256.to_owned(),
            replay_identity_sha256: CANONICAL_REPLAY_IDENTITY_SHA256.to_owned(),
            telemetry_record_sha256: CANONICAL_TELEMETRY_SHA256.to_owned(),
        },
    }
}

fn assert_runtime_values_are_represented(
    proof_manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
    values: RuntimeReplayValues,
) {
    let proof_evidence = evidence
        .proof_evidence
        .as_ref()
        .expect("runtime replay evidence carries proof metadata");
    assert_eq!(
        proof_evidence
            .metadata
            .get("ay_lra.runtime_value_facts")
            .map(String::as_str),
        Some(runtime_fact_csv().as_str())
    );

    for fact in RUNTIME_VALUE_FACTS {
        assert!(
            proof_manifest
                .required_facts
                .iter()
                .any(|requirement| requirement.fact == fact),
            "basis proof manifest must source runtime fact {}",
            fact.as_str()
        );
        assert_eq!(
            evidence.facts.get(&fact),
            Some(&AYLraEvidenceAvailability::Available)
        );
        assert_eq!(
            proof_evidence
                .metadata
                .get(&runtime_fact_key(fact))
                .map(String::as_str),
            Some(values.proof_payload(fact).as_str()),
            "proof evidence must represent runtime fact {}",
            fact.as_str()
        );
    }

    let digest = values.replay_digest();
    assert_eq!(
        proof_evidence
            .metadata
            .get("ay_lra.runtime_replay_digest")
            .map(String::as_str),
        Some(digest.as_str())
    );
    assert_eq!(
        evidence.replay.generic_behavior_sha256,
        CANONICAL_BEHAVIOR_SHA256
    );
    assert_ne!(evidence.replay.generic_behavior_sha256, digest);
    assert_eq!(
        evidence.replay.specialized_behavior_sha256,
        evidence.replay.generic_behavior_sha256
    );
    assert_eq!(
        evidence.replay.reference_behavior_sha256,
        evidence.replay.generic_behavior_sha256
    );
    assert_eq!(
        evidence.basis_epoch.current_epoch,
        values.current_basis_epoch
    );
    assert_eq!(
        evidence.basis_epoch.expected_epoch,
        values.expected_basis_epoch
    );
}

fn assert_rejected_non_promoting(
    decision: AYLraAarch64LoweringDecision,
    expected_reason: AYLraManifestRejectionReason,
) {
    match decision {
        AYLraAarch64LoweringDecision::RejectNonPromoting { admission } => {
            assert_eq!(
                admission.disposition,
                AYLraManifestDisposition::RejectNonPromoting
            );
            assert!(
                admission.reasons.contains(&expected_reason),
                "expected {}, got {:?}",
                expected_reason.as_str(),
                admission.reasons
            );
            assert!(admission.non_promoting);
            assert_eq!(admission.useful_native_delta, 0);
        }
        AYLraAarch64LoweringDecision::UseNative { kind, admission } => {
            panic!("expected runtime replay rejection, got {kind:?} with {admission:?}");
        }
    }
}

#[test]
fn ay_lra_aarch64_runtime_values_are_represented_in_replay_and_proof_evidence() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let values = RuntimeReplayValues::for_generation(manifest.invalidation.generation);
    let evidence = complete_ay_lra_replay_evidence(&manifest, &proof_manifest, values);

    assert_runtime_values_are_represented(&proof_manifest, &evidence, values);

    match select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence) {
        AYLraAarch64LoweringDecision::UseNative { admission, .. } => {
            assert_eq!(
                admission.disposition,
                AYLraManifestDisposition::EmitManifest
            );
            assert!(admission.reasons.is_empty());
            assert!(admission.non_promoting);
            assert_eq!(admission.useful_native_delta, 0);
        }
        AYLraAarch64LoweringDecision::RejectNonPromoting { admission } => {
            panic!("complete runtime replay evidence should select native: {admission:?}");
        }
    }
}

#[test]
fn ay_lra_aarch64_runtime_value_replay_mutations_reject_non_promoting() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let baseline = RuntimeReplayValues::for_generation(manifest.invalidation.generation);

    let mut output_capacity = baseline;
    output_capacity.output_capacity += 1;
    let mut coefficient_lhs = baseline;
    coefficient_lhs.coefficient_lhs += 1;
    let mut basis_epoch = baseline;
    basis_epoch.current_basis_epoch += 1;
    let mut committed_prefix_rows = baseline;
    committed_prefix_rows.committed_prefix_rows += 1;

    let replay_mismatch_cases = [
        (
            AYLraProofFact::OutputCapacityBounds,
            output_capacity,
            AYLraManifestRejectionReason::ReplayMismatch,
        ),
        (
            AYLraProofFact::CoefficientOverflow,
            coefficient_lhs,
            AYLraManifestRejectionReason::ReplayMismatch,
        ),
        (
            AYLraProofFact::BatchPrefixCommitRollback,
            committed_prefix_rows,
            AYLraManifestRejectionReason::ReplayMismatch,
        ),
    ];

    for (fact, mutated, expected_reason) in replay_mismatch_cases {
        let mut evidence = complete_ay_lra_replay_evidence(&manifest, &proof_manifest, baseline);
        let mutated_digest = mutated.replay_digest();
        evidence.replay.specialized_behavior_sha256 = mutated_digest.clone();
        let proof_evidence = evidence
            .proof_evidence
            .as_mut()
            .expect("runtime replay evidence carries proof metadata");
        proof_evidence
            .metadata
            .insert("ay_lra.runtime_replay_digest".to_owned(), mutated_digest);
        proof_evidence
            .metadata
            .insert(runtime_fact_key(fact), mutated.proof_payload(fact));

        assert_rejected_non_promoting(
            select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence),
            expected_reason,
        );
    }

    let mut epoch_evidence = complete_ay_lra_replay_evidence(&manifest, &proof_manifest, baseline);
    epoch_evidence.basis_epoch.current_epoch = basis_epoch.current_basis_epoch;
    epoch_evidence
        .proof_evidence
        .as_mut()
        .expect("runtime replay evidence carries proof metadata")
        .metadata
        .insert(
            runtime_fact_key(AYLraProofFact::BasisEpochFreshness),
            basis_epoch.proof_payload(AYLraProofFact::BasisEpochFreshness),
        );

    assert_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &epoch_evidence),
        AYLraManifestRejectionReason::StaleBasisEpoch,
    );
}
