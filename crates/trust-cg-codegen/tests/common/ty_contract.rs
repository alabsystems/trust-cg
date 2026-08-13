#![allow(dead_code)]

use trust_cg_codegen::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, AliasPolicy, ArtifactManifestV1, ArtifactSection,
    ArtifactSectionKind, ArtifactSymbol, DeterministicArtifactManifest, Endianness, FieldLayout,
    InvalidationKey, JitArtifactKind, LayoutManifest, Mutability, PointerBounds, PointerLayout,
    ProofEvidenceRejectionCode, ProofEvidenceSummary, ProofEvidenceVerdict, ProofPolicy,
    RecordLayout, SliceLayout, SymbolLayout, SymbolLookupContract, SymbolSignature,
    SymbolVisibility, TargetDescriptor, TargetOperatingSystem,
};
use trust_cg_codegen::jit_install_gate::{
    TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY, TY_NATIVE_FUSED_EVIDENCE_GATE_RESULT_KEY,
    TY_NATIVE_FUSED_EVIDENCE_MANIFEST_IDENTITY_KEY,
    TY_NATIVE_FUSED_EVIDENCE_MISSING_DISPOSITION_KEY, TY_NATIVE_FUSED_EVIDENCE_MISSING_FACT_KEY,
    TY_NATIVE_FUSED_EVIDENCE_REPLAY_ROOT_KEY, TY_NATIVE_FUSED_EVIDENCE_TELEMETRY_EVENT_KEY,
    TY_NATIVE_FUSED_EVIDENCE_VALIDATION_HASH_KEY, TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION,
    TY_NATIVE_FUSED_PROOF_FACT_MISSING, TY_NATIVE_FUSED_PROOF_FACT_VERIFIED,
    TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA,
    TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{ExecutableBuffer, Target};

pub fn abi_i32() -> AbiValue {
    AbiValue::new(AbiValueKind::I32)
}

pub fn abi_i64() -> AbiValue {
    AbiValue::new(AbiValueKind::I64)
}

pub fn abi_ptr() -> AbiValue {
    AbiValue::new(AbiValueKind::Ptr)
}

pub fn extern_c_signature(params: Vec<AbiValue>, returns: Vec<AbiValue>) -> SymbolSignature {
    SymbolSignature::extern_c(params, returns)
}

pub const TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA: &str =
    "trust-cg.ty.native_fused_parent_loop_manifest/v1";
pub const TY_NATIVE_FUSED_PARENT_LOOP_STATUS_ABI: &str =
    "ty.native_fused_parent_loop.status_deopt_abi.v1";
pub const TY_NATIVE_FUSED_PARENT_LOOP_WRAPPER_IDENTITY: &str = "ty.fused-parent-loop.wrapper.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TyNativeFusedManifestIdentity {
    pub kernel_identity: String,
    pub spec_source_lock_sha256: String,
    pub trust_ir_sha256: String,
    pub native_payload_sha256: String,
    pub trust_cg_source_lock_sha256: String,
    pub generation: u64,
}

impl TyNativeFusedManifestIdentity {
    pub fn fixture(kernel_identity: impl Into<String>) -> Self {
        let kernel_identity = kernel_identity.into();
        Self {
            spec_source_lock_sha256: format!("sha256:ty-{kernel_identity}-spec-lock"),
            trust_ir_sha256: format!("sha256:ty-{kernel_identity}-trust_ir"),
            native_payload_sha256: format!("sha256:ty-{kernel_identity}-native"),
            trust_cg_source_lock_sha256: "sha256:trust-cg-ty-native-fused-parent-loop".to_owned(),
            kernel_identity,
            generation: 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TyNativeFusedEvidenceRefs {
    pub certificate_identity: String,
    pub replay_root_sha256: String,
    pub telemetry_event_id: String,
    pub gate_result_sha256: String,
    pub proof_validation_sha256: String,
}

impl TyNativeFusedEvidenceRefs {
    pub fn fixture(kernel_identity: impl Into<String>) -> Self {
        let kernel_identity = kernel_identity.into();
        Self {
            certificate_identity: format!("ty-native-fused-parent-loop:{kernel_identity}:cert-v1"),
            replay_root_sha256: format!("sha256:ty-{kernel_identity}-replay-root"),
            telemetry_event_id: format!("ty-{kernel_identity}-native-fused-install"),
            gate_result_sha256: format!("sha256:ty-{kernel_identity}-gate-result"),
            proof_validation_sha256: format!("sha256:ty-{kernel_identity}-proof-validation"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TyNativeFusedRequiredProofFact {
    StateLayoutStability,
    HelperPurityReadonly,
    ActionIndependenceOrFusedStepEquivalence,
    StateVectorBounds,
    DispatchPanicDeoptSafety,
}

impl TyNativeFusedRequiredProofFact {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::StateLayoutStability => "state_layout_stability",
            Self::HelperPurityReadonly => "helper_purity_readonly",
            Self::ActionIndependenceOrFusedStepEquivalence => {
                "action_independence_or_fused_step_equivalence"
            }
            Self::StateVectorBounds => "state_vector_bounds",
            Self::DispatchPanicDeoptSafety => "dispatch_panic_deopt_safety",
        }
    }

    pub const fn metadata_key(self) -> &'static str {
        match self {
            Self::StateLayoutStability => "ty.native_fused.fact.state_layout_stability",
            Self::HelperPurityReadonly => "ty.native_fused.fact.helper_purity_readonly",
            Self::ActionIndependenceOrFusedStepEquivalence => {
                "ty.native_fused.fact.action_independence_or_fused_step_equivalence"
            }
            Self::StateVectorBounds => "ty.native_fused.fact.state_vector_bounds",
            Self::DispatchPanicDeoptSafety => "ty.native_fused.fact.dispatch_panic_deopt_safety",
        }
    }
}

pub const TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS: [TyNativeFusedRequiredProofFact; 5] = [
    TyNativeFusedRequiredProofFact::StateLayoutStability,
    TyNativeFusedRequiredProofFact::HelperPurityReadonly,
    TyNativeFusedRequiredProofFact::ActionIndependenceOrFusedStepEquivalence,
    TyNativeFusedRequiredProofFact::StateVectorBounds,
    TyNativeFusedRequiredProofFact::DispatchPanicDeoptSafety,
];

pub fn assert_ty_native_fused_required_proof_fact_bridge() {
    assert_eq!(
        TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS.len(),
        5,
        "native-fused TY parent-loop activation requires exactly five proof facts"
    );
    let test_fact_metadata = TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS
        .iter()
        .map(|fact| (fact.metadata_key(), fact.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(
        test_fact_metadata.as_slice(),
        TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA,
        "test proof-fact fixtures must stay aligned with install-gate metadata"
    );
}

pub fn ty_reducer_manifest(
    buffer: &ExecutableBuffer,
    opt_level: OptLevel,
    symbol: &str,
    signature: SymbolSignature,
) -> ArtifactManifestV1 {
    ty_reducer_manifest_with_proof_policy(
        buffer,
        opt_level,
        symbol,
        signature,
        ProofPolicy::disabled(),
    )
}

pub fn ty_reducer_manifest_with_proof_policy(
    buffer: &ExecutableBuffer,
    opt_level: OptLevel,
    symbol: &str,
    signature: SymbolSignature,
    proof_policy: ProofPolicy,
) -> ArtifactManifestV1 {
    let (offset_bytes, size_bytes, section_size_bytes) = symbol_layout_from_buffer(buffer, symbol);
    ty_reducer_manifest_for_symbol_with_proof_policy(
        opt_level,
        symbol,
        signature,
        offset_bytes,
        size_bytes,
        section_size_bytes,
        proof_policy,
    )
}

pub fn ty_reducer_manifest_for_symbol(
    opt_level: OptLevel,
    symbol: &str,
    signature: SymbolSignature,
    offset_bytes: u64,
    size_bytes: u64,
    section_size_bytes: u64,
) -> ArtifactManifestV1 {
    ty_reducer_manifest_for_symbol_with_proof_policy(
        opt_level,
        symbol,
        signature,
        offset_bytes,
        size_bytes,
        section_size_bytes,
        ProofPolicy::disabled(),
    )
}

pub fn ty_reducer_manifest_for_symbol_with_proof_policy(
    opt_level: OptLevel,
    symbol: &str,
    signature: SymbolSignature,
    offset_bytes: u64,
    size_bytes: u64,
    section_size_bytes: u64,
    proof_policy: ProofPolicy,
) -> ArtifactManifestV1 {
    let target =
        TargetDescriptor::for_trust_cg_target(Target::Aarch64, TargetOperatingSystem::Unknown);
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ty-reducer-aapcs64-lp64".to_owned();

    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some("ty::reducer::entrypoint:lp64:v1".to_owned());
    layout.symbols.push(SymbolLayout {
        name: symbol.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(offset_bytes),
        size_bytes,
        alignment_bytes: 16,
    });
    layout
        .metadata
        .insert("consumer".to_owned(), "ty".to_owned());
    layout
        .metadata
        .insert("surface".to_owned(), "reducer-entrypoint".to_owned());

    let invalidation = InvalidationKey::new(
        format!("ty:reducer:{symbol}:entrypoint-v1"),
        format!("trust-cg:aarch64-jit:{opt_level:?}"),
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        1,
    );
    let mut manifest = DeterministicArtifactManifest::new(
        format!("ty-reducer-{symbol}-{opt_level:?}"),
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: symbol.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature,
        offset_bytes: Some(offset_bytes),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: section_size_bytes,
        alignment_bytes: 16,
        checksum: None,
    });
    manifest
        .metadata
        .insert("consumer".to_owned(), "ty".to_owned());
    manifest.metadata.insert(
        "classification".to_owned(),
        "product-reducer-entrypoint".to_owned(),
    );
    manifest
}

pub fn ty_native_fused_parent_loop_manifest(
    buffer: &ExecutableBuffer,
    opt_level: OptLevel,
    symbol: &str,
    signature: SymbolSignature,
    identity: TyNativeFusedManifestIdentity,
) -> ArtifactManifestV1 {
    ty_native_fused_parent_loop_manifest_with_proof_policy(
        buffer,
        opt_level,
        symbol,
        signature,
        identity,
        ProofPolicy::require_certificates(["ty-native-fused-parent-loop", "trust-cg-verify"]),
    )
}

pub fn ty_native_fused_parent_loop_manifest_with_proof_policy(
    buffer: &ExecutableBuffer,
    opt_level: OptLevel,
    symbol: &str,
    signature: SymbolSignature,
    identity: TyNativeFusedManifestIdentity,
    proof_policy: ProofPolicy,
) -> ArtifactManifestV1 {
    let (offset_bytes, size_bytes, section_size_bytes) = symbol_layout_from_buffer(buffer, symbol);
    ty_native_fused_parent_loop_manifest_for_symbol_with_proof_policy(
        opt_level,
        symbol,
        signature,
        offset_bytes,
        size_bytes,
        section_size_bytes,
        identity,
        proof_policy,
    )
}

#[allow(clippy::too_many_arguments)] // Fixture fields intentionally mirror the manifest schema.
pub fn ty_native_fused_parent_loop_manifest_for_symbol_with_proof_policy(
    opt_level: OptLevel,
    symbol: &str,
    signature: SymbolSignature,
    offset_bytes: u64,
    size_bytes: u64,
    section_size_bytes: u64,
    identity: TyNativeFusedManifestIdentity,
    proof_policy: ProofPolicy,
) -> ArtifactManifestV1 {
    let target =
        TargetDescriptor::for_trust_cg_target(Target::Aarch64, TargetOperatingSystem::Macos)
            .with_cpu("apple-m")
            .with_features(["fp", "simd"]);
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ty-native-fused-parent-loop-aapcs64-lp64".to_owned();

    let mut layout = ty_native_fused_parent_loop_layout(symbol, offset_bytes, size_bytes);
    let proof_policy_checksum = proof_policy.checksum();
    let descriptor_identity =
        ty_native_fused_transition_cluster_descriptor_identity(&identity.kernel_identity);
    layout.metadata.insert(
        "proof_policy_checksum".to_owned(),
        proof_policy_checksum.to_string(),
    );
    layout.metadata.insert(
        "status_deopt_contract".to_owned(),
        TY_NATIVE_FUSED_PARENT_LOOP_STATUS_ABI.to_owned(),
    );
    layout.metadata.insert(
        "native_fused_kernel_identity".to_owned(),
        identity.kernel_identity.clone(),
    );
    layout.metadata.insert(
        TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY.to_owned(),
        descriptor_identity.clone(),
    );
    let layout_checksum = layout.checksum();

    let mut invalidation = InvalidationKey::new(
        identity.spec_source_lock_sha256.clone(),
        identity.trust_cg_source_lock_sha256.clone(),
        target.checksum(),
        abi.checksum(),
        layout_checksum,
        proof_policy_checksum,
        identity.generation,
    );
    invalidation.extra.insert(
        "trust_ir_sha256".to_owned(),
        identity.trust_ir_sha256.clone(),
    );
    invalidation.extra.insert(
        "native_payload_sha256".to_owned(),
        identity.native_payload_sha256.clone(),
    );
    invalidation.extra.insert(
        "status_deopt_contract".to_owned(),
        TY_NATIVE_FUSED_PARENT_LOOP_STATUS_ABI.to_owned(),
    );
    invalidation.extra.insert(
        "native_fused_kernel_identity".to_owned(),
        identity.kernel_identity.clone(),
    );
    invalidation.extra.insert(
        TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY.to_owned(),
        descriptor_identity.clone(),
    );
    invalidation.extra.insert(
        "missing_proof_disposition".to_owned(),
        TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION.to_owned(),
    );
    for fact in TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS {
        invalidation.extra.insert(
            format!("required_fact.{}", fact.as_str()),
            fact.metadata_key().to_owned(),
        );
    }

    let mut manifest = DeterministicArtifactManifest::new(
        format!("ty-native-fused-parent-loop-{symbol}-{opt_level:?}"),
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: symbol.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature,
        offset_bytes: Some(offset_bytes),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: section_size_bytes,
        alignment_bytes: 16,
        checksum: None,
    });
    manifest
        .metadata
        .insert("consumer".to_owned(), "ty".to_owned());
    manifest.metadata.insert(
        "ty_manifest_schema".to_owned(),
        TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA.to_owned(),
    );
    manifest.metadata.insert(
        "classification".to_owned(),
        "product-native-fused-parent-loop".to_owned(),
    );
    manifest.metadata.insert(
        "native_fused_kernel_identity".to_owned(),
        identity.kernel_identity.clone(),
    );
    manifest.metadata.insert(
        TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY.to_owned(),
        descriptor_identity,
    );
    manifest.metadata.insert(
        "spec_source_lock_sha256".to_owned(),
        identity.spec_source_lock_sha256,
    );
    manifest
        .metadata
        .insert("trust_ir_sha256".to_owned(), identity.trust_ir_sha256);
    manifest.metadata.insert(
        "native_payload_sha256".to_owned(),
        identity.native_payload_sha256,
    );
    manifest.metadata.insert(
        "trust_cg_source_lock_sha256".to_owned(),
        identity.trust_cg_source_lock_sha256,
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
        "status_deopt_contract".to_owned(),
        TY_NATIVE_FUSED_PARENT_LOOP_STATUS_ABI.to_owned(),
    );
    manifest.metadata.insert(
        "dispatch_gate".to_owned(),
        "native_install_gate:ty_activation".to_owned(),
    );
    manifest.metadata.insert(
        "admission_gate".to_owned(),
        "consumer_admission:ty_native_fused_parent_loop_allowlist".to_owned(),
    );
    manifest.metadata.insert(
        "certificate_dependencies".to_owned(),
        "jit_certificate,ty-native-fused-parent-loop,trust-cg-verify".to_owned(),
    );
    manifest.metadata.insert(
        "deopt_rollback_condition".to_owned(),
        "status_deopt_or_dispatch_panic_before_successor_commit".to_owned(),
    );
    manifest.metadata.insert(
        "missing_proof_disposition".to_owned(),
        TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION.to_owned(),
    );
    manifest.metadata.insert(
        "useful_native".to_owned(),
        "false_until_gate_accepts".to_owned(),
    );
    for fact in TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS {
        manifest.metadata.insert(
            format!("required_fact.{}", fact.as_str()),
            fact.metadata_key().to_owned(),
        );
    }
    manifest
}

fn ty_native_fused_transition_cluster_descriptor_identity(kernel_identity: &str) -> String {
    format!("ty-native-fused-transition-cluster:{kernel_identity}:descriptor-v1")
}

pub fn ty_native_fused_verified_evidence(
    manifest: &ArtifactManifestV1,
    refs: &TyNativeFusedEvidenceRefs,
) -> ProofEvidenceSummary {
    let native_payload_sha256 = manifest
        .metadata
        .get("native_payload_sha256")
        .cloned()
        .expect("native-fused manifest binds native_payload_sha256");
    let mut evidence = ProofEvidenceSummary::verified_for_artifact(
        "trust-cg-verify",
        manifest,
        native_payload_sha256,
        refs.proof_validation_sha256.clone(),
    );
    bind_ty_native_fused_evidence_refs(&mut evidence, manifest, refs);
    for (key, _fact) in TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA {
        evidence.metadata.insert(
            (*key).to_owned(),
            TY_NATIVE_FUSED_PROOF_FACT_VERIFIED.to_owned(),
        );
    }
    evidence
}

pub fn ty_native_fused_missing_fact_evidence(
    manifest: &ArtifactManifestV1,
    refs: &TyNativeFusedEvidenceRefs,
    missing_fact: TyNativeFusedRequiredProofFact,
) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::rejected(
        "trust-cg-verify",
        ProofEvidenceVerdict::MissingEvidence,
        ProofEvidenceRejectionCode::MissingEvidence,
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
        manifest.invalidation.checksum(),
        manifest.proof_policy.checksum(),
    );
    bind_ty_native_fused_evidence_refs(&mut evidence, manifest, refs);
    for fact in TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS {
        let value = if fact == missing_fact {
            TY_NATIVE_FUSED_PROOF_FACT_MISSING
        } else {
            TY_NATIVE_FUSED_PROOF_FACT_VERIFIED
        };
        evidence
            .metadata
            .insert(fact.metadata_key().to_owned(), value.to_owned());
    }
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_MISSING_FACT_KEY.to_owned(),
        missing_fact.as_str().to_owned(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_MISSING_DISPOSITION_KEY.to_owned(),
        TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION.to_owned(),
    );
    evidence
}

fn bind_ty_native_fused_evidence_refs(
    evidence: &mut ProofEvidenceSummary,
    manifest: &ArtifactManifestV1,
    refs: &TyNativeFusedEvidenceRefs,
) {
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_MANIFEST_IDENTITY_KEY.to_owned(),
        manifest.checksum().to_string(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY.to_owned(),
        refs.certificate_identity.clone(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_REPLAY_ROOT_KEY.to_owned(),
        refs.replay_root_sha256.clone(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_TELEMETRY_EVENT_KEY.to_owned(),
        refs.telemetry_event_id.clone(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_GATE_RESULT_KEY.to_owned(),
        refs.gate_result_sha256.clone(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_VALIDATION_HASH_KEY.to_owned(),
        refs.proof_validation_sha256.clone(),
    );
}

fn ty_native_fused_parent_loop_layout(
    symbol: &str,
    offset_bytes: u64,
    size_bytes: u64,
) -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some(TY_NATIVE_FUSED_PARENT_LOOP_WRAPPER_IDENTITY.to_owned());
    layout.records.push(RecordLayout {
        name: "TyNativeFusedParentLoopStatusAbi".to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: 32,
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
                name: "panic_code".to_owned(),
                offset_bytes: 2,
                size_bytes: 2,
                alignment_bytes: 2,
            },
            FieldLayout {
                name: "reserved".to_owned(),
                offset_bytes: 4,
                size_bytes: 4,
                alignment_bytes: 1,
            },
            FieldLayout {
                name: "generated_count".to_owned(),
                offset_bytes: 8,
                size_bytes: 8,
                alignment_bytes: 8,
            },
            FieldLayout {
                name: "first_failed_parent".to_owned(),
                offset_bytes: 16,
                size_bytes: 8,
                alignment_bytes: 8,
            },
            FieldLayout {
                name: "rollback_epoch".to_owned(),
                offset_bytes: 24,
                size_bytes: 8,
                alignment_bytes: 8,
            },
        ],
    });
    layout.slices.push(ty_native_fused_slice(
        "flat_state_buffer",
        "state_count",
        Mutability::Immutable,
    ));
    layout.slices.push(ty_native_fused_slice(
        "parent_buffer",
        "parent_capacity",
        Mutability::Mutable,
    ));
    layout.slices.push(ty_native_fused_slice(
        "successor_buffer",
        "successor_capacity",
        Mutability::Mutable,
    ));
    layout.slices.push(ty_native_fused_slice(
        "fingerprint_buffer",
        "successor_capacity",
        Mutability::Mutable,
    ));
    layout.slices.push(SliceLayout {
        name: "callback_status_buffer".to_owned(),
        element_size_bytes: 4,
        element_alignment_bytes: 4,
        stride_bytes: 4,
        length: None,
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: 256,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.pointers.push(PointerLayout {
        name: "runtime_arena".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: 4096,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.pointers.push(PointerLayout {
        name: "status_out".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: 32,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.symbols.push(SymbolLayout {
        name: symbol.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(offset_bytes),
        size_bytes,
        alignment_bytes: 16,
    });
    layout
        .metadata
        .insert("consumer".to_owned(), "ty".to_owned());
    layout.metadata.insert(
        "state_layout_stability".to_owned(),
        "flat_state_parent_successor_fingerprint_status_v1".to_owned(),
    );
    layout.metadata.insert(
        "helper_purity_readonly".to_owned(),
        "runtime_callbacks_status_only_no_state_mutation".to_owned(),
    );
    layout.metadata.insert(
        "fused_step_invariants".to_owned(),
        "parent_index_fingerprint_generated_count_preserved".to_owned(),
    );
    layout.metadata.insert(
        "bounds_pointer_facts".to_owned(),
        "state_count_parent_capacity_successor_capacity_runtime_checked".to_owned(),
    );
    layout.metadata.insert(
        "dispatch_panic_deopt_safety".to_owned(),
        "panic_or_status_error_deopts_before_useful_native_credit".to_owned(),
    );
    layout
}

fn ty_native_fused_slice(name: &str, bounds_symbol: &str, mutability: Mutability) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes: 8,
        element_alignment_bytes: 8,
        stride_bytes: 8,
        length: None,
        bounds: PointerBounds::Symbol(bounds_symbol.to_owned()),
        mutability,
        alias_policy: match mutability {
            Mutability::Immutable => AliasPolicy::SharedReadOnly,
            Mutability::Mutable => AliasPolicy::Exclusive,
        },
    }
}

pub fn ty_reducer_lookup_contract(
    manifest: &ArtifactManifestV1,
    symbol: &str,
    signature: SymbolSignature,
) -> SymbolLookupContract {
    SymbolLookupContract::new(
        symbol,
        signature,
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
}

pub fn bind_ty_reducer_entry<F: Copy>(
    buffer: &ExecutableBuffer,
    opt_level: OptLevel,
    symbol: &str,
    signature: SymbolSignature,
) -> F {
    let manifest = ty_reducer_manifest(buffer, opt_level, symbol, signature.clone());
    let contract = ty_reducer_lookup_contract(&manifest, symbol, signature);
    manifest
        .validate_symbol_lookup(&contract)
        .unwrap_or_else(|err| {
            panic!("{opt_level:?} {symbol} failed TY reducer fixture-contract validation: {err}")
        });
    // This helper is intentionally a low-level integration-test probe, not a
    // product install/dispatch boundary. A caller-synthesized fixture manifest
    // can assert the test's expected ABI but cannot stand in for the compiler-
    // derived payload binding required by InstalledArtifact product lookup.
    // SAFETY: the fixture contract above validates the ABI expected by this
    // test wrapper, and every caller retains `buffer` while invoking `F`.
    unsafe { buffer.get_fn_bound::<F>(symbol) }
        .unwrap_or_else(|| panic!("{opt_level:?} {symbol} missing from TY reducer JIT buffer"))
        .into_inner()
}

fn symbol_layout_from_buffer(buffer: &ExecutableBuffer, symbol: &str) -> (u64, u64, u64) {
    let offset_bytes = buffer
        .symbols()
        .find_map(|(name, offset)| (name == symbol).then_some(offset))
        .unwrap_or_else(|| panic!("{symbol} entry symbol should exist"));
    let size_bytes = buffer
        .symbols()
        .filter_map(|(_name, offset)| (offset > offset_bytes).then_some(offset - offset_bytes))
        .min()
        .unwrap_or_else(|| buffer.allocated_size() as u64 - offset_bytes);
    (offset_bytes, size_bytes, buffer.allocated_size() as u64)
}
