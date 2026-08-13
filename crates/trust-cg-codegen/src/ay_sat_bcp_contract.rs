// trust-cg-codegen/ay_sat_bcp_contract.rs - ay SAT watched-list BCP contract helpers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only artifact contract helpers for the ay SAT watched-list BCP slice.
//!
//! This module binds the proof metadata, ABI/layout records, signature,
//! proof-policy, invalidation, and manifest shape used by the pre-activation
//! watched-list BCP path. It intentionally does not publish native execution
//! entry points, register ay native dispatch, or authorize useful-native
//! counters.

use std::collections::BTreeMap;

use crate::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, AliasPolicy, ArtifactSection, ArtifactSectionKind,
    ArtifactSymbol, DeterministicArtifactManifest, Endianness, FieldLayout, InvalidationKey,
    JitArtifactKind, LayoutManifest, Mutability, PointerBounds, PointerLayout,
    ProofEvidenceSummary, ProofPolicy, RecordLayout, SliceLayout, SymbolLayout,
    SymbolLookupContract, SymbolSignature, SymbolVisibility, TargetDescriptor,
    TargetOperatingSystem,
};
use crate::target::Target;

/// Stable schema tag for SAT watched-list BCP contract helper output.
pub const AY_SAT_BCP_ARTIFACT_CONTRACT_SCHEMA: &str = "trust-cg.ay_sat_bcp.artifact_contract.v1";

/// Stable numeric schema version for SAT watched-list BCP contract helpers.
pub const AY_SAT_BCP_ARTIFACT_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Stable proof-fact schema shared with the ay canary allowlist.
pub const AY_SAT_BCP_PROOF_FACT_SCHEMA: &str =
    "trust-cg.jit_everywhere.ay_canary.bcp_proof_facts.v1";

/// Metadata key prefix for one required SAT watched-list BCP proof fact.
pub const AY_SAT_BCP_PROOF_FACT_METADATA_PREFIX: &str = "ay_bcp.proof_fact.";

/// Callable status-probe symbol named by the pre-activation contract.
pub const AY_SAT_BCP_SYMBOL: &str = "ay_sat_watch_bcp_status_probe";

/// Artifact id for the canonical SAT watched-list BCP status-probe manifest.
pub const AY_SAT_BCP_ARTIFACT_ID: &str = "ay-sat-watch-bcp-status-probe";

/// SAT watched-list BCP kernel metadata id.
pub const AY_SAT_BCP_KERNEL: &str = "ay_sat_watch_bcp";

/// Consumer metadata id.
pub const AY_SAT_BCP_CONSUMER: &str = "ay";

/// Domain metadata id.
pub const AY_SAT_BCP_DOMAIN: &str = "sat";

/// Proof family metadata id.
pub const AY_SAT_BCP_PROOF_FAMILY: &str = "ay-watch-bcp";

/// Rust wrapper/layout identity for the LP64 watched-list BCP kernel.
pub const AY_SAT_BCP_WRAPPER_IDENTITY: &str = "ay::sat::WatchBcpKernel::lp64:v1";

/// Propagation context record name.
pub const AY_SAT_BCP_CONTEXT_RECORD: &str = "PropagationContext";

/// Result ABI record name.
pub const AY_SAT_BCP_RESULT_RECORD: &str = "AYSatWatchBcpResultAbi";

/// Stable propagation context ABI metadata id.
pub const AY_SAT_BCP_CONTEXT_ABI: &str = "ay_sat_propagation_context_abi_v1";

/// Stable result/status ABI metadata id.
pub const AY_SAT_BCP_RESULT_ABI: &str = "ay_sat_bcp_result_abi_v1";

/// Runtime generation policy metadata id.
pub const AY_SAT_BCP_GENERATION_POLICY: &str = "fail_closed_epoch_match";

/// Watch-list layout metadata id.
pub const AY_SAT_BCP_WATCH_LAYOUT: &str = "two_watched_literals_v1";

/// Source invalidation fingerprint for the canonical SAT watched-list BCP contract.
pub const AY_SAT_BCP_SOURCE_FINGERPRINT: &str = "ay:sat:watch-bcp:kernel-v1";

/// Compiler/profile invalidation fingerprint for the canonical contract.
pub const AY_SAT_BCP_COMPILER_FINGERPRINT: &str = "trust-cg:phase5:sat:bcp:o2";

/// Default pre-activation generation used by the pure contract fixture.
pub const AY_SAT_BCP_DEFAULT_GENERATION: u64 = 66;

/// Canonical pre-activation text size used by the manifest contract.
pub const AY_SAT_BCP_TEXT_SIZE_BYTES: u64 = 320;

/// Canonical native payload digest for the pre-activation contract fixture.
pub const AY_SAT_BCP_NATIVE_PAYLOAD_SHA256: &str = "sha256:ay-sat-watch-bcp-native-payload";

/// Canonical proof report digest for the pre-activation contract fixture.
pub const AY_SAT_BCP_PROOF_REPORT_SHA256: &str = "sha256:ay-sat-watch-bcp-proof-report";

/// Propagation context record size.
pub const AY_SAT_BCP_CONTEXT_SIZE_BYTES: u64 = 168;

/// Result ABI record size.
pub const AY_SAT_BCP_RESULT_SIZE_BYTES: u64 = 56;

/// Watched-list entry size.
pub const AY_SAT_BCP_WATCH_ENTRY_SIZE_BYTES: u64 = 16;

/// Watched-list entry stride.
pub const AY_SAT_BCP_WATCH_ENTRY_STRIDE_BYTES: u64 = 16;

/// Typed SAT watched-list BCP proof fact required by the contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYSatBcpProofFact {
    /// Watch heads and entries implement the two-watched-literals layout.
    WatchLayout,
    /// Clause arena reads are bounded by the runtime arena length.
    ClauseArenaBounds,
    /// Assignment and trail generations are fresh for propagation.
    AssignmentTrailFreshness,
    /// Pending queue head/tail remain within capacity.
    PendingQueueBounds,
    /// Runtime, watch, assignment, and expected generations match.
    GenerationMatch,
    /// Result record ABI and status encoding are bound.
    ResultAbi,
    /// Generic, specialized, and reference replay artifacts compare equal.
    ReplayComparison,
}

impl AYSatBcpProofFact {
    /// Return the stable lower-snake-case fact id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::WatchLayout => "watch_layout",
            Self::ClauseArenaBounds => "clause_arena_bounds",
            Self::AssignmentTrailFreshness => "assignment_trail_freshness",
            Self::PendingQueueBounds => "pending_queue_bounds",
            Self::GenerationMatch => "generation_match",
            Self::ResultAbi => "result_abi",
            Self::ReplayComparison => "replay_comparison",
        }
    }

    /// Return the stable proof-evidence metadata key for this fact.
    pub fn metadata_key(self) -> String {
        format!("{AY_SAT_BCP_PROOF_FACT_METADATA_PREFIX}{}", self.as_str())
    }
}

/// One required SAT watched-list BCP proof-fact metadata binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AYSatBcpProofFactRequirement {
    /// Required proof fact.
    pub fact: AYSatBcpProofFact,
    /// Stable lemma or checker id expected from proof evidence.
    pub lemma_id: &'static str,
}

/// Required SAT watched-list BCP proof facts in canonical metadata order.
pub const AY_SAT_BCP_PROOF_FACT_REQUIREMENTS: [AYSatBcpProofFactRequirement; 7] = [
    AYSatBcpProofFactRequirement {
        fact: AYSatBcpProofFact::WatchLayout,
        lemma_id: "ay_sat_bcp.watch_layout_two_watched_literals",
    },
    AYSatBcpProofFactRequirement {
        fact: AYSatBcpProofFact::ClauseArenaBounds,
        lemma_id: "ay_sat_bcp.clause_arena_bounds",
    },
    AYSatBcpProofFactRequirement {
        fact: AYSatBcpProofFact::AssignmentTrailFreshness,
        lemma_id: "ay_sat_bcp.assignment_trail_freshness",
    },
    AYSatBcpProofFactRequirement {
        fact: AYSatBcpProofFact::PendingQueueBounds,
        lemma_id: "ay_sat_bcp.pending_queue_bounds",
    },
    AYSatBcpProofFactRequirement {
        fact: AYSatBcpProofFact::GenerationMatch,
        lemma_id: "ay_sat_bcp.generation_match",
    },
    AYSatBcpProofFactRequirement {
        fact: AYSatBcpProofFact::ResultAbi,
        lemma_id: "trust_cg_ay_bcp.result_abi_bound",
    },
    AYSatBcpProofFactRequirement {
        fact: AYSatBcpProofFact::ReplayComparison,
        lemma_id: "trust_cg_ay_bcp.replay_generic_specialized_reference_equal",
    },
];

/// Return the stable comma-separated required proof fact ids.
pub fn ay_sat_bcp_required_fact_csv() -> String {
    AY_SAT_BCP_PROOF_FACT_REQUIREMENTS
        .iter()
        .map(|requirement| requirement.fact.as_str())
        .collect::<Vec<_>>()
        .join(",")
}

/// Insert the canonical SAT watched-list BCP proof-fact metadata.
pub fn insert_ay_sat_bcp_proof_fact_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "proof_fact_schema".to_owned(),
        AY_SAT_BCP_PROOF_FACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "required_proof_facts".to_owned(),
        ay_sat_bcp_required_fact_csv(),
    );
    for requirement in AY_SAT_BCP_PROOF_FACT_REQUIREMENTS {
        metadata.insert(
            requirement.fact.metadata_key(),
            requirement.lemma_id.to_owned(),
        );
    }
}

/// Return true when a metadata map carries the canonical required fact bindings.
pub fn ay_sat_bcp_proof_fact_metadata_matches(metadata: &BTreeMap<String, String>) -> bool {
    metadata.get("proof_fact_schema").map(String::as_str) == Some(AY_SAT_BCP_PROOF_FACT_SCHEMA)
        && metadata.get("required_proof_facts").map(String::as_str)
            == Some(ay_sat_bcp_required_fact_csv().as_str())
        && AY_SAT_BCP_PROOF_FACT_REQUIREMENTS
            .iter()
            .all(|requirement| {
                metadata
                    .get(&requirement.fact.metadata_key())
                    .map(String::as_str)
                    == Some(requirement.lemma_id)
            })
}

/// Build the canonical SAT watched-list BCP `extern "C"` status signature.
pub fn ay_sat_watch_bcp_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![AbiValue::new(AbiValueKind::Ptr)],
        vec![AbiValue::new(AbiValueKind::I32)],
    )
}

/// Build the canonical AArch64/macOS target descriptor for this contract.
pub fn ay_sat_watch_bcp_aarch64_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target(Target::Aarch64, TargetOperatingSystem::Macos)
        .with_cpu("apple-m")
        .with_features(["fp", "simd"])
}

/// Build the canonical AAPCS64/LP64 ABI descriptor for this contract.
pub fn ay_sat_watch_bcp_aarch64_abi() -> AbiDescriptor {
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ay-sat-watch-bcp-aapcs64-lp64".to_owned();
    abi
}

/// Build the propagation context record layout.
pub fn ay_sat_watch_bcp_propagation_context_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_SAT_BCP_CONTEXT_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: AY_SAT_BCP_CONTEXT_SIZE_BYTES,
        alignment_bytes: 8,
        fields: vec![
            field("clause_arena", 0, 8, 8),
            field("clause_arena_len", 8, 8, 8),
            field("watch_heads", 16, 8, 8),
            field("watch_head_count", 24, 8, 8),
            field("watch_entries", 32, 8, 8),
            field("watch_entry_count", 40, 8, 8),
            field("assignment", 48, 8, 8),
            field("assignment_len", 56, 8, 8),
            field("trail", 64, 8, 8),
            field("trail_len", 72, 8, 8),
            field("pending_queue", 80, 8, 8),
            field("pending_queue_head", 88, 8, 8),
            field("pending_queue_tail", 96, 8, 8),
            field("pending_queue_capacity", 104, 8, 8),
            field("result", 112, 8, 8),
            field("generation_facts", 120, 8, 8),
            field("context_generation", 128, 8, 8),
            field("expected_generation", 136, 8, 8),
            field("watch_generation", 144, 8, 8),
            field("assignment_generation", 152, 8, 8),
            field("status", 160, 4, 4),
            field("reserved", 164, 4, 4),
        ],
    }
}

/// Build the result/status ABI record layout.
pub fn ay_sat_watch_bcp_result_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_SAT_BCP_RESULT_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: AY_SAT_BCP_RESULT_SIZE_BYTES,
        alignment_bytes: 8,
        fields: vec![
            field("status", 0, 4, 4),
            field("conflict_clause", 4, 4, 4),
            field("propagated_literals", 8, 8, 8),
            field("trail_len", 16, 8, 8),
            field("pending_queue_head", 24, 8, 8),
            field("pending_queue_tail", 32, 8, 8),
            field("generation", 40, 8, 8),
            field("detail", 48, 8, 8),
        ],
    }
}

/// Build the canonical LP64 layout manifest.
pub fn ay_sat_watch_bcp_layout() -> LayoutManifest {
    ay_sat_watch_bcp_layout_with_text_size(16, AY_SAT_BCP_TEXT_SIZE_BYTES)
}

/// Build an LP64 layout manifest with a caller-specified stack alignment and text size.
pub fn ay_sat_watch_bcp_layout_with_text_size(
    stack_alignment_bytes: u16,
    text_size_bytes: u64,
) -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, stack_alignment_bytes);
    layout.wrapper_identity = Some(AY_SAT_BCP_WRAPPER_IDENTITY.to_owned());
    layout
        .records
        .push(ay_sat_watch_bcp_propagation_context_record_layout());
    layout.records.push(ay_sat_watch_bcp_result_record_layout());
    layout.slices.push(fixed_slice(
        "propagation_context",
        AY_SAT_BCP_CONTEXT_SIZE_BYTES,
        8,
        1,
        Mutability::Mutable,
    ));
    layout.slices.push(slice(
        "clause_arena",
        4,
        4,
        PointerBounds::Symbol("clause_arena_len".to_owned()),
        Mutability::Immutable,
    ));
    layout.slices.push(slice(
        "watch_heads",
        4,
        4,
        PointerBounds::Symbol("watch_head_count".to_owned()),
        Mutability::Mutable,
    ));
    layout.slices.push(slice(
        "watch_entries",
        AY_SAT_BCP_WATCH_ENTRY_SIZE_BYTES,
        8,
        PointerBounds::Symbol("watch_entry_count".to_owned()),
        Mutability::Mutable,
    ));
    layout.slices.push(slice(
        "assignment",
        1,
        1,
        PointerBounds::Symbol("assignment_len".to_owned()),
        Mutability::Mutable,
    ));
    layout.slices.push(slice(
        "trail",
        4,
        4,
        PointerBounds::Symbol("trail_len".to_owned()),
        Mutability::Mutable,
    ));
    layout.slices.push(slice(
        "pending_queue",
        4,
        4,
        PointerBounds::Symbol("pending_queue_capacity".to_owned()),
        Mutability::Mutable,
    ));
    layout.slices.push(fixed_slice(
        "result",
        AY_SAT_BCP_RESULT_SIZE_BYTES,
        8,
        1,
        Mutability::Mutable,
    ));
    layout.slices.push(slice(
        "generation_facts",
        8,
        8,
        PointerBounds::Symbol("generation_fact_count".to_owned()),
        Mutability::Immutable,
    ));
    layout.pointers.push(PointerLayout {
        name: "context".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: AY_SAT_BCP_CONTEXT_SIZE_BYTES,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.pointers.push(PointerLayout {
        name: "result".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: AY_SAT_BCP_RESULT_SIZE_BYTES,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.symbols.push(SymbolLayout {
        name: AY_SAT_BCP_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: text_size_bytes,
        alignment_bytes: 16,
    });
    insert_ay_sat_bcp_layout_metadata(&mut layout.metadata);
    layout
}

/// Build the fail-closed proof policy for pre-activation SAT watched-list BCP.
pub fn ay_sat_watch_bcp_proof_policy() -> ProofPolicy {
    ProofPolicy::require_certificates(["ay-sat", AY_SAT_BCP_PROOF_FAMILY, "trust-cg-verify"])
}

/// Build the default invalidation key for the canonical AArch64 contract.
pub fn ay_sat_watch_bcp_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    ay_sat_watch_bcp_invalidation_with_generation(
        target,
        abi,
        layout,
        proof_policy,
        AY_SAT_BCP_DEFAULT_GENERATION,
    )
}

/// Build an invalidation key for a caller-specified generation.
pub fn ay_sat_watch_bcp_invalidation_with_generation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
    generation: u64,
) -> InvalidationKey {
    let mut invalidation = InvalidationKey::new(
        AY_SAT_BCP_SOURCE_FINGERPRINT,
        AY_SAT_BCP_COMPILER_FINGERPRINT,
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        generation,
    );
    insert_ay_sat_bcp_invalidation_metadata(&mut invalidation.extra);
    invalidation
}

/// Build the canonical pre-activation AArch64 artifact manifest.
pub fn ay_sat_watch_bcp_manifest() -> DeterministicArtifactManifest {
    ay_sat_watch_bcp_manifest_with_generation(AY_SAT_BCP_DEFAULT_GENERATION)
}

/// Build the canonical AArch64 artifact manifest for a caller-specified generation.
pub fn ay_sat_watch_bcp_manifest_with_generation(generation: u64) -> DeterministicArtifactManifest {
    let target = ay_sat_watch_bcp_aarch64_target();
    let abi = ay_sat_watch_bcp_aarch64_abi();
    let layout = ay_sat_watch_bcp_layout();
    let proof_policy = ay_sat_watch_bcp_proof_policy();
    ay_sat_watch_bcp_manifest_for_parts(
        target,
        abi,
        layout,
        proof_policy,
        generation,
        AY_SAT_BCP_TEXT_SIZE_BYTES,
    )
}

/// Build a manifest from explicit contract parts.
pub fn ay_sat_watch_bcp_manifest_for_parts(
    target: TargetDescriptor,
    abi: AbiDescriptor,
    layout: LayoutManifest,
    proof_policy: ProofPolicy,
    generation: u64,
    text_size_bytes: u64,
) -> DeterministicArtifactManifest {
    let text_size_bytes = ay_sat_watch_bcp_layout_text_size_bytes(&layout, text_size_bytes);
    let invalidation = ay_sat_watch_bcp_invalidation_with_generation(
        &target,
        &abi,
        &layout,
        &proof_policy,
        generation,
    );
    let mut manifest = DeterministicArtifactManifest::new(
        AY_SAT_BCP_ARTIFACT_ID,
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: AY_SAT_BCP_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_sat_watch_bcp_signature(),
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
    insert_ay_sat_bcp_manifest_metadata(&mut manifest.metadata);
    manifest
}

fn ay_sat_watch_bcp_layout_text_size_bytes(layout: &LayoutManifest, fallback: u64) -> u64 {
    layout
        .symbols
        .iter()
        .find(|symbol| symbol.name == AY_SAT_BCP_SYMBOL && symbol.section == ".text")
        .map(|symbol| symbol.size_bytes)
        .unwrap_or(fallback)
}

/// Build a verified proof-evidence summary bound to a SAT BCP manifest.
pub fn ay_sat_watch_bcp_verified_proof_evidence(
    verifier: impl Into<String>,
    manifest: &DeterministicArtifactManifest,
) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::verified_for_artifact(
        verifier,
        manifest,
        AY_SAT_BCP_NATIVE_PAYLOAD_SHA256,
        AY_SAT_BCP_PROOF_REPORT_SHA256,
    );
    insert_ay_sat_bcp_evidence_metadata(&mut evidence.metadata);
    evidence
}

/// Build the symbol lookup contract for the SAT watched-list BCP status probe.
pub fn ay_sat_watch_bcp_symbol_lookup_contract(
    manifest: &DeterministicArtifactManifest,
    proof_evidence: ProofEvidenceSummary,
) -> SymbolLookupContract {
    SymbolLookupContract::new(
        AY_SAT_BCP_SYMBOL,
        ay_sat_watch_bcp_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
    .with_proof_evidence(proof_evidence)
}

fn insert_ay_sat_bcp_layout_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert("kernel".to_owned(), AY_SAT_BCP_KERNEL.to_owned());
    metadata.insert("context_abi".to_owned(), AY_SAT_BCP_CONTEXT_ABI.to_owned());
    metadata.insert("status_abi".to_owned(), AY_SAT_BCP_RESULT_ABI.to_owned());
    metadata.insert(
        "generation_policy".to_owned(),
        AY_SAT_BCP_GENERATION_POLICY.to_owned(),
    );
    insert_ay_sat_bcp_proof_fact_metadata(metadata);
}

fn insert_ay_sat_bcp_manifest_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert("consumer".to_owned(), AY_SAT_BCP_CONSUMER.to_owned());
    metadata.insert("domain".to_owned(), AY_SAT_BCP_DOMAIN.to_owned());
    metadata.insert("kernel".to_owned(), AY_SAT_BCP_KERNEL.to_owned());
    metadata.insert("context_abi".to_owned(), AY_SAT_BCP_CONTEXT_ABI.to_owned());
    metadata.insert("status_abi".to_owned(), AY_SAT_BCP_RESULT_ABI.to_owned());
    metadata.insert(
        "artifact_contract_schema".to_owned(),
        AY_SAT_BCP_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema_version".to_owned(),
        AY_SAT_BCP_ARTIFACT_CONTRACT_SCHEMA_VERSION.to_string(),
    );
    metadata.insert(
        "native_install".to_owned(),
        "disabled_pre_activation".to_owned(),
    );
    metadata.insert("useful_native".to_owned(), "0".to_owned());
    metadata.insert(
        "baseline_authoritative_until_product_gate".to_owned(),
        "true".to_owned(),
    );
    metadata.insert(
        "native_payload_sha256".to_owned(),
        AY_SAT_BCP_NATIVE_PAYLOAD_SHA256.to_owned(),
    );
    insert_ay_sat_bcp_proof_fact_metadata(metadata);
}

fn insert_ay_sat_bcp_evidence_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert("kernel".to_owned(), AY_SAT_BCP_KERNEL.to_owned());
    metadata.insert(
        "proof_family".to_owned(),
        AY_SAT_BCP_PROOF_FAMILY.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema".to_owned(),
        AY_SAT_BCP_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
    );
    insert_ay_sat_bcp_proof_fact_metadata(metadata);
}

fn insert_ay_sat_bcp_invalidation_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert("assignment_generation".to_owned(), "runtime".to_owned());
    metadata.insert("clause_arena".to_owned(), "runtime_readonly".to_owned());
    metadata.insert("context_generation".to_owned(), "runtime".to_owned());
    metadata.insert("expected_generation".to_owned(), "runtime".to_owned());
    metadata.insert("generation_facts".to_owned(), "runtime_readonly".to_owned());
    metadata.insert(
        "generation_policy".to_owned(),
        AY_SAT_BCP_GENERATION_POLICY.to_owned(),
    );
    metadata.insert("pending_queue".to_owned(), "mutable_runtime".to_owned());
    metadata.insert("status_abi".to_owned(), AY_SAT_BCP_RESULT_ABI.to_owned());
    metadata.insert("trail".to_owned(), "mutable_runtime".to_owned());
    metadata.insert("watch_generation".to_owned(), "runtime".to_owned());
    metadata.insert(
        "watch_layout".to_owned(),
        AY_SAT_BCP_WATCH_LAYOUT.to_owned(),
    );
}

fn slice(
    name: &str,
    element_size_bytes: u64,
    element_alignment_bytes: u32,
    bounds: PointerBounds,
    mutability: Mutability,
) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes,
        element_alignment_bytes,
        stride_bytes: element_size_bytes,
        length: None,
        bounds,
        mutability,
        alias_policy: alias_policy_for_mutability(mutability),
    }
}

fn fixed_slice(
    name: &str,
    element_size_bytes: u64,
    element_alignment_bytes: u32,
    length: u64,
    mutability: Mutability,
) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes,
        element_alignment_bytes,
        stride_bytes: element_size_bytes,
        length: Some(length),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: element_size_bytes * length,
        },
        mutability,
        alias_policy: alias_policy_for_mutability(mutability),
    }
}

const fn alias_policy_for_mutability(mutability: Mutability) -> AliasPolicy {
    match mutability {
        Mutability::Immutable => AliasPolicy::SharedReadOnly,
        Mutability::Mutable => AliasPolicy::Exclusive,
    }
}

fn field(name: &str, offset_bytes: u64, size_bytes: u64, alignment_bytes: u32) -> FieldLayout {
    FieldLayout {
        name: name.to_owned(),
        offset_bytes,
        size_bytes,
        alignment_bytes,
    }
}
