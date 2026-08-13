// trust-cg-codegen/tests/ay_sat_bcp_manifest_contract.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeMap;

use trust_cg_codegen::ay_sat_bcp_contract::{
    AY_SAT_BCP_CONTEXT_RECORD, AY_SAT_BCP_CONTEXT_SIZE_BYTES, AY_SAT_BCP_PROOF_FACT_REQUIREMENTS,
    AY_SAT_BCP_PROOF_FACT_SCHEMA, AY_SAT_BCP_RESULT_RECORD, AY_SAT_BCP_RESULT_SIZE_BYTES,
    AY_SAT_BCP_SYMBOL, AY_SAT_BCP_TEXT_SIZE_BYTES, AY_SAT_BCP_WATCH_ENTRY_SIZE_BYTES,
    AY_SAT_BCP_WATCH_ENTRY_STRIDE_BYTES, AYSatBcpProofFact, ay_sat_bcp_required_fact_csv,
    ay_sat_watch_bcp_aarch64_abi, ay_sat_watch_bcp_aarch64_target,
    ay_sat_watch_bcp_layout_with_text_size, ay_sat_watch_bcp_manifest,
    ay_sat_watch_bcp_manifest_for_parts, ay_sat_watch_bcp_proof_policy, ay_sat_watch_bcp_signature,
    ay_sat_watch_bcp_symbol_lookup_contract, ay_sat_watch_bcp_verified_proof_evidence,
};
use trust_cg_codegen::jit_contract::{
    AbiValue, AbiValueKind, AliasPolicy, DeterministicArtifactManifest, Mutability, PointerBounds,
    RecordLayout, SliceLayout, SymbolSignature,
};

#[repr(C)]
struct PropagationContext {
    _opaque: [u8; 0],
}

type AYSatWatchBcpFn = unsafe extern "C" fn(*mut PropagationContext) -> i32;

fn assert_bcp_proof_fact_metadata(metadata: &BTreeMap<String, String>) {
    let required_facts = ay_sat_bcp_required_fact_csv();
    assert_eq!(
        metadata.get("proof_fact_schema").map(String::as_str),
        Some(AY_SAT_BCP_PROOF_FACT_SCHEMA)
    );
    assert_eq!(
        metadata.get("required_proof_facts").map(String::as_str),
        Some(required_facts.as_str())
    );
    for requirement in AY_SAT_BCP_PROOF_FACT_REQUIREMENTS {
        assert_eq!(
            metadata
                .get(&requirement.fact.metadata_key())
                .map(String::as_str),
            Some(requirement.lemma_id),
            "missing typed BCP proof fact metadata for {}",
            requirement.fact.as_str()
        );
    }
}

fn nullable_context_pointer_signature() -> SymbolSignature {
    let mut signature = ay_sat_watch_bcp_signature();
    let context = signature
        .params
        .first_mut()
        .expect("BCP signature includes a context pointer");
    *context = AbiValue::new(AbiValueKind::Ptr).nullable();
    signature
}

fn slice_by_name<'a>(manifest: &'a DeterministicArtifactManifest, name: &str) -> &'a SliceLayout {
    manifest
        .layout
        .slices
        .iter()
        .find(|slice| slice.name == name)
        .unwrap_or_else(|| panic!("SAT BCP manifest binds {name} layout"))
}

fn record_by_name<'a>(manifest: &'a DeterministicArtifactManifest, name: &str) -> &'a RecordLayout {
    manifest
        .layout
        .records
        .iter()
        .find(|record| record.name == name)
        .unwrap_or_else(|| panic!("SAT BCP manifest binds {name} record layout"))
}

#[test]
fn ay_sat_bcp_manifest_binds_context_status_generations_and_proof_evidence() {
    let manifest = ay_sat_watch_bcp_manifest();
    let expected_signature = ay_sat_watch_bcp_signature();
    let baseline_checksum = manifest.checksum();
    let proof_evidence = ay_sat_watch_bcp_verified_proof_evidence("trust-cg-verify", &manifest);
    assert_bcp_proof_fact_metadata(&manifest.layout.metadata);
    assert_bcp_proof_fact_metadata(&manifest.metadata);
    assert_bcp_proof_fact_metadata(&proof_evidence.metadata);
    let install_contract =
        ay_sat_watch_bcp_symbol_lookup_contract(&manifest, proof_evidence.clone());

    assert_eq!(
        std::mem::size_of::<AYSatWatchBcpFn>(),
        std::mem::size_of::<*const u8>()
    );
    assert_eq!(
        manifest.symbol_signature(AY_SAT_BCP_SYMBOL),
        Some(&expected_signature)
    );
    assert_eq!(
        expected_signature.params,
        vec![AbiValue::new(AbiValueKind::Ptr)]
    );
    assert_eq!(
        expected_signature.returns,
        vec![AbiValue::new(AbiValueKind::I32)]
    );
    assert_eq!(install_contract.symbol, AY_SAT_BCP_SYMBOL);
    assert_eq!(install_contract.signature, expected_signature);
    assert_eq!(install_contract.target_checksum, manifest.target.checksum());
    assert_eq!(install_contract.abi_checksum, manifest.abi.checksum());
    assert_eq!(install_contract.layout_checksum, manifest.layout.checksum());
    assert_eq!(
        install_contract.invalidation_checksum,
        Some(manifest.invalidation.checksum())
    );
    assert_eq!(install_contract.manifest_checksum, Some(baseline_checksum));
    assert_eq!(install_contract.proof_evidence, Some(proof_evidence));
    manifest
        .validate_symbol_lookup(&install_contract)
        .expect("manifest satisfies the typed SAT BCP symbol lookup contract");

    assert_eq!(manifest.target.pointer_width_bits, 64);
    assert_eq!(manifest.abi.pointer_width_bits, 64);
    assert_eq!(manifest.layout.pointer_size_bytes, 8);
    assert_eq!(manifest.layout.pointer_alignment_bytes, 8);
    assert_eq!(
        manifest.layout.wrapper_identity.as_deref(),
        Some("ay::sat::WatchBcpKernel::lp64:v1")
    );

    let context = record_by_name(&manifest, AY_SAT_BCP_CONTEXT_RECORD);
    assert_eq!(context.size_bytes, AY_SAT_BCP_CONTEXT_SIZE_BYTES);
    assert_eq!(context.alignment_bytes, 8);
    assert!(
        context
            .fields
            .iter()
            .any(|field| field.name == "status" && field.offset_bytes == 160)
    );
    assert!(
        context
            .fields
            .iter()
            .any(|field| field.name == "context_generation" && field.offset_bytes == 128)
    );
    assert!(
        context
            .fields
            .iter()
            .any(|field| field.name == "expected_generation" && field.offset_bytes == 136)
    );
    assert!(
        context
            .fields
            .iter()
            .any(|field| field.name == "watch_generation" && field.offset_bytes == 144)
    );
    assert!(
        context
            .fields
            .iter()
            .any(|field| field.name == "assignment_generation" && field.offset_bytes == 152)
    );

    let result = record_by_name(&manifest, AY_SAT_BCP_RESULT_RECORD);
    assert_eq!(result.size_bytes, AY_SAT_BCP_RESULT_SIZE_BYTES);
    assert_eq!(result.alignment_bytes, 8);
    assert!(
        result
            .fields
            .iter()
            .any(|field| field.name == "status" && field.offset_bytes == 0)
    );
    assert!(
        result
            .fields
            .iter()
            .any(|field| field.name == "generation" && field.offset_bytes == 40)
    );

    let propagation_context = slice_by_name(&manifest, "propagation_context");
    assert_eq!(propagation_context.length, Some(1));
    assert_eq!(
        propagation_context.element_size_bytes,
        AY_SAT_BCP_CONTEXT_SIZE_BYTES
    );
    assert_eq!(propagation_context.mutability, Mutability::Mutable);
    assert_eq!(propagation_context.alias_policy, AliasPolicy::Exclusive);

    let clause_arena = slice_by_name(&manifest, "clause_arena");
    assert_eq!(clause_arena.element_size_bytes, 4);
    assert_eq!(
        clause_arena.bounds,
        PointerBounds::Symbol("clause_arena_len".to_owned())
    );
    assert_eq!(clause_arena.mutability, Mutability::Immutable);
    assert_eq!(clause_arena.alias_policy, AliasPolicy::SharedReadOnly);

    let watch_heads = slice_by_name(&manifest, "watch_heads");
    assert_eq!(watch_heads.element_size_bytes, 4);
    assert_eq!(
        watch_heads.bounds,
        PointerBounds::Symbol("watch_head_count".to_owned())
    );
    assert_eq!(watch_heads.mutability, Mutability::Mutable);
    assert_eq!(watch_heads.alias_policy, AliasPolicy::Exclusive);

    let watch_entries = slice_by_name(&manifest, "watch_entries");
    assert_eq!(
        watch_entries.element_size_bytes,
        AY_SAT_BCP_WATCH_ENTRY_SIZE_BYTES
    );
    assert_eq!(
        watch_entries.stride_bytes,
        AY_SAT_BCP_WATCH_ENTRY_STRIDE_BYTES
    );
    assert_eq!(
        watch_entries.bounds,
        PointerBounds::Symbol("watch_entry_count".to_owned())
    );
    assert_eq!(watch_entries.mutability, Mutability::Mutable);
    assert_eq!(watch_entries.alias_policy, AliasPolicy::Exclusive);

    let assignment = slice_by_name(&manifest, "assignment");
    assert_eq!(assignment.element_size_bytes, 1);
    assert_eq!(
        assignment.bounds,
        PointerBounds::Symbol("assignment_len".to_owned())
    );
    assert_eq!(assignment.mutability, Mutability::Mutable);
    assert_eq!(assignment.alias_policy, AliasPolicy::Exclusive);

    let trail = slice_by_name(&manifest, "trail");
    assert_eq!(trail.element_size_bytes, 4);
    assert_eq!(trail.bounds, PointerBounds::Symbol("trail_len".to_owned()));
    assert_eq!(trail.mutability, Mutability::Mutable);
    assert_eq!(trail.alias_policy, AliasPolicy::Exclusive);

    let pending_queue = slice_by_name(&manifest, "pending_queue");
    assert_eq!(pending_queue.element_size_bytes, 4);
    assert_eq!(
        pending_queue.bounds,
        PointerBounds::Symbol("pending_queue_capacity".to_owned())
    );
    assert_eq!(pending_queue.mutability, Mutability::Mutable);
    assert_eq!(pending_queue.alias_policy, AliasPolicy::Exclusive);

    let result_slice = slice_by_name(&manifest, "result");
    assert_eq!(result_slice.length, Some(1));
    assert_eq!(
        result_slice.element_size_bytes,
        AY_SAT_BCP_RESULT_SIZE_BYTES
    );
    assert_eq!(result_slice.mutability, Mutability::Mutable);
    assert_eq!(result_slice.alias_policy, AliasPolicy::Exclusive);

    let generation_facts = slice_by_name(&manifest, "generation_facts");
    assert_eq!(generation_facts.element_size_bytes, 8);
    assert_eq!(
        generation_facts.bounds,
        PointerBounds::Symbol("generation_fact_count".to_owned())
    );
    assert_eq!(generation_facts.mutability, Mutability::Immutable);
    assert_eq!(generation_facts.alias_policy, AliasPolicy::SharedReadOnly);

    assert_eq!(
        manifest
            .layout
            .metadata
            .get("generation_policy")
            .map(String::as_str),
        Some("fail_closed_epoch_match")
    );
    assert_eq!(
        manifest.metadata.get("context_abi").map(String::as_str),
        Some("ay_sat_propagation_context_abi_v1")
    );
    assert_eq!(
        manifest.metadata.get("status_abi").map(String::as_str),
        Some("ay_sat_bcp_result_abi_v1")
    );
    assert_eq!(
        manifest.invalidation.target_checksum,
        manifest.target.checksum()
    );
    assert_eq!(manifest.invalidation.abi_checksum, manifest.abi.checksum());
    assert_eq!(
        manifest.invalidation.layout_checksum,
        manifest.layout.checksum()
    );
    assert_eq!(
        manifest.invalidation.proof_policy_checksum,
        manifest.proof_policy.checksum()
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("generation_policy")
            .map(String::as_str),
        Some("fail_closed_epoch_match")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("watch_layout")
            .map(String::as_str),
        Some("two_watched_literals_v1")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("context_generation")
            .map(String::as_str),
        Some("runtime")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("expected_generation")
            .map(String::as_str),
        Some("runtime")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("watch_generation")
            .map(String::as_str),
        Some("runtime")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("assignment_generation")
            .map(String::as_str),
        Some("runtime")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("generation_facts")
            .map(String::as_str),
        Some("runtime_readonly")
    );
}

#[test]
fn ay_sat_bcp_manifest_checksum_tracks_typed_bcp_proof_fact_metadata() {
    let manifest = ay_sat_watch_bcp_manifest();
    let baseline_checksum = manifest.checksum();
    let proof_evidence = ay_sat_watch_bcp_verified_proof_evidence("trust-cg-verify", &manifest);
    let baseline_evidence_checksum = proof_evidence.checksum();

    assert_bcp_proof_fact_metadata(&manifest.metadata);
    assert_bcp_proof_fact_metadata(&proof_evidence.metadata);

    let mut missing_pending_fact = manifest.clone();
    missing_pending_fact
        .metadata
        .remove(&AYSatBcpProofFact::PendingQueueBounds.metadata_key());
    assert_ne!(missing_pending_fact.checksum(), baseline_checksum);

    let mut tampered_generation_fact = manifest.clone();
    tampered_generation_fact.metadata.insert(
        AYSatBcpProofFact::GenerationMatch.metadata_key(),
        "ay_sat_bcp.generation_match.spoofed".to_owned(),
    );
    assert_ne!(tampered_generation_fact.checksum(), baseline_checksum);

    let mut missing_evidence_fact = proof_evidence.clone();
    missing_evidence_fact
        .metadata
        .remove(&AYSatBcpProofFact::PendingQueueBounds.metadata_key());
    assert_ne!(missing_evidence_fact.checksum(), baseline_evidence_checksum);

    let mut tampered_evidence_fact = proof_evidence;
    tampered_evidence_fact.metadata.insert(
        AYSatBcpProofFact::GenerationMatch.metadata_key(),
        "ay_sat_bcp.generation_match.spoofed".to_owned(),
    );
    assert_ne!(
        tampered_evidence_fact.checksum(),
        baseline_evidence_checksum
    );
}

#[test]
fn ay_sat_bcp_manifest_for_parts_text_section_follows_layout_symbol_size() {
    let layout_symbol_text_size = AY_SAT_BCP_TEXT_SIZE_BYTES + 64;
    let stale_section_text_size = AY_SAT_BCP_TEXT_SIZE_BYTES;
    let layout = ay_sat_watch_bcp_layout_with_text_size(16, layout_symbol_text_size);
    let manifest = ay_sat_watch_bcp_manifest_for_parts(
        ay_sat_watch_bcp_aarch64_target(),
        ay_sat_watch_bcp_aarch64_abi(),
        layout,
        ay_sat_watch_bcp_proof_policy(),
        99,
        stale_section_text_size,
    );

    let layout_symbol = manifest
        .layout
        .symbols
        .iter()
        .find(|symbol| symbol.name == AY_SAT_BCP_SYMBOL && symbol.section == ".text")
        .expect("SAT BCP layout binds the .text status probe symbol");
    let text_section = manifest
        .sections
        .iter()
        .find(|section| section.name == ".text")
        .expect("SAT BCP manifest binds a .text section");

    assert_eq!(layout_symbol.size_bytes, layout_symbol_text_size);
    assert_eq!(text_section.size_bytes, layout_symbol.size_bytes);
    assert_ne!(text_section.size_bytes, stale_section_text_size);
}

#[test]
fn ay_sat_bcp_manifest_checksum_tracks_watch_layout_changes() {
    let manifest = ay_sat_watch_bcp_manifest();
    let baseline_checksum = manifest.checksum();
    let expected_signature = ay_sat_watch_bcp_signature();

    let mut watch_stride_changed = manifest.clone();
    let watch_entries = watch_stride_changed
        .layout
        .slices
        .iter_mut()
        .find(|slice| slice.name == "watch_entries")
        .expect("SAT BCP manifest binds watch entry layout");
    watch_entries.element_size_bytes = 24;
    watch_entries.stride_bytes = 24;
    assert_eq!(watch_stride_changed.invalidation, manifest.invalidation);
    assert_ne!(
        watch_stride_changed.layout.checksum(),
        manifest.layout.checksum()
    );
    assert_ne!(watch_stride_changed.checksum(), baseline_checksum);

    let mut watch_heads_changed = manifest.clone();
    let watch_heads = watch_heads_changed
        .layout
        .slices
        .iter_mut()
        .find(|slice| slice.name == "watch_heads")
        .expect("SAT BCP manifest binds watch head layout");
    watch_heads.mutability = Mutability::Immutable;
    watch_heads.alias_policy = AliasPolicy::SharedReadOnly;
    watch_heads_changed.invalidation.layout_checksum = watch_heads_changed.layout.checksum();
    assert_ne!(
        watch_heads_changed.layout.checksum(),
        manifest.layout.checksum()
    );
    assert_ne!(
        watch_heads_changed.invalidation.checksum(),
        manifest.invalidation.checksum()
    );
    assert_ne!(watch_heads_changed.checksum(), baseline_checksum);

    let mut generation_changed = manifest.clone();
    generation_changed.invalidation.generation += 1;
    assert_eq!(generation_changed.layout, manifest.layout);
    assert_ne!(
        generation_changed.invalidation.checksum(),
        manifest.invalidation.checksum()
    );
    assert_ne!(generation_changed.checksum(), baseline_checksum);

    let mut status_signature_changed = manifest.clone();
    status_signature_changed.symbols[0].signature = nullable_context_pointer_signature();
    assert_eq!(status_signature_changed.layout, manifest.layout);
    assert_eq!(status_signature_changed.invalidation, manifest.invalidation);
    assert_ne!(
        status_signature_changed.symbols[0].signature.checksum(),
        expected_signature.checksum()
    );
    assert_ne!(status_signature_changed.checksum(), baseline_checksum);
}
