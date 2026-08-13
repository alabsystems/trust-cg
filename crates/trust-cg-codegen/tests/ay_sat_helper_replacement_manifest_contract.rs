// trust-cg-codegen/tests/ay_sat_helper_replacement_manifest_contract.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeMap;

use trust_cg_codegen::ay_sat_helper_replacement_contract::{
    AY_SAT_CONTAINS4_MASKED_ARGS_ABI, AY_SAT_CONTAINS4_MASKED_ARGS_RECORD,
    AY_SAT_CONTAINS4_MASKED_ARGS_SIZE_BYTES, AY_SAT_CONTAINS4_MASKED_DEFAULT_GENERATION,
    AY_SAT_CONTAINS4_MASKED_REFERENCE_ORACLE, AY_SAT_CONTAINS4_MASKED_RESULT_ABI,
    AY_SAT_CONTAINS4_MASKED_RESULT_RECORD, AY_SAT_CONTAINS4_MASKED_RESULT_SIZE_BYTES,
    AY_SAT_CONTAINS4_MASKED_SYMBOL, AY_SAT_CONTAINS4_MASKED_TEXT_SIZE_BYTES,
    AY_SAT_CONTAINS4_MASKED_WRAPPER_IDENTITY, AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA,
    AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA_VERSION, AY_SAT_HELPER_REPLACEMENT_KERNEL,
    AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_REQUIREMENTS, AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA,
    AY_SAT_MINIMIZE_CLASSIFY_CHECK, AY_SAT_MINIMIZE_CLASSIFY_DROP, AY_SAT_MINIMIZE_CLASSIFY_KEEP,
    AY_SAT_MINIMIZE_KEEP_DROP_ARGS_ABI, AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD,
    AY_SAT_MINIMIZE_KEEP_DROP_ARGS_SIZE_BYTES, AY_SAT_MINIMIZE_KEEP_DROP_DEFAULT_GENERATION,
    AY_SAT_MINIMIZE_KEEP_DROP_KERNEL, AY_SAT_MINIMIZE_KEEP_DROP_PROOF_FACT_REQUIREMENTS,
    AY_SAT_MINIMIZE_KEEP_DROP_REFERENCE_ORACLE, AY_SAT_MINIMIZE_KEEP_DROP_RESULT_ABI,
    AY_SAT_MINIMIZE_KEEP_DROP_RESULT_RECORD, AY_SAT_MINIMIZE_KEEP_DROP_RESULT_SIZE_BYTES,
    AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL, AY_SAT_MINIMIZE_KEEP_DROP_TEXT_SIZE_BYTES,
    AY_SAT_MINIMIZE_KEEP_DROP_WRAPPER_IDENTITY, AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_ABI,
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_RECORD,
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_SIZE_BYTES,
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_DEFAULT_GENERATION,
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_PROOF_FACT_REQUIREMENTS,
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_REFERENCE_ORACLE,
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_ABI, AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_RECORD,
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_SIZE_BYTES, AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL,
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_TEXT_SIZE_BYTES,
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_WRAPPER_IDENTITY, AY_SAT_THEORY_DISPATCH_FLAG_COND_ASSIGNED,
    AY_SAT_THEORY_DISPATCH_FLAG_COND_VALUE, AY_SAT_THEORY_DISPATCH_FLAG_ITE_GUARDED,
    AY_SAT_THEORY_DISPATCH_FLAG_THEN_BRANCH, AY_SAT_THEORY_DISPATCH_NO_ITE_COND_VAR,
    AY_SAT_THEORY_DISPATCH_RESULT_STATUS_MASK, AY_SAT_THEORY_DISPATCH_RESULT_TERM_SHIFT,
    AY_SAT_THEORY_DISPATCH_RESULT_VALUE_BIT, AY_SAT_THEORY_DISPATCH_STATUS_ASSERT,
    AY_SAT_THEORY_DISPATCH_STATUS_DEFER_ITE, AY_SAT_THEORY_DISPATCH_STATUS_SKIP,
    AYSatHelperReplacementProofFact, AYSatMinimizeKeepDropProofFact, AYSatTheoryDispatchProofFact,
    ay_sat_contains4_masked_aarch64_abi, ay_sat_contains4_masked_aarch64_target,
    ay_sat_contains4_masked_layout_with_text_size, ay_sat_contains4_masked_manifest,
    ay_sat_contains4_masked_manifest_for_parts, ay_sat_contains4_masked_proof_policy,
    ay_sat_contains4_masked_signature, ay_sat_contains4_masked_symbol_lookup_contract,
    ay_sat_contains4_masked_verified_proof_evidence,
    ay_sat_helper_replacement_proof_fact_metadata_matches,
    ay_sat_helper_replacement_required_fact_csv, ay_sat_minimize_keep_drop_aarch64_abi,
    ay_sat_minimize_keep_drop_aarch64_target, ay_sat_minimize_keep_drop_layout_with_text_size,
    ay_sat_minimize_keep_drop_manifest, ay_sat_minimize_keep_drop_manifest_for_parts,
    ay_sat_minimize_keep_drop_proof_fact_metadata_matches, ay_sat_minimize_keep_drop_proof_policy,
    ay_sat_minimize_keep_drop_required_fact_csv, ay_sat_minimize_keep_drop_signature,
    ay_sat_minimize_keep_drop_symbol_lookup_contract,
    ay_sat_minimize_keep_drop_verified_proof_evidence,
    ay_sat_theory_dispatch_assignment_aarch64_abi,
    ay_sat_theory_dispatch_assignment_aarch64_target,
    ay_sat_theory_dispatch_assignment_layout_with_text_size,
    ay_sat_theory_dispatch_assignment_manifest,
    ay_sat_theory_dispatch_assignment_manifest_for_parts,
    ay_sat_theory_dispatch_assignment_proof_fact_metadata_matches,
    ay_sat_theory_dispatch_assignment_proof_policy,
    ay_sat_theory_dispatch_assignment_required_fact_csv,
    ay_sat_theory_dispatch_assignment_signature,
    ay_sat_theory_dispatch_assignment_symbol_lookup_contract,
    ay_sat_theory_dispatch_assignment_verified_proof_evidence,
};
use trust_cg_codegen::jit_contract::{
    AbiValue, AbiValueKind, DeterministicArtifactManifest, FieldLayout, ProofPolicy,
};

#[repr(C)]
struct AYSatContains4MaskedArgsAbi {
    lane0: i32,
    lane1: i32,
    lane2: i32,
    lane3: i32,
    literal: i32,
    valid_mask: i32,
}

#[repr(C)]
struct AYSatContains4MaskedResultAbi {
    match_mask: i32,
}

type AYSatContains4MaskedFn = unsafe extern "C" fn(i32, i32, i32, i32, i32, i32) -> i32;

#[repr(C)]
struct AYSatMinimizeKeepDropArgsAbi {
    var_level: i32,
    trail_pos: i32,
    reason: i32,
    min_flags: i32,
    level_seen_count: i32,
    level_seen_trail: i32,
    decision_level: i32,
}

#[repr(C)]
struct AYSatMinimizeKeepDropResultAbi {
    classification: i32,
}

type AYSatMinimizeKeepDropFn = unsafe extern "C" fn(i32, i32, i32, i32, i32, i32, i32) -> i32;

#[repr(C)]
struct AYSatTheoryDispatchAssignmentArgsAbi {
    var_id: i32,
    table_len: i32,
    entry_present: i32,
    term_id: i32,
    assignment_value: i32,
    guard_flags: i32,
    decision_level: i32,
}

#[repr(C)]
struct AYSatTheoryDispatchAssignmentResultAbi {
    packed_result: i64,
}

type AYSatTheoryDispatchAssignmentFn =
    unsafe extern "C" fn(i32, i32, i32, i32, i32, i32, i32) -> i64;

fn assert_helper_proof_fact_metadata(metadata: &BTreeMap<String, String>) {
    let required_facts = ay_sat_helper_replacement_required_fact_csv();
    assert_eq!(
        metadata.get("proof_fact_schema").map(String::as_str),
        Some(AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA)
    );
    assert_eq!(
        metadata.get("required_proof_facts").map(String::as_str),
        Some(required_facts.as_str())
    );
    for requirement in AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_REQUIREMENTS {
        assert_eq!(
            metadata
                .get(&requirement.fact.metadata_key())
                .map(String::as_str),
            Some(requirement.lemma_id),
            "missing typed SAT helper proof fact metadata for {}",
            requirement.fact.as_str()
        );
    }
    assert!(ay_sat_helper_replacement_proof_fact_metadata_matches(
        metadata
    ));
}

fn assert_minimize_proof_fact_metadata(metadata: &BTreeMap<String, String>) {
    let required_facts = ay_sat_minimize_keep_drop_required_fact_csv();
    assert_eq!(
        metadata.get("proof_fact_schema").map(String::as_str),
        Some(AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA)
    );
    assert_eq!(
        metadata.get("required_proof_facts").map(String::as_str),
        Some(required_facts.as_str())
    );
    for requirement in AY_SAT_MINIMIZE_KEEP_DROP_PROOF_FACT_REQUIREMENTS {
        assert_eq!(
            metadata
                .get(&requirement.fact.metadata_key())
                .map(String::as_str),
            Some(requirement.lemma_id),
            "missing typed SAT minimization helper proof fact metadata for {}",
            requirement.fact.as_str()
        );
    }
    assert!(ay_sat_minimize_keep_drop_proof_fact_metadata_matches(
        metadata
    ));
}

fn assert_theory_dispatch_proof_fact_metadata(metadata: &BTreeMap<String, String>) {
    let required_facts = ay_sat_theory_dispatch_assignment_required_fact_csv();
    assert_eq!(
        metadata.get("proof_fact_schema").map(String::as_str),
        Some(AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA)
    );
    assert_eq!(
        metadata.get("required_proof_facts").map(String::as_str),
        Some(required_facts.as_str())
    );
    for requirement in AY_SAT_THEORY_DISPATCH_ASSIGNMENT_PROOF_FACT_REQUIREMENTS {
        assert_eq!(
            metadata
                .get(&requirement.fact.metadata_key())
                .map(String::as_str),
            Some(requirement.lemma_id),
            "missing typed SAT theory-dispatch proof fact metadata for {}",
            requirement.fact.as_str()
        );
    }
    assert!(ay_sat_theory_dispatch_assignment_proof_fact_metadata_matches(metadata));
}

fn record_field<'a>(
    manifest: &'a DeterministicArtifactManifest,
    record_name: &str,
    field_name: &str,
) -> &'a FieldLayout {
    manifest
        .layout
        .records
        .iter()
        .find(|record| record.name == record_name)
        .unwrap_or_else(|| panic!("SAT helper manifest binds {record_name} record"))
        .fields
        .iter()
        .find(|field| field.name == field_name)
        .unwrap_or_else(|| panic!("SAT helper {record_name} record binds {field_name}"))
}

#[test]
fn ay_sat_helper_manifest_binds_contains4_signature_layout_and_proof_facts() {
    let manifest = ay_sat_contains4_masked_manifest();
    let expected_signature = ay_sat_contains4_masked_signature();
    let baseline_checksum = manifest.checksum();
    let proof_evidence =
        ay_sat_contains4_masked_verified_proof_evidence("trust-cg-verify", &manifest);
    let install_contract =
        ay_sat_contains4_masked_symbol_lookup_contract(&manifest, proof_evidence.clone());

    assert_eq!(
        std::mem::size_of::<AYSatContains4MaskedFn>(),
        std::mem::size_of::<*const u8>()
    );
    assert_eq!(
        manifest.symbol_signature(AY_SAT_CONTAINS4_MASKED_SYMBOL),
        Some(&expected_signature)
    );
    assert_eq!(
        expected_signature.params,
        vec![
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
        ]
    );
    assert_eq!(
        expected_signature.returns,
        vec![AbiValue::new(AbiValueKind::I32)]
    );
    assert_eq!(install_contract.symbol, AY_SAT_CONTAINS4_MASKED_SYMBOL);
    assert_eq!(install_contract.signature, expected_signature);
    assert_eq!(install_contract.target_checksum, manifest.target.checksum());
    assert_eq!(install_contract.abi_checksum, manifest.abi.checksum());
    assert_eq!(install_contract.layout_checksum, manifest.layout.checksum());
    assert_eq!(
        install_contract.invalidation_checksum,
        Some(manifest.invalidation.checksum())
    );
    assert_eq!(install_contract.manifest_checksum, Some(baseline_checksum));
    assert_eq!(
        install_contract.proof_evidence,
        Some(proof_evidence.clone())
    );
    manifest
        .validate_symbol_lookup(&install_contract)
        .expect("manifest satisfies the typed SAT helper symbol lookup contract");

    assert_eq!(
        std::mem::size_of::<AYSatContains4MaskedArgsAbi>(),
        AY_SAT_CONTAINS4_MASKED_ARGS_SIZE_BYTES as usize
    );
    assert_eq!(
        std::mem::size_of::<AYSatContains4MaskedResultAbi>(),
        AY_SAT_CONTAINS4_MASKED_RESULT_SIZE_BYTES as usize
    );
    assert_eq!(manifest.target.pointer_width_bits, 64);
    assert_eq!(manifest.abi.pointer_width_bits, 64);
    assert_eq!(manifest.layout.pointer_size_bytes, 8);
    assert_eq!(manifest.layout.pointer_alignment_bytes, 8);
    assert_eq!(
        manifest.layout.wrapper_identity.as_deref(),
        Some(AY_SAT_CONTAINS4_MASKED_WRAPPER_IDENTITY)
    );

    let args_record = manifest
        .layout
        .records
        .iter()
        .find(|record| record.name == AY_SAT_CONTAINS4_MASKED_ARGS_RECORD)
        .expect("SAT helper manifest binds args record");
    assert_eq!(args_record.representation, "repr(C)");
    assert_eq!(
        args_record.size_bytes,
        AY_SAT_CONTAINS4_MASKED_ARGS_SIZE_BYTES
    );
    assert_eq!(args_record.alignment_bytes, 4);
    assert_eq!(
        record_field(&manifest, AY_SAT_CONTAINS4_MASKED_ARGS_RECORD, "lane0").offset_bytes,
        0
    );
    assert_eq!(
        record_field(&manifest, AY_SAT_CONTAINS4_MASKED_ARGS_RECORD, "lane1").offset_bytes,
        4
    );
    assert_eq!(
        record_field(&manifest, AY_SAT_CONTAINS4_MASKED_ARGS_RECORD, "lane2").offset_bytes,
        8
    );
    assert_eq!(
        record_field(&manifest, AY_SAT_CONTAINS4_MASKED_ARGS_RECORD, "lane3").offset_bytes,
        12
    );
    assert_eq!(
        record_field(&manifest, AY_SAT_CONTAINS4_MASKED_ARGS_RECORD, "literal").offset_bytes,
        16
    );
    assert_eq!(
        record_field(&manifest, AY_SAT_CONTAINS4_MASKED_ARGS_RECORD, "valid_mask").offset_bytes,
        20
    );

    let result_record = manifest
        .layout
        .records
        .iter()
        .find(|record| record.name == AY_SAT_CONTAINS4_MASKED_RESULT_RECORD)
        .expect("SAT helper manifest binds result record");
    assert_eq!(result_record.representation, "repr(C)");
    assert_eq!(
        result_record.size_bytes,
        AY_SAT_CONTAINS4_MASKED_RESULT_SIZE_BYTES
    );
    assert_eq!(result_record.alignment_bytes, 4);
    assert_eq!(
        record_field(
            &manifest,
            AY_SAT_CONTAINS4_MASKED_RESULT_RECORD,
            "match_mask"
        )
        .offset_bytes,
        0
    );

    assert_eq!(
        manifest.layout.symbols[0].name,
        AY_SAT_CONTAINS4_MASKED_SYMBOL
    );
    assert_eq!(
        manifest.layout.symbols[0].size_bytes,
        AY_SAT_CONTAINS4_MASKED_TEXT_SIZE_BYTES
    );
    assert_eq!(manifest.sections[0].name, ".text");
    assert_eq!(
        manifest.sections[0].size_bytes,
        AY_SAT_CONTAINS4_MASKED_TEXT_SIZE_BYTES
    );
    assert_eq!(
        manifest.layout.metadata.get("kernel").map(String::as_str),
        Some(AY_SAT_HELPER_REPLACEMENT_KERNEL)
    );
    assert_eq!(
        manifest.layout.metadata.get("args_abi").map(String::as_str),
        Some(AY_SAT_CONTAINS4_MASKED_ARGS_ABI)
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("result_abi")
            .map(String::as_str),
        Some(AY_SAT_CONTAINS4_MASKED_RESULT_ABI)
    );
    assert_eq!(
        manifest
            .metadata
            .get("artifact_contract_schema")
            .map(String::as_str),
        Some(AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA)
    );
    assert_eq!(
        manifest
            .metadata
            .get("artifact_contract_schema_version")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA_VERSION,
        1
    );
    assert_eq!(
        manifest.metadata.get("native_install").map(String::as_str),
        Some("helper_callable_gate_only")
    );
    assert_eq!(
        manifest.metadata.get("useful_native").map(String::as_str),
        Some("0")
    );
    assert_eq!(
        manifest
            .metadata
            .get("promotion_disposition")
            .map(String::as_str),
        Some("non_promoting_manifest_backed_helper_replacement")
    );
    assert_eq!(
        manifest
            .metadata
            .get("reference_oracle")
            .map(String::as_str),
        Some(AY_SAT_CONTAINS4_MASKED_REFERENCE_ORACLE)
    );
    assert_eq!(
        manifest.invalidation.generation,
        AY_SAT_CONTAINS4_MASKED_DEFAULT_GENERATION
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
            .get("helper_semantics")
            .map(String::as_str),
        Some("contains4_masked_i32_lane_mask")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("contains_literal_fold")
            .map(String::as_str),
        Some("or_nonzero_chunk_masks")
    );
    assert_helper_proof_fact_metadata(&manifest.layout.metadata);
    assert_helper_proof_fact_metadata(&manifest.metadata);
    assert_helper_proof_fact_metadata(&proof_evidence.metadata);
}

#[test]
fn ay_sat_helper_manifest_binds_minimize_keep_drop_signature_layout_and_proof_facts() {
    let manifest = ay_sat_minimize_keep_drop_manifest();
    let expected_signature = ay_sat_minimize_keep_drop_signature();
    let baseline_checksum = manifest.checksum();
    let proof_evidence =
        ay_sat_minimize_keep_drop_verified_proof_evidence("trust-cg-verify", &manifest);
    let install_contract =
        ay_sat_minimize_keep_drop_symbol_lookup_contract(&manifest, proof_evidence.clone());

    assert_eq!(
        std::mem::size_of::<AYSatMinimizeKeepDropFn>(),
        std::mem::size_of::<*const u8>()
    );
    assert_eq!(
        manifest.symbol_signature(AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL),
        Some(&expected_signature)
    );
    assert_eq!(
        expected_signature.params,
        vec![
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
        ]
    );
    assert_eq!(
        expected_signature.returns,
        vec![AbiValue::new(AbiValueKind::I32)]
    );
    assert_eq!(install_contract.symbol, AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL);
    assert_eq!(install_contract.signature, expected_signature);
    assert_eq!(install_contract.target_checksum, manifest.target.checksum());
    assert_eq!(install_contract.abi_checksum, manifest.abi.checksum());
    assert_eq!(install_contract.layout_checksum, manifest.layout.checksum());
    assert_eq!(
        install_contract.invalidation_checksum,
        Some(manifest.invalidation.checksum())
    );
    assert_eq!(install_contract.manifest_checksum, Some(baseline_checksum));
    assert_eq!(
        install_contract.proof_evidence,
        Some(proof_evidence.clone())
    );
    manifest
        .validate_symbol_lookup(&install_contract)
        .expect("manifest satisfies the typed SAT minimization symbol lookup contract");

    assert_eq!(
        std::mem::size_of::<AYSatMinimizeKeepDropArgsAbi>(),
        AY_SAT_MINIMIZE_KEEP_DROP_ARGS_SIZE_BYTES as usize
    );
    assert_eq!(
        std::mem::size_of::<AYSatMinimizeKeepDropResultAbi>(),
        AY_SAT_MINIMIZE_KEEP_DROP_RESULT_SIZE_BYTES as usize
    );
    assert_eq!(
        manifest.layout.wrapper_identity.as_deref(),
        Some(AY_SAT_MINIMIZE_KEEP_DROP_WRAPPER_IDENTITY)
    );

    let args_record = manifest
        .layout
        .records
        .iter()
        .find(|record| record.name == AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD)
        .expect("SAT minimization manifest binds args record");
    assert_eq!(args_record.representation, "repr(C)");
    assert_eq!(
        args_record.size_bytes,
        AY_SAT_MINIMIZE_KEEP_DROP_ARGS_SIZE_BYTES
    );
    assert_eq!(args_record.alignment_bytes, 4);
    assert_eq!(
        record_field(
            &manifest,
            AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD,
            "var_level"
        )
        .offset_bytes,
        0
    );
    assert_eq!(
        record_field(
            &manifest,
            AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD,
            "trail_pos"
        )
        .offset_bytes,
        4
    );
    assert_eq!(
        record_field(&manifest, AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD, "reason").offset_bytes,
        8
    );
    assert_eq!(
        record_field(
            &manifest,
            AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD,
            "min_flags"
        )
        .offset_bytes,
        12
    );
    assert_eq!(
        record_field(
            &manifest,
            AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD,
            "level_seen_count"
        )
        .offset_bytes,
        16
    );
    assert_eq!(
        record_field(
            &manifest,
            AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD,
            "level_seen_trail"
        )
        .offset_bytes,
        20
    );
    assert_eq!(
        record_field(
            &manifest,
            AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD,
            "decision_level"
        )
        .offset_bytes,
        24
    );

    let result_record = manifest
        .layout
        .records
        .iter()
        .find(|record| record.name == AY_SAT_MINIMIZE_KEEP_DROP_RESULT_RECORD)
        .expect("SAT minimization manifest binds result record");
    assert_eq!(result_record.representation, "repr(C)");
    assert_eq!(
        result_record.size_bytes,
        AY_SAT_MINIMIZE_KEEP_DROP_RESULT_SIZE_BYTES
    );
    assert_eq!(result_record.alignment_bytes, 4);
    assert_eq!(
        record_field(
            &manifest,
            AY_SAT_MINIMIZE_KEEP_DROP_RESULT_RECORD,
            "classification"
        )
        .offset_bytes,
        0
    );

    assert_eq!(
        manifest.layout.symbols[0].name,
        AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL
    );
    assert_eq!(
        manifest.layout.symbols[0].size_bytes,
        AY_SAT_MINIMIZE_KEEP_DROP_TEXT_SIZE_BYTES
    );
    assert_eq!(manifest.sections[0].name, ".text");
    assert_eq!(
        manifest.sections[0].size_bytes,
        AY_SAT_MINIMIZE_KEEP_DROP_TEXT_SIZE_BYTES
    );
    assert_eq!(
        manifest.layout.metadata.get("kernel").map(String::as_str),
        Some(AY_SAT_MINIMIZE_KEEP_DROP_KERNEL)
    );
    assert_eq!(
        manifest.layout.metadata.get("args_abi").map(String::as_str),
        Some(AY_SAT_MINIMIZE_KEEP_DROP_ARGS_ABI)
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("result_abi")
            .map(String::as_str),
        Some(AY_SAT_MINIMIZE_KEEP_DROP_RESULT_ABI)
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("classification_values")
            .map(String::as_str),
        Some("drop=0,keep=1,check=2")
    );
    assert_eq!(
        (
            AY_SAT_MINIMIZE_CLASSIFY_DROP,
            AY_SAT_MINIMIZE_CLASSIFY_KEEP,
            AY_SAT_MINIMIZE_CLASSIFY_CHECK,
        ),
        (0, 1, 2)
    );
    assert_eq!(
        manifest
            .metadata
            .get("artifact_contract_schema")
            .map(String::as_str),
        Some(AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA)
    );
    assert_eq!(
        manifest
            .metadata
            .get("artifact_contract_schema_version")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        manifest
            .metadata
            .get("reference_oracle")
            .map(String::as_str),
        Some(AY_SAT_MINIMIZE_KEEP_DROP_REFERENCE_ORACLE)
    );
    assert_eq!(
        manifest
            .metadata
            .get("promotion_disposition")
            .map(String::as_str),
        Some("non_promoting_manifest_backed_helper_replacement")
    );
    assert_eq!(
        manifest.invalidation.generation,
        AY_SAT_MINIMIZE_KEEP_DROP_DEFAULT_GENERATION
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("helper_semantics")
            .map(String::as_str),
        Some("minimize_keep_drop_literal_classification")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("cached_flag_bits")
            .map(String::as_str),
        Some("poison=0x01,removable=0x02,keep=0x08")
    );
    assert_minimize_proof_fact_metadata(&manifest.layout.metadata);
    assert_minimize_proof_fact_metadata(&manifest.metadata);
    assert_minimize_proof_fact_metadata(&proof_evidence.metadata);
}

#[test]
fn ay_sat_helper_manifest_binds_theory_dispatch_signature_layout_and_proof_facts() {
    let manifest = ay_sat_theory_dispatch_assignment_manifest();
    let expected_signature = ay_sat_theory_dispatch_assignment_signature();
    let baseline_checksum = manifest.checksum();
    let proof_evidence =
        ay_sat_theory_dispatch_assignment_verified_proof_evidence("trust-cg-verify", &manifest);
    let install_contract =
        ay_sat_theory_dispatch_assignment_symbol_lookup_contract(&manifest, proof_evidence.clone());

    assert_eq!(
        std::mem::size_of::<AYSatTheoryDispatchAssignmentFn>(),
        std::mem::size_of::<*const u8>()
    );
    assert_eq!(
        manifest.symbol_signature(AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL),
        Some(&expected_signature)
    );
    assert_eq!(
        expected_signature.params,
        vec![
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
        ]
    );
    assert_eq!(
        expected_signature.returns,
        vec![AbiValue::new(AbiValueKind::I64)]
    );
    assert_eq!(
        install_contract.symbol,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL
    );
    assert_eq!(install_contract.signature, expected_signature);
    assert_eq!(install_contract.target_checksum, manifest.target.checksum());
    assert_eq!(install_contract.abi_checksum, manifest.abi.checksum());
    assert_eq!(install_contract.layout_checksum, manifest.layout.checksum());
    assert_eq!(
        install_contract.invalidation_checksum,
        Some(manifest.invalidation.checksum())
    );
    assert_eq!(install_contract.manifest_checksum, Some(baseline_checksum));
    assert_eq!(
        install_contract.proof_evidence,
        Some(proof_evidence.clone())
    );
    manifest
        .validate_symbol_lookup(&install_contract)
        .expect("manifest satisfies the typed SAT theory-dispatch symbol lookup contract");

    assert_eq!(
        std::mem::size_of::<AYSatTheoryDispatchAssignmentArgsAbi>(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_SIZE_BYTES as usize
    );
    assert_eq!(
        std::mem::size_of::<AYSatTheoryDispatchAssignmentResultAbi>(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_SIZE_BYTES as usize
    );
    assert_eq!(
        manifest.layout.wrapper_identity.as_deref(),
        Some(AY_SAT_THEORY_DISPATCH_ASSIGNMENT_WRAPPER_IDENTITY)
    );

    let args_record = manifest
        .layout
        .records
        .iter()
        .find(|record| record.name == AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_RECORD)
        .expect("SAT theory-dispatch manifest binds args record");
    assert_eq!(args_record.representation, "repr(C)");
    assert_eq!(
        args_record.size_bytes,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_SIZE_BYTES
    );
    assert_eq!(args_record.alignment_bytes, 4);
    for (field_name, offset) in [
        ("var_id", 0),
        ("table_len", 4),
        ("entry_present", 8),
        ("term_id", 12),
        ("assignment_value", 16),
        ("guard_flags", 20),
        ("decision_level", 24),
    ] {
        assert_eq!(
            record_field(
                &manifest,
                AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_RECORD,
                field_name,
            )
            .offset_bytes,
            offset
        );
    }

    let result_record = manifest
        .layout
        .records
        .iter()
        .find(|record| record.name == AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_RECORD)
        .expect("SAT theory-dispatch manifest binds result record");
    assert_eq!(result_record.representation, "repr(C)");
    assert_eq!(
        result_record.size_bytes,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_SIZE_BYTES
    );
    assert_eq!(result_record.alignment_bytes, 8);
    assert_eq!(
        record_field(
            &manifest,
            AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_RECORD,
            "packed_result",
        )
        .offset_bytes,
        0
    );

    assert_eq!(
        manifest.layout.symbols[0].name,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL
    );
    assert_eq!(
        manifest.layout.symbols[0].size_bytes,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_TEXT_SIZE_BYTES
    );
    assert_eq!(manifest.sections[0].name, ".text");
    assert_eq!(
        manifest.sections[0].size_bytes,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_TEXT_SIZE_BYTES
    );
    assert_eq!(
        manifest.layout.metadata.get("args_abi").map(String::as_str),
        Some(AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_ABI)
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("result_abi")
            .map(String::as_str),
        Some(AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_ABI)
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("status_values")
            .map(String::as_str),
        Some("skip=0,assert=1,defer_ite=2")
    );
    assert_eq!(
        (
            AY_SAT_THEORY_DISPATCH_STATUS_SKIP,
            AY_SAT_THEORY_DISPATCH_STATUS_ASSERT,
            AY_SAT_THEORY_DISPATCH_STATUS_DEFER_ITE,
            AY_SAT_THEORY_DISPATCH_NO_ITE_COND_VAR,
        ),
        (0, 1, 2, -1)
    );
    assert_eq!(AY_SAT_THEORY_DISPATCH_RESULT_STATUS_MASK, 0x3);
    assert_eq!(AY_SAT_THEORY_DISPATCH_RESULT_VALUE_BIT, 1 << 2);
    assert_eq!(AY_SAT_THEORY_DISPATCH_RESULT_TERM_SHIFT, 32);
    assert_eq!(
        (
            AY_SAT_THEORY_DISPATCH_FLAG_ITE_GUARDED,
            AY_SAT_THEORY_DISPATCH_FLAG_THEN_BRANCH,
            AY_SAT_THEORY_DISPATCH_FLAG_COND_ASSIGNED,
            AY_SAT_THEORY_DISPATCH_FLAG_COND_VALUE,
        ),
        (0x01, 0x02, 0x04, 0x08)
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("guard_flags")
            .map(String::as_str),
        Some("ite_guarded=0x01,then_branch=0x02,cond_assigned=0x04,cond_value=0x08")
    );
    assert_eq!(
        manifest
            .metadata
            .get("artifact_contract_schema")
            .map(String::as_str),
        Some(AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA)
    );
    assert_eq!(
        manifest
            .metadata
            .get("reference_oracle")
            .map(String::as_str),
        Some(AY_SAT_THEORY_DISPATCH_ASSIGNMENT_REFERENCE_ORACLE)
    );
    assert_eq!(
        manifest
            .metadata
            .get("reference_provenance")
            .map(String::as_str),
        Some("local_private_reference_only")
    );
    assert_eq!(
        manifest
            .metadata
            .get("promotion_disposition")
            .map(String::as_str),
        Some("non_promoting_manifest_backed_helper_replacement")
    );
    assert_eq!(
        manifest
            .metadata
            .get("product_promotion_scope")
            .map(String::as_str),
        Some("does_not_unblock_665_product_promotion_or_public_ay_repin")
    );
    assert!(!manifest.proof_policy.requires_evidence());
    assert!(
        install_contract.require_proof_evidence,
        "typed theory-dispatch symbol exposure remains proof-evidence gated"
    );
    assert_eq!(
        manifest.invalidation.generation,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_DEFAULT_GENERATION
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("helper_semantics")
            .map(String::as_str),
        Some("theory_dispatch_lookup_assignment")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("ite_relevancy")
            .map(String::as_str),
        Some("defer_assigned_inactive_branch_only_when_decision_level_gt_zero")
    );
    assert_theory_dispatch_proof_fact_metadata(&manifest.layout.metadata);
    assert_theory_dispatch_proof_fact_metadata(&manifest.metadata);
    assert_theory_dispatch_proof_fact_metadata(&proof_evidence.metadata);
}

#[test]
fn ay_sat_helper_manifest_checksum_tracks_abi_policy_and_proof_fact_changes() {
    let manifest = ay_sat_contains4_masked_manifest();
    let baseline_checksum = manifest.checksum();
    let expected_signature = ay_sat_contains4_masked_signature();
    let proof_evidence =
        ay_sat_contains4_masked_verified_proof_evidence("trust-cg-verify", &manifest);
    let baseline_evidence_checksum = proof_evidence.checksum();

    let mut args_record_changed = manifest.clone();
    let valid_mask = args_record_changed.layout.records[0]
        .fields
        .iter_mut()
        .find(|field| field.name == "valid_mask")
        .expect("SAT helper args record binds valid_mask");
    valid_mask.offset_bytes = 24;
    assert_eq!(args_record_changed.invalidation, manifest.invalidation);
    assert_ne!(
        args_record_changed.layout.checksum(),
        manifest.layout.checksum()
    );
    assert_ne!(args_record_changed.checksum(), baseline_checksum);

    let mut generation_changed = manifest.clone();
    generation_changed.invalidation.generation += 1;
    assert_eq!(generation_changed.layout, manifest.layout);
    assert_ne!(
        generation_changed.invalidation.checksum(),
        manifest.invalidation.checksum()
    );
    assert_ne!(generation_changed.checksum(), baseline_checksum);

    let mut signature_changed = manifest.clone();
    signature_changed.symbols[0].signature.params[5] = AbiValue::new(AbiValueKind::I64);
    assert_eq!(signature_changed.layout, manifest.layout);
    assert_eq!(signature_changed.invalidation, manifest.invalidation);
    assert_ne!(
        signature_changed.symbols[0].signature.checksum(),
        expected_signature.checksum()
    );
    assert_ne!(signature_changed.checksum(), baseline_checksum);

    let mut missing_proof_fact = manifest.clone();
    missing_proof_fact
        .metadata
        .remove(&AYSatHelperReplacementProofFact::ValidMaskLaneBounds.metadata_key());
    assert_ne!(missing_proof_fact.checksum(), baseline_checksum);

    let mut tampered_evidence_fact = proof_evidence;
    tampered_evidence_fact.metadata.insert(
        AYSatHelperReplacementProofFact::ContainsLiteralChunkFold.metadata_key(),
        "ay_sat_helper.contains_literal_chunk_or_fold.spoofed".to_owned(),
    );
    assert_ne!(
        tampered_evidence_fact.checksum(),
        baseline_evidence_checksum
    );
}

#[test]
fn ay_sat_helper_minimize_manifest_checksum_tracks_abi_and_proof_fact_changes() {
    let manifest = ay_sat_minimize_keep_drop_manifest();
    let baseline_checksum = manifest.checksum();
    let expected_signature = ay_sat_minimize_keep_drop_signature();
    let proof_evidence =
        ay_sat_minimize_keep_drop_verified_proof_evidence("trust-cg-verify", &manifest);
    let baseline_evidence_checksum = proof_evidence.checksum();

    let mut args_record_changed = manifest.clone();
    let min_flags = args_record_changed.layout.records[0]
        .fields
        .iter_mut()
        .find(|field| field.name == "min_flags")
        .expect("SAT minimization args record binds min_flags");
    min_flags.offset_bytes = 16;
    assert_eq!(args_record_changed.invalidation, manifest.invalidation);
    assert_ne!(
        args_record_changed.layout.checksum(),
        manifest.layout.checksum()
    );
    assert_ne!(args_record_changed.checksum(), baseline_checksum);

    let mut signature_changed = manifest.clone();
    signature_changed.symbols[0].signature.params[6] = AbiValue::new(AbiValueKind::I64);
    assert_eq!(signature_changed.layout, manifest.layout);
    assert_eq!(signature_changed.invalidation, manifest.invalidation);
    assert_ne!(
        signature_changed.symbols[0].signature.checksum(),
        expected_signature.checksum()
    );
    assert_ne!(signature_changed.checksum(), baseline_checksum);

    let mut missing_proof_fact = manifest.clone();
    missing_proof_fact
        .metadata
        .remove(&AYSatMinimizeKeepDropProofFact::ReasonTrailGuards.metadata_key());
    assert_ne!(missing_proof_fact.checksum(), baseline_checksum);

    let mut tampered_evidence_fact = proof_evidence;
    tampered_evidence_fact.metadata.insert(
        AYSatMinimizeKeepDropProofFact::DecisionKeepAbort.metadata_key(),
        "ay_sat_helper.minimize_decision_keep_abort.spoofed".to_owned(),
    );
    assert_ne!(
        tampered_evidence_fact.checksum(),
        baseline_evidence_checksum
    );
}

#[test]
fn ay_sat_helper_theory_dispatch_manifest_checksum_tracks_abi_policy_and_proof_fact_changes() {
    let manifest = ay_sat_theory_dispatch_assignment_manifest();
    let baseline_checksum = manifest.checksum();
    let expected_signature = ay_sat_theory_dispatch_assignment_signature();
    let proof_evidence =
        ay_sat_theory_dispatch_assignment_verified_proof_evidence("trust-cg-verify", &manifest);
    let baseline_evidence_checksum = proof_evidence.checksum();

    let mut args_record_changed = manifest.clone();
    let guard_flags = args_record_changed.layout.records[0]
        .fields
        .iter_mut()
        .find(|field| field.name == "guard_flags")
        .expect("SAT theory-dispatch args record binds guard_flags");
    guard_flags.offset_bytes = 24;
    assert_eq!(args_record_changed.invalidation, manifest.invalidation);
    assert_ne!(
        args_record_changed.layout.checksum(),
        manifest.layout.checksum()
    );
    assert_ne!(args_record_changed.checksum(), baseline_checksum);

    let mut signature_changed = manifest.clone();
    signature_changed.symbols[0].signature.returns[0] = AbiValue::new(AbiValueKind::I32);
    assert_eq!(signature_changed.layout, manifest.layout);
    assert_eq!(signature_changed.invalidation, manifest.invalidation);
    assert_ne!(
        signature_changed.symbols[0].signature.checksum(),
        expected_signature.checksum()
    );
    assert_ne!(signature_changed.checksum(), baseline_checksum);

    let mut proof_policy_changed = manifest.clone();
    proof_policy_changed.proof_policy = ProofPolicy::require_certificates(["trust-cg-verify"]);
    assert_ne!(
        proof_policy_changed.proof_policy.checksum(),
        manifest.proof_policy.checksum()
    );
    assert_ne!(proof_policy_changed.checksum(), baseline_checksum);

    let mut missing_proof_fact = manifest.clone();
    missing_proof_fact
        .metadata
        .remove(&AYSatTheoryDispatchProofFact::IteInactiveBranchDeferral.metadata_key());
    assert_ne!(missing_proof_fact.checksum(), baseline_checksum);

    let mut tampered_evidence_fact = proof_evidence;
    tampered_evidence_fact.metadata.insert(
        AYSatTheoryDispatchProofFact::LevelZeroAssert.metadata_key(),
        "ay_sat_helper.theory_dispatch_level_zero_assert.spoofed".to_owned(),
    );
    assert_ne!(
        tampered_evidence_fact.checksum(),
        baseline_evidence_checksum
    );
}

#[test]
fn ay_sat_helper_manifest_for_parts_text_section_follows_layout_symbol_size() {
    let layout_symbol_text_size = AY_SAT_CONTAINS4_MASKED_TEXT_SIZE_BYTES + 64;
    let stale_section_text_size = AY_SAT_CONTAINS4_MASKED_TEXT_SIZE_BYTES;
    let layout = ay_sat_contains4_masked_layout_with_text_size(16, layout_symbol_text_size);
    let manifest = ay_sat_contains4_masked_manifest_for_parts(
        ay_sat_contains4_masked_aarch64_target(),
        ay_sat_contains4_masked_aarch64_abi(),
        layout,
        ay_sat_contains4_masked_proof_policy(),
        99,
        stale_section_text_size,
    );

    let layout_symbol = manifest
        .layout
        .symbols
        .iter()
        .find(|symbol| symbol.name == AY_SAT_CONTAINS4_MASKED_SYMBOL && symbol.section == ".text")
        .expect("SAT helper layout binds the .text helper symbol");
    let text_section = manifest
        .sections
        .iter()
        .find(|section| section.name == ".text")
        .expect("SAT helper manifest binds a .text section");

    assert_eq!(layout_symbol.size_bytes, layout_symbol_text_size);
    assert_eq!(text_section.size_bytes, layout_symbol.size_bytes);
    assert_ne!(text_section.size_bytes, stale_section_text_size);
}

#[test]
fn ay_sat_helper_minimize_manifest_for_parts_text_section_follows_layout_symbol_size() {
    let layout_symbol_text_size = AY_SAT_MINIMIZE_KEEP_DROP_TEXT_SIZE_BYTES + 64;
    let stale_section_text_size = AY_SAT_MINIMIZE_KEEP_DROP_TEXT_SIZE_BYTES;
    let layout = ay_sat_minimize_keep_drop_layout_with_text_size(16, layout_symbol_text_size);
    let manifest = ay_sat_minimize_keep_drop_manifest_for_parts(
        ay_sat_minimize_keep_drop_aarch64_target(),
        ay_sat_minimize_keep_drop_aarch64_abi(),
        layout,
        ay_sat_minimize_keep_drop_proof_policy(),
        99,
        stale_section_text_size,
    );

    let layout_symbol = manifest
        .layout
        .symbols
        .iter()
        .find(|symbol| symbol.name == AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL && symbol.section == ".text")
        .expect("SAT minimization layout binds the .text helper symbol");
    let text_section = manifest
        .sections
        .iter()
        .find(|section| section.name == ".text")
        .expect("SAT minimization manifest binds a .text section");

    assert_eq!(layout_symbol.size_bytes, layout_symbol_text_size);
    assert_eq!(text_section.size_bytes, layout_symbol.size_bytes);
    assert_ne!(text_section.size_bytes, stale_section_text_size);
}

#[test]
fn ay_sat_helper_theory_dispatch_manifest_for_parts_text_section_follows_layout_symbol_size() {
    let layout_symbol_text_size = AY_SAT_THEORY_DISPATCH_ASSIGNMENT_TEXT_SIZE_BYTES + 64;
    let stale_section_text_size = AY_SAT_THEORY_DISPATCH_ASSIGNMENT_TEXT_SIZE_BYTES;
    let layout =
        ay_sat_theory_dispatch_assignment_layout_with_text_size(16, layout_symbol_text_size);
    let manifest = ay_sat_theory_dispatch_assignment_manifest_for_parts(
        ay_sat_theory_dispatch_assignment_aarch64_target(),
        ay_sat_theory_dispatch_assignment_aarch64_abi(),
        layout,
        ay_sat_theory_dispatch_assignment_proof_policy(),
        99,
        stale_section_text_size,
    );

    let layout_symbol = manifest
        .layout
        .symbols
        .iter()
        .find(|symbol| {
            symbol.name == AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL && symbol.section == ".text"
        })
        .expect("SAT theory-dispatch layout binds the .text helper symbol");
    let text_section = manifest
        .sections
        .iter()
        .find(|section| section.name == ".text")
        .expect("SAT theory-dispatch manifest binds a .text section");

    assert_eq!(layout_symbol.size_bytes, layout_symbol_text_size);
    assert_eq!(text_section.size_bytes, layout_symbol.size_bytes);
    assert_ne!(text_section.size_bytes, stale_section_text_size);
}
