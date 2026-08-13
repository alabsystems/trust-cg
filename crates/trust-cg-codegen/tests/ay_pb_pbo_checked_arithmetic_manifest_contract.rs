// trust-cg-codegen/tests/ay_pb_pbo_checked_arithmetic_manifest_contract.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::ay_pb_pbo_checked_arithmetic_contract::{
    AY_PB_PBO_CHECKED_ARITHMETIC_ARTIFACT_CONTRACT_SCHEMA,
    AY_PB_PBO_CHECKED_ARITHMETIC_ARTIFACT_CONTRACT_SCHEMA_VERSION,
    AY_PB_PBO_CHECKED_ARITHMETIC_KERNEL, AY_PB_PBO_CHECKED_OBJECTIVE_DEFAULT_GENERATION,
    AY_PB_PBO_CHECKED_OBJECTIVE_REFERENCE_ORACLE, AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL,
    AY_PB_PBO_CHECKED_OBJECTIVE_TEXT_SIZE_BYTES, AY_PB_PBO_CHECKED_OBJECTIVE_WRAPPER_IDENTITY,
    AY_PB_PBO_OBJECTIVE_STATUS_ABI, AY_PB_PBO_OBJECTIVE_STATUS_ALIGNMENT_BYTES,
    AY_PB_PBO_OBJECTIVE_STATUS_RECORD, AY_PB_PBO_OBJECTIVE_STATUS_SIZE_BYTES,
    ay_pb_pbo_checked_objective_aarch64_abi, ay_pb_pbo_checked_objective_aarch64_target,
    ay_pb_pbo_checked_objective_layout_with_text_size, ay_pb_pbo_checked_objective_manifest,
    ay_pb_pbo_checked_objective_manifest_for_parts, ay_pb_pbo_checked_objective_proof_policy,
    ay_pb_pbo_checked_objective_signature, ay_pb_pbo_checked_objective_symbol_lookup_contract,
};
use trust_cg_codegen::jit_contract::{AbiValue, AbiValueKind, DeterministicArtifactManifest};

#[repr(C)]
struct AYPbPboObjectiveStatusAbi {
    status: u8,
    deopt: u8,
    reserved: [u8; 6],
    objective: i64,
    detail: i64,
}

type AYPbPboObjectiveFn =
    unsafe extern "C" fn(*const i64, *const i64, i64, *mut AYPbPboObjectiveStatusAbi);

fn field<'a>(
    manifest: &'a DeterministicArtifactManifest,
    name: &str,
) -> &'a trust_cg_codegen::jit_contract::FieldLayout {
    manifest.layout.records[0]
        .fields
        .iter()
        .find(|field| field.name == name)
        .unwrap_or_else(|| panic!("PB/PBO status ABI binds {name} field"))
}

#[test]
fn ay_pb_pbo_checked_arithmetic_manifest_binds_status_abi_and_disabled_native_policy() {
    let manifest = ay_pb_pbo_checked_objective_manifest();
    let expected_signature = ay_pb_pbo_checked_objective_signature();
    let baseline_checksum = manifest.checksum();
    let contract = ay_pb_pbo_checked_objective_symbol_lookup_contract(&manifest);

    assert_eq!(
        std::mem::size_of::<AYPbPboObjectiveFn>(),
        std::mem::size_of::<*const u8>()
    );
    assert_eq!(
        manifest.symbol_signature(AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL),
        Some(&expected_signature)
    );
    assert_eq!(
        expected_signature.params,
        vec![
            AbiValue::new(AbiValueKind::Ptr),
            AbiValue::new(AbiValueKind::Ptr),
            AbiValue::new(AbiValueKind::I64),
            AbiValue::new(AbiValueKind::Ptr),
        ]
    );
    assert!(expected_signature.returns.is_empty());
    assert_eq!(contract.symbol, AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL);
    assert_eq!(contract.signature, expected_signature);
    assert_eq!(contract.target_checksum, manifest.target.checksum());
    assert_eq!(contract.abi_checksum, manifest.abi.checksum());
    assert_eq!(contract.layout_checksum, manifest.layout.checksum());
    assert_eq!(
        contract.invalidation_checksum,
        Some(manifest.invalidation.checksum())
    );
    assert_eq!(contract.manifest_checksum, Some(baseline_checksum));
    manifest
        .validate_symbol_lookup(&contract)
        .expect("manifest satisfies the typed PB/PBO checked arithmetic symbol lookup contract");

    assert_eq!(manifest.target.pointer_width_bits, 64);
    assert_eq!(manifest.abi.pointer_width_bits, 64);
    assert_eq!(manifest.layout.pointer_size_bytes, 8);
    assert_eq!(manifest.layout.pointer_alignment_bytes, 8);
    assert_eq!(
        manifest.layout.wrapper_identity.as_deref(),
        Some(AY_PB_PBO_CHECKED_OBJECTIVE_WRAPPER_IDENTITY)
    );

    let record = &manifest.layout.records[0];
    assert_eq!(record.name, AY_PB_PBO_OBJECTIVE_STATUS_RECORD);
    assert_eq!(record.representation, "repr(C)");
    assert_eq!(record.size_bytes, AY_PB_PBO_OBJECTIVE_STATUS_SIZE_BYTES);
    assert_eq!(
        record.alignment_bytes,
        AY_PB_PBO_OBJECTIVE_STATUS_ALIGNMENT_BYTES
    );
    assert_eq!(field(&manifest, "status").offset_bytes, 0);
    assert_eq!(field(&manifest, "deopt").offset_bytes, 1);
    assert_eq!(field(&manifest, "reserved").offset_bytes, 2);
    assert_eq!(field(&manifest, "objective").offset_bytes, 8);
    assert_eq!(field(&manifest, "detail").offset_bytes, 16);

    assert_eq!(
        manifest.layout.symbols[0].name,
        AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL
    );
    assert_eq!(
        manifest.layout.symbols[0].size_bytes,
        AY_PB_PBO_CHECKED_OBJECTIVE_TEXT_SIZE_BYTES
    );
    assert_eq!(manifest.sections[0].name, ".text");
    assert_eq!(
        manifest.sections[0].size_bytes,
        AY_PB_PBO_CHECKED_OBJECTIVE_TEXT_SIZE_BYTES
    );

    assert_eq!(
        manifest.layout.metadata.get("kernel").map(String::as_str),
        Some(AY_PB_PBO_CHECKED_ARITHMETIC_KERNEL)
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("status_abi")
            .map(String::as_str),
        Some(AY_PB_PBO_OBJECTIVE_STATUS_ABI)
    );
    assert_eq!(
        manifest
            .metadata
            .get("artifact_contract_schema")
            .map(String::as_str),
        Some(AY_PB_PBO_CHECKED_ARITHMETIC_ARTIFACT_CONTRACT_SCHEMA)
    );
    assert_eq!(
        manifest
            .metadata
            .get("artifact_contract_schema_version")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        AY_PB_PBO_CHECKED_ARITHMETIC_ARTIFACT_CONTRACT_SCHEMA_VERSION,
        1
    );
    assert_eq!(
        manifest.metadata.get("native_install").map(String::as_str),
        Some("disabled")
    );
    assert_eq!(
        manifest.metadata.get("useful_native").map(String::as_str),
        Some("0")
    );
    assert_eq!(
        manifest
            .metadata
            .get("reference_oracle")
            .map(String::as_str),
        Some(AY_PB_PBO_CHECKED_OBJECTIVE_REFERENCE_ORACLE)
    );
    assert_eq!(
        manifest.invalidation.generation,
        AY_PB_PBO_CHECKED_OBJECTIVE_DEFAULT_GENERATION
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
            .get("checked_arithmetic")
            .map(String::as_str),
        Some("i64_mul_add_overflow_deopts")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("native_install")
            .map(String::as_str),
        Some("disabled")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("useful_native")
            .map(String::as_str),
        Some("0")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("reference_oracle")
            .map(String::as_str),
        Some(AY_PB_PBO_CHECKED_OBJECTIVE_REFERENCE_ORACLE)
    );
}

#[test]
fn ay_pb_pbo_checked_arithmetic_manifest_checksum_tracks_abi_and_policy_changes() {
    let manifest = ay_pb_pbo_checked_objective_manifest();
    let baseline_checksum = manifest.checksum();
    let expected_signature = ay_pb_pbo_checked_objective_signature();

    let mut status_record_changed = manifest.clone();
    status_record_changed.layout.records[0].fields[4].offset_bytes = 24;
    assert_eq!(status_record_changed.invalidation, manifest.invalidation);
    assert_ne!(
        status_record_changed.layout.checksum(),
        manifest.layout.checksum()
    );
    assert_ne!(status_record_changed.checksum(), baseline_checksum);

    let mut generation_changed = manifest.clone();
    generation_changed.invalidation.generation += 1;
    assert_eq!(generation_changed.layout, manifest.layout);
    assert_ne!(
        generation_changed.invalidation.checksum(),
        manifest.invalidation.checksum()
    );
    assert_ne!(generation_changed.checksum(), baseline_checksum);

    let mut signature_changed = manifest.clone();
    signature_changed.symbols[0].signature.params[3] = AbiValue::new(AbiValueKind::Ptr).nullable();
    assert_eq!(signature_changed.layout, manifest.layout);
    assert_eq!(signature_changed.invalidation, manifest.invalidation);
    assert_ne!(
        signature_changed.symbols[0].signature.checksum(),
        expected_signature.checksum()
    );
    assert_ne!(signature_changed.checksum(), baseline_checksum);

    let mut native_enabled = manifest.clone();
    native_enabled
        .metadata
        .insert("useful_native".to_owned(), "1".to_owned());
    assert_ne!(native_enabled.checksum(), baseline_checksum);
}

#[test]
fn ay_pb_pbo_checked_arithmetic_manifest_for_parts_text_section_follows_layout_symbol_size() {
    let layout_symbol_text_size = AY_PB_PBO_CHECKED_OBJECTIVE_TEXT_SIZE_BYTES + 64;
    let stale_section_text_size = AY_PB_PBO_CHECKED_OBJECTIVE_TEXT_SIZE_BYTES;
    let layout = ay_pb_pbo_checked_objective_layout_with_text_size(16, layout_symbol_text_size);
    let manifest = ay_pb_pbo_checked_objective_manifest_for_parts(
        ay_pb_pbo_checked_objective_aarch64_target(),
        ay_pb_pbo_checked_objective_aarch64_abi(),
        layout,
        ay_pb_pbo_checked_objective_proof_policy(),
        99,
        stale_section_text_size,
    );

    let layout_symbol = manifest
        .layout
        .symbols
        .iter()
        .find(|symbol| {
            symbol.name == AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL && symbol.section == ".text"
        })
        .expect("PB/PBO layout binds the .text status probe symbol");
    let text_section = manifest
        .sections
        .iter()
        .find(|section| section.name == ".text")
        .expect("PB/PBO manifest binds a .text section");

    assert_eq!(layout_symbol.size_bytes, layout_symbol_text_size);
    assert_eq!(text_section.size_bytes, layout_symbol.size_bytes);
    assert_ne!(text_section.size_bytes, stale_section_text_size);
}
