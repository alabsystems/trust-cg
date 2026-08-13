// trust-cg-codegen/tests/ay_lra_manifest_contract.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::ay_lra_proof_manifest::{
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_FIRST_FAILED_ROW,
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_OVERFLOW_DEOPTS,
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_PARTIAL_ROW_DEOPTS,
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_ROWS_ATTEMPTED,
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_ROWS_COMMITTED, AY_LRA_BASIS_ROW_BATCH_TELEMETRY_STALE_DEOPTS,
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_USEFUL_NATIVE_DELTA, AY_LRA_LOCAL_PERF_JSON_EVIDENCE_SCHEMA,
    AY_LRA_LOCAL_PERF_JSON_EVIDENCE_SCHEMA_VERSION, AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE,
    AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA, AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA_VERSION,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_BOUNDS_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_FIRST_FAILED_ROWS,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OBSERVATIONS,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OK_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OVERFLOW_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_ATTEMPTED,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED_TOTAL,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_STALE_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_USEFUL_NATIVE_DELTA, AY_LRA_SPARSE_PERF_JSON_BENCHMARK_COUNT,
    AY_LRA_SPARSE_PERF_JSON_QUEUE_COMPILE_US_TOTAL, AY_LRA_SPARSE_PERF_JSON_QUEUE_SUBMISSIONS,
    AY_LRA_SPARSE_PERF_JSON_REPORT_SCHEMA, AY_LRA_SPARSE_PERF_JSON_REPORT_SHA256,
    AY_LRA_SPARSE_PERF_JSON_SUBMIT_TO_INSTALL_US_TOTAL,
    AY_LRA_SPARSE_SOLVER_PROGRAM_BASELINE_PAR2_MILLIS,
    AY_LRA_SPARSE_SOLVER_PROGRAM_CANDIDATE_PAR2_MILLIS,
    AY_LRA_SPARSE_SOLVER_PROGRAM_EVIDENCE_WAIT_HITS, AY_LRA_SPARSE_SOLVER_PROGRAM_INSTALLS,
    AY_LRA_SPARSE_SOLVER_PROGRAM_NATIVE_APPLIES,
    AY_LRA_SPARSE_SOLVER_PROGRAM_PAR2_REGRESSION_MILLIS, AYLraAarch64LoweringDecision,
    AYLraAarch64LoweringKind, AYLraBasisEpochEvidence, AYLraBasisRowBatchTelemetryEvidence,
    AYLraEvidenceAvailability, AYLraKernelProofConsumptionManifest, AYLraManifestAdmission,
    AYLraManifestDisposition, AYLraManifestRejectionReason, AYLraProductGateEvidence,
    AYLraProofConsumptionEvidence, AYLraProofFact, AYLraProofFamily, AYLraReplayComparison,
    AYLraRequirementAvailability, AYLraSolverProgramEvidenceKind, AYLraSolverProgramEvidenceScope,
    AYLraSparseAffectedRowBatchEvidence, AYLraSparseSubstitutePerfJsonEvidence,
    AYLraSparseSubstituteSolverProgramEvidence, ay_lra_basis_update_proof_manifest,
    ay_lra_proof_fact_metadata_key, ay_lra_sparse_affected_row_batch_proof_manifest,
    ay_lra_sparse_substitute_proof_manifest, evaluate_ay_lra_basis_row_batch_telemetry_evidence,
    evaluate_ay_lra_manifest_admission, evaluate_ay_lra_sparse_affected_row_batch_evidence,
    evaluate_ay_lra_sparse_substitute_perf_json_evidence,
    evaluate_ay_lra_sparse_substitute_solver_program_evidence, select_ay_lra_aarch64_lowering,
};
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, AliasPolicy, ArtifactSection, ArtifactSectionKind,
    ArtifactSymbol, DeterministicArtifactManifest, Endianness, FieldLayout, InvalidationKey,
    JitArtifactKind, LayoutManifest, Mutability, PointerBounds, PointerLayout,
    ProofEvidenceSummary, ProofMode, ProofPolicy, RecordLayout, SliceLayout, SymbolLayout,
    SymbolLookupContract, SymbolSignature, SymbolVisibility, TargetDescriptor,
    TargetOperatingSystem,
};

const STATUS_SYMBOL: &str = "ay_lra_sparse_substitute_status_probe";
const STATUS_RECORD: &str = "AYLraSparseSubstituteStatusAbi";
const AFFECTED_ROW_BATCH_STATUS_SYMBOL: &str = "ay_lra_sparse_affected_row_batch_status_probe";
const AFFECTED_ROW_BATCH_STATUS_RECORD: &str = "AYLraSparseAffectedRowBatchStatusAbi";
const BATCH_STATUS_SYMBOL: &str = "ay_lra_basis_row_batch";
const BATCH_STATUS_RECORD: &str = "AYLraBasisRowBatchStatusAbi";
const SPARSE_TRUST_CG_SOURCE_LOCK: &str = "source-lock-sha256:trust-cg:ay-lra-sparse-substitute:v1";
const SPARSE_TRUST_IR_SOURCE_LOCK: &str = "source-lock-sha256:trust-ir:ay-lra-sparse-substitute:v1";
const AFFECTED_ROW_BATCH_TRUST_CG_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-cg:ay-lra-sparse-affected-row-batch:v1";
const AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-ir:ay-lra-sparse-affected-row-batch:v1";
const BASIS_TRUST_CG_SOURCE_LOCK: &str = "source-lock-sha256:trust-cg:ay-lra-basis-row-batch:v1";
const BASIS_TRUST_IR_SOURCE_LOCK: &str = "source-lock-sha256:trust-ir:ay-lra-basis-row-batch:v1";
const AY_LRA_NATIVE_PAYLOAD_SHA256: &str = "sha256:ay-lra-manifest-contract-native-payload";
const AY_LRA_PROOF_REPORT_SHA256: &str = "sha256:ay-lra-manifest-contract-proof-report";
const CANONICAL_SHA256_LOWER: &str =
    "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
const UPPERCASE_SHA256: &str =
    "sha256:ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789";
const SHORT_SHA256: &str = "sha256:0123456789abcdef";
const NON_HEX_SHA256: &str =
    "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdeg";
const WHITESPACE_SHA256: &str =
    " sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
const WRONG_PREFIX_SHA256: &str =
    "SHA256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

fn i64_value() -> AbiValue {
    AbiValue::new(AbiValueKind::I64)
}

fn ptr_value() -> AbiValue {
    AbiValue::new(AbiValueKind::Ptr)
}

fn ay_lra_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            i64_value(), // planned sparse-substitute output length
            i64_value(), // output capacity
            i64_value(), // checked arithmetic lhs
            i64_value(), // checked arithmetic rhs
            i64_value(), // current basis epoch
            i64_value(), // expected basis epoch
            ptr_value(), // AYLraSparseSubstituteStatusAbi*
        ],
        vec![],
    )
}

fn ay_lra_batch_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            ptr_value(), // tableau row pointers
            ptr_value(), // row scales
            i64_value(), // affected row count
            ptr_value(), // row output offsets
            ptr_value(), // mutable row output lengths
            i64_value(), // output capacity
            ptr_value(), // [current basis epoch, expected basis epoch]
            ptr_value(), // AYLraBasisRowBatchStatusAbi*
        ],
        vec![],
    )
}

fn ay_lra_affected_row_batch_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            i64_value(), // affected rows in the batch
            i64_value(), // per-row output capacity
            i64_value(), // synthetic failure mode
            i64_value(), // current basis epoch
            i64_value(), // expected basis epoch
            ptr_value(), // mutable row-output lengths
            ptr_value(), // AYLraSparseAffectedRowBatchStatusAbi*
        ],
        vec![],
    )
}

fn nullable_status_pointer_signature() -> SymbolSignature {
    let mut signature = ay_lra_status_signature();
    let status_out = signature
        .params
        .last_mut()
        .expect("status signature includes an output status pointer");
    *status_out = AbiValue::new(AbiValueKind::Ptr).nullable();
    signature
}

fn batch_signature_with_nullable_status_pointer() -> SymbolSignature {
    let mut signature = ay_lra_batch_status_signature();
    let status_out = signature
        .params
        .last_mut()
        .expect("batch status signature includes an output status pointer");
    *status_out = AbiValue::new(AbiValueKind::Ptr).nullable();
    signature
}

fn affected_row_batch_signature_with_nullable_status_pointer() -> SymbolSignature {
    let mut signature = ay_lra_affected_row_batch_status_signature();
    let status_out = signature
        .params
        .last_mut()
        .expect("affected-row batch status signature includes an output status pointer");
    *status_out = AbiValue::new(AbiValueKind::Ptr).nullable();
    signature
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

fn ay_lra_status_record_layout() -> RecordLayout {
    RecordLayout {
        name: STATUS_RECORD.to_owned(),
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
                name: "value".to_owned(),
                offset_bytes: 8,
                size_bytes: 8,
                alignment_bytes: 8,
            },
            FieldLayout {
                name: "detail".to_owned(),
                offset_bytes: 16,
                size_bytes: 8,
                alignment_bytes: 8,
            },
        ],
    }
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

fn ay_lra_affected_row_batch_status_record_layout() -> RecordLayout {
    let mut layout = ay_lra_batch_status_record_layout();
    layout.name = AFFECTED_ROW_BATCH_STATUS_RECORD.to_owned();
    let rows_committed = layout
        .fields
        .get_mut(3)
        .expect("status layout includes a rows-completed field");
    rows_committed.name = "rows_committed".to_owned();
    let first_failed_row = layout
        .fields
        .last_mut()
        .expect("status layout includes a final detail field");
    first_failed_row.name = "first_failed_row".to_owned();
    layout
}

fn sparse_i64_slice(name: &str, mutability: Mutability) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes: 8,
        element_alignment_bytes: 8,
        stride_bytes: 8,
        length: None,
        bounds: PointerBounds::Symbol("row_len".to_owned()),
        mutability,
        alias_policy: match mutability {
            Mutability::Immutable => AliasPolicy::SharedReadOnly,
            Mutability::Mutable => AliasPolicy::Exclusive,
        },
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

fn ay_lra_layout() -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some("ay::lra::SparseSubstituteKernel::lp64:v1".to_owned());
    layout.records.push(ay_lra_status_record_layout());
    layout
        .slices
        .push(sparse_i64_slice("pivot_coeffs", Mutability::Immutable));
    layout
        .slices
        .push(sparse_i64_slice("target_coeffs", Mutability::Mutable));
    layout.pointers.push(PointerLayout {
        name: "status_out".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: 24,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.symbols.push(SymbolLayout {
        name: STATUS_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: 192,
        alignment_bytes: 16,
    });
    layout
        .metadata
        .insert("kernel".to_owned(), "ay_lra_sparse_substitute".to_owned());
    layout
        .metadata
        .insert("status_abi".to_owned(), "ay_lra_status_abi_v1".to_owned());
    layout
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

fn ay_lra_affected_row_batch_layout() -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some("ay::lra::SparseAffectedRowBatchKernel::lp64:v1".to_owned());
    layout
        .records
        .push(ay_lra_affected_row_batch_status_record_layout());
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
        name: AFFECTED_ROW_BATCH_STATUS_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: 256,
        alignment_bytes: 16,
    });
    layout.metadata.insert(
        "kernel".to_owned(),
        "ay_lra_sparse_affected_row_batch".to_owned(),
    );
    layout.metadata.insert(
        "row_output_lengths".to_owned(),
        "exact_per_row_i64_lengths".to_owned(),
    );
    layout
        .metadata
        .insert("output_capacity".to_owned(), "runtime_i64".to_owned());
    layout
        .metadata
        .insert("status_value".to_owned(), "rows_committed".to_owned());
    layout
        .metadata
        .insert("status_detail".to_owned(), "first_failed_row".to_owned());
    layout.metadata.insert(
        "status_abi".to_owned(),
        "ay_lra_sparse_affected_row_batch_status_abi_v1".to_owned(),
    );
    layout
}

fn ay_lra_proof_policy() -> ProofPolicy {
    ProofPolicy::require_certificates(["ay-lra", "trust-cg-verify"])
}

fn ay_lra_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    let mut invalidation = InvalidationKey::new(
        "ay:lra:sparse-substitute:kernel-v1",
        "trust-cg:phase5:lra:o2",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        44,
    );
    invalidation
        .extra
        .insert("basis_epoch".to_owned(), "runtime".to_owned());
    invalidation
        .extra
        .insert("status_abi".to_owned(), "ay_lra_status_abi_v1".to_owned());
    invalidation
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
        .insert("output_capacity".to_owned(), "runtime_i64".to_owned());
    invalidation
        .extra
        .insert("row_output_offsets".to_owned(), "runtime".to_owned());
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

fn ay_lra_affected_row_batch_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    let mut invalidation = InvalidationKey::new(
        "ay:lra:sparse-affected-row-batch:kernel-v1",
        "trust-cg:phase5:lra:o2",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        46,
    );
    invalidation
        .extra
        .insert("basis_epoch".to_owned(), "runtime".to_owned());
    invalidation.extra.insert(
        "row_output_lengths".to_owned(),
        "mutable_runtime".to_owned(),
    );
    invalidation.extra.insert(
        "row_output_lengths_contract".to_owned(),
        "exact_per_row_i64_lengths".to_owned(),
    );
    invalidation
        .extra
        .insert("output_capacity".to_owned(), "runtime_i64".to_owned());
    invalidation.extra.insert(
        "status_abi".to_owned(),
        "ay_lra_sparse_affected_row_batch_status_abi_v1".to_owned(),
    );
    invalidation
        .extra
        .insert("status_detail".to_owned(), "first_failed_row".to_owned());
    invalidation
        .extra
        .insert("status_value".to_owned(), "rows_committed".to_owned());
    invalidation
}

fn attach_ay_lra_proof_consumption_metadata(
    manifest: &mut DeterministicArtifactManifest,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
    trust_ir_source_identity: &str,
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
        trust_ir_source_identity.to_owned(),
    );
    manifest.metadata.insert(
        "source_policy".to_owned(),
        "approved_private_source".to_owned(),
    );
    manifest.metadata.insert(
        "approved_private_source_policy".to_owned(),
        "issue_796_internal_source_lock_v1".to_owned(),
    );
    let (trust_cg_source_lock, trust_ir_source_lock) =
        ay_lra_source_locks_for_identity(trust_ir_source_identity);
    manifest.metadata.insert(
        "trust_cg_source_lock".to_owned(),
        trust_cg_source_lock.to_owned(),
    );
    manifest.metadata.insert(
        "trust_ir_source_lock".to_owned(),
        trust_ir_source_lock.to_owned(),
    );
    manifest.metadata.insert(
        "native_payload_sha256".to_owned(),
        AY_LRA_NATIVE_PAYLOAD_SHA256.to_owned(),
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

fn ay_lra_source_locks_for_identity(
    trust_ir_source_identity: &str,
) -> (&'static str, &'static str) {
    match trust_ir_source_identity {
        "trust_ir:ay:lra:sparse-affected-row-batch:v1" => (
            AFFECTED_ROW_BATCH_TRUST_CG_SOURCE_LOCK,
            AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_LOCK,
        ),
        "trust_ir:ay:lra:basis-row-batch:v1" => {
            (BASIS_TRUST_CG_SOURCE_LOCK, BASIS_TRUST_IR_SOURCE_LOCK)
        }
        _ => (SPARSE_TRUST_CG_SOURCE_LOCK, SPARSE_TRUST_IR_SOURCE_LOCK),
    }
}

fn ay_lra_manifest() -> DeterministicArtifactManifest {
    let target = ay_lra_target();
    let abi = ay_lra_abi();
    let layout = ay_lra_layout();
    let proof_policy = ay_lra_proof_policy();
    let invalidation = ay_lra_invalidation(&target, &abi, &layout, &proof_policy);
    let mut manifest = DeterministicArtifactManifest::new(
        "ay-lra-sparse-substitute-status-probe",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: STATUS_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_lra_status_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: 192,
        alignment_bytes: 16,
        checksum: None,
    });
    manifest
        .metadata
        .insert("consumer".to_owned(), "ay".to_owned());
    manifest
        .metadata
        .insert("kernel".to_owned(), "lra_sparse_substitute".to_owned());
    attach_ay_lra_proof_consumption_metadata(
        &mut manifest,
        &ay_lra_sparse_substitute_proof_manifest(),
        "trust_ir:ay:lra:sparse-substitute:v1",
    );
    manifest
}

fn ay_lra_batch_manifest() -> DeterministicArtifactManifest {
    let target = ay_lra_target();
    let abi = ay_lra_abi();
    let layout = ay_lra_batch_layout();
    let proof_policy = ay_lra_proof_policy();
    let invalidation = ay_lra_batch_invalidation(&target, &abi, &layout, &proof_policy);
    let mut manifest = DeterministicArtifactManifest::new(
        "ay-lra-basis-row-batch",
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
        "proof_rejection_disposition".to_owned(),
        "typed_lookup_rejects_before_callable_escape".to_owned(),
    );
    manifest.metadata.insert(
        "replay_bundle_manifest_ref".to_owned(),
        "replay/ay-lra-basis-row-batch/manifest.json".to_owned(),
    );
    manifest.metadata.insert(
        "replay_bundle_proof_ref".to_owned(),
        "proofs/ay-lra-basis-row-batch/proof-evidence.json".to_owned(),
    );
    manifest.metadata.insert(
        "replay_bundle_telemetry_ref".to_owned(),
        "telemetry/ay-lra-basis-row-batch/compile-telemetry.json".to_owned(),
    );
    manifest.metadata.insert(
        "telemetry_counter_policy".to_owned(),
        "metadata_only_useful_native_false".to_owned(),
    );
    manifest
        .metadata
        .insert("useful_native".to_owned(), "false".to_owned());
    manifest.metadata.insert(
        "downstream_readiness".to_owned(),
        "followup_issue_709".to_owned(),
    );
    attach_ay_lra_proof_consumption_metadata(
        &mut manifest,
        &ay_lra_basis_update_proof_manifest(),
        "trust_ir:ay:lra:basis-row-batch:v1",
    );
    manifest
}

fn ay_lra_affected_row_batch_manifest() -> DeterministicArtifactManifest {
    let target = ay_lra_target();
    let abi = ay_lra_abi();
    let layout = ay_lra_affected_row_batch_layout();
    let proof_policy = ay_lra_proof_policy();
    let invalidation =
        ay_lra_affected_row_batch_invalidation(&target, &abi, &layout, &proof_policy);
    let mut manifest = DeterministicArtifactManifest::new(
        "ay-lra-sparse-affected-row-batch-status-probe",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: AFFECTED_ROW_BATCH_STATUS_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_lra_affected_row_batch_status_signature(),
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
    manifest.metadata.insert(
        "kernel".to_owned(),
        "ay_lra_sparse_affected_row_batch".to_owned(),
    );
    manifest.metadata.insert(
        "row_output_lengths".to_owned(),
        "exact_per_row_i64_lengths".to_owned(),
    );
    manifest
        .metadata
        .insert("output_capacity".to_owned(), "runtime_i64".to_owned());
    manifest
        .metadata
        .insert("status_value".to_owned(), "rows_committed".to_owned());
    manifest
        .metadata
        .insert("status_detail".to_owned(), "first_failed_row".to_owned());
    attach_ay_lra_proof_consumption_metadata(
        &mut manifest,
        &ay_lra_sparse_affected_row_batch_proof_manifest(),
        "trust_ir:ay:lra:sparse-affected-row-batch:v1",
    );
    manifest
}

fn ay_lra_verified_evidence(
    manifest: &DeterministicArtifactManifest,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::verified_for_artifact(
        "trust-cg-verify",
        manifest,
        AY_LRA_NATIVE_PAYLOAD_SHA256,
        AY_LRA_PROOF_REPORT_SHA256,
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
    if let Some(trust_ir_source_identity) = manifest.metadata.get("trust_ir_source_identity") {
        evidence.metadata.insert(
            "trust_ir_source_identity".to_owned(),
            trust_ir_source_identity.clone(),
        );
    }
    if let Some(source_policy) = manifest.metadata.get("source_policy") {
        evidence
            .metadata
            .insert("source_policy".to_owned(), source_policy.clone());
    }
    for key in ["trust_cg_source_lock", "trust_ir_source_lock"] {
        if let Some(value) = manifest.metadata.get(key) {
            evidence.metadata.insert(key.to_owned(), value.clone());
        }
    }
    evidence
}

fn complete_ay_lra_consumption_evidence(
    manifest: &DeterministicArtifactManifest,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
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

    let behavior_sha256 = CANONICAL_SHA256_LOWER.to_owned();
    AYLraProofConsumptionEvidence {
        proof_evidence: Some(ay_lra_verified_evidence(manifest, proof_manifest)),
        facts,
        certificates,
        basis_epoch: AYLraBasisEpochEvidence {
            current_epoch: manifest.invalidation.generation,
            expected_epoch: manifest.invalidation.generation,
        },
        replay: AYLraReplayComparison {
            manifest_checksum: manifest.checksum(),
            replay_root_sha256: CANONICAL_SHA256_LOWER.to_owned(),
            generic_behavior_sha256: behavior_sha256.clone(),
            specialized_behavior_sha256: behavior_sha256.clone(),
            reference_behavior_sha256: behavior_sha256,
        },
        product_gate: AYLraProductGateEvidence {
            install_gate_packet_sha256: CANONICAL_SHA256_LOWER.to_owned(),
            consumer_admission_sha256: CANONICAL_SHA256_LOWER.to_owned(),
            replay_identity_sha256: CANONICAL_SHA256_LOWER.to_owned(),
            telemetry_record_sha256: CANONICAL_SHA256_LOWER.to_owned(),
        },
    }
}

fn use_canonical_evidence_hashes(evidence: &mut AYLraProofConsumptionEvidence) {
    evidence.replay.replay_root_sha256 = CANONICAL_SHA256_LOWER.to_owned();
    evidence.replay.generic_behavior_sha256 = CANONICAL_SHA256_LOWER.to_owned();
    evidence.replay.specialized_behavior_sha256 = CANONICAL_SHA256_LOWER.to_owned();
    evidence.replay.reference_behavior_sha256 = CANONICAL_SHA256_LOWER.to_owned();
    evidence.product_gate.install_gate_packet_sha256 = CANONICAL_SHA256_LOWER.to_owned();
    evidence.product_gate.consumer_admission_sha256 = CANONICAL_SHA256_LOWER.to_owned();
    evidence.product_gate.replay_identity_sha256 = CANONICAL_SHA256_LOWER.to_owned();
    evidence.product_gate.telemetry_record_sha256 = CANONICAL_SHA256_LOWER.to_owned();
}

fn malformed_evidence_hashes() -> [(&'static str, &'static str); 6] {
    [
        ("empty suffix", "sha256:"),
        ("short suffix", SHORT_SHA256),
        ("non-hex suffix", NON_HEX_SHA256),
        ("uppercase suffix", UPPERCASE_SHA256),
        ("whitespace", WHITESPACE_SHA256),
        ("wrong prefix", WRONG_PREFIX_SHA256),
    ]
}

fn is_canonical_sha256(value: &str) -> bool {
    value
        .strip_prefix("sha256:")
        .map(|digest| {
            digest.len() == 64
                && digest
                    .bytes()
                    .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
        })
        .unwrap_or(false)
}

fn set_replay_hash_field(evidence: &mut AYLraProofConsumptionEvidence, field: &str, value: &str) {
    match field {
        "replay_root_sha256" => evidence.replay.replay_root_sha256 = value.to_owned(),
        "generic_behavior_sha256" => evidence.replay.generic_behavior_sha256 = value.to_owned(),
        "specialized_behavior_sha256" => {
            evidence.replay.specialized_behavior_sha256 = value.to_owned();
        }
        "reference_behavior_sha256" => {
            evidence.replay.reference_behavior_sha256 = value.to_owned();
        }
        _ => panic!("unknown replay hash field {field}"),
    }
}

fn set_product_gate_hash_field(
    evidence: &mut AYLraProofConsumptionEvidence,
    field: &str,
    value: &str,
) {
    match field {
        "install_gate_packet_sha256" => {
            evidence.product_gate.install_gate_packet_sha256 = value.to_owned();
        }
        "consumer_admission_sha256" => {
            evidence.product_gate.consumer_admission_sha256 = value.to_owned();
        }
        "replay_identity_sha256" => {
            evidence.product_gate.replay_identity_sha256 = value.to_owned();
        }
        "telemetry_record_sha256" => {
            evidence.product_gate.telemetry_record_sha256 = value.to_owned();
        }
        _ => panic!("unknown product-gate hash field {field}"),
    }
}

fn align_manifest_metadata_to_proof_manifest(
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
        "product_gate_fields".to_owned(),
        proof_manifest.product_gate.required_parent_gates.join(","),
    );
    manifest.metadata.insert(
        "telemetry_counter_policy".to_owned(),
        proof_manifest
            .product_gate
            .telemetry_counter_policy
            .to_owned(),
    );
    manifest.metadata.insert(
        "useful_native".to_owned(),
        proof_manifest
            .product_gate
            .useful_native_eligible
            .to_string(),
    );
    manifest.metadata.insert(
        "baseline_authoritative_until_product_gate".to_owned(),
        proof_manifest
            .product_gate
            .baseline_authoritative_until_product_gate
            .to_string(),
    );
}

fn assert_rejected_non_promoting(
    decision: AYLraManifestAdmission,
    reason: AYLraManifestRejectionReason,
) {
    assert_eq!(
        decision.disposition,
        AYLraManifestDisposition::RejectNonPromoting
    );
    assert!(
        decision.reasons.contains(&reason),
        "expected {}, got {:?}",
        reason.as_str(),
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

fn required_lemma_id(
    proof_manifest: &AYLraKernelProofConsumptionManifest,
    fact: AYLraProofFact,
) -> &'static str {
    proof_manifest
        .required_facts
        .iter()
        .find(|requirement| requirement.fact == fact)
        .expect("proof manifest includes required fact")
        .lemma_id
}

fn assert_lowering_rejected_non_promoting(
    decision: AYLraAarch64LoweringDecision,
    reason: AYLraManifestRejectionReason,
) {
    match decision {
        AYLraAarch64LoweringDecision::RejectNonPromoting { admission } => {
            assert_rejected_non_promoting(admission, reason);
        }
        AYLraAarch64LoweringDecision::UseNative { kind, admission } => {
            panic!("expected selector rejection, got {kind:?} with {admission:?}");
        }
    }
}

#[test]
fn ay_lra_proof_consumption_manifest_names_required_and_future_families() {
    let sparse = ay_lra_sparse_substitute_proof_manifest();
    let affected = ay_lra_sparse_affected_row_batch_proof_manifest();
    let basis = ay_lra_basis_update_proof_manifest();

    assert_eq!(sparse.schema, AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA);
    assert_eq!(
        sparse.schema_version,
        AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA_VERSION
    );
    assert_eq!(sparse.issue, AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE);
    assert!(sparse.required_facts.iter().any(|requirement| {
        requirement.fact == AYLraProofFact::SortedSparseRows
            && requirement.availability == AYLraRequirementAvailability::RequiredForAdmission
    }));
    assert!(sparse.required_facts.iter().any(|requirement| {
        requirement.fact == AYLraProofFact::TargetPivotAliasPolicy
            && requirement.lemma_id.contains("alias")
    }));
    assert!(
        sparse
            .required_facts
            .iter()
            .any(|requirement| { requirement.fact == AYLraProofFact::OutputCapacityBounds })
    );
    assert!(
        sparse
            .required_facts
            .iter()
            .any(|requirement| { requirement.fact == AYLraProofFact::CoefficientOverflow })
    );
    assert!(
        sparse
            .required_facts
            .iter()
            .any(|requirement| { requirement.fact == AYLraProofFact::BasisEpochFreshness })
    );
    assert!(basis.required_facts.iter().any(|requirement| {
        requirement.fact == AYLraProofFact::BatchPrefixCommitRollback
            && requirement.lemma_id == "ay_lra_basis.batch_prefix_commit_rollback"
    }));
    assert_eq!(
        affected.kernel_family.as_str(),
        "ay_lra_sparse_affected_row_batch"
    );
    assert_ne!(affected.kernel_family, basis.kernel_family);
    assert_ne!(
        affected.product_gate.allowlist_family,
        basis.product_gate.allowlist_family
    );
    assert!(affected.required_facts.iter().any(|requirement| {
        requirement.fact == AYLraProofFact::OutputCapacityBounds
            && requirement.lemma_id == "ay_lra_sparse_affected_batch.output_capacity_bounds"
    }));
    assert!(
        !affected
            .required_facts
            .iter()
            .any(|requirement| { requirement.fact == AYLraProofFact::BatchPrefixCommitRollback })
    );

    let future_families: Vec<_> = sparse
        .future_facts
        .iter()
        .map(|requirement| (requirement.family, requirement.availability))
        .collect();
    assert_eq!(future_families.len(), 3);
    assert!(future_families.iter().any(|(family, availability)| {
        *family == AYLraProofFamily::SatCandidateLoop
            && *availability == AYLraRequirementAvailability::MissingFuture
    }));
    assert!(future_families.iter().any(|(family, availability)| {
        *family == AYLraProofFamily::ChcCandidateLoop
            && *availability == AYLraRequirementAvailability::MissingFuture
    }));
    assert!(future_families.iter().any(|(family, availability)| {
        *family == AYLraProofFamily::PbCandidateLoop
            && *availability == AYLraRequirementAvailability::MissingFuture
    }));

    assert_eq!(sparse.product_gate.consumer, "ay");
    assert_eq!(sparse.product_gate.surface, "ay_registry");
    assert_eq!(
        sparse.product_gate.required_parent_gates,
        vec![
            "native_install_gate_packet",
            "ay_consumer_admission",
            "manifest_replay_identity",
            "useful_native_telemetry_record"
        ]
    );
    assert!(!sparse.product_gate.useful_native_eligible);
    assert!(
        sparse
            .product_gate
            .baseline_authoritative_until_product_gate
    );
}

#[test]
fn ay_lra_manifest_admission_emits_complete_sparse_manifest_without_product_promotion() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    let decision = evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence);

    assert_eq!(decision.disposition, AYLraManifestDisposition::EmitManifest);
    assert!(decision.reasons.is_empty());
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
    assert_eq!(decision.manifest_checksum, manifest.checksum());
}

#[test]
fn ay_lra_manifest_admission_emits_complete_basis_manifest_without_product_promotion() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    let decision = evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence);

    assert_eq!(decision.disposition, AYLraManifestDisposition::EmitManifest);
    assert!(decision.reasons.is_empty());
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
    assert_eq!(decision.manifest_checksum, manifest.checksum());
}

#[test]
fn ay_lra_manifest_admission_emits_complete_sparse_affected_row_batch_manifest_without_product_promotion()
 {
    let manifest = ay_lra_affected_row_batch_manifest();
    let proof_manifest = ay_lra_sparse_affected_row_batch_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    let decision = evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence);

    assert_eq!(decision.disposition, AYLraManifestDisposition::EmitManifest);
    assert!(decision.reasons.is_empty());
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
    assert_eq!(decision.manifest_checksum, manifest.checksum());
}

#[test]
fn ay_lra_manifest_admission_accepts_canonical_sha256_evidence_hashes() {
    for (manifest, proof_manifest) in [
        (ay_lra_manifest(), ay_lra_sparse_substitute_proof_manifest()),
        (
            ay_lra_affected_row_batch_manifest(),
            ay_lra_sparse_affected_row_batch_proof_manifest(),
        ),
        (
            ay_lra_batch_manifest(),
            ay_lra_basis_update_proof_manifest(),
        ),
    ] {
        let mut evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
        use_canonical_evidence_hashes(&mut evidence);

        let decision = evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence);

        assert_eq!(decision.disposition, AYLraManifestDisposition::EmitManifest);
        assert!(
            decision.reasons.is_empty(),
            "canonical hashes should admit {}, got {:?}",
            proof_manifest.kernel_family.as_str(),
            decision.reasons
        );
        assert!(decision.non_promoting);
        assert_eq!(decision.useful_native_delta, 0);
        assert_eq!(decision.manifest_checksum, manifest.checksum());
    }
}

#[test]
fn ay_lra_manifest_admission_rejects_malformed_replay_hashes() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let replay_fields = [
        "replay_root_sha256",
        "generic_behavior_sha256",
        "specialized_behavior_sha256",
        "reference_behavior_sha256",
    ];

    for field in replay_fields {
        for (case, value) in malformed_evidence_hashes() {
            let mut evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
            set_replay_hash_field(&mut evidence, field, value);

            let decision =
                evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence);

            assert!(
                decision
                    .reasons
                    .contains(&AYLraManifestRejectionReason::ReplayMismatch),
                "expected replay mismatch for {field} {case}, got {:?}",
                decision.reasons
            );
            assert_eq!(
                decision.disposition,
                AYLraManifestDisposition::RejectNonPromoting
            );
            assert!(decision.non_promoting);
            assert_eq!(decision.useful_native_delta, 0);
        }
    }
}

#[test]
fn ay_lra_manifest_admission_rejects_malformed_product_gate_hashes() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let product_gate_fields = [
        "install_gate_packet_sha256",
        "consumer_admission_sha256",
        "replay_identity_sha256",
        "telemetry_record_sha256",
    ];

    for field in product_gate_fields {
        for (case, value) in malformed_evidence_hashes() {
            let mut evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
            set_product_gate_hash_field(&mut evidence, field, value);

            let decision =
                evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence);

            assert!(
                decision
                    .reasons
                    .contains(&AYLraManifestRejectionReason::MissingProductGate),
                "expected missing product gate for {field} {case}, got {:?}",
                decision.reasons
            );
            assert_eq!(
                decision.disposition,
                AYLraManifestDisposition::RejectNonPromoting
            );
            assert!(decision.non_promoting);
            assert_eq!(decision.useful_native_delta, 0);
        }
    }
}

#[test]
fn ay_lra_solver_program_private_slice_rejects_profile_only_native_counters_non_promoting() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let solver_program_evidence =
        AYLraSparseSubstituteSolverProgramEvidence::packet1_private_local_profile_only()
            .with_canonical_hashes(&proof_manifest, &evidence);

    assert_eq!(
        evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence).disposition,
        AYLraManifestDisposition::EmitManifest
    );
    assert_eq!(
        solver_program_evidence.evidence_kind,
        AYLraSolverProgramEvidenceKind::ProfileOnly
    );
    assert_eq!(
        solver_program_evidence.scope,
        AYLraSolverProgramEvidenceScope::PrivateLocal
    );
    assert_eq!(
        solver_program_evidence.counters.native_applies,
        AY_LRA_SPARSE_SOLVER_PROGRAM_NATIVE_APPLIES
    );
    assert_eq!(
        solver_program_evidence.counters.installs,
        AY_LRA_SPARSE_SOLVER_PROGRAM_INSTALLS
    );
    assert_eq!(
        solver_program_evidence.counters.evidence_wait_hits,
        AY_LRA_SPARSE_SOLVER_PROGRAM_EVIDENCE_WAIT_HITS
    );
    assert_eq!(
        solver_program_evidence.baseline_par2_millis,
        AY_LRA_SPARSE_SOLVER_PROGRAM_BASELINE_PAR2_MILLIS
    );
    assert_eq!(
        solver_program_evidence.candidate_par2_millis,
        AY_LRA_SPARSE_SOLVER_PROGRAM_CANDIDATE_PAR2_MILLIS
    );
    assert_eq!(
        solver_program_evidence.par2_regression_millis(),
        AY_LRA_SPARSE_SOLVER_PROGRAM_PAR2_REGRESSION_MILLIS
    );
    assert!(!solver_program_evidence.production_activation);
    assert!(!solver_program_evidence.publication_claim);

    let decision = evaluate_ay_lra_sparse_substitute_solver_program_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &solver_program_evidence,
    );

    assert_eq!(
        decision.disposition,
        AYLraManifestDisposition::RejectNonPromoting
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceKindMismatch),
        "profile-only evidence with native counters must not satisfy solver-program-native: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramPar2Regression),
        "fresh W2 private evidence has no PAR-2 regression: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramObservedFactMismatch),
        "private observed facts should be bound exactly: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "canonical private evidence hashes should validate: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_solver_program_private_solver_native_facts_remain_non_promoting() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let solver_program_evidence =
        AYLraSparseSubstituteSolverProgramEvidence::packet1_private_local(
            AYLraSolverProgramEvidenceKind::SolverProgramNative,
        )
        .with_canonical_hashes(&proof_manifest, &evidence);

    let decision = evaluate_ay_lra_sparse_substitute_solver_program_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &solver_program_evidence,
    );

    assert_eq!(solver_program_evidence.par2_regression_millis(), 0);
    assert!(!solver_program_evidence.has_par2_regression());
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
    assert!(
        !solver_program_evidence.production_activation
            && !solver_program_evidence.publication_claim
    );
}

#[test]
fn ay_lra_solver_program_hashes_are_canonical_and_mutation_sensitive() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let solver_program_evidence =
        AYLraSparseSubstituteSolverProgramEvidence::packet1_private_local(
            AYLraSolverProgramEvidenceKind::SolverProgramNative,
        )
        .with_canonical_hashes(&proof_manifest, &evidence);

    assert_eq!(
        solver_program_evidence.hashes,
        solver_program_evidence.canonical_hashes(&proof_manifest, &evidence)
    );
    assert!(is_canonical_sha256(
        &solver_program_evidence.hashes.proof_facts_sha256
    ));
    assert!(is_canonical_sha256(
        &solver_program_evidence.hashes.replay_sha256
    ));
    assert!(is_canonical_sha256(
        &solver_program_evidence.hashes.product_gate_sha256
    ));
    assert!(is_canonical_sha256(
        &solver_program_evidence.hashes.evidence_tuple_sha256
    ));

    let mut fact_mutated = evidence.clone();
    fact_mutated.facts.insert(
        AYLraProofFact::OutputCapacityBounds,
        AYLraEvidenceAvailability::Missing,
    );
    assert_ne!(
        solver_program_evidence
            .canonical_hashes(&proof_manifest, &fact_mutated)
            .proof_facts_sha256,
        solver_program_evidence.hashes.proof_facts_sha256
    );
    let decision = evaluate_ay_lra_sparse_substitute_solver_program_evidence(
        &manifest,
        &proof_manifest,
        &fact_mutated,
        &solver_program_evidence,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "proof-fact mutation should stale the evidence hash: {:?}",
        decision.reasons
    );

    let mut replay_mutated = evidence.clone();
    replay_mutated.replay.replay_root_sha256 =
        "sha256:1111111111111111111111111111111111111111111111111111111111111111".to_owned();
    assert_ne!(
        solver_program_evidence
            .canonical_hashes(&proof_manifest, &replay_mutated)
            .replay_sha256,
        solver_program_evidence.hashes.replay_sha256
    );
    let decision = evaluate_ay_lra_sparse_substitute_solver_program_evidence(
        &manifest,
        &proof_manifest,
        &replay_mutated,
        &solver_program_evidence,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "replay mutation should stale the evidence hash: {:?}",
        decision.reasons
    );

    let mut product_gate_mutated = evidence.clone();
    product_gate_mutated.product_gate.consumer_admission_sha256 =
        "sha256:2222222222222222222222222222222222222222222222222222222222222222".to_owned();
    assert_ne!(
        solver_program_evidence
            .canonical_hashes(&proof_manifest, &product_gate_mutated)
            .product_gate_sha256,
        solver_program_evidence.hashes.product_gate_sha256
    );
    let decision = evaluate_ay_lra_sparse_substitute_solver_program_evidence(
        &manifest,
        &proof_manifest,
        &product_gate_mutated,
        &solver_program_evidence,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "product-gate mutation should stale the evidence hash: {:?}",
        decision.reasons
    );

    let mut tuple_mutated = solver_program_evidence.clone();
    tuple_mutated.counters.installs += 1;
    assert_ne!(
        tuple_mutated
            .canonical_hashes(&proof_manifest, &evidence)
            .evidence_tuple_sha256,
        solver_program_evidence.hashes.evidence_tuple_sha256
    );
    let decision = evaluate_ay_lra_sparse_substitute_solver_program_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &tuple_mutated,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramObservedFactMismatch),
        "counter mutation should reject observed private facts: {:?}",
        decision.reasons
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "counter mutation should stale the evidence tuple hash: {:?}",
        decision.reasons
    );

    let mut malformed_hash = solver_program_evidence.clone();
    malformed_hash.hashes.proof_facts_sha256 = UPPERCASE_SHA256.to_owned();
    let decision = evaluate_ay_lra_sparse_substitute_solver_program_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &malformed_hash,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "malformed hash should reject: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_solver_program_rejects_publication_or_activation_claims() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    let mut published = AYLraSparseSubstituteSolverProgramEvidence::packet1_private_local(
        AYLraSolverProgramEvidenceKind::SolverProgramNative,
    );
    published.scope = AYLraSolverProgramEvidenceScope::Published;
    published.publication_claim = true;
    published.production_activation = true;
    let published = published.with_canonical_hashes(&proof_manifest, &evidence);

    let decision = evaluate_ay_lra_sparse_substitute_solver_program_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &published,
    );

    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceScopeMismatch),
        "published evidence scope should reject: {:?}",
        decision.reasons
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramAuthorityMismatch),
        "production/publication authority should reject: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_sparse_perf_json_binds_compile_amortization_and_blocks_missing_apply_latency() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let perf_json =
        AYLraSparseSubstitutePerfJsonEvidence::current_private_report_missing_apply_latency()
            .with_canonical_hashes(&manifest, &proof_manifest, &evidence);

    assert_eq!(perf_json.schema, AY_LRA_LOCAL_PERF_JSON_EVIDENCE_SCHEMA);
    assert_eq!(
        perf_json.schema_version,
        AY_LRA_LOCAL_PERF_JSON_EVIDENCE_SCHEMA_VERSION
    );
    assert_eq!(
        perf_json.report_schema,
        AY_LRA_SPARSE_PERF_JSON_REPORT_SCHEMA
    );
    assert_eq!(
        perf_json.report_sha256,
        AY_LRA_SPARSE_PERF_JSON_REPORT_SHA256
    );
    assert_eq!(
        perf_json.scope,
        AYLraSolverProgramEvidenceScope::PrivateLocal
    );
    assert_eq!(
        perf_json.compile_amortization.benchmark_count,
        AY_LRA_SPARSE_PERF_JSON_BENCHMARK_COUNT
    );
    assert_eq!(
        perf_json.compile_amortization.native_applies,
        AY_LRA_SPARSE_SOLVER_PROGRAM_NATIVE_APPLIES
    );
    assert_eq!(
        perf_json.compile_amortization.native_installs,
        AY_LRA_SPARSE_SOLVER_PROGRAM_INSTALLS
    );
    assert_eq!(
        perf_json.compile_amortization.queue_submissions,
        AY_LRA_SPARSE_PERF_JSON_QUEUE_SUBMISSIONS
    );
    assert_eq!(
        perf_json.compile_amortization.queue_compile_us_total,
        AY_LRA_SPARSE_PERF_JSON_QUEUE_COMPILE_US_TOTAL
    );
    assert_eq!(
        perf_json.compile_amortization.submit_to_install_us_total,
        AY_LRA_SPARSE_PERF_JSON_SUBMIT_TO_INSTALL_US_TOTAL
    );
    assert!(perf_json.compile_amortization.has_compile_amortization());
    assert!(!perf_json.apply_latency.has_p50_p95_apply_latency());
    assert!(!perf_json.production_activation);
    assert!(!perf_json.publication_claim);
    assert_eq!(perf_json.useful_native_delta, 0);
    assert!(is_canonical_sha256(&perf_json.hashes.manifest_sha256));
    assert!(is_canonical_sha256(&perf_json.hashes.proof_facts_sha256));
    assert!(is_canonical_sha256(&perf_json.hashes.replay_sha256));
    assert!(is_canonical_sha256(&perf_json.hashes.product_gate_sha256));
    assert!(is_canonical_sha256(&perf_json.hashes.evidence_tuple_sha256));
    assert_eq!(
        perf_json.hashes,
        perf_json.canonical_hashes(&manifest, &proof_manifest, &evidence)
    );

    let decision = evaluate_ay_lra_sparse_substitute_perf_json_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &perf_json,
    );

    assert_eq!(
        decision.disposition,
        AYLraManifestDisposition::RejectNonPromoting
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonApplyLatencyMissing),
        "current private report should be blocked only on p50/p95 apply latency for this perf slice: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonCompileAmortizationMissing),
        "compile amortization counters should be bound from the private report: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonEvidenceHashMismatch),
        "canonical perf JSON hashes should validate: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_sparse_perf_json_accepts_complete_private_latency_tuple_non_promoting() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let perf_json =
        AYLraSparseSubstitutePerfJsonEvidence::current_private_report_missing_apply_latency()
            .with_apply_latency(39, 58, 21, 34)
            .with_canonical_hashes(&manifest, &proof_manifest, &evidence);

    assert!(perf_json.apply_latency.has_p50_p95_apply_latency());

    let decision = evaluate_ay_lra_sparse_substitute_perf_json_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &perf_json,
    );

    assert_eq!(decision.disposition, AYLraManifestDisposition::EmitManifest);
    assert!(
        decision.reasons.is_empty(),
        "complete private perf JSON tuple should validate internally: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_sparse_perf_json_rejects_zero_apply_latency_tuple() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let perf_json =
        AYLraSparseSubstitutePerfJsonEvidence::current_private_report_missing_apply_latency()
            .with_apply_latency(0, 0, 0, 0)
            .with_canonical_hashes(&manifest, &proof_manifest, &evidence);

    assert!(!perf_json.apply_latency.has_p50_p95_apply_latency());

    let decision = evaluate_ay_lra_sparse_substitute_perf_json_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &perf_json,
    );

    assert_eq!(
        decision.disposition,
        AYLraManifestDisposition::RejectNonPromoting
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonApplyLatencyMissing),
        "zero p50/p95 latency should reject as malformed evidence: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonEvidenceHashMismatch),
        "zero latency tuple should reject on semantics, not stale hashes: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_sparse_perf_json_rejects_native_latency_regression() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let perf_json =
        AYLraSparseSubstitutePerfJsonEvidence::current_private_report_missing_apply_latency()
            .with_apply_latency(39, 58, 40, 59)
            .with_canonical_hashes(&manifest, &proof_manifest, &evidence);

    assert!(perf_json.apply_latency.has_p50_p95_apply_latency());
    assert!(
        perf_json
            .apply_latency
            .has_native_apply_latency_regression()
    );

    let decision = evaluate_ay_lra_sparse_substitute_perf_json_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &perf_json,
    );

    assert_eq!(
        decision.disposition,
        AYLraManifestDisposition::RejectNonPromoting
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonApplyLatencyRegression),
        "native p50/p95 regression should reject: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonApplyLatencyMissing),
        "complete but regressed latency should not be classified as missing: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_sparse_perf_json_rejects_stale_hashes_latency_and_authority() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let perf_json =
        AYLraSparseSubstitutePerfJsonEvidence::current_private_report_missing_apply_latency()
            .with_apply_latency(39, 58, 21, 34)
            .with_canonical_hashes(&manifest, &proof_manifest, &evidence);

    let mut stale_compile = perf_json.clone();
    stale_compile.compile_amortization.native_applies += 1;
    let decision = evaluate_ay_lra_sparse_substitute_perf_json_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &stale_compile,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonCompileAmortizationMissing),
        "stale compile amortization should reject: {:?}",
        decision.reasons
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonEvidenceHashMismatch),
        "stale compile amortization should stale the tuple hash: {:?}",
        decision.reasons
    );

    let mut malformed_latency = perf_json.clone();
    malformed_latency.apply_latency.native_p95_us = Some(20);
    malformed_latency.hashes =
        malformed_latency.canonical_hashes(&manifest, &proof_manifest, &evidence);
    let decision = evaluate_ay_lra_sparse_substitute_perf_json_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &malformed_latency,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonApplyLatencyMissing),
        "p95 below p50 is malformed latency evidence: {:?}",
        decision.reasons
    );

    let mut authority_claim = perf_json.clone();
    authority_claim.scope = AYLraSolverProgramEvidenceScope::Published;
    authority_claim.production_activation = true;
    authority_claim.publication_claim = true;
    authority_claim.useful_native_delta = 1;
    authority_claim.hashes =
        authority_claim.canonical_hashes(&manifest, &proof_manifest, &evidence);
    let decision = evaluate_ay_lra_sparse_substitute_perf_json_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &authority_claim,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonEvidenceScopeMismatch),
        "published perf evidence scope should reject: {:?}",
        decision.reasons
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonAuthorityMismatch),
        "production/publication/useful-native authority should reject: {:?}",
        decision.reasons
    );

    let mut malformed_hash = perf_json.clone();
    malformed_hash.hashes.manifest_sha256 = UPPERCASE_SHA256.to_owned();
    let decision = evaluate_ay_lra_sparse_substitute_perf_json_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &malformed_hash,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::PerfJsonEvidenceHashMismatch),
        "malformed perf hash should reject: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_sparse_affected_row_batch_evidence_binds_lengths_status_counts_and_hashes_non_promoting()
{
    let manifest = ay_lra_affected_row_batch_manifest();
    let proof_manifest = ay_lra_sparse_affected_row_batch_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let affected_row_evidence = AYLraSparseAffectedRowBatchEvidence::private_local()
        .with_canonical_hashes(&manifest, &proof_manifest, &evidence);

    assert_eq!(
        evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence).disposition,
        AYLraManifestDisposition::EmitManifest
    );
    assert_eq!(
        affected_row_evidence.evidence_kind,
        AYLraSolverProgramEvidenceKind::SolverProgramNative
    );
    assert_eq!(
        affected_row_evidence.scope,
        AYLraSolverProgramEvidenceScope::PrivateLocal
    );
    assert_eq!(
        affected_row_evidence.counters.affected_rows_per_observation,
        3
    );
    assert_eq!(
        affected_row_evidence.counters.row_output_lengths.as_slice(),
        &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS
    );
    assert_eq!(
        affected_row_evidence.counters.rows_attempted(),
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_ATTEMPTED
    );
    assert_eq!(
        affected_row_evidence.counters.rows_committed.as_slice(),
        &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED
    );
    assert_eq!(
        affected_row_evidence.counters.total_rows_committed(),
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED_TOTAL
    );
    assert_eq!(
        affected_row_evidence.counters.first_failed_rows.as_slice(),
        &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_FIRST_FAILED_ROWS
    );
    assert_eq!(
        affected_row_evidence.counters.ok_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OK_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.overflow_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OVERFLOW_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.bounds_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_BOUNDS_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.stale_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_STALE_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.ok_statuses
            + affected_row_evidence.counters.overflow_statuses
            + affected_row_evidence.counters.bounds_statuses
            + affected_row_evidence.counters.stale_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OBSERVATIONS
    );
    assert_eq!(
        affected_row_evidence.useful_native_delta,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_USEFUL_NATIVE_DELTA
    );
    assert!(!affected_row_evidence.production_activation);
    assert!(!affected_row_evidence.publication_claim);
    assert!(is_canonical_sha256(
        &affected_row_evidence.hashes.manifest_sha256
    ));
    assert!(is_canonical_sha256(
        &affected_row_evidence.hashes.proof_facts_sha256
    ));
    assert!(is_canonical_sha256(
        &affected_row_evidence.hashes.replay_sha256
    ));
    assert!(is_canonical_sha256(
        &affected_row_evidence.hashes.product_gate_sha256
    ));
    assert!(is_canonical_sha256(
        &affected_row_evidence.hashes.evidence_tuple_sha256
    ));
    assert_eq!(
        affected_row_evidence.hashes,
        affected_row_evidence.canonical_hashes(&manifest, &proof_manifest, &evidence)
    );

    let decision = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &affected_row_evidence,
    );

    assert_eq!(decision.disposition, AYLraManifestDisposition::EmitManifest);
    assert!(
        decision.reasons.is_empty(),
        "canonical local sparse affected-row evidence should be internally consistent: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
    assert_eq!(decision.manifest_checksum, manifest.checksum());
}

#[test]
fn ay_lra_sparse_affected_row_batch_rejects_stale_counters_hashes_and_claims() {
    let manifest = ay_lra_affected_row_batch_manifest();
    let proof_manifest = ay_lra_sparse_affected_row_batch_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let affected_row_evidence = AYLraSparseAffectedRowBatchEvidence::private_local()
        .with_canonical_hashes(&manifest, &proof_manifest, &evidence);

    let mut stale_lengths = affected_row_evidence.clone();
    stale_lengths.counters.row_output_lengths[1] = 4;
    let decision = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &stale_lengths,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramObservedFactMismatch),
        "row-output length mutation should stale observed sparse affected-row facts: {:?}",
        decision.reasons
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "row-output length mutation should stale tuple hashes: {:?}",
        decision.reasons
    );
    assert_eq!(
        decision.disposition,
        AYLraManifestDisposition::RejectNonPromoting
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);

    let mut useful_native_claim = affected_row_evidence.clone();
    useful_native_claim.useful_native_delta = 1;
    let decision = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &useful_native_claim,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramObservedFactMismatch),
        "positive useful-native credit is not authorized by private affected-row evidence: {:?}",
        decision.reasons
    );
    assert_eq!(decision.useful_native_delta, 0);

    let mut proof_mutated = evidence.clone();
    proof_mutated.facts.insert(
        AYLraProofFact::OutputCapacityBounds,
        AYLraEvidenceAvailability::Missing,
    );
    let decision = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &manifest,
        &proof_manifest,
        &proof_mutated,
        &affected_row_evidence,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "proof-fact mutation should stale sparse affected-row proof hash: {:?}",
        decision.reasons
    );

    let mut replay_mutated = evidence.clone();
    replay_mutated.replay.replay_root_sha256 =
        "sha256:1111111111111111111111111111111111111111111111111111111111111111".to_owned();
    let decision = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &manifest,
        &proof_manifest,
        &replay_mutated,
        &affected_row_evidence,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "replay mutation should stale sparse affected-row replay hash: {:?}",
        decision.reasons
    );

    let mut product_gate_mutated = evidence.clone();
    product_gate_mutated.product_gate.consumer_admission_sha256 =
        "sha256:2222222222222222222222222222222222222222222222222222222222222222".to_owned();
    let decision = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &manifest,
        &proof_manifest,
        &product_gate_mutated,
        &affected_row_evidence,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "product-gate mutation should stale sparse affected-row product-gate hash: {:?}",
        decision.reasons
    );

    let mut malformed_hash = affected_row_evidence.clone();
    malformed_hash.hashes.product_gate_sha256 = UPPERCASE_SHA256.to_owned();
    let decision = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &malformed_hash,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "malformed hash should reject: {:?}",
        decision.reasons
    );

    let mut authority_claim = affected_row_evidence.clone();
    authority_claim.production_activation = true;
    authority_claim.publication_claim = true;
    authority_claim.scope = AYLraSolverProgramEvidenceScope::Published;
    authority_claim.hashes =
        authority_claim.canonical_hashes(&manifest, &proof_manifest, &evidence);
    let decision = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &authority_claim,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceScopeMismatch),
        "published sparse affected-row evidence should reject: {:?}",
        decision.reasons
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramAuthorityMismatch),
        "production/publication authority should reject: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_sparse_affected_row_batch_rejects_wrong_manifest_family() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let affected_row_evidence = AYLraSparseAffectedRowBatchEvidence::private_local()
        .with_canonical_hashes(&manifest, &proof_manifest, &evidence);

    let decision = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &affected_row_evidence,
    );

    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::UnsupportedKernelFamily,
    );
}

#[test]
fn ay_lra_basis_row_batch_telemetry_replay_evidence_binds_counters_and_hashes_non_promoting() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let telemetry = AYLraBasisRowBatchTelemetryEvidence::private_local().with_canonical_hashes(
        &manifest,
        &proof_manifest,
        &evidence,
    );

    assert_eq!(
        evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence).disposition,
        AYLraManifestDisposition::EmitManifest
    );
    assert_eq!(
        telemetry.evidence_kind,
        AYLraSolverProgramEvidenceKind::SolverProgramNative
    );
    assert_eq!(
        telemetry.scope,
        AYLraSolverProgramEvidenceScope::PrivateLocal
    );
    assert_eq!(
        telemetry.counters.rows_attempted,
        AY_LRA_BASIS_ROW_BATCH_TELEMETRY_ROWS_ATTEMPTED
    );
    assert_eq!(
        telemetry.counters.rows_committed,
        AY_LRA_BASIS_ROW_BATCH_TELEMETRY_ROWS_COMMITTED
    );
    assert_eq!(
        telemetry.counters.first_failed_row,
        AY_LRA_BASIS_ROW_BATCH_TELEMETRY_FIRST_FAILED_ROW
    );
    assert_eq!(
        telemetry.counters.stale_deopts,
        AY_LRA_BASIS_ROW_BATCH_TELEMETRY_STALE_DEOPTS
    );
    assert_eq!(
        telemetry.counters.overflow_deopts,
        AY_LRA_BASIS_ROW_BATCH_TELEMETRY_OVERFLOW_DEOPTS
    );
    assert_eq!(
        telemetry.counters.partial_row_deopts,
        AY_LRA_BASIS_ROW_BATCH_TELEMETRY_PARTIAL_ROW_DEOPTS
    );
    assert_eq!(
        telemetry.useful_native_delta,
        AY_LRA_BASIS_ROW_BATCH_TELEMETRY_USEFUL_NATIVE_DELTA
    );
    assert!(!telemetry.production_activation);
    assert!(!telemetry.publication_claim);
    assert!(is_canonical_sha256(&telemetry.hashes.manifest_sha256));
    assert!(is_canonical_sha256(&telemetry.hashes.proof_facts_sha256));
    assert!(is_canonical_sha256(&telemetry.hashes.replay_sha256));
    assert!(is_canonical_sha256(&telemetry.hashes.product_gate_sha256));
    assert!(is_canonical_sha256(&telemetry.hashes.evidence_tuple_sha256));
    assert_eq!(
        telemetry.hashes,
        telemetry.canonical_hashes(&manifest, &proof_manifest, &evidence)
    );

    let decision = evaluate_ay_lra_basis_row_batch_telemetry_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &telemetry,
    );

    assert_eq!(decision.disposition, AYLraManifestDisposition::EmitManifest);
    assert!(
        decision.reasons.is_empty(),
        "canonical local telemetry should be internally consistent: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
    assert_eq!(decision.manifest_checksum, manifest.checksum());
}

#[test]
fn ay_lra_basis_row_batch_telemetry_rejects_stale_counters_and_hashes() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let telemetry = AYLraBasisRowBatchTelemetryEvidence::private_local().with_canonical_hashes(
        &manifest,
        &proof_manifest,
        &evidence,
    );

    let mut counter_mutated = telemetry.clone();
    counter_mutated.counters.rows_committed += 1;
    let decision = evaluate_ay_lra_basis_row_batch_telemetry_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &counter_mutated,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramObservedFactMismatch),
        "counter mutation should stale observed row facts: {:?}",
        decision.reasons
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "counter mutation should stale tuple hashes: {:?}",
        decision.reasons
    );
    assert_eq!(
        decision.disposition,
        AYLraManifestDisposition::RejectNonPromoting
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);

    let mut useful_native_mutated = telemetry.clone();
    useful_native_mutated.useful_native_delta = 1;
    let decision = evaluate_ay_lra_basis_row_batch_telemetry_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &useful_native_mutated,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramObservedFactMismatch),
        "useful-native credit is not authorized by private telemetry: {:?}",
        decision.reasons
    );
    assert_eq!(decision.useful_native_delta, 0);

    let mut replay_mutated = evidence.clone();
    replay_mutated.replay.replay_root_sha256 =
        "sha256:1111111111111111111111111111111111111111111111111111111111111111".to_owned();
    let decision = evaluate_ay_lra_basis_row_batch_telemetry_evidence(
        &manifest,
        &proof_manifest,
        &replay_mutated,
        &telemetry,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "replay mutation should stale telemetry replay hash: {:?}",
        decision.reasons
    );

    let mut product_gate_mutated = evidence.clone();
    product_gate_mutated.product_gate.telemetry_record_sha256 =
        "sha256:2222222222222222222222222222222222222222222222222222222222222222".to_owned();
    let decision = evaluate_ay_lra_basis_row_batch_telemetry_evidence(
        &manifest,
        &proof_manifest,
        &product_gate_mutated,
        &telemetry,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "product-gate mutation should stale telemetry product-gate hash: {:?}",
        decision.reasons
    );

    let mut malformed_hash = telemetry.clone();
    malformed_hash.hashes.manifest_sha256 = UPPERCASE_SHA256.to_owned();
    let decision = evaluate_ay_lra_basis_row_batch_telemetry_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &malformed_hash,
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "malformed manifest hash should reject: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_manifest_admission_fails_closed_on_manifest_identity_metadata() {
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();

    let mut missing_artifact_identity = ay_lra_manifest();
    missing_artifact_identity
        .metadata
        .remove("proof_consumption_manifest_schema");
    let evidence =
        complete_ay_lra_consumption_evidence(&missing_artifact_identity, &proof_manifest);
    let decision =
        evaluate_ay_lra_manifest_admission(&missing_artifact_identity, &proof_manifest, &evidence);
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::ManifestIdentityMetadataMismatch,
    );

    let manifest = ay_lra_manifest();
    let mut stale_proof_identity = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    stale_proof_identity
        .proof_evidence
        .as_mut()
        .expect("complete evidence carries proof metadata")
        .metadata
        .insert(
            "proof_consumption_manifest_issue".to_owned(),
            "#795".to_owned(),
        );
    let decision =
        evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &stale_proof_identity);
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::ManifestIdentityMetadataMismatch,
    );
}

#[test]
fn ay_lra_manifest_admission_fails_closed_on_product_gate_metadata() {
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();

    let mut stale_artifact_product_gate = ay_lra_manifest();
    stale_artifact_product_gate.metadata.insert(
        "product_gate_fields".to_owned(),
        "native_install_gate_packet,ay_consumer_admission".to_owned(),
    );
    let evidence =
        complete_ay_lra_consumption_evidence(&stale_artifact_product_gate, &proof_manifest);
    let decision = evaluate_ay_lra_manifest_admission(
        &stale_artifact_product_gate,
        &proof_manifest,
        &evidence,
    );
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::ProductGateMetadataMismatch,
    );

    let manifest = ay_lra_manifest();
    let mut stale_proof_product_gate =
        complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    stale_proof_product_gate
        .proof_evidence
        .as_mut()
        .expect("complete evidence carries proof metadata")
        .metadata
        .insert(
            "product_gate_fields".to_owned(),
            "native_install_gate_packet,ay_consumer_admission".to_owned(),
        );
    let decision =
        evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &stale_proof_product_gate);
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::ProductGateMetadataMismatch,
    );
}

#[test]
fn ay_lra_manifest_admission_fails_closed_on_status_signature_binding() {
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();

    let mut bad_signature = ay_lra_manifest();
    bad_signature.symbols[0].signature = nullable_status_pointer_signature();
    bad_signature.metadata.insert(
        "status_signature_checksum".to_owned(),
        bad_signature.symbols[0].signature.checksum().to_string(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&bad_signature, &proof_manifest);
    let decision = evaluate_ay_lra_manifest_admission(&bad_signature, &proof_manifest, &evidence);
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::StatusSignatureMismatch,
    );

    let mut bad_checksum = ay_lra_manifest();
    bad_checksum.metadata.insert(
        "status_signature_checksum".to_owned(),
        ay_lra_batch_status_signature().checksum().to_string(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&bad_checksum, &proof_manifest);
    let decision = evaluate_ay_lra_manifest_admission(&bad_checksum, &proof_manifest, &evidence);
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::StatusSignatureMismatch,
    );

    let mut bad_deopt_layout = ay_lra_manifest();
    let deopt_field = bad_deopt_layout.layout.records[0]
        .fields
        .iter_mut()
        .find(|field| field.name == "deopt")
        .expect("sparse status record binds deopt field");
    deopt_field.offset_bytes = 2;
    bad_deopt_layout.invalidation.layout_checksum = bad_deopt_layout.layout.checksum();
    bad_deopt_layout.metadata.insert(
        "invalidation_checksum".to_owned(),
        bad_deopt_layout.invalidation.checksum().to_string(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&bad_deopt_layout, &proof_manifest);
    let decision =
        evaluate_ay_lra_manifest_admission(&bad_deopt_layout, &proof_manifest, &evidence);
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::StatusSignatureMismatch,
    );
}

#[test]
fn ay_lra_manifest_admission_fails_closed_on_sparse_evidence_gaps() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let cases = [
        (
            AYLraProofFact::SortedSparseRows,
            AYLraManifestRejectionReason::MissingSortedSparseRows,
        ),
        (
            AYLraProofFact::OutputCapacityBounds,
            AYLraManifestRejectionReason::MissingOutputCapacityBounds,
        ),
        (
            AYLraProofFact::CoefficientOverflow,
            AYLraManifestRejectionReason::MissingCoefficientOverflow,
        ),
        (
            AYLraProofFact::TargetPivotAliasPolicy,
            AYLraManifestRejectionReason::MissingTargetPivotAliasPolicy,
        ),
    ];

    for (missing_fact, expected_reason) in cases {
        let mut evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
        evidence
            .facts
            .insert(missing_fact, AYLraEvidenceAvailability::Missing);

        let decision = evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence);
        assert_rejected_non_promoting(decision, expected_reason);
    }

    let mut stale_epoch = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    stale_epoch.basis_epoch.current_epoch += 1;
    let decision = evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &stale_epoch);
    assert_rejected_non_promoting(decision, AYLraManifestRejectionReason::StaleBasisEpoch);
}

#[test]
fn ay_lra_manifest_admission_requires_per_fact_proof_metadata_for_available_sparse_facts() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();

    let mut missing_metadata = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    missing_metadata
        .proof_evidence
        .as_mut()
        .expect("complete evidence carries proof metadata")
        .metadata
        .remove(&ay_lra_proof_fact_metadata_key(
            AYLraProofFact::OutputCapacityBounds,
        ));
    assert_eq!(
        missing_metadata
            .facts
            .get(&AYLraProofFact::OutputCapacityBounds),
        Some(&AYLraEvidenceAvailability::Available)
    );
    let decision =
        evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &missing_metadata);
    assert_eq!(
        decision.reasons,
        vec![
            AYLraManifestRejectionReason::RequiredProofMetadataMismatch,
            AYLraManifestRejectionReason::MissingOutputCapacityBounds,
        ]
    );
    assert_eq!(decision.proof_metadata_mismatch_details.len(), 1);
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].key,
        ay_lra_proof_fact_metadata_key(AYLraProofFact::OutputCapacityBounds)
    );
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].expected,
        required_lemma_id(&proof_manifest, AYLraProofFact::OutputCapacityBounds)
    );
    assert_eq!(decision.proof_metadata_mismatch_details[0].actual, None);
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::MissingOutputCapacityBounds,
    );

    let mut mismatched_metadata = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    mismatched_metadata
        .proof_evidence
        .as_mut()
        .expect("complete evidence carries proof metadata")
        .metadata
        .insert(
            ay_lra_proof_fact_metadata_key(AYLraProofFact::OutputCapacityBounds),
            "ay_lra_sparse.output_capacity_bounds.spoof".to_owned(),
        );
    assert_eq!(
        mismatched_metadata
            .facts
            .get(&AYLraProofFact::OutputCapacityBounds),
        Some(&AYLraEvidenceAvailability::Available)
    );
    let decision =
        evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &mismatched_metadata);
    assert_eq!(
        decision.reasons,
        vec![
            AYLraManifestRejectionReason::RequiredProofMetadataMismatch,
            AYLraManifestRejectionReason::MissingOutputCapacityBounds,
        ]
    );
    assert_eq!(decision.proof_metadata_mismatch_details.len(), 1);
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].key,
        ay_lra_proof_fact_metadata_key(AYLraProofFact::OutputCapacityBounds)
    );
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].expected,
        required_lemma_id(&proof_manifest, AYLraProofFact::OutputCapacityBounds)
    );
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].actual,
        Some("ay_lra_sparse.output_capacity_bounds.spoof".to_owned())
    );
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::MissingOutputCapacityBounds,
    );
}

#[test]
fn ay_lra_manifest_admission_reports_multiple_per_fact_metadata_mismatches_in_manifest_order() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();

    let mut evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let proof_metadata = &mut evidence
        .proof_evidence
        .as_mut()
        .expect("complete evidence carries proof metadata")
        .metadata;
    proof_metadata.remove(&ay_lra_proof_fact_metadata_key(
        AYLraProofFact::SortedSparseRows,
    ));
    proof_metadata.insert(
        ay_lra_proof_fact_metadata_key(AYLraProofFact::OutputCapacityBounds),
        "ay_lra_sparse.output_capacity_bounds.spoof".to_owned(),
    );

    let decision = evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence);

    assert_eq!(
        decision.reasons,
        vec![
            AYLraManifestRejectionReason::RequiredProofMetadataMismatch,
            AYLraManifestRejectionReason::MissingSortedSparseRows,
            AYLraManifestRejectionReason::MissingOutputCapacityBounds,
        ]
    );
    assert_eq!(decision.proof_metadata_mismatch_details.len(), 2);
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].key,
        ay_lra_proof_fact_metadata_key(AYLraProofFact::SortedSparseRows)
    );
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].expected,
        required_lemma_id(&proof_manifest, AYLraProofFact::SortedSparseRows)
    );
    assert_eq!(decision.proof_metadata_mismatch_details[0].actual, None);
    assert_eq!(
        decision.proof_metadata_mismatch_details[1].key,
        ay_lra_proof_fact_metadata_key(AYLraProofFact::OutputCapacityBounds)
    );
    assert_eq!(
        decision.proof_metadata_mismatch_details[1].expected,
        required_lemma_id(&proof_manifest, AYLraProofFact::OutputCapacityBounds)
    );
    assert_eq!(
        decision.proof_metadata_mismatch_details[1].actual,
        Some("ay_lra_sparse.output_capacity_bounds.spoof".to_owned())
    );
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::MissingOutputCapacityBounds,
    );
}

#[test]
fn ay_lra_basis_manifest_admission_fails_closed_on_prefix_commit_gap() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let mut evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    evidence.facts.insert(
        AYLraProofFact::BatchPrefixCommitRollback,
        AYLraEvidenceAvailability::Missing,
    );

    let decision = evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &evidence);

    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::MissingBatchPrefixCommitRollback,
    );
}

#[test]
fn ay_lra_basis_manifest_admission_requires_per_fact_prefix_commit_metadata() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();

    let mut missing_metadata = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    missing_metadata
        .proof_evidence
        .as_mut()
        .expect("complete evidence carries proof metadata")
        .metadata
        .remove(&ay_lra_proof_fact_metadata_key(
            AYLraProofFact::BatchPrefixCommitRollback,
        ));
    assert_eq!(
        missing_metadata
            .facts
            .get(&AYLraProofFact::BatchPrefixCommitRollback),
        Some(&AYLraEvidenceAvailability::Available)
    );
    let decision =
        evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &missing_metadata);
    assert_eq!(
        decision.reasons,
        vec![
            AYLraManifestRejectionReason::RequiredProofMetadataMismatch,
            AYLraManifestRejectionReason::MissingBatchPrefixCommitRollback,
        ]
    );
    assert_eq!(decision.proof_metadata_mismatch_details.len(), 1);
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].key,
        ay_lra_proof_fact_metadata_key(AYLraProofFact::BatchPrefixCommitRollback)
    );
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].expected,
        required_lemma_id(&proof_manifest, AYLraProofFact::BatchPrefixCommitRollback)
    );
    assert_eq!(decision.proof_metadata_mismatch_details[0].actual, None);
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::MissingBatchPrefixCommitRollback,
    );

    let mut mismatched_metadata = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    mismatched_metadata
        .proof_evidence
        .as_mut()
        .expect("complete evidence carries proof metadata")
        .metadata
        .insert(
            ay_lra_proof_fact_metadata_key(AYLraProofFact::BatchPrefixCommitRollback),
            "ay_lra_basis.batch_prefix_commit_rollback.spoof".to_owned(),
        );
    assert_eq!(
        mismatched_metadata
            .facts
            .get(&AYLraProofFact::BatchPrefixCommitRollback),
        Some(&AYLraEvidenceAvailability::Available)
    );
    let decision =
        evaluate_ay_lra_manifest_admission(&manifest, &proof_manifest, &mismatched_metadata);
    assert_eq!(
        decision.reasons,
        vec![
            AYLraManifestRejectionReason::RequiredProofMetadataMismatch,
            AYLraManifestRejectionReason::MissingBatchPrefixCommitRollback,
        ]
    );
    assert_eq!(decision.proof_metadata_mismatch_details.len(), 1);
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].key,
        ay_lra_proof_fact_metadata_key(AYLraProofFact::BatchPrefixCommitRollback)
    );
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].expected,
        required_lemma_id(&proof_manifest, AYLraProofFact::BatchPrefixCommitRollback)
    );
    assert_eq!(
        decision.proof_metadata_mismatch_details[0].actual,
        Some("ay_lra_basis.batch_prefix_commit_rollback.spoof".to_owned())
    );
    assert_rejected_non_promoting(
        decision,
        AYLraManifestRejectionReason::MissingBatchPrefixCommitRollback,
    );
}

#[test]
fn ay_lra_aarch64_lowering_selector_uses_native_basis_row_batch_non_promoting() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    let decision = select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence);

    match decision {
        AYLraAarch64LoweringDecision::UseNative { kind, admission } => {
            assert_eq!(kind, AYLraAarch64LoweringKind::BasisRowBatch);
            assert_eq!(kind.as_str(), "basis_row_batch");
            assert_eq!(
                admission.disposition,
                AYLraManifestDisposition::EmitManifest
            );
            assert!(admission.reasons.is_empty());
            assert!(admission.non_promoting);
            assert_eq!(admission.useful_native_delta, 0);
            assert_eq!(admission.manifest_checksum, manifest.checksum());
        }
        AYLraAarch64LoweringDecision::RejectNonPromoting { admission } => {
            panic!("expected basis row-batch native selector decision, got {admission:?}");
        }
    }
}

#[test]
fn ay_lra_aarch64_lowering_selector_accepts_replay_required_basis_row_batch() {
    let mut manifest = ay_lra_batch_manifest();
    manifest.proof_policy.mode = ProofMode::RequireReplay;
    manifest.invalidation.proof_policy_checksum = manifest.proof_policy.checksum();
    manifest.metadata.insert(
        "proof_policy_checksum".to_owned(),
        manifest.proof_policy.checksum().to_string(),
    );
    manifest.metadata.insert(
        "invalidation_checksum".to_owned(),
        manifest.invalidation.checksum().to_string(),
    );
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    let decision = select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence);

    assert!(decision.is_use_native());
    assert_eq!(decision.useful_native_delta(), 0);
}

#[test]
fn ay_lra_aarch64_lowering_selector_uses_native_sparse_substitute_non_promoting() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    let decision = select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence);

    match decision {
        AYLraAarch64LoweringDecision::UseNative { kind, admission } => {
            assert_eq!(kind, AYLraAarch64LoweringKind::SparseSubstitute);
            assert_eq!(kind.as_str(), "sparse_substitute");
            assert_eq!(
                admission.disposition,
                AYLraManifestDisposition::EmitManifest
            );
            assert!(admission.reasons.is_empty());
            assert!(admission.non_promoting);
            assert_eq!(admission.useful_native_delta, 0);
            assert_eq!(admission.manifest_checksum, manifest.checksum());
        }
        AYLraAarch64LoweringDecision::RejectNonPromoting { admission } => {
            panic!("expected sparse-substitute native selector decision, got {admission:?}");
        }
    }
}

#[test]
fn ay_lra_aarch64_lowering_selector_uses_native_sparse_affected_row_batch_non_promoting() {
    let manifest = ay_lra_affected_row_batch_manifest();
    let proof_manifest = ay_lra_sparse_affected_row_batch_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    let decision = select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence);

    match decision {
        AYLraAarch64LoweringDecision::UseNative { kind, admission } => {
            assert_eq!(kind, AYLraAarch64LoweringKind::SparseAffectedRowBatch);
            assert_eq!(kind.as_str(), "sparse_affected_row_batch");
            assert_eq!(
                admission.disposition,
                AYLraManifestDisposition::EmitManifest
            );
            assert!(admission.reasons.is_empty());
            assert!(admission.non_promoting);
            assert_eq!(admission.useful_native_delta, 0);
            assert_eq!(admission.manifest_checksum, manifest.checksum());
        }
        AYLraAarch64LoweringDecision::RejectNonPromoting { admission } => {
            panic!(
                "expected sparse affected-row batch native selector decision, got {admission:?}"
            );
        }
    }
}

#[test]
fn ay_lra_aarch64_lowering_selector_fails_closed_on_affected_row_batch_source_identity_gap() {
    let proof_manifest = ay_lra_sparse_affected_row_batch_proof_manifest();
    let mut stale_source_identity = ay_lra_affected_row_batch_manifest();
    stale_source_identity.metadata.insert(
        "trust_ir_source_identity".to_owned(),
        "trust_ir:ay:lra:sparse-affected-row-batch:stale".to_owned(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&stale_source_identity, &proof_manifest);

    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&stale_source_identity, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::MissingSourceIdentity,
    );
}

fn assert_sparse_selector_rejects_tampered_manifest_identity(
    proof_manifest: AYLraKernelProofConsumptionManifest,
) {
    let mut manifest = ay_lra_manifest();
    align_manifest_metadata_to_proof_manifest(&mut manifest, &proof_manifest);
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::ManifestIdentityMetadataMismatch,
    );
}

#[test]
fn ay_lra_aarch64_lowering_selector_rejects_tampered_sparse_manifest_identity() {
    let mut tampered_schema = ay_lra_sparse_substitute_proof_manifest();
    tampered_schema.schema = "trust-cg.ay_lra.proof_consumption_manifest.sparse_spoof";
    assert_sparse_selector_rejects_tampered_manifest_identity(tampered_schema);

    let mut tampered_issue = ay_lra_sparse_substitute_proof_manifest();
    tampered_issue.issue = 663;
    assert_sparse_selector_rejects_tampered_manifest_identity(tampered_issue);

    let mut tampered_product_gate = ay_lra_sparse_substitute_proof_manifest();
    tampered_product_gate.product_gate.surface = "ay_registry_spoof";
    assert_sparse_selector_rejects_tampered_manifest_identity(tampered_product_gate);
}

#[test]
fn ay_lra_aarch64_lowering_selector_fails_closed_on_sparse_identity_gaps() {
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();

    let mut stale_source_identity = ay_lra_manifest();
    stale_source_identity.metadata.insert(
        "trust_ir_source_identity".to_owned(),
        "trust_ir:ay:lra:sparse-substitute:stale".to_owned(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&stale_source_identity, &proof_manifest);
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&stale_source_identity, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::MissingSourceIdentity,
    );

    let stale_proof_source = ay_lra_manifest();
    let mut evidence = complete_ay_lra_consumption_evidence(&stale_proof_source, &proof_manifest);
    evidence
        .proof_evidence
        .as_mut()
        .expect("complete evidence carries proof metadata")
        .metadata
        .insert(
            "trust_ir_source_identity".to_owned(),
            "trust_ir:ay:lra:sparse-substitute:stale".to_owned(),
        );
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&stale_proof_source, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::MissingSourceIdentity,
    );

    let mut stale_layout = ay_lra_manifest();
    stale_layout.layout.wrapper_identity = Some("ay::lra::RawSparseKernel::lp64:v1".to_owned());
    stale_layout.invalidation.layout_checksum = stale_layout.layout.checksum();
    stale_layout.metadata.insert(
        "invalidation_checksum".to_owned(),
        stale_layout.invalidation.checksum().to_string(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&stale_layout, &proof_manifest);
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&stale_layout, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );

    let mut raw_sentinel_symbol = ay_lra_manifest();
    raw_sentinel_symbol.layout.symbols[0].name = "substitute_var_specialized".to_owned();
    raw_sentinel_symbol.invalidation.layout_checksum = raw_sentinel_symbol.layout.checksum();
    raw_sentinel_symbol.metadata.insert(
        "invalidation_checksum".to_owned(),
        raw_sentinel_symbol.invalidation.checksum().to_string(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&raw_sentinel_symbol, &proof_manifest);
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&raw_sentinel_symbol, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );

    let mut bad_status_abi = ay_lra_manifest();
    bad_status_abi
        .metadata
        .insert("status_abi".to_owned(), "ay_lra_status_abi_v0".to_owned());
    let evidence = complete_ay_lra_consumption_evidence(&bad_status_abi, &proof_manifest);
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&bad_status_abi, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::StatusSignatureMismatch,
    );

    let mut spoofed_abi = ay_lra_manifest();
    spoofed_abi.abi.calling_convention = "sysv_amd64".to_owned();
    spoofed_abi.invalidation.abi_checksum = spoofed_abi.abi.checksum();
    spoofed_abi.metadata.insert(
        "invalidation_checksum".to_owned(),
        spoofed_abi.invalidation.checksum().to_string(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&spoofed_abi, &proof_manifest);
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&spoofed_abi, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );
}

#[test]
fn ay_lra_manifest_admission_requires_source_metadata_in_artifact_and_proof() {
    let baseline = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();

    for key in [
        "source_policy",
        "trust_ir_source_identity",
        "trust_cg_source_lock",
        "trust_ir_source_lock",
    ] {
        let mut missing_artifact = baseline.clone();
        missing_artifact.metadata.remove(key);
        let mut evidence = complete_ay_lra_consumption_evidence(&missing_artifact, &proof_manifest);
        if let Some(value) = baseline.metadata.get(key) {
            evidence
                .proof_evidence
                .as_mut()
                .expect("complete evidence carries proof metadata")
                .metadata
                .insert(key.to_owned(), value.clone());
        }
        assert_rejected_non_promoting(
            evaluate_ay_lra_manifest_admission(&missing_artifact, &proof_manifest, &evidence),
            AYLraManifestRejectionReason::MissingSourceIdentity,
        );

        let mut missing_proof = complete_ay_lra_consumption_evidence(&baseline, &proof_manifest);
        missing_proof
            .proof_evidence
            .as_mut()
            .expect("complete evidence carries proof metadata")
            .metadata
            .remove(key);
        assert_rejected_non_promoting(
            evaluate_ay_lra_manifest_admission(&baseline, &proof_manifest, &missing_proof),
            AYLraManifestRejectionReason::MissingSourceIdentity,
        );

        let mut spoofed_proof = complete_ay_lra_consumption_evidence(&baseline, &proof_manifest);
        spoofed_proof
            .proof_evidence
            .as_mut()
            .expect("complete evidence carries proof metadata")
            .metadata
            .insert(key.to_owned(), format!("{}.spoof", baseline.metadata[key]));
        assert_rejected_non_promoting(
            evaluate_ay_lra_manifest_admission(&baseline, &proof_manifest, &spoofed_proof),
            AYLraManifestRejectionReason::MissingSourceIdentity,
        );
    }
}

#[test]
fn ay_lra_aarch64_lowering_selector_fails_closed_on_sparse_evidence_gaps() {
    let manifest = ay_lra_manifest();
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();

    let mut missing_entering_variable =
        complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    missing_entering_variable.facts.insert(
        AYLraProofFact::EnteringVariable,
        AYLraEvidenceAvailability::Missing,
    );
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &missing_entering_variable),
        AYLraManifestRejectionReason::MissingEnteringVariable,
    );

    let mut missing_certificate = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    missing_certificate.certificates.insert(
        "ay-lra-sparse-overflow".to_owned(),
        AYLraEvidenceAvailability::Missing,
    );
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &missing_certificate),
        AYLraManifestRejectionReason::MissingCertificateDependency,
    );

    let mut stale_epoch = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    stale_epoch.basis_epoch.current_epoch = manifest.invalidation.generation - 1;
    stale_epoch.basis_epoch.expected_epoch = manifest.invalidation.generation - 1;
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &stale_epoch),
        AYLraManifestRejectionReason::StaleBasisEpoch,
    );

    let mut bad_replay_hash = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    bad_replay_hash.replay.specialized_behavior_sha256 = "not-a-sha256-digest".to_owned();
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &bad_replay_hash),
        AYLraManifestRejectionReason::ReplayMismatch,
    );

    let mut bad_product_gate = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    bad_product_gate.product_gate.replay_identity_sha256 = "not-a-sha256-digest".to_owned();
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &bad_product_gate),
        AYLraManifestRejectionReason::MissingProductGate,
    );
}

fn assert_basis_selector_rejects_tampered_manifest_identity(
    proof_manifest: AYLraKernelProofConsumptionManifest,
) {
    let mut manifest = ay_lra_batch_manifest();
    align_manifest_metadata_to_proof_manifest(&mut manifest, &proof_manifest);
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::ManifestIdentityMetadataMismatch,
    );
}

#[test]
fn ay_lra_aarch64_lowering_selector_rejects_tampered_basis_manifest_identity() {
    let mut tampered_schema = ay_lra_basis_update_proof_manifest();
    tampered_schema.schema = "trust-cg.ay_lra.proof_consumption_manifest.audit_spoof";
    assert_basis_selector_rejects_tampered_manifest_identity(tampered_schema);

    let mut tampered_version = ay_lra_basis_update_proof_manifest();
    tampered_version.schema_version = AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA_VERSION + 1;
    assert_basis_selector_rejects_tampered_manifest_identity(tampered_version);

    let mut tampered_issue = ay_lra_basis_update_proof_manifest();
    tampered_issue.issue = 663;
    assert_basis_selector_rejects_tampered_manifest_identity(tampered_issue);

    let mut tampered_product_gate = ay_lra_basis_update_proof_manifest();
    tampered_product_gate.product_gate.surface = "ay_registry_spoof";
    tampered_product_gate.product_gate.required_parent_gates = vec![
        "native_install_gate_packet",
        "ay_consumer_admission",
        "manifest_replay_identity",
        "useful_native_telemetry_record",
        "spoofed_parent_gate",
    ];
    assert_basis_selector_rejects_tampered_manifest_identity(tampered_product_gate);
}

#[test]
fn ay_lra_aarch64_lowering_selector_rejects_spoofed_aapcs64_abi_fields() {
    let mut manifest = ay_lra_batch_manifest();
    manifest.abi.name = "spoofed-aapcs64-name".to_owned();
    manifest.abi.calling_convention = "sysv_amd64".to_owned();
    manifest.abi.stack_alignment_bytes = 8;
    manifest.abi.integer_argument_registers = vec!["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    manifest.invalidation.abi_checksum = manifest.abi.checksum();
    manifest.metadata.insert(
        "invalidation_checksum".to_owned(),
        manifest.invalidation.checksum().to_string(),
    );

    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);

    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );
}

#[test]
fn ay_lra_aarch64_lowering_selector_fails_closed_on_basis_evidence_gaps() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();

    let mut missing_prefix_fact = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    missing_prefix_fact.facts.insert(
        AYLraProofFact::BatchPrefixCommitRollback,
        AYLraEvidenceAvailability::Missing,
    );
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &missing_prefix_fact),
        AYLraManifestRejectionReason::MissingBatchPrefixCommitRollback,
    );

    let mut missing_prefix_certificate =
        complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    missing_prefix_certificate.certificates.insert(
        "ay-lra-basis-prefix-rollback".to_owned(),
        AYLraEvidenceAvailability::Missing,
    );
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &missing_prefix_certificate),
        AYLraManifestRejectionReason::MissingCertificateDependency,
    );

    let mut stale_source_identity = manifest.clone();
    stale_source_identity.metadata.insert(
        "trust_ir_source_identity".to_owned(),
        "trust_ir:ay:lra:basis-row-batch:stale".to_owned(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&stale_source_identity, &proof_manifest);
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&stale_source_identity, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::MissingSourceIdentity,
    );

    let mut stale_layout = manifest.clone();
    stale_layout
        .metadata
        .insert("commit_policy".to_owned(), "all_or_rollback".to_owned());
    stale_layout
        .layout
        .metadata
        .insert("commit_policy".to_owned(), "all_or_rollback".to_owned());
    stale_layout.invalidation.layout_checksum = stale_layout.layout.checksum();
    let evidence = complete_ay_lra_consumption_evidence(&stale_layout, &proof_manifest);
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&stale_layout, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );
}

#[test]
fn ay_lra_aarch64_lowering_selector_rejects_equal_but_stale_basis_epoch_pair() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let mut evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    evidence.basis_epoch.current_epoch = manifest.invalidation.generation - 1;
    evidence.basis_epoch.expected_epoch = manifest.invalidation.generation - 1;

    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence),
        AYLraManifestRejectionReason::StaleBasisEpoch,
    );
}

#[test]
fn ay_lra_aarch64_lowering_selector_requires_replay_and_product_gate_hashes() {
    let manifest = ay_lra_batch_manifest();
    let proof_manifest = ay_lra_basis_update_proof_manifest();

    let mut bad_replay_hash = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    bad_replay_hash.replay.specialized_behavior_sha256 = "not-a-sha256-digest".to_owned();
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &bad_replay_hash),
        AYLraManifestRejectionReason::ReplayMismatch,
    );

    let mut bad_product_gate = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    bad_product_gate.product_gate.install_gate_packet_sha256 = "not-a-sha256-digest".to_owned();
    assert_lowering_rejected_non_promoting(
        select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &bad_product_gate),
        AYLraManifestRejectionReason::MissingProductGate,
    );
}

#[test]
fn ay_lra_sparse_substitute_manifest_checksum_tracks_contract_changes() {
    let manifest = ay_lra_manifest();
    let expected_signature = ay_lra_status_signature();
    let baseline_checksum = manifest.checksum();

    assert_eq!(manifest.target.pointer_width_bits, 64);
    assert_eq!(manifest.abi.pointer_width_bits, 64);
    assert_eq!(manifest.layout.pointer_size_bytes, 8);
    assert_eq!(manifest.layout.pointer_alignment_bytes, 8);
    assert_eq!(manifest.layout.records[0].name, STATUS_RECORD);
    assert_eq!(
        manifest.symbol_signature(STATUS_SYMBOL),
        Some(&expected_signature)
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
            .metadata
            .get("proof_consumption_manifest_schema")
            .map(String::as_str),
        Some(AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA)
    );
    assert_eq!(
        manifest
            .metadata
            .get("proof_consumption_manifest_issue")
            .map(String::as_str),
        Some("#796")
    );
    assert_eq!(
        manifest
            .metadata
            .get("trust_ir_source_identity")
            .map(String::as_str),
        Some("trust_ir:ay:lra:sparse-substitute:v1")
    );
    assert_eq!(
        manifest.metadata.get("source_policy").map(String::as_str),
        Some("approved_private_source")
    );
    assert!(
        manifest
            .metadata
            .get("required_proof_facts")
            .expect("sparse manifest records required proof facts")
            .contains("sorted_sparse_rows")
    );
    assert_eq!(
        manifest
            .metadata
            .get("future_proof_families")
            .map(String::as_str),
        Some("ay_chc_candidate_loop,ay_pb_candidate_loop,ay_sat_candidate_loop")
    );
    assert_eq!(
        manifest
            .metadata
            .get("future_proof_status")
            .map(String::as_str),
        Some("missing_future")
    );
    assert_eq!(
        manifest.metadata.get("replay_compare").map(String::as_str),
        Some("generic_specialized_reference_manifest_identity")
    );
    assert_eq!(
        manifest.metadata.get("useful_native").map(String::as_str),
        Some("false")
    );

    let mut layout_changed = manifest.clone();
    layout_changed.layout.records[0].size_bytes = 32;
    layout_changed.layout.records[0].fields[3].offset_bytes = 16;
    layout_changed.layout.records[0].fields[4].offset_bytes = 24;
    assert_eq!(layout_changed.invalidation, manifest.invalidation);
    assert_ne!(layout_changed.layout.checksum(), manifest.layout.checksum());
    assert_ne!(layout_changed.checksum(), baseline_checksum);

    let mut invalidation_changed = manifest.clone();
    invalidation_changed.invalidation.generation += 1;
    assert_eq!(invalidation_changed.layout, manifest.layout);
    assert_ne!(
        invalidation_changed.invalidation.checksum(),
        manifest.invalidation.checksum()
    );
    assert_ne!(invalidation_changed.checksum(), baseline_checksum);

    let mut status_signature_changed = manifest.clone();
    status_signature_changed.symbols[0].signature = nullable_status_pointer_signature();
    assert_eq!(status_signature_changed.layout, manifest.layout);
    assert_eq!(status_signature_changed.invalidation, manifest.invalidation);
    assert_ne!(
        status_signature_changed.symbols[0].signature.checksum(),
        expected_signature.checksum()
    );
    assert_ne!(status_signature_changed.checksum(), baseline_checksum);
}

#[test]
fn ay_lra_sparse_affected_row_batch_manifest_binds_status_contract_and_fail_closes_metadata() {
    let manifest = ay_lra_affected_row_batch_manifest();
    let proof_manifest = ay_lra_sparse_affected_row_batch_proof_manifest();
    let evidence = complete_ay_lra_consumption_evidence(&manifest, &proof_manifest);
    let expected_signature = ay_lra_affected_row_batch_status_signature();
    let baseline_checksum = manifest.checksum();

    assert_eq!(
        proof_manifest.kernel_family.as_str(),
        "ay_lra_sparse_affected_row_batch"
    );
    assert_eq!(
        manifest.symbol_signature(AFFECTED_ROW_BATCH_STATUS_SYMBOL),
        Some(&expected_signature)
    );
    assert_eq!(
        manifest.layout.wrapper_identity.as_deref(),
        Some("ay::lra::SparseAffectedRowBatchKernel::lp64:v1")
    );
    assert_eq!(
        manifest.layout.records[0].name,
        AFFECTED_ROW_BATCH_STATUS_RECORD
    );
    assert_eq!(
        manifest.layout.metadata.get("kernel").map(String::as_str),
        Some("ay_lra_sparse_affected_row_batch")
    );
    assert_eq!(
        manifest.metadata.get("kernel").map(String::as_str),
        Some("ay_lra_sparse_affected_row_batch")
    );
    assert_eq!(
        manifest
            .metadata
            .get("trust_ir_source_identity")
            .map(String::as_str),
        Some("trust_ir:ay:lra:sparse-affected-row-batch:v1")
    );
    assert_eq!(
        manifest
            .metadata
            .get("row_output_lengths")
            .map(String::as_str),
        Some("exact_per_row_i64_lengths")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("row_output_lengths")
            .map(String::as_str),
        Some("exact_per_row_i64_lengths")
    );
    assert_eq!(
        manifest.metadata.get("status_value").map(String::as_str),
        Some("rows_committed")
    );
    assert_eq!(
        manifest.metadata.get("status_detail").map(String::as_str),
        Some("first_failed_row")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("status_abi")
            .map(String::as_str),
        Some("ay_lra_sparse_affected_row_batch_status_abi_v1")
    );

    let row_output_lengths = manifest
        .layout
        .slices
        .iter()
        .find(|slice| slice.name == "row_output_lengths")
        .expect("affected-row batch layout binds row output lengths");
    assert_eq!(row_output_lengths.mutability, Mutability::Mutable);
    assert_eq!(row_output_lengths.alias_policy, AliasPolicy::Exclusive);
    assert_eq!(
        row_output_lengths.bounds,
        PointerBounds::Symbol("affected_row_count".to_owned())
    );

    let decision = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &AYLraSparseAffectedRowBatchEvidence::private_local().with_canonical_hashes(
            &manifest,
            &proof_manifest,
            &evidence,
        ),
    );
    assert_eq!(decision.disposition, AYLraManifestDisposition::EmitManifest);
    assert!(decision.reasons.is_empty());
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);

    let mut missing_lengths = manifest.clone();
    missing_lengths.metadata.remove("row_output_lengths");
    missing_lengths.layout.metadata.remove("row_output_lengths");
    missing_lengths.invalidation.layout_checksum = missing_lengths.layout.checksum();
    missing_lengths.metadata.insert(
        "invalidation_checksum".to_owned(),
        missing_lengths.invalidation.checksum().to_string(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&missing_lengths, &proof_manifest);
    let affected_row_evidence = AYLraSparseAffectedRowBatchEvidence::private_local()
        .with_canonical_hashes(&missing_lengths, &proof_manifest, &evidence);
    assert_rejected_non_promoting(
        evaluate_ay_lra_sparse_affected_row_batch_evidence(
            &missing_lengths,
            &proof_manifest,
            &evidence,
            &affected_row_evidence,
        ),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );

    let mut bad_status_abi = manifest.clone();
    bad_status_abi.layout.metadata.insert(
        "status_abi".to_owned(),
        "ay_lra_sparse_affected_row_batch_status_abi_v0".to_owned(),
    );
    bad_status_abi.invalidation.layout_checksum = bad_status_abi.layout.checksum();
    bad_status_abi.metadata.insert(
        "invalidation_checksum".to_owned(),
        bad_status_abi.invalidation.checksum().to_string(),
    );
    let evidence = complete_ay_lra_consumption_evidence(&bad_status_abi, &proof_manifest);
    let affected_row_evidence = AYLraSparseAffectedRowBatchEvidence::private_local()
        .with_canonical_hashes(&bad_status_abi, &proof_manifest, &evidence);
    assert_rejected_non_promoting(
        evaluate_ay_lra_sparse_affected_row_batch_evidence(
            &bad_status_abi,
            &proof_manifest,
            &evidence,
            &affected_row_evidence,
        ),
        AYLraManifestRejectionReason::StatusSignatureMismatch,
    );

    let mut signature_changed = manifest.clone();
    signature_changed.symbols[0].signature =
        affected_row_batch_signature_with_nullable_status_pointer();
    assert_eq!(signature_changed.layout, manifest.layout);
    assert_eq!(signature_changed.invalidation, manifest.invalidation);
    assert_ne!(
        signature_changed.symbols[0].signature.checksum(),
        ay_lra_affected_row_batch_status_signature().checksum()
    );
    assert_ne!(signature_changed.checksum(), baseline_checksum);
}

#[test]
fn ay_lra_batch_manifest_binds_commit_policy_and_first_failure_status_contract() {
    let manifest = ay_lra_batch_manifest();
    let expected_signature = ay_lra_batch_status_signature();
    let baseline_checksum = manifest.checksum();
    let install_contract = SymbolLookupContract::new(
        BATCH_STATUS_SYMBOL,
        expected_signature.clone(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(baseline_checksum);

    assert_eq!(
        manifest.symbol_signature(BATCH_STATUS_SYMBOL),
        Some(&expected_signature)
    );
    assert_eq!(install_contract.symbol, BATCH_STATUS_SYMBOL);
    assert_eq!(install_contract.signature, expected_signature);
    assert_eq!(install_contract.target_checksum, manifest.target.checksum());
    assert_eq!(install_contract.abi_checksum, manifest.abi.checksum());
    assert_eq!(install_contract.layout_checksum, manifest.layout.checksum());
    assert_eq!(
        install_contract.invalidation_checksum,
        Some(manifest.invalidation.checksum())
    );
    assert_eq!(install_contract.manifest_checksum, Some(baseline_checksum));

    assert_eq!(manifest.layout.records[0].name, BATCH_STATUS_RECORD);
    assert_eq!(
        manifest.layout.metadata.get("kernel").map(String::as_str),
        Some("ay_lra_basis_row_batch")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("tableau_row_layout")
            .map(String::as_str),
        Some("ptrs_to_i64_rows_len5_stride40")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("basis_row_layout")
            .map(String::as_str),
        Some("basis_epoch_pair_current_expected")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("row_region_hash")
            .map(String::as_str),
        Some("pre_post_tableau_digest")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("scratch_rollback")
            .map(String::as_str),
        Some("row_lengths_as_commit_log_no_failed_row_rollback")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("rollback_failure_disposition")
            .map(String::as_str),
        Some("non_promoting_deopt_failed_row_left_uncommitted")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("alias_policy")
            .map(String::as_str),
        Some("exclusive_tableau_rows_shared_inputs")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("output_capacity")
            .map(String::as_str),
        Some("runtime_i64")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("commit_policy")
            .map(String::as_str),
        Some("partial_row_deopt")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("status_value")
            .map(String::as_str),
        Some("rows_completed")
    );
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("status_detail")
            .map(String::as_str),
        Some("first_failed_row")
    );
    assert_eq!(
        manifest.metadata.get("kernel").map(String::as_str),
        Some("ay_lra_basis_row_batch")
    );
    assert_eq!(
        manifest
            .metadata
            .get("tableau_row_layout")
            .map(String::as_str),
        Some("ptrs_to_i64_rows_len5_stride40")
    );
    assert_eq!(
        manifest
            .metadata
            .get("basis_row_layout")
            .map(String::as_str),
        Some("basis_epoch_pair_current_expected")
    );
    assert_eq!(
        manifest.metadata.get("row_region_hash").map(String::as_str),
        Some("pre_post_tableau_digest")
    );
    assert_eq!(
        manifest
            .metadata
            .get("scratch_rollback")
            .map(String::as_str),
        Some("row_lengths_as_commit_log_no_failed_row_rollback")
    );
    assert_eq!(
        manifest
            .metadata
            .get("rollback_failure_disposition")
            .map(String::as_str),
        Some("non_promoting_deopt_failed_row_left_uncommitted")
    );
    assert_eq!(
        manifest.metadata.get("alias_policy").map(String::as_str),
        Some("exclusive_tableau_rows_shared_inputs")
    );
    assert_eq!(
        manifest.metadata.get("commit_policy").map(String::as_str),
        Some("partial_row_deopt")
    );
    assert_eq!(
        manifest.metadata.get("output_capacity").map(String::as_str),
        Some("runtime_i64")
    );
    assert_eq!(
        manifest.metadata.get("status_value").map(String::as_str),
        Some("rows_completed")
    );
    assert_eq!(
        manifest.metadata.get("status_detail").map(String::as_str),
        Some("first_failed_row")
    );
    assert_eq!(
        manifest
            .metadata
            .get("proof_rejection_disposition")
            .map(String::as_str),
        Some("typed_lookup_rejects_before_callable_escape")
    );
    assert_eq!(
        manifest
            .metadata
            .get("replay_bundle_manifest_ref")
            .map(String::as_str),
        Some("replay/ay-lra-basis-row-batch/manifest.json")
    );
    assert_eq!(
        manifest
            .metadata
            .get("replay_bundle_proof_ref")
            .map(String::as_str),
        Some("proofs/ay-lra-basis-row-batch/proof-evidence.json")
    );
    assert_eq!(
        manifest
            .metadata
            .get("replay_bundle_telemetry_ref")
            .map(String::as_str),
        Some("telemetry/ay-lra-basis-row-batch/compile-telemetry.json")
    );
    assert_eq!(
        manifest
            .metadata
            .get("telemetry_counter_policy")
            .map(String::as_str),
        Some("metadata_only_useful_native_false")
    );
    assert_eq!(
        manifest.metadata.get("useful_native").map(String::as_str),
        Some("false")
    );
    assert_eq!(
        manifest
            .metadata
            .get("downstream_readiness")
            .map(String::as_str),
        Some("followup_issue_709")
    );
    assert_eq!(
        manifest
            .metadata
            .get("proof_consumption_manifest_schema")
            .map(String::as_str),
        Some(AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA)
    );
    assert_eq!(
        manifest
            .metadata
            .get("trust_ir_source_identity")
            .map(String::as_str),
        Some("trust_ir:ay:lra:basis-row-batch:v1")
    );
    assert!(
        manifest
            .metadata
            .get("required_proof_facts")
            .expect("basis manifest records required proof facts")
            .contains("batch_prefix_commit_rollback")
    );
    assert!(
        manifest
            .metadata
            .get("required_proof_lemmas")
            .expect("basis manifest records required lemmas")
            .contains("ay_lra_basis.batch_prefix_commit_rollback")
    );
    assert_eq!(
        manifest
            .metadata
            .get("future_proof_families")
            .map(String::as_str),
        Some("ay_chc_candidate_loop,ay_pb_candidate_loop,ay_sat_candidate_loop")
    );

    let tableau_row_ptrs = manifest
        .layout
        .slices
        .iter()
        .find(|slice| slice.name == "tableau_row_ptrs")
        .expect("batch layout binds tableau row pointers");
    assert_eq!(tableau_row_ptrs.mutability, Mutability::Mutable);
    assert_eq!(tableau_row_ptrs.alias_policy, AliasPolicy::Exclusive);
    assert_eq!(
        tableau_row_ptrs.bounds,
        PointerBounds::Symbol("affected_row_count".to_owned())
    );

    let row_scales = manifest
        .layout
        .slices
        .iter()
        .find(|slice| slice.name == "row_scales")
        .expect("batch layout binds immutable row scales");
    assert_eq!(row_scales.mutability, Mutability::Immutable);
    assert_eq!(row_scales.alias_policy, AliasPolicy::SharedReadOnly);
    assert_eq!(
        row_scales.bounds,
        PointerBounds::Symbol("affected_row_count".to_owned())
    );
    assert_eq!(expected_signature.params[1].kind, AbiValueKind::Ptr);

    let basis_epochs = manifest
        .layout
        .slices
        .iter()
        .find(|slice| slice.name == "basis_epochs")
        .expect("batch layout binds basis epoch pair");
    assert_eq!(basis_epochs.length, Some(2));
    assert_eq!(basis_epochs.mutability, Mutability::Immutable);
    assert_eq!(basis_epochs.alias_policy, AliasPolicy::SharedReadOnly);
    assert_eq!(expected_signature.params[6].kind, AbiValueKind::Ptr);

    let row_output_offsets = manifest
        .layout
        .slices
        .iter()
        .find(|slice| slice.name == "row_output_offsets")
        .expect("batch layout binds row output offsets");
    assert_eq!(row_output_offsets.mutability, Mutability::Immutable);
    assert_eq!(row_output_offsets.alias_policy, AliasPolicy::SharedReadOnly);
    assert_eq!(
        row_output_offsets.bounds,
        PointerBounds::Symbol("affected_row_count".to_owned())
    );

    let row_output_lengths = manifest
        .layout
        .slices
        .iter()
        .find(|slice| slice.name == "row_output_lengths")
        .expect("batch layout binds mutable row output lengths");
    assert_eq!(row_output_lengths.mutability, Mutability::Mutable);
    assert_eq!(row_output_lengths.alias_policy, AliasPolicy::Exclusive);
    assert_eq!(
        row_output_lengths.bounds,
        PointerBounds::Symbol("affected_row_count".to_owned())
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
            .get("tableau_row_ptrs")
            .map(String::as_str),
        Some("runtime")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("row_scales")
            .map(String::as_str),
        Some("runtime")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("basis_row_layout")
            .map(String::as_str),
        Some("basis_epoch_pair_current_expected")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("tableau_row_layout")
            .map(String::as_str),
        Some("ptrs_to_i64_rows_len5_stride40")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("row_region_hash")
            .map(String::as_str),
        Some("runtime_tableau_digest")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("scratch_rollback")
            .map(String::as_str),
        Some("row_lengths_as_commit_log_no_failed_row_rollback")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("rollback_failure_disposition")
            .map(String::as_str),
        Some("non_promoting_deopt_failed_row_left_uncommitted")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("row_output_offsets")
            .map(String::as_str),
        Some("runtime")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("row_output_lengths")
            .map(String::as_str),
        Some("mutable_runtime")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("output_capacity")
            .map(String::as_str),
        Some("runtime_i64")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("commit_policy")
            .map(String::as_str),
        Some("partial_row_deopt")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("status_value")
            .map(String::as_str),
        Some("rows_completed")
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get("status_detail")
            .map(String::as_str),
        Some("first_failed_row")
    );

    let mut commit_policy_changed = manifest.clone();
    commit_policy_changed
        .layout
        .metadata
        .insert("commit_policy".to_owned(), "all_or_rollback".to_owned());
    commit_policy_changed
        .metadata
        .insert("commit_policy".to_owned(), "all_or_rollback".to_owned());
    commit_policy_changed
        .invalidation
        .extra
        .insert("commit_policy".to_owned(), "all_or_rollback".to_owned());
    commit_policy_changed.invalidation.layout_checksum = commit_policy_changed.layout.checksum();
    assert_ne!(
        commit_policy_changed.layout.checksum(),
        manifest.layout.checksum()
    );
    assert_ne!(
        commit_policy_changed.invalidation.checksum(),
        manifest.invalidation.checksum()
    );
    assert_ne!(commit_policy_changed.checksum(), baseline_checksum);

    let mut row_output_mutability_changed = manifest.clone();
    let row_output_lengths = row_output_mutability_changed
        .layout
        .slices
        .iter_mut()
        .find(|slice| slice.name == "row_output_lengths")
        .expect("batch layout binds mutable row output lengths");
    row_output_lengths.mutability = Mutability::Immutable;
    row_output_lengths.alias_policy = AliasPolicy::SharedReadOnly;
    row_output_mutability_changed.invalidation.layout_checksum =
        row_output_mutability_changed.layout.checksum();
    assert_ne!(
        row_output_mutability_changed.layout.checksum(),
        manifest.layout.checksum()
    );
    assert_ne!(
        row_output_mutability_changed.invalidation.checksum(),
        manifest.invalidation.checksum()
    );
    assert_ne!(row_output_mutability_changed.checksum(), baseline_checksum);

    let mut output_capacity_changed = manifest.clone();
    output_capacity_changed
        .layout
        .metadata
        .insert("output_capacity".to_owned(), "compile_time_i64".to_owned());
    output_capacity_changed
        .metadata
        .insert("output_capacity".to_owned(), "compile_time_i64".to_owned());
    output_capacity_changed
        .invalidation
        .extra
        .insert("output_capacity".to_owned(), "compile_time_i64".to_owned());
    output_capacity_changed.invalidation.layout_checksum =
        output_capacity_changed.layout.checksum();
    assert_ne!(
        output_capacity_changed.layout.checksum(),
        manifest.layout.checksum()
    );
    assert_ne!(
        output_capacity_changed.invalidation.checksum(),
        manifest.invalidation.checksum()
    );
    assert_ne!(output_capacity_changed.checksum(), baseline_checksum);

    let mut signature_changed = manifest.clone();
    signature_changed.symbols[0].signature = batch_signature_with_nullable_status_pointer();
    assert_eq!(signature_changed.layout, manifest.layout);
    assert_eq!(signature_changed.invalidation, manifest.invalidation);
    assert_ne!(
        signature_changed.symbols[0].signature.checksum(),
        ay_lra_batch_status_signature().checksum()
    );
    assert_ne!(signature_changed.checksum(), baseline_checksum);
}
