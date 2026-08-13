// trust-cg-codegen/tests/jit_sparse_substitute_regression.rs
//
// Minimal Trust Codegen-owned sparse-substitute regression lifted from ay's trust_ir
// shape, but without depending on the ay repo. This specifically targets the
// sparse substitute "zero elimination" path where the carried output length
// must stay at 0 when the merged coefficient cancels to zero.

#![cfg(target_arch = "aarch64")]

#[path = "common/fixture_contract.rs"]
mod fixture_contract;
use fixture_contract::FixtureContractLookup;

use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};
use std::mem::{align_of, offset_of, size_of};
use std::time::Instant;

use trust_cg_codegen::Target;
use trust_cg_codegen::ay_lra_proof_manifest::{
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_FIRST_FAILED_ROW,
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_OVERFLOW_DEOPTS,
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_PARTIAL_ROW_DEOPTS,
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_ROWS_ATTEMPTED,
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_ROWS_COMMITTED, AY_LRA_BASIS_ROW_BATCH_TELEMETRY_STALE_DEOPTS,
    AY_LRA_BASIS_ROW_BATCH_TELEMETRY_USEFUL_NATIVE_DELTA,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_BOUNDS_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_FIRST_FAILED_ROWS,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OK_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OVERFLOW_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED_TOTAL,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_STALE_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_USEFUL_NATIVE_DELTA, AYLraAarch64LoweringDecision,
    AYLraBasisEpochEvidence, AYLraBasisRowBatchTelemetryEvidence, AYLraEvidenceAvailability,
    AYLraKernelProofConsumptionManifest, AYLraManifestDisposition, AYLraManifestRejectionReason,
    AYLraProductGateEvidence, AYLraProofConsumptionEvidence, AYLraReplayComparison,
    AYLraRequirementAvailability, AYLraSparseAffectedRowBatchEvidence,
    ay_lra_basis_update_proof_manifest, ay_lra_proof_fact_metadata_key,
    ay_lra_sparse_affected_row_batch_proof_manifest,
    evaluate_ay_lra_basis_row_batch_telemetry_evidence,
    evaluate_ay_lra_sparse_affected_row_batch_evidence, select_ay_lra_aarch64_lowering,
};
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, AliasPolicy, ArtifactChecksum, ArtifactContractError,
    ArtifactSection, ArtifactSectionKind, ArtifactSymbol, DeterministicArtifactManifest,
    Endianness, FieldLayout, InvalidationKey, JitArtifactKind, LayoutManifest, Mutability,
    PointerBounds, PointerLayout, ProofEvidenceRejectionCode, ProofEvidenceSummary,
    ProofEvidenceVerdict, ProofMode, ProofPolicy, RecordLayout, SliceLayout, SymbolLayout,
    SymbolLookupContract, SymbolSignature, SymbolVisibility, TargetArchitecture, TargetDescriptor,
    TargetOperatingSystem,
};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function};
use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::AArch64Opcode;
use trust_cg_verify::{
    AY_LRA_BASIS_UPDATE_KERNEL_FAMILY, AYLraRewriteKernelFamily, CandidateRegionExtractionInput,
    CegisResult, CertificateIdentity, ConcreteInput, CostContext, FailedProofCounterexampleCorpus,
    FailedProofCounterexampleSeedFilter, FailedProofReducerArtifact, KernelAllowlist,
    ProductGateEvidence, ProofFailureKind, ProofGuidedAdmissionVerdict, ReducerMetadata,
    TargetAbiLayoutIdentity, TransformIdentity, extract_rewrite_admission_candidate,
};
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{BinOp, Block, Constant, Function, ICmpOp, Inst, InstrNode, Module, OverflowOp, Ty};

const SPARSE_SUBSTITUTE_SYMBOL: &str = "substitute_var_specialized";
const PIVOT_ROW_SYMBOL: &str = "pivot_row_update";
const BATCH_PIVOT_SYMBOL: &str = "batch_pivot_update";
const BATCH_PIVOT_STATUS_SYMBOL: &str = "ay_lra_basis_row_batch";
const BATCH_STATUS_RECORD: &str = "AYLraBasisRowBatchStatusAbi";
const AFFECTED_ROW_BATCH_STATUS_SYMBOL: &str = "ay_lra_sparse_affected_row_batch_status_probe";
const AFFECTED_ROW_BATCH_STATUS_RECORD: &str = "AYLraSparseAffectedRowBatchStatusAbi";
const AY_LRA_BASIS_SUB_ZERO_TRANSFORM: &str = "ay_lra_basis_sub_zero";
const AY_LRA_BASIS_SUB_ZERO_PROOF_HASH: u64 = 0xba5e;
const AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH: &str = "0000000000000000ba5eba5ecafed00d";
const AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH: &str = "0000000000000000000000000000ba5e";
const CANONICAL_TELEMETRY_SHA256: &str =
    "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

type SparseSubstituteFn =
    unsafe extern "C" fn(*const u32, *const i64, i64, i64, *mut u32, *mut i64) -> i64;
type PivotRowFn = unsafe extern "C" fn(*mut i64, i64);
type BatchPivotFn = unsafe extern "C" fn(*const *mut i64, *const i64, i64) -> i64;
type BatchPivotStatusFn = unsafe extern "C" fn(
    *const *mut i64,
    *const i64,
    i64,
    *const i64,
    *mut i64,
    i64,
    *const i64,
    *mut AYLraBatchStatusAbi,
);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
#[repr(u8)]
enum AYLraStatus {
    Ok = 0,
    Bounds = 1,
    Overflow = 2,
    Stale = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
#[repr(u8)]
enum AYLraDeopt {
    None = 0,
    SparseSubstituteBounds = 1,
    SparseSubstituteOverflow = 2,
    BasisEpochStale = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
struct AYLraBatchStatusAbi {
    status: u8,
    deopt: u8,
    reserved: [u8; 6],
    rows_committed: i64,
    detail: i64,
}

impl AYLraBatchStatusAbi {
    const fn poisoned() -> Self {
        Self {
            status: 0xff,
            deopt: 0xff,
            reserved: [0xaa; 6],
            rows_committed: i64::MIN,
            detail: i64::MIN,
        }
    }

    fn assert_matches(
        &self,
        status: AYLraStatus,
        deopt: AYLraDeopt,
        rows_committed: i64,
        detail: i64,
    ) {
        assert_eq!(self.status, status as u8);
        assert_eq!(self.deopt, deopt as u8);
        assert_eq!(self.reserved, [0xaa; 6]);
        assert_eq!(self.rows_committed, rows_committed);
        assert_eq!(self.detail, detail);
    }
}

fn i64_value() -> AbiValue {
    AbiValue::new(AbiValueKind::I64)
}

fn i32_value() -> AbiValue {
    AbiValue::new(AbiValueKind::I32)
}

fn ptr_value() -> AbiValue {
    AbiValue::new(AbiValueKind::Ptr)
}

fn ay_lra_sparse_substitute_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            ptr_value(), // target vars: *const u32
            ptr_value(), // target coeffs: *const i64
            i64_value(), // target length
            i64_value(), // pivot scale
            ptr_value(), // out vars: *mut u32
            ptr_value(), // out coeffs: *mut i64
        ],
        vec![i64_value()],
    )
}

fn ay_lra_pivot_row_signature() -> SymbolSignature {
    SymbolSignature::extern_c(vec![ptr_value(), i64_value()], vec![])
}

fn ay_lra_batch_pivot_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![ptr_value(), ptr_value(), i64_value()],
        vec![i64_value()],
    )
}

fn ay_lra_batch_pivot_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            ptr_value(), // row pointers
            ptr_value(), // row scales
            i64_value(), // row count
            ptr_value(), // row output offsets
            ptr_value(), // mutable row output lengths
            i64_value(), // output capacity
            ptr_value(), // [current basis epoch, expected basis epoch]
            ptr_value(), // AYLraBatchStatusAbi*
        ],
        vec![],
    )
}

fn ay_lra_affected_row_batch_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            i64_value(), // affected row count
            i64_value(), // output capacity per row
            i64_value(), // synthetic status mode
            i64_value(), // current basis epoch
            i64_value(), // expected basis epoch
            ptr_value(), // mutable per-row output lengths
            ptr_value(), // AYLraSparseAffectedRowBatchStatusAbi*
        ],
        vec![],
    )
}

fn ay_lra_kernel_signature(symbol: &str) -> SymbolSignature {
    match symbol {
        SPARSE_SUBSTITUTE_SYMBOL => ay_lra_sparse_substitute_signature(),
        PIVOT_ROW_SYMBOL => ay_lra_pivot_row_signature(),
        BATCH_PIVOT_SYMBOL => ay_lra_batch_pivot_signature(),
        BATCH_PIVOT_STATUS_SYMBOL => ay_lra_batch_pivot_status_signature(),
        other => panic!("unknown ay LRA product-kernel symbol {other}"),
    }
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
        size_bytes: size_of::<AYLraBatchStatusAbi>() as u64,
        alignment_bytes: align_of::<AYLraBatchStatusAbi>() as u32,
        fields: vec![
            FieldLayout {
                name: "status".to_owned(),
                offset_bytes: offset_of!(AYLraBatchStatusAbi, status) as u64,
                size_bytes: size_of::<u8>() as u64,
                alignment_bytes: align_of::<u8>() as u32,
            },
            FieldLayout {
                name: "deopt".to_owned(),
                offset_bytes: offset_of!(AYLraBatchStatusAbi, deopt) as u64,
                size_bytes: size_of::<u8>() as u64,
                alignment_bytes: align_of::<u8>() as u32,
            },
            FieldLayout {
                name: "reserved".to_owned(),
                offset_bytes: offset_of!(AYLraBatchStatusAbi, reserved) as u64,
                size_bytes: size_of::<[u8; 6]>() as u64,
                alignment_bytes: align_of::<[u8; 6]>() as u32,
            },
            FieldLayout {
                name: "rows_committed".to_owned(),
                offset_bytes: offset_of!(AYLraBatchStatusAbi, rows_committed) as u64,
                size_bytes: size_of::<i64>() as u64,
                alignment_bytes: align_of::<i64>() as u32,
            },
            FieldLayout {
                name: "detail".to_owned(),
                offset_bytes: offset_of!(AYLraBatchStatusAbi, detail) as u64,
                size_bytes: size_of::<i64>() as u64,
                alignment_bytes: align_of::<i64>() as u32,
            },
        ],
    }
}

fn ay_lra_affected_row_batch_status_record_layout() -> RecordLayout {
    let mut layout = ay_lra_batch_status_record_layout();
    layout.name = AFFECTED_ROW_BATCH_STATUS_RECORD.to_owned();
    let first_failed_row = layout
        .fields
        .last_mut()
        .expect("status layout includes a final detail field");
    first_failed_row.name = "first_failed_row".to_owned();
    layout
}

fn ay_lra_batch_i64_slice(name: &str, mutability: Mutability) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes: size_of::<i64>() as u64,
        element_alignment_bytes: align_of::<i64>() as u32,
        stride_bytes: size_of::<i64>() as u64,
        length: None,
        bounds: PointerBounds::Symbol("row_count".to_owned()),
        mutability,
        alias_policy: match mutability {
            Mutability::Immutable => AliasPolicy::SharedReadOnly,
            Mutability::Mutable => AliasPolicy::Exclusive,
        },
    }
}

fn ay_lra_affected_row_batch_i64_slice(name: &str, mutability: Mutability) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes: size_of::<i64>() as u64,
        element_alignment_bytes: align_of::<i64>() as u32,
        stride_bytes: size_of::<i64>() as u64,
        length: None,
        bounds: PointerBounds::Symbol("affected_row_count".to_owned()),
        mutability,
        alias_policy: match mutability {
            Mutability::Immutable => AliasPolicy::SharedReadOnly,
            Mutability::Mutable => AliasPolicy::Exclusive,
        },
    }
}

fn ay_lra_kernel_proof_policy() -> ProofPolicy {
    let mut policy = ProofPolicy::disabled();
    policy.mode = ProofMode::AuditOnly;
    policy.require_jit_certificate = true;
    policy.require_layout_evidence = true;
    policy.require_abi_evidence = true;
    policy.accepted_solvers = vec!["trust-cg-verify".to_owned(), "ay".to_owned()];
    policy
}

fn ay_lra_kernel_manifest_for(
    symbol: &str,
    kernel: &str,
    signature: SymbolSignature,
    include_status_record: bool,
    section_size_bytes: u64,
) -> DeterministicArtifactManifest {
    let target = ay_lra_target();
    let abi = ay_lra_abi();
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some(format!("ay::lra::{kernel}::lp64:v1"));
    layout.symbols.push(SymbolLayout {
        name: symbol.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: section_size_bytes,
        alignment_bytes: 16,
    });
    if include_status_record {
        layout.records.push(ay_lra_batch_status_record_layout());
        layout.slices.push(ay_lra_batch_i64_slice(
            "row_output_offsets",
            Mutability::Immutable,
        ));
        layout.slices.push(ay_lra_batch_i64_slice(
            "row_output_lengths",
            Mutability::Mutable,
        ));
        layout.metadata.insert(
            "status_abi".to_owned(),
            "ay_lra_basis_row_batch_status_abi_v1".to_owned(),
        );
        layout
            .metadata
            .insert("commit_policy".to_owned(), "partial_row_deopt".to_owned());
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
        layout.metadata.insert(
            "row_output_offsets".to_owned(),
            "runtime_capacity_offsets".to_owned(),
        );
        layout.metadata.insert(
            "row_output_lengths".to_owned(),
            "mutable_runtime_lengths".to_owned(),
        );
        layout
            .metadata
            .insert("output_capacity".to_owned(), "runtime_i64".to_owned());
        layout
            .metadata
            .insert("status_value".to_owned(), "rows_completed".to_owned());
        layout
            .metadata
            .insert("status_detail".to_owned(), "first_failed_row".to_owned());
    }
    layout
        .metadata
        .insert("kernel".to_owned(), kernel.to_owned());
    layout.metadata.insert(
        "signature_checksum".to_owned(),
        signature.checksum().to_string(),
    );
    layout.metadata.insert(
        "lookup_contract".to_owned(),
        "manifest-backed-typed-symbol-v1".to_owned(),
    );

    let proof_policy = ay_lra_kernel_proof_policy();
    let mut invalidation = InvalidationKey::new(
        format!("ay:lra:{kernel}:trust_ir-fixture-v1"),
        "trust-cg:jit-sparse-substitute-regression:o0-o2",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        708,
    );
    invalidation
        .extra
        .insert("basis_epoch".to_owned(), "runtime".to_owned());
    if include_status_record {
        invalidation
            .extra
            .insert("commit_policy".to_owned(), "partial_row_deopt".to_owned());
        invalidation.extra.insert(
            "tableau_row_layout".to_owned(),
            "ptrs_to_i64_rows_len5_stride40".to_owned(),
        );
        invalidation.extra.insert(
            "basis_row_layout".to_owned(),
            "basis_epoch_pair_current_expected".to_owned(),
        );
        invalidation.extra.insert(
            "row_region_hash".to_owned(),
            "runtime_tableau_digest".to_owned(),
        );
        invalidation.extra.insert(
            "rollback_failure_disposition".to_owned(),
            "non_promoting_deopt_failed_row_left_uncommitted".to_owned(),
        );
        invalidation.extra.insert(
            "row_output_offsets".to_owned(),
            "runtime_capacity_offsets".to_owned(),
        );
        invalidation.extra.insert(
            "row_output_lengths".to_owned(),
            "mutable_runtime_lengths".to_owned(),
        );
        invalidation
            .extra
            .insert("output_capacity".to_owned(), "runtime_i64".to_owned());
        invalidation
            .extra
            .insert("status_detail".to_owned(), "first_failed_row".to_owned());
        invalidation
            .extra
            .insert("status_value".to_owned(), "rows_completed".to_owned());
    }
    invalidation.extra.insert(
        "lookup_contract".to_owned(),
        "manifest-backed-typed-symbol-v1".to_owned(),
    );

    let mut manifest = DeterministicArtifactManifest::new(
        format!("ay-lra-{kernel}-product-kernel"),
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
        offset_bytes: Some(0),
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
        .insert("consumer".to_owned(), "ay".to_owned());
    manifest
        .metadata
        .insert("issue".to_owned(), "708".to_owned());
    manifest.metadata.insert(
        "disposition".to_owned(),
        "manifest-backed typed lookup; audit-only proof evidence in this regression fixture"
            .to_owned(),
    );
    if include_status_record {
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
    }
    manifest
}

fn ay_lra_kernel_manifest(symbol: &str) -> DeterministicArtifactManifest {
    match symbol {
        SPARSE_SUBSTITUTE_SYMBOL => ay_lra_kernel_manifest_for(
            symbol,
            "sparse_substitute",
            ay_lra_sparse_substitute_signature(),
            false,
            4096,
        ),
        PIVOT_ROW_SYMBOL => ay_lra_kernel_manifest_for(
            symbol,
            "pivot_row_update",
            ay_lra_pivot_row_signature(),
            false,
            1024,
        ),
        BATCH_PIVOT_SYMBOL => ay_lra_kernel_manifest_for(
            symbol,
            "batch_pivot_update",
            ay_lra_batch_pivot_signature(),
            false,
            2048,
        ),
        BATCH_PIVOT_STATUS_SYMBOL => ay_lra_kernel_manifest_for(
            symbol,
            "basis_row_batch",
            ay_lra_batch_pivot_status_signature(),
            true,
            2048,
        ),
        other => panic!("unknown ay LRA product-kernel symbol {other}"),
    }
}

fn ay_lra_sparse_affected_row_batch_manifest() -> DeterministicArtifactManifest {
    let proof_manifest = ay_lra_sparse_affected_row_batch_proof_manifest();
    let target = ay_lra_target();
    let abi = ay_lra_abi();
    let signature = ay_lra_affected_row_batch_status_signature();
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some("ay::lra::SparseAffectedRowBatchKernel::lp64:v1".to_owned());
    layout
        .records
        .push(ay_lra_affected_row_batch_status_record_layout());
    layout.slices.push(ay_lra_affected_row_batch_i64_slice(
        "row_output_lengths",
        Mutability::Mutable,
    ));
    layout.pointers.push(PointerLayout {
        name: "batch_status_out".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: size_of::<AYLraBatchStatusAbi>() as u64,
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

    let proof_policy = ay_lra_kernel_proof_policy();
    let mut invalidation = InvalidationKey::new(
        "ay:lra:sparse-affected-row-batch:status-probe-v1",
        "trust-cg:jit-sparse-substitute-regression:o0-o2",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        953,
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
        signature,
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
    manifest.metadata.insert(
        "trust_ir_source_identity".to_owned(),
        "trust_ir:ay:lra:sparse-affected-row-batch:v1".to_owned(),
    );
    manifest.metadata.insert(
        "source_policy".to_owned(),
        "approved_private_source".to_owned(),
    );
    manifest.metadata.insert(
        "approved_private_source_policy".to_owned(),
        "issue_796_internal_source_lock_v1".to_owned(),
    );
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
        "required_certificate_dependencies".to_owned(),
        proof_manifest.required_certificate_csv(),
    );
    manifest.metadata.insert(
        "future_proof_status".to_owned(),
        "missing_future".to_owned(),
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
    manifest
}

fn ay_lra_kernel_lookup_contract_for(
    manifest: &DeterministicArtifactManifest,
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

fn ay_lra_kernel_lookup_contract(
    manifest: &DeterministicArtifactManifest,
    symbol: &str,
) -> SymbolLookupContract {
    ay_lra_kernel_lookup_contract_for(manifest, symbol, ay_lra_kernel_signature(symbol))
}

#[allow(clippy::result_large_err)] // Test binder preserves the production contract error.
fn bind_ay_lra_product_kernel<F: Copy>(
    buffer: &trust_cg_codegen::ExecutableBuffer,
    symbol: &str,
) -> Result<F, ArtifactContractError> {
    let manifest = ay_lra_kernel_manifest(symbol);
    let contract = ay_lra_kernel_lookup_contract(&manifest, symbol);
    let typed = buffer.get_fixture_contract_symbol_bound::<F>(&manifest, &contract)?;
    assert_eq!(typed.symbol(), symbol);
    assert_eq!(typed.signature(), &contract.signature);
    assert_eq!(typed.artifact_checksum(), manifest.checksum());
    // SAFETY: the function pointer escapes only after manifest-backed ABI,
    // layout, invalidation, manifest, signature, and non-null checks pass.
    Ok(unsafe { typed.into_fn() })
}

#[derive(Debug, Default)]
struct SparseCodeShape {
    real_inst_count: usize,
    encoded_bytes: usize,
    spill_slot_count: usize,
    branch_count: usize,
    cond_branch_count: usize,
    madd_count: usize,
    mul_count: usize,
    smulh_count: usize,
    lsl_ri_count: usize,
    add_rr_count: usize,
    adds_count: usize,
    subs_count: usize,
    cset_count: usize,
    load_count: usize,
    store_count: usize,
    /// Register-offset loads/stores (`LdrRO`/`StrRO`). The late ext-addr
    /// fold rewrites the row-indexing `SXTW/MADD + LDR/STR [addr]` chains
    /// into extended-register addressing, so row indexing shows up here
    /// instead of in `madd_count`.
    reg_offset_mem_count: usize,
}

struct TrustIrBuilder {
    next_value: u32,
    blocks: Vec<Block>,
    current_block: BlockId,
    current_body: Vec<InstrNode>,
}

impl TrustIrBuilder {
    fn new(entry_block: BlockId) -> Self {
        Self {
            next_value: 0,
            blocks: Vec::new(),
            current_block: entry_block,
            current_body: Vec::new(),
        }
    }

    fn fresh_value(&mut self) -> ValueId {
        let id = ValueId(self.next_value);
        self.next_value += 1;
        id
    }

    fn reserve_params(&mut self, count: u32) -> Vec<ValueId> {
        (0..count).map(|_| self.fresh_value()).collect()
    }

    fn emit(&mut self, inst: Inst) -> ValueId {
        let result = self.fresh_value();
        let node = InstrNode::new(inst).with_result(result);
        self.current_body.push(node);
        result
    }

    fn emit_void(&mut self, inst: Inst) {
        self.current_body.push(InstrNode::new(inst));
    }

    fn const_i64(&mut self, value: i64) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::I64,
            value: Constant::i64(value),
        })
    }

    fn const_i32(&mut self, value: i32) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::I32,
            value: Constant::i32(value),
        })
    }

    fn const_u64(&mut self, value: i64) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::I64,
            value: Constant::i64(value),
        })
    }

    fn const_int(&mut self, ty: Ty, value: i128) -> ValueId {
        self.emit(Inst::Const {
            ty,
            value: Constant::Int(value),
        })
    }

    fn binop(&mut self, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::BinOp { op, ty, lhs, rhs })
    }

    fn overflow(
        &mut self,
        op: OverflowOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> (ValueId, ValueId) {
        let value = self.fresh_value();
        let flag = self.fresh_value();
        let node = InstrNode::new(Inst::Overflow { op, ty, lhs, rhs })
            .with_result(value)
            .with_result(flag);
        self.current_body.push(node);
        (value, flag)
    }

    fn load(&mut self, ty: Ty, ptr: ValueId) -> ValueId {
        self.emit(Inst::Load {
            ty,
            ptr,
            volatile: false,
            align: None,
        })
    }

    fn store(&mut self, ty: Ty, ptr: ValueId, value: ValueId) {
        self.emit_void(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: None,
        });
    }

    fn index(&mut self, pointee_ty: Ty, base: ValueId, index: ValueId) -> ValueId {
        self.emit(Inst::GEP {
            pointee_ty,
            base,
            indices: vec![index],
            inbounds: false,
        })
    }

    fn icmp(&mut self, op: ICmpOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::ICmp { op, ty, lhs, rhs })
    }

    fn seal_block(&mut self) {
        let body = std::mem::take(&mut self.current_body);
        let mut block = Block::new(self.current_block);
        block.body = body;
        self.blocks.push(block);
    }

    fn seal_block_with_params(&mut self, params: Vec<(ValueId, Ty)>) {
        let body = std::mem::take(&mut self.current_body);
        let mut block = Block::new(self.current_block);
        for (vid, ty) in params {
            block = block.with_param(vid, ty);
        }
        block.body = body;
        self.blocks.push(block);
    }

    fn start_block(&mut self, id: BlockId) {
        self.current_block = id;
    }
}

fn fresh_block(next_block: &mut u32) -> BlockId {
    let id = BlockId(*next_block);
    *next_block += 1;
    id
}

fn load_sparse_var(b: &mut TrustIrBuilder, target_vars: ValueId, row_idx: ValueId) -> ValueId {
    let addr = b.index(Ty::I32, target_vars, row_idx);
    b.load(Ty::I32, addr)
}

fn load_sparse_coeff(b: &mut TrustIrBuilder, target_coeffs: ValueId, row_idx: ValueId) -> ValueId {
    let addr = b.index(Ty::I64, target_coeffs, row_idx);
    b.load(Ty::I64, addr)
}

fn store_sparse_output(
    b: &mut TrustIrBuilder,
    out_vars: ValueId,
    out_coeffs: ValueId,
    out_idx: ValueId,
    var: ValueId,
    coeff: ValueId,
) {
    let var_addr = b.index(Ty::I32, out_vars, out_idx);
    b.store(Ty::I32, var_addr, var);

    let coeff_addr = b.index(Ty::I64, out_coeffs, out_idx);
    b.store(Ty::I64, coeff_addr, coeff);
}

fn batch_status_field_ptr(b: &mut TrustIrBuilder, out: ValueId, byte_offset: i64) -> ValueId {
    if byte_offset == 0 {
        out
    } else {
        let idx = b.const_int(Ty::U64, i128::from(byte_offset));
        b.index(Ty::U8, out, idx)
    }
}

fn store_batch_status_u8(b: &mut TrustIrBuilder, out: ValueId, byte_offset: i64, value: u8) {
    let ptr = batch_status_field_ptr(b, out, byte_offset);
    let value = b.const_int(Ty::U8, i128::from(value));
    b.store(Ty::U8, ptr, value);
}

fn store_batch_status_i64(b: &mut TrustIrBuilder, out: ValueId, byte_offset: i64, value: ValueId) {
    let ptr = batch_status_field_ptr(b, out, byte_offset);
    b.store(Ty::I64, ptr, value);
}

fn write_batch_status_record(
    b: &mut TrustIrBuilder,
    out: ValueId,
    status: AYLraStatus,
    deopt: AYLraDeopt,
    rows_committed: ValueId,
    detail: ValueId,
) {
    store_batch_status_u8(b, out, 0, status as u8);
    store_batch_status_u8(b, out, 1, deopt as u8);
    store_batch_status_i64(b, out, 8, rows_committed);
    store_batch_status_i64(b, out, 16, detail);
}

fn emit_single_pivot_sparse_substitute_trust_ir(
    pivot_var: u32,
    pivot_coeff: i64,
    entering_var: u32,
) -> Module {
    let entry_block = BlockId(0);
    let overflow_exit = BlockId(1);
    let mut next_block = 2;

    let copy_header = fresh_block(&mut next_block);
    let copy_check_lt = fresh_block(&mut next_block);
    let copy_check_entering = fresh_block(&mut next_block);
    let copy_do = fresh_block(&mut next_block);
    let copy_advance = fresh_block(&mut next_block);
    let skip_ev_header = fresh_block(&mut next_block);
    let skip_ev_check = fresh_block(&mut next_block);
    let skip_ev_advance = fresh_block(&mut next_block);
    let check_match = fresh_block(&mut next_block);
    let match_mul = fresh_block(&mut next_block);
    let match_add = fresh_block(&mut next_block);
    let match_sum = fresh_block(&mut next_block);
    let match_write = fresh_block(&mut next_block);
    let no_match = fresh_block(&mut next_block);
    let no_match_check = fresh_block(&mut next_block);
    let no_match_write = fresh_block(&mut next_block);
    let tail_header = fresh_block(&mut next_block);
    let tail_check_entering = fresh_block(&mut next_block);
    let tail_copy = fresh_block(&mut next_block);
    let return_success = fresh_block(&mut next_block);

    let mut b = TrustIrBuilder::new(entry_block);
    let params = b.reserve_params(6);
    let target_vars = params[0];
    let target_coeffs = params[1];
    let target_len = params[2];
    let scale = params[3];
    let out_vars = params[4];
    let out_coeffs = params[5];

    let zero_idx = b.const_u64(0);
    let one_idx = b.const_u64(1);
    let zero_coeff = b.const_i64(0);
    let entering_val = b.const_i32(entering_var as i32);
    let pivot_var_val = b.const_i32(pivot_var as i32);
    let pivot_coeff_val = b.const_i64(pivot_coeff);

    b.emit_void(Inst::Br {
        target: copy_header,
        args: vec![zero_idx, zero_idx],
    });
    b.seal_block_with_params(vec![
        (target_vars, Ty::Ptr),
        (target_coeffs, Ty::Ptr),
        (target_len, Ty::I64),
        (scale, Ty::I64),
        (out_vars, Ty::Ptr),
        (out_coeffs, Ty::Ptr),
    ]);

    let hdr_ti = b.fresh_value();
    let hdr_oi = b.fresh_value();
    b.start_block(copy_header);
    let in_bounds = b.icmp(ICmpOp::Ult, Ty::I64, hdr_ti, target_len);
    b.emit_void(Inst::CondBr {
        cond: in_bounds,
        then_target: copy_check_lt,
        then_args: vec![hdr_ti, hdr_oi],
        else_target: skip_ev_header,
        else_args: vec![hdr_ti, hdr_oi],
    });
    b.seal_block_with_params(vec![(hdr_ti, Ty::I64), (hdr_oi, Ty::I64)]);

    let lt_ti = b.fresh_value();
    let lt_oi = b.fresh_value();
    b.start_block(copy_check_lt);
    let target_var = load_sparse_var(&mut b, target_vars, lt_ti);
    let target_lt_pivot = b.icmp(ICmpOp::Ult, Ty::I32, target_var, pivot_var_val);
    b.emit_void(Inst::CondBr {
        cond: target_lt_pivot,
        then_target: copy_check_entering,
        then_args: vec![lt_ti, lt_oi],
        else_target: skip_ev_header,
        else_args: vec![lt_ti, lt_oi],
    });
    b.seal_block_with_params(vec![(lt_ti, Ty::I64), (lt_oi, Ty::I64)]);

    let ce_ti = b.fresh_value();
    let ce_oi = b.fresh_value();
    b.start_block(copy_check_entering);
    let copy_var = load_sparse_var(&mut b, target_vars, ce_ti);
    let is_entering = b.icmp(ICmpOp::Eq, Ty::I32, copy_var, entering_val);
    b.emit_void(Inst::CondBr {
        cond: is_entering,
        then_target: copy_advance,
        then_args: vec![ce_ti, ce_oi],
        else_target: copy_do,
        else_args: vec![ce_ti, ce_oi],
    });
    b.seal_block_with_params(vec![(ce_ti, Ty::I64), (ce_oi, Ty::I64)]);

    let cd_ti = b.fresh_value();
    let cd_oi = b.fresh_value();
    b.start_block(copy_do);
    let copied_var = load_sparse_var(&mut b, target_vars, cd_ti);
    let copied_coeff = load_sparse_coeff(&mut b, target_coeffs, cd_ti);
    store_sparse_output(
        &mut b,
        out_vars,
        out_coeffs,
        cd_oi,
        copied_var,
        copied_coeff,
    );
    let next_oi_after_copy = b.binop(BinOp::Add, Ty::I64, cd_oi, one_idx);
    b.emit_void(Inst::Br {
        target: copy_advance,
        args: vec![cd_ti, next_oi_after_copy],
    });
    b.seal_block_with_params(vec![(cd_ti, Ty::I64), (cd_oi, Ty::I64)]);

    let ca_ti = b.fresh_value();
    let ca_oi = b.fresh_value();
    b.start_block(copy_advance);
    let next_ti_after_copy = b.binop(BinOp::Add, Ty::I64, ca_ti, one_idx);
    b.emit_void(Inst::Br {
        target: copy_header,
        args: vec![next_ti_after_copy, ca_oi],
    });
    b.seal_block_with_params(vec![(ca_ti, Ty::I64), (ca_oi, Ty::I64)]);

    let se_ti = b.fresh_value();
    let se_oi = b.fresh_value();
    b.start_block(skip_ev_header);
    let skip_in_bounds = b.icmp(ICmpOp::Ult, Ty::I64, se_ti, target_len);
    b.emit_void(Inst::CondBr {
        cond: skip_in_bounds,
        then_target: skip_ev_check,
        then_args: vec![se_ti, se_oi],
        else_target: no_match,
        else_args: vec![se_ti, se_oi],
    });
    b.seal_block_with_params(vec![(se_ti, Ty::I64), (se_oi, Ty::I64)]);

    let sec_ti = b.fresh_value();
    let sec_oi = b.fresh_value();
    b.start_block(skip_ev_check);
    let skip_var = load_sparse_var(&mut b, target_vars, sec_ti);
    let still_entering = b.icmp(ICmpOp::Eq, Ty::I32, skip_var, entering_val);
    b.emit_void(Inst::CondBr {
        cond: still_entering,
        then_target: skip_ev_advance,
        then_args: vec![sec_ti, sec_oi],
        else_target: check_match,
        else_args: vec![sec_ti, sec_oi],
    });
    b.seal_block_with_params(vec![(sec_ti, Ty::I64), (sec_oi, Ty::I64)]);

    let sea_ti = b.fresh_value();
    let sea_oi = b.fresh_value();
    b.start_block(skip_ev_advance);
    let next_ti_after_skip = b.binop(BinOp::Add, Ty::I64, sea_ti, one_idx);
    b.emit_void(Inst::Br {
        target: skip_ev_header,
        args: vec![next_ti_after_skip, sea_oi],
    });
    b.seal_block_with_params(vec![(sea_ti, Ty::I64), (sea_oi, Ty::I64)]);

    let cm_ti = b.fresh_value();
    let cm_oi = b.fresh_value();
    b.start_block(check_match);
    let match_var = load_sparse_var(&mut b, target_vars, cm_ti);
    let is_match = b.icmp(ICmpOp::Eq, Ty::I32, match_var, pivot_var_val);
    b.emit_void(Inst::CondBr {
        cond: is_match,
        then_target: match_mul,
        then_args: vec![cm_ti, cm_oi],
        else_target: no_match,
        else_args: vec![cm_ti, cm_oi],
    });
    b.seal_block_with_params(vec![(cm_ti, Ty::I64), (cm_oi, Ty::I64)]);

    let mm_ti = b.fresh_value();
    let mm_oi = b.fresh_value();
    b.start_block(match_mul);
    let (product, mul_overflow) =
        b.overflow(OverflowOp::MulOverflow, Ty::I64, scale, pivot_coeff_val);
    b.emit_void(Inst::CondBr {
        cond: mul_overflow,
        then_target: overflow_exit,
        then_args: vec![],
        else_target: match_add,
        else_args: vec![mm_ti, mm_oi, product],
    });
    b.seal_block_with_params(vec![(mm_ti, Ty::I64), (mm_oi, Ty::I64)]);

    let ma_ti = b.fresh_value();
    let ma_oi = b.fresh_value();
    let ma_product = b.fresh_value();
    b.start_block(match_add);
    let old_coeff = load_sparse_coeff(&mut b, target_coeffs, ma_ti);
    let (sum, add_overflow) = b.overflow(OverflowOp::AddOverflow, Ty::I64, old_coeff, ma_product);
    b.emit_void(Inst::CondBr {
        cond: add_overflow,
        then_target: overflow_exit,
        then_args: vec![],
        else_target: match_sum,
        else_args: vec![ma_ti, ma_oi, sum],
    });
    b.seal_block_with_params(vec![
        (ma_ti, Ty::I64),
        (ma_oi, Ty::I64),
        (ma_product, Ty::I64),
    ]);

    let ms_ti = b.fresh_value();
    let ms_oi = b.fresh_value();
    let ms_sum = b.fresh_value();
    b.start_block(match_sum);
    let sum_nonzero = b.icmp(ICmpOp::Ne, Ty::I64, ms_sum, zero_coeff);
    let next_ti_after_match = b.binop(BinOp::Add, Ty::I64, ms_ti, one_idx);
    b.emit_void(Inst::CondBr {
        cond: sum_nonzero,
        then_target: match_write,
        then_args: vec![next_ti_after_match, ms_oi, ms_sum],
        else_target: tail_header,
        else_args: vec![next_ti_after_match, ms_oi],
    });
    b.seal_block_with_params(vec![(ms_ti, Ty::I64), (ms_oi, Ty::I64), (ms_sum, Ty::I64)]);

    let mw_ti = b.fresh_value();
    let mw_oi = b.fresh_value();
    let mw_sum = b.fresh_value();
    b.start_block(match_write);
    store_sparse_output(&mut b, out_vars, out_coeffs, mw_oi, pivot_var_val, mw_sum);
    let next_oi_after_match = b.binop(BinOp::Add, Ty::I64, mw_oi, one_idx);
    b.emit_void(Inst::Br {
        target: tail_header,
        args: vec![mw_ti, next_oi_after_match],
    });
    b.seal_block_with_params(vec![(mw_ti, Ty::I64), (mw_oi, Ty::I64), (mw_sum, Ty::I64)]);

    let nm_ti = b.fresh_value();
    let nm_oi = b.fresh_value();
    b.start_block(no_match);
    let (no_match_product, no_match_overflow) =
        b.overflow(OverflowOp::MulOverflow, Ty::I64, scale, pivot_coeff_val);
    b.emit_void(Inst::CondBr {
        cond: no_match_overflow,
        then_target: overflow_exit,
        then_args: vec![],
        else_target: no_match_check,
        else_args: vec![nm_ti, nm_oi, no_match_product],
    });
    b.seal_block_with_params(vec![(nm_ti, Ty::I64), (nm_oi, Ty::I64)]);

    let nc_ti = b.fresh_value();
    let nc_oi = b.fresh_value();
    let nc_product = b.fresh_value();
    b.start_block(no_match_check);
    let product_nonzero = b.icmp(ICmpOp::Ne, Ty::I64, nc_product, zero_coeff);
    b.emit_void(Inst::CondBr {
        cond: product_nonzero,
        then_target: no_match_write,
        then_args: vec![nc_ti, nc_oi, nc_product],
        else_target: tail_header,
        else_args: vec![nc_ti, nc_oi],
    });
    b.seal_block_with_params(vec![
        (nc_ti, Ty::I64),
        (nc_oi, Ty::I64),
        (nc_product, Ty::I64),
    ]);

    let nw_ti = b.fresh_value();
    let nw_oi = b.fresh_value();
    let nw_product = b.fresh_value();
    b.start_block(no_match_write);
    store_sparse_output(
        &mut b,
        out_vars,
        out_coeffs,
        nw_oi,
        pivot_var_val,
        nw_product,
    );
    let next_oi_after_no_match = b.binop(BinOp::Add, Ty::I64, nw_oi, one_idx);
    b.emit_void(Inst::Br {
        target: tail_header,
        args: vec![nw_ti, next_oi_after_no_match],
    });
    b.seal_block_with_params(vec![
        (nw_ti, Ty::I64),
        (nw_oi, Ty::I64),
        (nw_product, Ty::I64),
    ]);

    let tail_ti = b.fresh_value();
    let tail_oi = b.fresh_value();
    b.start_block(tail_header);
    let tail_in_bounds = b.icmp(ICmpOp::Ult, Ty::I64, tail_ti, target_len);
    b.emit_void(Inst::CondBr {
        cond: tail_in_bounds,
        then_target: tail_check_entering,
        then_args: vec![tail_ti, tail_oi],
        else_target: return_success,
        else_args: vec![tail_oi],
    });
    b.seal_block_with_params(vec![(tail_ti, Ty::I64), (tail_oi, Ty::I64)]);

    let tc_ti = b.fresh_value();
    let tc_oi = b.fresh_value();
    b.start_block(tail_check_entering);
    let tail_var = load_sparse_var(&mut b, target_vars, tc_ti);
    let tail_is_entering = b.icmp(ICmpOp::Eq, Ty::I32, tail_var, entering_val);
    let next_ti_tail = b.binop(BinOp::Add, Ty::I64, tc_ti, one_idx);
    b.emit_void(Inst::CondBr {
        cond: tail_is_entering,
        then_target: tail_header,
        then_args: vec![next_ti_tail, tc_oi],
        else_target: tail_copy,
        else_args: vec![tc_ti, tc_oi],
    });
    b.seal_block_with_params(vec![(tc_ti, Ty::I64), (tc_oi, Ty::I64)]);

    let tail_copy_ti = b.fresh_value();
    let tail_copy_oi = b.fresh_value();
    b.start_block(tail_copy);
    let copied_tail_var = load_sparse_var(&mut b, target_vars, tail_copy_ti);
    let copied_tail_coeff = load_sparse_coeff(&mut b, target_coeffs, tail_copy_ti);
    store_sparse_output(
        &mut b,
        out_vars,
        out_coeffs,
        tail_copy_oi,
        copied_tail_var,
        copied_tail_coeff,
    );
    let next_ti_after_tail = b.binop(BinOp::Add, Ty::I64, tail_copy_ti, one_idx);
    let next_oi_after_tail = b.binop(BinOp::Add, Ty::I64, tail_copy_oi, one_idx);
    b.emit_void(Inst::Br {
        target: tail_header,
        args: vec![next_ti_after_tail, next_oi_after_tail],
    });
    b.seal_block_with_params(vec![(tail_copy_ti, Ty::I64), (tail_copy_oi, Ty::I64)]);

    let success_oi = b.fresh_value();
    b.start_block(return_success);
    b.emit_void(Inst::Return {
        values: vec![success_oi],
    });
    b.seal_block_with_params(vec![(success_oi, Ty::I64)]);

    b.start_block(overflow_exit);
    let overflow = b.const_i64(-1);
    b.emit_void(Inst::Return {
        values: vec![overflow],
    });
    b.seal_block();

    let mut module = Module::new("jit_sparse_substitute_regression");
    let func_ty_id = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::I64, Ty::I64, Ty::Ptr, Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut func = Function::new(FuncId(0), SPARSE_SUBSTITUTE_SYMBOL, func_ty_id, entry_block);
    func.blocks = b.blocks;
    module.add_function(func);
    module
}

fn maybe_dump_sparse_substitute_pipeline(
    module: &Module,
    jit: &JitCompilationResult,
    opt_level: OptLevel,
) {
    if std::env::var("TRUST_CG_DEBUG_SPARSE_SUBSTITUTE").is_err() {
        return;
    }

    let raw_ptr = jit
        .buffer
        .get_fn_ptr_bound(SPARSE_SUBSTITUTE_SYMBOL)
        .expect("substitute_var_specialized symbol missing")
        .as_ptr();
    eprintln!(
        "internal debug only: sparse substitute raw jit entry {:p} opt_level={opt_level:?}; not installable product evidence",
        raw_ptr
    );

    let lir_functions =
        trust_cg_lower::translate_module(module).expect("sparse substitute module should lower");
    assert_eq!(lir_functions.len(), 1, "expected a single lowered function");

    let pipeline_config = trust_cg_codegen::PipelineConfig {
        opt_level,
        ..trust_cg_codegen::PipelineConfig::default()
    };
    let pipeline = Pipeline::new(pipeline_config);
    let (ir_func, metrics) = pipeline
        .prepare_function_with_metrics(&lir_functions[0].0, Some(&lir_functions[0].1))
        .expect("sparse substitute pipeline prepare should succeed");
    eprintln!("sparse substitute prepare metrics: {metrics:#?}");
    eprintln!("sparse substitute prepared ir:\n{ir_func:#?}");
}

fn sparse_substitute_compiler(opt_level: OptLevel) -> Compiler {
    let config = CompilerConfig {
        opt_level,
        parallel: false,
        ..CompilerConfig::default()
    };
    Compiler::new(config)
}

fn jit_compile_sparse_substitute_with_pipeline_config(
    pipeline_config: PipelineConfig,
) -> (trust_cg_codegen::ExecutableBuffer, SparseSubstituteFn) {
    let module = emit_single_pivot_sparse_substitute_trust_ir(3, 2, 1);
    let lir_functions =
        trust_cg_lower::translate_module(&module).expect("sparse substitute module should lower");
    assert_eq!(lir_functions.len(), 1, "expected a single lowered function");

    let pipeline = Pipeline::new(pipeline_config.clone());
    let (ir_func, _metrics) = pipeline
        .prepare_function_with_metrics(&lir_functions[0].0, Some(&lir_functions[0].1))
        .expect("sparse substitute pipeline prepare should succeed");

    let jit = JitCompiler::new(JitConfig {
        opt_level: pipeline_config.opt_level,
        ..JitConfig::default()
    });
    let buffer = jit
        .compile_raw(&[ir_func], &HashMap::new())
        .expect("Trust Codegen raw JIT compile should succeed for sparse substitute regression");
    let f = bind_ay_lra_product_kernel::<SparseSubstituteFn>(&buffer, SPARSE_SUBSTITUTE_SYMBOL)
        .expect("substitute_var_specialized symbol must satisfy ay LRA product-kernel contract");
    (buffer, f)
}

fn jit_compile_sparse_substitute_with_opt_level(
    opt_level: OptLevel,
) -> (JitCompilationResult, SparseSubstituteFn) {
    let module = emit_single_pivot_sparse_substitute_trust_ir(3, 2, 1);
    let compiler = sparse_substitute_compiler(opt_level);
    let result = compiler
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Trust Codegen JIT compile should succeed for sparse substitute regression");
    maybe_dump_sparse_substitute_pipeline(&module, &result, opt_level);
    let f =
        bind_ay_lra_product_kernel::<SparseSubstituteFn>(&result.buffer, SPARSE_SUBSTITUTE_SYMBOL)
            .expect(
                "substitute_var_specialized symbol must satisfy ay LRA product-kernel contract",
            );
    (result, f)
}

fn jit_compile_sparse_substitute() -> (JitCompilationResult, SparseSubstituteFn) {
    jit_compile_sparse_substitute_with_opt_level(OptLevel::O2)
}

fn code_shape_for_module(module: &Module, opt_level: OptLevel) -> SparseCodeShape {
    let lir_functions =
        trust_cg_lower::translate_module(module).expect("sparse substitute module should lower");
    assert_eq!(lir_functions.len(), 1, "expected a single lowered function");

    let pipeline_config = PipelineConfig {
        opt_level,
        ..PipelineConfig::default()
    };
    let pipeline = Pipeline::new(pipeline_config);
    let (ir_func, metrics) = pipeline
        .prepare_function_with_metrics(&lir_functions[0].0, Some(&lir_functions[0].1))
        .expect("sparse substitute pipeline prepare should succeed");
    measure_code_shape(&ir_func, metrics.spill_slot_count)
}

fn measure_code_shape(func: &MachFunction, spill_slot_count: usize) -> SparseCodeShape {
    let encoded_bytes = encode_function(func)
        .expect("prepared sparse substitute function should encode")
        .len();
    let mut shape = SparseCodeShape {
        encoded_bytes,
        spill_slot_count,
        ..SparseCodeShape::default()
    };

    for &block_id in &func.block_order {
        let block = &func.blocks[block_id.0 as usize];
        for &inst_id in &block.insts {
            let inst = &func.insts[inst_id.0 as usize];
            if inst.is_pseudo() {
                continue;
            }

            shape.real_inst_count += 1;
            if inst.is_terminator()
                || matches!(
                    inst.opcode,
                    AArch64Opcode::B
                        | AArch64Opcode::BCond
                        | AArch64Opcode::Bcc
                        | AArch64Opcode::Cbz
                        | AArch64Opcode::Cbnz
                        | AArch64Opcode::Tbz
                        | AArch64Opcode::Tbnz
                        | AArch64Opcode::Br
                        | AArch64Opcode::Bl
                        | AArch64Opcode::BL
                        | AArch64Opcode::Blr
                        | AArch64Opcode::BLR
                        | AArch64Opcode::Ret
                )
            {
                shape.branch_count += 1;
            }
            if matches!(
                inst.opcode,
                AArch64Opcode::BCond
                    | AArch64Opcode::Bcc
                    | AArch64Opcode::Cbz
                    | AArch64Opcode::Cbnz
                    | AArch64Opcode::Tbz
                    | AArch64Opcode::Tbnz
            ) {
                shape.cond_branch_count += 1;
            }

            if matches!(inst.opcode, AArch64Opcode::LdrRO | AArch64Opcode::StrRO) {
                shape.reg_offset_mem_count += 1;
            }
            match inst.opcode {
                AArch64Opcode::Madd => shape.madd_count += 1,
                AArch64Opcode::MulRR => shape.mul_count += 1,
                AArch64Opcode::Smulh => shape.smulh_count += 1,
                AArch64Opcode::LslRI => shape.lsl_ri_count += 1,
                AArch64Opcode::AddRR => shape.add_rr_count += 1,
                AArch64Opcode::AddsRR | AArch64Opcode::AddsRI => shape.adds_count += 1,
                AArch64Opcode::SubsRR | AArch64Opcode::SubsRI => shape.subs_count += 1,
                AArch64Opcode::CSet => shape.cset_count += 1,
                AArch64Opcode::LdrRI
                | AArch64Opcode::LdrRO
                | AArch64Opcode::LdrbRI
                | AArch64Opcode::LdrhRI
                | AArch64Opcode::LdrsbRI
                | AArch64Opcode::LdrshRI
                | AArch64Opcode::LdrLiteral
                | AArch64Opcode::LdpRI
                | AArch64Opcode::LdpPostIndex
                | AArch64Opcode::LdrGot
                | AArch64Opcode::LdrTlvp => shape.load_count += 1,
                AArch64Opcode::StrRI
                | AArch64Opcode::StrRO
                | AArch64Opcode::StrbRI
                | AArch64Opcode::StrhRI
                | AArch64Opcode::StpRI
                | AArch64Opcode::StpPreIndex => shape.store_count += 1,
                _ => {}
            }
        }
    }

    shape
}

fn prepared_kernel_function_for_module(
    module: &Module,
    opt_level: OptLevel,
) -> (MachFunction, SparseCodeShape, Vec<u8>) {
    let lir_functions =
        trust_cg_lower::translate_module(module).expect("real ay LRA module should lower");
    assert_eq!(lir_functions.len(), 1, "expected a single lowered function");

    let pipeline_config = PipelineConfig {
        opt_level,
        ..PipelineConfig::default()
    };
    let pipeline = Pipeline::new(pipeline_config);
    let (ir_func, metrics) = pipeline
        .prepare_function_with_metrics(&lir_functions[0].0, Some(&lir_functions[0].1))
        .expect("real ay LRA kernel should prepare through the codegen pipeline");
    let encoded =
        encode_function(&ir_func).expect("prepared real ay LRA kernel should encode as AArch64");
    let shape = measure_code_shape(&ir_func, metrics.spill_slot_count);
    assert_eq!(shape.encoded_bytes, encoded.len());
    (ir_func, shape, encoded)
}

fn target_arch_name(arch: &TargetArchitecture) -> String {
    match arch {
        TargetArchitecture::Aarch64 => "aarch64".to_owned(),
        TargetArchitecture::X86_64 => "x86_64".to_owned(),
        TargetArchitecture::Riscv64 => "riscv64".to_owned(),
        TargetArchitecture::Other(value) => value.clone(),
    }
}

fn target_identity_from_manifest(
    manifest: &DeterministicArtifactManifest,
) -> TargetAbiLayoutIdentity {
    TargetAbiLayoutIdentity {
        arch: target_arch_name(&manifest.target.architecture),
        target_triple: manifest.target.triple.clone(),
        abi: manifest.abi.calling_convention.clone(),
        data_layout: format!("layout-checksum:{}", manifest.layout.checksum()),
        cpu: manifest
            .target
            .cpu
            .clone()
            .unwrap_or_else(|| "generic".to_owned()),
        features: manifest.target.features.clone(),
    }
}

fn ay_lra_real_kernel_region_payload(
    manifest: &DeterministicArtifactManifest,
    encoded: &[u8],
    shape: &SparseCodeShape,
) -> Vec<u8> {
    let mut payload = Vec::new();
    let fields = [
        BATCH_PIVOT_STATUS_SYMBOL.to_owned(),
        manifest.checksum().to_string(),
        manifest.layout.checksum().to_string(),
        manifest.invalidation.checksum().to_string(),
        format!("real_inst_count={}", shape.real_inst_count),
        format!("encoded_bytes={}", shape.encoded_bytes),
    ];
    for field in fields {
        payload.extend_from_slice(field.as_bytes());
        payload.push(0);
    }
    payload.extend_from_slice(encoded);
    payload
}

fn ay_lra_basis_cost_context(shape: &SparseCodeShape) -> CostContext {
    let source_cost =
        (shape.real_inst_count + shape.branch_count * 2 + shape.load_count + shape.store_count)
            as i64;
    let replacement_cost = source_cost.saturating_sub(5).max(1);
    CostContext::aarch64(
        "trust-cg-aarch64",
        "2026.05-real-ay-lra",
        source_cost,
        replacement_cost,
    )
    .with_profile("ay-lra-basis-row-batch-real-kernel")
    .with_note(format!("encoded_bytes={}", shape.encoded_bytes))
}

fn ay_lra_basis_sub_zero_transform() -> TransformIdentity {
    let mut transform = TransformIdentity::new(AY_LRA_BASIS_SUB_ZERO_TRANSFORM, "v1");
    transform.discovered_rule_name = Some(AY_LRA_BASIS_SUB_ZERO_TRANSFORM.to_owned());
    transform.discovered_rule_proof_hash = Some(AY_LRA_BASIS_SUB_ZERO_PROOF_HASH);
    transform.certificate_hash = Some(AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH.to_owned());
    transform.certificate_validation_hash = Some(AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH.to_owned());
    transform
}

fn ay_lra_basis_sub_zero_certificate_identity() -> CertificateIdentity {
    CertificateIdentity {
        producer: "trust-cg-opt.proof-opts".to_owned(),
        certificate_hash: Some(AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH.to_owned()),
        certificate_chain_id: Some(format!(
            "{AY_LRA_BASIS_SUB_ZERO_TRANSFORM}@v1:{AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH}"
        )),
    }
}

fn required_admission_certificate_ids(
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> Vec<String> {
    proof_manifest
        .certificate_dependencies
        .iter()
        .filter(|dependency| {
            dependency.availability == AYLraRequirementAvailability::RequiredForAdmission
        })
        .map(|dependency| dependency.id.to_owned())
        .collect()
}

fn ay_lra_basis_admission_verdict(
    record: &trust_cg_verify::RewriteAdmissionRecord,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
    manifest: &DeterministicArtifactManifest,
    encoded: &[u8],
) -> ProofGuidedAdmissionVerdict {
    ProofGuidedAdmissionVerdict::accepted_for_record(
        record,
        required_admission_certificate_ids(proof_manifest),
        format!(
            "machir:{BATCH_PIVOT_STATUS_SYMBOL}:{}",
            ArtifactChecksum::for_bytes(encoded)
        ),
        manifest.checksum().to_string(),
        "ay_lra_basis_row_batch_status_abi_v1",
        "replay/ay-lra-basis-row-batch",
        "telemetry/ay-lra-basis-row-batch/admitted-rewrite",
        0,
        "trust_cg_disable_admitted_rewrite_ay_lra_basis_row_batch",
    )
}

fn ay_lra_basis_reducer_artifact_hash(
    manifest: &DeterministicArtifactManifest,
    encoded: &[u8],
) -> String {
    format!(
        "sha256:{:032x}{:032x}",
        manifest.checksum().get(),
        ArtifactChecksum::for_bytes(encoded).get()
    )
}

fn emit_single_coeff_update(
    b: &mut TrustIrBuilder,
    target: ValueId,
    scale: ValueId,
    var_idx: u32,
    coeff: i64,
) {
    if coeff == 0 {
        return;
    }

    let idx = b.const_u64(var_idx as i64);
    let addr = b.index(Ty::I64, target, idx);
    let cur = b.load(Ty::I64, addr);
    let new_val = match coeff {
        1 => b.binop(BinOp::Add, Ty::I64, cur, scale),
        -1 => b.binop(BinOp::Sub, Ty::I64, cur, scale),
        _ => {
            let coeff_val = b.const_i64(coeff);
            let product = b.binop(BinOp::Mul, Ty::I64, scale, coeff_val);
            b.binop(BinOp::Add, Ty::I64, cur, product)
        }
    };
    b.store(Ty::I64, addr, new_val);
}

fn emit_pivot_row_trust_ir(coefficients: &[(u32, i64)]) -> Module {
    let entry_block = BlockId(0);
    let mut b = TrustIrBuilder::new(entry_block);
    let params = b.reserve_params(2);
    let target = params[0];
    let scale = params[1];

    for &(var_idx, coeff) in coefficients {
        emit_single_coeff_update(&mut b, target, scale, var_idx, coeff);
    }

    b.emit_void(Inst::Return { values: vec![] });
    b.seal_block_with_params(vec![(target, Ty::Ptr), (scale, Ty::I64)]);

    let mut module = Module::new("simplex_pivot_row");
    let func_ty_id = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I64],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId(0), PIVOT_ROW_SYMBOL, func_ty_id, entry_block);
    func.blocks = b.blocks;
    module.add_function(func);
    module
}

fn seal_overflow_check_block(
    b: &mut TrustIrBuilder,
    row_idx: ValueId,
    overflow: ValueId,
    overflow_exit: BlockId,
) -> BlockId {
    let continue_block = BlockId(b.blocks.len() as u32 + 5);
    b.emit_void(Inst::CondBr {
        cond: overflow,
        then_target: overflow_exit,
        then_args: vec![row_idx],
        else_target: continue_block,
        else_args: vec![row_idx],
    });
    b.seal_block_with_params(vec![(row_idx, Ty::I64)]);
    b.start_block(continue_block);
    continue_block
}

fn emit_batch_coeff_update_with_overflow(
    b: &mut TrustIrBuilder,
    cur_target: ValueId,
    cur_scale: ValueId,
    row_idx: ValueId,
    var_idx: u32,
    coeff: i64,
    overflow_exit: BlockId,
) {
    if coeff == 0 {
        return;
    }

    let idx = b.const_u64(var_idx as i64);
    let addr = b.index(Ty::I64, cur_target, idx);
    let cur = b.load(Ty::I64, addr);

    let updated = match coeff {
        1 => {
            let (sum, overflow) = b.overflow(OverflowOp::AddOverflow, Ty::I64, cur, cur_scale);
            seal_overflow_check_block(b, row_idx, overflow, overflow_exit);
            sum
        }
        -1 => {
            let (diff, overflow) = b.overflow(OverflowOp::SubOverflow, Ty::I64, cur, cur_scale);
            seal_overflow_check_block(b, row_idx, overflow, overflow_exit);
            diff
        }
        _ => {
            let coeff_val = b.const_i64(coeff);
            let (product, mul_overflow) =
                b.overflow(OverflowOp::MulOverflow, Ty::I64, cur_scale, coeff_val);
            seal_overflow_check_block(b, row_idx, mul_overflow, overflow_exit);

            let (sum, add_overflow) = b.overflow(OverflowOp::AddOverflow, Ty::I64, cur, product);
            seal_overflow_check_block(b, row_idx, add_overflow, overflow_exit);
            sum
        }
    };

    b.store(Ty::I64, addr, updated);
}

fn emit_batch_pivot_trust_ir(coefficients: &[(u32, i64)]) -> Module {
    let entry_block = BlockId(0);
    let loop_header = BlockId(1);
    let loop_body = BlockId(2);
    let exit_success = BlockId(3);
    let overflow_exit = BlockId(4);

    let mut b = TrustIrBuilder::new(entry_block);
    let params = b.reserve_params(3);
    let targets = params[0];
    let scales = params[1];
    let num_rows = params[2];

    let zero = b.const_u64(0);
    b.emit_void(Inst::Br {
        target: loop_header,
        args: vec![zero],
    });
    b.seal_block_with_params(vec![
        (targets, Ty::Ptr),
        (scales, Ty::Ptr),
        (num_rows, Ty::I64),
    ]);

    let row_idx_header = b.fresh_value();
    b.start_block(loop_header);
    let done = b.icmp(ICmpOp::Uge, Ty::I64, row_idx_header, num_rows);
    b.emit_void(Inst::CondBr {
        cond: done,
        then_target: exit_success,
        then_args: vec![],
        else_target: loop_body,
        else_args: vec![row_idx_header],
    });
    b.seal_block_with_params(vec![(row_idx_header, Ty::I64)]);

    let row_idx_body = b.fresh_value();
    b.start_block(loop_body);
    let target_ptr_ptr = b.index(Ty::Ptr, targets, row_idx_body);
    let cur_target = b.load(Ty::Ptr, target_ptr_ptr);
    let scale_ptr = b.index(Ty::I64, scales, row_idx_body);
    let cur_scale = b.load(Ty::I64, scale_ptr);

    for &(var_idx, coeff) in coefficients {
        emit_batch_coeff_update_with_overflow(
            &mut b,
            cur_target,
            cur_scale,
            row_idx_body,
            var_idx,
            coeff,
            overflow_exit,
        );
    }

    let one = b.const_u64(1);
    let next_idx = b.binop(BinOp::Add, Ty::I64, row_idx_body, one);
    b.emit_void(Inst::Br {
        target: loop_header,
        args: vec![next_idx],
    });
    b.seal_block_with_params(vec![(row_idx_body, Ty::I64)]);

    b.start_block(exit_success);
    let success = b.const_i64(0);
    b.emit_void(Inst::Return {
        values: vec![success],
    });
    b.seal_block();

    let overflow_row = b.fresh_value();
    b.start_block(overflow_exit);
    let one_overflow = b.const_u64(1);
    let result = b.binop(BinOp::Add, Ty::I64, overflow_row, one_overflow);
    b.emit_void(Inst::Return {
        values: vec![result],
    });
    b.seal_block_with_params(vec![(overflow_row, Ty::I64)]);

    let mut module = Module::new("simplex_batch_pivot");
    let func_ty_id = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId(0), BATCH_PIVOT_SYMBOL, func_ty_id, entry_block);
    func.blocks = b.blocks;
    module.add_function(func);
    module
}

fn emit_batch_pivot_status_trust_ir(coefficients: &[(u32, i64)]) -> Module {
    let entry_block = BlockId(0);
    let loop_header = BlockId(1);
    let loop_body = BlockId(2);
    let exit_success = BlockId(3);
    let overflow_exit = BlockId(4);
    let stale_exit = BlockId(5);
    let bounds_exit = BlockId(6);

    let mut b = TrustIrBuilder::new(entry_block);
    let params = b.reserve_params(8);
    let targets = params[0];
    let scales = params[1];
    let num_rows = params[2];
    let row_output_offsets = params[3];
    let row_output_lengths = params[4];
    let output_capacity = params[5];
    let basis_epochs = params[6];
    let out_status = params[7];
    let planned_row_len_value = coefficients.iter().filter(|(_, coeff)| *coeff != 0).count() as i64;

    let zero = b.const_u64(0);
    let one_epoch = b.const_u64(1);
    let current_basis_epoch = b.load(Ty::I64, basis_epochs);
    let expected_basis_epoch_ptr = b.index(Ty::I64, basis_epochs, one_epoch);
    let expected_basis_epoch = b.load(Ty::I64, expected_basis_epoch_ptr);
    let stale_basis_epoch = b.icmp(
        ICmpOp::Ne,
        Ty::I64,
        current_basis_epoch,
        expected_basis_epoch,
    );
    b.emit_void(Inst::CondBr {
        cond: stale_basis_epoch,
        then_target: stale_exit,
        then_args: vec![],
        else_target: loop_header,
        else_args: vec![zero],
    });
    b.seal_block_with_params(vec![
        (targets, Ty::Ptr),
        (scales, Ty::Ptr),
        (num_rows, Ty::I64),
        (row_output_offsets, Ty::Ptr),
        (row_output_lengths, Ty::Ptr),
        (output_capacity, Ty::I64),
        (basis_epochs, Ty::Ptr),
        (out_status, Ty::Ptr),
    ]);

    let row_idx_header = b.fresh_value();
    b.start_block(loop_header);
    let done = b.icmp(ICmpOp::Uge, Ty::I64, row_idx_header, num_rows);
    b.emit_void(Inst::CondBr {
        cond: done,
        then_target: exit_success,
        then_args: vec![],
        else_target: loop_body,
        else_args: vec![row_idx_header],
    });
    b.seal_block_with_params(vec![(row_idx_header, Ty::I64)]);

    let row_idx_body = b.fresh_value();
    b.start_block(loop_body);
    let row_offset_ptr = b.index(Ty::I64, row_output_offsets, row_idx_body);
    let row_offset = b.load(Ty::I64, row_offset_ptr);
    let planned_row_len = b.const_i64(planned_row_len_value);
    let (required_end, required_end_overflow) = b.overflow(
        OverflowOp::AddOverflow,
        Ty::I64,
        row_offset,
        planned_row_len,
    );
    let capacity_check = BlockId(b.blocks.len() as u32 + 5);
    b.emit_void(Inst::CondBr {
        cond: required_end_overflow,
        then_target: bounds_exit,
        then_args: vec![row_idx_body],
        else_target: capacity_check,
        else_args: vec![row_idx_body, required_end],
    });
    b.seal_block_with_params(vec![(row_idx_body, Ty::I64)]);

    let capacity_row_idx = b.fresh_value();
    let capacity_required_end = b.fresh_value();
    b.start_block(capacity_check);
    let capacity_exceeded = b.icmp(ICmpOp::Ugt, Ty::I64, capacity_required_end, output_capacity);
    let bounds_ok = BlockId(b.blocks.len() as u32 + 5);
    b.emit_void(Inst::CondBr {
        cond: capacity_exceeded,
        then_target: bounds_exit,
        then_args: vec![capacity_row_idx],
        else_target: bounds_ok,
        else_args: vec![capacity_row_idx],
    });
    b.seal_block_with_params(vec![
        (capacity_row_idx, Ty::I64),
        (capacity_required_end, Ty::I64),
    ]);

    let bounds_ok_row_idx = b.fresh_value();
    b.start_block(bounds_ok);
    let row_len_ptr = b.index(Ty::I64, row_output_lengths, bounds_ok_row_idx);
    b.store(Ty::I64, row_len_ptr, planned_row_len);

    let target_ptr_ptr = b.index(Ty::Ptr, targets, bounds_ok_row_idx);
    let cur_target = b.load(Ty::Ptr, target_ptr_ptr);
    let scale_ptr = b.index(Ty::I64, scales, bounds_ok_row_idx);
    let cur_scale = b.load(Ty::I64, scale_ptr);

    for &(var_idx, coeff) in coefficients {
        emit_batch_coeff_update_with_overflow(
            &mut b,
            cur_target,
            cur_scale,
            bounds_ok_row_idx,
            var_idx,
            coeff,
            overflow_exit,
        );
    }

    let one = b.const_u64(1);
    let next_idx = b.binop(BinOp::Add, Ty::I64, bounds_ok_row_idx, one);
    b.emit_void(Inst::Br {
        target: loop_header,
        args: vec![next_idx],
    });
    b.seal_block_with_params(vec![(bounds_ok_row_idx, Ty::I64)]);

    b.start_block(exit_success);
    let no_failed_row_detail = b.const_i64(0);
    write_batch_status_record(
        &mut b,
        out_status,
        AYLraStatus::Ok,
        AYLraDeopt::None,
        num_rows,
        no_failed_row_detail,
    );
    b.emit_void(Inst::Return { values: vec![] });
    b.seal_block();

    let overflow_row = b.fresh_value();
    b.start_block(overflow_exit);
    write_batch_status_record(
        &mut b,
        out_status,
        AYLraStatus::Overflow,
        AYLraDeopt::SparseSubstituteOverflow,
        overflow_row,
        overflow_row,
    );
    b.emit_void(Inst::Return { values: vec![] });
    b.seal_block_with_params(vec![(overflow_row, Ty::I64)]);

    let bounds_row = b.fresh_value();
    b.start_block(bounds_exit);
    write_batch_status_record(
        &mut b,
        out_status,
        AYLraStatus::Bounds,
        AYLraDeopt::SparseSubstituteBounds,
        bounds_row,
        bounds_row,
    );
    b.emit_void(Inst::Return { values: vec![] });
    b.seal_block_with_params(vec![(bounds_row, Ty::I64)]);

    b.start_block(stale_exit);
    let no_committed_rows = b.const_i64(0);
    write_batch_status_record(
        &mut b,
        out_status,
        AYLraStatus::Stale,
        AYLraDeopt::BasisEpochStale,
        no_committed_rows,
        current_basis_epoch,
    );
    b.emit_void(Inst::Return { values: vec![] });
    b.seal_block();

    let mut module = Module::new("simplex_batch_pivot_status");
    let func_ty_id = module.add_func_type(FuncTy {
        params: vec![
            Ty::Ptr,
            Ty::Ptr,
            Ty::I64,
            Ty::Ptr,
            Ty::Ptr,
            Ty::I64,
            Ty::Ptr,
            Ty::Ptr,
        ],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = Function::new(
        FuncId(0),
        BATCH_PIVOT_STATUS_SYMBOL,
        func_ty_id,
        entry_block,
    );
    func.blocks = b.blocks;
    module.add_function(func);
    module
}

fn compile_module_with_opt_level(module: &Module, opt_level: OptLevel) -> JitCompilationResult {
    let compiler = sparse_substitute_compiler(opt_level);
    compiler
        .compile_module_to_jit(module, &HashMap::new())
        .expect("Trust Codegen JIT compile should succeed for ay integer simplex regression")
}

fn jit_compile_pivot_row_with_opt_level(
    coefficients: &[(u32, i64)],
    opt_level: OptLevel,
) -> (JitCompilationResult, PivotRowFn) {
    let module = emit_pivot_row_trust_ir(coefficients);
    let result = compile_module_with_opt_level(&module, opt_level);
    let f = bind_ay_lra_product_kernel::<PivotRowFn>(&result.buffer, PIVOT_ROW_SYMBOL)
        .expect("pivot_row_update symbol must satisfy ay LRA product-kernel contract");
    (result, f)
}

fn jit_compile_batch_pivot_with_opt_level(
    coefficients: &[(u32, i64)],
    opt_level: OptLevel,
) -> (JitCompilationResult, BatchPivotFn) {
    let module = emit_batch_pivot_trust_ir(coefficients);
    let result = compile_module_with_opt_level(&module, opt_level);
    let f = bind_ay_lra_product_kernel::<BatchPivotFn>(&result.buffer, BATCH_PIVOT_SYMBOL)
        .expect("batch_pivot_update symbol must satisfy ay LRA product-kernel contract");
    (result, f)
}

fn jit_compile_batch_pivot_status_with_opt_level(
    coefficients: &[(u32, i64)],
    opt_level: OptLevel,
) -> (JitCompilationResult, BatchPivotStatusFn) {
    let module = emit_batch_pivot_status_trust_ir(coefficients);
    let result = compile_module_with_opt_level(&module, opt_level);
    let f =
        bind_ay_lra_product_kernel::<BatchPivotStatusFn>(&result.buffer, BATCH_PIVOT_STATUS_SYMBOL)
            .expect("ay_lra_basis_row_batch symbol must satisfy ay LRA product-kernel contract");
    (result, f)
}

fn reference_sparse_substitute(
    target: &[(u32, i64)],
    pivot: &[(u32, i64)],
    entering_var: u32,
    scale: i64,
) -> Option<Vec<(u32, i64)>> {
    let mut result = Vec::new();
    let mut ti = 0;
    let mut pi = 0;

    while ti < target.len() || pi < pivot.len() {
        while pi < pivot.len() && pivot[pi].0 == entering_var {
            pi += 1;
        }

        match (target.get(ti).copied(), pivot.get(pi).copied()) {
            (Some((tv, tc)), Some((pv, _pc))) if tv < pv => {
                if tv != entering_var && tc != 0 {
                    result.push((tv, tc));
                }
                ti += 1;
            }
            (Some((tv, tc)), Some((pv, pc))) if tv == pv => {
                if tv != entering_var {
                    let prod = scale.checked_mul(pc)?;
                    let sum = tc.checked_add(prod)?;
                    if sum != 0 {
                        result.push((tv, sum));
                    }
                }
                ti += 1;
                pi += 1;
            }
            (_, Some((pv, pc))) => {
                let prod = scale.checked_mul(pc)?;
                if pv != entering_var && prod != 0 {
                    result.push((pv, prod));
                }
                pi += 1;
            }
            (Some((tv, tc)), None) => {
                if tv != entering_var && tc != 0 {
                    result.push((tv, tc));
                }
                ti += 1;
            }
            (None, None) => break,
        }
    }

    Some(result)
}

fn run_sparse_substitute_case(
    f: SparseSubstituteFn,
    pivot: &[(u32, i64)],
    entering_var: u32,
    target: &[(u32, i64)],
    scale: i64,
) {
    let expected = reference_sparse_substitute(target, pivot, entering_var, scale);
    let target_vars: Vec<u32> = target.iter().map(|(var, _)| *var).collect();
    let target_coeffs: Vec<i64> = target.iter().map(|(_, coeff)| *coeff).collect();
    let mut out_vars = vec![u32::MAX; target.len() + pivot.len() + 2];
    let mut out_coeffs = vec![i64::MIN; target.len() + pivot.len() + 2];

    let raw = unsafe {
        f(
            target_vars.as_ptr(),
            target_coeffs.as_ptr(),
            target.len() as i64,
            scale,
            out_vars.as_mut_ptr(),
            out_coeffs.as_mut_ptr(),
        )
    };

    match expected {
        Some(expected) => {
            assert!(raw >= 0, "sparse substitute unexpectedly overflowed");
            let len = raw as usize;
            let actual: Vec<(u32, i64)> = out_vars[..len]
                .iter()
                .copied()
                .zip(out_coeffs[..len].iter().copied())
                .collect();
            assert_eq!(actual, expected);
        }
        None => assert_eq!(raw, -1, "sparse substitute should report overflow"),
    }
}

fn reference_pivot_row_update(coefficients: &[(u32, i64)], row: &mut [i64], scale: i64) {
    for &(var_idx, coeff) in coefficients {
        row[var_idx as usize] += scale * coeff;
    }
}

fn reference_batch_pivot_update(
    coefficients: &[(u32, i64)],
    rows: &mut [[i64; 5]],
    scales: &[i64],
) -> i64 {
    for (row_idx, (row, scale)) in rows.iter_mut().zip(scales.iter().copied()).enumerate() {
        for &(var_idx, coeff) in coefficients {
            let cell = &mut row[var_idx as usize];
            let delta = match coeff {
                1 => scale,
                -1 => match 0i64.checked_sub(scale) {
                    Some(delta) => delta,
                    None => return row_idx as i64 + 1,
                },
                _ => match scale.checked_mul(coeff) {
                    Some(delta) => delta,
                    None => return row_idx as i64 + 1,
                },
            };
            match cell.checked_add(delta) {
                Some(sum) => *cell = sum,
                None => return row_idx as i64 + 1,
            }
        }
    }
    0
}

fn digest_hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn tableau_digest(rows: &[[i64; 5]]) -> u64 {
    digest_hash(&rows)
}

fn basis_digest(basis_epochs: &[i64; 2]) -> u64 {
    digest_hash(basis_epochs)
}

fn assert_batch_status_lookup_rejected_before_tableau_mutation(
    result: &JitCompilationResult,
    manifest: &DeterministicArtifactManifest,
    contract: &SymbolLookupContract,
    assert_error: impl FnOnce(ArtifactContractError),
) {
    let rows = [[10, 20, 30, 40, 50], [-5, 0, 9, 2, -11], [0, 1, -2, 3, -4]];
    let original_rows = rows;
    let status = AYLraBatchStatusAbi::poisoned();
    let original_status = status;

    let err = result
        .buffer
        .get_fixture_contract_symbol_bound::<BatchPivotStatusFn>(manifest, contract)
        .expect_err("contract mismatch must reject before a callable pointer escapes");
    assert_error(err);
    assert_eq!(
        rows, original_rows,
        "rejected lookup must not mutate tableau rows"
    );
    assert_eq!(
        status, original_status,
        "rejected lookup must not write batch status"
    );
}

fn rejected_batch_proof_evidence(manifest: &DeterministicArtifactManifest) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::rejected(
        "trust-cg-verify",
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
        manifest.invalidation.checksum(),
        manifest.proof_policy.checksum(),
    );
    evidence.metadata.insert(
        "disposition".to_owned(),
        "proof_rejected_non_promoting_local_fixture".to_owned(),
    );
    evidence.metadata.insert(
        "replay_bundle_ref".to_owned(),
        "replay/ay-lra-basis-row-batch/proof-evidence.json".to_owned(),
    );
    evidence
}

fn ay_lra_selector_verified_evidence(
    manifest: &DeterministicArtifactManifest,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::verified(
        "trust-cg-verify",
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
        manifest.invalidation.checksum(),
        manifest.proof_policy.checksum(),
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
    evidence
}

fn complete_ay_lra_selector_evidence(
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

    let behavior_sha256 = format!(
        "sha256:{}:reference-behavior",
        proof_manifest.kernel_family.as_str()
    );
    AYLraProofConsumptionEvidence {
        proof_evidence: Some(ay_lra_selector_verified_evidence(manifest, proof_manifest)),
        facts,
        certificates,
        basis_epoch: AYLraBasisEpochEvidence {
            current_epoch: manifest.invalidation.generation,
            expected_epoch: manifest.invalidation.generation,
        },
        replay: AYLraReplayComparison {
            manifest_checksum: manifest.checksum(),
            replay_root_sha256: format!(
                "sha256:{}:replay-root",
                proof_manifest.kernel_family.as_str()
            ),
            generic_behavior_sha256: behavior_sha256.clone(),
            specialized_behavior_sha256: behavior_sha256.clone(),
            reference_behavior_sha256: behavior_sha256,
        },
        product_gate: AYLraProductGateEvidence {
            install_gate_packet_sha256: format!(
                "sha256:{}:install-gate",
                proof_manifest.kernel_family.as_str()
            ),
            consumer_admission_sha256: format!(
                "sha256:{}:consumer-admission",
                proof_manifest.kernel_family.as_str()
            ),
            replay_identity_sha256: format!(
                "sha256:{}:replay-identity",
                proof_manifest.kernel_family.as_str()
            ),
            telemetry_record_sha256: format!(
                "sha256:{}:telemetry",
                proof_manifest.kernel_family.as_str()
            ),
        },
    }
}

fn use_canonical_basis_row_batch_telemetry_hashes(evidence: &mut AYLraProofConsumptionEvidence) {
    evidence.replay.replay_root_sha256 = CANONICAL_TELEMETRY_SHA256.to_owned();
    evidence.replay.generic_behavior_sha256 = CANONICAL_TELEMETRY_SHA256.to_owned();
    evidence.replay.specialized_behavior_sha256 = CANONICAL_TELEMETRY_SHA256.to_owned();
    evidence.replay.reference_behavior_sha256 = CANONICAL_TELEMETRY_SHA256.to_owned();
    evidence.product_gate.install_gate_packet_sha256 = CANONICAL_TELEMETRY_SHA256.to_owned();
    evidence.product_gate.consumer_admission_sha256 = CANONICAL_TELEMETRY_SHA256.to_owned();
    evidence.product_gate.replay_identity_sha256 = CANONICAL_TELEMETRY_SHA256.to_owned();
    evidence.product_gate.telemetry_record_sha256 = CANONICAL_TELEMETRY_SHA256.to_owned();
}

#[test]
fn ay_lra_product_kernel_contract_lookup_rejects_mismatches_before_tableau_mutation() {
    let coefficients = [(0, 1), (2, -1), (4, 3)];
    let (jit, _f) = jit_compile_batch_pivot_status_with_opt_level(&coefficients, OptLevel::O2);
    let manifest = ay_lra_kernel_manifest(BATCH_PIVOT_STATUS_SYMBOL);
    let contract = ay_lra_kernel_lookup_contract(&manifest, BATCH_PIVOT_STATUS_SYMBOL);

    let mut wrong_signature = contract.clone();
    wrong_signature.signature.params[0] = i32_value();
    assert_batch_status_lookup_rejected_before_tableau_mutation(
        &jit,
        &manifest,
        &wrong_signature,
        |err| match err {
            ArtifactContractError::SignatureMismatch { symbol, actual, .. } => {
                assert_eq!(symbol, BATCH_PIVOT_STATUS_SYMBOL);
                assert!(
                    actual.is_some(),
                    "manifest should carry the original signature"
                );
            }
            other => panic!("expected signature mismatch, got {other:?}"),
        },
    );

    let mut missing_manifest_symbol = manifest.clone();
    missing_manifest_symbol.symbols.clear();
    let missing_symbol_contract = ay_lra_kernel_lookup_contract_for(
        &missing_manifest_symbol,
        BATCH_PIVOT_STATUS_SYMBOL,
        ay_lra_batch_pivot_status_signature(),
    );
    assert_batch_status_lookup_rejected_before_tableau_mutation(
        &jit,
        &missing_manifest_symbol,
        &missing_symbol_contract,
        |err| match err {
            ArtifactContractError::SignatureMismatch {
                symbol,
                actual: None,
                ..
            } => {
                assert_eq!(symbol, BATCH_PIVOT_STATUS_SYMBOL);
            }
            other => panic!("expected missing manifest symbol rejection, got {other:?}"),
        },
    );

    let mut wrong_manifest_checksum = contract.clone();
    wrong_manifest_checksum.manifest_checksum =
        Some(ArtifactChecksum::new(manifest.checksum().get() ^ 1));
    assert_batch_status_lookup_rejected_before_tableau_mutation(
        &jit,
        &manifest,
        &wrong_manifest_checksum,
        |err| match err {
            ArtifactContractError::ChecksumMismatch { component, .. } => {
                assert_eq!(component, "artifact_manifest");
            }
            other => panic!("expected manifest checksum mismatch, got {other:?}"),
        },
    );

    let mut wrong_layout = contract.clone();
    wrong_layout.layout_checksum = ArtifactChecksum::new(contract.layout_checksum.get() ^ 1);
    assert_batch_status_lookup_rejected_before_tableau_mutation(
        &jit,
        &manifest,
        &wrong_layout,
        |err| match err {
            ArtifactContractError::ChecksumMismatch { component, .. } => {
                assert_eq!(component, "layout");
            }
            other => panic!("expected layout checksum mismatch, got {other:?}"),
        },
    );

    let null_symbol = "batch_pivot_status_update_missing";
    let null_signature = ay_lra_batch_pivot_status_signature();
    let null_manifest = ay_lra_kernel_manifest_for(
        null_symbol,
        "batch_pivot_status_update",
        null_signature.clone(),
        true,
        2048,
    );
    let null_contract =
        ay_lra_kernel_lookup_contract_for(&null_manifest, null_symbol, null_signature);
    assert_batch_status_lookup_rejected_before_tableau_mutation(
        &jit,
        &null_manifest,
        &null_contract,
        |err| match err {
            ArtifactContractError::NullSymbolPointer { symbol } => {
                assert_eq!(symbol, null_symbol);
            }
            other => panic!("expected null symbol pointer, got {other:?}"),
        },
    );

    let missing_proof_contract = contract.clone().with_required_proof_evidence();
    assert_batch_status_lookup_rejected_before_tableau_mutation(
        &jit,
        &manifest,
        &missing_proof_contract,
        |err| match err {
            ArtifactContractError::MissingProofEvidence { rejection_code } => {
                assert_eq!(rejection_code, ProofEvidenceRejectionCode::MissingEvidence);
            }
            other => panic!("expected missing proof evidence rejection, got {other:?}"),
        },
    );

    let rejected_proof_contract = contract
        .clone()
        .with_required_proof_evidence()
        .with_proof_evidence(rejected_batch_proof_evidence(&manifest));
    assert_batch_status_lookup_rejected_before_tableau_mutation(
        &jit,
        &manifest,
        &rejected_proof_contract,
        |err| match err {
            ArtifactContractError::ProofEvidenceRejected {
                verifier,
                verdict,
                rejection_code,
                ..
            } => {
                assert_eq!(verifier, "trust-cg-verify");
                assert_eq!(verdict, ProofEvidenceVerdict::VerifierFailure);
                assert_eq!(
                    rejection_code,
                    Some(ProofEvidenceRejectionCode::VerifierFailure)
                );
            }
            other => panic!("expected rejected proof evidence, got {other:?}"),
        },
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
            .get("telemetry_counter_policy")
            .map(String::as_str),
        Some("metadata_only_useful_native_false")
    );
    assert_eq!(
        manifest.metadata.get("useful_native").map(String::as_str),
        Some("false")
    );
}

#[test]
fn ay_lra_basis_row_batch_selector_rejects_audit_fixture_non_promoting() {
    let manifest = ay_lra_kernel_manifest(BATCH_PIVOT_STATUS_SYMBOL);
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let evidence = complete_ay_lra_selector_evidence(&manifest, &proof_manifest);

    let decision = select_ay_lra_aarch64_lowering(&manifest, &proof_manifest, &evidence);

    match decision {
        AYLraAarch64LoweringDecision::RejectNonPromoting { admission } => {
            assert_eq!(
                admission.disposition,
                AYLraManifestDisposition::RejectNonPromoting
            );
            assert!(
                admission
                    .reasons
                    .contains(&AYLraManifestRejectionReason::MissingProofEvidence),
                "audit-only regression fixture must not select certificate-driven native lowering: {:?}",
                admission.reasons
            );
            assert!(admission.non_promoting);
            assert_eq!(admission.useful_native_delta, 0);
            assert_eq!(
                manifest.metadata.get("useful_native").map(String::as_str),
                Some("false")
            );
            assert_eq!(
                manifest
                    .metadata
                    .get("telemetry_counter_policy")
                    .map(String::as_str),
                Some("metadata_only_useful_native_false")
            );
        }
        AYLraAarch64LoweringDecision::UseNative { kind, admission } => {
            panic!("audit-only JIT fixture selected {kind:?}: {admission:?}");
        }
    }
}

#[test]
fn ay_lra_basis_row_batch_telemetry_replay_evidence_stays_non_promoting() {
    let manifest = ay_lra_sparse_affected_row_batch_manifest();
    let proof_manifest = ay_lra_sparse_affected_row_batch_proof_manifest();
    let mut evidence = complete_ay_lra_selector_evidence(&manifest, &proof_manifest);
    use_canonical_basis_row_batch_telemetry_hashes(&mut evidence);
    let telemetry = AYLraBasisRowBatchTelemetryEvidence::private_local().with_canonical_hashes(
        &manifest,
        &proof_manifest,
        &evidence,
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
    assert_eq!(
        telemetry.hashes,
        telemetry.canonical_hashes(&manifest, &proof_manifest, &evidence)
    );
    assert_eq!(
        manifest.metadata.get("useful_native").map(String::as_str),
        Some("false")
    );

    let decision = evaluate_ay_lra_basis_row_batch_telemetry_evidence(
        &manifest,
        &proof_manifest,
        &evidence,
        &telemetry,
    );

    assert_eq!(
        decision.disposition,
        AYLraManifestDisposition::RejectNonPromoting
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::MissingProofEvidence),
        "audit-only JIT fixture should still block product promotion: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramObservedFactMismatch),
        "basis-row telemetry counters should stay bound: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "basis-row telemetry hashes should stay bound: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_sparse_affected_row_batch_pivot_status_evidence_binds_jit_lengths_non_promoting() {
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let success_coefficients = [(0, 1), (2, -1), (4, 3)];
        let (_success_jit, success_f) =
            jit_compile_batch_pivot_status_with_opt_level(&success_coefficients, opt_level);
        let overflow_coefficients = [(0, 1), (1, 2), (4, -1)];
        let (_overflow_jit, overflow_f) =
            jit_compile_batch_pivot_status_with_opt_level(&overflow_coefficients, opt_level);

        let mut observed_lengths = Vec::new();
        let mut observed_rows_committed = Vec::new();
        let mut observed_first_failed_rows = Vec::new();
        let mut ok_statuses = 0;
        let mut overflow_statuses = 0;
        let mut bounds_statuses = 0;
        let mut stale_statuses = 0;

        let mut rows = [[10, 20, 30, 40, 50], [-5, 0, 9, 2, -11], [0, 1, -2, 3, -4]];
        let scales = [7, -3, 0];
        let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();
        let row_output_offsets = [0, 3, 6];
        let mut row_output_lengths = [i64::MIN; 3];
        let mut status = AYLraBatchStatusAbi::poisoned();
        let basis_epochs = [37, 37];
        unsafe {
            success_f(
                row_ptrs.as_mut_ptr(),
                scales.as_ptr(),
                rows.len() as i64,
                row_output_offsets.as_ptr(),
                row_output_lengths.as_mut_ptr(),
                9,
                basis_epochs.as_ptr(),
                &mut status,
            );
        }
        status.assert_matches(AYLraStatus::Ok, AYLraDeopt::None, 3, 0);
        observed_lengths.extend_from_slice(&row_output_lengths);
        observed_rows_committed.push(status.rows_committed as u64);
        observed_first_failed_rows.push(-1);
        ok_statuses += 1;

        let mut rows = [
            [10, 20, 30, 40, 50],
            [i64::MAX, 7, 0, 0, 11],
            [i64::MAX, 9, 0, 0, 13],
        ];
        let scales = [3, 1, 1];
        let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();
        let row_output_offsets = [0, 3, 6];
        let mut row_output_lengths = [i64::MIN; 3];
        let mut status = AYLraBatchStatusAbi::poisoned();
        let basis_epochs = [37, 37];
        unsafe {
            overflow_f(
                row_ptrs.as_mut_ptr(),
                scales.as_ptr(),
                rows.len() as i64,
                row_output_offsets.as_ptr(),
                row_output_lengths.as_mut_ptr(),
                9,
                basis_epochs.as_ptr(),
                &mut status,
            );
        }
        status.assert_matches(
            AYLraStatus::Overflow,
            AYLraDeopt::SparseSubstituteOverflow,
            1,
            1,
        );
        observed_lengths.extend_from_slice(&row_output_lengths);
        observed_rows_committed.push(status.rows_committed as u64);
        observed_first_failed_rows.push(status.detail);
        overflow_statuses += 1;

        let mut rows = [[10, 20, 30, 40, 50], [-5, 0, 9, 2, -11], [0, 1, -2, 3, -4]];
        let scales = [7, -3, 5];
        let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();
        let row_output_offsets = [0, 7, 0];
        let mut row_output_lengths = [i64::MIN; 3];
        let mut status = AYLraBatchStatusAbi::poisoned();
        let basis_epochs = [37, 37];
        unsafe {
            success_f(
                row_ptrs.as_mut_ptr(),
                scales.as_ptr(),
                rows.len() as i64,
                row_output_offsets.as_ptr(),
                row_output_lengths.as_mut_ptr(),
                9,
                basis_epochs.as_ptr(),
                &mut status,
            );
        }
        status.assert_matches(
            AYLraStatus::Bounds,
            AYLraDeopt::SparseSubstituteBounds,
            1,
            1,
        );
        observed_lengths.extend_from_slice(&row_output_lengths);
        observed_rows_committed.push(status.rows_committed as u64);
        observed_first_failed_rows.push(status.detail);
        bounds_statuses += 1;

        let mut rows = [[10, 20, 30, 40, 50], [-5, 0, 9, 2, -11], [0, 1, -2, 3, -4]];
        let scales = [7, -3, 0];
        let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();
        let row_output_offsets = [0, 3, 6];
        let mut row_output_lengths = [i64::MIN; 3];
        let mut status = AYLraBatchStatusAbi::poisoned();
        let basis_epochs = [42, 41];
        unsafe {
            success_f(
                row_ptrs.as_mut_ptr(),
                scales.as_ptr(),
                rows.len() as i64,
                row_output_offsets.as_ptr(),
                row_output_lengths.as_mut_ptr(),
                9,
                basis_epochs.as_ptr(),
                &mut status,
            );
        }
        status.assert_matches(AYLraStatus::Stale, AYLraDeopt::BasisEpochStale, 0, 42);
        observed_lengths.extend_from_slice(&row_output_lengths);
        observed_rows_committed.push(status.rows_committed as u64);
        observed_first_failed_rows.push(-1);
        stale_statuses += 1;

        assert_eq!(
            observed_lengths.as_slice(),
            &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS,
            "opt_level={opt_level:?}"
        );
        assert_eq!(
            observed_rows_committed.as_slice(),
            &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED,
            "opt_level={opt_level:?}"
        );
        assert_eq!(
            observed_rows_committed.iter().sum::<u64>(),
            AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED_TOTAL,
            "opt_level={opt_level:?}"
        );
        assert_eq!(
            observed_first_failed_rows.as_slice(),
            &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_FIRST_FAILED_ROWS,
            "opt_level={opt_level:?}"
        );
        assert_eq!(
            ok_statuses, AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OK_STATUS_COUNT,
            "opt_level={opt_level:?}"
        );
        assert_eq!(
            overflow_statuses, AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OVERFLOW_STATUS_COUNT,
            "opt_level={opt_level:?}"
        );
        assert_eq!(
            bounds_statuses, AY_LRA_SPARSE_AFFECTED_ROW_BATCH_BOUNDS_STATUS_COUNT,
            "opt_level={opt_level:?}"
        );
        assert_eq!(
            stale_statuses, AY_LRA_SPARSE_AFFECTED_ROW_BATCH_STALE_STATUS_COUNT,
            "opt_level={opt_level:?}"
        );
    }

    let manifest = ay_lra_kernel_manifest(BATCH_PIVOT_STATUS_SYMBOL);
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let mut evidence = complete_ay_lra_selector_evidence(&manifest, &proof_manifest);
    use_canonical_basis_row_batch_telemetry_hashes(&mut evidence);
    let affected_row_evidence = AYLraSparseAffectedRowBatchEvidence::private_local()
        .with_canonical_hashes(&manifest, &proof_manifest, &evidence);

    assert_eq!(
        affected_row_evidence.counters.row_output_lengths.as_slice(),
        &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS
    );
    assert_eq!(
        affected_row_evidence.useful_native_delta,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_USEFUL_NATIVE_DELTA
    );
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

    assert_eq!(
        decision.disposition,
        AYLraManifestDisposition::RejectNonPromoting
    );
    assert!(
        decision
            .reasons
            .contains(&AYLraManifestRejectionReason::MissingProofEvidence),
        "audit-only JIT fixture should still block product promotion: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramObservedFactMismatch),
        "sparse affected-row counters should stay bound: {:?}",
        decision.reasons
    );
    assert!(
        !decision
            .reasons
            .contains(&AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch),
        "sparse affected-row hashes should stay bound: {:?}",
        decision.reasons
    );
    assert!(decision.non_promoting);
    assert_eq!(decision.useful_native_delta, 0);
}

#[test]
fn ay_lra_basis_row_batch_real_kernel_admission_reaches_pipeline_and_reducer_audit() {
    let coefficients = [(0, 1), (2, -1), (4, 3)];
    let module = emit_batch_pivot_status_trust_ir(&coefficients);
    let (_jit, f) = jit_compile_batch_pivot_status_with_opt_level(&coefficients, OptLevel::O2);

    let mut row0 = [10, 20, 30, 40, 50];
    let mut row1 = [-5, 0, 9, 2, -11];
    let row_ptrs = [row0.as_mut_ptr(), row1.as_mut_ptr()];
    let scales = [2, -1];
    let row_output_offsets = [0, 0];
    let mut row_output_lengths = [-1, -1];
    let basis_epochs = [37, 37];
    let mut status = AYLraBatchStatusAbi::poisoned();

    unsafe {
        f(
            row_ptrs.as_ptr(),
            scales.as_ptr(),
            row_ptrs.len() as i64,
            row_output_offsets.as_ptr(),
            row_output_lengths.as_mut_ptr(),
            5,
            basis_epochs.as_ptr(),
            &mut status,
        );
    }
    status.assert_matches(AYLraStatus::Ok, AYLraDeopt::None, 2, 0);
    assert_eq!(row_output_lengths, [3, 3]);

    let manifest = ay_lra_kernel_manifest(BATCH_PIVOT_STATUS_SYMBOL);
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    assert_eq!(
        proof_manifest.kernel_family.as_str(),
        AY_LRA_BASIS_UPDATE_KERNEL_FAMILY
    );

    let (prepared_func, shape, encoded) =
        prepared_kernel_function_for_module(&module, OptLevel::O2);
    assert!(shape.real_inst_count > 0);
    assert!(shape.encoded_bytes > 0);

    let input = CandidateRegionExtractionInput::new(
        AY_LRA_BASIS_UPDATE_KERNEL_FAMILY,
        AYLraRewriteKernelFamily::BasisUpdate.default_kernel_name(),
        ay_lra_real_kernel_region_payload(&manifest, &encoded, &shape),
        target_identity_from_manifest(&manifest),
        ay_lra_basis_cost_context(&shape)
            .with_note(format!("manifest_checksum={}", manifest.checksum())),
        ay_lra_basis_sub_zero_transform(),
    )
    .with_function_symbol(BATCH_PIVOT_STATUS_SYMBOL)
    .with_region_label("real-ay-lra-basis-row-batch:o2-machir");
    let extracted = extract_rewrite_admission_candidate(input)
        .expect("real ay LRA basis row-batch kernel should extract for admission");
    assert_eq!(
        extracted.inputs.source_region.kernel_family,
        AY_LRA_BASIS_UPDATE_KERNEL_FAMILY
    );
    assert_eq!(
        extracted.inputs.source_region.function_symbol.as_deref(),
        Some(BATCH_PIVOT_STATUS_SYMBOL)
    );
    assert!(extracted.inputs.proof_assumptions.iter().any(|assumption| {
        assumption.id == "ay-lra-basis-prefix-rollback"
            && assumption
                .formula
                .contains("required_ay_lra_certificate_dependency")
    }));

    let record = extracted
        .to_disabled_record()
        .with_cegis_result(
            &CegisResult::Equivalent {
                proof_hash: AY_LRA_BASIS_SUB_ZERO_PROOF_HASH,
                iterations: 3,
            },
            None,
        )
        .with_certificate_identity(ay_lra_basis_sub_zero_certificate_identity());
    let verdict = ay_lra_basis_admission_verdict(&record, &proof_manifest, &manifest, &encoded);
    let record = record
        .with_proof_guided_admission_verdict(verdict)
        .with_profile_review(
            KernelAllowlist::ay_lra_allowlisted(AYLraRewriteKernelFamily::BasisUpdate),
            ProductGateEvidence::all_passed_record(),
        );

    assert!(record.can_admit_to_declarative_rewrite());
    let json = record.to_json_pretty().expect("admission record JSON");
    let mut opt_func = prepared_func.clone();
    let result = trust_cg_opt::OptimizationPipeline::new(trust_cg_opt::OptLevel::O1)
        .with_admitted_rewrite_records([json])
        .with_rewrite_admission_config(
            trust_cg_opt::rewrite::RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .run_with_report(&mut opt_func);

    assert!(
        result
            .pipeline_report
            .rewrite_admission_load_error
            .is_none()
    );
    let report = result
        .pipeline_report
        .rewrite_admission_load_report
        .expect("real ay LRA admission should be visible in the opt pipeline report");
    assert!(report.loader_enabled);
    assert_eq!(report.input_records, 1);
    assert_eq!(report.parsed_records, 1);
    assert_eq!(report.eligible_records, 1);
    assert_eq!(report.registered_rules, 1);
    assert_eq!(report.loaded_records.len(), 1);
    let loaded = &report.loaded_records[0];
    assert_eq!(loaded.transform_name, AY_LRA_BASIS_SUB_ZERO_TRANSFORM);
    assert_eq!(loaded.kernel_family, AY_LRA_BASIS_UPDATE_KERNEL_FAMILY);
    assert_eq!(
        loaded.kernel_name.as_deref(),
        Some(AYLraRewriteKernelFamily::BasisUpdate.default_kernel_name())
    );
    assert_eq!(loaded.proof_hash, AY_LRA_BASIS_SUB_ZERO_PROOF_HASH);
    assert_eq!(loaded.aarch64_cost_delta, record.aarch64_cost_delta);
    assert!(
        result
            .pass_stats
            .runs
            .iter()
            .any(|(name, count)| name == "declarative-rewrite" && *count == 1)
    );

    let failed_result = CegisResult::NotEquivalent {
        counterexample: ConcreteInput::from_pairs(&[("row_idx", 1), ("output_capacity", 0)]),
        found_by_concrete: false,
    };
    let reducer =
        ReducerMetadata::new(ProofFailureKind::BadCandidate, "ay-lra-real-kernel-reducer")
            .with_artifact(
                "replay/ay-lra-basis-row-batch/reducers/basis-sub-zero-counterexample.json",
                ay_lra_basis_reducer_artifact_hash(&manifest, &encoded),
            )
            .with_follow_up_issue_title(
                "Bad solver candidate: ay LRA basis row-batch real-kernel reducer",
            );
    let failed_record = extracted
        .to_disabled_record()
        .with_cegis_result(&failed_result, Some(reducer));
    let artifact = FailedProofReducerArtifact::from_admission_record(&failed_record)
        .expect("real ay LRA failed proof should produce a reducer artifact");
    assert_eq!(artifact.failure_kind, ProofFailureKind::BadCandidate);
    assert_eq!(artifact.source_region, failed_record.source_region);
    assert_eq!(artifact.target, failed_record.target);
    assert!(artifact.follow_up.body.contains("Parent: #798"));
    assert!(
        artifact
            .follow_up
            .body
            .contains("replay/ay-lra-basis-row-batch")
    );
    let artifact_json = artifact
        .to_json_pretty()
        .expect("real-kernel reducer artifact should serialize");
    assert_eq!(
        FailedProofReducerArtifact::from_json_str(&artifact_json)
            .expect("real-kernel reducer artifact should roundtrip"),
        artifact
    );

    let variable_names = vec!["output_capacity".to_owned(), "row_idx".to_owned()];
    let filter = FailedProofCounterexampleSeedFilter::enabled(
        failed_record.source_region.clone(),
        failed_record.target.clone(),
        variable_names.clone(),
    );
    let corpus = FailedProofCounterexampleCorpus::from_artifacts([&artifact], &filter);
    assert_eq!(corpus.len(), 1);
    let seeds = corpus.concrete_inputs_for_scope(
        &failed_record.source_region,
        &failed_record.target,
        &variable_names,
    );
    assert_eq!(seeds.len(), 1);
    assert_eq!(seeds[0].values.get("row_idx"), Some(&1u64));
    assert_eq!(seeds[0].values.get("output_capacity"), Some(&0u64));
}

#[test]
fn jit_sparse_substitute_zero_elimination_returns_zero_len() {
    let (_jit, f) = jit_compile_sparse_substitute();

    let target_vars = [3u32];
    let target_coeffs = [-6i64];
    let mut out_vars = [0u32; 3];
    let mut out_coeffs = [0i64; 3];

    let raw = unsafe {
        f(
            target_vars.as_ptr(),
            target_coeffs.as_ptr(),
            target_vars.len() as i64,
            3,
            out_vars.as_mut_ptr(),
            out_coeffs.as_mut_ptr(),
        )
    };

    assert_eq!(
        raw, 0,
        "zero-elimination sparse substitute should return length 0, got {raw} with out_vars={out_vars:?} out_coeffs={out_coeffs:?}"
    );
}

#[test]
fn jit_sparse_substitute_single_match_preserves_prefix_and_updates_match() {
    let (_jit, f) = jit_compile_sparse_substitute();

    let target_vars = [2u32, 3u32];
    let target_coeffs = [10i64, 5i64];
    let mut out_vars = [0u32; 4];
    let mut out_coeffs = [0i64; 4];

    let raw = unsafe {
        f(
            target_vars.as_ptr(),
            target_coeffs.as_ptr(),
            target_vars.len() as i64,
            3,
            out_vars.as_mut_ptr(),
            out_coeffs.as_mut_ptr(),
        )
    };

    assert_eq!(raw, 2, "single-match sparse substitute should return len 2");
    assert_eq!(out_vars[..2], [2, 3]);
    assert_eq!(out_coeffs[..2], [10, 11]);
}

#[test]
fn jit_ay_sparse_substitute_row_merge_matches_reference_o2() {
    let pivot = [(1, 1), (3, 2)];
    let (_jit, f) = jit_compile_sparse_substitute_with_opt_level(OptLevel::O2);

    run_sparse_substitute_case(f, &pivot, 1, &[(3, -6)], 3);
    run_sparse_substitute_case(f, &pivot, 1, &[(2, 10), (3, 5), (8, -4)], 3);
    run_sparse_substitute_case(f, &pivot, 1, &[(0, 7), (1, 99), (9, -11)], -2);
    run_sparse_substitute_case(f, &pivot, 1, &[(3, i64::MAX)], 1);
}

#[test]
fn jit_ay_sparse_substitute_row_merge_matches_reference_o0() {
    let pivot = [(1, 1), (3, 2)];
    let (_jit, f) = jit_compile_sparse_substitute_with_opt_level(OptLevel::O0);

    run_sparse_substitute_case(f, &pivot, 1, &[(3, -6)], 3);
    run_sparse_substitute_case(f, &pivot, 1, &[(2, 10), (3, 5), (8, -4)], 3);
    run_sparse_substitute_case(f, &pivot, 1, &[(0, 7), (1, 99), (9, -11)], -2);
    run_sparse_substitute_case(f, &pivot, 1, &[(3, i64::MAX)], 1);
}

#[test]
fn jit_ay_single_row_pivot_update_matches_reference_o0_o2() {
    let coefficients = [(0, 1), (2, -1), (4, 3)];

    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let (_jit, f) = jit_compile_pivot_row_with_opt_level(&coefficients, opt_level);

        for (mut row, scale) in [
            ([10, 20, 30, 40, 50], 7),
            ([-5, 0, 9, 2, -11], -3),
            ([0, 1, -2, 3, -4], 0),
        ] {
            let mut expected = row;
            reference_pivot_row_update(&coefficients, &mut expected, scale);

            unsafe {
                f(row.as_mut_ptr(), scale);
            }

            assert_eq!(row, expected, "opt_level={opt_level:?} scale={scale}");
        }
    }
}

#[test]
fn jit_ay_batch_pivot_update_success_matches_reference_o0_o2() {
    let coefficients = [(0, 1), (2, -1), (4, 3)];

    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let (_jit, f) = jit_compile_batch_pivot_with_opt_level(&coefficients, opt_level);

        let mut rows = [[10, 20, 30, 40, 50], [-5, 0, 9, 2, -11], [0, 1, -2, 3, -4]];
        let scales = [7, -3, 0];
        let mut expected = rows;
        let expected_raw = reference_batch_pivot_update(&coefficients, &mut expected, &scales);
        let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();

        let raw = unsafe { f(row_ptrs.as_mut_ptr(), scales.as_ptr(), rows.len() as i64) };

        assert_eq!(raw, expected_raw, "opt_level={opt_level:?}");
        assert_eq!(rows, expected, "opt_level={opt_level:?}");
    }
}

#[test]
fn jit_ay_batch_pivot_update_returns_first_overflowing_row_o0_o2() {
    let coefficients = [(0, 1), (1, 2), (4, -1)];

    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let (_jit, f) = jit_compile_batch_pivot_with_opt_level(&coefficients, opt_level);

        let mut rows = [
            [10, 20, 30, 40, 50],
            [i64::MAX, 7, 0, 0, 11],
            [i64::MAX, 9, 0, 0, 13],
        ];
        let scales = [3, 1, 1];
        let mut expected = rows;
        let expected_raw = reference_batch_pivot_update(&coefficients, &mut expected, &scales);
        let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();

        let raw = unsafe { f(row_ptrs.as_mut_ptr(), scales.as_ptr(), rows.len() as i64) };

        assert_eq!(expected_raw, 2, "reference case should overflow on row 2");
        assert_eq!(raw, 2, "opt_level={opt_level:?}");
        assert_eq!(
            rows, expected,
            "batch overflow path should preserve exact partial-update semantics at opt_level={opt_level:?}"
        );
    }
}

#[test]
fn jit_ay_batch_pivot_status_reports_rows_committed_and_first_failed_row_o0_o2() {
    assert_eq!(size_of::<AYLraBatchStatusAbi>(), 24);
    assert_eq!(align_of::<AYLraBatchStatusAbi>(), 8);
    assert_eq!(offset_of!(AYLraBatchStatusAbi, status), 0);
    assert_eq!(offset_of!(AYLraBatchStatusAbi, deopt), 1);
    assert_eq!(offset_of!(AYLraBatchStatusAbi, rows_committed), 8);
    assert_eq!(offset_of!(AYLraBatchStatusAbi, detail), 16);

    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let success_coefficients = [(0, 1), (2, -1), (4, 3)];
        let (_jit, f) =
            jit_compile_batch_pivot_status_with_opt_level(&success_coefficients, opt_level);

        let mut rows = [[10, 20, 30, 40, 50], [-5, 0, 9, 2, -11], [0, 1, -2, 3, -4]];
        let scales = [7, -3, 0];
        let mut expected = rows;
        let expected_raw =
            reference_batch_pivot_update(&success_coefficients, &mut expected, &scales);
        let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();
        let row_output_offsets = [0, 3, 6];
        let mut row_output_lengths = [i64::MIN; 3];
        let mut status = AYLraBatchStatusAbi::poisoned();
        let basis_epochs = [37, 37];
        let pre_tableau_digest = tableau_digest(&rows);
        let pre_basis_digest = basis_digest(&basis_epochs);

        unsafe {
            f(
                row_ptrs.as_mut_ptr(),
                scales.as_ptr(),
                rows.len() as i64,
                row_output_offsets.as_ptr(),
                row_output_lengths.as_mut_ptr(),
                9,
                basis_epochs.as_ptr(),
                &mut status,
            );
        }

        assert_eq!(
            expected_raw, 0,
            "reference success case should not overflow"
        );
        status.assert_matches(AYLraStatus::Ok, AYLraDeopt::None, rows.len() as i64, 0);
        assert_eq!(
            rows, expected,
            "success rows mismatch at opt_level={opt_level:?}"
        );
        assert_ne!(
            tableau_digest(&rows),
            pre_tableau_digest,
            "success must record a changed post-tableau digest at opt_level={opt_level:?}"
        );
        assert_eq!(
            basis_digest(&basis_epochs),
            pre_basis_digest,
            "basis digest must be stable for a committed row batch at opt_level={opt_level:?}"
        );
        assert_eq!(
            row_output_lengths,
            [3, 3, 3],
            "success must write exact per-row output lengths at opt_level={opt_level:?}"
        );

        let overflow_coefficients = [(0, 1), (1, 2), (4, -1)];
        let (_jit, f) =
            jit_compile_batch_pivot_status_with_opt_level(&overflow_coefficients, opt_level);

        let mut rows = [
            [10, 20, 30, 40, 50],
            [i64::MAX, 7, 0, 0, 11],
            [i64::MAX, 9, 0, 0, 13],
        ];
        let original_rows = rows;
        let scales = [3, 1, 1];
        let mut expected = rows;
        let expected_raw =
            reference_batch_pivot_update(&overflow_coefficients, &mut expected, &scales);
        let expected_first_failed_row = expected_raw - 1;
        let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();
        let row_output_offsets = [0, 3, 6];
        let mut row_output_lengths = [i64::MIN; 3];
        let mut status = AYLraBatchStatusAbi::poisoned();
        let basis_epochs = [37, 37];
        let pre_basis_digest = basis_digest(&basis_epochs);

        unsafe {
            f(
                row_ptrs.as_mut_ptr(),
                scales.as_ptr(),
                rows.len() as i64,
                row_output_offsets.as_ptr(),
                row_output_lengths.as_mut_ptr(),
                9,
                basis_epochs.as_ptr(),
                &mut status,
            );
        }

        assert_eq!(expected_raw, 2, "reference case should overflow on row 1");
        status.assert_matches(
            AYLraStatus::Overflow,
            AYLraDeopt::SparseSubstituteOverflow,
            expected_first_failed_row,
            expected_first_failed_row,
        );
        assert_ne!(
            status.detail, expected_raw,
            "typed detail should use the zero-based failed row, not the old row+1 sentinel"
        );
        assert_eq!(
            status.rows_committed, expected_first_failed_row,
            "overflow must report the committed prefix length at opt_level={opt_level:?}"
        );
        assert_eq!(
            status.rows_committed, status.detail,
            "overflow rows_committed must match first_failed_row at opt_level={opt_level:?}"
        );
        let failed_row = expected_first_failed_row as usize;
        assert_eq!(
            &rows[..failed_row],
            &expected[..failed_row],
            "overflow should preserve committed prefix updates at opt_level={opt_level:?}"
        );
        assert_eq!(
            &rows[(failed_row + 1)..],
            &original_rows[(failed_row + 1)..],
            "overflow should not mutate rows after the failed row at opt_level={opt_level:?}"
        );
        assert_eq!(
            rows, expected,
            "overflow rows mismatch at opt_level={opt_level:?}"
        );
        assert_eq!(
            row_output_lengths,
            [3, 3, i64::MIN],
            "overflow writes lengths only for rows that pass bounds before arithmetic at opt_level={opt_level:?}"
        );
        assert_eq!(
            basis_digest(&basis_epochs),
            pre_basis_digest,
            "overflow deopt must not mutate basis evidence at opt_level={opt_level:?}"
        );
    }
}

#[test]
fn jit_ay_basis_row_batch_reports_first_middle_last_overflow_rows_o0_o2() {
    let coefficients = [(0, 1), (1, 2), (4, -1)];
    let manifest = ay_lra_kernel_manifest(BATCH_PIVOT_STATUS_SYMBOL);
    assert_eq!(
        manifest
            .layout
            .metadata
            .get("rollback_failure_disposition")
            .map(String::as_str),
        Some("non_promoting_deopt_failed_row_left_uncommitted")
    );

    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let (_jit, f) = jit_compile_batch_pivot_status_with_opt_level(&coefficients, opt_level);

        for (label, failing_row) in [("first", 0usize), ("middle", 1usize), ("last", 2usize)] {
            let mut rows = [[10, 20, 30, 40, 50], [-5, 0, 9, 2, -11], [0, 1, -2, 3, -4]];
            rows[failing_row][0] = i64::MAX;
            let original_rows = rows;
            let scales = [1, 1, 1];
            let mut expected = rows;
            let expected_raw = reference_batch_pivot_update(&coefficients, &mut expected, &scales);
            assert_eq!(
                expected_raw,
                failing_row as i64 + 1,
                "reference overflow row for {label}"
            );

            let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();
            let row_output_offsets = [0, 3, 6];
            let mut row_output_lengths = [i64::MIN; 3];
            let mut status = AYLraBatchStatusAbi::poisoned();
            let basis_epochs = [37, 37];
            let pre_basis_digest = basis_digest(&basis_epochs);

            unsafe {
                f(
                    row_ptrs.as_mut_ptr(),
                    scales.as_ptr(),
                    rows.len() as i64,
                    row_output_offsets.as_ptr(),
                    row_output_lengths.as_mut_ptr(),
                    9,
                    basis_epochs.as_ptr(),
                    &mut status,
                );
            }

            let failed_row = failing_row as i64;
            status.assert_matches(
                AYLraStatus::Overflow,
                AYLraDeopt::SparseSubstituteOverflow,
                failed_row,
                failed_row,
            );
            assert_eq!(
                &rows[..failing_row],
                &expected[..failing_row],
                "overflow {label} should commit the exact prefix at opt_level={opt_level:?}"
            );
            assert_eq!(
                &rows[failing_row..],
                &original_rows[failing_row..],
                "rollback-failure disposition for overflow {label} must leave failed and later rows uncommitted at opt_level={opt_level:?}"
            );
            for (idx, &actual_len) in row_output_lengths.iter().enumerate().take(rows.len()) {
                let expected_len = if idx <= failing_row { 3 } else { i64::MIN };
                assert_eq!(
                    actual_len, expected_len,
                    "overflow {label} row_output_lengths[{idx}] remains commit-log evidence at opt_level={opt_level:?}"
                );
            }
            assert_eq!(basis_digest(&basis_epochs), pre_basis_digest);
        }
    }
}

#[test]
fn jit_ay_batch_pivot_status_reports_bounds_and_preserves_partial_rows_o0_o2() {
    let coefficients = [(0, 1), (2, -1), (4, 3)];

    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let (_jit, f) = jit_compile_batch_pivot_status_with_opt_level(&coefficients, opt_level);

        for (label, row_output_offsets, expected_failed_row) in [
            ("first", [7, 0, 0], 0usize),
            ("middle", [0, 7, 0], 1usize),
            ("last", [0, 3, 7], 2usize),
        ] {
            let mut rows = [[10, 20, 30, 40, 50], [-5, 0, 9, 2, -11], [0, 1, -2, 3, -4]];
            let original_rows = rows;
            let scales = [7, -3, 5];
            let mut expected = rows;
            reference_batch_pivot_update(
                &coefficients,
                &mut expected[..expected_failed_row],
                &scales[..expected_failed_row],
            );
            let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();
            let mut row_output_lengths = [i64::MIN; 3];
            let mut status = AYLraBatchStatusAbi::poisoned();
            let basis_epochs = [37, 37];
            let pre_basis_digest = basis_digest(&basis_epochs);

            unsafe {
                f(
                    row_ptrs.as_mut_ptr(),
                    scales.as_ptr(),
                    rows.len() as i64,
                    row_output_offsets.as_ptr(),
                    row_output_lengths.as_mut_ptr(),
                    9,
                    basis_epochs.as_ptr(),
                    &mut status,
                );
            }

            let failed_row = expected_failed_row as i64;
            status.assert_matches(
                AYLraStatus::Bounds,
                AYLraDeopt::SparseSubstituteBounds,
                failed_row,
                failed_row,
            );
            assert_eq!(
                &rows[..expected_failed_row],
                &expected[..expected_failed_row],
                "bounds {label} should commit only the proven prefix at opt_level={opt_level:?}"
            );
            assert_eq!(
                &rows[expected_failed_row..],
                &original_rows[expected_failed_row..],
                "bounds {label} must leave failed and later rows unchanged at opt_level={opt_level:?}"
            );
            for (idx, &actual_len) in row_output_lengths.iter().enumerate().take(rows.len()) {
                let expected_len = if idx < expected_failed_row {
                    3
                } else {
                    i64::MIN
                };
                assert_eq!(
                    actual_len, expected_len,
                    "bounds {label} row_output_lengths[{idx}] at opt_level={opt_level:?}"
                );
            }
            assert_eq!(
                basis_digest(&basis_epochs),
                pre_basis_digest,
                "bounds {label} must not mutate basis evidence at opt_level={opt_level:?}"
            );
        }
    }
}

#[test]
fn jit_ay_batch_pivot_status_reports_stale_basis_epoch_before_mutating_rows_o0_o2() {
    let coefficients = [(0, 1), (2, -1), (4, 3)];

    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let (_jit, f) = jit_compile_batch_pivot_status_with_opt_level(&coefficients, opt_level);

        let mut rows = [[10, 20, 30, 40, 50], [-5, 0, 9, 2, -11], [0, 1, -2, 3, -4]];
        let original_rows = rows;
        let scales = [7, -3, 0];
        let mut row_ptrs: Vec<*mut i64> = rows.iter_mut().map(|row| row.as_mut_ptr()).collect();
        let row_output_offsets = [0, 3, 6];
        let mut row_output_lengths = [i64::MIN; 3];
        let mut status = AYLraBatchStatusAbi::poisoned();
        let current_basis_epoch = 42;
        let expected_basis_epoch = 41;
        let basis_epochs = [current_basis_epoch, expected_basis_epoch];
        let pre_tableau_digest = tableau_digest(&rows);
        let pre_basis_digest = basis_digest(&basis_epochs);

        unsafe {
            f(
                row_ptrs.as_mut_ptr(),
                scales.as_ptr(),
                rows.len() as i64,
                row_output_offsets.as_ptr(),
                row_output_lengths.as_mut_ptr(),
                9,
                basis_epochs.as_ptr(),
                &mut status,
            );
        }

        status.assert_matches(
            AYLraStatus::Stale,
            AYLraDeopt::BasisEpochStale,
            0,
            current_basis_epoch,
        );
        assert_eq!(
            rows, original_rows,
            "stale basis epoch must leave rows unchanged at opt_level={opt_level:?}"
        );
        assert_eq!(
            tableau_digest(&rows),
            pre_tableau_digest,
            "stale basis epoch must preserve pre-tableau digest at opt_level={opt_level:?}"
        );
        assert_eq!(
            basis_digest(&basis_epochs),
            pre_basis_digest,
            "stale basis epoch must preserve basis digest at opt_level={opt_level:?}"
        );
        assert_eq!(
            row_output_lengths,
            [i64::MIN; 3],
            "stale basis epoch must not write row output lengths at opt_level={opt_level:?}"
        );
    }
}

#[test]
fn jit_ay_sparse_substitute_mul_add_code_shape_uses_madd_o2() {
    // Coeff 11 = 8+2+1 needs >=3 signed power-of-two terms, so `MulShiftReduce`
    // (mul-by-small-constant strength reduction, 1dec870) BAILS and the genuine
    // `coeff*scale + acc` MADD fusion is exercised. Small coeffs like 3 (=2+1)
    // are strength-reduced to a cheaper shift-add and would show madd_count 0 —
    // correct, but not what this test validates.
    let module = emit_pivot_row_trust_ir(&[(0, 1), (2, -1), (4, 11)]);
    let shape = code_shape_for_module(&module, OptLevel::O2);

    eprintln!("ay sparse row-update O2 code shape: {shape:#?}");

    assert!(
        shape.madd_count >= 1,
        "one-use coeff*scale + accumulator update should select at least one MADD: {shape:#?}"
    );
    assert_eq!(
        shape.mul_count, 0,
        "non-overflow row-update hot path should not leave a standalone MUL: {shape:#?}"
    );
    assert_eq!(
        shape.smulh_count, 0,
        "non-overflow row-update lane should not use overflow high-half multiply: {shape:#?}"
    );
    assert_eq!(
        shape.adds_count, 0,
        "non-overflow row-update lane should not set overflow flags: {shape:#?}"
    );
    assert_eq!(
        shape.subs_count, 0,
        "non-overflow row-update lane should not set overflow flags: {shape:#?}"
    );
    assert!(
        shape.real_inst_count > 0 && shape.encoded_bytes >= shape.real_inst_count * 4,
        "prepared AArch64 code should encode to non-empty fixed-width instructions: {shape:#?}"
    );
}

#[test]
fn jit_ay_sparse_substitute_overflow_code_shape_tracks_checked_path_o2() {
    // Coeff 11 (>=3 power-of-two terms) so `MulShiftReduce` bails and the
    // checked multiply keeps its canonical MUL+SMULH high-half overflow test;
    // a small coeff like 3 strength-reduces the low half to a shift-add (the lo
    // stays bit-exact, SMULH still detects overflow — correct, but not the
    // MUL+SMULH shape this test asserts).
    let module = emit_batch_pivot_trust_ir(&[(0, 1), (2, -1), (4, 11)]);
    let shape = code_shape_for_module(&module, OptLevel::O2);

    eprintln!("ay sparse batch overflow O2 code shape: {shape:#?}");

    assert!(
        shape.adds_count >= 1,
        "checked add overflow should lower through ADDS on the hot checked path: {shape:#?}"
    );
    assert!(
        shape.subs_count >= 1,
        "checked sub overflow should lower through SUBS on the hot checked path: {shape:#?}"
    );
    assert!(
        shape.mul_count >= 1 && shape.smulh_count >= 1,
        "checked multiply overflow should keep MUL+SMULH high-half test: {shape:#?}"
    );
    assert!(
        shape.cset_count + shape.cond_branch_count >= 3,
        "checked add/sub/mul overflow flags should feed materialized booleans or cold-exit branches: {shape:#?}"
    );
    assert!(
        shape.branch_count >= 6,
        "overflow lane should retain explicit branches to the cold exit: {shape:#?}"
    );
}

#[test]
fn jit_ay_sparse_substitute_full_merge_code_shape_report_o2() {
    // pivot_coeff 11 (>=3 power-of-two terms) so `MulShiftReduce` bails and the
    // checked multiplies keep their canonical MUL+SMULH overflow tests; coeff 2
    // (a power of two) strength-reduces to a shift and shows mul_count 0.
    let module = emit_single_pivot_sparse_substitute_trust_ir(3, 11, 1);
    let shape = code_shape_for_module(&module, OptLevel::O2);

    eprintln!("ay sparse substitute full merge O2 code shape: {shape:#?}");

    assert!(
        shape.madd_count + shape.reg_offset_mem_count >= 4,
        "full sparse merge should expose the row-indexing address shapes (MADDs, or \
         extended-register loads/stores once the ext-addr fold claims them): {shape:#?}"
    );
    assert!(
        shape.mul_count >= 2 && shape.smulh_count >= 2,
        "full sparse merge should still measure checked multiply overflow paths: {shape:#?}"
    );
    assert!(
        shape.adds_count >= 1,
        "full sparse merge should measure checked add overflow lowering: {shape:#?}"
    );
    assert!(
        shape.cset_count + shape.cond_branch_count >= 4,
        "full sparse merge should keep overflow/comparison flag consumers visible: {shape:#?}"
    );
    assert!(
        shape.branch_count >= 12,
        "full sparse merge should keep branch-heavy sorted-merge control flow visible: {shape:#?}"
    );
    assert!(
        shape.real_inst_count <= 320,
        "full sparse merge O2 code shape unexpectedly grew past the current acceptance envelope: {shape:#?}"
    );
    assert!(
        shape.spill_slot_count <= 16,
        "full sparse merge O2 register pressure unexpectedly grew past the current acceptance envelope: {shape:#?}"
    );
}

#[test]
fn jit_ay_sparse_substitute_mul_add_code_shape_strength_reduces_constant_o2() {
    // Complement of `uses_madd_o2` above: coeff 3 (= 2+1) IS claimed by
    // `MulShiftReduce`, so the row update must lower to a shift+add chain
    // with no MADD/MUL on the hot dependency chain. `ShiftAluFuse` may then
    // fold the standalone LSL into a shifted-register ADD, so no standalone
    // LSL is required — only the absence of MADD/MUL plus an add-shaped chain.
    let module = emit_pivot_row_trust_ir(&[(0, 1), (2, -1), (4, 3)]);
    let shape = code_shape_for_module(&module, OptLevel::O2);

    eprintln!("ay sparse row-update O2 code shape: {shape:#?}");

    assert_eq!(
        shape.madd_count, 0,
        "multiply-by-three MADD should be strength-reduced off the hot dependency chain: {shape:#?}"
    );
    assert_eq!(
        shape.mul_count, 0,
        "non-overflow row-update hot path should not leave a standalone MUL: {shape:#?}"
    );
    assert!(
        shape.lsl_ri_count + shape.add_rr_count >= 2,
        "multiply-by-three row update should lower to a (possibly shift-fused) add chain: {shape:#?}"
    );
    assert_eq!(
        shape.smulh_count, 0,
        "non-overflow row-update lane should not use overflow high-half multiply: {shape:#?}"
    );
    assert_eq!(
        shape.adds_count, 0,
        "non-overflow row-update lane should not set overflow flags: {shape:#?}"
    );
    assert_eq!(
        shape.subs_count, 0,
        "non-overflow row-update lane should not set overflow flags: {shape:#?}"
    );
    assert!(
        shape.real_inst_count > 0 && shape.encoded_bytes >= shape.real_inst_count * 4,
        "prepared AArch64 code should encode to non-empty fixed-width instructions: {shape:#?}"
    );
}

#[test]
fn jit_ay_sparse_substitute_overflow_code_shape_strength_reduces_low_product_o2() {
    // Complement of `tracks_checked_path_o2` above: with coeff 3 the checked
    // multiply's LOW product strength-reduces to shift/add (the shift may be
    // fused into a shifted-register ALU form by `ShiftAluFuse`) while SMULH is
    // retained for the overflow test.
    let module = emit_batch_pivot_trust_ir(&[(0, 1), (2, -1), (4, 3)]);
    let shape = code_shape_for_module(&module, OptLevel::O2);

    eprintln!("ay sparse batch overflow O2 code shape: {shape:#?}");

    assert!(
        shape.adds_count >= 1,
        "checked add overflow should lower through ADDS on the hot checked path: {shape:#?}"
    );
    assert!(
        shape.subs_count >= 1,
        "checked sub overflow should lower through SUBS on the hot checked path: {shape:#?}"
    );
    assert_eq!(
        shape.mul_count, 0,
        "checked multiply's low product should be strength-reduced: {shape:#?}"
    );
    assert!(
        shape.smulh_count >= 1,
        "checked multiply should retain the SMULH overflow test alongside its strength-reduced low product: {shape:#?}"
    );
    assert!(
        shape.cset_count + shape.cond_branch_count >= 3,
        "checked add/sub/mul overflow flags should feed materialized booleans or cold-exit branches: {shape:#?}"
    );
    assert!(
        shape.branch_count >= 6,
        "overflow lane should retain explicit branches to the cold exit: {shape:#?}"
    );
}

#[test]
fn jit_ay_sparse_substitute_full_merge_code_shape_strength_reduced_o2() {
    // Complement of `report_o2` above: pivot coeff 2 (a power of two)
    // strength-reduces every checked-multiply low product while the SMULH
    // high-half overflow tests survive.
    let module = emit_single_pivot_sparse_substitute_trust_ir(3, 2, 1);
    let shape = code_shape_for_module(&module, OptLevel::O2);

    eprintln!("ay sparse substitute full merge O2 code shape: {shape:#?}");

    assert!(
        shape.madd_count + shape.reg_offset_mem_count >= 4,
        "full sparse merge should expose the row-indexing address shapes (MADDs, or \
         extended-register loads/stores once the ext-addr fold claims them): {shape:#?}"
    );
    assert_eq!(
        shape.mul_count, 0,
        "full sparse merge low products should be strength-reduced: {shape:#?}"
    );
    assert!(
        shape.lsl_ri_count >= 2 && shape.smulh_count >= 2,
        "full sparse merge should retain checked-multiply high halves alongside strength-reduced low products: {shape:#?}"
    );
    assert!(
        shape.adds_count >= 1,
        "full sparse merge should measure checked add overflow lowering: {shape:#?}"
    );
    assert!(
        shape.cset_count + shape.cond_branch_count >= 4,
        "full sparse merge should keep overflow/comparison flag consumers visible: {shape:#?}"
    );
    assert!(
        shape.branch_count >= 12,
        "full sparse merge should keep branch-heavy sorted-merge control flow visible: {shape:#?}"
    );
    assert!(
        shape.real_inst_count <= 320,
        "full sparse merge O2 code shape unexpectedly grew past the current acceptance envelope: {shape:#?}"
    );
    assert!(
        shape.spill_slot_count <= 16,
        "full sparse merge O2 register pressure unexpectedly grew past the current acceptance envelope: {shape:#?}"
    );
}

#[test]
fn jit_ay_sparse_substitute_apple_aarch64_benchmark_lane_smoke() {
    if !cfg!(target_os = "macos") {
        eprintln!("Skipping Apple/AArch64 benchmark lane on non-macOS aarch64 host");
        return;
    }

    let pivot = [(1, 1), (3, 2)];
    let case_zero = [(3, -6)];
    let case_match = [(2, 10), (3, 5), (8, -4)];
    let case_skip = [(0, 7), (1, 99), (9, -11)];
    let cases = [
        (&case_zero[..], 3),
        (&case_match[..], 3),
        (&case_skip[..], -2),
    ];

    let (jit, f) = jit_compile_sparse_substitute_with_opt_level(OptLevel::O2);
    let module = emit_single_pivot_sparse_substitute_trust_ir(3, 2, 1);
    let shape = code_shape_for_module(&module, OptLevel::O2);

    let iterations = std::env::var("TRUST_CG_SPARSE_SUBSTITUTE_BENCH_ITERS")
        .ok()
        .and_then(|raw| raw.parse::<usize>().ok())
        .unwrap_or(256)
        .max(1);

    let start = Instant::now();
    let mut checksum = 0i64;
    for _ in 0..iterations {
        for (target, scale) in cases {
            run_sparse_substitute_case(f, &pivot, 1, target, scale);
            checksum = checksum
                .wrapping_add(scale)
                .wrapping_add(target.len() as i64);
        }
    }
    let elapsed = start.elapsed();
    std::hint::black_box(checksum);

    let calls = iterations * cases.len();
    let ns_per_call = elapsed.as_nanos() / calls as u128;
    eprintln!(
        "ay sparse substitute Apple/AArch64 benchmark lane: calls={calls} elapsed={elapsed:?} ns_per_call={ns_per_call} jit_metrics={:?} shape={shape:#?}",
        jit.metrics
    );

    assert!(elapsed.as_nanos() > 0, "benchmark lane should record time");
    assert_eq!(jit.metrics.function_count, 1);
    assert!(jit.metrics.code_size_bytes > 0);
    assert!(
        shape.madd_count + shape.reg_offset_mem_count >= 4,
        "benchmark lane should exercise the O2 sparse merge's row-indexing shapes \
         (MADD-bearing, or extended-register addressing after the ext-addr fold): {shape:#?}"
    );
}

#[test]
fn jit_sparse_substitute_zero_elimination_returns_zero_len_o0() {
    let (_jit, f) = jit_compile_sparse_substitute_with_opt_level(OptLevel::O0);

    let target_vars = [3u32];
    let target_coeffs = [-6i64];
    let mut out_vars = [0u32; 3];
    let mut out_coeffs = [0i64; 3];

    let raw = unsafe {
        f(
            target_vars.as_ptr(),
            target_coeffs.as_ptr(),
            target_vars.len() as i64,
            3,
            out_vars.as_mut_ptr(),
            out_coeffs.as_mut_ptr(),
        )
    };

    assert_eq!(raw, 0, "O0 zero-elimination should return length 0");
}

#[test]
fn jit_sparse_substitute_single_match_preserves_prefix_and_updates_match_o0() {
    let (_jit, f) = jit_compile_sparse_substitute_with_opt_level(OptLevel::O0);

    let target_vars = [2u32, 3u32];
    let target_coeffs = [10i64, 5i64];
    let mut out_vars = [0u32; 4];
    let mut out_coeffs = [0i64; 4];

    let raw = unsafe {
        f(
            target_vars.as_ptr(),
            target_coeffs.as_ptr(),
            target_vars.len() as i64,
            3,
            out_vars.as_mut_ptr(),
            out_coeffs.as_mut_ptr(),
        )
    };

    assert_eq!(
        raw, 2,
        "O0 single-match sparse substitute should return len 2"
    );
    assert_eq!(out_vars[..2], [2, 3]);
    assert_eq!(out_coeffs[..2], [10, 11]);
}

#[test]
fn jit_sparse_substitute_single_match_preserves_prefix_and_updates_match_o2_explicit() {
    let config = PipelineConfig {
        opt_level: OptLevel::O2,
        ..PipelineConfig::default()
    };
    let (_jit, f) = jit_compile_sparse_substitute_with_pipeline_config(config);

    let target_vars = [2u32, 3u32];
    let target_coeffs = [10i64, 5i64];
    let mut out_vars = [0u32; 4];
    let mut out_coeffs = [0i64; 4];

    let raw = unsafe {
        f(
            target_vars.as_ptr(),
            target_coeffs.as_ptr(),
            target_vars.len() as i64,
            3,
            out_vars.as_mut_ptr(),
            out_coeffs.as_mut_ptr(),
        )
    };

    assert_eq!(raw, 2, "O2 pipeline should return len 2");
    assert_eq!(out_vars[..2], [2, 3]);
    assert_eq!(out_coeffs[..2], [10, 11]);
}

#[test]
fn jit_sparse_substitute_single_match_preserves_prefix_and_updates_match_o2_post_ra() {
    let config = PipelineConfig {
        opt_level: OptLevel::O2,
        ..PipelineConfig::default()
    };
    let (_jit, f) = jit_compile_sparse_substitute_with_pipeline_config(config);

    let target_vars = [2u32, 3u32];
    let target_coeffs = [10i64, 5i64];
    let mut out_vars = [0u32; 4];
    let mut out_coeffs = [0i64; 4];

    let raw = unsafe {
        f(
            target_vars.as_ptr(),
            target_coeffs.as_ptr(),
            target_vars.len() as i64,
            3,
            out_vars.as_mut_ptr(),
            out_coeffs.as_mut_ptr(),
        )
    };

    assert_eq!(raw, 2, "O2 without post-RA opt should return len 2");
    assert_eq!(out_vars[..2], [2, 3]);
    assert_eq!(out_coeffs[..2], [10, 11]);
}
