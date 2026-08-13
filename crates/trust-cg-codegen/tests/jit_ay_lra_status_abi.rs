// trust-cg-codegen/tests/jit_ay_lra_status_abi.rs
//
// Test-local expected ay LRA sparse-substitute status ABI. This is intentionally
// kept out of production modules until the shared ay contract type lands.

#![cfg(target_arch = "aarch64")]

#[path = "common/fixture_contract.rs"]
mod fixture_contract;
use fixture_contract::FixtureContractLookup;

use std::collections::HashMap;
use std::mem::{align_of, offset_of, size_of};

use trust_cg_codegen::Target;
use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, ArtifactContractError, ArtifactSection,
    ArtifactSectionKind, ArtifactSymbol, DeterministicArtifactManifest, Endianness, FieldLayout,
    InvalidationKey, JitArtifactKind, LayoutManifest, ProofEvidenceSummary, ProofPolicy,
    RecordLayout, SymbolLookupContract, SymbolSignature, SymbolVisibility, TargetDescriptor,
    TargetOperatingSystem,
};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::regs::{FP, SP, WZR, XZR};
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, PReg, SpecialReg};
use trust_cg_lower::instructions::Block as LowerBlock;
use trust_cg_lower::{
    AppleAArch64ABI, ArgLocation, ISelOperand, InstructionSelector, Type as LowerType,
};
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, ICmpOp,
    Inst, InstrNode, Module as TrustIrModule, OverflowOp, Ty, ValueId,
};

const STATUS_NATIVE_PAYLOAD_SHA256: &str = "sha256:ay-lra-status-probe-native-payload";
const STATUS_PROOF_REPORT_SHA256: &str = "sha256:ay-lra-status-probe-proof-report";
const STATUS_SYMBOL: &str = "ay_lra_sparse_substitute_status_probe";
const STATUS_RECORD: &str = "AYLraSparseSubstituteStatusAbi";
const AFFECTED_ROW_BATCH_STATUS_SYMBOL: &str = "ay_lra_sparse_affected_row_batch_status_probe";
const AFFECTED_ROW_BATCH_STATUS_RECORD: &str = "AYLraSparseAffectedRowBatchStatusAbi";
const AFFECTED_ROW_BATCH_ROWS: usize = 3;

type AYLraStatusProbeFn =
    unsafe extern "C" fn(i64, i64, i64, i64, i64, i64, *mut ExpectedAYLraStatusAbi);
type AYLraAffectedRowBatchStatusProbeFn = unsafe extern "C" fn(
    i64,
    i64,
    i64,
    i64,
    i64,
    *mut i64,
    *mut ExpectedAYLraAffectedRowBatchStatusAbi,
);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum ExpectedAYLraStatus {
    Ok = 0,
    Bounds = 1,
    Overflow = 2,
    Stale = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum ExpectedAYLraDeopt {
    None = 0,
    SparseSubstituteBounds = 1,
    SparseSubstituteOverflow = 2,
    BasisEpochStale = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
struct ExpectedAYLraStatusAbi {
    status: u8,
    deopt: u8,
    reserved: [u8; 6],
    value: i64,
    detail: i64,
}

impl ExpectedAYLraStatusAbi {
    const fn poisoned() -> Self {
        Self {
            status: 0xff,
            deopt: 0xff,
            reserved: [0xaa; 6],
            value: i64::MIN,
            detail: i64::MIN,
        }
    }

    fn assert_matches(
        &self,
        status: ExpectedAYLraStatus,
        deopt: ExpectedAYLraDeopt,
        value: i64,
        detail: i64,
    ) {
        assert_eq!(self.status, status as u8);
        assert_eq!(self.deopt, deopt as u8);
        assert_eq!(self.reserved, [0xaa; 6]);
        assert_eq!(self.value, value);
        assert_eq!(self.detail, detail);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
struct ExpectedAYLraAffectedRowBatchStatusAbi {
    status: u8,
    deopt: u8,
    reserved: [u8; 6],
    rows_committed: i64,
    first_failed_row: i64,
}

impl ExpectedAYLraAffectedRowBatchStatusAbi {
    const fn poisoned() -> Self {
        Self {
            status: 0xff,
            deopt: 0xff,
            reserved: [0xaa; 6],
            rows_committed: i64::MIN,
            first_failed_row: i64::MIN,
        }
    }

    fn assert_matches(
        &self,
        status: ExpectedAYLraStatus,
        deopt: ExpectedAYLraDeopt,
        rows_committed: i64,
        first_failed_row: i64,
    ) {
        assert_eq!(self.status, status as u8);
        assert_eq!(self.deopt, deopt as u8);
        assert_eq!(self.reserved, [0xaa; 6]);
        assert_eq!(self.rows_committed, rows_committed);
        assert_eq!(self.first_failed_row, first_failed_row);
        assert!(
            self.rows_committed >= 0 && self.first_failed_row >= 0,
            "sparse affected-row batch status must use typed nonnegative fields, not negative sentinels"
        );
    }
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn push_result(block: &mut TrustIrBlock, next_value: &mut u32, inst: Inst) -> ValueId {
    let result = v(*next_value);
    *next_value += 1;
    block.body.push(InstrNode::new(inst).with_result(result));
    result
}

fn push_void(block: &mut TrustIrBlock, inst: Inst) {
    block.body.push(InstrNode::new(inst));
}

fn iconst(block: &mut TrustIrBlock, next_value: &mut u32, ty: Ty, int: i128) -> ValueId {
    push_result(
        block,
        next_value,
        Inst::Const {
            ty,
            value: Constant::Int(int),
        },
    )
}

fn byte_gep(
    block: &mut TrustIrBlock,
    next_value: &mut u32,
    base: ValueId,
    offset: i128,
) -> ValueId {
    let offset = iconst(block, next_value, Ty::U64, offset);
    push_result(
        block,
        next_value,
        Inst::GEP {
            pointee_ty: Ty::U8,
            base,
            indices: vec![offset],
            inbounds: false,
        },
    )
}

fn store_volatile(block: &mut TrustIrBlock, ty: Ty, ptr: ValueId, value: ValueId) {
    push_void(
        block,
        Inst::Store {
            ty,
            ptr,
            value,
            volatile: true,
            align: None,
        },
    );
}

fn store_u8_const(
    block: &mut TrustIrBlock,
    next_value: &mut u32,
    out: ValueId,
    offset: i128,
    byte: u8,
) {
    let ptr = if offset == 0 {
        out
    } else {
        byte_gep(block, next_value, out, offset)
    };
    let value = iconst(block, next_value, Ty::U8, byte as i128);
    store_volatile(block, Ty::U8, ptr, value);
}

fn store_i64_value(
    block: &mut TrustIrBlock,
    next_value: &mut u32,
    out: ValueId,
    offset: i128,
    value: ValueId,
) {
    let ptr = byte_gep(block, next_value, out, offset);
    store_volatile(block, Ty::I64, ptr, value);
}

fn store_plain_i64_value(
    block: &mut TrustIrBlock,
    next_value: &mut u32,
    out: ValueId,
    offset: i128,
    value: ValueId,
) {
    let ptr = byte_gep(block, next_value, out, offset);
    push_void(
        block,
        Inst::Store {
            ty: Ty::I64,
            ptr,
            value,
            volatile: false,
            align: None,
        },
    );
}

fn store_row_length_const(
    block: &mut TrustIrBlock,
    next_value: &mut u32,
    row_lengths: ValueId,
    row_index: usize,
    length: i128,
) {
    let value = iconst(block, next_value, Ty::I64, length);
    store_plain_i64_value(
        block,
        next_value,
        row_lengths,
        (row_index * size_of::<i64>()) as i128,
        value,
    );
}

fn write_status_record(
    block: &mut TrustIrBlock,
    next_value: &mut u32,
    out: ValueId,
    status: ExpectedAYLraStatus,
    deopt: ExpectedAYLraDeopt,
    value: ValueId,
    detail: ValueId,
) {
    store_u8_const(block, next_value, out, 0, status as u8);
    store_u8_const(block, next_value, out, 1, deopt as u8);
    store_i64_value(block, next_value, out, 8, value);
    store_i64_value(block, next_value, out, 16, detail);
}

fn return_void(block: &mut TrustIrBlock) {
    push_void(block, Inst::Return { values: vec![] });
}

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

fn ay_lra_affected_row_batch_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            i64_value(), // affected rows in the batch
            i64_value(), // per-row output capacity
            i64_value(), // synthetic failure mode: 0 ok, 1 bounds, 2 overflow
            i64_value(), // current basis epoch
            i64_value(), // expected basis epoch
            ptr_value(), // i64 row-output lengths[AFFECTED_ROW_BATCH_ROWS]
            ptr_value(), // AYLraSparseAffectedRowBatchStatusAbi*
        ],
        vec![],
    )
}

fn wrong_status_signature() -> SymbolSignature {
    let mut signature = ay_lra_status_signature();
    signature.params[0] = AbiValue::new(AbiValueKind::I32);
    signature
}

fn ay_lra_status_record_layout() -> RecordLayout {
    RecordLayout {
        name: STATUS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: size_of::<ExpectedAYLraStatusAbi>() as u64,
        alignment_bytes: align_of::<ExpectedAYLraStatusAbi>() as u32,
        fields: vec![
            FieldLayout {
                name: "status".to_owned(),
                offset_bytes: offset_of!(ExpectedAYLraStatusAbi, status) as u64,
                size_bytes: size_of::<u8>() as u64,
                alignment_bytes: align_of::<u8>() as u32,
            },
            FieldLayout {
                name: "deopt".to_owned(),
                offset_bytes: offset_of!(ExpectedAYLraStatusAbi, deopt) as u64,
                size_bytes: size_of::<u8>() as u64,
                alignment_bytes: align_of::<u8>() as u32,
            },
            FieldLayout {
                name: "reserved".to_owned(),
                offset_bytes: offset_of!(ExpectedAYLraStatusAbi, reserved) as u64,
                size_bytes: size_of::<[u8; 6]>() as u64,
                alignment_bytes: align_of::<[u8; 6]>() as u32,
            },
            FieldLayout {
                name: "value".to_owned(),
                offset_bytes: offset_of!(ExpectedAYLraStatusAbi, value) as u64,
                size_bytes: size_of::<i64>() as u64,
                alignment_bytes: align_of::<i64>() as u32,
            },
            FieldLayout {
                name: "detail".to_owned(),
                offset_bytes: offset_of!(ExpectedAYLraStatusAbi, detail) as u64,
                size_bytes: size_of::<i64>() as u64,
                alignment_bytes: align_of::<i64>() as u32,
            },
        ],
    }
}

fn ay_lra_affected_row_batch_status_record_layout() -> RecordLayout {
    RecordLayout {
        name: AFFECTED_ROW_BATCH_STATUS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: size_of::<ExpectedAYLraAffectedRowBatchStatusAbi>() as u64,
        alignment_bytes: align_of::<ExpectedAYLraAffectedRowBatchStatusAbi>() as u32,
        fields: vec![
            FieldLayout {
                name: "status".to_owned(),
                offset_bytes: offset_of!(ExpectedAYLraAffectedRowBatchStatusAbi, status) as u64,
                size_bytes: size_of::<u8>() as u64,
                alignment_bytes: align_of::<u8>() as u32,
            },
            FieldLayout {
                name: "deopt".to_owned(),
                offset_bytes: offset_of!(ExpectedAYLraAffectedRowBatchStatusAbi, deopt) as u64,
                size_bytes: size_of::<u8>() as u64,
                alignment_bytes: align_of::<u8>() as u32,
            },
            FieldLayout {
                name: "reserved".to_owned(),
                offset_bytes: offset_of!(ExpectedAYLraAffectedRowBatchStatusAbi, reserved) as u64,
                size_bytes: size_of::<[u8; 6]>() as u64,
                alignment_bytes: align_of::<[u8; 6]>() as u32,
            },
            FieldLayout {
                name: "rows_committed".to_owned(),
                offset_bytes: offset_of!(ExpectedAYLraAffectedRowBatchStatusAbi, rows_committed)
                    as u64,
                size_bytes: size_of::<i64>() as u64,
                alignment_bytes: align_of::<i64>() as u32,
            },
            FieldLayout {
                name: "first_failed_row".to_owned(),
                offset_bytes: offset_of!(ExpectedAYLraAffectedRowBatchStatusAbi, first_failed_row)
                    as u64,
                size_bytes: size_of::<i64>() as u64,
                alignment_bytes: align_of::<i64>() as u32,
            },
        ],
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

fn ay_lra_layout(symbol: &str) -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some("ay::lra::SparseSubstituteKernel::lp64:v1".to_owned());
    layout.records.push(ay_lra_status_record_layout());
    layout
        .symbols
        .push(trust_cg_codegen::jit_contract::SymbolLayout {
            name: symbol.to_owned(),
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

fn ay_lra_affected_row_batch_layout(symbol: &str) -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some("ay::lra::SparseAffectedRowBatchKernel::lp64:v1".to_owned());
    layout
        .records
        .push(ay_lra_affected_row_batch_status_record_layout());
    layout
        .symbols
        .push(trust_cg_codegen::jit_contract::SymbolLayout {
            name: symbol.to_owned(),
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
        "status_abi".to_owned(),
        "ay_lra_sparse_affected_row_batch_status_abi_v1".to_owned(),
    );
    layout.metadata.insert(
        "row_output_lengths".to_owned(),
        "exact_per_row_i64_lengths".to_owned(),
    );
    layout
        .metadata
        .insert("status_value".to_owned(), "rows_committed".to_owned());
    layout
        .metadata
        .insert("status_detail".to_owned(), "first_failed_row".to_owned());
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

fn ay_lra_manifest_for_symbol(symbol: &str) -> DeterministicArtifactManifest {
    let target = ay_lra_target();
    let abi = ay_lra_abi();
    let layout = ay_lra_layout(symbol);
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
        name: symbol.to_owned(),
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
    manifest.metadata.insert(
        "native_payload_sha256".to_owned(),
        STATUS_NATIVE_PAYLOAD_SHA256.to_owned(),
    );
    manifest.metadata.insert(
        "proof_report_sha256".to_owned(),
        STATUS_PROOF_REPORT_SHA256.to_owned(),
    );
    manifest
}

fn ay_lra_manifest() -> DeterministicArtifactManifest {
    ay_lra_manifest_for_symbol(STATUS_SYMBOL)
}

fn ay_lra_affected_row_batch_manifest() -> DeterministicArtifactManifest {
    let target = ay_lra_target();
    let abi = ay_lra_abi();
    let layout = ay_lra_affected_row_batch_layout(AFFECTED_ROW_BATCH_STATUS_SYMBOL);
    let proof_policy = ay_lra_proof_policy();
    let invalidation = ay_lra_invalidation(&target, &abi, &layout, &proof_policy);
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
        "lra_sparse_affected_row_batch".to_owned(),
    );
    manifest.metadata.insert(
        "row_output_lengths".to_owned(),
        "exact_per_row_i64_lengths".to_owned(),
    );
    manifest
        .metadata
        .insert("status_value".to_owned(), "rows_committed".to_owned());
    manifest
        .metadata
        .insert("status_detail".to_owned(), "first_failed_row".to_owned());
    manifest.metadata.insert(
        "native_payload_sha256".to_owned(),
        STATUS_NATIVE_PAYLOAD_SHA256.to_owned(),
    );
    manifest.metadata.insert(
        "proof_report_sha256".to_owned(),
        STATUS_PROOF_REPORT_SHA256.to_owned(),
    );
    manifest
}

fn ay_lra_verified_evidence(manifest: &DeterministicArtifactManifest) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::verified_for_artifact(
        "trust-cg-verify",
        manifest,
        STATUS_NATIVE_PAYLOAD_SHA256,
        STATUS_PROOF_REPORT_SHA256,
    );
    evidence
        .metadata
        .insert("kernel".to_owned(), "ay_lra_sparse_substitute".to_owned());
    evidence
        .metadata
        .insert("proof_family".to_owned(), "ay-lra-status-abi".to_owned());
    evidence
}

fn ay_lra_status_lookup_contract(
    manifest: &DeterministicArtifactManifest,
    symbol: &str,
) -> SymbolLookupContract {
    SymbolLookupContract::new(
        symbol,
        ay_lra_status_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
    .with_proof_evidence(ay_lra_verified_evidence(manifest))
}

fn ay_lra_affected_row_batch_status_lookup_contract(
    manifest: &DeterministicArtifactManifest,
) -> SymbolLookupContract {
    SymbolLookupContract::new(
        AFFECTED_ROW_BATCH_STATUS_SYMBOL,
        ay_lra_affected_row_batch_status_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
    .with_proof_evidence(ay_lra_verified_evidence(manifest))
}

fn build_status_probe_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("jit_ay_lra_status_abi");
    let func_ty_id = module.add_func_type(FuncTy {
        params: vec![
            Ty::I64, // planned sparse-substitute output length
            Ty::I64, // output capacity
            Ty::I64, // checked arithmetic lhs
            Ty::I64, // checked arithmetic rhs
            Ty::I64, // current basis epoch
            Ty::I64, // expected basis epoch
            Ty::Ptr, // ExpectedAYLraStatusAbi*
        ],
        returns: vec![],
        is_vararg: false,
    });

    let entry_id = b(0);
    let stale_id = b(1);
    let bounds_check_id = b(2);
    let bounds_id = b(3);
    let overflow_check_id = b(4);
    let overflow_id = b(5);
    let ok_id = b(6);

    let mut next_value = 0;
    let planned_len = v(next_value);
    next_value += 1;
    let capacity = v(next_value);
    next_value += 1;
    let lhs = v(next_value);
    next_value += 1;
    let rhs = v(next_value);
    next_value += 1;
    let basis_epoch = v(next_value);
    next_value += 1;
    let expected_epoch = v(next_value);
    next_value += 1;
    let out = v(next_value);
    next_value += 1;

    let mut entry = TrustIrBlock::new(entry_id)
        .with_param(planned_len, Ty::I64)
        .with_param(capacity, Ty::I64)
        .with_param(lhs, Ty::I64)
        .with_param(rhs, Ty::I64)
        .with_param(basis_epoch, Ty::I64)
        .with_param(expected_epoch, Ty::I64)
        .with_param(out, Ty::Ptr);
    let stale = push_result(
        &mut entry,
        &mut next_value,
        Inst::ICmp {
            op: ICmpOp::Ne,
            ty: Ty::I64,
            lhs: basis_epoch,
            rhs: expected_epoch,
        },
    );
    push_void(
        &mut entry,
        Inst::CondBr {
            cond: stale,
            then_target: stale_id,
            then_args: vec![],
            else_target: bounds_check_id,
            else_args: vec![],
        },
    );

    let mut stale_block = TrustIrBlock::new(stale_id);
    let zero_for_stale = iconst(&mut stale_block, &mut next_value, Ty::I64, 0);
    write_status_record(
        &mut stale_block,
        &mut next_value,
        out,
        ExpectedAYLraStatus::Stale,
        ExpectedAYLraDeopt::BasisEpochStale,
        zero_for_stale,
        basis_epoch,
    );
    return_void(&mut stale_block);

    let mut bounds_check = TrustIrBlock::new(bounds_check_id);
    let out_of_bounds = push_result(
        &mut bounds_check,
        &mut next_value,
        Inst::ICmp {
            op: ICmpOp::Ugt,
            ty: Ty::I64,
            lhs: planned_len,
            rhs: capacity,
        },
    );
    push_void(
        &mut bounds_check,
        Inst::CondBr {
            cond: out_of_bounds,
            then_target: bounds_id,
            then_args: vec![],
            else_target: overflow_check_id,
            else_args: vec![],
        },
    );

    let mut bounds_block = TrustIrBlock::new(bounds_id);
    let zero_for_bounds = iconst(&mut bounds_block, &mut next_value, Ty::I64, 0);
    write_status_record(
        &mut bounds_block,
        &mut next_value,
        out,
        ExpectedAYLraStatus::Bounds,
        ExpectedAYLraDeopt::SparseSubstituteBounds,
        zero_for_bounds,
        planned_len,
    );
    return_void(&mut bounds_block);

    let mut overflow_check = TrustIrBlock::new(overflow_check_id);
    let sum = v(next_value);
    next_value += 1;
    let overflow = v(next_value);
    next_value += 1;
    overflow_check.body.push(
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I64,
            lhs,
            rhs,
        })
        .with_result(sum)
        .with_result(overflow),
    );
    push_void(
        &mut overflow_check,
        Inst::CondBr {
            cond: overflow,
            then_target: overflow_id,
            then_args: vec![],
            else_target: ok_id,
            else_args: vec![sum],
        },
    );

    let mut overflow_block = TrustIrBlock::new(overflow_id);
    let zero_value_for_overflow = iconst(&mut overflow_block, &mut next_value, Ty::I64, 0);
    let zero_detail_for_overflow = iconst(&mut overflow_block, &mut next_value, Ty::I64, 0);
    write_status_record(
        &mut overflow_block,
        &mut next_value,
        out,
        ExpectedAYLraStatus::Overflow,
        ExpectedAYLraDeopt::SparseSubstituteOverflow,
        zero_value_for_overflow,
        zero_detail_for_overflow,
    );
    return_void(&mut overflow_block);

    let ok_sum = v(next_value);
    next_value += 1;
    let mut ok_block = TrustIrBlock::new(ok_id).with_param(ok_sum, Ty::I64);
    write_status_record(
        &mut ok_block,
        &mut next_value,
        out,
        ExpectedAYLraStatus::Ok,
        ExpectedAYLraDeopt::None,
        ok_sum,
        planned_len,
    );
    return_void(&mut ok_block);

    let mut func = TrustIrFunction::new(FuncId::new(0), STATUS_SYMBOL, func_ty_id, entry_id);
    func.blocks = vec![
        entry,
        stale_block,
        bounds_check,
        bounds_block,
        overflow_check,
        overflow_block,
        ok_block,
    ];
    module.add_function(func);
    module
}

fn build_affected_row_batch_status_probe_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("jit_ay_lra_affected_row_batch_status_abi");
    let func_ty_id = module.add_func_type(FuncTy {
        params: vec![
            Ty::I64, // affected rows in the batch
            Ty::I64, // per-row output capacity
            Ty::I64, // synthetic failure mode
            Ty::I64, // current basis epoch
            Ty::I64, // expected basis epoch
            Ty::Ptr, // i64 row-output lengths[AFFECTED_ROW_BATCH_ROWS]
            Ty::Ptr, // ExpectedAYLraAffectedRowBatchStatusAbi*
        ],
        returns: vec![],
        is_vararg: false,
    });

    let entry_id = b(0);
    let stale_id = b(1);
    let capacity_check_id = b(2);
    let capacity_bounds_id = b(3);
    let bounds_mode_check_id = b(4);
    let bounds_row_one_id = b(5);
    let overflow_mode_check_id = b(6);
    let overflow_row_two_id = b(7);
    let ok_id = b(8);

    let mut next_value = 0;
    let row_count = v(next_value);
    next_value += 1;
    let output_capacity = v(next_value);
    next_value += 1;
    let failure_mode = v(next_value);
    next_value += 1;
    let basis_epoch = v(next_value);
    next_value += 1;
    let expected_epoch = v(next_value);
    next_value += 1;
    let row_lengths = v(next_value);
    next_value += 1;
    let out = v(next_value);
    next_value += 1;

    let mut entry = TrustIrBlock::new(entry_id)
        .with_param(row_count, Ty::I64)
        .with_param(output_capacity, Ty::I64)
        .with_param(failure_mode, Ty::I64)
        .with_param(basis_epoch, Ty::I64)
        .with_param(expected_epoch, Ty::I64)
        .with_param(row_lengths, Ty::Ptr)
        .with_param(out, Ty::Ptr);
    let stale = push_result(
        &mut entry,
        &mut next_value,
        Inst::ICmp {
            op: ICmpOp::Ne,
            ty: Ty::I64,
            lhs: basis_epoch,
            rhs: expected_epoch,
        },
    );
    push_void(
        &mut entry,
        Inst::CondBr {
            cond: stale,
            then_target: stale_id,
            then_args: vec![],
            else_target: capacity_check_id,
            else_args: vec![],
        },
    );

    let mut stale_block = TrustIrBlock::new(stale_id);
    let zero_rows = iconst(&mut stale_block, &mut next_value, Ty::I64, 0);
    let first_row = iconst(&mut stale_block, &mut next_value, Ty::I64, 0);
    write_status_record(
        &mut stale_block,
        &mut next_value,
        out,
        ExpectedAYLraStatus::Stale,
        ExpectedAYLraDeopt::BasisEpochStale,
        zero_rows,
        first_row,
    );
    return_void(&mut stale_block);

    let mut capacity_check = TrustIrBlock::new(capacity_check_id);
    let required_row_len = iconst(&mut capacity_check, &mut next_value, Ty::I64, 3);
    let capacity_too_small = push_result(
        &mut capacity_check,
        &mut next_value,
        Inst::ICmp {
            op: ICmpOp::Ugt,
            ty: Ty::I64,
            lhs: required_row_len,
            rhs: output_capacity,
        },
    );
    push_void(
        &mut capacity_check,
        Inst::CondBr {
            cond: capacity_too_small,
            then_target: capacity_bounds_id,
            then_args: vec![],
            else_target: bounds_mode_check_id,
            else_args: vec![],
        },
    );

    let mut capacity_bounds = TrustIrBlock::new(capacity_bounds_id);
    let zero_rows = iconst(&mut capacity_bounds, &mut next_value, Ty::I64, 0);
    let first_row = iconst(&mut capacity_bounds, &mut next_value, Ty::I64, 0);
    write_status_record(
        &mut capacity_bounds,
        &mut next_value,
        out,
        ExpectedAYLraStatus::Bounds,
        ExpectedAYLraDeopt::SparseSubstituteBounds,
        zero_rows,
        first_row,
    );
    return_void(&mut capacity_bounds);

    let mut bounds_mode_check = TrustIrBlock::new(bounds_mode_check_id);
    let bounds_mode = iconst(&mut bounds_mode_check, &mut next_value, Ty::I64, 1);
    let is_bounds_mode = push_result(
        &mut bounds_mode_check,
        &mut next_value,
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::I64,
            lhs: failure_mode,
            rhs: bounds_mode,
        },
    );
    push_void(
        &mut bounds_mode_check,
        Inst::CondBr {
            cond: is_bounds_mode,
            then_target: bounds_row_one_id,
            then_args: vec![],
            else_target: overflow_mode_check_id,
            else_args: vec![],
        },
    );

    let mut bounds_row_one = TrustIrBlock::new(bounds_row_one_id);
    store_row_length_const(&mut bounds_row_one, &mut next_value, row_lengths, 0, 3);
    let committed_rows = iconst(&mut bounds_row_one, &mut next_value, Ty::I64, 1);
    let first_failed_row = iconst(&mut bounds_row_one, &mut next_value, Ty::I64, 1);
    write_status_record(
        &mut bounds_row_one,
        &mut next_value,
        out,
        ExpectedAYLraStatus::Bounds,
        ExpectedAYLraDeopt::SparseSubstituteBounds,
        committed_rows,
        first_failed_row,
    );
    return_void(&mut bounds_row_one);

    let mut overflow_mode_check = TrustIrBlock::new(overflow_mode_check_id);
    let overflow_mode = iconst(&mut overflow_mode_check, &mut next_value, Ty::I64, 2);
    let is_overflow_mode = push_result(
        &mut overflow_mode_check,
        &mut next_value,
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::I64,
            lhs: failure_mode,
            rhs: overflow_mode,
        },
    );
    push_void(
        &mut overflow_mode_check,
        Inst::CondBr {
            cond: is_overflow_mode,
            then_target: overflow_row_two_id,
            then_args: vec![],
            else_target: ok_id,
            else_args: vec![],
        },
    );

    let mut overflow_row_two = TrustIrBlock::new(overflow_row_two_id);
    store_row_length_const(&mut overflow_row_two, &mut next_value, row_lengths, 0, 3);
    store_row_length_const(&mut overflow_row_two, &mut next_value, row_lengths, 1, 2);
    let committed_rows = iconst(&mut overflow_row_two, &mut next_value, Ty::I64, 2);
    let first_failed_row = iconst(&mut overflow_row_two, &mut next_value, Ty::I64, 2);
    write_status_record(
        &mut overflow_row_two,
        &mut next_value,
        out,
        ExpectedAYLraStatus::Overflow,
        ExpectedAYLraDeopt::SparseSubstituteOverflow,
        committed_rows,
        first_failed_row,
    );
    return_void(&mut overflow_row_two);

    let mut ok_block = TrustIrBlock::new(ok_id);
    store_row_length_const(&mut ok_block, &mut next_value, row_lengths, 0, 3);
    store_row_length_const(&mut ok_block, &mut next_value, row_lengths, 1, 2);
    store_row_length_const(&mut ok_block, &mut next_value, row_lengths, 2, 1);
    let committed_rows = iconst(
        &mut ok_block,
        &mut next_value,
        Ty::I64,
        AFFECTED_ROW_BATCH_ROWS as i128,
    );
    let no_failed_row = iconst(
        &mut ok_block,
        &mut next_value,
        Ty::I64,
        AFFECTED_ROW_BATCH_ROWS as i128,
    );
    write_status_record(
        &mut ok_block,
        &mut next_value,
        out,
        ExpectedAYLraStatus::Ok,
        ExpectedAYLraDeopt::None,
        committed_rows,
        no_failed_row,
    );
    return_void(&mut ok_block);

    let mut func = TrustIrFunction::new(
        FuncId::new(0),
        AFFECTED_ROW_BATCH_STATUS_SYMBOL,
        func_ty_id,
        entry_id,
    );
    func.blocks = vec![
        entry,
        stale_block,
        capacity_check,
        capacity_bounds,
        bounds_mode_check,
        bounds_row_one,
        overflow_mode_check,
        overflow_row_two,
        ok_block,
    ];
    module.add_function(func);
    module
}

fn prepare_status_probe_machine() -> trust_cg_ir::MachFunction {
    let module = build_status_probe_module();
    let lowered = trust_cg_lower::translate_module(&module).expect("ay LRA status probe lowers");
    assert_eq!(lowered.len(), 1, "expected one lowered status probe");

    let pipeline_config = PipelineConfig {
        opt_level: OptLevel::O2,
        ..PipelineConfig::default()
    };
    let pipeline = Pipeline::new(pipeline_config);
    pipeline
        .prepare_function_with_proofs(&lowered[0].0, Some(&lowered[0].1))
        .expect("ay LRA status probe prepares")
}

fn prepare_affected_row_batch_status_probe_machine() -> trust_cg_ir::MachFunction {
    let module = build_affected_row_batch_status_probe_module();
    let lowered =
        trust_cg_lower::translate_module(&module).expect("ay LRA affected-row batch probe lowers");
    assert_eq!(
        lowered.len(),
        1,
        "expected one lowered affected-row batch probe"
    );

    let pipeline_config = PipelineConfig {
        opt_level: OptLevel::O2,
        ..PipelineConfig::default()
    };
    let pipeline = Pipeline::new(pipeline_config);
    pipeline
        .prepare_function_with_proofs(&lowered[0].0, Some(&lowered[0].1))
        .expect("ay LRA affected-row batch probe prepares")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct X6AddressOrigin {
    offset: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TrackedAddressValue {
    Origin(X6AddressOrigin),
    Constant(i64),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct X6AddressState {
    origins: HashMap<PReg, X6AddressOrigin>,
    constants: HashMap<PReg, i64>,
}

impl X6AddressState {
    fn seed() -> Self {
        let mut state = Self::default();
        state.set_origin(trust_cg_lower::gpr::X6, X6AddressOrigin { offset: 0 });
        state
    }

    fn clear_reg(&mut self, reg: PReg) {
        self.origins.remove(&reg);
        self.constants.remove(&reg);
    }

    fn set_origin(&mut self, reg: PReg, origin: X6AddressOrigin) {
        self.origins.insert(reg, origin);
        self.constants.remove(&reg);
    }

    fn set_constant(&mut self, reg: PReg, value: i64) {
        self.constants.insert(reg, value);
        self.origins.remove(&reg);
    }

    fn origin(&self, reg: PReg) -> Option<X6AddressOrigin> {
        self.origins.get(&reg).copied()
    }

    fn constant(&self, reg: PReg) -> Option<i64> {
        self.constants.get(&reg).copied()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StatusStoreHit {
    inst_id: u32,
    opcode: AArch64Opcode,
    base: PReg,
    origin: X6AddressOrigin,
}

fn preg_operand(op: Option<&MachOperand>) -> Option<PReg> {
    match op {
        Some(MachOperand::PReg(reg)) => Some(*reg),
        _ => None,
    }
}

fn imm_operand(op: Option<&MachOperand>) -> Option<i64> {
    match op {
        Some(MachOperand::Imm(value)) => Some(*value),
        _ => None,
    }
}

fn has_unresolved_store_operand(inst: &MachInst) -> bool {
    inst.operands.iter().any(|op| {
        matches!(
            op,
            MachOperand::VReg(_) | MachOperand::IncomingArg(_) | MachOperand::StackSlot(_)
        )
    })
}

fn forbidden_status_store_base_name(op: &MachOperand) -> Option<&'static str> {
    match op {
        MachOperand::PReg(reg) => forbidden_status_store_preg_name(*reg),
        MachOperand::Special(SpecialReg::SP) => Some("SP"),
        MachOperand::Special(SpecialReg::XZR) => Some("XZR"),
        MachOperand::Special(SpecialReg::WZR) => Some("WZR"),
        _ => None,
    }
}

fn forbidden_status_store_preg_name(reg: PReg) -> Option<&'static str> {
    if reg == SP {
        Some("SP")
    } else if reg == FP {
        Some("FP")
    } else if reg == XZR {
        Some("XZR")
    } else if reg == WZR {
        Some("WZR")
    } else {
        None
    }
}

fn is_target_status_offset(offset: i64) -> bool {
    matches!(offset, 0 | 1 | 8 | 16)
}

fn add_origin_offset(origin: X6AddressOrigin, offset: i64) -> X6AddressOrigin {
    X6AddressOrigin {
        offset: origin.offset + offset,
    }
}

fn update_x6_address_state(state: &mut X6AddressState, inst: &MachInst) {
    let computed = match inst.opcode {
        AArch64Opcode::Copy | AArch64Opcode::MovR => {
            let dst = preg_operand(inst.operands.first());
            let src = preg_operand(inst.operands.get(1));
            dst.map(|dst| {
                let value = src.and_then(|src| {
                    state
                        .origin(src)
                        .map(TrackedAddressValue::Origin)
                        .or_else(|| state.constant(src).map(TrackedAddressValue::Constant))
                });
                (dst, value)
            })
        }
        AArch64Opcode::MovI | AArch64Opcode::Movz => {
            let dst = preg_operand(inst.operands.first());
            let imm = imm_operand(inst.operands.get(1));
            dst.map(|dst| (dst, imm.map(TrackedAddressValue::Constant)))
        }
        AArch64Opcode::AddRI => {
            let dst = preg_operand(inst.operands.first());
            let src = preg_operand(inst.operands.get(1));
            let imm = imm_operand(inst.operands.get(2));
            dst.map(|dst| {
                let value = src.and_then(|src| {
                    imm.and_then(|imm| {
                        if let Some(origin) = state.origin(src) {
                            Some(TrackedAddressValue::Origin(add_origin_offset(origin, imm)))
                        } else {
                            state
                                .constant(src)
                                .map(|constant| TrackedAddressValue::Constant(constant + imm))
                        }
                    })
                });
                (dst, value)
            })
        }
        AArch64Opcode::SubRI => {
            let dst = preg_operand(inst.operands.first());
            let src = preg_operand(inst.operands.get(1));
            let imm = imm_operand(inst.operands.get(2));
            dst.map(|dst| {
                let value = src.and_then(|src| {
                    imm.and_then(|imm| {
                        if let Some(origin) = state.origin(src) {
                            Some(TrackedAddressValue::Origin(add_origin_offset(origin, -imm)))
                        } else {
                            state
                                .constant(src)
                                .map(|constant| TrackedAddressValue::Constant(constant - imm))
                        }
                    })
                });
                (dst, value)
            })
        }
        AArch64Opcode::AddRR => {
            let dst = preg_operand(inst.operands.first());
            let lhs = preg_operand(inst.operands.get(1));
            let rhs = preg_operand(inst.operands.get(2));
            dst.map(|dst| {
                let value = lhs.zip(rhs).and_then(|(lhs, rhs)| {
                    if let (Some(origin), Some(constant)) = (state.origin(lhs), state.constant(rhs))
                    {
                        Some(TrackedAddressValue::Origin(add_origin_offset(
                            origin, constant,
                        )))
                    } else if let (Some(constant), Some(origin)) =
                        (state.constant(lhs), state.origin(rhs))
                    {
                        Some(TrackedAddressValue::Origin(add_origin_offset(
                            origin, constant,
                        )))
                    } else {
                        state
                            .constant(lhs)
                            .zip(state.constant(rhs))
                            .map(|(lhs, rhs)| TrackedAddressValue::Constant(lhs + rhs))
                    }
                });
                (dst, value)
            })
        }
        AArch64Opcode::SubRR => {
            let dst = preg_operand(inst.operands.first());
            let lhs = preg_operand(inst.operands.get(1));
            let rhs = preg_operand(inst.operands.get(2));
            dst.map(|dst| {
                let value = lhs.zip(rhs).and_then(|(lhs, rhs)| {
                    if let (Some(origin), Some(constant)) = (state.origin(lhs), state.constant(rhs))
                    {
                        Some(TrackedAddressValue::Origin(add_origin_offset(
                            origin, -constant,
                        )))
                    } else {
                        state
                            .constant(lhs)
                            .zip(state.constant(rhs))
                            .map(|(lhs, rhs)| TrackedAddressValue::Constant(lhs - rhs))
                    }
                });
                (dst, value)
            })
        }
        _ if inst.opcode.produces_value() => {
            preg_operand(inst.operands.first()).map(|dst| (dst, None))
        }
        _ => None,
    };

    if let Some((dst, value)) = computed {
        match value {
            Some(TrackedAddressValue::Origin(origin)) => state.set_origin(dst, origin),
            Some(TrackedAddressValue::Constant(value)) => state.set_constant(dst, value),
            None => state.clear_reg(dst),
        }
    }

    for reg in inst.implicit_defs {
        state.clear_reg(*reg);
    }
}

fn merge_x6_address_origins(into: &mut X6AddressState, incoming: &X6AddressState) -> bool {
    let before = into.clone();
    into.origins
        .retain(|reg, origin| incoming.origins.get(reg) == Some(origin));
    into.constants
        .retain(|reg, value| incoming.constants.get(reg) == Some(value));
    before != *into
}

fn x6_address_state_by_block(mach: &trust_cg_ir::MachFunction) -> Vec<Option<X6AddressState>> {
    let mut input_states = vec![None; mach.blocks.len()];
    input_states[mach.entry.0 as usize] = Some(X6AddressState::seed());

    let mut worklist = vec![mach.entry];
    while let Some(block_id) = worklist.pop() {
        let Some(mut state) = input_states[block_id.0 as usize].clone() else {
            continue;
        };
        let block = mach.block(block_id);
        for inst_id in &block.insts {
            update_x6_address_state(&mut state, mach.inst(*inst_id));
        }

        for succ in &block.succs {
            let slot = &mut input_states[succ.0 as usize];
            let changed = if let Some(existing) = slot {
                merge_x6_address_origins(existing, &state)
            } else {
                *slot = Some(state.clone());
                true
            };
            if changed {
                worklist.push(*succ);
            }
        }
    }

    input_states
}

fn collect_status_store_hits(mach: &trust_cg_ir::MachFunction) -> Vec<StatusStoreHit> {
    let input_states = x6_address_state_by_block(mach);
    let mut hits = Vec::new();

    for block_id in &mach.block_order {
        let mut state = input_states[block_id.0 as usize]
            .clone()
            .unwrap_or_default();
        let block = mach.block(*block_id);
        for inst_id in &block.insts {
            let inst = mach.inst(*inst_id);

            match inst.opcode {
                AArch64Opcode::VolatileStrRI
                | AArch64Opcode::VolatileStrbRI
                | AArch64Opcode::VolatileStrhRI => {
                    assert!(
                        !has_unresolved_store_operand(inst),
                        "status volatile store {inst_id:?} has unresolved operands: {inst:?}"
                    );
                    let base_operand = inst
                        .operands
                        .get(1)
                        .expect("status volatile store has address operand");
                    if let Some(name) = forbidden_status_store_base_name(base_operand) {
                        panic!(
                            "status volatile store {inst_id:?} uses forbidden base {name}: {inst:?}"
                        );
                    }
                    let Some(base) = preg_operand(Some(base_operand)) else {
                        panic!("status volatile store {inst_id:?} base is not a PReg: {inst:?}");
                    };
                    let Some(origin) = state.origin(base) else {
                        update_x6_address_state(&mut state, inst);
                        continue;
                    };
                    let immediate = imm_operand(inst.operands.get(2))
                        .expect("status volatile store has immediate offset");
                    let effective_offset = origin.offset + immediate;
                    assert!(
                        is_target_status_offset(effective_offset),
                        "status volatile store {inst_id:?} writes unexpected X6-relative offset \
                         {effective_offset}: {inst:?}"
                    );
                    match effective_offset {
                        0 | 1 => assert_eq!(
                            inst.opcode,
                            AArch64Opcode::VolatileStrbRI,
                            "byte status fields must use volatile STRB at {inst_id:?}"
                        ),
                        8 | 16 => assert_eq!(
                            inst.opcode,
                            AArch64Opcode::VolatileStrRI,
                            "i64 status fields must use volatile STR at {inst_id:?}"
                        ),
                        _ => unreachable!(),
                    }
                    hits.push(StatusStoreHit {
                        inst_id: inst_id.0,
                        opcode: inst.opcode,
                        base,
                        origin: X6AddressOrigin {
                            offset: effective_offset,
                        },
                    });
                }
                AArch64Opcode::Stlrb | AArch64Opcode::Stlr | AArch64Opcode::Stlrh => {
                    assert!(
                        !has_unresolved_store_operand(inst),
                        "status atomic store {inst_id:?} has unresolved operands: {inst:?}"
                    );
                    let base = inst
                        .operands
                        .get(1)
                        .expect("status atomic store has address operand");
                    if let Some(name) = forbidden_status_store_base_name(base) {
                        panic!(
                            "status atomic store {inst_id:?} uses forbidden base {name}: {inst:?}"
                        );
                    }
                    let Some(base) = preg_operand(Some(base)) else {
                        panic!("status atomic store {inst_id:?} base is not a PReg: {inst:?}");
                    };
                    let Some(origin) = state.origin(base) else {
                        panic!(
                            "status atomic store {inst_id:?} base {base:?} is not derived from X6: {inst:?}"
                        );
                    };
                    assert!(
                        is_target_status_offset(origin.offset),
                        "status atomic store {inst_id:?} writes unexpected X6-relative offset {}: {inst:?}",
                        origin.offset
                    );
                    match origin.offset {
                        0 | 1 => assert_eq!(
                            inst.opcode,
                            AArch64Opcode::Stlrb,
                            "byte status fields must use STLRB at {inst_id:?}"
                        ),
                        8 | 16 => assert_eq!(
                            inst.opcode,
                            AArch64Opcode::Stlr,
                            "i64 status fields must use STLR at {inst_id:?}"
                        ),
                        _ => unreachable!(),
                    }
                    hits.push(StatusStoreHit {
                        inst_id: inst_id.0,
                        opcode: inst.opcode,
                        base,
                        origin,
                    });
                }
                AArch64Opcode::StrRI
                | AArch64Opcode::StrbRI
                | AArch64Opcode::StrhRI
                | AArch64Opcode::STRWui
                | AArch64Opcode::STRXui => {
                    assert!(
                        !has_unresolved_store_operand(inst),
                        "prepared store {inst_id:?} has unresolved operands: {inst:?}"
                    );
                    if let (Some(base), Some(imm)) = (
                        preg_operand(inst.operands.get(1)),
                        imm_operand(inst.operands.get(2)),
                    ) && let Some(origin) = state.origin(base)
                    {
                        let effective_offset = origin.offset + imm;
                        assert!(
                            !is_target_status_offset(effective_offset),
                            "status store at X6-relative offset {effective_offset} used a normal STR opcode: {inst:?}"
                        );
                    }
                }
                _ => {}
            }

            update_x6_address_state(&mut state, inst);
        }
    }

    hits
}

fn compile_status_probe_buffer() -> trust_cg_codegen::ExecutableBuffer {
    let mach = prepare_status_probe_machine();

    let jit = JitCompiler::new(JitConfig {
        opt_level: OptLevel::O2,
        ..JitConfig::default()
    });
    jit.compile_raw(&[mach], &HashMap::new())
        .expect("ay LRA status probe JIT compiles")
}

fn compile_status_probe() -> (trust_cg_codegen::ExecutableBuffer, AYLraStatusProbeFn) {
    let buffer = compile_status_probe_buffer();
    let manifest = ay_lra_manifest();
    let contract = ay_lra_status_lookup_contract(&manifest, STATUS_SYMBOL);
    let f = unsafe {
        buffer
            .get_fixture_contract_symbol_bound::<AYLraStatusProbeFn>(&manifest, &contract)
            .expect("ay LRA status probe symbol satisfies artifact contract")
            .into_fn()
    };

    (buffer, f)
}

fn compile_affected_row_batch_status_probe_buffer() -> trust_cg_codegen::ExecutableBuffer {
    let mach = prepare_affected_row_batch_status_probe_machine();

    let jit = JitCompiler::new(JitConfig {
        opt_level: OptLevel::O2,
        ..JitConfig::default()
    });
    jit.compile_raw(&[mach], &HashMap::new())
        .expect("ay LRA affected-row batch status probe JIT compiles")
}

fn compile_affected_row_batch_status_probe() -> (
    trust_cg_codegen::ExecutableBuffer,
    AYLraAffectedRowBatchStatusProbeFn,
) {
    let buffer = compile_affected_row_batch_status_probe_buffer();
    let manifest = ay_lra_affected_row_batch_manifest();
    let contract = ay_lra_affected_row_batch_status_lookup_contract(&manifest);
    let f = unsafe {
        buffer
            .get_fixture_contract_symbol_bound::<AYLraAffectedRowBatchStatusProbeFn>(
                &manifest, &contract,
            )
            .expect("ay LRA affected-row batch status probe symbol satisfies artifact contract")
            .into_fn()
    };

    (buffer, f)
}

#[test]
fn ay_lra_status_abi_layout_is_ready_for_contract_type() {
    assert_eq!(size_of::<ExpectedAYLraStatusAbi>(), 24);
    assert_eq!(align_of::<ExpectedAYLraStatusAbi>(), 8);
    assert_eq!(offset_of!(ExpectedAYLraStatusAbi, status), 0);
    assert_eq!(offset_of!(ExpectedAYLraStatusAbi, deopt), 1);
    assert_eq!(offset_of!(ExpectedAYLraStatusAbi, value), 8);
    assert_eq!(offset_of!(ExpectedAYLraStatusAbi, detail), 16);
}

#[test]
fn ay_lra_sparse_affected_row_batch_status_abi_layout_is_ready_for_contract_type() {
    assert_eq!(size_of::<ExpectedAYLraAffectedRowBatchStatusAbi>(), 24);
    assert_eq!(align_of::<ExpectedAYLraAffectedRowBatchStatusAbi>(), 8);
    assert_eq!(
        offset_of!(ExpectedAYLraAffectedRowBatchStatusAbi, status),
        0
    );
    assert_eq!(offset_of!(ExpectedAYLraAffectedRowBatchStatusAbi, deopt), 1);
    assert_eq!(
        offset_of!(ExpectedAYLraAffectedRowBatchStatusAbi, rows_committed),
        8
    );
    assert_eq!(
        offset_of!(ExpectedAYLraAffectedRowBatchStatusAbi, first_failed_row),
        16
    );
}

#[test]
fn ay_lra_status_probe_o2_volatile_status_stores_are_resolved_from_x6() {
    let mach = prepare_status_probe_machine();
    let hits = collect_status_store_hits(&mach);
    assert_eq!(
        hits.len(),
        16,
        "expected four status records with four atomic field stores each, got {hits:?}"
    );

    let mut counts_by_offset = [0usize; 4];
    for hit in &hits {
        match hit.origin.offset {
            0 => counts_by_offset[0] += 1,
            1 => counts_by_offset[1] += 1,
            8 => counts_by_offset[2] += 1,
            16 => counts_by_offset[3] += 1,
            other => panic!("unexpected status store offset {other}: {hit:?}"),
        }
    }
    assert_eq!(
        counts_by_offset,
        [4, 4, 4, 4],
        "expected one store per status-record field on each exit path: {hits:?}"
    );
}

#[test]
fn ay_lra_status_probe_seventh_pointer_arg_is_x6_livein_and_lookup_only() {
    let module = build_status_probe_module();
    let lowered = trust_cg_lower::translate_module(&module).expect("ay LRA status probe lowers");
    assert_eq!(lowered.len(), 1, "expected one lowered status probe");
    let lir = &lowered[0].0;

    assert_eq!(lir.signature.params.len(), 7);
    assert_eq!(
        lir.signature.params[6],
        LowerType::I64,
        "the trust_ir status pointer lowers to a 64-bit integer-class formal"
    );

    let arg_locs = AppleAArch64ABI::classify_params(&lir.signature.params);
    assert_eq!(arg_locs.len(), 7);
    for (idx, loc) in arg_locs.iter().enumerate() {
        assert!(
            !matches!(loc, ArgLocation::Stack { .. }),
            "status probe arg {idx} must stay register-passed, got {loc:?}"
        );
    }
    assert_eq!(
        arg_locs[6],
        ArgLocation::Reg(trust_cg_lower::gpr::X6),
        "the status output pointer is the 7th integer-class formal and must enter in X6"
    );

    let entry = LowerBlock(0);
    let mut isel = InstructionSelector::new(
        "ay_lra_status_formal_liveins".to_owned(),
        lir.signature.clone(),
    );
    isel.lower_formal_arguments(&lir.signature, entry)
        .expect("formal arguments lower");
    let isel_func = isel.finalize();
    let entry_block = &isel_func.blocks[&entry];
    let seventh_copy = &entry_block.insts[6];
    assert_eq!(seventh_copy.opcode, AArch64Opcode::Copy);
    assert_eq!(
        seventh_copy.operands[1],
        ISelOperand::PReg(trust_cg_lower::gpr::X6),
        "ISel must copy the status output pointer from X6, not an incoming stack slot"
    );
    assert!(
        entry_block.insts.iter().all(|inst| !inst
            .operands
            .iter()
            .any(|op| matches!(op, ISelOperand::IncomingArg(_)))),
        "7-arg status probe should not use IncomingArg stack-addressing for its output pointer"
    );

    let mach = prepare_status_probe_machine();
    assert!(
        mach.insts.iter().all(|inst| !inst
            .operands
            .iter()
            .any(|op| matches!(op, MachOperand::IncomingArg(_)))),
        "prepared status probe must resolve all incoming-arg operands before lookup"
    );

    let buffer = compile_status_probe_buffer();
    let manifest = ay_lra_manifest();
    let contract = ay_lra_status_lookup_contract(&manifest, STATUS_SYMBOL);
    let typed = buffer
        .get_fixture_contract_symbol_bound::<AYLraStatusProbeFn>(&manifest, &contract)
        .expect("lookup-only status probe symbol satisfies artifact contract");
    assert_eq!(typed.symbol(), STATUS_SYMBOL);
    assert!(!typed.as_ptr().is_null());
}

#[test]
fn ay_lra_sparse_affected_row_batch_status_probe_resolves_status_from_x6() {
    let module = build_affected_row_batch_status_probe_module();
    let lowered =
        trust_cg_lower::translate_module(&module).expect("ay LRA affected-row batch probe lowers");
    assert_eq!(
        lowered.len(),
        1,
        "expected one lowered affected-row batch probe"
    );
    let lir = &lowered[0].0;

    assert_eq!(lir.signature.params.len(), 7);
    assert_eq!(
        lir.signature.params[5],
        LowerType::I64,
        "the row-output length pointer lowers to a 64-bit integer-class formal"
    );
    assert_eq!(
        lir.signature.params[6],
        LowerType::I64,
        "the batch status pointer lowers to a 64-bit integer-class formal"
    );

    let arg_locs = AppleAArch64ABI::classify_params(&lir.signature.params);
    assert_eq!(arg_locs.len(), 7);
    for (idx, loc) in arg_locs.iter().enumerate() {
        assert!(
            !matches!(loc, ArgLocation::Stack { .. }),
            "affected-row batch status probe arg {idx} must stay register-passed, got {loc:?}"
        );
    }
    assert_eq!(
        arg_locs[5],
        ArgLocation::Reg(trust_cg_lower::gpr::X5),
        "row-output lengths are the 6th integer-class formal and must enter in X5"
    );
    assert_eq!(
        arg_locs[6],
        ArgLocation::Reg(trust_cg_lower::gpr::X6),
        "batch status output pointer is the 7th integer-class formal and must enter in X6"
    );

    let entry = LowerBlock(0);
    let mut isel = InstructionSelector::new(
        "ay_lra_affected_row_batch_status_formal_liveins".to_owned(),
        lir.signature.clone(),
    );
    isel.lower_formal_arguments(&lir.signature, entry)
        .expect("formal arguments lower");
    let isel_func = isel.finalize();
    let entry_block = &isel_func.blocks[&entry];
    assert_eq!(
        entry_block.insts[5].operands[1],
        ISelOperand::PReg(trust_cg_lower::gpr::X5),
        "ISel must copy the row-output length pointer from X5"
    );
    assert_eq!(
        entry_block.insts[6].operands[1],
        ISelOperand::PReg(trust_cg_lower::gpr::X6),
        "ISel must copy the batch status output pointer from X6"
    );
    assert!(
        entry_block.insts.iter().all(|inst| !inst
            .operands
            .iter()
            .any(|op| matches!(op, ISelOperand::IncomingArg(_)))),
        "7-arg affected-row batch probe should not use IncomingArg stack-addressing"
    );

    let mach = prepare_affected_row_batch_status_probe_machine();
    assert!(
        mach.insts.iter().all(|inst| !inst
            .operands
            .iter()
            .any(|op| matches!(op, MachOperand::IncomingArg(_)))),
        "prepared affected-row batch probe must resolve all incoming-arg operands before lookup"
    );

    let hits = collect_status_store_hits(&mach);
    assert_eq!(
        hits.len(),
        20,
        "expected five typed batch status records with four atomic field stores each, got {hits:?}"
    );

    let mut counts_by_offset = [0usize; 4];
    for hit in &hits {
        match hit.origin.offset {
            0 => counts_by_offset[0] += 1,
            1 => counts_by_offset[1] += 1,
            8 => counts_by_offset[2] += 1,
            16 => counts_by_offset[3] += 1,
            other => panic!("unexpected batch status store offset {other}: {hit:?}"),
        }
    }
    assert_eq!(
        counts_by_offset,
        [5, 5, 5, 5],
        "expected one store per batch status-record field on each exit path: {hits:?}"
    );

    let buffer = compile_affected_row_batch_status_probe_buffer();
    let manifest = ay_lra_affected_row_batch_manifest();
    let contract = ay_lra_affected_row_batch_status_lookup_contract(&manifest);
    let typed = buffer
        .get_fixture_contract_symbol_bound::<AYLraAffectedRowBatchStatusProbeFn>(
            &manifest, &contract,
        )
        .expect("lookup-only affected-row batch status probe satisfies artifact contract");
    assert_eq!(typed.symbol(), AFFECTED_ROW_BATCH_STATUS_SYMBOL);
    assert!(!typed.as_ptr().is_null());
}

#[test]
fn ay_lra_sparse_substitute_status_abi_reports_typed_deopts() {
    let (_buffer, probe) = compile_status_probe();

    let mut out = ExpectedAYLraStatusAbi::poisoned();
    unsafe {
        probe(2, 4, 40, 2, 7, 7, &mut out);
    }
    out.assert_matches(ExpectedAYLraStatus::Ok, ExpectedAYLraDeopt::None, 42, 2);

    let mut out = ExpectedAYLraStatusAbi::poisoned();
    unsafe {
        probe(5, 4, 40, 2, 7, 7, &mut out);
    }
    out.assert_matches(
        ExpectedAYLraStatus::Bounds,
        ExpectedAYLraDeopt::SparseSubstituteBounds,
        0,
        5,
    );

    let mut out = ExpectedAYLraStatusAbi::poisoned();
    unsafe {
        probe(2, 4, i64::MAX, 1, 7, 7, &mut out);
    }
    out.assert_matches(
        ExpectedAYLraStatus::Overflow,
        ExpectedAYLraDeopt::SparseSubstituteOverflow,
        0,
        0,
    );

    let mut out = ExpectedAYLraStatusAbi::poisoned();
    unsafe {
        probe(5, 4, i64::MAX, 1, 9, 7, &mut out);
    }
    out.assert_matches(
        ExpectedAYLraStatus::Stale,
        ExpectedAYLraDeopt::BasisEpochStale,
        0,
        9,
    );
}

fn assert_committed_lengths_do_not_use_negative_sentinels(
    lengths: &[i64; AFFECTED_ROW_BATCH_ROWS],
    rows_committed: usize,
) {
    assert!(
        lengths[..rows_committed].iter().all(|length| *length >= 0),
        "committed affected-row output lengths must be exact nonnegative lengths, not negative sentinels: {lengths:?}"
    );
}

#[test]
fn ay_lra_sparse_affected_row_batch_status_abi_reports_exact_lengths_and_deopts() {
    let (_buffer, probe) = compile_affected_row_batch_status_probe();

    let mut out = ExpectedAYLraAffectedRowBatchStatusAbi::poisoned();
    let mut lengths = [-9; AFFECTED_ROW_BATCH_ROWS];
    unsafe {
        probe(
            AFFECTED_ROW_BATCH_ROWS as i64,
            3,
            0,
            7,
            7,
            lengths.as_mut_ptr(),
            &mut out,
        );
    }
    out.assert_matches(
        ExpectedAYLraStatus::Ok,
        ExpectedAYLraDeopt::None,
        AFFECTED_ROW_BATCH_ROWS as i64,
        AFFECTED_ROW_BATCH_ROWS as i64,
    );
    assert_eq!(lengths, [3, 2, 1]);
    assert_committed_lengths_do_not_use_negative_sentinels(&lengths, AFFECTED_ROW_BATCH_ROWS);

    let mut out = ExpectedAYLraAffectedRowBatchStatusAbi::poisoned();
    let mut lengths = [-9; AFFECTED_ROW_BATCH_ROWS];
    unsafe {
        probe(
            AFFECTED_ROW_BATCH_ROWS as i64,
            2,
            0,
            7,
            7,
            lengths.as_mut_ptr(),
            &mut out,
        );
    }
    out.assert_matches(
        ExpectedAYLraStatus::Bounds,
        ExpectedAYLraDeopt::SparseSubstituteBounds,
        0,
        0,
    );
    assert_eq!(
        lengths, [-9; AFFECTED_ROW_BATCH_ROWS],
        "capacity rejection must not publish row lengths before a typed reject"
    );

    let mut out = ExpectedAYLraAffectedRowBatchStatusAbi::poisoned();
    let mut lengths = [-9; AFFECTED_ROW_BATCH_ROWS];
    unsafe {
        probe(
            AFFECTED_ROW_BATCH_ROWS as i64,
            3,
            1,
            7,
            7,
            lengths.as_mut_ptr(),
            &mut out,
        );
    }
    out.assert_matches(
        ExpectedAYLraStatus::Bounds,
        ExpectedAYLraDeopt::SparseSubstituteBounds,
        1,
        1,
    );
    assert_eq!(lengths, [3, -9, -9]);
    assert_committed_lengths_do_not_use_negative_sentinels(&lengths, 1);

    let mut out = ExpectedAYLraAffectedRowBatchStatusAbi::poisoned();
    let mut lengths = [-9; AFFECTED_ROW_BATCH_ROWS];
    unsafe {
        probe(
            AFFECTED_ROW_BATCH_ROWS as i64,
            3,
            2,
            7,
            7,
            lengths.as_mut_ptr(),
            &mut out,
        );
    }
    out.assert_matches(
        ExpectedAYLraStatus::Overflow,
        ExpectedAYLraDeopt::SparseSubstituteOverflow,
        2,
        2,
    );
    assert_eq!(lengths, [3, 2, -9]);
    assert_committed_lengths_do_not_use_negative_sentinels(&lengths, 2);

    let mut out = ExpectedAYLraAffectedRowBatchStatusAbi::poisoned();
    let mut lengths = [-9; AFFECTED_ROW_BATCH_ROWS];
    unsafe {
        probe(
            AFFECTED_ROW_BATCH_ROWS as i64,
            3,
            0,
            8,
            7,
            lengths.as_mut_ptr(),
            &mut out,
        );
    }
    out.assert_matches(
        ExpectedAYLraStatus::Stale,
        ExpectedAYLraDeopt::BasisEpochStale,
        0,
        0,
    );
    assert_eq!(
        lengths, [-9; AFFECTED_ROW_BATCH_ROWS],
        "stale basis rejection must not publish row lengths before a typed reject"
    );
}

#[test]
fn ay_lra_status_contract_lookup_rejects_mismatches() {
    let (buffer, _probe) = compile_status_probe();
    let manifest = ay_lra_manifest();
    let contract = ay_lra_status_lookup_contract(&manifest, STATUS_SYMBOL);

    let mut wrong_signature = contract.clone();
    wrong_signature.signature = wrong_status_signature();
    let err = buffer
        .get_fixture_contract_symbol_bound::<AYLraStatusProbeFn>(&manifest, &wrong_signature)
        .expect_err("wrong status signature must reject contract symbol lookup");
    match err {
        ArtifactContractError::SignatureMismatch { symbol, .. } => {
            assert_eq!(symbol, STATUS_SYMBOL);
        }
        other => panic!("expected signature mismatch, got {other:?}"),
    }

    let mut wrong_layout = contract.clone();
    wrong_layout.layout_checksum = ay_lra_layout("wrong-layout-symbol").checksum();
    let err = buffer
        .get_fixture_contract_symbol_bound::<AYLraStatusProbeFn>(&manifest, &wrong_layout)
        .expect_err("wrong layout checksum must reject contract symbol lookup");
    match err {
        ArtifactContractError::ChecksumMismatch { component, .. } => {
            assert_eq!(component, "layout");
        }
        other => panic!("expected layout checksum mismatch, got {other:?}"),
    }

    let missing_symbol = "ay_lra_sparse_substitute_status_probe_missing";
    let missing_manifest = ay_lra_manifest_for_symbol(missing_symbol);
    let missing_contract = ay_lra_status_lookup_contract(&missing_manifest, missing_symbol);
    let err = buffer
        .get_fixture_contract_symbol_bound::<AYLraStatusProbeFn>(
            &missing_manifest,
            &missing_contract,
        )
        .expect_err("missing buffer symbol must surface through the contract path");
    match err {
        ArtifactContractError::NullSymbolPointer { symbol } => {
            assert_eq!(symbol, missing_symbol);
        }
        other => panic!("expected null symbol pointer, got {other:?}"),
    }
}
