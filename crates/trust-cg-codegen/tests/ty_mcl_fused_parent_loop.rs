// Regression for a TY MCL-shaped native fused parent loop.
//
// The loop carries parent-loop state through MCLamportMutex-like action guards,
// records generated parent indexes and fingerprints, and calls an indirect
// runtime callback from each enabled action.

#![cfg(target_arch = "aarch64")]

#[path = "common/fixture_contract.rs"]
mod fixture_contract;
use fixture_contract::FixtureContractLookup;

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};

use trust_cg_codegen::compile_service::{ArtifactInstallDisposition, ArtifactManifestReference};
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, ArtifactContractError, ArtifactManifestV1, ArtifactSection, ArtifactSectionKind,
    ArtifactSymbol, InvalidationKey, JitArtifactKind, LayoutManifest, ProofEvidenceRejectionCode,
    ProofEvidenceSummary, ProofEvidenceVerdict, ProofMode, ProofPolicy, SymbolVisibility,
    TargetDescriptor,
};
use trust_cg_codegen::jit_install_gate::{
    NATIVE_INSTALL_GATE_PRODUCT_PROMOTION_PACKET_SCHEMA,
    NATIVE_INSTALL_GATE_PRODUCT_PROMOTION_PACKET_SCHEMA_VERSION, NativeInstallGateDenyControlPlane,
    NativeInstallGateDenyReason, NativeInstallGateDenyScope, NativeInstallGatePacket,
    NativeInstallGateProductPromotionPacket, NativeInstallGateProductPromotionRejectionReason,
    TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY, TY_NATIVE_FUSED_EVIDENCE_GATE_RESULT_KEY,
    TY_NATIVE_FUSED_EVIDENCE_REPLAY_ROOT_KEY, TY_NATIVE_FUSED_EVIDENCE_TELEMETRY_EVENT_KEY,
    TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE, TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY,
    native_install_gate_non_promoting_product_promotion_packet as native_install_gate_non_promoting_product_promotion_packet_impl,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::ty_reducer_evidence::TyReducerEvidenceCoverageSummary;
use trust_cg_codegen::{
    CompileGeneration, CompileProfile, CompileRequest, CompileService, CompileStatus, Compiler,
    CompilerConfig, DispatchVerifyMode, ExecutableBuffer, InstallIntent, InstalledArtifact,
    JitConfig, NATIVE_INSTALL_GATE_REPLAY_SCHEMA, NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
    NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA, NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
    NativeInstallGateAuthority, NativeInstallGateConsumerAdmissionEvidence,
    NativeInstallGateDisposition, NativeInstallGateExpectedBindings, NativeInstallGateInput,
    NativeInstallGateLayoutEvidence, NativeInstallGatePayloadIdentity,
    NativeInstallGateProofEvidence, NativeInstallGateRejectionCode,
    NativeInstallGateReplayIdentity, NativeInstallGateRevalidationInput, NativeInstallGateSurface,
    NativeInstallGateTelemetryInput, ProfileHookMode, ProofOptimizationCertificateCitation,
    ProofOptimizationConsumedFactCitation, SourceKind, Target, TyReducerEvidencePacket,
    TyReducerEvidenceRow, TyReducerEvidenceStatus, native_install_gate_consumer_admission,
    native_install_gate_consumer_allowlist_key, validate_native_install_gate,
};
use trust_ir::{BinOp, FuncAttrs, FuncTyId, ICmpOp, ParamAttrs, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

#[path = "common/ty_contract.rs"]
mod ty_contract;

use ty_contract::{
    TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA, TY_NATIVE_FUSED_PARENT_LOOP_STATUS_ABI,
    TY_NATIVE_FUSED_PARENT_LOOP_WRAPPER_IDENTITY, TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS,
    TyNativeFusedEvidenceRefs, TyNativeFusedManifestIdentity, abi_i64, abi_ptr,
    assert_ty_native_fused_required_proof_fact_bridge, bind_ty_reducer_entry, extern_c_signature,
    ty_native_fused_missing_fact_evidence, ty_native_fused_parent_loop_manifest,
    ty_native_fused_parent_loop_manifest_for_symbol_with_proof_policy,
    ty_native_fused_verified_evidence, ty_reducer_lookup_contract,
    ty_reducer_manifest_with_proof_policy,
};

const ENTRY_NAME: &str = "ty_mcl_fused_parent_loop";
const SUMMARY_SLOTS: usize = 7;

type RuntimeCallbackFn =
    extern "C" fn(*mut RuntimeStatus, *mut u64, u64, u64, u32, u64, u64) -> u64;
type EntryFn = extern "C" fn(
    RuntimeCallbackFn,
    *const u64,
    *const u64,
    u64,
    *mut u64,
    *mut u64,
    *mut u64,
    *mut u64,
) -> u64;

const STATUS_OK: u8 = 0;
const STATUS_RUNTIME_ERROR: u8 = 9;
const CALLOUT_ENABLED: u64 = 1;

const FINGERPRINT_SEED: u64 = 0x1234_5678_9abc_def0;
const PARENT_DIGEST_SEED: u64 = 0x0715_2026_6620_0001;
const CALLBACK_DIGEST_SEED: u64 = 0xfeed_face_cafe_6620;

const TCG_ACTION_STRIDE: u64 = 0x1_0000_0001;
const IDX_PRIME: u64 = 0x9e37_79b1;
const PARENT_MIX: u64 = 0x1000_01b3;
const FINGERPRINT_PRIME: u64 = 0x0000_0100_0000_01b3;
const RUNTIME_PRIME: u64 = 0x0000_0001_0000_01b3;
const PARENT_INDEX_PRIME: u64 = 0x0000_0000_85eb_ca6b;
const PARENT_DIGEST_PRIME: u64 = 0x0000_0000_c2b2_ae35;
const FINGERPRINT_DIGEST_PRIME: u64 = 0x0000_0001_65b1_e9dd;
const CALLBACK_DIGEST_PRIME: u64 = 0x0000_0000_27d4_eb2f;

fn native_fused_reducer_evidence_summary() -> TyReducerEvidenceCoverageSummary {
    TyReducerEvidencePacket::phase4_local([
        native_fused_reducer_evidence_row("minimal_parent_loop"),
        native_fused_reducer_evidence_row("no_action_body_parent_loop"),
        native_fused_reducer_evidence_row("mcl_shaped_native_fused_parent_loop"),
        native_fused_reducer_evidence_row("callback_abi_call_clobber"),
        native_fused_reducer_evidence_row("edge_copy_block_arg"),
        native_fused_reducer_evidence_row("o3_materialized_helper_return"),
    ])
    .coverage_summary()
    .expect("test packet covers required reducer families")
}

fn native_fused_reducer_evidence_row(reducer_family: &str) -> TyReducerEvidenceRow {
    TyReducerEvidenceRow {
        command: format!("cargo test -p trust-cg-codegen --test {reducer_family}"),
        target_tuple: "aarch64-apple-darwin".to_owned(),
        trust_cg_revision: "trust-cg-test-revision".to_owned(),
        opt_level: "O1/O3".to_owned(),
        reducer_family: reducer_family.to_owned(),
        case_name: "green_local_reducer_evidence".to_owned(),
        parent_digest: format!("trust-cg-stable128:{reducer_family}:parent"),
        state_count: 1,
        generated_count: 1,
        fingerprint_digest: Some(format!("trust-cg-stable128:{reducer_family}:fingerprint")),
        callback_observations: vec![],
        status: TyReducerEvidenceStatus::GreenReducerEvidence,
        issue_refs: vec!["#667".to_owned()],
    }
}

fn bind_native_fused_reducer_evidence(
    manifest: &mut ArtifactManifestV1,
    summary: &TyReducerEvidenceCoverageSummary,
) {
    for (key, value) in summary.metadata_bindings() {
        manifest.metadata.insert(key, value);
    }
}

fn native_install_gate_non_promoting_product_promotion_packet<'a>(
    manifest: &ArtifactManifestV1,
    packet: &NativeInstallGatePacket,
    citation: impl Into<Option<&'a ProofOptimizationCertificateCitation>>,
) -> Result<NativeInstallGateProductPromotionPacket, NativeInstallGateProductPromotionRejectionReason>
{
    let reducer_summary = native_fused_reducer_evidence_summary();
    native_install_gate_non_promoting_product_promotion_packet_impl(
        manifest,
        packet,
        citation,
        &reducer_summary,
    )
}
const CALLBACK_RUNTIME_MUL: u64 = 0x0000_0000_94d0_49bb;

const FLAG0_MASK: u64 = 0x01;
const FLAG1_MASK: u64 = 0x02;
const TURN1_MASK: u64 = 0x04;
const PC0_WAITING_MASK: u64 = 0x08;
const PC1_WAITING_MASK: u64 = 0x10;

static CALLBACK_CALLS: AtomicUsize = AtomicUsize::new(0);
static CALLBACK_LAST_PARENT: AtomicU64 = AtomicU64::new(0);
static CALLBACK_LAST_IDX: AtomicU64 = AtomicU64::new(0);
static CALLBACK_LAST_ACTION: AtomicU32 = AtomicU32::new(0);
static CALLBACK_LAST_STATE: AtomicU64 = AtomicU64::new(0);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RuntimeStatus {
    status: u8,
    _pad: [u8; 7],
    value: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CallbackObservation {
    parent: u64,
    idx: u64,
    action: u32,
    state: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MclRun {
    summary: [u64; SUMMARY_SLOTS],
    parent_indexes: Vec<u64>,
    fingerprints: Vec<u64>,
    runtime_values: Vec<u64>,
    calls: usize,
    last_callback: Option<CallbackObservation>,
}

#[derive(Clone, Copy)]
struct ActionInputs {
    callback_ptr: ValueId,
    callback_ty: FuncTyId,
    callout: ValueId,
    parent_out: ValueId,
    fingerprints_out: ValueId,
    runtime_slots: ValueId,
    parent: ValueId,
    idx: ValueId,
    state: ValueId,
    generated: ValueId,
    fingerprint: ValueId,
    status: ValueId,
    parent_digest: ValueId,
    callback_digest: ValueId,
}

#[derive(Clone, Copy)]
struct ActionOutputs {
    generated: ValueId,
    last_parent: ValueId,
    fingerprint: ValueId,
    status: ValueId,
    parent_digest: ValueId,
    callback_digest: ValueId,
}

fn store_summary_slot(fb: &mut FunctionBuilder<'_>, summary: ValueId, slot: u64, value: ValueId) {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, summary, vec![slot]);
    fb.store(Ty::U64, ptr, value);
}

fn runtime_callback_value(parent: u64, idx: u64, action: u32, state: u64, candidate: u64) -> u64 {
    candidate
        .wrapping_mul(CALLBACK_RUNTIME_MUL)
        .wrapping_add(parent.rotate_left(7))
        .wrapping_add(idx.wrapping_mul(37))
        .wrapping_add(u64::from(action).wrapping_mul(0x101))
        .wrapping_add(state & 0xff)
}

extern "C" fn host_mcl_runtime_callback(
    callout: *mut RuntimeStatus,
    runtime_slot: *mut u64,
    parent: u64,
    idx: u64,
    action: u32,
    state: u64,
    candidate: u64,
) -> u64 {
    let runtime_value = runtime_callback_value(parent, idx, action, state, candidate);

    CALLBACK_CALLS.fetch_add(1, Ordering::SeqCst);
    CALLBACK_LAST_PARENT.store(parent, Ordering::SeqCst);
    CALLBACK_LAST_IDX.store(idx, Ordering::SeqCst);
    CALLBACK_LAST_ACTION.store(action, Ordering::SeqCst);
    CALLBACK_LAST_STATE.store(state, Ordering::SeqCst);

    unsafe {
        core::arch::asm!(
            "mov x0, #1",
            "mov x1, #2",
            "mov x2, #3",
            "mov x3, #4",
            "mov x4, #5",
            "mov x5, #6",
            "mov x6, #7",
            "mov x7, #8",
            "mov x8, #9",
            "mov x9, #10",
            "mov x10, #11",
            "mov x11, #12",
            "mov x12, #13",
            "mov x13, #14",
            "mov x14, #15",
            "mov x15, #16",
            "mov x16, #17",
            "mov x17, #18",
            out("x0") _,
            out("x1") _,
            out("x2") _,
            out("x3") _,
            out("x4") _,
            out("x5") _,
            out("x6") _,
            out("x7") _,
            out("x8") _,
            out("x9") _,
            out("x10") _,
            out("x11") _,
            out("x12") _,
            out("x13") _,
            out("x14") _,
            out("x15") _,
            out("x16") _,
            out("x17") _,
            options(nostack)
        );

        if !runtime_slot.is_null() {
            *runtime_slot = runtime_value;
        }
        if !callout.is_null() {
            (*callout).status = STATUS_OK;
            (*callout).value = CALLOUT_ENABLED;
        }
    }

    runtime_value
}

fn emit_action(fb: &mut FunctionBuilder<'_>, action: u32, input: ActionInputs) -> ActionOutputs {
    let action_u64 = fb.iconst(Ty::U64, i128::from(action));
    let action_u32 = fb.iconst(Ty::U32, i128::from(action));
    let action_stride = fb.iconst(Ty::U64, i128::from(TCG_ACTION_STRIDE));
    let action_term = fb.binop(BinOp::Mul, Ty::U64, action_u64, action_stride);
    let idx_prime = fb.iconst(Ty::U64, i128::from(IDX_PRIME));
    let idx_term = fb.binop(BinOp::Mul, Ty::U64, input.idx, idx_prime);
    let parent_mix = fb.iconst(Ty::U64, i128::from(PARENT_MIX));
    let parent_term = fb.binop(BinOp::Mul, Ty::U64, input.parent, parent_mix);
    let state_action = fb.binop(BinOp::Xor, Ty::U64, input.state, action_term);
    let base = fb.binop(BinOp::Xor, Ty::U64, input.fingerprint, state_action);
    let with_parent = fb.binop(BinOp::Add, Ty::U64, base, parent_term);
    let with_idx = fb.binop(BinOp::Add, Ty::U64, with_parent, idx_term);
    let fp_prime = fb.iconst(Ty::U64, i128::from(FINGERPRINT_PRIME));
    let scaled = fb.binop(BinOp::Mul, Ty::U64, with_idx, fp_prime);
    let candidate = fb.binop(BinOp::Add, Ty::U64, scaled, action_term);

    let busy = fb.iconst(Ty::U8, i128::from(STATUS_RUNTIME_ERROR));
    fb.store(Ty::U8, input.callout, busy);
    let one_slot = fb.iconst(Ty::U64, 1);
    let callout_value_ptr = fb.gep(Ty::U64, input.callout, vec![one_slot]);
    let zero = fb.iconst(Ty::U64, 0);
    fb.store(Ty::U64, callout_value_ptr, zero);

    let runtime_slot = fb.gep(Ty::U64, input.runtime_slots, vec![input.generated]);
    let returned = fb.call_indirect(
        input.callback_ptr,
        input.callback_ty,
        vec![
            input.callout,
            runtime_slot,
            input.parent,
            input.idx,
            action_u32,
            input.state,
            candidate,
        ],
    );

    let callback_status = fb.load(Ty::U8, input.callout);
    let callback_status = fb.zext(Ty::U8, Ty::U64, callback_status);
    let enabled = fb.load(Ty::U64, callout_value_ptr);
    let runtime_written = fb.load(Ty::U64, runtime_slot);

    let returned_xor_written = fb.binop(BinOp::Xor, Ty::U64, returned, runtime_written);
    let one = fb.iconst(Ty::U64, 1);
    let enabled_delta = fb.binop(BinOp::Sub, Ty::U64, enabled, one);
    let with_status = fb.binop(BinOp::Add, Ty::U64, input.status, callback_status);
    let with_runtime_check = fb.binop(BinOp::Add, Ty::U64, with_status, returned_xor_written);
    let next_status = fb.binop(BinOp::Add, Ty::U64, with_runtime_check, enabled_delta);

    let runtime_prime = fb.iconst(Ty::U64, i128::from(RUNTIME_PRIME));
    let fp_runtime = fb.binop(BinOp::Xor, Ty::U64, candidate, returned);
    let fp_scaled = fb.binop(BinOp::Mul, Ty::U64, fp_runtime, runtime_prime);
    let generated_fingerprint = fb.binop(BinOp::Add, Ty::U64, fp_scaled, enabled);
    let fingerprint_slot = fb.gep(Ty::U64, input.fingerprints_out, vec![input.generated]);
    fb.store(Ty::U64, fingerprint_slot, generated_fingerprint);
    let parent_slot = fb.gep(Ty::U64, input.parent_out, vec![input.generated]);
    fb.store(Ty::U64, parent_slot, input.idx);

    let next_generated = fb.binop(BinOp::Add, Ty::U64, input.generated, enabled);

    let parent_index_prime = fb.iconst(Ty::U64, i128::from(PARENT_INDEX_PRIME));
    let parent_index = fb.binop(BinOp::Mul, Ty::U64, input.idx, parent_index_prime);
    let parent_mix = fb.binop(BinOp::Xor, Ty::U64, input.parent, parent_index);
    let parent_mix = fb.binop(BinOp::Xor, Ty::U64, parent_mix, action_term);
    let parent_xor = fb.binop(BinOp::Xor, Ty::U64, input.parent_digest, parent_mix);
    let parent_digest_prime = fb.iconst(Ty::U64, i128::from(PARENT_DIGEST_PRIME));
    let parent_scaled = fb.binop(BinOp::Mul, Ty::U64, parent_xor, parent_digest_prime);
    let next_parent_digest = fb.binop(BinOp::Add, Ty::U64, parent_scaled, next_generated);

    let fp_xor = fb.binop(
        BinOp::Xor,
        Ty::U64,
        input.fingerprint,
        generated_fingerprint,
    );
    let fp_digest_prime = fb.iconst(Ty::U64, i128::from(FINGERPRINT_DIGEST_PRIME));
    let fp_digest_scaled = fb.binop(BinOp::Mul, Ty::U64, fp_xor, fp_digest_prime);
    let fp_with_generated = fb.binop(BinOp::Add, Ty::U64, fp_digest_scaled, next_generated);
    let next_fingerprint = fb.binop(BinOp::Add, Ty::U64, fp_with_generated, action_u64);

    let runtime_xor_candidate = fb.binop(BinOp::Xor, Ty::U64, runtime_written, candidate);
    let callback_mix = fb.binop(BinOp::Add, Ty::U64, returned, runtime_xor_candidate);
    let callback_mix = fb.binop(BinOp::Add, Ty::U64, callback_mix, action_term);
    let callback_xor = fb.binop(BinOp::Xor, Ty::U64, input.callback_digest, callback_mix);
    let callback_prime = fb.iconst(Ty::U64, i128::from(CALLBACK_DIGEST_PRIME));
    let callback_scaled = fb.binop(BinOp::Mul, Ty::U64, callback_xor, callback_prime);
    let next_callback_digest = fb.binop(BinOp::Add, Ty::U64, callback_scaled, input.parent);

    ActionOutputs {
        generated: next_generated,
        last_parent: input.idx,
        fingerprint: next_fingerprint,
        status: next_status,
        parent_digest: next_parent_digest,
        callback_digest: next_callback_digest,
    }
}

fn build_mcl_fused_parent_loop_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("ty_mcl_fused_parent_loop");
    let callback_ty = mb.add_func_type(
        vec![
            Ty::Ptr,
            Ty::Ptr,
            Ty::U64,
            Ty::U64,
            Ty::U32,
            Ty::U64,
            Ty::U64,
        ],
        vec![Ty::U64],
    );
    let entry_ty = mb.add_func_type(
        vec![
            Ty::Func(callback_ty),
            Ty::Ptr,
            Ty::Ptr,
            Ty::U64,
            Ty::Ptr,
            Ty::Ptr,
            Ty::Ptr,
            Ty::Ptr,
        ],
        vec![Ty::U64],
    );

    {
        let mut fb = mb.function(ENTRY_NAME, entry_ty);
        fb.set_attrs(FuncAttrs {
            params: vec![
                ParamAttrs::default(),
                ParamAttrs {
                    nonnull: true,
                    ..Default::default()
                },
                ParamAttrs {
                    nonnull: true,
                    ..Default::default()
                },
                ParamAttrs::default(),
                ParamAttrs {
                    nonnull: true,
                    ..Default::default()
                },
                ParamAttrs {
                    nonnull: true,
                    ..Default::default()
                },
                ParamAttrs {
                    nonnull: true,
                    ..Default::default()
                },
                ParamAttrs {
                    nonnull: true,
                    ..Default::default()
                },
            ],
            ..Default::default()
        });

        let entry = fb.create_block();
        let callback_ptr = fb.add_block_param(entry, Ty::Func(callback_ty));
        let parents = fb.add_block_param(entry, Ty::Ptr);
        let states = fb.add_block_param(entry, Ty::Ptr);
        let parent_count = fb.add_block_param(entry, Ty::U64);
        let parent_out = fb.add_block_param(entry, Ty::Ptr);
        let fingerprints_out = fb.add_block_param(entry, Ty::Ptr);
        let runtime_slots = fb.add_block_param(entry, Ty::Ptr);
        let summary = fb.add_block_param(entry, Ty::Ptr);

        let header = fb.create_block();
        let idx = fb.add_block_param(header, Ty::U64);
        let state_count = fb.add_block_param(header, Ty::U64);
        let generated = fb.add_block_param(header, Ty::U64);
        let last_parent = fb.add_block_param(header, Ty::U64);
        let fingerprint = fb.add_block_param(header, Ty::U64);
        let status = fb.add_block_param(header, Ty::U64);
        let parent_digest = fb.add_block_param(header, Ty::U64);
        let callback_digest = fb.add_block_param(header, Ty::U64);

        let body = fb.create_block();
        let p0_flag_check = fb.create_block();
        let p0_turn_check = fb.create_block();
        let p0_emit = fb.create_block();

        let after_p0 = fb.create_block();
        let p0_generated = fb.add_block_param(after_p0, Ty::U64);
        let p0_last_parent = fb.add_block_param(after_p0, Ty::U64);
        let p0_fingerprint = fb.add_block_param(after_p0, Ty::U64);
        let p0_status = fb.add_block_param(after_p0, Ty::U64);
        let p0_parent_digest = fb.add_block_param(after_p0, Ty::U64);
        let p0_callback_digest = fb.add_block_param(after_p0, Ty::U64);

        let p1_flag_check = fb.create_block();
        let p1_turn_check = fb.create_block();
        let p1_emit = fb.create_block();

        let after_p1 = fb.create_block();
        let p1_generated = fb.add_block_param(after_p1, Ty::U64);
        let p1_last_parent = fb.add_block_param(after_p1, Ty::U64);
        let p1_fingerprint = fb.add_block_param(after_p1, Ty::U64);
        let p1_status = fb.add_block_param(after_p1, Ty::U64);
        let p1_parent_digest = fb.add_block_param(after_p1, Ty::U64);
        let p1_callback_digest = fb.add_block_param(after_p1, Ty::U64);

        let done = fb.create_block();
        let done_state_count = fb.add_block_param(done, Ty::U64);
        let done_generated = fb.add_block_param(done, Ty::U64);
        let done_last_parent = fb.add_block_param(done, Ty::U64);
        let done_fingerprint = fb.add_block_param(done, Ty::U64);
        let done_status = fb.add_block_param(done, Ty::U64);
        let done_parent_digest = fb.add_block_param(done, Ty::U64);
        let done_callback_digest = fb.add_block_param(done, Ty::U64);

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        let fingerprint_seed = fb.iconst(Ty::U64, i128::from(FINGERPRINT_SEED));
        let parent_digest_seed = fb.iconst(Ty::U64, i128::from(PARENT_DIGEST_SEED));
        let callback_digest_seed = fb.iconst(Ty::U64, i128::from(CALLBACK_DIGEST_SEED));
        fb.br(
            header,
            vec![
                zero,
                zero,
                zero,
                zero,
                fingerprint_seed,
                zero,
                parent_digest_seed,
                callback_digest_seed,
            ],
        );

        fb.switch_to_block(header);
        let has_parent = fb.icmp(ICmpOp::Ult, Ty::U64, idx, parent_count);
        fb.condbr(
            has_parent,
            body,
            vec![],
            done,
            vec![
                state_count,
                generated,
                last_parent,
                fingerprint,
                status,
                parent_digest,
                callback_digest,
            ],
        );

        fb.switch_to_block(body);
        let parent_ptr = fb.gep(Ty::U64, parents, vec![idx]);
        let parent = fb.load(Ty::U64, parent_ptr);
        let state_ptr = fb.gep(Ty::U64, states, vec![idx]);
        let state = fb.load(Ty::U64, state_ptr);
        let zero_cmp = fb.iconst(Ty::U64, 0);
        let flag0_mask = fb.iconst(Ty::U64, i128::from(FLAG0_MASK));
        let flag1_mask = fb.iconst(Ty::U64, i128::from(FLAG1_MASK));
        let turn1_mask = fb.iconst(Ty::U64, i128::from(TURN1_MASK));
        let pc0_mask = fb.iconst(Ty::U64, i128::from(PC0_WAITING_MASK));
        let pc1_mask = fb.iconst(Ty::U64, i128::from(PC1_WAITING_MASK));
        let flag0 = fb.binop(BinOp::And, Ty::U64, state, flag0_mask);
        let flag1 = fb.binop(BinOp::And, Ty::U64, state, flag1_mask);
        let turn1 = fb.binop(BinOp::And, Ty::U64, state, turn1_mask);
        let pc0_waiting = fb.binop(BinOp::And, Ty::U64, state, pc0_mask);
        let pc1_waiting = fb.binop(BinOp::And, Ty::U64, state, pc1_mask);
        let pc0_enabled_candidate = fb.icmp(ICmpOp::Ne, Ty::U64, pc0_waiting, zero_cmp);
        fb.condbr(
            pc0_enabled_candidate,
            p0_flag_check,
            vec![],
            after_p0,
            vec![
                generated,
                last_parent,
                fingerprint,
                status,
                parent_digest,
                callback_digest,
            ],
        );

        fb.switch_to_block(p0_flag_check);
        let flag1_set = fb.icmp(ICmpOp::Ne, Ty::U64, flag1, zero_cmp);
        fb.condbr(flag1_set, p0_turn_check, vec![], p0_emit, vec![]);

        fb.switch_to_block(p0_turn_check);
        let turn_is_zero = fb.icmp(ICmpOp::Eq, Ty::U64, turn1, zero_cmp);
        fb.condbr(
            turn_is_zero,
            p0_emit,
            vec![],
            after_p0,
            vec![
                generated,
                last_parent,
                fingerprint,
                status,
                parent_digest,
                callback_digest,
            ],
        );

        fb.switch_to_block(p0_emit);
        let p0 = emit_action(
            &mut fb,
            0,
            ActionInputs {
                callback_ptr,
                callback_ty,
                callout: summary,
                parent_out,
                fingerprints_out,
                runtime_slots,
                parent,
                idx,
                state,
                generated,
                fingerprint,
                status,
                parent_digest,
                callback_digest,
            },
        );
        fb.br(
            after_p0,
            vec![
                p0.generated,
                p0.last_parent,
                p0.fingerprint,
                p0.status,
                p0.parent_digest,
                p0.callback_digest,
            ],
        );

        fb.switch_to_block(after_p0);
        let pc1_enabled_candidate = fb.icmp(ICmpOp::Ne, Ty::U64, pc1_waiting, zero_cmp);
        fb.condbr(
            pc1_enabled_candidate,
            p1_flag_check,
            vec![],
            after_p1,
            vec![
                p0_generated,
                p0_last_parent,
                p0_fingerprint,
                p0_status,
                p0_parent_digest,
                p0_callback_digest,
            ],
        );

        fb.switch_to_block(p1_flag_check);
        let flag0_set = fb.icmp(ICmpOp::Ne, Ty::U64, flag0, zero_cmp);
        fb.condbr(flag0_set, p1_turn_check, vec![], p1_emit, vec![]);

        fb.switch_to_block(p1_turn_check);
        let turn_is_one = fb.icmp(ICmpOp::Ne, Ty::U64, turn1, zero_cmp);
        fb.condbr(
            turn_is_one,
            p1_emit,
            vec![],
            after_p1,
            vec![
                p0_generated,
                p0_last_parent,
                p0_fingerprint,
                p0_status,
                p0_parent_digest,
                p0_callback_digest,
            ],
        );

        fb.switch_to_block(p1_emit);
        let p1 = emit_action(
            &mut fb,
            1,
            ActionInputs {
                callback_ptr,
                callback_ty,
                callout: summary,
                parent_out,
                fingerprints_out,
                runtime_slots,
                parent,
                idx,
                state,
                generated: p0_generated,
                fingerprint: p0_fingerprint,
                status: p0_status,
                parent_digest: p0_parent_digest,
                callback_digest: p0_callback_digest,
            },
        );
        fb.br(
            after_p1,
            vec![
                p1.generated,
                p1.last_parent,
                p1.fingerprint,
                p1.status,
                p1.parent_digest,
                p1.callback_digest,
            ],
        );

        fb.switch_to_block(after_p1);
        let one = fb.iconst(Ty::U64, 1);
        let next_idx = fb.binop(BinOp::Add, Ty::U64, idx, one);
        let next_state_count = fb.binop(BinOp::Add, Ty::U64, state_count, one);
        fb.br(
            header,
            vec![
                next_idx,
                next_state_count,
                p1_generated,
                p1_last_parent,
                p1_fingerprint,
                p1_status,
                p1_parent_digest,
                p1_callback_digest,
            ],
        );

        fb.switch_to_block(done);
        store_summary_slot(&mut fb, summary, 0, done_state_count);
        store_summary_slot(&mut fb, summary, 1, done_generated);
        store_summary_slot(&mut fb, summary, 2, done_last_parent);
        store_summary_slot(&mut fb, summary, 3, done_fingerprint);
        store_summary_slot(&mut fb, summary, 4, done_status);
        store_summary_slot(&mut fb, summary, 5, done_parent_digest);
        store_summary_slot(&mut fb, summary, 6, done_callback_digest);
        fb.ret(vec![done_status]);

        fb.build();
    }

    mb.build()
}

fn compile_to_jit(module: &trust_ir::Module, opt_level: OptLevel) -> ExecutableBuffer {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|err| panic!("{opt_level:?} compile failed: {err}"))
        .buffer
}

fn entry_signature() -> trust_cg_codegen::jit_contract::SymbolSignature {
    extern_c_signature(
        vec![
            abi_ptr(),
            abi_ptr(),
            abi_ptr(),
            abi_i64(),
            abi_ptr(),
            abi_ptr(),
            abi_ptr(),
            abi_ptr(),
        ],
        vec![abi_i64()],
    )
}

fn enabled_actions(state: u64) -> Vec<u32> {
    let flag0 = state & FLAG0_MASK;
    let flag1 = state & FLAG1_MASK;
    let turn1 = state & TURN1_MASK;
    let mut actions = Vec::new();

    if state & PC0_WAITING_MASK != 0 && (flag1 == 0 || turn1 == 0) {
        actions.push(0);
    }
    if state & PC1_WAITING_MASK != 0 && (flag0 == 0 || turn1 != 0) {
        actions.push(1);
    }

    actions
}

fn candidate_fingerprint(fingerprint: u64, parent: u64, idx: u64, action: u32, state: u64) -> u64 {
    let action_term = u64::from(action).wrapping_mul(TCG_ACTION_STRIDE);
    let idx_term = idx.wrapping_mul(IDX_PRIME);
    let parent_term = parent.wrapping_mul(PARENT_MIX);
    let state_action = state ^ action_term;
    let base = fingerprint ^ state_action;
    base.wrapping_add(parent_term)
        .wrapping_add(idx_term)
        .wrapping_mul(FINGERPRINT_PRIME)
        .wrapping_add(action_term)
}

fn generated_fingerprint(candidate: u64, runtime_value: u64) -> u64 {
    (candidate ^ runtime_value)
        .wrapping_mul(RUNTIME_PRIME)
        .wrapping_add(CALLOUT_ENABLED)
}

fn next_parent_digest(
    parent_digest: u64,
    parent: u64,
    idx: u64,
    action: u32,
    generated: u64,
) -> u64 {
    let action_term = u64::from(action).wrapping_mul(TCG_ACTION_STRIDE);
    let parent_mix = parent ^ idx.wrapping_mul(PARENT_INDEX_PRIME) ^ action_term;
    (parent_digest ^ parent_mix)
        .wrapping_mul(PARENT_DIGEST_PRIME)
        .wrapping_add(generated)
}

fn next_fingerprint_digest(
    fingerprint: u64,
    emitted_fingerprint: u64,
    action: u32,
    generated: u64,
) -> u64 {
    (fingerprint ^ emitted_fingerprint)
        .wrapping_mul(FINGERPRINT_DIGEST_PRIME)
        .wrapping_add(generated)
        .wrapping_add(u64::from(action))
}

fn next_callback_digest(
    callback_digest: u64,
    runtime_value: u64,
    candidate: u64,
    parent: u64,
    action: u32,
) -> u64 {
    let action_term = u64::from(action).wrapping_mul(TCG_ACTION_STRIDE);
    let callback_mix = runtime_value
        .wrapping_add(runtime_value ^ candidate)
        .wrapping_add(action_term);
    (callback_digest ^ callback_mix)
        .wrapping_mul(CALLBACK_DIGEST_PRIME)
        .wrapping_add(parent)
}

fn reference_run(parents: &[u64], states: &[u64]) -> MclRun {
    assert_eq!(parents.len(), states.len());

    let mut generated = 0_u64;
    let mut last_parent = 0_u64;
    let mut fingerprint = FINGERPRINT_SEED;
    let status = 0_u64;
    let mut parent_digest = PARENT_DIGEST_SEED;
    let mut callback_digest = CALLBACK_DIGEST_SEED;
    let mut parent_indexes = Vec::new();
    let mut fingerprints = Vec::new();
    let mut runtime_values = Vec::new();
    let mut last_callback = None;

    for (idx, (&parent, &state)) in parents.iter().zip(states).enumerate() {
        let idx = idx as u64;
        for action in enabled_actions(state) {
            let candidate = candidate_fingerprint(fingerprint, parent, idx, action, state);
            let runtime_value = runtime_callback_value(parent, idx, action, state, candidate);
            let emitted_fingerprint = generated_fingerprint(candidate, runtime_value);

            parent_indexes.push(idx);
            fingerprints.push(emitted_fingerprint);
            runtime_values.push(runtime_value);
            generated = generated.wrapping_add(CALLOUT_ENABLED);
            last_parent = idx;
            parent_digest = next_parent_digest(parent_digest, parent, idx, action, generated);
            fingerprint =
                next_fingerprint_digest(fingerprint, emitted_fingerprint, action, generated);
            callback_digest =
                next_callback_digest(callback_digest, runtime_value, candidate, parent, action);
            last_callback = Some(CallbackObservation {
                parent,
                idx,
                action,
                state,
            });
        }
    }

    MclRun {
        summary: [
            parents.len() as u64,
            generated,
            last_parent,
            fingerprint,
            status,
            parent_digest,
            callback_digest,
        ],
        parent_indexes,
        fingerprints,
        runtime_values,
        calls: generated as usize,
        last_callback,
    }
}

fn reset_callback_observations() {
    CALLBACK_CALLS.store(0, Ordering::SeqCst);
    CALLBACK_LAST_PARENT.store(u64::MAX, Ordering::SeqCst);
    CALLBACK_LAST_IDX.store(u64::MAX, Ordering::SeqCst);
    CALLBACK_LAST_ACTION.store(u32::MAX, Ordering::SeqCst);
    CALLBACK_LAST_STATE.store(u64::MAX, Ordering::SeqCst);
}

fn run_at(opt_level: OptLevel, parents: &[u64], states: &[u64]) -> MclRun {
    assert_eq!(parents.len(), states.len());
    reset_callback_observations();

    let module = build_mcl_fused_parent_loop_module();
    let buffer = compile_to_jit(&module, opt_level);
    let entry: EntryFn = bind_ty_reducer_entry(&buffer, opt_level, ENTRY_NAME, entry_signature());

    let max_generated = parents.len().saturating_mul(2);
    let mut parent_indexes = vec![u64::MAX; max_generated];
    let mut fingerprints = vec![u64::MAX; max_generated];
    let mut runtime_values = vec![u64::MAX; max_generated];
    let mut summary = [u64::MAX; SUMMARY_SLOTS];
    let status = entry(
        host_mcl_runtime_callback,
        parents.as_ptr(),
        states.as_ptr(),
        parents.len() as u64,
        parent_indexes.as_mut_ptr(),
        fingerprints.as_mut_ptr(),
        runtime_values.as_mut_ptr(),
        summary.as_mut_ptr(),
    );

    assert_eq!(
        status, summary[4],
        "{opt_level:?} return/status summary mismatch"
    );
    let generated = usize::try_from(summary[1]).expect("generated count should fit usize");
    assert!(
        generated <= max_generated,
        "{opt_level:?} generated {generated} exceeds capacity {max_generated}"
    );
    parent_indexes.truncate(generated);
    fingerprints.truncate(generated);
    runtime_values.truncate(generated);

    let calls = CALLBACK_CALLS.load(Ordering::SeqCst);
    let last_callback = (calls != 0).then(|| CallbackObservation {
        parent: CALLBACK_LAST_PARENT.load(Ordering::SeqCst),
        idx: CALLBACK_LAST_IDX.load(Ordering::SeqCst),
        action: CALLBACK_LAST_ACTION.load(Ordering::SeqCst),
        state: CALLBACK_LAST_STATE.load(Ordering::SeqCst),
    });

    MclRun {
        summary,
        parent_indexes,
        fingerprints,
        runtime_values,
        calls,
        last_callback,
    }
}

#[derive(Debug, PartialEq, Eq)]
struct BlockedActivation {
    code: NativeInstallGateRejectionCode,
    parent_indexes: Vec<u64>,
    fingerprints: Vec<u64>,
    runtime_values: Vec<u64>,
    summary: [u64; SUMMARY_SLOTS],
    calls: usize,
}

impl BlockedActivation {
    fn assert_native_state_untouched(&self, name: &str) {
        assert_eq!(self.calls, 0, "{name} must block before runtime callback");
        assert!(
            self.parent_indexes.iter().all(|&value| value == u64::MAX),
            "{name} must block before parent-index writes"
        );
        assert!(
            self.fingerprints.iter().all(|&value| value == u64::MAX),
            "{name} must block before fingerprint writes"
        );
        assert!(
            self.runtime_values.iter().all(|&value| value == u64::MAX),
            "{name} must block before runtime-slot writes"
        );
        assert_eq!(
            self.summary,
            [u64::MAX; SUMMARY_SLOTS],
            "{name} must block before summary writes"
        );
    }
}

fn compile_service_profile(opt_level: OptLevel) -> CompileProfile {
    let mut compiler = CompilerConfig::jit_fast(Target::Aarch64);
    compiler.opt_level = opt_level;
    CompileProfile::Custom {
        compiler,
        jit: JitConfig {
            opt_level,
            verify: false,
            verify_dispatch: DispatchVerifyMode::ErrorOnFailure,
            profile_hooks: ProfileHookMode::None,
            emit_entry_counters: false,
            cache_certificates: false,
        },
    }
}

#[derive(Clone, Debug)]
struct ObservedTyKernelPayload {
    target: TargetDescriptor,
    abi: AbiDescriptor,
    layout: LayoutManifest,
    trust_ir_sha256: String,
    native_payload_sha256: String,
    code_size_bytes: u64,
    symbol_offset_bytes: u64,
    symbol_size_bytes: u64,
}

fn observe_ty_kernel_payload(opt_level: OptLevel) -> ObservedTyKernelPayload {
    // The product manifest carries TY-specific layout and proof claims, but
    // compile-service preflight deliberately accepts only compiler-derived
    // target/core-layout facts. Calibrate the portable fixture with a
    // compile-only request that grants no manifest or install authority, then
    // bind the authoritative request below to a fresh deterministic compile.
    let module = build_mcl_fused_parent_loop_module();
    let mut request = CompileRequest::new("ty-mcl-observe-live-payload", CompileGeneration::new(0));
    request.profile = compile_service_profile(opt_level);
    request.install_intent = InstallIntent::CompileOnly;
    request.provenance.source_kind = SourceKind::TrustIrModule;

    let response = CompileService::default().compile(request, &module);
    assert_eq!(
        response.status,
        CompileStatus::Compiled,
        "compile-only TY payload observation diagnostics: {:?}",
        response.diagnostics
    );
    assert_eq!(
        response.disposition,
        ArtifactInstallDisposition::ProfileOnly,
        "payload observation must not carry install authority"
    );
    let binding = response
        .artifact
        .as_ref()
        .and_then(|artifact| artifact.install.installed_payload_binding.as_ref())
        .expect("compile-only TY observation seals a live payload binding");
    let symbol = binding
        .symbols
        .iter()
        .find(|symbol| symbol.name == ENTRY_NAME)
        .expect("live TY payload binding contains the reducer entry");
    assert_eq!(symbol.signature, entry_signature());

    ObservedTyKernelPayload {
        target: binding.authoritative_target.clone(),
        abi: binding.authoritative_abi.clone(),
        layout: binding.authoritative_layout.clone(),
        trust_ir_sha256: binding.trust_ir_module_sha256.clone(),
        native_payload_sha256: binding.native_payload_sha256.clone(),
        code_size_bytes: binding.code_size_bytes,
        symbol_offset_bytes: symbol.start_offset,
        symbol_size_bytes: symbol.end_offset - symbol.start_offset,
    }
}

fn compile_service_ty_manifest(
    observed: &ObservedTyKernelPayload,
    identity: &TyNativeFusedManifestIdentity,
) -> ArtifactManifestV1 {
    let proof_policy = ProofPolicy::disabled();
    let mut invalidation = InvalidationKey::new(
        identity.spec_source_lock_sha256.clone(),
        identity.trust_cg_source_lock_sha256.clone(),
        observed.target.checksum(),
        observed.abi.checksum(),
        observed.layout.checksum(),
        proof_policy.checksum(),
        identity.generation,
    );
    invalidation.extra.insert(
        "trust_ir_sha256".to_owned(),
        observed.trust_ir_sha256.clone(),
    );
    invalidation.extra.insert(
        "native_payload_sha256".to_owned(),
        observed.native_payload_sha256.clone(),
    );

    let mut manifest = ArtifactManifestV1::new(
        format!("ty-mcl-compile-service-{ENTRY_NAME}"),
        JitArtifactKind::ExecutableMemory,
        observed.target.clone(),
        observed.abi.clone(),
        observed.layout.clone(),
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: ENTRY_NAME.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: entry_signature(),
        offset_bytes: Some(observed.symbol_offset_bytes),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: "executable_text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: observed.code_size_bytes,
        alignment_bytes: Target::Aarch64.stack_alignment(),
        checksum: None,
    });
    manifest.metadata.insert(
        "native_payload_sha256".to_owned(),
        observed.native_payload_sha256.clone(),
    );
    manifest.metadata.insert(
        "trust_ir_sha256".to_owned(),
        observed.trust_ir_sha256.clone(),
    );
    manifest
        .metadata
        .insert("consumer".to_owned(), "ty".to_owned());
    manifest.metadata.insert(
        "classification".to_owned(),
        "compiler-sealed-ty-reducer-entrypoint".to_owned(),
    );
    manifest
}

fn compile_ty_kernel_to_installed_artifact(
    opt_level: OptLevel,
    identity: &TyNativeFusedManifestIdentity,
) -> (
    InstalledArtifact,
    ArtifactManifestV1,
    ArtifactManifestV1,
    TyNativeFusedManifestIdentity,
) {
    let module = build_mcl_fused_parent_loop_module();
    let observed = observe_ty_kernel_payload(opt_level);
    let mut live_identity = identity.clone();
    live_identity.trust_ir_sha256 = observed.trust_ir_sha256.clone();
    live_identity.native_payload_sha256 = observed.native_payload_sha256.clone();

    // This product/control-plane manifest retains TY's independently checked
    // status/deopt, wrapper, and transition-cluster contract. It is consumed by
    // the TY activation gate, never presented as compiler-derived layout.
    let mut product_manifest = ty_native_fused_parent_loop_manifest_for_symbol_with_proof_policy(
        opt_level,
        ENTRY_NAME,
        entry_signature(),
        observed.symbol_offset_bytes,
        observed.symbol_size_bytes,
        observed.code_size_bytes,
        live_identity.clone(),
        ProofPolicy::disabled(),
    );
    product_manifest.target = observed.target.clone();
    product_manifest.abi = observed.abi.clone();
    product_manifest.invalidation.target_checksum = product_manifest.target.checksum();
    product_manifest.invalidation.abi_checksum = product_manifest.abi.checksum();
    product_manifest.invalidation.layout_checksum = product_manifest.layout.checksum();
    product_manifest.metadata.insert(
        "invalidation_checksum".to_owned(),
        product_manifest.invalidation.checksum().to_string(),
    );

    // The installed artifact is separately bound to a minimal manifest whose
    // target, core layout, payload digest, section extent, and symbol range all
    // came from the compiler-sealed observation above.
    let compile_manifest = compile_service_ty_manifest(&observed, &live_identity);
    let mut request = CompileRequest::new(
        "ty-mcl-compile-service-activation",
        CompileGeneration::new(live_identity.generation),
    )
    .with_artifact_manifest(compile_manifest.clone());
    request.profile = compile_service_profile(opt_level);
    request.proof_policy = compile_manifest.proof_policy.clone();
    request.provenance.source_kind = SourceKind::TrustIrModule;
    request.provenance.source_fingerprint = Some(live_identity.spec_source_lock_sha256.clone());
    request
        .provenance
        .caller_context
        .insert("native_install_consumer".to_owned(), "ty".to_owned());
    request.provenance.caller_context.insert(
        "native_install_consumer_mode".to_owned(),
        "direct_compile".to_owned(),
    );
    request.provenance.caller_context.insert(
        "trust_ir_sha256".to_owned(),
        live_identity.trust_ir_sha256.clone(),
    );

    let response = CompileService::default().compile(request, &module);
    assert_eq!(
        response.status,
        CompileStatus::Compiled,
        "compile-service diagnostics: {:?}",
        response.diagnostics
    );
    let packet = response
        .native_install_gate_packet()
        .expect("compiled TY executable should carry a direct-install gate packet");
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(
        packet.actions.expose_callable,
        "direct compile gate should authorize installed-artifact exposure"
    );
    let installed = response
        .into_installed_artifact()
        .expect("compile service should expose an installed TY artifact");
    assert_eq!(
        installed.metadata.artifact_manifest,
        Some(ArtifactManifestReference::from_manifest(&compile_manifest))
    );
    let binding = installed
        .metadata
        .installed_payload_binding
        .as_ref()
        .expect("installed TY artifact retains compiler-sealed payload authority");
    assert_eq!(
        binding.native_payload_sha256,
        live_identity.native_payload_sha256
    );
    assert_eq!(
        binding.trust_ir_module_sha256,
        live_identity.trust_ir_sha256
    );

    (installed, compile_manifest, product_manifest, live_identity)
}

#[allow(clippy::result_large_err)] // Failure carries the complete blocked-activation evidence.
fn run_installed_activation(
    installed: &InstalledArtifact,
    manifest: &ArtifactManifestV1,
    evidence: ProofEvidenceSummary,
    gate_input: NativeInstallGateInput,
    parents: &[u64],
    states: &[u64],
) -> Result<MclRun, BlockedActivation> {
    run_installed_activation_with_admission(
        installed,
        manifest,
        evidence,
        gate_input,
        parents,
        states,
        accepted_ty_activation_admission_evidence,
    )
}

fn accepted_ty_activation_admission_evidence(
    packet: &NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
) -> NativeInstallGateConsumerAdmissionEvidence {
    NativeInstallGateConsumerAdmissionEvidence::from_packet(
        packet,
        current,
        native_install_gate_consumer_allowlist_key(packet, current)
            .expect("TY activation packet should have an allowlist key"),
        true,
        true,
        true,
    )
}

#[allow(clippy::result_large_err)] // Failure carries the complete blocked-activation evidence.
fn run_installed_activation_with_admission<F>(
    installed: &InstalledArtifact,
    manifest: &ArtifactManifestV1,
    evidence: ProofEvidenceSummary,
    gate_input: NativeInstallGateInput,
    parents: &[u64],
    states: &[u64],
    admission_evidence_for: F,
) -> Result<MclRun, BlockedActivation>
where
    F: FnOnce(
        &NativeInstallGatePacket,
        &NativeInstallGateRevalidationInput,
    ) -> NativeInstallGateConsumerAdmissionEvidence,
{
    assert_eq!(parents.len(), states.len());
    reset_callback_observations();

    let max_generated = parents.len().saturating_mul(2);
    let mut parent_indexes = vec![u64::MAX; max_generated];
    let mut fingerprints = vec![u64::MAX; max_generated];
    let mut runtime_values = vec![u64::MAX; max_generated];
    let mut summary = [u64::MAX; SUMMARY_SLOTS];

    let packet = validate_native_install_gate(&gate_input);
    if packet.disposition != NativeInstallGateDisposition::Installable
        || !packet.actions.ty_native_activate
    {
        return Err(BlockedActivation {
            code: packet
                .rejection_code
                .expect("rejected activation packet should carry a code"),
            parent_indexes,
            fingerprints,
            runtime_values,
            summary,
            calls: CALLBACK_CALLS.load(Ordering::SeqCst),
        });
    }

    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let admission_evidence = admission_evidence_for(&packet, &current);
    let admission = native_install_gate_consumer_admission(
        &packet,
        Some(packet.packet_hash),
        &current,
        &admission_evidence,
    );
    if admission.disposition != NativeInstallGateDisposition::Installable
        || !admission.actions.ty_native_activate
    {
        return Err(BlockedActivation {
            code: admission
                .rejection_code
                .expect("rejected activation admission should carry a code"),
            parent_indexes,
            fingerprints,
            runtime_values,
            summary,
            calls: CALLBACK_CALLS.load(Ordering::SeqCst),
        });
    }

    // The product/control-plane manifest is intentionally richer than the
    // compiler manifest used for typed lookup, so their manifest checksums do
    // not match. Bridge the two authority planes through the immutable facts
    // they must share: the compiler-derived target/ABI and the exact Trust IR
    // and native payload digests. A self-consistent product packet for any
    // other payload must still fail closed before callable exposure.
    let installed_matches_product_packet = installed
        .metadata
        .installed_payload_binding
        .as_ref()
        .is_some_and(|binding| {
            binding.authoritative_target.checksum() == packet.artifact.target_checksum
                && binding.authoritative_abi.checksum() == packet.artifact.abi_checksum
                && binding.trust_ir_module_sha256 == packet.artifact.trust_ir_sha256
                && binding.native_payload_sha256 == packet.artifact.native_payload_sha256
        });
    if !installed_matches_product_packet {
        return Err(BlockedActivation {
            code: NativeInstallGateRejectionCode::EvidenceBindingMismatch,
            parent_indexes,
            fingerprints,
            runtime_values,
            summary,
            calls: CALLBACK_CALLS.load(Ordering::SeqCst),
        });
    }

    let contract = ty_reducer_lookup_contract(manifest, ENTRY_NAME, entry_signature())
        .with_required_proof_evidence()
        .with_proof_evidence(evidence);
    let typed = installed
        .get_contract_symbol_bound::<EntryFn>(manifest, &contract)
        .unwrap_or_else(|err| {
            panic!("compile-service installed TY activation lookup failed: {err}")
        });
    assert_eq!(typed.symbol(), ENTRY_NAME);
    assert_eq!(typed.signature(), &entry_signature());
    assert_eq!(typed.artifact_checksum(), manifest.checksum());

    let entry = unsafe {
        // SAFETY: the installed-artifact contract lookup above validated the
        // manifest, TY proof evidence, symbol, and extern "C" signature.
        typed.into_fn()
    };
    let status = entry(
        host_mcl_runtime_callback,
        parents.as_ptr(),
        states.as_ptr(),
        parents.len() as u64,
        parent_indexes.as_mut_ptr(),
        fingerprints.as_mut_ptr(),
        runtime_values.as_mut_ptr(),
        summary.as_mut_ptr(),
    );

    assert_eq!(status, summary[4]);
    let generated = usize::try_from(summary[1]).expect("generated count should fit usize");
    assert!(generated <= max_generated);
    parent_indexes.truncate(generated);
    fingerprints.truncate(generated);
    runtime_values.truncate(generated);

    let calls = CALLBACK_CALLS.load(Ordering::SeqCst);
    let last_callback = (calls != 0).then(|| CallbackObservation {
        parent: CALLBACK_LAST_PARENT.load(Ordering::SeqCst),
        idx: CALLBACK_LAST_IDX.load(Ordering::SeqCst),
        action: CALLBACK_LAST_ACTION.load(Ordering::SeqCst),
        state: CALLBACK_LAST_STATE.load(Ordering::SeqCst),
    });

    Ok(MclRun {
        summary,
        parent_indexes,
        fingerprints,
        runtime_values,
        calls,
        last_callback,
    })
}

fn native_fused_manifest_identity() -> TyNativeFusedManifestIdentity {
    TyNativeFusedManifestIdentity::fixture(ENTRY_NAME)
}

fn native_fused_evidence_refs() -> TyNativeFusedEvidenceRefs {
    TyNativeFusedEvidenceRefs::fixture(ENTRY_NAME)
}

fn native_fused_proof_opt_citation(
    refs: &TyNativeFusedEvidenceRefs,
) -> ProofOptimizationCertificateCitation {
    ProofOptimizationCertificateCitation {
        function_name: ENTRY_NAME.to_owned(),
        certificate_id: refs.certificate_identity.clone(),
        proof_hash: "00000000000000000000000000000801".to_owned(),
        validation_hash: refs.proof_validation_sha256.clone(),
        source_region_hash: "00000000000000000000000000000802".to_owned(),
        target_region_hash: "00000000000000000000000000000803".to_owned(),
        transform_name: "ty-native-fused-parent-loop".to_owned(),
        transform_version: 1,
        admission: "proof-annotation+proof-facts".to_owned(),
        kind: "TyNativeFusedParentLoop".to_owned(),
        status: "applied".to_owned(),
        rejection_code: None,
        rejection_fact: None,
        rejection_detail: None,
        consumed_facts: TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS
            .iter()
            .map(|fact| ProofOptimizationConsumedFactCitation {
                name: fact.as_str().to_owned(),
                payload: Some(fact.metadata_key().to_owned()),
            })
            .collect(),
    }
}

fn native_fused_payload_identity(
    identity: &TyNativeFusedManifestIdentity,
) -> NativeInstallGatePayloadIdentity {
    NativeInstallGatePayloadIdentity {
        source_sha256: identity.spec_source_lock_sha256.clone(),
        trust_ir_sha256: identity.trust_ir_sha256.clone(),
        native_payload_sha256: identity.native_payload_sha256.clone(),
    }
}

fn native_fused_counter_scope(artifact_id: &str) -> String {
    format!(
        "ty:{}:{}:{}",
        TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE,
        NativeInstallGateSurface::TyActivation.as_str(),
        artifact_id
    )
}

fn native_fused_replay_identity(
    expected: &NativeInstallGateExpectedBindings,
    identity: &TyNativeFusedManifestIdentity,
    refs: &TyNativeFusedEvidenceRefs,
) -> NativeInstallGateReplayIdentity {
    NativeInstallGateReplayIdentity {
        schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
        replay_root_sha256: refs.replay_root_sha256.clone(),
        replay_consumer: "ty".to_owned(),
        replay_family: TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE.to_owned(),
        artifact_id: expected.artifact_id.clone(),
        source_sha256: identity.spec_source_lock_sha256.clone(),
        trust_ir_sha256: identity.trust_ir_sha256.clone(),
        native_payload_sha256: identity.native_payload_sha256.clone(),
        replay_record_sha256: String::new(),
    }
    .with_canonical_record_sha256()
}

fn native_fused_telemetry(
    expected: &NativeInstallGateExpectedBindings,
    refs: &TyNativeFusedEvidenceRefs,
) -> NativeInstallGateTelemetryInput {
    NativeInstallGateTelemetryInput {
        schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
        event_id: refs.telemetry_event_id.clone(),
        counter_scope: native_fused_counter_scope(&expected.artifact_id),
        record_sha256: String::new(),
        artifact_id: expected.artifact_id.clone(),
        manifest_checksum: expected.manifest_checksum,
        proof_report_sha256: Some(refs.proof_validation_sha256.clone()),
        layout_checksum: expected.layout_checksum,
        invalidation_checksum: expected.invalidation_checksum,
        disposition: NativeInstallGateDisposition::Installable,
        rejection_code: None,
        install_authority: NativeInstallGateAuthority::CanaryCallable,
        useful_native_delta: 0,
    }
    .with_canonical_record_sha256()
}

fn native_fused_gate_input(
    manifest: ArtifactManifestV1,
    identity: &TyNativeFusedManifestIdentity,
    refs: &TyNativeFusedEvidenceRefs,
    mut proof_summary: ProofEvidenceSummary,
) -> NativeInstallGateInput {
    let expected = NativeInstallGateExpectedBindings::from_manifest(&manifest);
    let payload_identity = native_fused_payload_identity(identity);
    let layout_evidence = NativeInstallGateLayoutEvidence::ty_fused_parent_loop_prework(
        expected.layout_checksum,
        expected.abi_checksum,
        expected.invalidation_checksum,
        TY_NATIVE_FUSED_PARENT_LOOP_WRAPPER_IDENTITY,
    );
    let replay_identity = native_fused_replay_identity(&expected, identity, refs);
    let telemetry = native_fused_telemetry(&expected, refs);
    proof_summary.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_GATE_RESULT_KEY.to_owned(),
        telemetry.record_sha256.clone(),
    );
    let proof_evidence = NativeInstallGateProofEvidence {
        summary: proof_summary,
        proof_report_sha256: Some(refs.proof_validation_sha256.clone()),
        obligation_set: Some("ty-native-fused-parent-loop-required-facts-v1".to_owned()),
        timeout_ms: Some(1_000),
        native_payload_sha256: Some(identity.native_payload_sha256.clone()),
    };
    let current_invalidation_checksum = expected.invalidation_checksum;
    let current_generation = expected.current_generation;

    NativeInstallGateInput {
        consumer: "ty".to_owned(),
        consumer_mode: TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE.to_owned(),
        surface: NativeInstallGateSurface::TyActivation,
        candidate_disposition: NativeInstallGateDisposition::Installable,
        requested_authority: NativeInstallGateAuthority::CanaryCallable,
        manifest_reference: Some(ArtifactManifestReference::from_manifest(&manifest)),
        manifest: Some(manifest),
        expected,
        payload_identity: payload_identity.clone(),
        candidate_payload_identity: payload_identity,
        layout_evidence: Some(layout_evidence),
        proof_evidence: Some(proof_evidence),
        current_invalidation_checksum,
        artifact_generation: current_generation,
        current_generation,
        revoked: false,
        deny_control: None,
        replay_identity: Some(replay_identity),
        telemetry: Some(telemetry),
    }
}

fn set_native_fused_proof_metadata(input: &mut NativeInstallGateInput, key: &str, value: &str) {
    input
        .proof_evidence
        .as_mut()
        .expect("native fused gate input carries proof evidence")
        .summary
        .metadata
        .insert(key.to_owned(), value.to_owned());
}

#[test]
fn ty_mcl_fused_parent_loop_proof_required_manifest_fails_closed_without_certificates() {
    reset_callback_observations();

    let module = build_mcl_fused_parent_loop_module();
    let buffer = compile_to_jit(&module, OptLevel::O3);
    let signature = entry_signature();
    let manifest = ty_reducer_manifest_with_proof_policy(
        &buffer,
        OptLevel::O3,
        ENTRY_NAME,
        signature.clone(),
        ProofPolicy::require_certificates(["ty-native-fused-parent-loop", "trust-cg-verify"]),
    );

    assert_eq!(manifest.proof_policy.mode, ProofMode::RequireCertificates);
    assert!(manifest.proof_policy.require_jit_certificate);
    assert!(manifest.proof_policy.require_layout_evidence);
    assert!(manifest.proof_policy.require_abi_evidence);
    assert!(manifest.proof_policy.requires_evidence());
    assert_eq!(
        manifest.invalidation.proof_policy_checksum,
        manifest.proof_policy.checksum()
    );

    let contract = ty_reducer_lookup_contract(&manifest, ENTRY_NAME, signature.clone());
    let err = buffer
        .get_fixture_contract_symbol_bound::<EntryFn>(&manifest, &contract)
        .expect_err("proof-required TY fused reducer must not expose a handle without evidence");
    match err {
        ArtifactContractError::MissingProofEvidence { rejection_code } => {
            assert_eq!(rejection_code, ProofEvidenceRejectionCode::MissingEvidence);
        }
        other => panic!("expected missing proof evidence rejection, got {other:?}"),
    }
    assert_eq!(CALLBACK_CALLS.load(Ordering::SeqCst), 0);

    let rejected = ProofEvidenceSummary::rejected(
        "trust-cg-verify",
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
        manifest.invalidation.checksum(),
        manifest.proof_policy.checksum(),
    );
    let rejected_contract =
        ty_reducer_lookup_contract(&manifest, ENTRY_NAME, signature).with_proof_evidence(rejected);
    let err = buffer
        .get_fixture_contract_symbol_bound::<EntryFn>(&manifest, &rejected_contract)
        .expect_err("proof-required TY fused reducer must not expose rejected evidence");
    match err {
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
    }
    assert_eq!(CALLBACK_CALLS.load(Ordering::SeqCst), 0);
}

#[test]
fn ty_mcl_native_fused_manifest_binds_proof_consumption_contract() {
    reset_callback_observations();
    assert_ty_native_fused_required_proof_fact_bridge();

    let module = build_mcl_fused_parent_loop_module();
    let buffer = compile_to_jit(&module, OptLevel::O3);
    let identity = native_fused_manifest_identity();
    let refs = native_fused_evidence_refs();
    let signature = entry_signature();
    let manifest = ty_native_fused_parent_loop_manifest(
        &buffer,
        OptLevel::O3,
        ENTRY_NAME,
        signature.clone(),
        identity.clone(),
    );
    let manifest_checksum = manifest.checksum();
    let manifest_checksum_text = manifest_checksum.to_string();
    let proof_policy_checksum_text = manifest.proof_policy.checksum().to_string();
    let invalidation_checksum_text = manifest.invalidation.checksum().to_string();

    assert_eq!(
        manifest
            .metadata
            .get("ty_manifest_schema")
            .map(String::as_str),
        Some(TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA)
    );
    assert_eq!(
        manifest
            .metadata
            .get("native_fused_kernel_identity")
            .map(String::as_str),
        Some(ENTRY_NAME)
    );
    let descriptor_identity = manifest
        .metadata
        .get(TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY)
        .expect("manifest binds native-fused transition-cluster descriptor identity");
    assert_eq!(
        manifest
            .layout
            .metadata
            .get(TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY),
        Some(descriptor_identity)
    );
    assert_eq!(
        manifest
            .invalidation
            .extra
            .get(TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY),
        Some(descriptor_identity)
    );
    assert_eq!(
        manifest.metadata.get("spec_source_lock_sha256"),
        Some(&identity.spec_source_lock_sha256)
    );
    assert_eq!(
        manifest.metadata.get("trust_ir_sha256"),
        Some(&identity.trust_ir_sha256)
    );
    assert_eq!(
        manifest.metadata.get("native_payload_sha256"),
        Some(&identity.native_payload_sha256)
    );
    assert_eq!(
        manifest.metadata.get("trust_cg_source_lock_sha256"),
        Some(&identity.trust_cg_source_lock_sha256)
    );
    assert_eq!(
        manifest
            .metadata
            .get("proof_policy_checksum")
            .map(String::as_str),
        Some(proof_policy_checksum_text.as_str())
    );
    assert_eq!(
        manifest
            .metadata
            .get("invalidation_checksum")
            .map(String::as_str),
        Some(invalidation_checksum_text.as_str())
    );
    assert_eq!(
        manifest
            .metadata
            .get("status_deopt_contract")
            .map(String::as_str),
        Some(TY_NATIVE_FUSED_PARENT_LOOP_STATUS_ABI)
    );
    assert_eq!(
        manifest
            .metadata
            .get("missing_proof_disposition")
            .map(String::as_str),
        Some("reject_non_promoting_useful_native_false")
    );
    assert_eq!(
        manifest.invalidation.source_fingerprint,
        identity.spec_source_lock_sha256
    );
    assert_eq!(
        manifest.invalidation.compiler_fingerprint,
        identity.trust_cg_source_lock_sha256
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
    assert!(manifest.proof_policy.requires_evidence());
    assert!(
        manifest
            .proof_policy
            .accepted_solvers
            .iter()
            .any(|solver| solver == "trust-cg-verify")
    );

    let status_record = manifest
        .layout
        .records
        .iter()
        .find(|record| record.name == "TyNativeFusedParentLoopStatusAbi")
        .expect("manifest binds status/deopt ABI record");
    assert_eq!(status_record.size_bytes, 32);
    assert_eq!(
        status_record
            .fields
            .iter()
            .map(|field| field.name.as_str())
            .collect::<Vec<_>>(),
        vec![
            "status",
            "deopt",
            "panic_code",
            "reserved",
            "generated_count",
            "first_failed_parent",
            "rollback_epoch"
        ]
    );
    for required_slice in [
        "flat_state_buffer",
        "parent_buffer",
        "successor_buffer",
        "fingerprint_buffer",
        "callback_status_buffer",
    ] {
        assert!(
            manifest
                .layout
                .slices
                .iter()
                .any(|slice| slice.name == required_slice),
            "manifest should bind {required_slice}"
        );
    }
    for fact in TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS {
        assert_eq!(
            manifest
                .metadata
                .get(&format!("required_fact.{}", fact.as_str()))
                .map(String::as_str),
            Some(fact.metadata_key()),
            "manifest should name required fact {}",
            fact.as_str()
        );
    }

    let evidence = ty_native_fused_verified_evidence(&manifest, &refs);
    assert_eq!(
        evidence
            .metadata
            .get("ty.native_fused.manifest_identity")
            .map(String::as_str),
        Some(manifest_checksum_text.as_str())
    );
    assert_eq!(
        evidence
            .metadata
            .get("ty.native_fused.certificate_identity"),
        Some(&refs.certificate_identity)
    );
    assert_eq!(
        evidence.metadata.get("ty.native_fused.replay_root_sha256"),
        Some(&refs.replay_root_sha256)
    );
    assert_eq!(
        evidence.metadata.get("ty.native_fused.telemetry_event_id"),
        Some(&refs.telemetry_event_id)
    );
    assert_eq!(
        evidence.metadata.get("ty.native_fused.gate_result_sha256"),
        Some(&refs.gate_result_sha256)
    );
    assert_eq!(
        evidence
            .metadata
            .get("ty.native_fused.proof_validation_sha256"),
        Some(&refs.proof_validation_sha256)
    );
    for fact in TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS {
        assert_eq!(
            evidence
                .metadata
                .get(fact.metadata_key())
                .map(String::as_str),
            Some("verified"),
            "verified evidence should bind {}",
            fact.as_str()
        );
    }

    let contract = ty_reducer_lookup_contract(&manifest, ENTRY_NAME, signature)
        .with_proof_evidence(evidence.clone());
    let typed = buffer
        .get_fixture_contract_symbol_bound::<EntryFn>(&manifest, &contract)
        .expect("complete TY native-fused evidence should expose a typed handle");
    assert_eq!(typed.symbol(), ENTRY_NAME);

    let gate_input = native_fused_gate_input(manifest, &identity, &refs, evidence);
    let packet = validate_native_install_gate(&gate_input);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ty_native_activate);
    assert!(packet.actions.useful_native_eligible);
    assert_eq!(
        packet
            .replay_identity
            .as_ref()
            .map(|replay| replay.replay_root_sha256.as_str()),
        Some(refs.replay_root_sha256.as_str())
    );
    assert_eq!(
        packet
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.event_id.as_str()),
        Some(refs.telemetry_event_id.as_str())
    );
    assert_eq!(
        packet.validation.proof_report_sha256.as_deref(),
        Some(refs.proof_validation_sha256.as_str())
    );
    assert_eq!(
        packet
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.useful_native_delta),
        Some(0)
    );
    assert_eq!(CALLBACK_CALLS.load(Ordering::SeqCst), 0);
}

#[test]
fn ty_mcl_native_fused_non_promoting_product_packet_binds_proof_opt_citation() {
    reset_callback_observations();

    let module = build_mcl_fused_parent_loop_module();
    let buffer = compile_to_jit(&module, OptLevel::O3);
    let identity = native_fused_manifest_identity();
    let refs = native_fused_evidence_refs();
    let signature = entry_signature();
    let mut manifest = ty_native_fused_parent_loop_manifest(
        &buffer,
        OptLevel::O3,
        ENTRY_NAME,
        signature,
        identity.clone(),
    );
    manifest.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY.to_owned(),
        refs.certificate_identity.clone(),
    );
    let reducer_summary = native_fused_reducer_evidence_summary();
    bind_native_fused_reducer_evidence(&mut manifest, &reducer_summary);
    let evidence = ty_native_fused_verified_evidence(&manifest, &refs);
    let gate_packet = validate_native_install_gate(&native_fused_gate_input(
        manifest.clone(),
        &identity,
        &refs,
        evidence,
    ));
    assert_eq!(
        gate_packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(gate_packet.actions.ty_native_activate);
    assert!(gate_packet.actions.useful_native_eligible);

    let citation = native_fused_proof_opt_citation(&refs);
    let product_packet = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        &citation,
    )
    .expect("complete native-fused evidence should emit a non-promoting product packet");

    assert_eq!(
        product_packet.schema,
        NATIVE_INSTALL_GATE_PRODUCT_PROMOTION_PACKET_SCHEMA
    );
    assert_eq!(
        product_packet.schema_version,
        NATIVE_INSTALL_GATE_PRODUCT_PROMOTION_PACKET_SCHEMA_VERSION
    );
    assert_eq!(product_packet.issue, 800);
    assert!(!product_packet.product_promotion_allowed);
    assert_eq!(
        product_packet.product_promotion_disposition,
        "reject_non_promoting_useful_native_false"
    );
    assert!(!product_packet.promotion_useful_native_credit_allowed);
    assert_eq!(
        product_packet.proof_optimization_certificate_id,
        citation.certificate_id
    );
    assert_eq!(
        product_packet.parent_proof_certificate_identity,
        refs.certificate_identity
    );
    assert_eq!(
        product_packet.proof_optimization_proof_hash,
        citation.proof_hash
    );
    assert_eq!(
        product_packet.proof_optimization_validation_hash,
        citation.validation_hash
    );
    assert_eq!(
        product_packet.proof_optimization_source_region_hash,
        citation.source_region_hash
    );
    assert_eq!(
        product_packet.proof_optimization_target_region_hash,
        citation.target_region_hash
    );
    assert_eq!(
        product_packet.proof_optimization_transform_name,
        citation.transform_name
    );
    assert_eq!(product_packet.proof_optimization_transform_version, 1);
    assert_eq!(
        product_packet.proof_optimization_admission,
        "proof-annotation+proof-facts"
    );
    assert_eq!(
        product_packet.proof_optimization_kind,
        "TyNativeFusedParentLoop"
    );
    assert_eq!(product_packet.proof_optimization_status, "applied");
    assert_eq!(
        product_packet.gate_proof_validation_hash,
        refs.proof_validation_sha256
    );
    assert_eq!(product_packet.replay_root_sha256, refs.replay_root_sha256);
    assert_eq!(
        product_packet.replay_binding_packet_hash,
        gate_packet.packet_hash
    );
    assert_eq!(product_packet.telemetry_event_id, refs.telemetry_event_id);
    assert_eq!(product_packet.telemetry_useful_native_delta, 0);
    assert!(product_packet.gate_useful_native_eligible);
    assert!(product_packet.gate_ty_native_activate);
    assert_eq!(
        product_packet.reducer_evidence_schema,
        reducer_summary.schema
    );
    assert_eq!(
        product_packet.reducer_evidence_schema_version,
        reducer_summary.schema_version
    );
    assert_eq!(
        product_packet.reducer_evidence_packet_sha256,
        reducer_summary.packet_sha256
    );
    assert_eq!(
        product_packet.reducer_evidence_families,
        reducer_summary.reducer_families
    );
    assert_eq!(
        product_packet.status_deopt_contract,
        TY_NATIVE_FUSED_PARENT_LOOP_STATUS_ABI
    );
    assert_eq!(
        product_packet.deopt_rollback_condition,
        "status_deopt_or_dispatch_panic_before_successor_commit"
    );
    assert_eq!(
        product_packet.required_fact_bindings.len(),
        TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS.len()
    );
    for fact in TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS {
        assert!(
            product_packet.required_fact_bindings.iter().any(|binding| {
                binding.fact == fact.as_str()
                    && binding.manifest_metadata_value == fact.metadata_key()
                    && binding.invalidation_metadata_value == fact.metadata_key()
            }),
            "product packet should bind required fact {}",
            fact.as_str()
        );
    }
    assert_eq!(
        product_packet.packet_sha256,
        product_packet.canonical_packet_sha256()
    );

    let missing_reducer_summary = native_install_gate_non_promoting_product_promotion_packet_impl(
        &manifest,
        &gate_packet,
        &citation,
        None::<&TyReducerEvidenceCoverageSummary>,
    )
    .expect_err("missing reducer evidence summary should not emit a product packet");
    assert_eq!(
        missing_reducer_summary,
        NativeInstallGateProductPromotionRejectionReason::MissingReducerEvidenceBinding
    );

    let mut missing_reducer_hash_manifest = manifest.clone();
    missing_reducer_hash_manifest
        .metadata
        .remove("ty.local_reducer_evidence.packet_sha256");
    let missing_reducer_hash_err = native_install_gate_non_promoting_product_promotion_packet_impl(
        &missing_reducer_hash_manifest,
        &gate_packet,
        &citation,
        &reducer_summary,
    )
    .expect_err("missing reducer packet hash should fail closed");
    assert_eq!(
        missing_reducer_hash_err,
        NativeInstallGateProductPromotionRejectionReason::MissingReducerEvidenceBinding
    );

    let mut stale_reducer_hash_manifest = manifest.clone();
    stale_reducer_hash_manifest.metadata.insert(
        "ty.local_reducer_evidence.packet_sha256".to_owned(),
        "sha256:stale-local-reducer-evidence".to_owned(),
    );
    let stale_reducer_hash_err = native_install_gate_non_promoting_product_promotion_packet_impl(
        &stale_reducer_hash_manifest,
        &gate_packet,
        &citation,
        &reducer_summary,
    )
    .expect_err("stale reducer packet hash should fail closed");
    assert_eq!(
        stale_reducer_hash_err,
        NativeInstallGateProductPromotionRejectionReason::ReducerEvidenceBindingMismatch
    );

    let mut incomplete_reducer_summary = reducer_summary.clone();
    incomplete_reducer_summary.reducer_families.pop();
    let incomplete_reducer_err = native_install_gate_non_promoting_product_promotion_packet_impl(
        &manifest,
        &gate_packet,
        &citation,
        &incomplete_reducer_summary,
    )
    .expect_err("missing expected reducer family should fail closed");
    assert_eq!(
        incomplete_reducer_err,
        NativeInstallGateProductPromotionRejectionReason::ReducerEvidenceCoverageIncomplete
    );

    let missing_citation = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        None::<&ProofOptimizationCertificateCitation>,
    )
    .expect_err("missing citation should not emit a product packet");
    assert_eq!(
        missing_citation,
        NativeInstallGateProductPromotionRejectionReason::MissingProofOptimizationCitation
    );

    let mut missing_hash = citation.clone();
    missing_hash.validation_hash.clear();
    let missing_hash_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        &missing_hash,
    )
    .expect_err("missing validation hash should not emit a product packet");
    assert_eq!(
        missing_hash_err,
        NativeInstallGateProductPromotionRejectionReason::MissingValidationHash
    );

    let mut missing_source_region = citation.clone();
    missing_source_region.source_region_hash.clear();
    let missing_source_region_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        &missing_source_region,
    )
    .expect_err("missing source-region provenance should not emit a product packet");
    assert_eq!(
        missing_source_region_err,
        NativeInstallGateProductPromotionRejectionReason::MissingProofOptimizationCitation
    );

    let mut missing_proof_hash = citation.clone();
    missing_proof_hash.proof_hash.clear();
    let missing_proof_hash_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        &missing_proof_hash,
    )
    .expect_err("missing proof hash should not emit a product packet");
    assert_eq!(
        missing_proof_hash_err,
        NativeInstallGateProductPromotionRejectionReason::MissingProofOptimizationCitation
    );

    let mut missing_target_region = citation.clone();
    missing_target_region.target_region_hash.clear();
    let missing_target_region_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        &missing_target_region,
    )
    .expect_err("missing target-region provenance should not emit a product packet");
    assert_eq!(
        missing_target_region_err,
        NativeInstallGateProductPromotionRejectionReason::MissingProofOptimizationCitation
    );

    let mut mismatched_citation = citation.clone();
    mismatched_citation.validation_hash = "sha256:ty-wrong-proof-validation".to_owned();
    let mismatched_citation_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        &mismatched_citation,
    )
    .expect_err("mismatched citation should not emit a product packet");
    assert_eq!(
        mismatched_citation_err,
        NativeInstallGateProductPromotionRejectionReason::ProofOptimizationCitationMismatch
    );

    let mut wrong_certificate = citation.clone();
    wrong_certificate.certificate_id = "ty-native-fused-parent-loop:wrong-cert-v1".to_owned();
    let wrong_certificate_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        &wrong_certificate,
    )
    .expect_err("citation certificate id must match parent proof metadata");
    assert_eq!(
        wrong_certificate_err,
        NativeInstallGateProductPromotionRejectionReason::ProofOptimizationCitationMismatch
    );

    let mut wrong_transform = citation.clone();
    wrong_transform.transform_name = "proof-opts.no-overflow".to_owned();
    let mut wrong_transform_version = citation.clone();
    wrong_transform_version.transform_version = 2;
    let mut wrong_admission = citation.clone();
    wrong_admission.admission = "profile-only".to_owned();
    let mut wrong_kind = citation.clone();
    wrong_kind.kind = "CheckedToUnchecked".to_owned();
    for (name, bad_citation) in [
        ("transform", wrong_transform),
        ("transform version", wrong_transform_version),
        ("admission", wrong_admission),
        ("kind", wrong_kind),
    ] {
        let err = native_install_gate_non_promoting_product_promotion_packet(
            &manifest,
            &gate_packet,
            &bad_citation,
        )
        .expect_err("wrong citation route metadata should not emit a product packet");
        assert_eq!(
            err,
            NativeInstallGateProductPromotionRejectionReason::ProofOptimizationCitationMismatch,
            "{name}"
        );
    }

    let mut empty_consumed_facts = citation.clone();
    empty_consumed_facts.consumed_facts.clear();
    let empty_consumed_facts_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        &empty_consumed_facts,
    )
    .expect_err("citation must consume the TY proof facts");
    assert_eq!(
        empty_consumed_facts_err,
        NativeInstallGateProductPromotionRejectionReason::ProofOptimizationCitationMismatch
    );

    let mut incomplete_consumed_facts = citation.clone();
    incomplete_consumed_facts.consumed_facts.pop();
    let incomplete_consumed_facts_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        &incomplete_consumed_facts,
    )
    .expect_err("citation must cover all TY required proof facts and metadata keys");
    assert_eq!(
        incomplete_consumed_facts_err,
        NativeInstallGateProductPromotionRejectionReason::ProofOptimizationCitationMismatch
    );

    let mut wrong_fact_payload = citation.clone();
    wrong_fact_payload.consumed_facts[0].payload = Some("wrong-metadata-key".to_owned());
    let wrong_fact_payload_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &gate_packet,
        &wrong_fact_payload,
    )
    .expect_err("citation consumed facts must carry expected metadata payloads");
    assert_eq!(
        wrong_fact_payload_err,
        NativeInstallGateProductPromotionRejectionReason::ProofOptimizationCitationMismatch
    );

    let mut replay_root_packet = gate_packet.clone();
    replay_root_packet
        .replay_identity
        .as_mut()
        .expect("gate packet carries replay identity")
        .replay_root_sha256 = "sha256:wrong-ty-replay-root".to_owned();
    let replay_root_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &replay_root_packet,
        &citation,
    )
    .expect_err("replay identity root mismatch should fail closed");
    assert_eq!(
        replay_root_err,
        NativeInstallGateProductPromotionRejectionReason::ReplayIdentityMismatch
    );

    let mut nonzero_delta_packet = gate_packet.clone();
    nonzero_delta_packet
        .telemetry
        .as_mut()
        .expect("gate packet carries telemetry")
        .useful_native_delta = 1;
    let nonzero_delta_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &nonzero_delta_packet,
        &citation,
    )
    .expect_err("useful-native deltas must fail closed");
    assert_eq!(
        nonzero_delta_err,
        NativeInstallGateProductPromotionRejectionReason::UsefulNativeDeltaNonzero
    );

    let mut telemetry_hash_packet = gate_packet.clone();
    telemetry_hash_packet
        .telemetry
        .as_mut()
        .expect("gate packet carries telemetry")
        .record_sha256 = "sha256:wrong-telemetry-record".to_owned();
    let telemetry_hash_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &telemetry_hash_packet,
        &citation,
    )
    .expect_err("telemetry hash mismatch should fail closed");
    assert_eq!(
        telemetry_hash_err,
        NativeInstallGateProductPromotionRejectionReason::TelemetryMismatch
    );

    let mut missing_rollback_manifest = manifest.clone();
    missing_rollback_manifest
        .metadata
        .remove("deopt_rollback_condition");
    let missing_rollback_err = native_install_gate_non_promoting_product_promotion_packet(
        &missing_rollback_manifest,
        &gate_packet,
        &citation,
    )
    .expect_err("rollback/deopt metadata is required");
    assert_eq!(
        missing_rollback_err,
        NativeInstallGateProductPromotionRejectionReason::ManifestMissingRollbackMetadata
    );

    let mut approved_manifest = manifest.clone();
    approved_manifest
        .metadata
        .insert("product_promotion_approved".to_owned(), "true".to_owned());
    let approved_err = native_install_gate_non_promoting_product_promotion_packet(
        &approved_manifest,
        &gate_packet,
        &citation,
    )
    .expect_err("this packet must not approve product promotion");
    assert_eq!(
        approved_err,
        NativeInstallGateProductPromotionRejectionReason::ProductPromotionRequestedApproved
    );

    for (key, value) in [
        ("product_promotion", "Approved"),
        ("promotion_disposition", "USEFUL_NATIVE_PROMOTED"),
        ("product_promotion_requested_approved", "Promoted"),
        ("product_promotion_approved", "TRUE"),
    ] {
        let mut approved_variant = manifest.clone();
        approved_variant
            .metadata
            .insert(key.to_owned(), value.to_owned());
        let err = native_install_gate_non_promoting_product_promotion_packet(
            &approved_variant,
            &gate_packet,
            &citation,
        )
        .expect_err("approval variants should not emit product packets");
        assert_eq!(
            err,
            NativeInstallGateProductPromotionRejectionReason::ProductPromotionRequestedApproved,
            "{key}={value}"
        );
    }

    let mut wrong_surface_packet = gate_packet.clone();
    wrong_surface_packet.surface = NativeInstallGateSurface::CacheHit;
    let wrong_surface_err = native_install_gate_non_promoting_product_promotion_packet(
        &manifest,
        &wrong_surface_packet,
        &citation,
    )
    .expect_err("only TY native-fused activation gates are accepted");
    assert_eq!(
        wrong_surface_err,
        NativeInstallGateProductPromotionRejectionReason::GateNotTyNativeFusedActivation
    );

    assert_eq!(CALLBACK_CALLS.load(Ordering::SeqCst), 0);
}

#[test]
fn ty_mcl_native_fused_proof_refs_must_match_gate_inputs() {
    reset_callback_observations();

    let module = build_mcl_fused_parent_loop_module();
    let buffer = compile_to_jit(&module, OptLevel::O3);
    let identity = native_fused_manifest_identity();
    let refs = native_fused_evidence_refs();
    let signature = entry_signature();
    let manifest = ty_native_fused_parent_loop_manifest(
        &buffer,
        OptLevel::O3,
        ENTRY_NAME,
        signature,
        identity.clone(),
    );
    let evidence = ty_native_fused_verified_evidence(&manifest, &refs);

    let accepted = validate_native_install_gate(&native_fused_gate_input(
        manifest.clone(),
        &identity,
        &refs,
        evidence.clone(),
    ));
    assert_eq!(
        accepted.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(accepted.actions.ty_native_activate);

    let cases = [
        (
            "replay root",
            TY_NATIVE_FUSED_EVIDENCE_REPLAY_ROOT_KEY,
            "sha256:wrong-ty-replay-root",
            NativeInstallGateRejectionCode::ReplayIdentityMismatch,
        ),
        (
            "telemetry event",
            TY_NATIVE_FUSED_EVIDENCE_TELEMETRY_EVENT_KEY,
            "wrong-ty-native-fused-install",
            NativeInstallGateRejectionCode::TelemetryMismatch,
        ),
        (
            "gate result",
            TY_NATIVE_FUSED_EVIDENCE_GATE_RESULT_KEY,
            "sha256:wrong-ty-gate-result",
            NativeInstallGateRejectionCode::EvidenceBindingMismatch,
        ),
        (
            "certificate identity",
            TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY,
            "ty-native-fused-parent-loop:wrong-kernel:cert-v1",
            NativeInstallGateRejectionCode::EvidenceBindingMismatch,
        ),
    ];

    for (name, key, value, expected_code) in cases {
        let mut input =
            native_fused_gate_input(manifest.clone(), &identity, &refs, evidence.clone());
        set_native_fused_proof_metadata(&mut input, key, value);
        let packet = validate_native_install_gate(&input);
        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Rejected,
            "{name}"
        );
        assert_eq!(packet.rejection_code, Some(expected_code), "{name}");
        assert!(packet.actions.all_install_authority_blocked(), "{name}");
    }

    assert_eq!(CALLBACK_CALLS.load(Ordering::SeqCst), 0);
}

#[test]
fn ty_mcl_native_fused_stale_same_kernel_certificate_identity_rejects() {
    reset_callback_observations();

    let module = build_mcl_fused_parent_loop_module();
    let buffer = compile_to_jit(&module, OptLevel::O3);
    let identity = native_fused_manifest_identity();
    let refs = native_fused_evidence_refs();
    let signature = entry_signature();
    let manifest = ty_native_fused_parent_loop_manifest(
        &buffer,
        OptLevel::O3,
        ENTRY_NAME,
        signature,
        identity.clone(),
    );
    let evidence = ty_native_fused_verified_evidence(&manifest, &refs);

    let mut input = native_fused_gate_input(manifest, &identity, &refs, evidence);
    let stale_same_kernel_certificate = format!("ty-native-fused-parent-loop:{ENTRY_NAME}:cert-v0");
    set_native_fused_proof_metadata(
        &mut input,
        TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY,
        &stale_same_kernel_certificate,
    );

    let packet = validate_native_install_gate(&input);
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert!(packet.actions.all_install_authority_blocked());
    assert_eq!(CALLBACK_CALLS.load(Ordering::SeqCst), 0);
}

#[test]
fn ty_mcl_native_fused_stale_manifest_and_proof_same_kernel_certificate_identity_rejects() {
    reset_callback_observations();

    let module = build_mcl_fused_parent_loop_module();
    let buffer = compile_to_jit(&module, OptLevel::O3);
    let identity = native_fused_manifest_identity();
    let refs = native_fused_evidence_refs();
    let signature = entry_signature();
    let mut manifest = ty_native_fused_parent_loop_manifest(
        &buffer,
        OptLevel::O3,
        ENTRY_NAME,
        signature,
        identity.clone(),
    );
    let stale_same_kernel_certificate = format!("ty-native-fused-parent-loop:{ENTRY_NAME}:cert-v0");
    manifest.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY.to_owned(),
        stale_same_kernel_certificate.clone(),
    );
    let mut evidence = ty_native_fused_verified_evidence(&manifest, &refs);
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY.to_owned(),
        stale_same_kernel_certificate,
    );

    let packet = validate_native_install_gate(&native_fused_gate_input(
        manifest, &identity, &refs, evidence,
    ));
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert!(packet.actions.all_install_authority_blocked());
    assert_eq!(CALLBACK_CALLS.load(Ordering::SeqCst), 0);
}

#[test]
fn ty_mcl_native_fused_manifest_completeness_is_gate_enforced() {
    reset_callback_observations();

    let module = build_mcl_fused_parent_loop_module();
    let buffer = compile_to_jit(&module, OptLevel::O3);
    let identity = native_fused_manifest_identity();
    let refs = native_fused_evidence_refs();
    let signature = entry_signature();
    let manifest = ty_native_fused_parent_loop_manifest(
        &buffer,
        OptLevel::O3,
        ENTRY_NAME,
        signature,
        identity.clone(),
    );

    let mut variants = Vec::new();
    let mut missing_manifest_status = manifest.clone();
    missing_manifest_status
        .metadata
        .remove("status_deopt_contract");
    variants.push(("manifest status/deopt", missing_manifest_status));

    let mut missing_manifest_kernel = manifest.clone();
    missing_manifest_kernel
        .metadata
        .remove("native_fused_kernel_identity");
    variants.push(("manifest kernel identity", missing_manifest_kernel));

    let mut missing_layout_status = manifest.clone();
    missing_layout_status
        .layout
        .metadata
        .remove("status_deopt_contract");
    variants.push(("layout status/deopt", missing_layout_status));

    let mut missing_invalidation_kernel = manifest.clone();
    missing_invalidation_kernel
        .invalidation
        .extra
        .remove("native_fused_kernel_identity");
    variants.push(("invalidation kernel identity", missing_invalidation_kernel));

    let mut missing_manifest_descriptor = manifest.clone();
    missing_manifest_descriptor
        .metadata
        .remove(TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY);
    variants.push((
        "manifest transition-cluster descriptor identity",
        missing_manifest_descriptor,
    ));

    let mut missing_layout_descriptor = manifest.clone();
    missing_layout_descriptor
        .layout
        .metadata
        .remove(TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY);
    variants.push((
        "layout transition-cluster descriptor identity",
        missing_layout_descriptor,
    ));

    let mut missing_invalidation_descriptor = manifest.clone();
    missing_invalidation_descriptor
        .invalidation
        .extra
        .remove(TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY);
    variants.push((
        "invalidation transition-cluster descriptor identity",
        missing_invalidation_descriptor,
    ));

    let mut mismatched_layout_descriptor = manifest.clone();
    mismatched_layout_descriptor.layout.metadata.insert(
        TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY.to_owned(),
        "ty-native-fused-transition-cluster:wrong:descriptor-v1".to_owned(),
    );
    variants.push((
        "layout transition-cluster descriptor identity mismatch",
        mismatched_layout_descriptor,
    ));

    let mut mismatched_invalidation_descriptor = manifest.clone();
    mismatched_invalidation_descriptor
        .invalidation
        .extra
        .insert(
            TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY.to_owned(),
            "ty-native-fused-transition-cluster:wrong:descriptor-v1".to_owned(),
        );
    variants.push((
        "invalidation transition-cluster descriptor identity mismatch",
        mismatched_invalidation_descriptor,
    ));

    for (name, incomplete_manifest) in variants {
        let evidence = ty_native_fused_verified_evidence(&incomplete_manifest, &refs);
        let packet = validate_native_install_gate(&native_fused_gate_input(
            incomplete_manifest,
            &identity,
            &refs,
            evidence,
        ));
        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Rejected,
            "{name}"
        );
        assert_eq!(
            packet.rejection_code,
            Some(NativeInstallGateRejectionCode::MissingManifest),
            "{name}"
        );
        assert!(packet.actions.all_install_authority_blocked(), "{name}");
    }

    assert_eq!(CALLBACK_CALLS.load(Ordering::SeqCst), 0);
}

#[test]
fn ty_mcl_native_fused_missing_required_facts_are_non_promoting() {
    reset_callback_observations();
    assert_ty_native_fused_required_proof_fact_bridge();

    let module = build_mcl_fused_parent_loop_module();
    let buffer = compile_to_jit(&module, OptLevel::O3);
    let identity = native_fused_manifest_identity();
    let refs = native_fused_evidence_refs();
    let signature = entry_signature();
    let manifest = ty_native_fused_parent_loop_manifest(
        &buffer,
        OptLevel::O3,
        ENTRY_NAME,
        signature.clone(),
        identity.clone(),
    );

    for missing_fact in TY_NATIVE_FUSED_REQUIRED_PROOF_FACTS {
        let evidence = ty_native_fused_missing_fact_evidence(&manifest, &refs, missing_fact);
        assert_eq!(
            evidence
                .metadata
                .get("ty.native_fused.missing_fact")
                .map(String::as_str),
            Some(missing_fact.as_str())
        );
        assert_eq!(
            evidence
                .metadata
                .get("ty.native_fused.missing_disposition")
                .map(String::as_str),
            Some("reject_non_promoting_useful_native_false")
        );

        let contract = ty_reducer_lookup_contract(&manifest, ENTRY_NAME, signature.clone())
            .with_proof_evidence(evidence.clone());
        let err = buffer
            .get_fixture_contract_symbol_bound::<EntryFn>(&manifest, &contract)
            .expect_err("missing TY native-fused proof fact must not expose a typed handle");
        match err {
            ArtifactContractError::ProofEvidenceRejected {
                verdict,
                rejection_code,
                ..
            } => {
                assert_eq!(verdict, ProofEvidenceVerdict::MissingEvidence);
                assert_eq!(
                    rejection_code,
                    Some(ProofEvidenceRejectionCode::MissingEvidence)
                );
            }
            other => panic!(
                "expected missing proof evidence rejection for {}, got {other:?}",
                missing_fact.as_str()
            ),
        }

        let packet = validate_native_install_gate(&native_fused_gate_input(
            manifest.clone(),
            &identity,
            &refs,
            evidence,
        ));
        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Rejected,
            "{}",
            missing_fact.as_str()
        );
        assert_eq!(
            packet.rejection_code,
            Some(NativeInstallGateRejectionCode::ProofMissingEvidence),
            "{}",
            missing_fact.as_str()
        );
        assert_eq!(
            packet.validation.proof_reject_code,
            Some(missing_fact.as_str()),
            "packet evidence should preserve explicit missing fact {}",
            missing_fact.as_str()
        );
        assert!(packet.actions.all_install_authority_blocked());
        assert!(!packet.actions.ty_native_activate);
        assert!(!packet.actions.useful_native_eligible);
        assert_eq!(
            packet
                .telemetry
                .as_ref()
                .map(|telemetry| telemetry.useful_native_delta),
            Some(0)
        );

        let mut incomplete_verified = ty_native_fused_verified_evidence(&manifest, &refs);
        incomplete_verified
            .metadata
            .remove(missing_fact.metadata_key());
        let contract = ty_reducer_lookup_contract(&manifest, ENTRY_NAME, signature.clone())
            .with_proof_evidence(incomplete_verified.clone());
        let err = buffer
            .get_fixture_contract_symbol_bound::<EntryFn>(&manifest, &contract)
            .expect_err(
                "verified TY native-fused evidence missing a required fact must not expose a typed handle",
            );
        match err {
            ArtifactContractError::ProofEvidenceRejected {
                verdict,
                rejection_code,
                detail,
                ..
            } => {
                assert_eq!(verdict, ProofEvidenceVerdict::Verified);
                assert_eq!(
                    rejection_code,
                    Some(ProofEvidenceRejectionCode::MissingEvidence)
                );
                assert!(
                    detail.contains(missing_fact.as_str()),
                    "typed rejection should name missing fact {}, got {detail}",
                    missing_fact.as_str()
                );
            }
            other => panic!(
                "expected typed missing proof fact rejection for {}, got {other:?}",
                missing_fact.as_str()
            ),
        }
        let packet = validate_native_install_gate(&native_fused_gate_input(
            manifest.clone(),
            &identity,
            &refs,
            incomplete_verified,
        ));
        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Rejected,
            "verified evidence missing {} should still fail closed",
            missing_fact.as_str()
        );
        assert_eq!(
            packet.rejection_code,
            Some(NativeInstallGateRejectionCode::ProofMissingEvidence),
            "verified evidence missing {} should be non-promoting",
            missing_fact.as_str()
        );
        assert_eq!(
            packet.validation.proof_reject_code,
            Some(missing_fact.as_str()),
            "packet evidence should preserve missing fact {}",
            missing_fact.as_str()
        );
        assert!(packet.actions.all_install_authority_blocked());
        assert_eq!(
            packet
                .telemetry
                .as_ref()
                .map(|telemetry| telemetry.useful_native_delta),
            Some(0)
        );
    }

    assert_eq!(CALLBACK_CALLS.load(Ordering::SeqCst), 0);
}

#[test]
fn ty_mcl_compile_service_installed_artifact_activation_gates_native_call() {
    let parents = vec![0x31, 0x32, 0x55];
    let states = vec![
        PC0_WAITING_MASK,
        PC1_WAITING_MASK | FLAG0_MASK | TURN1_MASK,
        PC0_WAITING_MASK | FLAG1_MASK | TURN1_MASK,
    ];
    let expected = reference_run(&parents, &states);
    let seed_identity = native_fused_manifest_identity();
    let refs = native_fused_evidence_refs();
    let (installed, compile_manifest, product_manifest, identity) =
        compile_ty_kernel_to_installed_artifact(OptLevel::O3, &seed_identity);
    let compile_evidence = ty_native_fused_verified_evidence(&compile_manifest, &refs);
    let product_evidence = ty_native_fused_verified_evidence(&product_manifest, &refs);

    let activated = run_installed_activation(
        &installed,
        &compile_manifest,
        compile_evidence.clone(),
        native_fused_gate_input(
            product_manifest.clone(),
            &identity,
            &refs,
            product_evidence.clone(),
        ),
        &parents,
        &states,
    )
    .expect("accepted TY activation should call through installed artifact lookup");
    assert_eq!(activated, expected);

    let rollback_not_ready = run_installed_activation_with_admission(
        &installed,
        &compile_manifest,
        compile_evidence.clone(),
        native_fused_gate_input(
            product_manifest.clone(),
            &identity,
            &refs,
            product_evidence.clone(),
        ),
        &parents,
        &states,
        |packet, current| {
            let mut evidence = accepted_ty_activation_admission_evidence(packet, current);
            evidence.rollback_ready = false;
            evidence.with_canonical_evidence_sha256()
        },
    )
    .expect_err("missing TY rollback readiness must block before native activation");
    assert_eq!(
        rollback_not_ready.code,
        NativeInstallGateRejectionCode::EvidenceBindingMismatch
    );
    rollback_not_ready.assert_native_state_untouched("rollback-not-ready activation");

    let mut other_identity = identity.clone();
    other_identity.native_payload_sha256 = "sha256:ty-mcl-other-native-payload".to_owned();
    let mut other_product_manifest = product_manifest.clone();
    other_product_manifest.invalidation.extra.insert(
        "native_payload_sha256".to_owned(),
        other_identity.native_payload_sha256.clone(),
    );
    other_product_manifest.metadata.insert(
        "native_payload_sha256".to_owned(),
        other_identity.native_payload_sha256.clone(),
    );
    other_product_manifest.metadata.insert(
        "invalidation_checksum".to_owned(),
        other_product_manifest.invalidation.checksum().to_string(),
    );
    let other_product_evidence = ty_native_fused_verified_evidence(&other_product_manifest, &refs);
    let mismatched_payload = run_installed_activation(
        &installed,
        &compile_manifest,
        compile_evidence.clone(),
        native_fused_gate_input(
            other_product_manifest,
            &other_identity,
            &refs,
            other_product_evidence,
        ),
        &parents,
        &states,
    )
    .expect_err("a product packet for another native payload must not expose this artifact");
    assert_eq!(
        mismatched_payload.code,
        NativeInstallGateRejectionCode::EvidenceBindingMismatch
    );
    mismatched_payload.assert_native_state_untouched("product/installed payload mismatch");

    let mut stale = native_fused_gate_input(
        product_manifest.clone(),
        &identity,
        &refs,
        product_evidence.clone(),
    );
    stale.current_generation += 1;

    let mut revoked = native_fused_gate_input(
        product_manifest.clone(),
        &identity,
        &refs,
        product_evidence.clone(),
    );
    revoked.revoked = true;

    let mut kill_switch =
        native_fused_gate_input(product_manifest, &identity, &refs, product_evidence);
    kill_switch.deny_control = Some(
        NativeInstallGateDenyControlPlane::active(
            NativeInstallGateDenyScope::Global,
            NativeInstallGateDenyReason::KillSwitch,
        )
        .with_canonical_deny_sha256(),
    );

    for (name, input, expected_code) in [
        (
            "stale activation",
            stale,
            NativeInstallGateRejectionCode::StaleInvalidation,
        ),
        (
            "revoked activation",
            revoked,
            NativeInstallGateRejectionCode::RevokedArtifact,
        ),
        (
            "kill-switch activation",
            kill_switch,
            NativeInstallGateRejectionCode::KillSwitchActive,
        ),
    ] {
        let blocked = run_installed_activation(
            &installed,
            &compile_manifest,
            compile_evidence.clone(),
            input,
            &parents,
            &states,
        )
        .expect_err("rejected TY activation must not expose a callable entry");
        assert_eq!(blocked.code, expected_code, "{name}");
        blocked.assert_native_state_untouched(name);
    }
}

#[test]
fn ty_mcl_fused_parent_loop_o1_o3_match_reference() {
    let cases = [
        ("empty", vec![], vec![]),
        (
            "mixed",
            vec![0x31, 0x32, 0x55, 0x80, 0x99],
            vec![
                PC0_WAITING_MASK,
                PC1_WAITING_MASK | FLAG0_MASK | TURN1_MASK,
                PC0_WAITING_MASK | FLAG1_MASK | TURN1_MASK,
                PC0_WAITING_MASK | PC1_WAITING_MASK,
                PC1_WAITING_MASK | FLAG0_MASK,
            ],
        ),
    ];

    for (name, parents, states) in cases {
        let expected = reference_run(&parents, &states);
        let o1 = run_at(OptLevel::O1, &parents, &states);
        let o3 = run_at(OptLevel::O3, &parents, &states);

        assert_eq!(o1, expected, "O1 diverged for {name}");
        assert_eq!(o3, expected, "O3 diverged for {name}");
        assert_eq!(
            o3, o1,
            "O3 should match O1 for state count, generated count, parent indexes, fingerprints, callback results, and status in {name}"
        );
    }
}
