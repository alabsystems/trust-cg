// Regression for TY-shaped indirect callback ABI and call-clobber handling.
//
// The generated loop carries parent-loop state across an indirect callback with
// pointer, u32, and u64 arguments. The host callback deliberately clobbers
// the host C ABI's call-volatile GPRs before writing the status-shaped result.

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

#[path = "common/fixture_contract.rs"]
mod fixture_contract;
use fixture_contract::FixtureContractLookup;

#[cfg(target_arch = "aarch64")]
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard, PoisonError};

use trust_cg_codegen::jit_contract::{ArtifactChecksum, ArtifactContractError, SymbolSignature};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, ExecutableBuffer};
use trust_ir::{BinOp, CastOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

#[path = "common/ty_contract.rs"]
mod ty_contract;

use ty_contract::{
    abi_i32, abi_i64, abi_ptr, bind_ty_reducer_entry, extern_c_signature,
    ty_reducer_lookup_contract, ty_reducer_manifest, ty_reducer_manifest_for_symbol,
};

const ENTRY_NAME: &str = "ty_callback_abi_parent_loop";
const STATUS_RUNTIME_ERROR: u8 = 9;
const STATUS_OK: u8 = 0;
const CALLOUT_ENABLED: u64 = 1;
const TCG_STATE_BIAS: u64 = 80;
const INITIAL_CHECKSUM: u64 = 0x1234_5678;
const LIVE_LANES: u64 = 20;
const FPR_LIVE_LANES: u64 = 8;

type EntryFn = extern "C" fn(u64, *const u64, *mut u64, u64, *mut CallbackStatus, *mut u64) -> u64;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CallbackStatus {
    status: u8,
    _pad: [u8; 7],
    value: u64,
}

impl CallbackStatus {
    const fn poisoned() -> Self {
        Self {
            status: 0xaa,
            _pad: [0xbb; 7],
            value: u64::MAX,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LoopRun {
    summary: [u64; 4],
    states: Vec<u64>,
    callout: CallbackStatus,
    calls: usize,
}

// The JIT entry receives a bare `extern "C"` callback, so the host callback
// records into process-wide statics. libtest runs this binary's tests
// concurrently: every test that resets, reads, or drives these observations
// must hold a `CallbackObservations` (which owns `CALLBACK_OBSERVATION_LOCK`)
// for its whole body, or one test's native callbacks are counted against
// another test's "rejected before any native call" assertion.
static CALLBACK_OBSERVATION_LOCK: Mutex<()> = Mutex::new(());
static CALLBACK_CALLS: AtomicUsize = AtomicUsize::new(0);
static CALLBACK_LAST_LEN: AtomicU32 = AtomicU32::new(0);
static CALLBACK_LAST_IDX: AtomicU64 = AtomicU64::new(0);
static CALLBACK_LAST_PARENT: AtomicU64 = AtomicU64::new(0);

/// Exclusive access to the process-wide host-callback observations.
///
/// While a value is alive no other test in this binary can reset them or run
/// the host callback, so `calls()` counts every callback made in the process
/// since the last `reset()`.
struct CallbackObservations {
    _serial: MutexGuard<'static, ()>,
}

impl CallbackObservations {
    /// Blocks until no other test owns the observations, then resets them.
    /// A poisoned lock (a test panicked while holding it) is taken anyway:
    /// the reset discards whatever that test left behind, so one failure does
    /// not cascade into every later test.
    fn acquire() -> Self {
        let observations = Self {
            _serial: CALLBACK_OBSERVATION_LOCK
                .lock()
                .unwrap_or_else(PoisonError::into_inner),
        };
        observations.reset();
        observations
    }

    fn reset(&self) {
        CALLBACK_CALLS.store(0, Ordering::SeqCst);
        CALLBACK_LAST_LEN.store(u32::MAX, Ordering::SeqCst);
        CALLBACK_LAST_IDX.store(u64::MAX, Ordering::SeqCst);
        CALLBACK_LAST_PARENT.store(u64::MAX, Ordering::SeqCst);
    }

    fn calls(&self) -> usize {
        CALLBACK_CALLS.load(Ordering::SeqCst)
    }

    fn last_len(&self) -> u32 {
        CALLBACK_LAST_LEN.load(Ordering::SeqCst)
    }

    fn last_idx(&self) -> u64 {
        CALLBACK_LAST_IDX.load(Ordering::SeqCst)
    }

    fn last_parent(&self) -> u64 {
        CALLBACK_LAST_PARENT.load(Ordering::SeqCst)
    }
}

fn callback_state_value(parent: u64, idx: u64, len: u32) -> u64 {
    parent
        .wrapping_add(idx)
        .wrapping_add(u64::from(len))
        .wrapping_add(TCG_STATE_BIAS)
}

extern "C" fn host_ty_callback_abi_clobber(
    out: *mut CallbackStatus,
    parent: *const u64,
    state_out: *mut u64,
    len: u32,
    idx: u64,
) {
    let parent_value = unsafe { parent.as_ref().copied().unwrap_or(0) };
    let state_value = callback_state_value(parent_value, idx, len);

    CALLBACK_CALLS.fetch_add(1, Ordering::SeqCst);
    CALLBACK_LAST_LEN.store(len, Ordering::SeqCst);
    CALLBACK_LAST_IDX.store(idx, Ordering::SeqCst);
    CALLBACK_LAST_PARENT.store(parent_value, Ordering::SeqCst);

    unsafe {
        ty_contract::clobber_call_volatile_gprs();

        if !state_out.is_null() {
            *state_out = state_value;
        }
        if !out.is_null() {
            (*out).status = STATUS_OK;
            (*out).value = CALLOUT_ENABLED;
        }
    }
}

fn store_summary_slot(fb: &mut FunctionBuilder<'_>, summary: ValueId, slot: u64, value: ValueId) {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, summary, vec![slot]);
    fb.store(Ty::U64, ptr, value);
}

fn build_callback_parent_loop_module(include_fpr_lanes: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("ty_callback_abi_call_clobber");
    let callback_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32, Ty::U64], vec![]);
    let mut entry_params = vec![Ty::U64, Ty::Ptr];
    if include_fpr_lanes {
        entry_params.push(Ty::Ptr);
    }
    entry_params.extend([Ty::Ptr, Ty::U64, Ty::Ptr, Ty::Ptr]);
    let entry_ty = mb.add_func_type(entry_params, vec![Ty::U64]);

    {
        let mut fb = mb.function(ENTRY_NAME, entry_ty);

        let entry = fb.create_block();
        let callback_raw = fb.add_block_param(entry, Ty::U64);
        let parents = fb.add_block_param(entry, Ty::Ptr);
        let fpr_lanes = include_fpr_lanes.then(|| fb.add_block_param(entry, Ty::Ptr));
        let states = fb.add_block_param(entry, Ty::Ptr);
        let parent_count = fb.add_block_param(entry, Ty::U64);
        let callout = fb.add_block_param(entry, Ty::Ptr);
        let summary = fb.add_block_param(entry, Ty::Ptr);

        let header = fb.create_block();
        let idx = fb.add_block_param(header, Ty::U64);
        let generated = fb.add_block_param(header, Ty::U64);
        let checksum = fb.add_block_param(header, Ty::U64);
        let status_sum = fb.add_block_param(header, Ty::U64);

        let body = fb.create_block();
        let done = fb.create_block();
        let done_idx = fb.add_block_param(done, Ty::U64);
        let done_generated = fb.add_block_param(done, Ty::U64);
        let done_checksum = fb.add_block_param(done, Ty::U64);
        let done_status_sum = fb.add_block_param(done, Ty::U64);

        fb.switch_to_block(entry);
        let callback_ptr = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, callback_raw);
        let zero = fb.iconst(Ty::U64, 0);
        let initial_checksum = fb.iconst(Ty::U64, i128::from(INITIAL_CHECKSUM));
        fb.br(header, vec![zero, zero, initial_checksum, zero]);

        fb.switch_to_block(header);
        let has_parent = fb.icmp(ICmpOp::Ult, Ty::U64, idx, parent_count);
        fb.condbr(
            has_parent,
            body,
            vec![],
            done,
            vec![idx, generated, checksum, status_sum],
        );

        fb.switch_to_block(body);
        let parent_ptr = fb.gep(Ty::U64, parents, vec![idx]);
        let parent = fb.load(Ty::U64, parent_ptr);
        let state_out = fb.gep(Ty::U64, states, vec![idx]);

        let busy = fb.iconst(Ty::U8, i128::from(STATUS_RUNTIME_ERROR));
        fb.store(Ty::U8, callout, busy);
        let one_slot = fb.iconst(Ty::U64, 1);
        let value_ptr = fb.gep(Ty::U64, callout, vec![one_slot]);
        let zero_value = fb.iconst(Ty::U64, 0);
        fb.store(Ty::U64, value_ptr, zero_value);

        let mut live_values = Vec::new();
        for lane in 0..LIVE_LANES {
            let idx_bias = fb.iconst(Ty::U64, i128::from(lane + 3));
            let idx_term = fb.binop(BinOp::Add, Ty::U64, idx, idx_bias);
            let parent_bias = fb.iconst(Ty::U64, i128::from(lane * 5 + 7));
            let parent_term = fb.binop(BinOp::Add, Ty::U64, parent, parent_bias);
            let product = fb.binop(BinOp::Mul, Ty::U64, idx_term, parent_term);
            let generated_bias = fb.iconst(Ty::U64, i128::from(lane));
            let generated_term = fb.binop(BinOp::Add, Ty::U64, generated, generated_bias);
            let mixed = fb.binop(BinOp::Add, Ty::U64, product, checksum);
            live_values.push(fb.binop(BinOp::Add, Ty::U64, mixed, generated_term));
        }

        let mut live_f64_values = Vec::new();
        if let Some(fpr_lanes) = fpr_lanes {
            for lane in 0..FPR_LIVE_LANES {
                let lane_idx = fb.iconst(Ty::U64, i128::from(lane));
                let lane_ptr = fb.gep(Ty::F64, fpr_lanes, vec![lane_idx]);
                live_f64_values.push(fb.load(Ty::F64, lane_ptr));
            }
        }

        let one_len = fb.iconst(Ty::U32, 1);
        fb.call_indirect_void(
            callback_ptr,
            callback_ty,
            vec![callout, parent_ptr, state_out, one_len, idx],
        );

        let status = fb.load(Ty::U8, callout);
        let status_u64 = fb.zext(Ty::U8, Ty::U64, status);
        let enabled = fb.load(Ty::U64, value_ptr);
        let state_value = fb.load(Ty::U64, state_out);

        let mut live_sum = checksum;
        for (lane, live) in live_values.into_iter().enumerate() {
            let weight = fb.iconst(Ty::U64, i128::from((lane + 1) as u64));
            let weighted = fb.binop(BinOp::Mul, Ty::U64, live, weight);
            live_sum = fb.binop(BinOp::Add, Ty::U64, live_sum, weighted);
        }

        let mut fpr_live_sum = zero;
        for (lane, live) in live_f64_values.into_iter().enumerate() {
            let live_u64 = fb.cast(CastOp::Bitcast, Ty::F64, Ty::U64, live);
            let weight = fb.iconst(Ty::U64, i128::from((lane + 1) as u64));
            let weighted = fb.binop(BinOp::Mul, Ty::U64, live_u64, weight);
            fpr_live_sum = fb.binop(BinOp::Add, Ty::U64, fpr_live_sum, weighted);
        }

        let next_generated = fb.binop(BinOp::Add, Ty::U64, generated, enabled);
        let next_status_sum = fb.binop(BinOp::Add, Ty::U64, status_sum, status_u64);
        let with_state = fb.binop(BinOp::Add, Ty::U64, live_sum, state_value);
        let with_fpr_live = fb.binop(BinOp::Add, Ty::U64, with_state, fpr_live_sum);
        let with_enabled = fb.binop(BinOp::Add, Ty::U64, with_fpr_live, enabled);
        let with_generated = fb.binop(BinOp::Add, Ty::U64, with_enabled, next_generated);
        let next_checksum = fb.binop(BinOp::Add, Ty::U64, with_generated, next_status_sum);
        let one = fb.iconst(Ty::U64, 1);
        let next_idx = fb.binop(BinOp::Add, Ty::U64, idx, one);
        fb.br(
            header,
            vec![next_idx, next_generated, next_checksum, next_status_sum],
        );

        fb.switch_to_block(done);
        store_summary_slot(&mut fb, summary, 0, done_generated);
        store_summary_slot(&mut fb, summary, 1, done_checksum);
        store_summary_slot(&mut fb, summary, 2, done_status_sum);
        store_summary_slot(&mut fb, summary, 3, done_idx);
        fb.ret(vec![done_status_sum]);

        fb.build();
    }

    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn compile_to_jit(module: &trust_ir::Module, opt_level: OptLevel) -> ExecutableBuffer {
    let mut config = CompilerConfig::jit_fast(ty_contract::host_jit_target());
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|err| panic!("{opt_level:?} compile failed: {err}"))
        .buffer
}

fn prepare_callback_parent_loop(opt_level: OptLevel) -> ExecutableBuffer {
    let module = build_callback_parent_loop_module(false);
    compile_to_jit(&module, opt_level)
}

#[cfg(target_arch = "aarch64")]
fn prepare_callback_parent_loop_with_fpr_frame(opt_level: OptLevel) -> ExecutableBuffer {
    let module = build_callback_parent_loop_module(true);
    compile_to_jit(&module, opt_level)
}

fn entry_signature(include_fpr_lanes: bool) -> SymbolSignature {
    let mut params = vec![abi_i64(), abi_ptr()];
    if include_fpr_lanes {
        params.push(abi_ptr());
    }
    params.extend([abi_ptr(), abi_i64(), abi_ptr(), abi_ptr()]);
    extern_c_signature(params, vec![abi_i64()])
}

fn wrong_entry_signature(include_fpr_lanes: bool) -> SymbolSignature {
    let mut params = vec![abi_i32(), abi_ptr()];
    if include_fpr_lanes {
        params.push(abi_ptr());
    }
    params.extend([abi_ptr(), abi_i64(), abi_ptr(), abi_ptr()]);
    extern_c_signature(params, vec![abi_i64()])
}

#[cfg(target_arch = "aarch64")]
fn aarch64_callee_saved_gpr_name(reg: u8) -> Option<&'static str> {
    match reg {
        19 => Some("x19"),
        20 => Some("x20"),
        21 => Some("x21"),
        22 => Some("x22"),
        23 => Some("x23"),
        24 => Some("x24"),
        25 => Some("x25"),
        26 => Some("x26"),
        27 => Some("x27"),
        28 => Some("x28"),
        _ => None,
    }
}

#[cfg(target_arch = "aarch64")]
fn aarch64_callee_saved_fpr_name(reg: u8) -> Option<&'static str> {
    match reg {
        8 => Some("d8"),
        9 => Some("d9"),
        10 => Some("d10"),
        11 => Some("d11"),
        12 => Some("d12"),
        13 => Some("d13"),
        14 => Some("d14"),
        15 => Some("d15"),
        _ => None,
    }
}

#[cfg(target_arch = "aarch64")]
fn decode_aarch64_gpr_pair_stack_access(word: u32) -> Option<(u8, u8)> {
    let size = (word >> 30) & 0b11;
    let major = (word >> 27) & 0b111;
    let vector = (word >> 26) & 0b1;
    let mode = (word >> 23) & 0b111;
    let base = ((word >> 5) & 0b1_1111) as u8;

    if size != 0b10 || major != 0b101 || vector != 0 || !(0b001..=0b011).contains(&mode) {
        return None;
    }
    if base != 31 {
        return None;
    }

    let rt = (word & 0b1_1111) as u8;
    let rt2 = ((word >> 10) & 0b1_1111) as u8;
    Some((rt, rt2))
}

#[cfg(target_arch = "aarch64")]
fn decode_aarch64_dpr_pair_stack_access(word: u32) -> Option<(u8, u8)> {
    let size = (word >> 30) & 0b11;
    let major = (word >> 27) & 0b111;
    let vector = (word >> 26) & 0b1;
    let mode = (word >> 23) & 0b111;
    let base = ((word >> 5) & 0b1_1111) as u8;

    if size != 0b01 || major != 0b101 || vector != 1 || !(0b001..=0b011).contains(&mode) {
        return None;
    }
    if base != 31 {
        return None;
    }

    let rt = (word & 0b1_1111) as u8;
    let rt2 = ((word >> 10) & 0b1_1111) as u8;
    Some((rt, rt2))
}

#[cfg(target_arch = "aarch64")]
fn entry_code(buffer: &ExecutableBuffer) -> &[u8] {
    let entry_offset = buffer
        .symbols()
        .find_map(|(name, offset)| (name == ENTRY_NAME).then_some(offset))
        .expect("entry symbol should exist");
    let code_len = buffer
        .symbols()
        .filter_map(|(_name, offset)| (offset > entry_offset).then_some(offset - entry_offset))
        .min()
        .unwrap_or_else(|| buffer.allocated_size() as u64 - entry_offset)
        as usize;
    let code_ptr = buffer
        .get_fn_ptr_bound(ENTRY_NAME)
        .expect("entry symbol should exist")
        .as_ptr();
    unsafe { std::slice::from_raw_parts(code_ptr, code_len) }
}

#[cfg(target_arch = "aarch64")]
fn extract_used_aarch64_callee_saved_gprs(buffer: &ExecutableBuffer) -> Vec<&'static str> {
    let code = entry_code(buffer);
    let mut regs = BTreeSet::new();
    for inst in code.as_chunks::<4>().0 {
        let word = u32::from_le_bytes(*inst);
        if let Some((rt, rt2)) = decode_aarch64_gpr_pair_stack_access(word) {
            if let Some(name) = aarch64_callee_saved_gpr_name(rt) {
                regs.insert(name);
            }
            if let Some(name) = aarch64_callee_saved_gpr_name(rt2) {
                regs.insert(name);
            }
        }
    }
    regs.into_iter().collect()
}

#[cfg(target_arch = "aarch64")]
fn extract_used_aarch64_callee_saved_fprs(buffer: &ExecutableBuffer) -> Vec<&'static str> {
    let code = entry_code(buffer);
    let mut regs = BTreeSet::new();
    for inst in code.as_chunks::<4>().0 {
        let word = u32::from_le_bytes(*inst);
        if let Some((rt, rt2)) = decode_aarch64_dpr_pair_stack_access(word) {
            if aarch64_callee_saved_fpr_name(rt).is_some() {
                regs.insert(rt);
            }
            if aarch64_callee_saved_fpr_name(rt2).is_some() {
                regs.insert(rt2);
            }
        }
    }
    regs.into_iter()
        .map(|reg| aarch64_callee_saved_fpr_name(reg).expect("validated callee-saved FPR"))
        .collect()
}

fn reference_run(parents: &[u64]) -> ([u64; 4], Vec<u64>) {
    let mut generated = 0_u64;
    let mut checksum = INITIAL_CHECKSUM;
    let mut status_sum = 0_u64;
    let mut states = Vec::with_capacity(parents.len());

    for (idx, &parent) in parents.iter().enumerate() {
        let idx = idx as u64;
        let mut live_sum = checksum;
        for lane in 0..LIVE_LANES {
            let live = idx
                .wrapping_add(lane + 3)
                .wrapping_mul(parent.wrapping_add(lane * 5 + 7))
                .wrapping_add(checksum)
                .wrapping_add(generated.wrapping_add(lane));
            live_sum = live_sum.wrapping_add(live.wrapping_mul(lane + 1));
        }

        let state = callback_state_value(parent, idx, 1);
        states.push(state);
        generated = generated.wrapping_add(CALLOUT_ENABLED);
        status_sum = status_sum.wrapping_add(u64::from(STATUS_OK));
        checksum = live_sum
            .wrapping_add(state)
            .wrapping_add(CALLOUT_ENABLED)
            .wrapping_add(generated)
            .wrapping_add(status_sum);
    }

    (
        [generated, checksum, status_sum, parents.len() as u64],
        states,
    )
}

fn run_at(callbacks: &CallbackObservations, opt_level: OptLevel, parents: &[u64]) -> LoopRun {
    callbacks.reset();

    let buffer = prepare_callback_parent_loop(opt_level);
    let entry: EntryFn =
        bind_ty_reducer_entry(&buffer, opt_level, ENTRY_NAME, entry_signature(false));

    let mut states = vec![u64::MAX; parents.len()];
    let mut callout = CallbackStatus::poisoned();
    let mut summary = [u64::MAX; 4];
    let status_sum = entry(
        host_ty_callback_abi_clobber as *const () as usize as u64,
        parents.as_ptr(),
        states.as_mut_ptr(),
        parents.len() as u64,
        &mut callout,
        summary.as_mut_ptr(),
    );

    assert_eq!(
        status_sum, summary[2],
        "{opt_level:?} returned status sum should match summary slot"
    );
    assert_eq!(
        callbacks.calls(),
        parents.len(),
        "{opt_level:?} should call the action once per parent"
    );
    if let Some((&last_parent, last_idx)) = parents
        .last()
        .zip(parents.len().checked_sub(1).map(|idx| idx as u64))
    {
        assert_eq!(callbacks.last_len(), 1);
        assert_eq!(callbacks.last_idx(), last_idx);
        assert_eq!(callbacks.last_parent(), last_parent);
    }

    LoopRun {
        summary,
        states,
        callout,
        calls: callbacks.calls(),
    }
}

fn assert_contract_rejection_left_native_state_untouched(
    callbacks: &CallbackObservations,
    states: &[u64],
    callout: &CallbackStatus,
    summary: &[u64; 4],
) {
    assert_eq!(callbacks.calls(), 0);
    assert!(
        states.iter().all(|&state| state == u64::MAX),
        "state output should stay poisoned when contract lookup rejects"
    );
    assert_eq!(*callout, CallbackStatus::poisoned());
    assert_eq!(*summary, [u64::MAX; 4]);
}

#[test]
fn ty_callback_contract_lookup_rejects_mismatches_before_native_writes() {
    let callbacks = CallbackObservations::acquire();

    let buffer = prepare_callback_parent_loop(OptLevel::O1);
    let signature = entry_signature(false);
    let manifest = ty_reducer_manifest(&buffer, OptLevel::O1, ENTRY_NAME, signature.clone());
    let contract = ty_reducer_lookup_contract(&manifest, ENTRY_NAME, signature.clone());

    let states = vec![u64::MAX; 2];
    let callout = CallbackStatus::poisoned();
    let summary = [u64::MAX; 4];

    let mut wrong_signature = contract.clone();
    wrong_signature.signature = wrong_entry_signature(false);
    let err = buffer
        .get_fixture_contract_symbol_bound::<EntryFn>(&manifest, &wrong_signature)
        .expect_err("wrong TY callback reducer signature must reject");
    match err {
        ArtifactContractError::SignatureMismatch { symbol, .. } => {
            assert_eq!(symbol, ENTRY_NAME);
        }
        other => panic!("expected signature mismatch, got {other:?}"),
    }
    assert_contract_rejection_left_native_state_untouched(&callbacks, &states, &callout, &summary);

    let mut wrong_layout = contract.clone();
    wrong_layout.layout_checksum = ArtifactChecksum::new(wrong_layout.layout_checksum.get() ^ 1);
    let err = buffer
        .get_fixture_contract_symbol_bound::<EntryFn>(&manifest, &wrong_layout)
        .expect_err("wrong TY callback reducer layout checksum must reject");
    match err {
        ArtifactContractError::ChecksumMismatch { component, .. } => {
            assert_eq!(component, "layout");
        }
        other => panic!("expected layout checksum mismatch, got {other:?}"),
    }
    assert_contract_rejection_left_native_state_untouched(&callbacks, &states, &callout, &summary);

    let mut missing_manifest = manifest.clone();
    missing_manifest.symbols.clear();
    let missing_contract =
        ty_reducer_lookup_contract(&missing_manifest, ENTRY_NAME, signature.clone());
    let err = buffer
        .get_fixture_contract_symbol_bound::<EntryFn>(&missing_manifest, &missing_contract)
        .expect_err("missing TY callback reducer manifest symbol must reject");
    match err {
        ArtifactContractError::SignatureMismatch { symbol, actual, .. } => {
            assert_eq!(symbol, ENTRY_NAME);
            assert!(actual.is_none());
        }
        other => panic!("expected missing-symbol signature mismatch, got {other:?}"),
    }
    assert_contract_rejection_left_native_state_untouched(&callbacks, &states, &callout, &summary);

    let null_symbol = "ty_callback_abi_parent_loop_missing_buffer_symbol";
    let null_manifest = ty_reducer_manifest_for_symbol(
        OptLevel::O1,
        null_symbol,
        signature,
        0,
        0,
        buffer.allocated_size() as u64,
    );
    let null_contract =
        ty_reducer_lookup_contract(&null_manifest, null_symbol, entry_signature(false));
    let err = buffer
        .get_fixture_contract_symbol_bound::<EntryFn>(&null_manifest, &null_contract)
        .expect_err("null TY callback reducer buffer symbol pointer must reject");
    match err {
        ArtifactContractError::NullSymbolPointer { symbol } => {
            assert_eq!(symbol, null_symbol);
        }
        other => panic!("expected null symbol pointer, got {other:?}"),
    }
    assert_contract_rejection_left_native_state_untouched(&callbacks, &states, &callout, &summary);
}

// AArch64 machine-code evidence: pins the exact AAPCS64 callee-saved GPR
// (x19-x28) and lower-64 FPR (d8-d15) frame the JIT emits under live-lane
// pressure. It has no x86-64 twin yet: SysV AMD64 preserves rbx/rbp/r12-r15
// only and has no callee-saved XMM registers, so the FPR half needs a
// stack-spill oracle rather than a register-frame decoder.
#[cfg(target_arch = "aarch64")]
#[test]
fn ty_callback_live_values_force_aarch64_callee_save_frame_o1_o3() {
    for (opt_level, expected) in [
        (
            OptLevel::O1,
            [
                "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28",
            ],
        ),
        (
            OptLevel::O3,
            [
                "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28",
            ],
        ),
    ] {
        let buffer = prepare_callback_parent_loop_with_fpr_frame(opt_level);
        let used = extract_used_aarch64_callee_saved_gprs(&buffer);
        assert!(
            !used.is_empty(),
            "{opt_level:?} should force callee-saved GPR pressure with {LIVE_LANES} live lanes"
        );
        assert_eq!(
            used,
            Vec::from(expected),
            "{opt_level:?} callee-saved GPR pressure changed"
        );

        let used_fprs = extract_used_aarch64_callee_saved_fprs(&buffer);
        assert!(
            !used_fprs.is_empty(),
            "{opt_level:?} should force lower-64 FPR callee-save pressure with {FPR_LIVE_LANES} F64 live-across-callback lanes"
        );
        assert_eq!(
            used_fprs,
            Vec::from(["d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"]),
            "{opt_level:?} lower-64 FPR callee-save frame evidence changed"
        );
    }
}

#[test]
fn ty_indirect_callback_abi_and_call_clobbers_match_o1_o3() {
    let callbacks = CallbackObservations::acquire();
    for parents in [&[][..], &[2, 5, 11][..]] {
        let (expected_summary, expected_states) = reference_run(parents);
        for opt_level in [OptLevel::O1, OptLevel::O3] {
            let run = run_at(&callbacks, opt_level, parents);
            assert_eq!(
                run.summary, expected_summary,
                "{opt_level:?} summary diverged for parents={parents:?}"
            );
            assert_eq!(
                run.states, expected_states,
                "{opt_level:?} callback state writes diverged for parents={parents:?}"
            );
            assert_eq!(run.calls, parents.len());
            if parents.is_empty() {
                assert_eq!(run.callout, CallbackStatus::poisoned());
            } else {
                assert_eq!(run.callout.status, STATUS_OK);
                assert_eq!(run.callout.value, CALLOUT_ENABLED);
            }
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
