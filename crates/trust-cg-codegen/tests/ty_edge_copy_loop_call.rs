// Regression for TY-shaped loop-carried block args across indirect calls.
//
// The reducer splits each parent-loop iteration through two duplicate-looking
// edges, joins at an indirect call, then uses a latch backedge that swaps and
// duplicates loop-carried values.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, ExecutableBuffer, Target};
use trust_ir::{BinOp, CastOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

#[path = "common/ty_contract.rs"]
mod ty_contract;

use ty_contract::{abi_i64, abi_ptr, bind_ty_reducer_entry, extern_c_signature};

const ENTRY_NAME: &str = "ty_edge_copy_parent_loop";
const INITIAL_LEFT: u64 = 0x11;
const INITIAL_RIGHT: u64 = 0x29;
const INITIAL_SHADOW: u64 = 0x43;
const INITIAL_CHECKSUM: u64 = 0x5f;
const TCG_CALLBACK_BIAS: u64 = 97;
const SUMMARY_SLOTS: usize = 8;

type EntryFn = extern "C" fn(u64, *const u64, *mut u64, u64, *mut u64) -> u64;

static CALLBACK_CALLS: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Debug, PartialEq, Eq)]
struct EdgeCopyRun {
    summary: [u64; SUMMARY_SLOTS],
    scratch: Vec<u64>,
    calls: usize,
}

fn callback_value(parent: u64, idx: u64, lhs: u64, rhs: u64, alias: u64) -> u64 {
    parent
        .wrapping_mul(17)
        .wrapping_add(idx.wrapping_mul(31))
        .wrapping_add(lhs ^ rhs)
        .wrapping_add(alias.wrapping_mul(3))
        .wrapping_add(TCG_CALLBACK_BIAS)
}

extern "C" fn host_ty_edge_copy_call(
    out: *mut u64,
    parent: u64,
    idx: u64,
    lhs: u64,
    rhs: u64,
    alias: u64,
) -> u64 {
    let value = callback_value(parent, idx, lhs, rhs, alias);
    CALLBACK_CALLS.fetch_add(1, Ordering::SeqCst);

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

        if !out.is_null() {
            *out = value;
        }
    }

    value
}

fn store_summary_slot(fb: &mut FunctionBuilder<'_>, summary: ValueId, slot: u64, value: ValueId) {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, summary, vec![slot]);
    fb.store(Ty::U64, ptr, value);
}

fn build_edge_copy_parent_loop_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("ty_edge_copy_loop_call");
    let callback_ty = mb.add_func_type(
        vec![Ty::Ptr, Ty::U64, Ty::U64, Ty::U64, Ty::U64, Ty::U64],
        vec![Ty::U64],
    );
    let entry_ty = mb.add_func_type(
        vec![Ty::U64, Ty::Ptr, Ty::Ptr, Ty::U64, Ty::Ptr],
        vec![Ty::U64],
    );

    {
        let mut fb = mb.function(ENTRY_NAME, entry_ty);

        let entry = fb.create_block();
        let callback_raw = fb.add_block_param(entry, Ty::U64);
        let parents = fb.add_block_param(entry, Ty::Ptr);
        let scratch = fb.add_block_param(entry, Ty::Ptr);
        let parent_count = fb.add_block_param(entry, Ty::U64);
        let summary = fb.add_block_param(entry, Ty::Ptr);

        let header = fb.create_block();
        let idx = fb.add_block_param(header, Ty::U64);
        let left = fb.add_block_param(header, Ty::U64);
        let right = fb.add_block_param(header, Ty::U64);
        let shadow = fb.add_block_param(header, Ty::U64);
        let checksum = fb.add_block_param(header, Ty::U64);
        let last_parent = fb.add_block_param(header, Ty::U64);
        let status = fb.add_block_param(header, Ty::U64);

        let body = fb.create_block();
        let even_edge = fb.create_block();
        let odd_edge = fb.create_block();

        let call_block = fb.create_block();
        let call_idx = fb.add_block_param(call_block, Ty::U64);
        let call_parent = fb.add_block_param(call_block, Ty::U64);
        let call_slot = fb.add_block_param(call_block, Ty::Ptr);
        let call_lhs = fb.add_block_param(call_block, Ty::U64);
        let call_rhs = fb.add_block_param(call_block, Ty::U64);
        let call_alias = fb.add_block_param(call_block, Ty::U64);
        let call_checksum = fb.add_block_param(call_block, Ty::U64);
        let call_status = fb.add_block_param(call_block, Ty::U64);

        let latch = fb.create_block();
        let latch_idx = fb.add_block_param(latch, Ty::U64);
        let latch_left = fb.add_block_param(latch, Ty::U64);
        let latch_right = fb.add_block_param(latch, Ty::U64);
        let latch_shadow = fb.add_block_param(latch, Ty::U64);
        let latch_checksum = fb.add_block_param(latch, Ty::U64);
        let latch_parent = fb.add_block_param(latch, Ty::U64);
        let latch_status = fb.add_block_param(latch, Ty::U64);

        let done = fb.create_block();
        let done_idx = fb.add_block_param(done, Ty::U64);
        let done_left = fb.add_block_param(done, Ty::U64);
        let done_right = fb.add_block_param(done, Ty::U64);
        let done_shadow = fb.add_block_param(done, Ty::U64);
        let done_checksum = fb.add_block_param(done, Ty::U64);
        let done_parent = fb.add_block_param(done, Ty::U64);
        let done_status = fb.add_block_param(done, Ty::U64);

        fb.switch_to_block(entry);
        let callback_ptr = fb.cast(
            CastOp::IntToPtr,
            Ty::U64,
            Ty::Func(callback_ty),
            callback_raw,
        );
        let zero = fb.iconst(Ty::U64, 0);
        let initial_left = fb.iconst(Ty::U64, i128::from(INITIAL_LEFT));
        let initial_right = fb.iconst(Ty::U64, i128::from(INITIAL_RIGHT));
        let initial_shadow = fb.iconst(Ty::U64, i128::from(INITIAL_SHADOW));
        let initial_checksum = fb.iconst(Ty::U64, i128::from(INITIAL_CHECKSUM));
        fb.br(
            header,
            vec![
                zero,
                initial_left,
                initial_right,
                initial_shadow,
                initial_checksum,
                zero,
                zero,
            ],
        );

        fb.switch_to_block(header);
        let has_parent = fb.icmp(ICmpOp::Ult, Ty::U64, idx, parent_count);
        fb.condbr(
            has_parent,
            body,
            vec![],
            done,
            vec![idx, left, right, shadow, checksum, last_parent, status],
        );

        fb.switch_to_block(body);
        let parent_ptr = fb.gep(Ty::U64, parents, vec![idx]);
        let parent = fb.load(Ty::U64, parent_ptr);
        let scratch_slot = fb.gep(Ty::U64, scratch, vec![idx]);
        let one = fb.iconst(Ty::U64, 1);
        let parent_low_bit = fb.binop(BinOp::And, Ty::U64, parent, one);
        let zero_cmp = fb.iconst(Ty::U64, 0);
        let is_odd = fb.icmp(ICmpOp::Ne, Ty::U64, parent_low_bit, zero_cmp);
        let left_plus_parent = fb.binop(BinOp::Add, Ty::U64, left, parent);
        let right_plus_idx = fb.binop(BinOp::Add, Ty::U64, right, idx);
        let pair_sum = fb.binop(BinOp::Add, Ty::U64, left_plus_parent, right_plus_idx);
        let edge_checksum = fb.binop(BinOp::Add, Ty::U64, checksum, pair_sum);
        fb.condbr(is_odd, odd_edge, vec![], even_edge, vec![]);

        fb.switch_to_block(even_edge);
        fb.br(
            call_block,
            vec![
                idx,
                parent,
                scratch_slot,
                left_plus_parent,
                right_plus_idx,
                left_plus_parent,
                edge_checksum,
                status,
            ],
        );

        fb.switch_to_block(odd_edge);
        fb.br(
            call_block,
            vec![
                idx,
                parent,
                scratch_slot,
                right_plus_idx,
                left_plus_parent,
                right_plus_idx,
                edge_checksum,
                status,
            ],
        );

        fb.switch_to_block(call_block);
        let returned = fb.call_indirect(
            callback_ptr,
            callback_ty,
            vec![
                call_slot,
                call_parent,
                call_idx,
                call_lhs,
                call_rhs,
                call_alias,
            ],
        );
        let stored = fb.load(Ty::U64, call_slot);
        let call_delta = fb.binop(BinOp::Xor, Ty::U64, returned, stored);
        let next_status = fb.binop(BinOp::Add, Ty::U64, call_status, call_delta);
        let two_call_values = fb.binop(BinOp::Add, Ty::U64, returned, stored);
        let next_left = fb.binop(BinOp::Add, Ty::U64, call_lhs, two_call_values);
        let next_right = fb.binop(BinOp::Xor, Ty::U64, call_rhs, returned);
        let next_shadow = fb.binop(BinOp::Add, Ty::U64, call_alias, call_parent);
        let with_left = fb.binop(BinOp::Add, Ty::U64, call_checksum, next_left);
        let with_right = fb.binop(BinOp::Add, Ty::U64, with_left, next_right);
        let next_checksum = fb.binop(BinOp::Add, Ty::U64, with_right, next_shadow);
        let next_idx = fb.binop(BinOp::Add, Ty::U64, call_idx, one);
        fb.br(
            latch,
            vec![
                next_idx,
                next_left,
                next_right,
                next_shadow,
                next_checksum,
                call_parent,
                next_status,
            ],
        );

        fb.switch_to_block(latch);
        let rotated_checksum = fb.binop(BinOp::Add, Ty::U64, latch_checksum, latch_shadow);
        fb.br(
            header,
            vec![
                latch_idx,
                latch_right,
                latch_left,
                latch_left,
                rotated_checksum,
                latch_parent,
                latch_status,
            ],
        );

        fb.switch_to_block(done);
        store_summary_slot(&mut fb, summary, 0, done_idx);
        store_summary_slot(&mut fb, summary, 1, done_idx);
        store_summary_slot(&mut fb, summary, 2, done_parent);
        store_summary_slot(&mut fb, summary, 3, done_checksum);
        store_summary_slot(&mut fb, summary, 4, done_status);
        store_summary_slot(&mut fb, summary, 5, done_left);
        store_summary_slot(&mut fb, summary, 6, done_right);
        store_summary_slot(&mut fb, summary, 7, done_shadow);
        fb.ret(vec![done_checksum]);

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
        vec![abi_i64(), abi_ptr(), abi_ptr(), abi_i64(), abi_ptr()],
        vec![abi_i64()],
    )
}

fn run_at(opt_level: OptLevel, parents: &[u64]) -> EdgeCopyRun {
    CALLBACK_CALLS.store(0, Ordering::SeqCst);

    let module = build_edge_copy_parent_loop_module();
    let buffer = compile_to_jit(&module, opt_level);
    let entry: EntryFn = bind_ty_reducer_entry(&buffer, opt_level, ENTRY_NAME, entry_signature());

    let mut scratch = vec![u64::MAX; parents.len()];
    let mut summary = [u64::MAX; SUMMARY_SLOTS];
    let returned = entry(
        host_ty_edge_copy_call as *const () as usize as u64,
        parents.as_ptr(),
        scratch.as_mut_ptr(),
        parents.len() as u64,
        summary.as_mut_ptr(),
    );

    assert_eq!(
        returned, summary[3],
        "{opt_level:?} return/fingerprint mismatch"
    );

    EdgeCopyRun {
        summary,
        scratch,
        calls: CALLBACK_CALLS.load(Ordering::SeqCst),
    }
}

fn reference_run(parents: &[u64]) -> EdgeCopyRun {
    let mut left = INITIAL_LEFT;
    let mut right = INITIAL_RIGHT;
    let mut shadow = INITIAL_SHADOW;
    let mut checksum = INITIAL_CHECKSUM;
    let mut last_parent = 0_u64;
    let mut status = 0_u64;
    let mut scratch = vec![u64::MAX; parents.len()];

    for (idx, &parent) in parents.iter().enumerate() {
        let idx = idx as u64;
        let left_plus_parent = left.wrapping_add(parent);
        let right_plus_idx = right.wrapping_add(idx);
        let pair_sum = left_plus_parent.wrapping_add(right_plus_idx);
        let edge_checksum = checksum.wrapping_add(pair_sum);

        let (lhs, rhs, alias) = if parent & 1 == 0 {
            (left_plus_parent, right_plus_idx, left_plus_parent)
        } else {
            (right_plus_idx, left_plus_parent, right_plus_idx)
        };

        let value = callback_value(parent, idx, lhs, rhs, alias);
        scratch[idx as usize] = value;
        let call_delta = value ^ scratch[idx as usize];
        let next_status = status.wrapping_add(call_delta);
        let two_call_values = value.wrapping_add(scratch[idx as usize]);
        let next_left = lhs.wrapping_add(two_call_values);
        let next_right = rhs ^ value;
        let next_shadow = alias.wrapping_add(parent);
        let next_checksum = edge_checksum
            .wrapping_add(next_left)
            .wrapping_add(next_right)
            .wrapping_add(next_shadow);

        left = next_right;
        right = next_left;
        shadow = next_left;
        checksum = next_checksum.wrapping_add(next_shadow);
        last_parent = parent;
        status = next_status;
    }

    EdgeCopyRun {
        summary: [
            parents.len() as u64,
            parents.len() as u64,
            last_parent,
            checksum,
            status,
            left,
            right,
            shadow,
        ],
        scratch,
        calls: parents.len(),
    }
}

#[test]
fn ty_edge_copy_loop_call_block_args_match_o1_o3() {
    for parents in [&[][..], &[2, 5, 8, 13][..]] {
        let expected = reference_run(parents);
        for opt_level in [OptLevel::O1, OptLevel::O3] {
            let run = run_at(opt_level, parents);
            assert_eq!(
                run.summary, expected.summary,
                "{opt_level:?} summary diverged for parents={parents:?}"
            );
            assert_eq!(
                run.scratch, expected.scratch,
                "{opt_level:?} callback writes diverged for parents={parents:?}"
            );
            assert_eq!(
                run.calls,
                parents.len(),
                "{opt_level:?} should call the edge-copy callback once per parent"
            );
        }
    }
}
