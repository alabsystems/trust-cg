// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! U10 prologue stack-limit check: encoded words and emulated execution
//! (`docs/u10-prologue-stack-limit.md` §3-§4, §9).
//!
//! Real frames go through frame insertion, branch resolution and the
//! encoder (with its decode check). The check's words are compared with
//! words written here from the Arm ARM, independently of the encoder, and
//! the `[TCG-A64-STACK-LIMIT]` net certifies each lowered function. The
//! stack-touch emulator then runs each frame with `S − L` around the checked
//! total: a passing call touches nothing below `L`, and an overflowing call
//! leaves through the handler tail call with SP, LR, X0-X7 and X19-X29 as
//! they were at entry, having written only its callee-saved area. Executable
//! evidence for the listed inputs, not a proof over all frames.

#[path = "common/stack_probe_emulator.rs"]
mod emulator;

use emulator::{ENTRY_SP, Exit, Exits};
use trust_cg_codegen::frame::{self, FrameLayout};
use trust_cg_codegen::pipeline;
use trust_cg_ir::function::{
    EhCallSiteEntry, MachFunction, MachStackLimit, Signature, StackLimitOverflow,
    StackLimitRequest, StackLimitSource, StackProtectorMode, StackSlot,
};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{X0, X1, X2, X3, X4, X5, X6, X7, X16};
use trust_cg_ir::types::BlockId;
use trust_cg_verify::aarch64_stack_limit::{StackLimitOutcome, check};

const MIB: u32 = 1 << 20;

/// `ldr x17, [x0, #off]` (LDR immediate, unsigned offset, 64-bit).
fn ldr_x17_x0(offset: u32) -> u32 {
    0xF940_0000 | ((offset / 8) << 10) | 17
}
/// `subs x16, sp, x17` / `cmp sp, x17` (SUBS extended register, UXTX).
const SUBS_X16_SP_X17: u32 = 0xEB31_63F0;
const CMP_SP_X17: u32 = 0xEB31_63FF;
/// `subs x16, sp, x0` (Value source in X0).
const SUBS_X16_SP_X0: u32 = 0xEB20_63F0;
/// `cmp x16, x17` (SUBS XZR, X16, X17, shifted register).
const CMP_X16_X17: u32 = 0xEB11_021F;
/// `brk #0x534c`.
const BRK_STACK_LIMIT: u32 = 0xD420_0000 | (0x534C << 5);

fn cmp_x16_imm(imm: u32) -> u32 {
    0xF100_021F | (imm << 10)
}

fn b_lo(word: u32) -> bool {
    word & 0xFF00_001F == 0x5400_0003
}

fn limit(source: StackLimitSource, overflow: StackLimitOverflow) -> MachStackLimit {
    MachStackLimit {
        request: StackLimitRequest {
            param: 0,
            source,
            overflow,
        },
        limit_reg: X0,
        arg_regs: vec![X0, X1, X2, X3, X4, X5, X6, X7],
    }
}

fn handler() -> StackLimitOverflow {
    StackLimitOverflow::Handler {
        symbol: "on_overflow".to_string(),
    }
}

/// A frame of `local` bytes below the 16-byte frame record, requesting a
/// check; lowered, branch-resolved and encoded.
fn lowered(local: u32, limit: MachStackLimit) -> (MachFunction, FrameLayout, Vec<u8>) {
    let mut func = MachFunction::new(format!("requester_{local}"), Signature::new(vec![], vec![]));
    if local > 0 {
        func.alloc_stack_slot(StackSlot::new(local, 16));
    }
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, ret);
    func.stack_limit = Some(limit);
    let layout = frame::compute_frame_layout(&func, 0, false);
    assert_eq!(layout.callee_saved_area_size, 16);
    assert_eq!(layout.sp_adjustment(), local);
    frame::insert_prologue_epilogue(&mut func, &layout).expect("frame insertion");
    pipeline::resolve_branches(&mut func).expect("branch resolution");
    let code = pipeline::encode_function(&func).expect("encoding with decode-check");
    (func, layout, code)
}

fn words(code: &[u8]) -> Vec<u32> {
    let (chunks, rest) = code.as_chunks::<4>();
    assert!(rest.is_empty(), "AArch64 code is a whole number of words");
    chunks.iter().map(|w| u32::from_le_bytes(*w)).collect()
}

const LOCALS: [u32; 7] = [
    0,
    32,
    4080,
    4096,
    64 * 1024,
    5 * 4096, // probe loop
    MIB + MIB / 2 + 16,
];

#[test]
fn the_check_words_follow_the_frame_record_for_every_frame_size() {
    for local in LOCALS {
        for source in [
            StackLimitSource::Pointee { offset: 24 },
            StackLimitSource::Value,
        ] {
            let (func, layout, code) = lowered(local, limit(source, handler()));
            let words = words(&code);
            // stp x29, x30, [sp, #-16]!; mov x29, sp
            assert_eq!(&words[..2], &[0xA9BF_7BFD, 0x9100_03FD], "{local}");
            let mut at = 2;
            if let StackLimitSource::Pointee { offset } = source {
                assert_eq!(words[at], ldr_x17_x0(u32::from(offset)), "{local}");
                at += 1;
            }
            let sp_adj = layout.sp_adjustment();
            let subtrahend_x0 = source == StackLimitSource::Value;
            match (sp_adj, subtrahend_x0) {
                (0, false) => assert_eq!(words[at], CMP_SP_X17, "{local}"),
                (0, true) => assert_eq!(words[at], 0xEB20_63FF, "{local}"),
                (_, false) => assert_eq!(words[at], SUBS_X16_SP_X17, "{local}"),
                (_, true) => assert_eq!(words[at], SUBS_X16_SP_X0, "{local}"),
            }
            assert!(b_lo(words[at + 1]), "{local}: {:#010x}", words[at + 1]);
            at += 2;
            if sp_adj > 0 {
                if sp_adj <= 4095 {
                    assert_eq!(words[at], cmp_x16_imm(sp_adj), "{local}");
                    at += 1;
                } else {
                    // movz x17, #lo16 [, movk x17, #hi16, lsl #16]
                    assert_eq!(words[at], 0xD280_0011 | ((sp_adj & 0xFFFF) << 5), "{local}");
                    at += 1;
                    if sp_adj >> 16 != 0 {
                        assert_eq!(words[at], 0xF2A0_0011 | ((sp_adj >> 16) << 5), "{local}");
                        at += 1;
                    }
                    assert_eq!(words[at], CMP_X16_X17, "{local}");
                    at += 1;
                }
                assert!(b_lo(words[at]), "{local}");
            }
            // The net certifies the lowered function with the exact total.
            let certificate = check(&func).unwrap().unwrap();
            let StackLimitOutcome::Checked(checked) = certificate.outcome else {
                panic!("{local}: expected a present check");
            };
            assert_eq!((checked.csa, checked.total), (16, 16 + local), "{local}");
        }
    }
}

#[test]
fn a_trap_overflow_is_one_brk_with_the_frame_intact() {
    let (_, _, code) = lowered(32, limit(StackLimitSource::Value, StackLimitOverflow::Trap));
    let words = words(&code);
    assert_eq!(words.last().copied(), Some(BRK_STACK_LIMIT));
}

/// Run `code` with `x0 = L` and distinct values in X1-X28.
fn run(code: &[u8], l: u64) -> emulator::Run {
    let mut registers = [0u64; 31];
    for (index, value) in registers.iter_mut().enumerate() {
        *value = 0x1000 + index as u64;
    }
    registers[0] = l;
    emulator::run_with_exits(
        code,
        registers,
        Exits {
            tail_call: true,
            trap: true,
        },
    )
    .unwrap_or_else(|error| panic!("L {l:#x}: {error}"))
}

#[test]
fn passing_calls_stay_above_the_limit_and_overflows_reach_the_handler_intact() {
    for local in LOCALS {
        let (_, layout, code) = lowered(local, limit(StackLimitSource::Value, handler()));
        let total = u64::from(layout.total_frame_size);
        let cases = [
            ENTRY_SP - total - 1, // pass, one byte to spare
            ENTRY_SP - total,     // pass exactly
            ENTRY_SP - total + 1, // overflow by one
            ENTRY_SP,             // S − L = 0
            ENTRY_SP + 16,        // S < L
            ENTRY_SP - 16,        // S − L below the frame
            0,                    // no limit
        ];
        for l in cases {
            let result = run(&code, l);
            let fits = ENTRY_SP
                .checked_sub(total)
                .is_some_and(|bottom| bottom >= l);
            if fits {
                assert_eq!(result.exit, Exit::Ret, "{local}: L {l:#x}");
                assert!(result.min_sp >= l, "{local}: SP went below L");
                assert!(result.lowest_touch >= l, "{local}: a store below L");
            } else {
                assert_eq!(result.exit, Exit::TailCall, "{local}: L {l:#x}");
                // Only the frame record was written, and every argument and
                // callee-saved register is the entry value.
                assert_eq!(result.lowest_touch, ENTRY_SP - 16, "{local}: L {l:#x}");
                assert_eq!(result.registers[0], l);
                // X1-X7, the indirect-result register X8, and X19-X28.
                for index in (1..=8).chain(19..=28) {
                    assert_eq!(
                        result.registers[index],
                        0x1000 + index as u64,
                        "{local}: x{index} at the handler"
                    );
                }
            }
        }
    }
}

#[test]
fn a_trap_overflow_stops_with_the_frame_record_saved() {
    let (_, _, code) = lowered(
        4096,
        limit(StackLimitSource::Value, StackLimitOverflow::Trap),
    );
    let result = run(&code, ENTRY_SP);
    assert_eq!(result.exit, Exit::Trap(0x534C));
    assert_eq!(result.lowest_touch, ENTRY_SP - 16);
    let result = run(&code, 0);
    assert_eq!(result.exit, Exit::Ret);
}

#[test]
fn a_dynamic_allocation_is_refused_before_any_edit() {
    let mut func = MachFunction::new("dynamic".to_string(), Signature::new(vec![], vec![]));
    for inst in [
        MachInst::new(
            AArch64Opcode::StackAlloc,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(1),
                MachOperand::Imm(16),
            ],
        ),
        MachInst::new(AArch64Opcode::Ret, vec![]),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(func.entry, id);
    }
    func.stack_limit = Some(limit(StackLimitSource::Value, handler()));
    let layout = frame::compute_frame_layout(&func, 0, false);
    let before = func.clone();
    let error = frame::insert_prologue_epilogue(&mut func, &layout).unwrap_err();
    assert!(
        error.to_string().contains("[TCG-A64-STACK-LIMIT]"),
        "{error}"
    );
    assert_eq!(func.insts.len(), before.insts.len(), "no edit on refusal");
}

/// The frame net's diagnostic switch does not reach the stack-limit net: with
/// `TCG_AARCH64_POST_RA_SPILL_SLOTS=off`, a check whose frame compare is 16
/// bytes short is still refused at encoding.
#[test]
fn the_spill_slot_switch_does_not_turn_the_stack_limit_net_off() {
    let (mut func, _, _) = lowered(32, limit(StackLimitSource::Value, handler()));
    let compare = func
        .insts
        .iter_mut()
        .find(|inst| {
            inst.opcode == AArch64Opcode::CmpRI
                && inst.operands.first() == Some(&MachOperand::PReg(X16))
        })
        .expect("the frame compare");
    compare.operands[1] = MachOperand::Imm(16);
    let error = trust_cg_codegen::env_lock::with_env_overrides(
        &[("TCG_AARCH64_POST_RA_SPILL_SLOTS", "off")],
        || pipeline::encode_function(&func).map_err(Box::new),
    )
    .expect_err("a short total is refused whatever the frame net's mode");
    assert!(
        error.to_string().contains("[TCG-A64-STACK-LIMIT]"),
        "{error}"
    );
}

/// A stack protector and a stack limit on one function: the canary is stored
/// after the check, and the overflow block neither reads it nor calls
/// `__stack_chk_fail`.
#[test]
fn protector_and_stack_limit_compose() {
    let mut func = MachFunction::new("protected".to_string(), Signature::new(vec![], vec![]));
    func.alloc_stack_slot(StackSlot::new(64, 16));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, ret);
    func.stack_protector = StackProtectorMode::StackGuard;
    frame::ensure_stack_protector_slot(&mut func).unwrap();
    func.stack_limit = Some(limit(StackLimitSource::Pointee { offset: 0 }, handler()));
    let layout = frame::compute_frame_layout(&func, 0, false);
    frame::insert_prologue_epilogue(&mut func, &layout).expect("frame insertion");
    let overflow = func.stack_limit_overflow_block.expect("overflow block");
    let overflow_ops: Vec<_> = func.blocks[overflow.0 as usize]
        .insts
        .iter()
        .map(|id| func.insts[id.0 as usize].opcode)
        .collect();
    assert_eq!(
        overflow_ops,
        vec![AArch64Opcode::LdpPostIndex, AArch64Opcode::TailCall],
        "the overflow path restores the frame record and leaves"
    );
    let certificate = check(&func).unwrap().unwrap();
    let StackLimitOutcome::Checked(checked) = certificate.outcome else {
        panic!("expected a present check");
    };
    assert_eq!(checked.total, layout.total_frame_size);
    pipeline::resolve_branches(&mut func).expect("branch resolution");
    pipeline::encode_function(&func).expect("encoding");
}

/// A branch back to the original entry gets a one-time entry for the frame
/// setup, and the check lives there, run once.
#[test]
fn an_entry_that_is_a_branch_target_gets_a_one_time_entry() {
    let mut func = MachFunction::new("looping".to_string(), Signature::new(vec![], vec![]));
    func.alloc_stack_slot(StackSlot::new(32, 16));
    let exit = func.create_block();
    let original = func.entry;
    // entry: cbnz x1, exit; b entry  (a loop on the entry block)
    let cbz = func.push_inst(MachInst::new(
        AArch64Opcode::Cbnz,
        vec![MachOperand::PReg(X1), MachOperand::Block(exit)],
    ));
    let back = func.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(original)],
    ));
    func.append_inst(original, cbz);
    func.append_inst(original, back);
    func.add_edge(original, exit);
    func.add_edge(original, original);
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(exit, ret);
    func.stack_limit = Some(limit(StackLimitSource::Value, handler()));
    let layout = frame::compute_frame_layout(&func, 0, false);
    frame::insert_prologue_epilogue(&mut func, &layout).expect("frame insertion");
    assert_ne!(func.entry, original, "a one-time entry holds the prologue");
    let certificate = check(&func).unwrap().unwrap();
    assert!(matches!(certificate.outcome, StackLimitOutcome::Checked(_)));
    pipeline::resolve_branches(&mut func).expect("branch resolution");
    let code = pipeline::encode_function(&func).expect("encoding");
    // x1 != 0 leaves the loop at once; a passing limit returns, a failing
    // one reaches the handler.
    let total = u64::from(layout.total_frame_size);
    assert_eq!(run(&code, ENTRY_SP - total).exit, Exit::Ret);
    assert_eq!(run(&code, ENTRY_SP).exit, Exit::TailCall);
}

/// An EH-protected call in the entry block moves with its call when the
/// entry is split after the check, and keeps its landing-pad edge.
#[test]
fn an_eh_call_site_in_the_entry_moves_with_its_call() {
    let mut func = MachFunction::new("eh".to_string(), Signature::new(vec![], vec![]));
    func.eh_metadata.personality = Some("__gxx_personality_v0".into());
    func.alloc_stack_slot(StackSlot::new(32, 16));
    let pad = func.create_block();
    let call = func.push_inst(MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("may_throw".into())],
    ));
    let done = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, call);
    func.append_inst(func.entry, done);
    let pad_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(pad, pad_ret);
    func.add_edge(func.entry, pad);
    func.eh_metadata.call_sites.push(EhCallSiteEntry {
        call_block: func.entry,
        start_offset: 0,
        length: 0,
        landing_pad_block: Some(pad),
    });
    func.stack_limit = Some(limit(StackLimitSource::Value, handler()));
    let layout = frame::compute_frame_layout(&func, 0, false);
    frame::insert_prologue_epilogue(&mut func, &layout).expect("frame insertion");
    let site = func.eh_metadata.call_sites[0].call_block;
    assert_ne!(site, func.entry, "the call site left the check's block");
    assert!(func.blocks[site.0 as usize].insts.contains(&call));
    assert!(func.blocks[site.0 as usize].succs.contains(&pad));
    assert!(!func.blocks[func.entry.0 as usize].succs.contains(&pad));
    let certificate = check(&func).unwrap().unwrap();
    assert!(matches!(certificate.outcome, StackLimitOutcome::Checked(_)));
    let _ = BlockId(0);
}
