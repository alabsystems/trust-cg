// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Producer candidate selection only. The verifier independently checks the
//! selected words/operands and relative regions, without body/proof authority.

use trust_cg_codegen::frame::{self, FrameLayout};
use trust_cg_ir::{AArch64Opcode, InstId, MachFunction};
use trust_cg_verify::aarch64_static_frame::{
    SavedFrameRegister, StaticFrameEnvelopeCandidates, StaticFrameLayoutClaim,
};

pub fn claim(machine: &MachFunction, layout: &FrameLayout) -> StaticFrameLayoutClaim {
    let register = |reg: trust_cg_ir::PReg, fpr: bool| {
        if fpr {
            let index = match reg.encoding() {
                64..=95 => reg.encoding() - 64,
                96..=127 => reg.encoding() - 96,
                _ => panic!("unsupported frame register"),
            };
            SavedFrameRegister::D(index as u8)
        } else {
            SavedFrameRegister::X(reg.encoding() as u8)
        }
    };
    StaticFrameLayoutClaim {
        saved_pairs: layout
            .callee_saved_pairs
            .iter()
            .map(|pair| {
                [
                    register(pair.reg1, pair.is_fpr),
                    register(pair.reg2, pair.is_fpr),
                ]
            })
            .collect(),
        callee_saved_bytes: layout.callee_saved_area_size,
        stack_slot_bytes: layout
            .spill_area_size
            .checked_add(layout.local_area_size)
            .unwrap(),
        outgoing_argument_bytes: layout.outgoing_arg_area_size,
        total_bytes: layout.total_frame_size,
        uses_frame_pointer: layout.uses_frame_pointer,
        dynamic_allocation: layout.has_dynamic_alloc,
        red_zone: layout.uses_red_zone,
        slot_fp_offsets: frame::stack_slot_frame_offsets(machine, layout),
    }
}

pub fn candidates(machine: &MachFunction, layout: &FrameLayout) -> StaticFrameEnvelopeCandidates {
    let real = |block: trust_cg_ir::BlockId| -> Vec<InstId> {
        machine.blocks[block.0 as usize]
            .insts
            .iter()
            .copied()
            .filter(|id| !machine.insts[id.0 as usize].is_pseudo())
            .collect()
    };
    let prologue_len = frame::emit_prologue(layout).len();
    let epilogue_len = frame::emit_epilogue(layout).len();
    StaticFrameEnvelopeCandidates {
        prologue: real(machine.entry)[..prologue_len].to_vec(),
        epilogues: machine
            .block_order
            .iter()
            .filter_map(|&block| {
                let row = real(block);
                row.last()
                    .filter(|id| machine.insts[id.0 as usize].opcode == AArch64Opcode::Ret)
                    .map(|_| row[row.len() - epilogue_len..].to_vec())
            })
            .collect(),
    }
}
