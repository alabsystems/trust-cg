// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Independent allocated-MachIR observation for pending memory/status owners.
//! No encoder, word decoder, producer origin, frame metric or proof hint chooses
//! a value or edge. Only uniquely linked allocated instructions execute.
//! Exact harmless unlinked copy/formal-carrier NOPs and retired direct B forms
//! are admitted as arena tombstones, not execution/dataflow or authority credit.

use super::{MAX_STEPS, Profile, ReadOnlyTargetError, Step, flags, register};
use crate::aarch64_semantics as semantics;
use crate::aarch64_value_decode_proofs::cset_condition_from_encoding;
use crate::nzcv::{self, NzcvFlags};
use crate::smt::SmtExpr as E;
use crate::source_bound_frame::inert_allocated_nop;
use trust_cg_ir::cc::OperandSize;
use trust_cg_ir::{
    AArch64Opcode as M, InstId, MachFunction, MachInst, MachOperand as O, SpecialReg, Type,
};

const MAX_BLOCKS: usize = 16;
const MAX_ARENA: usize = 1024;
const MAX_VREGS: u32 = 4096;

#[cfg(test)]
#[path = "read_only_target_machine_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "read_only_target_machine_scalar_tests.rs"]
mod scalar_tests;

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "read_only_target_writer_retirement_tests.rs"]
mod writer_retirement_tests;

fn invalid(reason: &'static str) -> ReadOnlyTargetError {
    ReadOnlyTargetError::Machine(reason)
}

// Internal PReg encodings, NOT hardware register fields: X0..17, W0..17,
// explicit XZR/WZR. Register 31/SP and platform/callee-saved registers refuse.
fn carrier(operand: &O) -> Result<(Option<usize>, u32), ReadOnlyTargetError> {
    match operand {
        O::PReg(reg) => match reg.encoding() {
            index @ 0..=17 => Ok((Some(usize::from(index)), 64)),
            index @ 32..=49 => Ok((Some(usize::from(index - 32)), 32)),
            160 => Ok((None, 64)),
            161 => Ok((None, 32)),
            _ => Err(invalid("reserved or noninteger physical register")),
        },
        O::Special(SpecialReg::XZR) => Ok((None, 64)),
        O::Special(SpecialReg::WZR) => Ok((None, 32)),
        _ => Err(invalid("fully allocated caller integer carrier required")),
    }
}

fn read(operand: &O, bits: u32, typed_copy: bool) -> Result<E, ReadOnlyTargetError> {
    let (index, actual_bits) = carrier(operand)?;
    if actual_bits != bits && !(typed_copy && index.is_some()) {
        return Err(invalid("mixed register widths"));
    }
    let full = index.map_or_else(|| E::bv_const(0, 64), register);
    Ok(if bits == 32 {
        full.extract(31, 0)
    } else {
        full
    })
}

fn size(bits: u32) -> OperandSize {
    if bits == 32 {
        OperandSize::S32
    } else {
        OperandSize::S64
    }
}

fn scalar(destination: Option<usize>, bits: u32, value: E, flags: Option<NzcvFlags>) -> Step {
    Step::Scalar {
        destination,
        value: if bits == 32 {
            value.zero_ext(32)
        } else {
            value
        },
        flags: flags.map(Box::new),
    }
}

fn condition(cc: i64) -> Result<E, ReadOnlyTargetError> {
    let cc = cset_condition_from_encoding(cc).ok_or_else(|| invalid("condition outside 0..13"))?;
    Ok(nzcv::eval_condition(cc, &flags()))
}

fn plain(inst: &MachInst) -> bool {
    inst.flags == inst.opcode.default_flags()
        && inst.implicit_defs.is_empty()
        && inst.implicit_uses.is_empty()
        && inst.proof.is_none()
}

fn nop(inst: &MachInst, machine: &MachFunction) -> bool {
    if !inert_allocated_nop(inst, machine.next_vreg) || inst.proof.is_some() {
        return false;
    }
    if inst.implicit_uses.is_empty() {
        return true;
    }
    // These are the exact remaining-formal suffix markers carried by the
    // producer's entry copies. They do not execute a read or define a value.
    let params = machine.signature.params.len();
    let start = usize::from(inst.implicit_uses[0].encoding());
    start > 0
        && start < params
        && inst.implicit_uses.len() == params - start
        && inst
            .implicit_uses
            .iter()
            .enumerate()
            .all(|(i, reg)| usize::from(reg.encoding()) == start + i)
        && match inst.operands.as_slice() {
            [] => true,
            [O::PReg(a), O::PReg(b)] => a == b && usize::from(a.encoding()) + 1 == start,
            [O::VReg(_), O::PReg(b)] => usize::from(b.encoding()) + 1 == start,
            _ => false,
        }
}

fn retired_branch(inst: &MachInst, machine: &MachFunction) -> bool {
    inst.opcode == M::B
        && plain(inst)
        && match inst.operands.as_slice() {
            [O::Imm(offset)] => (-(1i64 << 25)..(1i64 << 25)).contains(offset),
            // Resolution rewrites only linked instructions. The actual O2
            // producer leaves exact removed B Block(...) tombstones behind.
            [O::Block(target)] => (target.0 as usize) < machine.blocks.len(),
            _ => false,
        }
}

struct Layout {
    linked: Vec<InstId>,
    words: Vec<i64>,
    targets: Vec<usize>,
}

fn layout(machine: &MachFunction) -> Result<Layout, ReadOnlyTargetError> {
    if machine.blocks.is_empty() || machine.block_order.is_empty() {
        return Err(invalid("empty machine control"));
    }
    if machine.blocks.len() > MAX_BLOCKS
        || machine.insts.len() > MAX_ARENA
        || machine.next_vreg > MAX_VREGS
    {
        return Err(ReadOnlyTargetError::Budget("machine arena"));
    }
    if machine.block_order.len() > machine.blocks.len()
        || machine.block_order.first() != Some(&machine.entry)
    {
        return Err(invalid("entry/layout mismatch"));
    }
    let linked_count = machine
        .blocks
        .iter()
        .try_fold(0usize, |n, block| n.checked_add(block.insts.len()))
        .ok_or(ReadOnlyTargetError::Budget("machine ownership count"))?;
    if linked_count == 0 || linked_count > MAX_STEPS {
        return Err(ReadOnlyTargetError::Budget("machine linked steps"));
    }
    let mut blocks = vec![false; machine.blocks.len()];
    let mut owned = vec![false; machine.insts.len()];
    let mut linked = Vec::with_capacity(linked_count);
    for id in &machine.block_order {
        let block = machine
            .blocks
            .get(id.0 as usize)
            .ok_or_else(|| invalid("layout block outside arena"))?;
        if std::mem::replace(&mut blocks[id.0 as usize], true)
            || block.insts.is_empty()
            || block.loop_depth != 0
        {
            return Err(invalid("duplicate/empty/loop-marked layout block"));
        }
        if block.preds.len() > MAX_BLOCKS || block.succs.len() > MAX_BLOCKS {
            return Err(ReadOnlyTargetError::Budget("machine CFG metadata"));
        }
        for edge in block.preds.iter().chain(&block.succs) {
            if (edge.0 as usize) >= machine.blocks.len() || !machine.block_order.contains(edge) {
                return Err(invalid("CFG metadata points outside layout"));
            }
        }
        for inst in &block.insts {
            let seen = owned
                .get_mut(inst.0 as usize)
                .ok_or_else(|| invalid("instruction outside arena"))?;
            if std::mem::replace(seen, true) {
                return Err(invalid("instruction has duplicate live ownership"));
            }
            linked.push(*inst);
        }
    }
    for (block, live) in machine.blocks.iter().zip(blocks) {
        if !live
            && (!block.insts.is_empty()
                || !block.preds.is_empty()
                || !block.succs.is_empty()
                || block.loop_depth != 0)
        {
            return Err(invalid("nonempty block outside layout"));
        }
    }
    for (inst, live) in machine.insts.iter().zip(owned) {
        if !live && !nop(inst, machine) && !retired_branch(inst, machine) {
            return Err(invalid("unowned non-inert instruction"));
        }
    }
    let entry_prefix = machine.blocks[machine.entry.0 as usize]
        .insts
        .iter()
        .take_while(|id| machine.insts[id.0 as usize].opcode == M::Nop)
        .count();
    let mut words = Vec::with_capacity(linked.len());
    let mut targets = Vec::with_capacity(linked.len());
    let mut word = 0i64;
    for (step, id) in linked.iter().enumerate() {
        let inst = &machine.insts[id.0 as usize];
        words.push(word);
        if inst.opcode == M::Nop {
            if !nop(inst, machine) || (!inst.implicit_uses.is_empty() && step >= entry_prefix) {
                return Err(invalid("malformed/nonentry inert copy marker"));
            }
        } else if inst.is_pseudo() {
            return Err(invalid("unsupported pseudo in allocated stream"));
        }
        // A validated IS_PSEUDO copy marker emits no word. EMPTY-flags NOP
        // emits one architectural NOP; both steps still exist in this view.
        if !inst.is_pseudo() {
            while targets.len() <= word as usize {
                targets.push(step);
            }
            word += 1;
        } else if targets.len() == word as usize {
            // Let an edge land at the first zero-byte marker preceding the
            // actual word. It defines/reads no register or flag.
            targets.push(step);
        }
    }
    targets.truncate(word as usize);
    Ok(Layout {
        linked,
        words,
        targets,
    })
}

impl Layout {
    fn target(&self, step: usize, offset: i64, bits: u32) -> Result<usize, ReadOnlyTargetError> {
        if !(-(1i64 << (bits - 1))..(1i64 << (bits - 1))).contains(&offset) {
            return Err(invalid("direct displacement outside architectural field"));
        }
        let word = self.words[step]
            .checked_add(offset)
            .and_then(|n| usize::try_from(n).ok())
            .ok_or_else(|| invalid("direct target outside word stream"))?;
        self.targets
            .get(word)
            .copied()
            .ok_or_else(|| invalid("direct target outside word stream"))
    }
}

fn instruction(inst: &MachInst, pc: usize, layout: &Layout) -> Result<Step, ReadOnlyTargetError> {
    let operands = inst.operands.as_slice();
    if inst.opcode == M::Nop {
        return Ok(Step::Inert);
    }
    if inst.opcode == M::Ret {
        if inst.flags != M::Ret.default_flags()
            || !inst.implicit_defs.is_empty()
            || inst.proof.is_some()
            || !(inst.implicit_uses.is_empty()
                || (inst.implicit_uses.len() == 1 && inst.implicit_uses[0].encoding() == 0))
            || !matches!(operands, [O::PReg(reg)] if reg.encoding() == 30)
        {
            return Err(invalid(
                "requires exact RET X30 and optional X0 result carrier",
            ));
        }
        return Ok(Step::Return);
    }
    if !plain(inst) {
        return Err(invalid("noncanonical effects/implicit operands/proof"));
    }
    match (inst.opcode, operands) {
        (M::B, [O::Imm(offset)]) => return Ok(Step::Jump(layout.target(pc, *offset, 26)?)),
        (M::BCond | M::Bcc, [O::Imm(cc), O::Imm(offset)]) => {
            return Ok(Step::Branch {
                condition: condition(*cc)?,
                taken: layout.target(pc, *offset, 19)?,
            });
        }
        (M::Cbz | M::Cbnz, [reg, O::Imm(offset)]) => {
            let (_, bits) = carrier(reg)?;
            let zero = read(reg, bits, false)?.eq_expr(E::bv_const(0, bits));
            return Ok(Step::Branch {
                condition: if inst.opcode == M::Cbnz {
                    zero.not_expr()
                } else {
                    zero
                },
                taken: layout.target(pc, *offset, 19)?,
            });
        }
        (M::LdrRI, [dst, base, O::Imm(offset)]) => {
            let (destination, 64) = carrier(dst)? else {
                return Err(invalid("requires 64-bit X load destination"));
            };
            let (Some(_), 64) = carrier(base)? else {
                return Err(invalid("load base must be ordinary X, not SP/ZR"));
            };
            if !(-256..=255).contains(offset) && !(0..=32760).contains(offset) {
                return Err(invalid("load displacement not emittable"));
            }
            if !(-256..=255).contains(offset) && offset % 8 != 0 {
                return Err(invalid("load immediate scale"));
            }
            return Ok(Step::Load {
                // XZR discards only the value, NOT the observed read demand.
                destination: destination.unwrap_or(31),
                address: crate::memory_proofs::qf_bv_byte_addr(
                    &read(base, 64, false)?,
                    *offset as u64,
                ),
                alignment: 1,
            });
        }
        (
            M::CmpRR | M::CmpRI | M::CMPWrr | M::CMPXrr | M::CMPWri | M::CMPXri | M::Tst,
            [left, right],
        ) => {
            let (_, bits) = carrier(left)?;
            if (matches!(inst.opcode, M::CMPWrr | M::CMPWri) && bits != 32)
                || (matches!(inst.opcode, M::CMPXrr | M::CMPXri) && bits != 64)
            {
                return Err(invalid("comparison alias width"));
            }
            let a = read(left, bits, false)?;
            let b = if matches!(inst.opcode, M::CmpRI | M::CMPWri | M::CMPXri) {
                if carrier(left)?.0.is_none() {
                    return Err(invalid("CMP immediate cannot use SP/ZR"));
                }
                let O::Imm(value @ 0..=4095) = right else {
                    return Err(invalid("CMP imm12 required"));
                };
                E::bv_const(*value as u64, bits)
            } else if inst.opcode == M::Tst && matches!(right, O::Imm(_)) {
                logical(right, bits)?
            } else {
                read(right, bits, false)?
            };
            let updated = if inst.opcode == M::Tst {
                nzcv::encode_tst(a, b, bits)
            } else {
                nzcv::encode_cmp(a, b, bits)
            };
            return Ok(scalar(None, 64, E::bv_const(0, 64), Some(updated)));
        }
        _ => {}
    }
    let dst = operands
        .first()
        .ok_or_else(|| invalid("missing scalar destination"))?;
    let (destination, view) = carrier(dst)?;
    let bits = match inst.opcode {
        M::MOVWrr => 32,
        M::MOVXrr => 64,
        _ => view,
    };
    if destination.is_none() && view != bits {
        return Err(invalid("zero-destination width"));
    }
    let operand_size = size(bits);
    let mut updated_flags = None;
    let value = match (inst.opcode, operands) {
        (M::MovR | M::MOVWrr | M::MOVXrr, [_, src]) => {
            semantics::encode_mov_rr(operand_size, read(src, bits, inst.opcode != M::MovR)?)
        }
        (M::Movz | M::Movn | M::Movk, [_, O::Imm(imm)]) => {
            move_wide(inst.opcode, dst, bits, *imm, 0)?
        }
        (M::Movz | M::Movn | M::Movk, [_, O::Imm(imm), O::Imm(shift)]) => {
            move_wide(inst.opcode, dst, bits, *imm, *shift)?
        }
        (
            M::AddRR | M::SubRR | M::MulRR | M::AndRR | M::OrrRR | M::EorRR | M::AddsRR | M::SubsRR,
            [_, left, right],
        ) => {
            let a = read(left, bits, false)?;
            let b = read(right, bits, false)?;
            match inst.opcode {
                M::AddRR => semantics::encode_add_rr(operand_size, a, b),
                M::SubRR => semantics::encode_sub_rr(operand_size, a, b),
                M::MulRR => semantics::encode_mul_rr(operand_size, a, b),
                M::AndRR => semantics::encode_and_rr(operand_size, a, b),
                M::OrrRR => semantics::encode_orr_rr(operand_size, a, b),
                M::EorRR => semantics::encode_eor_rr(operand_size, a, b),
                M::AddsRR => {
                    let (value, flags) = nzcv::encode_adds(a, b, bits);
                    updated_flags = Some(flags);
                    value
                }
                M::SubsRR => {
                    let (value, flags) = nzcv::encode_subs(a, b, bits);
                    updated_flags = Some(flags);
                    value
                }
                _ => unreachable!(),
            }
        }
        (
            M::AddRI | M::SubRI | M::AddRIShift12 | M::AddsRI | M::SubsRI,
            [_, src, O::Imm(imm @ 0..=4095)],
        ) => {
            // ADD/SUB immediate encode register 31 as SP, not ZR.
            if destination.is_none() || carrier(src)?.0.is_none() {
                return Err(invalid("immediate ADD/SUB cannot access SP/ZR"));
            }
            let a = read(src, bits, false)?;
            let shift = if inst.opcode == M::AddRIShift12 {
                12
            } else {
                0
            };
            let b = E::bv_const((*imm as u64) << shift, bits);
            match inst.opcode {
                M::SubRI => semantics::encode_sub_rr(operand_size, a, b),
                M::AddsRI => {
                    let (value, flags) = nzcv::encode_adds(a, b, bits);
                    updated_flags = Some(flags);
                    value
                }
                M::SubsRI => {
                    let (value, flags) = nzcv::encode_subs(a, b, bits);
                    updated_flags = Some(flags);
                    value
                }
                _ => semantics::encode_add_rr(operand_size, a, b),
            }
        }
        (M::AndRI | M::OrrRI | M::EorRI, [_, src, imm]) => {
            // Non-setting logical-immediate Rd=31 is SP/WSP, not ZR.
            // A decoded discarded destination would silently lose a frame
            // effect here, so the frameless observation profile refuses it.
            if destination.is_none() {
                return Err(invalid("logical immediate would write SP"));
            }
            let a = read(src, bits, false)?;
            let b = logical(imm, bits)?;
            match inst.opcode {
                M::AndRI => semantics::encode_and_rr(operand_size, a, b),
                M::OrrRI => semantics::encode_orr_rr(operand_size, a, b),
                _ => semantics::encode_eor_rr(operand_size, a, b),
            }
        }
        (M::LslRI | M::LsrRI | M::AsrRI, [_, src, O::Imm(shift)])
            if (0..i64::from(bits)).contains(shift) =>
        {
            let a = read(src, bits, false)?;
            let b = E::bv_const(*shift as u64, bits);
            match inst.opcode {
                M::LslRI => semantics::encode_lsl_rr(operand_size, a, b),
                M::LsrRI => semantics::encode_lsr_rr(operand_size, a, b),
                _ => semantics::encode_asr_rr(operand_size, a, b),
            }
        }
        (M::CSet, [_, O::Imm(cc)]) => {
            E::ite(condition(*cc)?, E::bv_const(1, bits), E::bv_const(0, bits))
        }
        (M::Csel | M::Csinc | M::Csinv | M::Csneg, [_, yes, no, O::Imm(cc)]) => {
            let yes = read(yes, bits, false)?;
            let no = read(no, bits, false)?;
            let no = match inst.opcode {
                M::Csinc => no.bvadd(E::bv_const(1, bits)),
                M::Csinv => no.bvxor(E::bv_const(u64::MAX, bits)),
                M::Csneg => no.bvneg(),
                _ => no,
            };
            E::ite(condition(*cc)?, yes, no)
        }
        _ => return Err(invalid("unsupported allocated scalar operation/arity")),
    };
    Ok(scalar(destination, bits, value, updated_flags))
}

fn memory_effect(inst: &MachInst, address: E, data: &O) -> Result<Step, ReadOnlyTargetError> {
    let (destination, bits) = carrier(data)?;
    let byte_width = bits / 8;
    if matches!(inst.opcode, M::LdrRI | M::LdrRO) {
        Ok(Step::MemoryLoad {
            destination: destination.unwrap_or(31),
            address,
            byte_width,
            alignment: 1,
        })
    } else {
        Ok(Step::MemoryStore {
            address,
            value: Box::new(read(data, bits, false)?),
            byte_width,
            alignment: 1,
        })
    }
}

fn immediate_memory(inst: &MachInst) -> Result<Step, ReadOnlyTargetError> {
    // Reuse operand admission, not its separately re-derived instruction word.
    // This preserves the ordinary explicit, implicit-zero and MemOp spellings.
    let access = crate::aarch64_instruction_word_proofs::scalar_memory_access(inst)
        .ok_or_else(|| invalid("unsupported scalar immediate memory shape"))?;
    if !matches!(access.bytes, 4 | 8) || access.base > 17 {
        return Err(invalid(
            "scalar memory requires 4/8 bytes and ordinary X base",
        ));
    }
    let data = &inst.operands[0];
    let (_, bits) = carrier(data)?;
    if bits / 8 != access.bytes {
        return Err(invalid("scalar memory transfer width"));
    }
    let address = crate::memory_proofs::qf_bv_byte_addr(
        &register(usize::from(access.base)),
        access.offset as u64,
    );
    memory_effect(inst, address, data)
}

fn register_memory(inst: &MachInst) -> Result<Step, ReadOnlyTargetError> {
    let (data, base, index, mode) = match inst.operands.as_slice() {
        [data, base, index] => (data, base, index, 6),
        [data, base, index, O::Imm(mode)] if matches!(*mode, 4 | 5 | 6 | 7 | 12 | 13 | 14 | 15) => {
            (data, base, index, *mode)
        }
        _ => return Err(invalid("unsupported scalar register memory shape")),
    };
    let (_, bits) = carrier(data)?;
    let (Some(_), 64) = carrier(base)? else {
        return Err(invalid("scalar memory base must be ordinary X, not SP/ZR"));
    };
    let (index_slot, index_bits) = carrier(index)?;
    let option = (mode >> 1) as u32;
    if matches!(option, 3 | 7) && index_bits != 64 && index_slot.is_some() {
        return Err(invalid("full-width memory index requires X or known zero"));
    }
    let shift = if mode & 1 == 0 { 0 } else { bits.ilog2() - 3 };
    let index_value = index_slot.map_or_else(|| E::bv_const(0, 64), register);
    let extended =
        crate::aarch64_instruction_word_proofs::extend_reg_value(index_value, option, shift)
            .ok_or_else(|| invalid("unsupported memory index extension"))?;
    let address = read(base, 64, false)?.bvadd(extended);
    memory_effect(inst, address, data)
}

fn load_pair(inst: &MachInst) -> Result<Step, ReadOnlyTargetError> {
    let (first, second, base, offset) = match inst.operands.as_slice() {
        [first, second, base] => (first, second, base, 0),
        [first, second, base, O::Imm(offset)] => (first, second, base, *offset),
        _ => return Err(invalid("unsupported offset load-pair shape")),
    };
    let (first_slot, bits) = carrier(first)?;
    let (second_slot, second_bits) = carrier(second)?;
    if bits != second_bits {
        return Err(invalid("load-pair transfer widths differ"));
    }
    // Repeated architectural destinations, INCLUDING ZR/ZR, are constrained
    // unpredictable. Base overlap is legal without writeback: the driver
    // snapshots this one address before either destination is updated.
    if first_slot == second_slot {
        return Err(invalid("load-pair destinations repeat"));
    }
    let (Some(_), 64) = carrier(base)? else {
        return Err(invalid("load-pair base must be ordinary X, not SP/ZR"));
    };
    let byte_width = bits / 8;
    let scale = i64::from(byte_width);
    if offset % scale != 0 || !(-64..=63).contains(&(offset / scale)) {
        return Err(invalid("load-pair signed scaled displacement"));
    }
    Ok(Step::LoadPair {
        destinations: [first_slot.unwrap_or(31), second_slot.unwrap_or(31)],
        address: Box::new(crate::memory_proofs::qf_bv_byte_addr(
            &read(base, 64, false)?,
            offset as u64,
        )),
        byte_width,
        alignment: 1,
    })
}

fn instruction_profile(
    inst: &MachInst,
    pc: usize,
    layout: &Layout,
    profile: Profile,
    returned: Option<&[usize]>,
) -> Result<Step, ReadOnlyTargetError> {
    if inst.opcode == M::Ret
        && let Some(registers) = returned
    {
        if inst.flags != M::Ret.default_flags()
            || !inst.implicit_defs.is_empty()
            || inst.proof.is_some()
            || inst.implicit_uses.len() != registers.len()
            || inst
                .implicit_uses
                .iter()
                .zip(registers)
                .any(|(actual, expected)| usize::from(actual.encoding()) != *expected)
            || !matches!(inst.operands.as_slice(), [O::PReg(reg)] if reg.encoding() == 30)
        {
            return Err(invalid(
                "requires exact RET X30 and complete ordered result carriers",
            ));
        }
        return Ok(Step::Return);
    }
    if profile == Profile::ReadOnly
        || !matches!(
            inst.opcode,
            M::LdrRI
                | M::StrRI
                | M::LdrRO
                | M::StrRO
                | M::LdpRI
                | M::Madd
                | M::Uxtw
                | M::AddRRShift
        )
    {
        return instruction(inst, pc, layout);
    }
    if !plain(inst) {
        return Err(invalid("noncanonical effects/implicit operands/proof"));
    }
    match inst.opcode {
        M::LdrRI | M::StrRI => return immediate_memory(inst),
        M::LdrRO | M::StrRO => return register_memory(inst),
        M::LdpRI => return load_pair(inst),
        _ => {}
    }
    let operands = inst.operands.as_slice();
    let dst = operands
        .first()
        .ok_or_else(|| invalid("missing scalar destination"))?;
    let (destination, bits) = carrier(dst)?;
    let value = match (inst.opcode, operands) {
        (M::Madd, [_, left, right, addend]) => semantics::encode_madd_rr(
            size(bits),
            read(left, bits, false)?,
            read(right, bits, false)?,
            read(addend, bits, false)?,
        ),
        (M::Uxtw, [_, source]) => {
            // The established alias writes Wd even with X-tracked operands.
            // Read low32 and zero the full X result at either destination view.
            let source = if carrier(source)?.0.is_none() {
                E::bv_const(0, 32)
            } else {
                read(source, 32, true)?
            };
            return Ok(scalar(
                destination,
                64,
                semantics::encode_uxt(32, 64, source),
                None,
            ));
        }
        (M::AddRRShift, [_, left, right, O::Imm(shift)])
            if (1..i64::from(bits)).contains(shift) =>
        {
            semantics::encode_add_shifted_reg(
                size(bits),
                read(left, bits, false)?,
                read(right, bits, false)?,
                semantics::RegShiftKind::Lsl,
                *shift as u32,
            )
        }
        _ => return Err(invalid("unsupported scalar-memory arithmetic shape")),
    };
    Ok(scalar(destination, bits, value, None))
}

fn logical(operand: &O, bits: u32) -> Result<E, ReadOnlyTargetError> {
    let O::Imm(imm) = operand else {
        return Err(invalid("logical immediate required"));
    };
    if !trust_cg_opt::const_materialize::is_logical_immediate(*imm as u64, bits) {
        return Err(invalid("unencodable logical immediate"));
    }
    Ok(E::bv_const(*imm as u64, bits))
}

fn move_wide(op: M, dst: &O, bits: u32, imm: i64, shift: i64) -> Result<E, ReadOnlyTargetError> {
    if !(0..=65535).contains(&imm)
        || !(0..i64::from(bits)).contains(&shift)
        || shift % 16 != 0
        || (op == M::Movz && shift != 0)
    {
        return Err(invalid("move-wide immediate/shift policy"));
    }
    let value = (imm as u64) << shift;
    Ok(match op {
        M::Movn => E::bv_const(!value, bits),
        M::Movk => read(dst, bits, false)?
            .bvand(E::bv_const(!(0xffffu64 << shift), bits))
            .bvor(E::bv_const(value, bits)),
        _ => E::bv_const(value, bits),
    })
}

pub(super) fn adapt(machine: &MachFunction) -> Result<Vec<Step>, ReadOnlyTargetError> {
    adapt_profile(machine, Profile::ReadOnly)
}

pub(super) fn adapt_profile(
    machine: &MachFunction,
    profile: Profile,
) -> Result<Vec<Step>, ReadOnlyTargetError> {
    adapt_profile_returning(machine, profile, None)
}

pub(super) fn adapt_returns(
    machine: &MachFunction,
    registers: &[usize],
) -> Result<Vec<Step>, ReadOnlyTargetError> {
    if registers.is_empty()
        || registers.len() > 8
        || registers
            .iter()
            .enumerate()
            .any(|(index, register)| *register != index)
    {
        return Err(invalid(
            "complete ordered scalar result carrier inventory required",
        ));
    }
    adapt_profile_returning(machine, Profile::ScalarMemory, Some(registers))
}

pub(super) fn adapt_void(machine: &MachFunction) -> Result<Vec<Step>, ReadOnlyTargetError> {
    if machine.signature.params != [Type::I64, Type::I64] || !machine.signature.returns.is_empty() {
        return Err(invalid("requires exact two-word/void ABI"));
    }
    adapt_profile_returning(machine, Profile::ScalarMemory, Some(&[]))
}

fn adapt_profile_returning(
    machine: &MachFunction,
    profile: Profile,
    returned: Option<&[usize]>,
) -> Result<Vec<Step>, ReadOnlyTargetError> {
    if machine.signature.params.is_empty()
        || machine.signature.params.len() > 8
        || machine.signature.params.iter().any(|ty| *ty != Type::I64)
        || returned.map_or_else(
            || machine.signature.returns != [Type::I64],
            |registers| {
                machine.signature.returns.len() != registers.len()
                    || machine.signature.returns.iter().any(|ty| *ty != Type::I64)
            },
        )
    {
        return Err(invalid("requires 1..8 I64 ABI parameters and I64 result"));
    }
    if !machine.stack_slots.is_empty()
        || machine.stack_protector.is_enabled()
        || machine.stack_protector_slot.is_some()
        || machine.stack_limit.is_some()
        || machine.stack_limit_overflow_block.is_some()
        || !machine.jump_tables.is_empty()
        || machine.eh_metadata.has_eh_info()
        || !machine.call_abi_facts.is_empty()
        || machine
            .incoming_stack_arg_bytes
            .is_some_and(|bytes| bytes != 0)
        || !machine.function_proofs.is_empty()
        || !machine.function_target_features.is_empty()
    {
        return Err(invalid(
            "frameless ordinary integer ABI/effect profile required",
        ));
    }
    let layout = layout(machine)?;
    layout
        .linked
        .iter()
        .enumerate()
        .map(|(pc, id)| {
            instruction_profile(
                &machine.insts[id.0 as usize],
                pc,
                &layout,
                profile,
                returned,
            )
        })
        .collect()
}
