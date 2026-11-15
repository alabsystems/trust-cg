// trust-cg-opt - Test-only MachIR interpreter for the vectorizer's loop idioms
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A small, strict MachIR interpreter used as a differential oracle for the
//! CFG-rewriting loop idioms (the i32 induction store and the reverse
//! accumulation), and for `loop_unroll`'s bounded-early-exit address fold.
//!
//! It executes only the opcodes those fixtures and their rewrites emit, and it
//! returns `Err` rather than guessing on anything else: an unsupported opcode
//! or operand shape, a read of a register nothing has written, a register read
//! at a different class than it was written, a condition read before any
//! compare, an access outside the memory regions the test mapped, or a run
//! longer than its step budget. A rewrite passes these tests only when the
//! rewritten function returns with exactly the scalar function's memory and
//! observed registers.
//!
//! Semantics follow AArch64: register values are the architectural W/X/Q
//! contents, `B.cond`/`CSET` immediates are the hardware 4-bit condition
//! encodings, compares set NZCV from a subtraction at the width of their
//! first operand, move-wide immediates must be encodable, and a block whose
//! last instruction does not branch falls through to the next block in
//! `block_order`. Stack slot `n` lives at `FRAME_BASE + n * FRAME_SLOT_BYTES`.
//!
//! This is evidence for the shapes and inputs the tests run, not a model of
//! the whole ISA and not a proof of either rewrite.

use crate::fast_hash::FxHashMap as HashMap;

use trust_cg_ir::{AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, RegClass, VReg};

/// Address of stack slot 0.
pub(crate) const FRAME_BASE: u64 = 0x0000_7fff_0000_0000;
/// Bytes reserved per stack slot.
pub(crate) const FRAME_SLOT_BYTES: u64 = 64;

/// One mapped memory region.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Region {
    pub(crate) start: u64,
    pub(crate) bytes: Vec<u8>,
}

impl Region {
    /// A region holding `values` as consecutive little-endian i32s.
    pub(crate) fn i32s(start: u64, values: &[i32]) -> Self {
        Self {
            start,
            bytes: values
                .iter()
                .flat_map(|value| value.to_le_bytes())
                .collect(),
        }
    }

    /// The stack frame for `slots` slots, zero-initialized.
    pub(crate) fn frame(slots: u64) -> Self {
        Self {
            start: FRAME_BASE,
            bytes: vec![0; (slots * FRAME_SLOT_BYTES) as usize],
        }
    }

    /// The region read back as consecutive little-endian i32s.
    pub(crate) fn read_i32s(&self) -> Vec<i32> {
        let (words, _) = self.bytes.as_chunks::<4>();
        words.iter().map(|&word| i32::from_le_bytes(word)).collect()
    }
}

/// Registers and memory of one run.
#[derive(Debug, Clone)]
pub(crate) struct MachState {
    regs: HashMap<u32, (RegClass, u128)>,
    pub(crate) regions: Vec<Region>,
}

impl MachState {
    pub(crate) fn new(regions: Vec<Region>) -> Self {
        Self {
            regs: HashMap::default(),
            regions,
        }
    }

    /// Seed a live-in register.
    pub(crate) fn with_reg(mut self, vreg: VReg, value: u128) -> Self {
        let bits = class_bits(vreg.class).expect("seeded register class");
        self.regs.insert(vreg.id, (vreg.class, value & mask(bits)));
        self
    }

    /// The value of `vreg` if it was last written at exactly that class.
    pub(crate) fn reg(&self, vreg: VReg) -> Option<u128> {
        self.regs
            .get(&vreg.id)
            .and_then(|&(class, value)| (class == vreg.class).then_some(value))
    }

    fn read(&self, vreg: VReg) -> Result<u128, String> {
        match self.regs.get(&vreg.id) {
            Some(&(class, value)) if class == vreg.class => Ok(value),
            Some(&(class, _)) => Err(format!(
                "v{} read as {:?} but last written as {class:?}",
                vreg.id, vreg.class
            )),
            None => Err(format!(
                "read of undefined register v{} ({:?})",
                vreg.id, vreg.class
            )),
        }
    }

    fn write(&mut self, vreg: VReg, value: u128) -> Result<(), String> {
        let bits = class_bits(vreg.class)?;
        self.regs.insert(vreg.id, (vreg.class, value & mask(bits)));
        Ok(())
    }

    fn region_offset(&self, addr: u64, len: usize) -> Result<(usize, usize), String> {
        for (index, region) in self.regions.iter().enumerate() {
            let Some(offset) = addr.checked_sub(region.start) else {
                continue;
            };
            let Ok(offset) = usize::try_from(offset) else {
                continue;
            };
            if offset
                .checked_add(len)
                .is_some_and(|end| end <= region.bytes.len())
            {
                return Ok((index, offset));
            }
        }
        Err(format!(
            "{len}-byte access at {addr:#x} is outside mapped memory"
        ))
    }

    fn load(&self, addr: u64, len: usize) -> Result<u128, String> {
        let (index, offset) = self.region_offset(addr, len)?;
        let bytes = &self.regions[index].bytes[offset..offset + len];
        Ok(bytes
            .iter()
            .rev()
            .fold(0u128, |acc, &byte| (acc << 8) | u128::from(byte)))
    }

    fn store(&mut self, addr: u64, len: usize, value: u128) -> Result<(), String> {
        let (index, offset) = self.region_offset(addr, len)?;
        for (i, byte) in self.regions[index].bytes[offset..offset + len]
            .iter_mut()
            .enumerate()
        {
            *byte = (value >> (8 * i)) as u8;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
struct Nzcv {
    n: bool,
    z: bool,
    c: bool,
    v: bool,
}

fn class_bits(class: RegClass) -> Result<u32, String> {
    match class {
        RegClass::Gpr32 => Ok(32),
        RegClass::Gpr64 => Ok(64),
        RegClass::Fpr128 => Ok(128),
        other => Err(format!("unsupported register class {other:?}")),
    }
}

fn mask(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

fn sub_flags(lhs: u128, rhs: u128, bits: u32) -> Nzcv {
    let width = mask(bits);
    let (lhs, rhs) = (lhs & width, rhs & width);
    let result = lhs.wrapping_sub(rhs) & width;
    let sign = 1u128 << (bits - 1);
    Nzcv {
        n: result & sign != 0,
        z: result == 0,
        c: lhs >= rhs,
        v: (lhs ^ rhs) & (lhs ^ result) & sign != 0,
    }
}

/// Arm `ConditionHolds` over a 4-bit condition encoding.
fn condition_holds(cond: i64, flags: Nzcv) -> Result<bool, String> {
    if !(0..=15).contains(&cond) {
        return Err(format!("condition encoding {cond} is not 4-bit"));
    }
    let base = match cond >> 1 {
        0 => flags.z,
        1 => flags.c,
        2 => flags.n,
        3 => flags.v,
        4 => flags.c && !flags.z,
        5 => flags.n == flags.v,
        6 => flags.n == flags.v && !flags.z,
        _ => true,
    };
    Ok(if cond & 1 == 1 && cond != 15 {
        !base
    } else {
        base
    })
}

fn expect_len(inst: &MachInst, lens: &[usize]) -> Result<(), String> {
    if lens.contains(&inst.operands.len()) {
        Ok(())
    } else {
        Err(format!(
            "{:?} with {} operands is outside the modeled forms",
            inst.opcode,
            inst.operands.len()
        ))
    }
}

fn vreg_at(inst: &MachInst, pos: usize) -> Result<VReg, String> {
    match inst.operands.get(pos) {
        Some(MachOperand::VReg(vreg)) => Ok(*vreg),
        other => Err(format!(
            "{:?} operand {pos} is {other:?}, not a virtual register",
            inst.opcode
        )),
    }
}

fn imm_at(inst: &MachInst, pos: usize) -> Result<i64, String> {
    match inst.operands.get(pos) {
        Some(MachOperand::Imm(value)) => Ok(*value),
        None => Ok(0),
        other => Err(format!(
            "{:?} operand {pos} is {other:?}, not an immediate",
            inst.opcode
        )),
    }
}

fn block_at(inst: &MachInst, pos: usize) -> Result<BlockId, String> {
    match inst.operands.get(pos) {
        Some(MachOperand::Block(block)) => Ok(*block),
        other => Err(format!(
            "{:?} operand {pos} is {other:?}, not a block",
            inst.opcode
        )),
    }
}

fn same_class(inst: &MachInst, regs: &[VReg]) -> Result<u32, String> {
    let class = regs[0].class;
    if regs.iter().any(|reg| reg.class != class) {
        return Err(format!(
            "{:?} mixes register classes: {regs:?}",
            inst.opcode
        ));
    }
    class_bits(class)
}

fn gpr_address(state: &MachState, inst: &MachInst, pos: usize) -> Result<u64, String> {
    let base = vreg_at(inst, pos)?;
    if base.class != RegClass::Gpr64 {
        return Err(format!("{:?} base {base:?} is not a Gpr64", inst.opcode));
    }
    Ok(state.read(base)? as u64)
}

fn data_bytes(class: RegClass) -> Result<usize, String> {
    match class {
        RegClass::Gpr32 => Ok(4),
        RegClass::Gpr64 => Ok(8),
        RegClass::Fpr128 => Ok(16),
        other => Err(format!("unsupported transfer class {other:?}")),
    }
}

const S4_ARRANGEMENT: i64 = 5;
const S_ELEMENT_BYTES: i64 = 4;

fn lane32(value: u128, lane: u32) -> u128 {
    (value >> (32 * lane)) & 0xFFFF_FFFF
}

/// Run `func` from its entry until `Ret`, or fail.
pub(crate) fn run(
    func: &MachFunction,
    mut state: MachState,
    max_steps: usize,
) -> Result<MachState, String> {
    let mut block = func.entry;
    let mut pos = 0usize;
    let mut flags: Option<Nzcv> = None;
    for _ in 0..max_steps {
        let Some(&inst_id) = func.block(block).insts.get(pos) else {
            let at = func
                .block_order
                .iter()
                .position(|&candidate| candidate == block)
                .ok_or_else(|| format!("bb{} is not in block_order", block.0))?;
            block = *func
                .block_order
                .get(at + 1)
                .ok_or_else(|| format!("bb{} falls off the end of the layout", block.0))?;
            pos = 0;
            continue;
        };
        let inst = func.inst(inst_id);
        pos += 1;
        match inst.opcode {
            AArch64Opcode::Nop => {}
            AArch64Opcode::Ret => return Ok(state),
            AArch64Opcode::B => {
                expect_len(inst, &[1])?;
                block = block_at(inst, 0)?;
                pos = 0;
            }
            AArch64Opcode::BCond => {
                expect_len(inst, &[2])?;
                let taken = condition_holds(
                    imm_at(inst, 0)?,
                    flags.ok_or("B.cond reads NZCV before any compare")?,
                )?;
                if taken {
                    block = block_at(inst, 1)?;
                    pos = 0;
                }
            }
            AArch64Opcode::Movz | AArch64Opcode::Movn => {
                let (dst, imm, shift) = crate::reaching_const::parse_move_wide_inst(inst)
                    .ok_or_else(|| format!("unencodable move-wide {:?}", inst.operands))?;
                let wide = u128::from(imm) << shift;
                let value = if inst.opcode == AArch64Opcode::Movz {
                    wide
                } else {
                    !wide
                };
                state.write(dst, value)?;
            }
            AArch64Opcode::MovR | AArch64Opcode::Copy => {
                expect_len(inst, &[2])?;
                let (dst, src) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?);
                same_class(inst, &[dst, src])?;
                state.write(dst, state.read(src)?)?;
            }
            AArch64Opcode::AddRR => {
                expect_len(inst, &[3])?;
                let (dst, lhs, rhs) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?, vreg_at(inst, 2)?);
                same_class(inst, &[dst, lhs, rhs])?;
                state.write(dst, state.read(lhs)?.wrapping_add(state.read(rhs)?))?;
            }
            AArch64Opcode::AndRR => {
                expect_len(inst, &[3])?;
                let (dst, lhs, rhs) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?, vreg_at(inst, 2)?);
                same_class(inst, &[dst, lhs, rhs])?;
                state.write(dst, state.read(lhs)? & state.read(rhs)?)?;
            }
            AArch64Opcode::AddRI | AArch64Opcode::SubRI => {
                expect_len(inst, &[3])?;
                let (dst, src) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?);
                let bits = same_class(inst, &[dst, src])?;
                let imm = (imm_at(inst, 2)? as i128 as u128) & mask(bits);
                let value = state.read(src)?;
                let result = if inst.opcode == AArch64Opcode::AddRI {
                    value.wrapping_add(imm)
                } else {
                    value.wrapping_sub(imm)
                };
                state.write(dst, result)?;
            }
            AArch64Opcode::Sxtw => {
                expect_len(inst, &[2])?;
                let (dst, src) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?);
                if dst.class != RegClass::Gpr64 || src.class != RegClass::Gpr32 {
                    return Err(format!("sxtw {dst:?} <- {src:?} is not X <- W"));
                }
                let value = state.read(src)? as u32 as i32 as i64 as u64;
                state.write(dst, u128::from(value))?;
            }
            AArch64Opcode::Madd => {
                expect_len(inst, &[4])?;
                let regs = [
                    vreg_at(inst, 0)?,
                    vreg_at(inst, 1)?,
                    vreg_at(inst, 2)?,
                    vreg_at(inst, 3)?,
                ];
                same_class(inst, &regs)?;
                let product = state.read(regs[1])?.wrapping_mul(state.read(regs[2])?);
                state.write(regs[0], product.wrapping_add(state.read(regs[3])?))?;
            }
            AArch64Opcode::CmpRR => {
                expect_len(inst, &[2])?;
                let (lhs, rhs) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?);
                let bits = same_class(inst, &[lhs, rhs])?;
                flags = Some(sub_flags(state.read(lhs)?, state.read(rhs)?, bits));
            }
            AArch64Opcode::CmpRI => {
                expect_len(inst, &[2])?;
                let lhs = vreg_at(inst, 0)?;
                let bits = class_bits(lhs.class)?;
                let imm = imm_at(inst, 1)? as i128 as u128;
                flags = Some(sub_flags(state.read(lhs)?, imm, bits));
            }
            AArch64Opcode::CSet => {
                expect_len(inst, &[2])?;
                let taken = condition_holds(
                    imm_at(inst, 1)?,
                    flags.ok_or("CSET reads NZCV before any compare")?,
                )?;
                state.write(vreg_at(inst, 0)?, u128::from(taken))?;
            }
            AArch64Opcode::LdrRI => {
                expect_len(inst, &[2, 3])?;
                let dst = vreg_at(inst, 0)?;
                let addr = gpr_address(&state, inst, 1)?.wrapping_add(imm_at(inst, 2)? as u64);
                let value = state.load(addr, data_bytes(dst.class)?)?;
                state.write(dst, value)?;
            }
            AArch64Opcode::StrRI => {
                expect_len(inst, &[2, 3])?;
                let src = vreg_at(inst, 0)?;
                let addr = gpr_address(&state, inst, 1)?.wrapping_add(imm_at(inst, 2)? as u64);
                state.store(addr, data_bytes(src.class)?, state.read(src)?)?;
            }
            AArch64Opcode::LdpRI => {
                expect_len(inst, &[3, 4])?;
                let (first, second) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?);
                same_class(inst, &[first, second])?;
                let len = data_bytes(first.class)?;
                let addr = gpr_address(&state, inst, 2)?.wrapping_add(imm_at(inst, 3)? as u64);
                let lo = state.load(addr, len)?;
                let hi = state.load(addr.wrapping_add(len as u64), len)?;
                state.write(first, lo)?;
                state.write(second, hi)?;
            }
            AArch64Opcode::StpRI => {
                expect_len(inst, &[3, 4])?;
                let (first, second) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?);
                same_class(inst, &[first, second])?;
                let len = data_bytes(first.class)?;
                let addr = gpr_address(&state, inst, 2)?.wrapping_add(imm_at(inst, 3)? as u64);
                let (lo, hi) = (state.read(first)?, state.read(second)?);
                state.store(addr, len, lo)?;
                state.store(addr.wrapping_add(len as u64), len, hi)?;
            }
            AArch64Opcode::AddPCRel => {
                expect_len(inst, &[3])?;
                let dst = vreg_at(inst, 0)?;
                let Some(MachOperand::StackSlot(slot)) = inst.operands.get(2) else {
                    return Err(format!(
                        "AddPCRel without a stack slot: {:?}",
                        inst.operands
                    ));
                };
                if dst.class != RegClass::Gpr64 {
                    return Err(format!("stack address {dst:?} is not a Gpr64"));
                }
                let addr = FRAME_BASE + u64::from(slot.0) * FRAME_SLOT_BYTES;
                state.write(dst, u128::from(addr))?;
            }
            AArch64Opcode::NeonDupGen => {
                expect_len(inst, &[3])?;
                let (dst, src) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?);
                if dst.class != RegClass::Fpr128
                    || src.class != RegClass::Gpr32
                    || imm_at(inst, 2)? != S_ELEMENT_BYTES
                {
                    return Err(format!("unmodeled DUP form {:?}", inst.operands));
                }
                let lane = state.read(src)?;
                state.write(dst, (0..4).fold(0u128, |acc, i| acc | (lane << (32 * i))))?;
            }
            AArch64Opcode::NeonInsGen => {
                expect_len(inst, &[4])?;
                let (dst, src) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?);
                let lane = imm_at(inst, 2)?;
                if dst.class != RegClass::Fpr128
                    || src.class != RegClass::Gpr32
                    || !(0..4).contains(&lane)
                    || imm_at(inst, 3)? != S_ELEMENT_BYTES
                {
                    return Err(format!("unmodeled INS form {:?}", inst.operands));
                }
                let shift = 32 * lane as u32;
                let cleared = state.read(dst)? & !(0xFFFF_FFFFu128 << shift);
                state.write(dst, cleared | (state.read(src)? << shift))?;
            }
            AArch64Opcode::NeonSt1Post => {
                expect_len(inst, &[3])?;
                let (src, base) = (vreg_at(inst, 0)?, vreg_at(inst, 1)?);
                if src.class != RegClass::Fpr128
                    || base.class != RegClass::Gpr64
                    || imm_at(inst, 2)? != S4_ARRANGEMENT
                {
                    return Err(format!("unmodeled ST1 form {:?}", inst.operands));
                }
                let addr = state.read(base)? as u64;
                state.store(addr, 16, state.read(src)?)?;
                state.write(base, u128::from(addr.wrapping_add(16)))?;
            }
            AArch64Opcode::NeonAddV => {
                expect_len(inst, &[4])?;
                let regs = [vreg_at(inst, 0)?, vreg_at(inst, 1)?, vreg_at(inst, 2)?];
                if regs.iter().any(|reg| reg.class != RegClass::Fpr128)
                    || imm_at(inst, 3)? != S4_ARRANGEMENT
                {
                    return Err(format!("unmodeled ADD (vector) form {:?}", inst.operands));
                }
                let (lhs, rhs) = (state.read(regs[1])?, state.read(regs[2])?);
                let sum = (0..4).fold(0u128, |acc, lane| {
                    let lane_sum = (lane32(lhs, lane) + lane32(rhs, lane)) & 0xFFFF_FFFF;
                    acc | (lane_sum << (32 * lane))
                });
                state.write(regs[0], sum)?;
            }
            other => return Err(format!("unmodeled opcode {other:?}")),
        }
    }
    Err(format!("step budget of {max_steps} exhausted"))
}
