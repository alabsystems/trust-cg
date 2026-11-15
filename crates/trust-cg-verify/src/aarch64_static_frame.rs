// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked relative geometry of explicitly selected static AArch64 envelopes.
//!
//! This is NOT a source/body proof, ABI certificate, memory-ownership witness or
//! instruction-credit route. Every epilogue is checked CONDITIONAL on entering
//! it with the prologue's SP/FP and saved-slot contents. All intervening body
//! intervals remain unresolved, including calls preserving SP/FP/private bytes.
//! No function verifier or publisher consumes this diagnostic owner.
//!
//! The image is the supplied, address-free fixed-width body, not an installed
//! image. Offsets follow real instructions in block order, never arena IDs.
//! Pair and address-arithmetic words use the existing independent word checks.
//! Relocation/final-image, CFG reachability, source refinement and provider
//! implementation evidence remain separate obligations. In particular only
//! selected envelope words are decoded: all MachIR RET rows are inventoried,
//! but body-image opcode/control correspondence remains unresolved.
//!
//! Entry SP must be 16-byte aligned, and adding the reported relative range to
//! it must not wrap the architectural address space. A writable allocation,
//! private-byte separation and body/call preservation are NOT established.

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_ir::{
    AArch64Opcode as Op, BlockId, InstId, MachFunction, MachInst, MachOperand as O, SpecialReg,
};
use trust_cg_lower::Function;

use crate::aarch64_memory_effect::{AccessForm, memory_access};
use crate::aarch64_pair_memory::{
    PairMemoryBase, PairMemoryFormat, PairMemoryMode, check_pair_encoding,
};

/// A half-open byte interval relative to entry SP. No absolute allocation,
/// writable extent, initialization or non-aliasing is established by it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RelativeFrameRegion {
    pub start: i64,
    pub end: i64,
}

impl RelativeFrameRegion {
    fn contains(self, other: Self) -> bool {
        self.start <= other.start && other.end <= self.end
    }
    fn overlaps(self, other: Self) -> bool {
        self.start < self.end
            && other.start < other.end
            && self.start < other.end
            && other.start < self.end
    }
    fn len(self) -> i64 {
        self.end - self.start
    }
}

/// The preserved-width identity, not a register allocator alias spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SavedFrameRegister {
    X(u8),
    D(u8),
}

/// Producer-supplied layout observations. These are claims checked against the
/// envelopes, not authority from a public layout constructor. `stack_slot_bytes`
/// combines addressable locals and spills; their separate provenance is unknown.
#[derive(Debug, Clone)]
pub struct StaticFrameLayoutClaim {
    /// Unordered register membership per pair, not transfer lane ordering or
    /// the producer's legacy pair-offset metadata. Actual slots are separate.
    pub saved_pairs: Vec<[SavedFrameRegister; 2]>,
    pub callee_saved_bytes: u32,
    pub stack_slot_bytes: u32,
    pub outgoing_argument_bytes: u32,
    pub total_bytes: u32,
    pub uses_frame_pointer: bool,
    pub dynamic_allocation: bool,
    pub red_zone: bool,
    /// Actual producer offsets, indexed by the original machine's slot ID.
    pub slot_fp_offsets: Vec<Option<i32>>,
}

/// Exact candidate instruction lists from the producer. The checker requires
/// an entry-block prefix, one block suffix per RET, and no reused instruction.
#[derive(Debug, Clone)]
pub struct StaticFrameEnvelopeCandidates {
    pub prologue: Vec<InstId>,
    pub epilogues: Vec<Vec<InstId>>,
}

/// Producer-supplied pending patch extent. Completeness and correspondence to
/// the eventual relocator remain unresolved; checked envelopes exclude every
/// byte in each supplied extent, including patches wider than one word.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrameImagePatch {
    pub offset: u32,
    pub bytes: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SavedFrameSlot {
    pub register: SavedFrameRegister,
    pub region: RelativeFrameRegion,
}

/// No claim is made that this interval preserves SP, FP, saved bytes or source
/// results, or even that its control flow reaches the selected epilogue.
#[derive(Debug)]
pub struct UnprovedFrameBodyInterval {
    pub block: BlockId,
    pub instructions: Vec<InstId>,
    /// MachIR call opcodes (regardless of mutable flags), not decoded body words.
    pub calls: Vec<InstId>,
}

#[derive(Debug)]
pub struct ConditionalFrameExit {
    pub return_instruction: InstId,
    /// Required state at this envelope's entry, NOT inferred across its body.
    pub required_sp: i64,
    pub required_fp: Option<i64>,
}

/// Borrowed geometry correspondence only; deliberately has no certificate,
/// proof-verdict, opcode-credit, install or callable conversion.
#[derive(Debug)]
pub struct CheckedStaticFrameEnvelopes<'a> {
    source: &'a Function,
    machine: &'a MachFunction,
    image: &'a [u8],
    claim: &'a StaticFrameLayoutClaim,
    candidates: &'a StaticFrameEnvelopeCandidates,
    patches: &'a [FrameImagePatch],
    saved_area: RelativeFrameRegion,
    stack_slots_area: RelativeFrameRegion,
    outgoing_area: RelativeFrameRegion,
    padding_area: RelativeFrameRegion,
    slots: Vec<SavedFrameSlot>,
    fixed_slots: Vec<RelativeFrameRegion>,
    exits: Vec<ConditionalFrameExit>,
    unresolved_body: Vec<UnprovedFrameBodyInterval>,
    offsets: BTreeMap<InstId, usize>,
}

impl<'a> CheckedStaticFrameEnvelopes<'a> {
    /// An unresolved entry-state requirement, not an alignment proof.
    pub fn required_entry_sp_alignment(&self) -> u32 {
        16
    }
    /// Entry SP plus this relative range must form a nonwrapping writable
    /// allocation. Neither allocation nor saved-byte privacy is established.
    pub fn required_nonwrapping_frame_range(&self) -> RelativeFrameRegion {
        RelativeFrameRegion {
            start: -i64::from(self.claim.total_bytes),
            end: 0,
        }
    }
    pub fn source(&self) -> &'a Function {
        self.source
    }
    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }
    pub fn image(&self) -> &'a [u8] {
        self.image
    }
    pub fn layout_claim(&self) -> &'a StaticFrameLayoutClaim {
        self.claim
    }
    pub fn candidates(&self) -> &'a StaticFrameEnvelopeCandidates {
        self.candidates
    }
    pub fn patches(&self) -> &'a [FrameImagePatch] {
        self.patches
    }
    pub fn saved_area(&self) -> RelativeFrameRegion {
        self.saved_area
    }
    pub fn stack_slots_area(&self) -> RelativeFrameRegion {
        self.stack_slots_area
    }
    pub fn outgoing_area(&self) -> RelativeFrameRegion {
        self.outgoing_area
    }
    pub fn padding_area(&self) -> RelativeFrameRegion {
        self.padding_area
    }
    pub fn saved_slots(&self) -> &[SavedFrameSlot] {
        &self.slots
    }
    pub fn fixed_slots(&self) -> &[RelativeFrameRegion] {
        &self.fixed_slots
    }
    pub fn conditional_exits(&self) -> &[ConditionalFrameExit] {
        &self.exits
    }
    pub fn unresolved_body(&self) -> &[UnprovedFrameBodyInterval] {
        &self.unresolved_body
    }
    pub fn byte_offset(&self, instruction: InstId) -> Option<usize> {
        self.offsets.get(&instruction).copied()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("static frame geometry: {0}")]
pub struct StaticFrameGeometryError(pub String);

type Result<T> = std::result::Result<T, StaticFrameGeometryError>;
fn refuse(why: impl Into<String>) -> StaticFrameGeometryError {
    StaticFrameGeometryError(why.into())
}

#[derive(Clone, Copy)]
struct State {
    sp: i64,
    fp: Option<i64>,
}

fn base(state: State, operand: &O) -> Option<i64> {
    match operand {
        O::Special(SpecialReg::SP) => Some(state.sp),
        O::PReg(reg) if reg.encoding() == 29 => state.fp,
        _ => None,
    }
}

fn ordinary(inst: &MachInst) -> bool {
    inst.flags == MachInst::new(inst.opcode, vec![]).flags
        && inst.implicit_defs.is_empty()
        && inst.implicit_uses.is_empty()
}

fn geometry_adjust(inst: &MachInst, word: u32, state: &mut State) -> Result<()> {
    let [dst, src, O::Imm(imm @ 0..=4095)] = inst.operands.as_slice() else {
        return Err(refuse("non-imm12 frame adjustment"));
    };
    if !ordinary(inst) {
        return Err(refuse("hidden adjustment effects"));
    }
    crate::aarch64_instruction_word_proofs::check_emitted_instruction_word(inst, word)
        .ok_or_else(|| refuse("unmodeled adjustment word"))?
        .map_err(refuse)?;
    let value = base(*state, src).ok_or_else(|| refuse("unknown frame adjustment base"))?;
    let next = if inst.opcode == Op::AddRI {
        value.checked_add(*imm)
    } else {
        value.checked_sub(*imm)
    }
    .ok_or_else(|| refuse("frame offset overflow"))?;
    match dst {
        O::Special(SpecialReg::SP) if next % 16 == 0 => state.sp = next,
        O::PReg(reg) if reg.encoding() == 29 => state.fp = Some(next),
        _ => return Err(refuse("adjustment is not aligned SP or FP setup")),
    }
    Ok(())
}

fn pair_slots(inst: &MachInst, word: u32, state: &mut State) -> Result<[SavedFrameSlot; 2]> {
    if !ordinary(inst) {
        return Err(refuse("hidden pair effects"));
    }
    let pair = check_pair_encoding(inst, &word.to_le_bytes())
        .map_err(|error| refuse(error.to_string()))?;
    let old_sp = state.sp;
    let access = memory_access(inst).ok_or_else(|| refuse("unmodeled pair memory effect"))?;
    if !matches!(access.form, AccessForm::Pair(_)) || access.bytes != 8 {
        return Err(refuse("pair is not two 64-bit lanes"));
    }
    let origin = match pair.base() {
        PairMemoryBase::Sp => state.sp,
        PairMemoryBase::Register(29) => state.fp.ok_or_else(|| refuse("unknown FP pair base"))?,
        _ => return Err(refuse("pair base is not SP or FP")),
    };
    let start = origin
        .checked_add(access.lane0_displacement())
        .ok_or_else(|| refuse("pair offset overflow"))?;
    if start % 8 != 0 {
        return Err(refuse("unaligned saved pair"));
    }
    if let Some(displacement) = access.writeback_displacement() {
        let next = origin
            .checked_add(displacement)
            .ok_or_else(|| refuse("pair writeback overflow"))?;
        match pair.base() {
            PairMemoryBase::Sp if next % 16 == 0 => state.sp = next,
            PairMemoryBase::Register(29) if displacement == 0 => {}
            _ => return Err(refuse("unaligned SP or unsupported FP writeback")),
        }
    }
    let access_sp = if pair.mode() == PairMemoryMode::PreIndex {
        state.sp
    } else {
        old_sp
    };
    if start < access_sp {
        return Err(refuse("pair accesses below the live SP"));
    }
    let fields = pair.transfer_fields();
    let register = |field| match pair.format() {
        PairMemoryFormat::X64 if (19..=30).contains(&field) => Ok(SavedFrameRegister::X(field)),
        PairMemoryFormat::D64 if (8..=15).contains(&field) => Ok(SavedFrameRegister::D(field)),
        _ => Err(refuse(
            "saved register outside supported callee-save widths/banks",
        )),
    };
    Ok([
        SavedFrameSlot {
            register: register(fields[0])?,
            region: RelativeFrameRegion {
                start,
                end: start + 8,
            },
        },
        SavedFrameSlot {
            register: register(fields[1])?,
            region: RelativeFrameRegion {
                start: start + 8,
                end: start + 16,
            },
        },
    ])
}

/// Check explicitly selected envelopes, without recognizing or proving the
/// intervening function body. The exact source is borrowed for endpoint custody
/// only. Image-to-row coordinates follow AArch64's existing fixed-width final
/// block-order contract; this API admits no jump-table/data suffix or pseudos
/// inside an envelope. Supplied fixup-list completeness, body opcode binding
/// and installed-byte replay remain external.
pub fn check_static_frame_envelopes<'a>(
    source: &'a Function,
    machine: &'a MachFunction,
    image: &'a [u8],
    claim: &'a StaticFrameLayoutClaim,
    candidates: &'a StaticFrameEnvelopeCandidates,
    patches: &'a [FrameImagePatch],
) -> Result<CheckedStaticFrameEnvelopes<'a>> {
    if image.len() > u32::MAX as usize {
        return Err(refuse("image exceeds fixup coordinate domain"));
    }
    if source.name != machine.name {
        return Err(refuse("different source/machine names"));
    }
    if claim.dynamic_allocation
        || claim.red_zone
        || machine.stack_slots.iter().any(|s| s.is_runtime_sized())
        || machine.eh_metadata.has_eh_info()
        || !machine.jump_tables.is_empty()
    {
        return Err(refuse(
            "dynamic, red-zone, EH or jump-table frame outside static envelope domain",
        ));
    }
    let saved = i64::from(claim.callee_saved_bytes);
    let storage = i64::from(claim.stack_slot_bytes);
    let outgoing = i64::from(claim.outgoing_argument_bytes);
    let total = i64::from(claim.total_bytes);
    let minimum = saved + storage + outgoing;
    if total % 16 != 0
        || saved % 16 != 0
        || outgoing % 16 != 0
        || total < minimum
        || total - minimum >= 16
        || claim.saved_pairs.len().checked_mul(16) != Some(claim.callee_saved_bytes as usize)
        || claim.uses_frame_pointer != (saved != 0)
    {
        return Err(refuse("inconsistent aligned region extents"));
    }
    let saved_area = RelativeFrameRegion {
        start: -saved,
        end: 0,
    };
    let stack_slots_area = RelativeFrameRegion {
        start: -saved - storage,
        end: -saved,
    };
    let outgoing_area = RelativeFrameRegion {
        start: -total,
        end: -total + outgoing,
    };
    let padding_area = RelativeFrameRegion {
        start: outgoing_area.end,
        end: stack_slots_area.start,
    };
    let mut expected = BTreeSet::new();
    for &pair in &claim.saved_pairs {
        for register in pair {
            if !matches!(
                register,
                SavedFrameRegister::X(19..=30) | SavedFrameRegister::D(8..=15)
            ) || !expected.insert(register)
            {
                return Err(refuse("invalid or duplicate claimed saved register"));
            }
        }
    }
    if claim.uses_frame_pointer
        && (!expected.contains(&SavedFrameRegister::X(29))
            || !expected.contains(&SavedFrameRegister::X(30)))
    {
        return Err(refuse("missing claimed FP/LR"));
    }
    let mut offsets = BTreeMap::new();
    let mut rows = Vec::new();
    let mut blocks = BTreeSet::new();
    if machine.block_order.first() != Some(&machine.entry) {
        return Err(refuse("entry is not first emitted block"));
    }
    for &block in &machine.block_order {
        if !blocks.insert(block) {
            return Err(refuse("duplicate emitted block"));
        }
        let body = machine
            .blocks
            .get(block.0 as usize)
            .ok_or_else(|| refuse("missing emitted block"))?;
        let mut real = Vec::new();
        for &id in &body.insts {
            let inst = machine
                .insts
                .get(id.0 as usize)
                .ok_or_else(|| refuse("missing emitted instruction"))?;
            if inst.is_pseudo() {
                continue;
            }
            let offset = offsets
                .len()
                .checked_mul(4)
                .ok_or_else(|| refuse("image size overflow"))?;
            if offsets.insert(id, offset).is_some() {
                return Err(refuse("reused emitted instruction"));
            }
            real.push(id);
        }
        rows.push((block, real));
    }
    if offsets.len().checked_mul(4) != Some(image.len()) {
        return Err(refuse("image is not exact fixed-width body"));
    }
    let mut patchable = Vec::new();
    for patch in patches {
        let region = RelativeFrameRegion {
            start: i64::from(patch.offset),
            end: i64::from(patch.offset) + i64::from(patch.bytes),
        };
        if patch.offset % 4 != 0
            || patch.bytes == 0
            || region.end > image.len() as i64
            || patchable.iter().any(|other| region.overlaps(*other))
        {
            return Err(refuse(
                "overlapping, unaligned or out-of-image patch extent",
            ));
        }
        patchable.push(region);
    }
    let word = |id: InstId| -> Result<u32> {
        let offset = *offsets
            .get(&id)
            .ok_or_else(|| refuse("envelope instruction is not emitted"))?;
        let region = RelativeFrameRegion {
            start: offset as i64,
            end: offset as i64 + 4,
        };
        if patchable.iter().any(|patch| region.overlaps(*patch)) {
            return Err(refuse("pending patch overlaps envelope word"));
        }
        Ok(u32::from_le_bytes(
            image[offset..offset + 4]
                .try_into()
                .expect("four checked bytes"),
        ))
    };
    let entry = &rows.first().ok_or_else(|| refuse("no emitted entry"))?.1;
    if !entry.starts_with(&candidates.prologue) {
        return Err(refuse("prologue is not an entry prefix"));
    }
    let mut used = BTreeSet::new();
    let mut state = State { sp: 0, fp: None };
    let mut slots = Vec::new();
    let mut actual_pairs = BTreeSet::new();
    for &id in &candidates.prologue {
        if !used.insert(id) {
            return Err(refuse("reused envelope instruction"));
        }
        let inst = &machine.insts[id.0 as usize];
        match inst.opcode {
            Op::AddRI | Op::SubRI => {
                if matches!(inst.operands.first(), Some(O::PReg(r)) if r.encoding() == 29)
                    && !slots
                        .iter()
                        .any(|slot: &SavedFrameSlot| slot.register == SavedFrameRegister::X(29))
                {
                    return Err(refuse("FP changed before saving incoming X29"));
                }
                geometry_adjust(inst, word(id)?, &mut state)?;
            }
            Op::StpPreIndex | Op::StpRI => {
                let pair = pair_slots(inst, word(id)?, &mut state)?;
                let mut registers = pair.map(|slot| slot.register);
                registers.sort();
                actual_pairs.insert(registers);
                slots.extend(pair);
            }
            _ => return Err(refuse("prologue contains a non-envelope operation")),
        }
        if state.sp < -total || state.sp > 0 {
            return Err(refuse("prologue SP outside frame"));
        }
    }
    if state.sp != -total || state.fp != claim.uses_frame_pointer.then_some(-16) {
        return Err(refuse("wrong final prologue SP/FP"));
    }
    let mut actual = BTreeSet::new();
    for (index, slot) in slots.iter().enumerate() {
        if !saved_area.contains(slot.region)
            || !actual.insert(slot.register)
            || slots[..index]
                .iter()
                .any(|other| slot.region.overlaps(other.region))
        {
            return Err(refuse("overlapping, duplicate or out-of-region save"));
        }
        if (slot.register == SavedFrameRegister::X(29) && slot.region.start != -16)
            || (slot.register == SavedFrameRegister::X(30) && slot.region.start != -8)
        {
            return Err(refuse("FP/LR do not occupy the canonical top frame record"));
        }
    }
    if actual != expected || slots.len() as i64 * 8 != saved_area.len() {
        return Err(refuse("saved register inventory differs"));
    }
    let claimed_pairs = claim
        .saved_pairs
        .iter()
        .copied()
        .map(|mut pair| {
            pair.sort();
            pair
        })
        .collect();
    if actual_pairs != claimed_pairs {
        return Err(refuse("saved pair grouping differs"));
    }
    if claim.slot_fp_offsets.len() != machine.stack_slots.len() {
        return Err(refuse("missing fixed slot coordinates"));
    }
    let mut storage_slots = Vec::new();
    for (slot, offset) in machine.stack_slots.iter().zip(&claim.slot_fp_offsets) {
        let offset = offset.ok_or_else(|| refuse("non-static slot coordinate"))?;
        if !slot.align.is_power_of_two() || slot.align > 16 {
            return Err(refuse("slot alignment exceeds entry-SP guarantee"));
        }
        let start = state
            .fp
            .ok_or_else(|| refuse("slot without frame pointer"))?
            + i64::from(offset);
        let region = RelativeFrameRegion {
            start,
            end: start + i64::from(slot.size),
        };
        if start % i64::from(slot.align) != 0
            || !stack_slots_area.contains(region)
            || storage_slots.iter().any(|other| region.overlaps(*other))
        {
            return Err(refuse(
                "misaligned, overlapping or out-of-region fixed slot",
            ));
        }
        storage_slots.push(region);
    }
    let after_prologue = state;
    let mut exits = Vec::new();
    let mut returns = BTreeSet::new();
    for epilogue in &candidates.epilogues {
        let ret = *epilogue.last().ok_or_else(|| refuse("empty epilogue"))?;
        if !rows.iter().any(|(_, row)| row.ends_with(epilogue)) {
            return Err(refuse("epilogue is not one emitted block suffix"));
        }
        let mut state = after_prologue;
        let mut restored = BTreeSet::new();
        for &id in epilogue {
            if !used.insert(id) {
                return Err(refuse("overlapping envelopes"));
            }
            let inst = &machine.insts[id.0 as usize];
            match inst.opcode {
                Op::AddRI | Op::SubRI if id != ret => {
                    if matches!(inst.operands.first(), Some(O::PReg(r)) if r.encoding() == 29)
                        && restored.contains(&SavedFrameRegister::X(29))
                    {
                        return Err(refuse("FP changed after restoring incoming X29"));
                    }
                    geometry_adjust(inst, word(id)?, &mut state)?;
                }
                Op::LdpRI | Op::LdpPostIndex if id != ret => {
                    for slot in pair_slots(inst, word(id)?, &mut state)? {
                        if !slots.contains(&slot) || !restored.insert(slot.register) {
                            return Err(refuse("restore differs from actual saved slot"));
                        }
                        if slot.register == SavedFrameRegister::X(29) {
                            state.fp = None;
                        }
                    }
                }
                Op::Ret
                    if id == ret
                        // Return-value liveness uses do not alter geometry.
                        && inst.flags == MachInst::new(Op::Ret, vec![]).flags
                        && inst.implicit_defs.is_empty()
                        && word(id)? == 0xd65f03c0
                        && (inst.operands.is_empty()
                            || matches!(inst.operands.as_slice(), [O::PReg(r)] if r.encoding() == 30)) =>
                    {}
                _ => return Err(refuse("epilogue contains a non-envelope operation")),
            }
            if state.sp < -total || state.sp > 0 {
                return Err(refuse("epilogue SP outside frame"));
            }
        }
        if state.sp != 0 || restored != expected {
            return Err(refuse("incomplete SP/register restore"));
        }
        returns.insert(ret);
        exits.push(ConditionalFrameExit {
            return_instruction: ret,
            required_sp: after_prologue.sp,
            required_fp: after_prologue.fp,
        });
    }
    let actual_returns: BTreeSet<_> = offsets
        .keys()
        .copied()
        .filter(|id| machine.insts[id.0 as usize].opcode == Op::Ret)
        .collect();
    if returns.is_empty() || returns != actual_returns {
        return Err(refuse("missing or extra return envelope"));
    }
    let mut unresolved_body = Vec::new();
    for (block, row) in rows {
        let instructions: Vec<_> = row.into_iter().filter(|id| !used.contains(id)).collect();
        if !instructions.is_empty() {
            let calls = instructions
                .iter()
                .copied()
                .filter(|id| {
                    machine.insts[id.0 as usize]
                        .opcode
                        .default_flags()
                        .is_call()
                })
                .collect();
            unresolved_body.push(UnprovedFrameBodyInterval {
                block,
                instructions,
                calls,
            });
        }
    }
    Ok(CheckedStaticFrameEnvelopes {
        source,
        machine,
        image,
        claim,
        candidates,
        patches,
        saved_area,
        stack_slots_area,
        outgoing_area,
        padding_area,
        slots,
        fixed_slots: storage_slots,
        exits,
        unresolved_body,
        offsets,
    })
}
