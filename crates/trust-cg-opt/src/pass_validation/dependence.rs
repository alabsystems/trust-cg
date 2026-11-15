// trust-cg-opt - Per-pass translation validation: dependence preservation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Dependence-preservation validation of instruction reordering.
//!
//! A scheduler may only permute instructions within a block. This validator
//! checks that it did exactly that, and that the new order keeps every
//! dependence of the old one. The dependences are recomputed here from the
//! instructions alone; nothing is read from the scheduler's DAG.
//!
//! # Structure
//!
//! The block count, layout order, CFG lists and instruction arena length are
//! unchanged, every block's new list is a permutation of its old list, and
//! the arena's behavior digest ([`super::hash_inst`]) is unchanged (so no
//! instruction was rewritten in place).
//!
//! # Dependences
//!
//! For two instructions `a` before `b` in the old order, `b` must stay after
//! `a` when:
//!
//! - **Registers.** One writes a location the other reads or writes. A
//!   location is a virtual register (by id, whatever its class), a
//!   general-purpose or SIMD/FP register unit (`X3`/`W3` are one unit), the
//!   stack pointer, NZCV or a system register. Reads are every register
//!   operand outside a pure-definition position, every `MemOp` base and the
//!   implicit uses; writes are the definition positions and the implicit
//!   definitions (a call is a fence, below, which subsumes its clobbers). NZCV is
//!   written by anything that may clobber it ([`may_clobber_nzcv`]) and read
//!   by the conditional selects, carries and branches ([`reads_nzcv`]).
//!   Two reads never conflict.
//! - **Memory.** Both access memory, unless both are proof-reorderable
//!   ordinary loads, or `a` is a proof-reorderable `StrRI` and `b` a
//!   proof-reorderable `LdrRI` whose byte ranges are disjoint off the same
//!   base register, which no instruction between them redefines.
//! - **Side effects.** Both carry `HAS_SIDE_EFFECTS`.
//! - **Fences.** Either is a call, a memory barrier or a terminator
//!   (including the mid-block trap carriers): nothing crosses it.
//! - **Pre-allocation fixed registers.** `a` reads an allocatable physical
//!   register and `b` defines a virtual register, or `b` writes an
//!   allocatable physical register and `a` defines or uses a virtual
//!   register (the allocator may assign that physical register to the
//!   virtual one).
//!
//! Each rule is checked in time linear in the block: per location the
//! accesses form a chain (every write after the previous write and the reads
//! since it), memory accesses other than reorderable loads form a chain, and
//! the fence and fixed-register rules compare one position with a prefix
//! maximum or suffix minimum.

use crate::fast_hash::FxHashMap as HashMap;
use std::hash::{Hash, Hasher};

use trust_cg_ir::regs::{ALLOCATABLE_FPRS, ALLOCATABLE_GPRS, regs_overlap};
use trust_cg_ir::{
    AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand, PReg,
    SpecialReg,
};

use super::ValidationVerdict;
use crate::effects::{
    aarch64_for_each_def_position, aarch64_for_each_use_position, may_clobber_nzcv, opcode_effect,
    reads_nzcv,
};

/// The block structure and instruction digest before a permutation pass.
#[derive(Debug, Clone)]
pub struct PermutationSnapshot {
    /// Every block's instruction list, concatenated; block `b` is
    /// `insts[offsets[b]..offsets[b + 1]]`.
    insts: Vec<InstId>,
    offsets: Vec<u32>,
    block_order: Vec<BlockId>,
    /// Digest of the CFG lists (`preds`/`succs`) of every block.
    cfg: u64,
    inst_count: usize,
    content: u64,
}

impl PermutationSnapshot {
    /// Capture `func`'s block lists, layout, CFG lists and instruction digest.
    pub fn capture(func: &MachFunction) -> Self {
        let mut insts = Vec::with_capacity(func.insts.len());
        let mut offsets = Vec::with_capacity(func.blocks.len() + 1);
        offsets.push(0);
        for block in &func.blocks {
            insts.extend_from_slice(&block.insts);
            offsets.push(insts.len() as u32);
        }
        Self {
            insts,
            offsets,
            block_order: func.block_order.clone(),
            cfg: cfg_digest(func),
            inst_count: func.insts.len(),
            content: content_digest(func),
        }
    }

    fn block(&self, index: usize) -> &[InstId] {
        &self.insts[self.offsets[index] as usize..self.offsets[index + 1] as usize]
    }

    fn block_count(&self) -> usize {
        self.offsets.len() - 1
    }

    /// Whether `func` still has exactly this structure and these orders.
    pub fn matches(&self, func: &MachFunction) -> bool {
        self.structure_error(func).is_none()
            && func
                .blocks
                .iter()
                .enumerate()
                .all(|(index, block)| self.block(index) == block.insts.as_slice())
    }

    fn structure_error(&self, func: &MachFunction) -> Option<String> {
        if func.blocks.len() != self.block_count() {
            return Some(format!(
                "block count changed from {} to {}",
                self.block_count(),
                func.blocks.len()
            ));
        }
        if func.block_order != self.block_order {
            return Some("block layout order changed".to_string());
        }
        if cfg_digest(func) != self.cfg {
            return Some("a block's CFG lists changed".to_string());
        }
        if func.insts.len() != self.inst_count {
            return Some(format!(
                "instruction arena changed from {} to {} entries",
                self.inst_count,
                func.insts.len()
            ));
        }
        if content_digest(func) != self.content {
            return Some("an instruction was rewritten in place".to_string());
        }
        None
    }
}

/// Digest of every block's predecessor and successor lists.
fn cfg_digest(func: &MachFunction) -> u64 {
    let mut hasher = crate::fast_hash::FxHasher::default();
    for block in &func.blocks {
        block.preds.len().hash(&mut hasher);
        for p in &block.preds {
            p.0.hash(&mut hasher);
        }
        block.succs.len().hash(&mut hasher);
        for s in &block.succs {
            s.0.hash(&mut hasher);
        }
    }
    hasher.finish()
}

/// Digest of every instruction's behavior-relevant fields, in arena order.
fn content_digest(func: &MachFunction) -> u64 {
    let mut hasher = crate::fast_hash::FxHasher::default();
    for inst in &func.insts {
        super::hash_inst(inst, &mut hasher);
    }
    hasher.finish()
}

/// Result of one permutation validation.
#[derive(Debug, Clone)]
pub struct PermutationOutcome {
    /// The verdict.
    pub verdict: ValidationVerdict,
    /// Instructions examined (a deterministic cost measure).
    pub examined: u64,
}

/// Validate that `func` is a dependence-preserving per-block permutation of
/// the function `before` was captured from.
pub fn validate_permutation(
    before: &PermutationSnapshot,
    func: &MachFunction,
) -> PermutationOutcome {
    let mut examined = func.insts.len() as u64 * 2;
    if let Some(error) = before.structure_error(func) {
        return PermutationOutcome {
            verdict: ValidationVerdict::Refuted(error),
            examined,
        };
    }
    for (index, block) in func.blocks.iter().enumerate() {
        let old = before.block(index);
        if old == block.insts.as_slice() {
            continue;
        }
        examined += old.len() as u64;
        if let Err(reason) = check_block(func, BlockId(index as u32), old, &block.insts) {
            return PermutationOutcome {
                verdict: ValidationVerdict::Refuted(reason),
                examined,
            };
        }
    }
    PermutationOutcome {
        verdict: ValidationVerdict::Validated,
        examined,
    }
}

/// A storage location for dependence purposes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum DepLoc {
    VReg(u32),
    Gpr(u8),
    Fpr(u8),
    Sp,
    Flags,
    Sys(u16),
    /// A physical register encoding outside the modeled banks: keyed
    /// exactly.
    Other(u16),
}

/// The architectural unit a physical register encoding names; `None` for
/// the zero registers.
fn preg_loc(preg: PReg) -> Option<DepLoc> {
    let e = preg.encoding();
    Some(match e {
        0..=30 => DepLoc::Gpr(e as u8),
        31 | 63 => DepLoc::Sp,
        32..=62 => DepLoc::Gpr((e - 32) as u8),
        64..=95 => DepLoc::Fpr((e - 64) as u8),
        96..=127 => DepLoc::Fpr((e - 96) as u8),
        128..=159 => DepLoc::Fpr((e - 128) as u8),
        160 | 161 => return None,
        162 => DepLoc::Flags,
        163 | 164 => DepLoc::Sys(e),
        165..=196 => DepLoc::Fpr((e - 165) as u8),
        197..=228 => DepLoc::Fpr((e - 197) as u8),
        _ => DepLoc::Other(e),
    })
}

fn operand_loc(operand: &MachOperand) -> Option<DepLoc> {
    match operand {
        MachOperand::VReg(v) => Some(DepLoc::VReg(v.id)),
        MachOperand::PReg(p) => preg_loc(*p),
        MachOperand::Special(SpecialReg::SP) => Some(DepLoc::Sp),
        MachOperand::Special(SpecialReg::XZR | SpecialReg::WZR) => None,
        MachOperand::MemOp { base, .. } => preg_loc(*base),
        _ => None,
    }
}

fn is_allocatable_alias(preg: PReg) -> bool {
    ALLOCATABLE_GPRS
        .iter()
        .chain(ALLOCATABLE_FPRS.iter())
        .any(|&allocatable| regs_overlap(preg, allocatable))
}

/// How an instruction takes part in memory ordering.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum MemoryRole {
    /// A proof-reorderable ordinary load: unordered against other such
    /// loads.
    ReorderableLoad,
    /// Every other memory access, totally ordered.
    Ordered,
}

/// Everything one instruction reads, writes and orders against. `reads`
/// and `writes` are ranges of the block's shared location buffer.
#[derive(Debug, Default)]
struct Access {
    reads: (u32, u32),
    writes: (u32, u32),
    memory: Option<MemoryRole>,
    side_effect: bool,
    fence: bool,
    vreg_def: bool,
    vreg_use: bool,
    fixed_read: bool,
    fixed_write: bool,
}

impl Access {
    fn reads<'b>(&self, buf: &'b [DepLoc]) -> &'b [DepLoc] {
        &buf[self.reads.0 as usize..self.reads.1 as usize]
    }

    fn writes<'b>(&self, buf: &'b [DepLoc]) -> &'b [DepLoc] {
        &buf[self.writes.0 as usize..self.writes.1 as usize]
    }
}

/// Append `loc` to the buffer unless the run starting at `start` has it.
fn push_unique(buf: &mut Vec<DepLoc>, start: usize, loc: DepLoc) {
    if !buf[start..].contains(&loc) {
        buf.push(loc);
    }
}

fn is_call(inst: &MachInst) -> bool {
    inst.flags
        .union(inst.opcode.default_flags())
        .contains(InstFlags::IS_CALL)
        || matches!(
            inst.opcode,
            AArch64Opcode::Bl | AArch64Opcode::Blr | AArch64Opcode::BL | AArch64Opcode::BLR
        )
}

/// Whether proof-reorderability facts are admitted (the same authority the
/// scheduler and the lowering consult).
fn reorderability_admitted() -> bool {
    cfg!(test) || trust_cg_lower::guard_evidence::validator_guard_replay_authority_available()
}

fn reorderable_load(inst: &MachInst) -> bool {
    use AArch64Opcode::*;
    reorderability_admitted()
        && inst.flags.contains(InstFlags::PROOF_REORDERABLE)
        && inst
            .flags
            .intersection(
                InstFlags::WRITES_MEMORY
                    .union(InstFlags::HAS_SIDE_EFFECTS)
                    .union(InstFlags::IS_CALL),
            )
            .is_empty()
        && matches!(
            inst.opcode,
            LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | LdrRO | LdrswRO | LdrLiteral | LdpRI
        )
}

/// The `(base, offset, bytes)` of a proof-reorderable plain `StrRI`/`LdrRI`
/// whose transfer register is virtual.
fn proven_ri_range(inst: &MachInst, opcode: AArch64Opcode) -> Option<(&MachOperand, i64, i64)> {
    if inst.opcode != opcode || !reorderability_admitted() {
        return None;
    }
    if !inst.flags.contains(InstFlags::PROOF_REORDERABLE) {
        return None;
    }
    let forbidden = if opcode == AArch64Opcode::StrRI {
        if !inst.flags.contains(InstFlags::WRITES_MEMORY) {
            return None;
        }
        InstFlags::READS_MEMORY
            .union(InstFlags::IS_CALL)
            .union(InstFlags::IS_PSEUDO)
    } else {
        InstFlags::WRITES_MEMORY
            .union(InstFlags::HAS_SIDE_EFFECTS)
            .union(InstFlags::IS_CALL)
    };
    if !inst.flags.intersection(forbidden).is_empty() {
        return None;
    }
    let bytes = match inst.operands.first()? {
        MachOperand::VReg(v) => i64::from(v.class.size_bytes()),
        _ => return None,
    };
    let base = inst.operands.get(1)?;
    let offset = inst.operands.get(2)?.as_imm()?;
    (bytes > 0).then_some((base, offset, bytes))
}

fn summarize(inst: &MachInst, buf: &mut Vec<DepLoc>) -> Access {
    let mut access = Access::default();
    let flags = inst.flags.union(inst.opcode.default_flags());
    let call = is_call(inst);
    let effect = opcode_effect(inst.opcode);
    // A `BRK` ends execution whatever its flags say.
    access.fence = call
        || effect.is_barrier()
        || flags.contains(InstFlags::IS_TERMINATOR)
        || inst.opcode == AArch64Opcode::Brk;
    access.side_effect = flags.contains(InstFlags::HAS_SIDE_EFFECTS);
    let touches_memory = effect.reads_memory()
        || effect.writes_memory()
        || effect.is_barrier()
        || flags.contains(InstFlags::READS_MEMORY)
        || flags.contains(InstFlags::WRITES_MEMORY)
        || call;
    if touches_memory {
        access.memory = Some(if reorderable_load(inst) {
            MemoryRole::ReorderableLoad
        } else {
            MemoryRole::Ordered
        });
    }
    let start = buf.len() as u32;
    access.reads = (start, start);
    access.writes = (start, start);
    if access.fence {
        // Nothing crosses a fence, which subsumes its register dependences.
        return access;
    }

    let mut def_mask = 0u64;
    aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| {
        if pos < 64 {
            def_mask |= 1 << pos;
        }
    });
    let mut use_mask = 0u64;
    aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
        if pos < 64 {
            use_mask |= 1 << pos;
        }
    });
    // Reads first, then writes, each deduplicated within its own run.
    let reads_start = buf.len();
    for (pos, operand) in inst.operands.iter().enumerate() {
        let bit = if pos < 64 { 1u64 << pos } else { 0 };
        let is_def = def_mask & bit != 0;
        // A register outside every role position is still treated as read.
        let is_read = !is_def || use_mask & bit != 0;
        if let MachOperand::MemOp { base, .. } = operand {
            if let Some(loc) = operand_loc(operand) {
                push_unique(buf, reads_start, loc);
            }
            if is_allocatable_alias(*base) {
                access.fixed_read = true;
            }
            continue;
        }
        if !is_read {
            continue;
        }
        let Some(loc) = operand_loc(operand) else {
            continue;
        };
        push_unique(buf, reads_start, loc);
        match operand {
            MachOperand::VReg(_) => access.vreg_use = true,
            MachOperand::PReg(p) if is_allocatable_alias(*p) => access.fixed_read = true,
            _ => {}
        }
    }
    for &preg in inst.implicit_uses {
        if let Some(loc) = preg_loc(preg) {
            push_unique(buf, reads_start, loc);
        }
        if is_allocatable_alias(preg) {
            access.fixed_read = true;
        }
    }
    if reads_nzcv(inst) {
        push_unique(buf, reads_start, DepLoc::Flags);
    }
    let writes_start = buf.len();
    for (pos, operand) in inst.operands.iter().enumerate() {
        let bit = if pos < 64 { 1u64 << pos } else { 0 };
        if def_mask & bit == 0 || matches!(operand, MachOperand::MemOp { .. }) {
            continue;
        }
        let Some(loc) = operand_loc(operand) else {
            continue;
        };
        push_unique(buf, writes_start, loc);
        match operand {
            MachOperand::VReg(_) => access.vreg_def = true,
            MachOperand::PReg(p) if is_allocatable_alias(*p) => access.fixed_write = true,
            _ => {}
        }
    }
    for &preg in inst.implicit_defs {
        if let Some(loc) = preg_loc(preg) {
            push_unique(buf, writes_start, loc);
        }
        if is_allocatable_alias(preg) {
            access.fixed_write = true;
        }
    }
    if may_clobber_nzcv(inst) {
        push_unique(buf, writes_start, DepLoc::Flags);
    }
    access.reads = (reads_start as u32, writes_start as u32);
    access.writes = (writes_start as u32, buf.len() as u32);
    access
}

/// Per-location chain state: the last write and the latest-placed read
/// since it, as `(old index, new position)`.
#[derive(Default)]
struct Chain {
    last_write: Option<(usize, usize)>,
    latest_read: Option<(usize, usize)>,
}

fn describe(func: &MachFunction, ids: &[InstId], index: usize) -> String {
    let id = ids[index];
    format!("#{} {:?} (inst {})", index, func.inst(id).opcode, id.0)
}

fn check_block(
    func: &MachFunction,
    block: BlockId,
    old: &[InstId],
    new: &[InstId],
) -> Result<(), String> {
    let n = old.len();
    if new.len() != n {
        return Err(format!(
            "block {} changed length from {} to {}",
            block.0,
            n,
            new.len()
        ));
    }
    let mut position: HashMap<InstId, usize> = HashMap::default();
    position.reserve(n);
    for (pos, &id) in new.iter().enumerate() {
        if position.insert(id, pos).is_some() {
            return Err(format!("block {} lists inst {} twice", block.0, id.0));
        }
    }
    let mut new_pos = Vec::with_capacity(n);
    for &id in old {
        match position.get(&id) {
            Some(&pos) => new_pos.push(pos),
            None => {
                return Err(format!(
                    "block {} lost inst {} ({:?})",
                    block.0,
                    id.0,
                    func.inst(id).opcode
                ));
            }
        }
    }

    let mut buf: Vec<DepLoc> = Vec::with_capacity(n * 3);
    let accesses: Vec<Access> = old
        .iter()
        .map(|&id| summarize(func.inst(id), &mut buf))
        .collect();
    let violation = |kind: &str, earlier: usize, later: usize| -> String {
        format!(
            "block {}: {kind} dependence reversed: {} must stay before {}",
            block.0,
            describe(func, old, earlier),
            describe(func, old, later)
        )
    };

    // Registers and NZCV: per-location chains.
    let mut chains: HashMap<DepLoc, Chain> = HashMap::default();
    for (index, access) in accesses.iter().enumerate() {
        let here = new_pos[index];
        for loc in access.reads(&buf) {
            let chain = chains.entry(*loc).or_default();
            if let Some((w, wpos)) = chain.last_write
                && wpos > here
            {
                return Err(violation(&format!("{loc:?} read-after-write"), w, index));
            }
            if chain.latest_read.is_none_or(|(_, rpos)| here > rpos) {
                chain.latest_read = Some((index, here));
            }
        }
        for loc in access.writes(&buf) {
            let chain = chains.entry(*loc).or_default();
            if let Some((w, wpos)) = chain.last_write
                && wpos > here
            {
                return Err(violation(&format!("{loc:?} write-after-write"), w, index));
            }
            if let Some((r, rpos)) = chain.latest_read
                && r != index
                && rpos > here
            {
                return Err(violation(&format!("{loc:?} write-after-read"), r, index));
            }
            chain.last_write = Some((index, here));
            chain.latest_read = None;
        }
    }

    // Memory: ordered accesses chain; a reorderable load stays after the
    // latest ordered access it may depend on and before the next one.
    let mut ordered: Vec<usize> = Vec::new();
    for (index, access) in accesses.iter().enumerate() {
        match access.memory {
            None => {}
            Some(MemoryRole::Ordered) => {
                if let Some(&prev) = ordered.last()
                    && new_pos[prev] > new_pos[index]
                {
                    return Err(violation("memory", prev, index));
                }
                ordered.push(index);
            }
            Some(MemoryRole::ReorderableLoad) => {
                let load = func.inst(old[index]);
                if let Some(&prev) = ordered.iter().rev().find(|&&prev| {
                    !store_load_disjoint(func, old, &accesses, &buf, prev, index, load)
                }) && new_pos[prev] > new_pos[index]
                {
                    return Err(violation("memory", prev, index));
                }
            }
        }
    }
    // The next ordered access after each reorderable load.
    let mut next_ordered: Option<usize> = None;
    for index in (0..n).rev() {
        match accesses[index].memory {
            Some(MemoryRole::Ordered) => next_ordered = Some(index),
            Some(MemoryRole::ReorderableLoad) => {
                if let Some(next) = next_ordered
                    && new_pos[index] > new_pos[next]
                {
                    return Err(violation("memory", index, next));
                }
            }
            _ => {}
        }
    }

    // Side effects chain.
    let mut last_effect: Option<usize> = None;
    for (index, access) in accesses.iter().enumerate() {
        if access.side_effect {
            if let Some(prev) = last_effect
                && new_pos[prev] > new_pos[index]
            {
                return Err(violation("side-effect", prev, index));
            }
            last_effect = Some(index);
        }
    }

    // Fences: the set placed before a fence is exactly the old prefix. With
    // a permutation that holds iff the fence keeps its index and every
    // earlier instruction stays below it.
    let mut prefix_max: Option<usize> = None;
    for (index, access) in accesses.iter().enumerate() {
        if access.fence
            && (new_pos[index] != index || prefix_max.is_some_and(|pmax| pmax > new_pos[index]))
        {
            let crossing = (0..n)
                .find(|&j| j != index && (j < index) != (new_pos[j] < new_pos[index]))
                .unwrap_or(index);
            let (earlier, later) = if crossing < index {
                (crossing, index)
            } else {
                (index, crossing)
            };
            return Err(violation("fence", earlier, later));
        }
        if prefix_max.is_none_or(|pmax| new_pos[index] > pmax) {
            prefix_max = Some(new_pos[index]);
        }
    }

    // Pre-allocation fixed registers.
    let mut vreg_touch_max: Option<(usize, usize)> = None;
    for (index, access) in accesses.iter().enumerate() {
        if access.fixed_write
            && let Some((i, pmax)) = vreg_touch_max
            && pmax > new_pos[index]
        {
            return Err(violation("fixed-register", i, index));
        }
        if (access.vreg_def || access.vreg_use)
            && vreg_touch_max.is_none_or(|(_, pmax)| new_pos[index] > pmax)
        {
            vreg_touch_max = Some((index, new_pos[index]));
        }
    }
    let mut vreg_def_min: Option<(usize, usize)> = None;
    for index in (0..n).rev() {
        let access = &accesses[index];
        if access.fixed_read
            && let Some((j, smin)) = vreg_def_min
            && smin < new_pos[index]
        {
            return Err(violation("fixed-register", index, j));
        }
        if access.vreg_def && vreg_def_min.is_none_or(|(_, smin)| new_pos[index] < smin) {
            vreg_def_min = Some((index, new_pos[index]));
        }
    }
    Ok(())
}

/// Whether the ordered access at old index `store` provably writes bytes
/// disjoint from what the reorderable load at old index `load` reads: a
/// proof-reorderable `StrRI` and `LdrRI` off the same base register, which
/// nothing between them redefines, with non-overlapping byte ranges.
fn store_load_disjoint(
    func: &MachFunction,
    old: &[InstId],
    accesses: &[Access],
    buf: &[DepLoc],
    store: usize,
    load: usize,
    load_inst: &MachInst,
) -> bool {
    let store_inst = func.inst(old[store]);
    let Some((store_base, store_off, store_bytes)) =
        proven_ri_range(store_inst, AArch64Opcode::StrRI)
    else {
        return false;
    };
    let Some((load_base, load_off, load_bytes)) = proven_ri_range(load_inst, AArch64Opcode::LdrRI)
    else {
        return false;
    };
    if store_base != load_base {
        return false;
    }
    let Some(base_loc) = operand_loc(store_base) else {
        return false;
    };
    if !matches!(store_base, MachOperand::VReg(_) | MachOperand::PReg(_)) {
        return false;
    }
    // The base must hold one value from the store through the load.
    let redefined = accesses[store + 1..load]
        .iter()
        .any(|access| access.fence || access.writes(buf).contains(&base_loc));
    if redefined {
        return false;
    }
    let (Some(store_end), Some(load_end)) = (
        store_off.checked_add(store_bytes),
        load_off.checked_add(load_bytes),
    ) else {
        return false;
    };
    store_end <= load_off || load_end <= store_off
}
