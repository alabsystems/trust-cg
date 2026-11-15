// trust-cg-opt - Per-pass translation validation: code-motion side conditions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Validation of loop-invariant code motion.
//!
//! LICM moves instructions (the same `InstId`, unchanged) from loop blocks to
//! the loop's preheader. A run is validated in two parts:
//!
//! 1. **Side conditions of every move**, checked on the input function's
//!    instruction-derived CFG (its own dominators and natural loops, not the
//!    pass's analyses). An instruction moved from block `L` to block `P`:
//!    - `P` is the loop's only entry (its sole successor is the header `H`,
//!      and `H`'s other predecessors are inside the loop) and `L` is in the
//!      loop;
//!    - it neither touches NZCV nor writes anything but virtual registers,
//!      and is either free of memory and effects or a plain load;
//!    - every register it reads is written nowhere in the loop except by
//!      instructions moved ahead of it into `P`, and nowhere in `P` after its
//!      new position;
//!    - every register it writes has no other writer in the loop, is not live
//!      into `H` (no iteration reads the value from before the loop), is not
//!      read or written by `P`'s own instructions after it, and is not live
//!      into a loop exit unless `L` dominates every exiting block. A register
//!      only moved instructions write is exempt from the liveness conditions
//!      (an early read in the input read an undefined register) only when
//!      `P` lies on no cycle: in an outer loop the input's early read sees
//!      the value an earlier visit left;
//!    - a load reads memory nothing in the loop writes, and nothing in `P`
//!      after it writes. The only writer admitted is a bounded direct access
//!      to a different fixed-size stack slot than the load's, itself
//!      bounded: both addresses resolve to their slots and every byte either
//!      touches lies inside its slot's allocation. Distinct symbols, a slot
//!      against a global, or an access whose bytes are not bounded are not
//!      taken as disjoint (OD-127), nor is a call or barrier;
//!    - an instruction that can fault (a load) either reads inside one
//!      fixed-size stack slot, or is guaranteed to execute: `L` dominates
//!      every latch and every exiting block, and nothing on a path from `H`
//!      to it can end execution first (a call, a trap carrier, `BRK`);
//!    - when `P` is an invoke block, an exception taken after the new
//!      position reaches `L` only through `P` again, and none taken before
//!      it reaches a landing pad that reads what it writes
//!      (`check_exception_edges`).
//! 2. **Everything else is unchanged**: every block a move left is exactly
//!    its input list minus the moved instructions (no deletion, insertion
//!    or replacement beside the moves), no instruction is laid out twice,
//!    and with every moved instruction put back the function must pass
//!    [`super::region::validate_regions`].
//!
//! Together these are the classic LICM correctness argument: the moved
//! value is the same on every iteration and on the first, it is computed
//! only where it cannot fault or would have faulted anyway, and no reader
//! observes the earlier definition.
//!
//! LICM also places pure values in blocks that are not a loop's
//! straight-line entry: a guard preheader that branches around the loop,
//! or the block ahead of an earlier loop the path to this one runs through.
//! When the loop shape does not hold, a pure value whose registers only
//! moved instructions write is checked as a **dominating move**
//! (`check_dominating_move`): the target dominates the source, the moved
//! instruction precedes every exit of the target, no instruction on a path
//! from the target to the source writes an operand, and no reader can see
//! the definition before the source would have made it. The input CFG
//! includes the exception edges ([`super::region::Cfg`]), so dominance and
//! liveness account for landing pads, and the exception-handling metadata
//! must be unchanged. A call can leave an invoke block mid-way through its
//! exception edge, so "precedes every exit of the target" counts a call in
//! an invoke target as an exit when a landing pad reaches the source without
//! passing the target.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use trust_cg_ir::function::StackSlotAllocationKind;
use trust_cg_ir::{AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand};

use super::ValidationVerdict;
use super::region::{Cfg, Liveness, RegionOutcome, Shape, inst_eq, validate_regions};
use super::semantics::{base_offset_access, for_each_access, instruction_access};
use super::term::Loc;
use crate::effects::{MemoryEffect, may_clobber_nzcv, opcode_effect, reads_nzcv};

/// Validate a code-motion run.
pub(super) fn validate_hoists(before: &MachFunction, after: &MachFunction) -> RegionOutcome {
    let mut examined = 0u64;
    let verdict = match check(before, after, &mut examined) {
        Ok(()) => ValidationVerdict::Validated,
        Err(reason) => ValidationVerdict::Unproved(reason),
    };
    RegionOutcome { verdict, examined }
}

/// `(block, index)` of every laid-out instruction. An instruction laid out
/// twice (a copy rather than a move) is not a code-motion run.
fn placements(func: &MachFunction) -> Result<HashMap<InstId, (BlockId, usize)>, String> {
    let mut map = HashMap::default();
    for &b in &func.block_order {
        if let Some(block) = func.blocks.get(b.0 as usize) {
            for (i, &id) in block.insts.iter().enumerate() {
                if map.insert(id, (b, i)).is_some() {
                    return Err(format!("inst {} is laid out more than once", id.0));
                }
            }
        }
    }
    Ok(map)
}

/// Immediate dominators over the instruction-derived CFG (Cooper, Harvey
/// and Kennedy), for reachable blocks.
struct Dominators {
    idom: HashMap<BlockId, BlockId>,
    entry: BlockId,
}

impl Dominators {
    fn compute(cfg: &Cfg, entry: BlockId) -> Self {
        // Reverse postorder.
        let mut order = Vec::new();
        let mut seen: HashSet<BlockId> = HashSet::default();
        let mut stack: Vec<(BlockId, usize)> = vec![(entry, 0)];
        seen.insert(entry);
        while let Some((b, i)) = stack.pop() {
            let succs = cfg.successors(b).to_vec();
            if i < succs.len() {
                stack.push((b, i + 1));
                let s = succs[i];
                if seen.insert(s) {
                    stack.push((s, 0));
                }
            } else {
                order.push(b);
            }
        }
        order.reverse();
        let rpo: HashMap<BlockId, usize> = order.iter().enumerate().map(|(i, b)| (*b, i)).collect();
        let mut idom: HashMap<BlockId, BlockId> = HashMap::default();
        idom.insert(entry, entry);
        let mut changed = true;
        while changed {
            changed = false;
            for &b in order.iter().skip(1) {
                let mut new: Option<BlockId> = None;
                for &p in cfg.preds.get(&b).into_iter().flatten() {
                    if !idom.contains_key(&p) || !rpo.contains_key(&p) {
                        continue;
                    }
                    new = Some(match new {
                        None => p,
                        Some(mut a) => {
                            let mut c = p;
                            while a != c {
                                while rpo[&a] > rpo[&c] {
                                    a = idom[&a];
                                }
                                while rpo[&c] > rpo[&a] {
                                    c = idom[&c];
                                }
                            }
                            a
                        }
                    });
                }
                if let Some(n) = new
                    && idom.get(&b) != Some(&n)
                {
                    idom.insert(b, n);
                    changed = true;
                }
            }
        }
        Self { idom, entry }
    }

    fn dominates(&self, a: BlockId, mut b: BlockId) -> bool {
        loop {
            if a == b {
                return true;
            }
            if b == self.entry {
                return false;
            }
            match self.idom.get(&b) {
                Some(&p) if p != b => b = p,
                _ => return false,
            }
        }
    }
}

/// The natural loop with header `header`: the header plus every block that
/// reaches a back edge into it without passing through it.
fn natural_loop(
    cfg: &Cfg,
    dom: &Dominators,
    header: BlockId,
) -> Option<(HashSet<BlockId>, Vec<BlockId>)> {
    let latches: Vec<BlockId> = cfg
        .preds
        .get(&header)
        .into_iter()
        .flatten()
        .copied()
        .filter(|&p| cfg.reachable.contains(&p) && dom.dominates(header, p))
        .collect();
    if latches.is_empty() {
        return None;
    }
    let mut body: HashSet<BlockId> = HashSet::default();
    body.insert(header);
    let mut stack = latches.clone();
    while let Some(b) = stack.pop() {
        if body.insert(b) {
            stack.extend(cfg.preds.get(&b).into_iter().flatten().copied());
        }
    }
    Some((body, latches))
}

/// Single-writer facts of one function.
struct Writers<'f> {
    func: &'f MachFunction,
    /// Every instruction writing each virtual register.
    writers: HashMap<Loc, Vec<InstId>>,
    placements: &'f HashMap<InstId, (BlockId, usize)>,
    dom: &'f Dominators,
}

/// A position: `(block, index)`.
type At = (BlockId, usize);

fn is_self_copy(inst: &MachInst) -> bool {
    matches!(inst.opcode, AArch64Opcode::MovR | AArch64Opcode::Copy)
        && matches!(
            inst.operands.as_slice(),
            [MachOperand::VReg(d), MachOperand::VReg(s)] if d.id == s.id
        )
}

impl<'f> Writers<'f> {
    /// Every writer of every virtual register.
    fn new(
        func: &'f MachFunction,
        placements: &'f HashMap<InstId, (BlockId, usize)>,
        dom: &'f Dominators,
    ) -> Self {
        let mut writers: HashMap<Loc, Vec<InstId>> = HashMap::default();
        for &b in &func.block_order {
            for &id in &func.block(b).insts {
                for_each_access(func.inst(id), |loc, write| {
                    if write && matches!(loc, Loc::VReg(_)) {
                        let list = writers.entry(loc).or_default();
                        if list.last() != Some(&id) {
                            list.push(id);
                        }
                    }
                });
            }
        }
        Self {
            func,
            writers,
            placements,
            dom,
        }
    }

    /// The one definition of `op`'s value (self-copies, which keep it, aside)
    /// when it dominates `at`, and its position.
    fn single_def(&self, op: &MachOperand, at: At) -> Option<(&'f MachInst, At)> {
        let MachOperand::VReg(v) = op else {
            return None;
        };
        let mut defs = self
            .writers
            .get(&Loc::VReg(v.id))?
            .iter()
            .filter(|&&id| !is_self_copy(self.func.inst(id)));
        let id = *defs.next()?;
        if defs.next().is_some() {
            return None;
        }
        let inst = self.func.inst(id);
        if inst.operands.first() != Some(op) {
            return None;
        }
        let def_at = *self.placements.get(&id)?;
        let dominates = if def_at.0 == at.0 {
            def_at.1 < at.1
        } else {
            self.dom.dominates(def_at.0, at.0)
        };
        dominates.then_some((inst, def_at))
    }

    fn constant(&self, op: &MachOperand, at: At) -> Option<i64> {
        let (def, _) = self.single_def(op, at)?;
        match (def.opcode, def.operands.as_slice()) {
            (AArch64Opcode::MovI | AArch64Opcode::Movz, [_, MachOperand::Imm(c)]) => Some(*c),
            _ => None,
        }
    }

    /// The stack slot and byte offset a 64-bit address operand holds at
    /// `at`, through dominating single definitions: the slot's frame
    /// address, copies, immediate adds and constant-index products. No other
    /// object is resolved: a symbol's address is never an alias root
    /// (OD-127).
    fn resolve(&self, op: &MachOperand, at: At, fuel: u32) -> Option<(u32, i64)> {
        if fuel == 0 {
            return None;
        }
        if let MachOperand::StackSlot(s) = op {
            return Some((s.0, 0));
        }
        let (def, def_at) = self.single_def(op, at)?;
        match (def.opcode, def.operands.as_slice()) {
            (AArch64Opcode::AddPCRel, [_, base, MachOperand::StackSlot(s)])
                if matches!(base, MachOperand::Special(trust_cg_ir::SpecialReg::SP))
                    || matches!(base, MachOperand::PReg(p) if p.encoding() == 31) =>
            {
                Some((s.0, 0))
            }
            (AArch64Opcode::MovR | AArch64Opcode::Copy, [_, src]) => {
                self.resolve(src, def_at, fuel - 1)
            }
            (AArch64Opcode::AddRI, [_, src, MachOperand::Imm(k)]) => {
                let (root, off) = self.resolve(src, def_at, fuel - 1)?;
                Some((root, off.checked_add(*k)?))
            }
            (AArch64Opcode::SubRI, [_, src, MachOperand::Imm(k)]) => {
                let (root, off) = self.resolve(src, def_at, fuel - 1)?;
                Some((root, off.checked_sub(*k)?))
            }
            (AArch64Opcode::Madd, [_, x, y, src]) => {
                let product = self
                    .constant(x, def_at)?
                    .checked_mul(self.constant(y, def_at)?)?;
                let (root, off) = self.resolve(src, def_at, fuel - 1)?;
                Some((root, off.checked_add(product)?))
            }
            _ => None,
        }
    }

    /// The fixed-size stack slot a plain base-plus-immediate access (scalar
    /// or pair) at `at` stays inside: its base resolves to the slot and every
    /// byte it reads or writes lies within the slot's allocation. Such an
    /// access cannot fault anywhere in the activation, and two of them in
    /// different slots touch no byte in common.
    fn bounded_slot_access(&self, inst: &MachInst, at: At) -> Option<u32> {
        let (base, offset, bytes) = base_offset_access(inst)?;
        let (slot, base_offset) = self.resolve(base, at, 8)?;
        let info = self.func.stack_slots.get(slot as usize)?;
        if info.allocation != StackSlotAllocationKind::Fixed || info.size == 0 {
            return None;
        }
        let start = base_offset.checked_add(offset)?;
        let end = start.checked_add(i64::try_from(bytes).ok()?)?;
        (start >= 0 && end <= i64::from(info.size)).then_some(slot)
    }
}

fn plain_load(inst: &MachInst) -> bool {
    let flags = inst.flags.union(inst.opcode.default_flags());
    opcode_effect(inst.opcode) == MemoryEffect::Load
        && flags
            .intersection(
                InstFlags::WRITES_MEMORY
                    .union(InstFlags::HAS_SIDE_EFFECTS)
                    .union(InstFlags::IS_CALL)
                    .union(InstFlags::IS_BRANCH)
                    .union(InstFlags::IS_TERMINATOR),
            )
            .is_empty()
        && matches!(
            inst.opcode,
            AArch64Opcode::LdrRI
                | AArch64Opcode::LdrbRI
                | AArch64Opcode::LdrhRI
                | AArch64Opcode::LdrsbRI
                | AArch64Opcode::LdrshRI
        )
}

fn pure_value(inst: &MachInst) -> bool {
    let flags = inst.flags.union(inst.opcode.default_flags());
    opcode_effect(inst.opcode).is_pure()
        && flags
            .intersection(
                InstFlags::HAS_SIDE_EFFECTS
                    .union(InstFlags::IS_CALL)
                    .union(InstFlags::IS_BRANCH)
                    .union(InstFlags::IS_TERMINATOR)
                    .union(InstFlags::READS_MEMORY)
                    .union(InstFlags::WRITES_MEMORY),
            )
            .is_empty()
}

fn writes_memory(inst: &MachInst) -> bool {
    let flags = inst.flags.union(inst.opcode.default_flags());
    let effect = opcode_effect(inst.opcode);
    effect.writes_memory()
        || effect.is_barrier()
        || flags.contains(InstFlags::WRITES_MEMORY)
        || flags.contains(InstFlags::IS_CALL)
}

/// Whether executing `inst` can end execution before what follows it: a
/// call, a trap carrier, `BRK` or anything else that is a terminator.
fn may_end_execution(inst: &MachInst) -> bool {
    let flags = inst.flags.union(inst.opcode.default_flags());
    flags.contains(InstFlags::IS_CALL)
        || flags.contains(InstFlags::IS_TERMINATOR)
        || inst.opcode == AArch64Opcode::Brk
}

/// Whether `x` can leave its block mid-way, through the block's exception
/// edge when it is an invoke block: a call, or anything else that can end
/// execution before what follows it (a trap carrier, `BRK`), the block's
/// own exit branches aside.
fn may_leave_mid_block(func: &MachFunction, x: InstId) -> bool {
    may_end_execution(func.inst(x)) && !is_block_exit(func, x)
}

/// The exception edges of an invoke target `P` (none for any other block).
///
/// - Placed after an instruction that may raise, the moved instruction does
///   not run when that instruction takes the edge. That is sound only when
///   no landing pad of `P` reaches the source block without passing `P`
///   again (whose next run, if it leaves normally, runs it).
/// - Placed ahead of one, it runs before the landing pad does, which the
///   input did not: no register it writes may be live into a pad of `P`.
fn check_exception_edges(
    f: &MoveFacts<'_>,
    target: BlockId,
    position: usize,
    source: BlockId,
    writes: &[Loc],
) -> Result<(), String> {
    let Some(pads) = f.bc.eh_succs.get(&target) else {
        return Ok(());
    };
    let target_insts = &f.after.block(target).insts;
    if let Some(&x) = target_insts[..position]
        .iter()
        .find(|&&x| may_leave_mid_block(f.after, x))
    {
        let from_pads = reach(
            pads.iter().copied(),
            |b| f.bc.successors(b).to_vec(),
            &[target],
        );
        if from_pads.contains(&source) {
            return Err(format!(
                "it follows inst {} ({:?}), whose exception edge leaves invoke block {} for a \
                 landing pad that reaches block {} without it",
                x.0,
                f.after.inst(x).opcode,
                target.0,
                source.0
            ));
        }
    }
    if target_insts[position + 1..]
        .iter()
        .any(|&x| may_leave_mid_block(f.after, x))
    {
        for loc in writes {
            if let Some(&pad) = pads.iter().find(|&&pad| f.live.is_live(pad, *loc)) {
                return Err(format!(
                    "{loc:?} is live into landing pad {}, which an exception after it in invoke \
                     block {} reaches",
                    pad.0, target.0
                ));
            }
        }
    }
    Ok(())
}

fn check(before: &MachFunction, after: &MachFunction, examined: &mut u64) -> Result<(), String> {
    let pb = placements(before)?;
    let pa = placements(after)?;
    let mut moved: Vec<InstId> = pb
        .iter()
        .filter(|(id, (b, _))| pa.get(id).is_some_and(|(a, _)| a != b))
        .map(|(id, _)| *id)
        .collect();
    moved.sort_unstable();
    if moved.is_empty() {
        let outcome = validate_regions(before, after);
        *examined += outcome.examined;
        return match outcome.verdict {
            ValidationVerdict::Validated => Ok(()),
            other => Err(other.reason().unwrap_or("not shown").to_string()),
        };
    }
    let moved_set: HashSet<InstId> = moved.iter().copied().collect();

    // Put every moved instruction back: each source block must be exactly
    // its input list minus the moved instructions.
    for &id in &moved {
        if !inst_eq(before.inst(id), after.inst(id)) {
            return Err(format!("moved inst {} was also rewritten", id.0));
        }
    }
    // Apart from the moves, every block keeps its list: undoing the moves
    // gives back the input's lists. (A block may both lose and gain moved
    // instructions: an inner loop's preheader inside an outer loop.)
    let same_layout = before.entry == after.entry
        && before.block_order == after.block_order
        && before.blocks.len() == after.blocks.len()
        && before.stack_slots == after.stack_slots
        && super::region::same_eh_metadata(before, after);
    let without_moves = |list: &[InstId]| -> Vec<InstId> {
        list.iter()
            .copied()
            .filter(|id| !moved_set.contains(id))
            .collect()
    };
    // A source block is put back by restoring its input list, which is
    // exact only when nothing else in it changed: a deletion or a
    // replacement there would otherwise vanish from the undone function.
    let sources: HashSet<BlockId> = moved.iter().map(|id| pb[id].0).collect();
    let mut sources_sorted: Vec<BlockId> = sources.iter().copied().collect();
    sources_sorted.sort_unstable_by_key(|b| b.0);
    for &b in &sources_sorted {
        if !after.block_order.contains(&b) || after.blocks.get(b.0 as usize).is_none() {
            return Err(format!("source block {} is gone from the output", b.0));
        }
        if without_moves(&before.block(b).insts) != without_moves(&after.block(b).insts) {
            return Err(format!(
                "source block {} changed besides the moved instructions",
                b.0
            ));
        }
    }
    let lists_match = same_layout
        && before.block_order.iter().all(|&b| {
            without_moves(&before.block(b).insts) == without_moves(&after.block(b).insts)
        });
    if !lists_match {
        // Something besides the moves changed outside the source blocks:
        // check the undone function.
        let mut restored = after.clone();
        for &b in &after.block_order {
            let list = if sources.contains(&b) {
                before.block(b).insts.clone()
            } else {
                without_moves(&after.block(b).insts)
            };
            restored.block_mut(b).insts = list;
        }
        let outcome = validate_regions(before, &restored);
        *examined += outcome.examined;
        if let ValidationVerdict::Unproved(reason) | ValidationVerdict::Refuted(reason) =
            outcome.verdict
        {
            return Err(format!("with the moves undone: {reason}"));
        }
    } else if let Some(id) = before.block_order.iter().find_map(|&b| {
        before
            .block(b)
            .insts
            .iter()
            .copied()
            .find(|&id| !inst_eq(before.inst(id), after.inst(id)))
    }) {
        return Err(format!("inst {} was rewritten in place", id.0));
    }

    let bc = Cfg::build(before);
    let ac = Cfg::build(after);
    let dom = Dominators::compute(&bc, before.entry);
    let mut interest: Vec<Loc> = Vec::new();
    for &id in &moved {
        for_each_access(before.inst(id), |loc, write| {
            if write && !interest.contains(&loc) {
                interest.push(loc);
            }
        });
    }
    let live = Liveness::compute(before, &bc, &interest);
    // Values are resolved in the output, where the moved instructions now
    // run (its CFG is the input's: only instructions moved).
    let writers = Writers::new(after, &pa, &dom);
    let facts = MoveFacts {
        before,
        after,
        bc: &bc,
        ac: &ac,
        dom: &dom,
        live: &live,
        writers: &writers,
        moved: &moved_set,
        pa: &pa,
        pb: &pb,
    };
    for &id in &moved {
        *examined += 1;
        check_move(&facts, id)
            .or_else(|loop_reason| {
                // The loop-preheader shape did not hold. A pure value whose
                // registers only moved instructions write may still have
                // moved to any block that dominates its source (a guard
                // preheader, or ahead of an earlier loop): check that move
                // on its own terms when nothing but moves changed.
                if !lists_match {
                    return Err(loop_reason);
                }
                check_dominating_move(&facts, id)
                    .map_err(|general| format!("{loop_reason}; as a dominating move: {general}"))
            })
            .map_err(|e| format!("moved inst {} ({:?}): {e}", id.0, before.inst(id).opcode))?;
    }
    Ok(())
}

/// What every move check reads.
struct MoveFacts<'a> {
    before: &'a MachFunction,
    after: &'a MachFunction,
    /// The input's CFG (with its exception edges); the output's is the same
    /// when only instructions moved.
    bc: &'a Cfg,
    ac: &'a Cfg,
    dom: &'a Dominators,
    /// Input liveness of every location a moved instruction writes.
    live: &'a Liveness,
    /// Writers and single definitions of the output.
    writers: &'a Writers<'a>,
    moved: &'a HashSet<InstId>,
    pa: &'a HashMap<InstId, (BlockId, usize)>,
    pb: &'a HashMap<InstId, (BlockId, usize)>,
}

/// Blocks reachable from `starts` without entering a block of `stop`.
fn reach(
    starts: impl IntoIterator<Item = BlockId>,
    next: impl Fn(BlockId) -> Vec<BlockId>,
    stop: &[BlockId],
) -> HashSet<BlockId> {
    let mut seen: HashSet<BlockId> = HashSet::default();
    let mut stack: Vec<BlockId> = starts.into_iter().filter(|b| !stop.contains(b)).collect();
    while let Some(b) = stack.pop() {
        if !seen.insert(b) {
            continue;
        }
        stack.extend(next(b).into_iter().filter(|s| !stop.contains(s)));
    }
    seen
}

/// A pure value moved to a block `P` that dominates its source block `S`,
/// shown without assuming `P` is a loop preheader:
///
/// - **the value is the same**: no instruction on a path from `P` to `S`
///   that does not pass `P` again (the region `R`, `S` included) writes an
///   operand, except an earlier moved writer that now precedes it in `P`
///   and ran before it in the input, and nothing after it in `P` does; so
///   every execution of it in `S` computed what the latest `P` computes;
/// - **no reader sees the earlier definition**: every register it writes is
///   written only by moved instructions, is not live into `P` in the input,
///   is not read in `S` ahead of it, is not live into any block reachable
///   from `P` without passing `S`, and is not touched after it in `P`. So
///   every read of the register follows an execution of the instruction in
///   `S` since the latest `P`, which computed the same value; a read with no
///   such execution read an undefined register in the input, which the
///   earlier definition refines.
///
/// It must sit ahead of every exit of `P` (so it runs whenever `P` does),
/// be free of memory, effects, NZCV and implicit registers and write only
/// virtual registers, so running it on paths where `S` does not run cannot
/// fault or be observed.
fn check_dominating_move(f: &MoveFacts<'_>, id: InstId) -> Result<(), String> {
    let inst = f.before.inst(id);
    let source = f.pb[&id].0;
    let (target, position) = f.pa[&id];
    if reads_nzcv(inst) || may_clobber_nzcv(inst) {
        return Err("it reads or writes NZCV".to_string());
    }
    if !pure_value(inst) {
        return Err("it is not a pure value".to_string());
    }
    if !inst.implicit_defs.is_empty() || !inst.implicit_uses.is_empty() {
        return Err("it has implicit registers".to_string());
    }
    let (reads, writes) = instruction_access(inst);
    if writes.iter().any(|l| !matches!(l, Loc::VReg(_))) {
        return Err("it writes a physical register".to_string());
    }
    if !f.bc.reachable.contains(&source) || !f.dom.dominates(target, source) {
        return Err(format!(
            "block {} does not dominate the source block {}",
            target.0, source.0
        ));
    }
    let successors = |b: BlockId| f.bc.successors(b).to_vec();
    let predecessors = |b: BlockId| f.bc.preds.get(&b).cloned().unwrap_or_default();
    let forward = reach(
        f.bc.successors(target).iter().copied(),
        successors,
        &[target],
    );
    let backward = reach([source], predecessors, &[target]);
    let region: Vec<BlockId> = {
        let mut r: Vec<BlockId> = forward.intersection(&backward).copied().collect();
        r.sort_unstable_by_key(|b| b.0);
        r
    };
    if !region.contains(&source) {
        return Err(format!(
            "block {} is not reached from block {}",
            source.0, target.0
        ));
    }
    let target_insts = &f.after.block(target).insts;
    let later_in_target = &target_insts[position + 1..];
    let src_index = f.pb[&id].1;
    // It runs whenever `P` runs: nothing ahead of it in `P` leaves the
    // block (a conditional exit ahead of it would reach `S` without it).
    if let Some(&x) = target_insts[..position].iter().find(|&&x| {
        let inst = f.after.inst(x);
        let flags = inst.flags.union(inst.opcode.default_flags());
        flags.contains(InstFlags::IS_BRANCH)
            || flags.contains(InstFlags::IS_RETURN)
            || is_block_exit(f.after, x)
    }) {
        return Err(format!(
            "it follows inst {} ({:?}), which leaves block {}",
            x.0,
            f.after.inst(x).opcode,
            target.0
        ));
    }
    check_exception_edges(f, target, position, source, &writes)?;

    // The value is the same.
    for loc in &reads {
        let mut region_writers = Vec::new();
        for &b in &region {
            for &w in &f.before.block(b).insts {
                if w != id && instruction_access(f.before.inst(w)).1.contains(loc) {
                    region_writers.push(w);
                }
            }
        }
        for &w in &region_writers {
            let (w_source, w_index) = f.pb[&w];
            let ran_before = if w_source == source {
                w_index < src_index
            } else {
                f.dom.dominates(w_source, source)
            };
            let ahead_in_target = f.moved.contains(&w)
                && f.pa
                    .get(&w)
                    .is_some_and(|&(b, i)| b == target && i < position);
            if !(ahead_in_target && ran_before && region_writers.len() == 1) {
                return Err(format!(
                    "its operand {loc:?} is written between blocks {} and {} by inst {}",
                    target.0, source.0, w.0
                ));
            }
        }
        if let Some(&w) = later_in_target
            .iter()
            .find(|&&w| instruction_access(f.after.inst(w)).1.contains(loc))
        {
            return Err(format!(
                "its operand {loc:?} is written after it in block {} by inst {}",
                target.0, w.0
            ));
        }
    }

    // No reader sees the earlier definition.
    let source_insts = &f.before.block(source).insts;
    let not_source = forward_without(f, target, source);
    for loc in &writes {
        let chain: Vec<InstId> = f.writers.writers.get(loc).cloned().unwrap_or_default();
        if let Some(w) = chain.iter().find(|w| !f.moved.contains(w)) {
            return Err(format!(
                "{loc:?} is also written by inst {}, which did not move",
                w.0
            ));
        }
        if chain.len() > 1 {
            // A constant chain (`MOVZ; MOVK`) moved as a unit: one source
            // block, the same order, nothing else touching it in between.
            if let Some(w) = chain
                .iter()
                .find(|w| f.pb[w].0 != source || f.pa[w].0 != target)
            {
                return Err(format!(
                    "{loc:?} is written by inst {} from another block",
                    w.0
                ));
            }
            let order_in = |list: &[InstId]| -> Vec<InstId> {
                list.iter().copied().filter(|x| chain.contains(x)).collect()
            };
            if order_in(source_insts) != order_in(target_insts) {
                return Err(format!("the chain writing {loc:?} was reordered"));
            }
            for (list, func) in [
                (source_insts.as_slice(), f.before),
                (target_insts.as_slice(), f.after),
            ] {
                let positions: Vec<usize> = list
                    .iter()
                    .enumerate()
                    .filter(|(_, x)| chain.contains(x))
                    .map(|(i, _)| i)
                    .collect();
                let (first, last) = (positions[0], positions[positions.len() - 1]);
                if let Some(&x) = list[first..=last].iter().find(|&&x| {
                    !chain.contains(&x) && {
                        let mut touches = false;
                        for_each_access(func.inst(x), |l, _| touches |= l == *loc);
                        touches
                    }
                }) {
                    return Err(format!(
                        "inst {} touches {loc:?} inside the moved chain",
                        x.0
                    ));
                }
            }
        }
        if f.live.is_live(target, *loc) {
            return Err(format!("{loc:?} is live into block {}", target.0));
        }
        let first_member = source_insts
            .iter()
            .position(|x| chain.contains(x) || *x == id)
            .unwrap_or(src_index);
        if let Some(&x) = source_insts[..first_member].iter().find(|&&x| {
            let (r, w) = instruction_access(f.before.inst(x));
            r.contains(loc) || w.contains(loc)
        }) {
            return Err(format!(
                "{loc:?} is used in block {} ahead of it, by inst {}",
                source.0, x.0
            ));
        }
        if let Some(&b) = not_source.iter().find(|&&b| f.live.is_live(b, *loc)) {
            return Err(format!(
                "{loc:?} is live into block {}, which is reached from block {} without block {}",
                b.0, target.0, source.0
            ));
        }
        if let Some(&w) = later_in_target.iter().find(|&&w| {
            !chain.contains(&w) && {
                let (r, wr) = instruction_access(f.after.inst(w));
                r.contains(loc) || wr.contains(loc)
            }
        }) {
            return Err(format!(
                "{loc:?} is used after it in block {} by inst {}",
                target.0, w.0
            ));
        }
    }
    Ok(())
}

/// Blocks reachable from `target`'s successors without entering `source`,
/// in id order.
fn forward_without(f: &MoveFacts<'_>, target: BlockId, source: BlockId) -> Vec<BlockId> {
    let mut out: Vec<BlockId> = reach(
        f.bc.successors(target).iter().copied(),
        |b| f.bc.successors(b).to_vec(),
        &[source],
    )
    .into_iter()
    .collect();
    out.sort_unstable_by_key(|b| b.0);
    out
}

/// The loop-preheader side conditions of one move (the module header's
/// list).
fn check_move(f: &MoveFacts<'_>, id: InstId) -> Result<(), String> {
    let MoveFacts {
        before,
        after,
        bc,
        ac,
        dom,
        live,
        writers,
        moved,
        pa,
        pb,
    } = *f;
    let inst = before.inst(id);
    let source = pb[&id].0;
    let (target, position) = pa[&id];

    // The target is the loop's only entry, and the source is in the loop.
    let Some(header) = ac.shapes.get(&target).and_then(Shape::single_successor) else {
        return Err(format!(
            "block {} is not straight-line code continuing at one block",
            target.0
        ));
    };
    let (body, latches) = natural_loop(bc, dom, header)
        .ok_or_else(|| format!("block {} is not a loop header", header.0))?;
    if !body.contains(&source) {
        return Err(format!(
            "block {} is not in the loop at {}",
            source.0, header.0
        ));
    }
    if body.contains(&target) {
        return Err(format!("block {} is inside the loop", target.0));
    }
    if let Some(p) = bc
        .preds
        .get(&header)
        .into_iter()
        .flatten()
        .find(|p| !body.contains(p) && **p != target)
    {
        return Err(format!("the loop is also entered from block {}", p.0));
    }

    // What the instruction may be.
    if reads_nzcv(inst) || may_clobber_nzcv(inst) {
        return Err("it reads or writes NZCV".to_string());
    }
    let load = plain_load(inst);
    if !load && !pure_value(inst) {
        return Err("it is neither a pure value nor a plain load".to_string());
    }
    if !inst.implicit_defs.is_empty() || !inst.implicit_uses.is_empty() {
        return Err("it has implicit registers".to_string());
    }
    let (reads, writes) = instruction_access(inst);
    if writes.iter().any(|l| !matches!(l, Loc::VReg(_))) {
        return Err("it writes a physical register".to_string());
    }
    check_exception_edges(f, target, position, source, &writes)?;

    // Loop and preheader instructions, from the input and output, with what
    // each loop instruction writes.
    let loop_insts: Vec<InstId> = body
        .iter()
        .flat_map(|b| before.block(*b).insts.iter().copied())
        .collect();
    let loop_writes: Vec<(InstId, Vec<Loc>)> = loop_insts
        .iter()
        .map(|&w| (w, instruction_access(before.inst(w)).1))
        .collect();
    let target_insts = &after.block(target).insts;
    let later_in_target = &target_insts[position + 1..];

    // Operands are invariant: every writer of an operand in the loop is
    // moved to the target too, ahead of this instruction; a chain of writers
    // in this instruction's own block keeps its order relative to it.
    for loc in &reads {
        let loop_writers: Vec<InstId> = loop_writes
            .iter()
            .filter(|(w, w_writes)| *w != id && w_writes.contains(loc))
            .map(|(w, _)| *w)
            .collect();
        for &w in &loop_writers {
            if !moved.contains(&w) || pa[&w].0 != target {
                return Err(format!(
                    "its operand {loc:?} is written in the loop by inst {}",
                    w.0
                ));
            }
            let ahead_in_target = pa[&w].1 < position;
            if pb[&w].0 == source {
                if (pb[&w].1 < pb[&id].1) != ahead_in_target {
                    return Err(format!(
                        "its operand {loc:?} is written by inst {} on the other side of it \
                         than in the loop",
                        w.0
                    ));
                }
            } else if loop_writers.len() > 1 || !ahead_in_target {
                return Err(format!(
                    "its operand {loc:?} is written in the loop by inst {} in another block",
                    w.0
                ));
            }
        }
        if let Some(&w) = later_in_target.iter().find(|&&w| {
            !loop_writers.contains(&w) && instruction_access(after.inst(w)).1.contains(loc)
        }) {
            return Err(format!(
                "its operand {loc:?} is written after it in block {} by inst {}",
                target.0, w.0
            ));
        }
    }

    // The definitions are not observed early.
    let dominates_exits = body.iter().all(|&b| {
        let leaves = bc.successors(b).iter().any(|t| !body.contains(t));
        !leaves || dom.dominates(source, b)
    });
    // Whether the target can run again in one activation (it lies on a
    // cycle, such as an outer loop): an earlier visit to this loop may then
    // have left a value in a register only moved instructions write.
    let target_repeats = reach(
        bc.successors(target).iter().copied(),
        |b| bc.successors(b).to_vec(),
        &[],
    )
    .contains(&target);
    for loc in &writes {
        // Every writer of the location in the loop. More than one is a chain
        // moved as a unit (`MOVZ; MOVK` building one constant): every member
        // moved out of the source block, in the same order into the target,
        // with nothing else touching the location between members in either.
        let chain: Vec<InstId> = loop_writes
            .iter()
            .filter(|(_, w_writes)| w_writes.contains(loc))
            .map(|(w, _)| *w)
            .collect();
        if chain.len() > 1 {
            if let Some(w) = chain
                .iter()
                .find(|w| !moved.contains(w) || pb[w].0 != source || pa[w].0 != target)
            {
                return Err(format!(
                    "{loc:?} has another writer in the loop, inst {}",
                    w.0
                ));
            }
            let span_clean = |list: &[InstId], func: &MachFunction| -> Result<(), String> {
                let positions: Vec<usize> = list
                    .iter()
                    .enumerate()
                    .filter(|(_, x)| chain.contains(x))
                    .map(|(i, _)| i)
                    .collect();
                let (first, last) = (positions[0], positions[positions.len() - 1]);
                for &x in &list[first..=last] {
                    if chain.contains(&x) {
                        continue;
                    }
                    let mut touches = false;
                    for_each_access(func.inst(x), |l, _| touches |= l == *loc);
                    if touches {
                        return Err(format!(
                            "inst {} touches {loc:?} inside the moved chain",
                            x.0
                        ));
                    }
                }
                Ok(())
            };
            span_clean(&before.block(source).insts, before)?;
            span_clean(target_insts, after)?;
            let order_in = |list: &[InstId]| -> Vec<InstId> {
                list.iter().copied().filter(|x| chain.contains(x)).collect()
            };
            if order_in(&before.block(source).insts) != order_in(target_insts) {
                return Err(format!("the chain writing {loc:?} was reordered"));
            }
        }
        // A register written only by moved instructions holds no defined
        // value before their first execution in an activation: reading it
        // early in the input reads an undefined register, which the output's
        // earlier definition refines. That holds only when the target runs
        // at most once per activation. When it repeats, a read before the
        // loop's next execution of the source sees the value an earlier
        // visit left, which the output replaces, so the register is checked
        // as if another instruction wrote it.
        let defined_elsewhere = target_repeats
            || writers
                .writers
                .get(loc)
                .is_none_or(|all| all.iter().any(|w| !moved.contains(w)));
        if defined_elsewhere && live.is_live(header, *loc) {
            return Err(format!("{loc:?} is live into the loop header"));
        }
        if let Some(&w) = later_in_target.iter().find(|&&w| {
            !moved.contains(&w) && {
                let (r, wr) = instruction_access(after.inst(w));
                r.contains(loc) || wr.contains(loc)
            }
        }) {
            return Err(format!(
                "{loc:?} is used after it in block {} by inst {}",
                target.0, w.0
            ));
        }
        if !dominates_exits && defined_elsewhere {
            for &b in &body {
                for &t in bc.successors(b) {
                    if !body.contains(&t) && live.is_live(t, *loc) {
                        return Err(format!(
                            "{loc:?} is live out of the loop at block {} and the source does not \
                             dominate every exit",
                            t.0
                        ));
                    }
                }
            }
        }
    }

    if !load {
        return Ok(());
    }
    // Memory the load reads is not written in the loop or after it.
    // The load's base resolves where it now runs.
    let load_at = (target, position);
    let load_slot = writers.bounded_slot_access(inst, load_at);
    for &w in &loop_insts {
        let winst = before.inst(w);
        if !writes_memory(winst) {
            continue;
        }
        // Resolved where the writer now runs; one missing from the output
        // is a change the move check does not account for.
        let Some(&w_at) = pa.get(&w) else {
            return Err(format!(
                "the loop's memory writer inst {} is missing from the output",
                w.0
            ));
        };
        // Two bounded direct accesses in different fixed slots; nothing
        // else (a symbol, a slot against a global, an unbounded access) is
        // taken as disjoint.
        let disjoint = !winst
            .flags
            .union(winst.opcode.default_flags())
            .contains(InstFlags::IS_CALL)
            && !opcode_effect(winst.opcode).is_barrier()
            && matches!(
                (load_slot, writers.bounded_slot_access(winst, w_at)),
                (Some(a), Some(b)) if a != b
            );
        if !disjoint {
            return Err(format!(
                "the loop may write what it loads (inst {} {:?})",
                w.0, winst.opcode
            ));
        }
    }
    if let Some(&w) = later_in_target
        .iter()
        .find(|&&w| writes_memory(after.inst(w)))
    {
        return Err(format!(
            "block {} writes memory after its new position (inst {})",
            target.0, w.0
        ));
    }
    // Fault safety.
    if load_slot.is_some() {
        return Ok(());
    }
    let dominates_latches = latches.iter().all(|&l| dom.dominates(source, l));
    if !dominates_latches || !dominates_exits {
        return Err("a load that can fault is not guaranteed to execute in the loop".to_string());
    }
    // Nothing on a path from the header to it can end execution first.
    let mut on_path: HashSet<BlockId> = HashSet::default();
    let mut stack = vec![source];
    while let Some(b) = stack.pop() {
        if !on_path.insert(b) || b == header {
            continue;
        }
        stack.extend(
            bc.preds
                .get(&b)
                .into_iter()
                .flatten()
                .copied()
                .filter(|p| body.contains(p)),
        );
    }
    for &b in &on_path {
        let insts = &before.block(b).insts;
        let upto = if b == source {
            insts.iter().position(|&x| x == id).unwrap_or(insts.len())
        } else {
            insts.len()
        };
        if let Some(&x) = insts[..upto]
            .iter()
            .find(|&&x| may_end_execution(before.inst(x)) && !is_block_exit(before, x))
        {
            return Err(format!(
                "inst {} ({:?}) can end execution before it",
                x.0,
                before.inst(x).opcode
            ));
        }
    }
    Ok(())
}

/// Whether `id` is a branch of its block's exit sequence, which leaves
/// control inside the function.
fn is_block_exit(func: &MachFunction, id: InstId) -> bool {
    matches!(
        func.inst(id).opcode,
        AArch64Opcode::B
            | AArch64Opcode::BCond
            | AArch64Opcode::Bcc
            | AArch64Opcode::Cbz
            | AArch64Opcode::Cbnz
            | AArch64Opcode::Tbz
            | AArch64Opcode::Tbnz
    )
}
