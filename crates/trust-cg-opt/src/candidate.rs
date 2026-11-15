//! Checked construction for optional machine-IR rewrites.
//!
//! A recognized rewrite runs on a private function and publishes only on
//! success. These helpers admit the identities/anchors they use, not arbitrary
//! IR, target semantics, resource policy, or recoverable memory exhaustion.

use crate::fast_hash::FxHashSet as HashSet;
use crate::loop_contract::{CoverageFrame, CoveredLoop, Lanes, check_coverage_in};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand};

/// Clone only after recognition. Synchronize once, then use checked allocation
/// throughout the candidate; direct insertion of new caller-owned register IDs
/// would require another synchronization. Refusal never publishes partial edits.
///
/// L10-P5: the function itself is admitted first, so a counter left stale
/// before this pass is refused (sticky on `func`, reported by the pass
/// manager) instead of being repaired by the candidate's synchronization and
/// published. After that admission the synchronization changes the counter
/// only for IDs this pass wrote without allocating.
pub(crate) fn commit(
    func: &mut MachFunction,
    rewrite: impl FnOnce(&mut MachFunction) -> Option<()>,
) -> bool {
    if func.admit_ids_before_allocation().is_err() {
        return false;
    }
    let mut candidate = func.clone();
    if candidate.try_sync_vreg_counter().is_none() || rewrite(&mut candidate).is_none() {
        return false;
    }
    *func = candidate;
    true
}

/// [`commit`] through the loop-state contract's iteration-coverage clause
/// (`crate::loop_contract::coverage`): the candidate is published only when
/// the new code `rewrite` builds, counted as the [`Lanes`] it returns, plus the
/// scalar remainder run exactly the iterations of the loop `scope` names.
pub(crate) fn commit_covered(
    func: &mut MachFunction,
    scope: &CoveredLoop<BlockId>,
    rewrite: impl FnOnce(&mut MachFunction) -> Option<Lanes<BlockId>>,
) -> bool {
    commit_covered_all(func, &[scope], |candidate| Some(vec![rewrite(candidate)?]))
}

/// [`commit_covered`] for several loops rewritten on ONE candidate: `rewrite`
/// returns one [`Lanes`] per scope, in order, and every loop must pass the
/// clause against the original function before anything is published.
pub(crate) fn commit_covered_all(
    func: &mut MachFunction,
    scopes: &[&CoveredLoop<BlockId>],
    rewrite: impl FnOnce(&mut MachFunction) -> Option<Vec<Lanes<BlockId>>>,
) -> bool {
    let mut candidate = func.clone();
    if candidate.try_sync_vreg_counter().is_none() {
        return false;
    }
    let Some(lanes) = rewrite(&mut candidate) else {
        return false;
    };
    if lanes.len() != scopes.len() {
        return false;
    }
    // One frame for the candidate: each loop's check then costs its region.
    let frame = CoverageFrame::new(&*func, &candidate);
    if scopes
        .iter()
        .zip(&lanes)
        .any(|(scope, lanes)| check_coverage_in(&frame, &*func, &candidate, scope, lanes).is_err())
    {
        return false;
    }
    *func = candidate;
    true
}

pub(crate) fn alloc(func: &mut MachFunction, class: RegClass) -> Option<VReg> {
    func.try_alloc_vreg().map(|id| VReg::new(id, class))
}

pub(crate) fn emit(
    func: &mut MachFunction,
    block: BlockId,
    opcode: AArch64Opcode,
    operands: Vec<MachOperand>,
) -> Option<InstId> {
    func.blocks.get(block.0 as usize)?;
    let id = func.try_push_inst(MachInst::new(opcode, operands))?;
    func.append_inst(block, id);
    Some(id)
}

/// Locate an arena-resident instruction owned exactly once by one block.
fn inst_location(func: &MachFunction, id: InstId) -> Option<(usize, usize)> {
    func.insts.get(id.0 as usize)?;
    let mut found = None;
    for (block, body) in func.blocks.iter().enumerate() {
        for (position, &inst) in body.insts.iter().enumerate() {
            if inst == id {
                if found.is_some() {
                    return None;
                }
                found = Some((block, position));
            }
        }
    }
    found
}

pub(crate) fn emit_before(
    func: &mut MachFunction,
    before: InstId,
    opcode: AArch64Opcode,
    operands: Vec<MachOperand>,
) -> Option<InstId> {
    let (block, position) = inst_location(func, before)?;
    let id = func.try_push_inst(MachInst::new(opcode, operands))?;
    func.blocks[block].insts.insert(position, id);
    Some(id)
}

/// Move freshly appended blocks before a unique existing layout anchor.
/// Missing/duplicate anchors or fresh IDs decline before layout mutation.
pub(crate) fn insert_new_blocks_before(
    func: &mut MachFunction,
    before: BlockId,
    new_blocks: &[BlockId],
) -> Option<()> {
    func.blocks.get(before.0 as usize)?;
    let mut pending = HashSet::with_capacity_and_hasher(new_blocks.len(), Default::default());
    for &id in new_blocks {
        func.blocks.get(id.0 as usize)?;
        if id == before || !pending.insert(id) {
            return None;
        }
    }
    let fresh = pending.clone();
    let mut anchor_seen = false;
    for &id in &func.block_order {
        if id == before {
            if anchor_seen {
                return None;
            }
            anchor_seen = true;
        }
        if fresh.contains(&id) && !pending.remove(&id) {
            return None;
        }
    }
    if !anchor_seen || !pending.is_empty() {
        return None;
    }
    // Every fresh ID already occurs once in the layout, so length is unchanged.
    let mut order = Vec::with_capacity(func.block_order.len());
    for &id in &func.block_order {
        if id == before {
            order.extend_from_slice(new_blocks);
        }
        if !fresh.contains(&id) {
            order.push(id);
        }
    }
    func.block_order = order;
    Some(())
}

/// Redirect one recognized entry edge and its instruction together. Other
/// candidate edges remain the caller's responsibility. This checks the named
/// edge and instruction ownership, not the complete CFG or branch semantics.
pub(crate) fn splice_edge(
    func: &mut MachFunction,
    from: BlockId,
    term: InstId,
    old: BlockId,
    new: BlockId,
) -> Option<()> {
    let (owner, _) = inst_location(func, term)?;
    if owner != from.0 as usize
        || !func.blocks.get(owner)?.succs.contains(&old)
        || !func.blocks.get(old.0 as usize)?.preds.contains(&from)
        || !func.insts[term.0 as usize]
            .operands
            .iter()
            .any(|op| matches!(op, MachOperand::Block(id) if *id == old))
    {
        return None;
    }
    func.blocks.get(new.0 as usize)?;
    for op in &mut func.insts[term.0 as usize].operands {
        if matches!(op, MachOperand::Block(id) if *id == old) {
            *op = MachOperand::Block(new);
        }
    }
    func.blocks[owner].succs.retain(|id| *id != old);
    func.blocks[old.0 as usize].preds.retain(|id| *id != from);
    func.add_edge(from, new);
    Some(())
}

#[cfg(test)]
pub(crate) mod tests;
