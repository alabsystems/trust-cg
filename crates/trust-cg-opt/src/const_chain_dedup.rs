// trust-cg-opt - Merge a repeated multi-instruction constant within one block
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Merge a repeated `MOVZ` + `MOVK` constant within one block.
//!
//! LICM hoists every loop-invariant constant chain into the loop's preheader,
//! one chain per constant the selector materialized, so a constant the loop
//! body spells twice (`s * A + B` twice in `p3_gcd`, `x % 100` twice in
//! `p4_matmul`'s initialization loop) ends up materialized twice there, in two
//! registers that both stay live through the loop. CSE does not merge the
//! chains: a `MOVK` reads and writes its own register. This pass keeps the
//! first chain and points the readers of the second at it:
//!
//! ```text
//!   v0 = MOVZ #a ; v0 = MOVK v0, #b, lsl #16 ; ...   ; kept
//!   v1 = MOVZ #a ; v1 = MOVK v1, #b, lsl #16 ; ...   ; same value: removed
//!   ... v1 ...                                       ; now reads v0
//! ```
//!
//! # Why it is the same value
//!
//! Each register is written by nothing but its chain: every instruction in
//! the layout that writes the register's numeric ID (a W write included) is
//! one of the chain's instructions, and the chain is one contiguous `MOVZ`
//! (shift zero) + `MOVK` run in one block
//! ([`crate::mach_util::materialized_runs_value`] folds it). Both runs
//! produce the same value in the same register class, and `v0`'s run comes
//! first in the block. On any path to a read of `v1`, the last write of `v1`
//! is `v1`'s run (its only writer), `v0`'s run executed just before it in the
//! same block, and nothing writes `v0` again, so `v0` holds the same value at
//! the read. (A path that never executes `v1`'s run would read `v1`
//! uninitialized.) A W-view read of `v1` becomes the W view of `v0`.
//!
//! # When it fires (fail-closed)
//!
//! * runs of at least two instructions in the same block, the same register
//!   class (`Gpr64` or `Gpr32`) and the same value; a single `MOVZ` is left
//!   alone (cheaper than a longer live range);
//! * every instruction of both runs has ordinary metadata (default flags, no
//!   implicit operands, no proof annotation);
//! * `v0` is read at or after `v1`'s run (later in the block, before its own
//!   run in a loop, or in another block), so `v0` is live where `v1` is
//!   defined: the merge only replaces `v1`'s live range by an extension of a
//!   range that already overlapped it, and register pressure never rises;
//! * every instruction the merge rewrites or removes is linked by exactly one
//!   block of the function, and no block outside the layout names `v1`
//!   (OD-109 ownership).
//!
//! Removed chain IDs are retired as canonical nonemitting Nops only after all
//! link splices, and only if no block still owns them. Stable arena IDs and
//! historical source-lowering sidecars remain unchanged; unrelated orphans
//! are not swept. This representation repair does not certify the rewrite.
//! Accepted duplicates map directly to their first surviving carrier. Apply
//! batches those numeric-ID substitutions and ordered link removals in one
//! layout sweep, not one whole-function scan/allocation per merged chain.
//!
//! Runs late (after LICM and the unrollers, before the scheduler); a function
//! without a `MOVK` is not scanned. Kill switch:
//! `TRUST_CG_DISABLE_PASSES=constdedup`.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    RegClass, VReg,
};

use crate::effects::for_each_inst_def;
use crate::pass_manager::{AnalysisCache, MachinePass};
use crate::reaching_const::{apply_movk, movz_value};

/// Stable pass name (also the provenance pass ID).
pub const CONST_CHAIN_DEDUP_PASS_NAME: &str = "const-chain-dedup";

/// The repeated-constant merge pass.
pub struct ConstChainDedup;

impl MachinePass for ConstChainDedup {
    fn name(&self) -> &str {
        CONST_CHAIN_DEDUP_PASS_NAME
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        dedup(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        dedup(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        // Instructions are removed and operands renamed inside blocks; no
        // edge changes, so the cached CFG analyses stay valid.
        dedup(func, Some(provenance))
    }
}

fn pass_id() -> PassId {
    PassId::new(CONST_CHAIN_DEDUP_PASS_NAME)
}

/// Default flags, no implicit definitions or uses and no proof annotation.
fn ordinary_metadata(inst: &MachInst) -> bool {
    inst.flags == inst.opcode.default_flags()
        && inst.implicit_defs.is_empty()
        && inst.implicit_uses.is_empty()
        && inst.proof.is_none()
}

/// One contiguous `MOVZ` + `MOVK` run in a block.
#[derive(Clone, Debug)]
struct Run {
    carrier: VReg,
    value: u64,
    /// Position of the `MOVZ` in the block.
    head: usize,
    insts: Vec<InstId>,
}

/// The runs of `block`: a shift-zero `MOVZ` into a `Gpr64`/`Gpr32` virtual
/// register followed by at least one `MOVK` into the same register at the
/// next positions, every instruction with ordinary metadata.
fn block_runs(func: &MachFunction, block: BlockId) -> Vec<Run> {
    let insts = &func.block(block).insts;
    let mut runs = Vec::new();
    let mut pos = 0;
    while pos < insts.len() {
        let head = func.inst(insts[pos]);
        let Some((carrier, first)) = movz_value(head)
            .filter(|(v, _)| matches!(v.class, RegClass::Gpr64 | RegClass::Gpr32))
            .filter(|_| ordinary_metadata(head))
        else {
            pos += 1;
            continue;
        };
        let mut value = if carrier.class == RegClass::Gpr32 {
            first & 0xFFFF_FFFF
        } else {
            first
        };
        let mut end = pos + 1;
        while end < insts.len() {
            let inst = func.inst(insts[end]);
            if !ordinary_metadata(inst) {
                break;
            }
            let Some(next) = apply_movk(inst, carrier, value) else {
                break;
            };
            value = next;
            end += 1;
        }
        if end - pos >= 2 {
            runs.push(Run {
                carrier,
                value,
                head: pos,
                insts: insts[pos..end].to_vec(),
            });
        }
        pos = end;
    }
    runs
}

/// One merge: `dup`'s readers read `keep` instead, and `dup`'s run goes.
struct Merge {
    keep: VReg,
    keep_last: InstId,
    dup: VReg,
    dup_insts: Vec<InstId>,
}

fn dedup(func: &mut MachFunction, provenance: Option<&mut ProvenanceMap>) -> bool {
    let has_movk = func
        .block_order
        .iter()
        .flat_map(|&b| func.block(b).insts.iter())
        .any(|&i| func.inst(i).opcode == AArch64Opcode::Movk);
    if !has_movk {
        return false;
    }
    let merges = find_merges(func);
    apply(func, merges, provenance)
}

fn find_merges(func: &MachFunction) -> Vec<Merge> {
    // Instructions in the layout writing each numeric register ID, and the
    // positions (block, index) of the instructions naming it. For a register
    // written only by its own run, every naming instruction outside the run
    // reads it.
    let mut defs: HashMap<u32, usize> = HashMap::default();
    let mut named_at: HashMap<u32, Vec<(BlockId, usize)>> = HashMap::default();
    for &block in &func.block_order {
        for (pos, &id) in func.block(block).insts.iter().enumerate() {
            let inst = func.inst(id);
            for_each_inst_def(inst, |v| *defs.entry(v.id).or_insert(0) += 1);
            let mut named: Vec<u32> = Vec::new();
            for op in &inst.operands {
                if let MachOperand::VReg(v) = op
                    && !named.contains(&v.id)
                {
                    named.push(v.id);
                    named_at.entry(v.id).or_default().push((block, pos));
                }
            }
        }
    }
    // The reads of a run's carrier: the instructions naming it outside the run.
    let reads_of = |run: &Run, block: BlockId| -> Vec<(BlockId, usize)> {
        let end = run.head + run.insts.len();
        named_at
            .get(&run.carrier.id)
            .map(|at| {
                at.iter()
                    .copied()
                    .filter(|&(b, pos)| b != block || pos < run.head || pos >= end)
                    .collect()
            })
            .unwrap_or_default()
    };
    // Instructions linked by more than one block (any block, in the layout or
    // not), and the register IDs named outside the layout.
    let mut links: HashMap<InstId, u8> = HashMap::default();
    let in_layout: HashSet<BlockId> = func.block_order.iter().copied().collect();
    let mut named_outside: HashSet<u32> = HashSet::default();
    for (index, block) in func.blocks.iter().enumerate() {
        let outside = u32::try_from(index)
            .map(|i| !in_layout.contains(&BlockId(i)))
            .unwrap_or(true);
        for &id in &block.insts {
            let n = links.entry(id).or_insert(0);
            *n = n.saturating_add(1);
            if outside {
                for op in &func.inst(id).operands {
                    if let MachOperand::VReg(v) = op {
                        named_outside.insert(v.id);
                    }
                }
            }
        }
    }
    let solely_linked = |id: &InstId| links.get(id) == Some(&1);

    let mut merges = Vec::new();
    let mut retired: HashSet<u32> = HashSet::default();
    for &block in &func.block_order {
        let mut first_of: HashMap<(RegClass, u64), Run> = HashMap::default();
        for run in block_runs(func, block) {
            // Every write of the carrier's ID is this run.
            if defs.get(&run.carrier.id) != Some(&run.insts.len())
                || named_outside.contains(&run.carrier.id)
                || !run.insts.iter().all(solely_linked)
            {
                continue;
            }
            let key = (run.carrier.class, run.value);
            let Some(keep) = first_of.get(&key) else {
                first_of.insert(key, run);
                continue;
            };
            if keep.carrier.id == run.carrier.id || retired.contains(&keep.carrier.id) {
                continue;
            }
            // `keep` is live at `run`'s head: read after it in the block,
            // before its own run (a loop-carried read), or in another block.
            let keep_live = reads_of(keep, block)
                .iter()
                .any(|&(b, pos)| b != block || pos > run.head || pos < keep.head);
            if !keep_live {
                continue;
            }
            // Every reader of the duplicate is rewritten in place.
            let readers_owned = reads_of(&run, block)
                .iter()
                .all(|&(b, pos)| solely_linked(&func.block(b).insts[pos]));
            if !readers_owned {
                continue;
            }
            retired.insert(run.carrier.id);
            merges.push(Merge {
                keep: keep.carrier,
                keep_last: *keep.insts.last().expect("a run has two instructions"),
                dup: run.carrier,
                dup_insts: run.insts,
            });
        }
    }
    merges
}

fn apply(
    func: &mut MachFunction,
    merges: Vec<Merge>,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    if merges.is_empty() {
        return false;
    }
    // Discovery never replaces first_of's canonical run by a duplicate, and
    // each carrier is written only by its own run throughout the function.
    // Consequently accepted keep IDs are not themselves retired and every
    // duplicate has one destination: no transitive rename walk is required.
    let mut rewrites = HashMap::default();
    let mut consumed = Vec::new();
    for merge in &merges {
        let previous = rewrites.insert(merge.dup.id, merge.keep.id);
        debug_assert!(previous.is_none(), "one merge per duplicate carrier");
        consumed.extend(merge.dup_insts.iter().copied());
    }
    debug_assert!(
        rewrites.values().all(|keep| !rewrites.contains_key(keep)),
        "the first surviving carrier is never a duplicate"
    );
    let dead: HashSet<InstId> = consumed.iter().copied().collect();
    let mut rewritten = Vec::new();
    for &block in &func.block_order {
        // Borrow disjoint storage, rather than cloning layout/link vectors to
        // call whole-function accessors. Only this pass's actual consumed IDs
        // are spliced; retain preserves every surviving link's order.
        let insts = &mut func.blocks[block.0 as usize].insts;
        insts.retain(|id| !dead.contains(id));
        for &id in insts.iter() {
            let inst = &mut func.insts[id.0 as usize];
            let mut hit = false;
            for op in &mut inst.operands {
                if let MachOperand::VReg(v) = op
                    && let Some(&keep) = rewrites.get(&v.id)
                {
                    // W/X views alias by numeric ID, but retain the reader's
                    // exact width/class, as the sequential implementation did.
                    *v = VReg::new(keep, v.class);
                    hit = true;
                }
            }
            // Discovery requires every modified reader to have one owner in
            // ALL blocks. Thus each rewritten ID is visited once, even when
            // this instruction reads several duplicates. No dedup set or
            // provenance scratch is needed on the ordinary no-history lane.
            if hit && provenance.is_some() {
                rewritten.push(id);
            }
        }
    }
    // These indexes are no longer needed. Retirement builds its own all-block
    // ownership index; do not overlap that allocation with apply's scratch.
    drop(dead);
    drop(rewrites);
    for merge in &merges {
        if let Some(provenance) = provenance.as_deref_mut() {
            for &id in &merge.dup_insts {
                provenance.record_merge(&[merge.keep_last, id], merge.keep_last, pass_id());
            }
        }
    }
    // Retire only this pass's actual consumed IDs after every splice. The
    // shared helper checks links in all blocks, including outside layout,
    // and leaves stable IDs and historical lowering sidecars untouched.
    crate::retirement::retire_unlinked(func, &consumed);
    if let Some(provenance) = provenance {
        for id in rewritten {
            provenance.record_in_place_transform(id, pass_id());
        }
    }
    true
}

#[cfg(test)]
mod tests;
