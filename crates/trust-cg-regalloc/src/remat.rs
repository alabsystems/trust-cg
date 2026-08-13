// trust-cg-regalloc/remat.rs - Rematerialization for the register allocator
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Rematerialization: recompute cheap values instead of loading from spill slots.
//!
//! For values defined by instructions that are cheap to recompute (constants,
//! address computations, simple ALU ops with immediates), we can clone the
//! defining instruction at each use site instead of inserting a spill load.
//! This eliminates the memory traffic of the spill and often produces better
//! code.
//!
//! Reference: LLVM `InlineSpiller.cpp` — rematerialization during spilling.

use std::collections::{BTreeMap, BTreeSet};

use crate::linear_scan::SpillInfo;
use crate::machine_types::{InstId, MachFunction, MachInst, MachOperand, StackSlotId, VReg};
use crate::spill::PSEUDO_SPILL_LOAD;

/// Cost classification for rematerialization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RematCost {
    /// Free to rematerialize: instruction uses only immediates.
    /// Examples: `MOV Xd, #imm`, `FMOV Dd, #fimm`.
    Free,
    /// Cheap to rematerialize: one VReg input plus an immediate.
    /// Examples: `ADD Xd, Xn, #imm`, `SUB Xd, Xn, #imm`.
    Cheap,
    /// Too expensive to rematerialize: multiple register inputs,
    /// memory operations, calls, or side effects.
    Expensive,
}

/// A candidate for rematerialization.
#[derive(Debug, Clone)]
pub struct RematCandidate {
    /// The spilled virtual register.
    pub vreg: VReg,
    /// The instruction that defines this VReg.
    pub defining_inst_id: InstId,
    /// The cost classification.
    pub cost: RematCost,
}

/// Classify the rematerialization cost of an instruction.
///
/// Rules:
/// - Instructions with IS_CALL, READS_MEMORY, WRITES_MEMORY, or
///   HAS_SIDE_EFFECTS flags are always Expensive.
/// - Instructions where all uses are Imm/FImm are Free.
/// - Instructions with exactly one VReg use and at least one Imm/FImm
///   use are Cheap.
/// - Everything else is Expensive.
pub fn classify_remat_cost(inst: &MachInst) -> RematCost {
    let flags = inst.flags;

    // Side-effectful or memory instructions cannot be rematerialized.
    if flags.is_call() || flags.reads_memory() || flags.writes_memory() || flags.has_side_effects()
    {
        return RematCost::Expensive;
    }

    // Phi and branch instructions are not rematerializable.
    if flags.is_phi() || flags.is_branch() || flags.is_terminator() || flags.is_return() {
        return RematCost::Expensive;
    }

    let mut vreg_count = 0u32;
    let mut imm_count = 0u32;

    for op in &inst.uses {
        match op {
            MachOperand::VReg(_) => vreg_count += 1,
            MachOperand::PReg(_) => vreg_count += 1, // physical regs count as register uses
            MachOperand::Imm(_) | MachOperand::FImm(_) => imm_count += 1,
            MachOperand::Block(_) | MachOperand::StackSlot(_) => {
                return RematCost::Expensive;
            }
        }
    }

    if vreg_count == 0 && imm_count > 0 {
        RematCost::Free
    } else if vreg_count == 1 && imm_count >= 1 {
        RematCost::Cheap
    } else {
        RematCost::Expensive
    }
}

/// Find rematerialization candidates among spilled VRegs.
///
/// For each spilled VReg, looks up its single defining instruction and
/// checks if it's cheap enough to rematerialize. VRegs with zero or multiple
/// non-reload full-identity definitions are not candidates. Spill reloads are
/// the uses this pass replaces, so they do not count as original definitions.
/// Returns candidates that are Free or Cheap.
pub fn find_remat_candidates(func: &MachFunction, spilled_vregs: &[VReg]) -> Vec<RematCandidate> {
    let mut candidates = Vec::new();

    for &vreg in spilled_vregs {
        // Find the unique defining instruction for this VReg.
        if let Some(def_inst_id) = find_single_defining_inst(func, vreg) {
            let inst = &func.insts[def_inst_id.0 as usize];
            let cost = classify_remat_cost(inst);

            match cost {
                RematCost::Free | RematCost::Cheap => {
                    candidates.push(RematCandidate {
                        vreg,
                        defining_inst_id: def_inst_id,
                        cost,
                    });
                }
                RematCost::Expensive => {}
            }
        }
    }

    candidates
}

/// Apply rematerialization: replace spill loads with cloned defining
/// instructions.
///
/// For each remat candidate:
/// 1. Find all PSEUDO_SPILL_LOAD instructions that load this VReg.
/// 2. Replace each with a clone of the defining instruction.
/// 3. Remove the candidate from `spill_infos` (no spill slot needed).
/// 4. Remove any now-unreferenced stack slot metadata for those spill infos.
///
/// Returns the number of rematerializations performed.
pub fn apply_rematerialization(
    func: &mut MachFunction,
    candidates: &[RematCandidate],
    spill_infos: &mut Vec<SpillInfo>,
) -> u32 {
    let mut remat_count = 0u32;
    let remat_vregs: std::collections::BTreeSet<VReg> = candidates.iter().map(|c| c.vreg).collect();

    // Clone the defining instructions upfront to avoid borrow conflicts.
    let def_inst_clones: std::collections::BTreeMap<VReg, MachInst> = candidates
        .iter()
        .map(|c| (c.vreg, func.insts[c.defining_inst_id.0 as usize].clone()))
        .collect();

    // Phase 1: Scan for spill loads to replace. Collect the plan.
    // Each entry: (block_idx, inst_position_in_block, loaded_vreg).
    let mut replacements: Vec<(usize, usize, VReg)> = Vec::new();

    for (block_idx, block) in func.blocks.iter().enumerate() {
        for (pos, &inst_id) in block.insts.iter().enumerate() {
            let inst = &func.insts[inst_id.0 as usize];
            if inst.opcode != PSEUDO_SPILL_LOAD {
                continue;
            }

            // Check if the loaded VReg is a remat candidate.
            if let Some(loaded_vreg) = inst.defs.first().and_then(|op| op.as_vreg())
                && remat_vregs.contains(&loaded_vreg)
            {
                replacements.push((block_idx, pos, loaded_vreg));
            }
        }
    }

    // Loop-depth guard (hoist-preserving). Rematerializing a value into a
    // STRICTLY DEEPER loop than its defining location re-clones the defining
    // instruction inside the loop, undoing a hoist the optimizer performed —
    // most importantly LICM's lift of a loop-invariant `adrp`/`add` global
    // address out of the loop. `classify_remat_cost` sees `adrp` as imm-only
    // `Free` (its `Symbol` maps to `Imm(0)`), so without this guard a spilled
    // hoisted address would be re-materialized once per iteration. We derive an
    // honest per-block loop depth from the CFG (the `loop_depth` field is a
    // pipeline stub) and keep the spill reload instead when the use site is
    // deeper than the def. Conservative: when depth is unknown (0) — including
    // very large functions and functions with no loops — the guard never fires
    // and remat proceeds exactly as before. Suppressing a remat is always
    // value-preserving (the reload yields the same value), so this is a pure
    // code-quality decision with no correctness effect.
    let loop_depths = compute_loop_depths(func);
    let def_loop_depth = candidate_def_loop_depths(func, candidates, &loop_depths);

    // Phase 2: Apply replacements in reverse order to preserve positions.
    // Track candidate VRegs whose remat was SUPPRESSED so their spill slot is
    // retained (some loads still read it).
    let mut suppressed: BTreeSet<VReg> = BTreeSet::new();
    for &(block_idx, pos, loaded_vreg) in replacements.iter().rev() {
        let use_depth = loop_depths.get(block_idx).copied().unwrap_or(0);
        let def_depth = def_loop_depth.get(&loaded_vreg).copied().unwrap_or(0);
        if use_depth > def_depth {
            // Would deepen the def's loop nesting: keep the spill reload.
            suppressed.insert(loaded_vreg);
            continue;
        }
        if let Some(def_inst) = def_inst_clones.get(&loaded_vreg) {
            let remat_inst = def_inst.clone();
            let new_inst_id = InstId(func.insts.len() as u32);
            func.insts.push(remat_inst);

            // Replace the spill load with the rematerialized instruction.
            func.blocks[block_idx].insts[pos] = new_inst_id;
            remat_count += 1;
        }
    }

    // A candidate is fully rematerialized only if NONE of its loads were
    // suppressed; only then may we drop its spill slot/info. With no
    // suppression this equals `remat_vregs`, preserving prior behavior exactly.
    let fully_rematerialized: BTreeSet<VReg> = remat_vregs
        .iter()
        .copied()
        .filter(|v| !suppressed.contains(v))
        .collect();

    let remat_slots: Vec<StackSlotId> = spill_infos
        .iter()
        .filter(|si| fully_rematerialized.contains(&si.vreg))
        .map(|si| si.slot)
        .collect();

    // Phase 3: Remove spill infos for fully-rematerialized VRegs.
    spill_infos.retain(|si| !fully_rematerialized.contains(&si.vreg));
    prune_unreferenced_stack_slots(func, &remat_slots);

    remat_count
}

/// For each remat candidate, the loop depth of the block that defines it.
fn candidate_def_loop_depths(
    func: &MachFunction,
    candidates: &[RematCandidate],
    loop_depths: &[u32],
) -> BTreeMap<VReg, u32> {
    // Map InstId -> block index (original instructions only; remat clones are
    // appended later with higher ids and never looked up here).
    let mut inst_to_block: Vec<u32> = vec![u32::MAX; func.insts.len()];
    for (bi, block) in func.blocks.iter().enumerate() {
        for &iid in &block.insts {
            if let Some(slot) = inst_to_block.get_mut(iid.0 as usize) {
                *slot = bi as u32;
            }
        }
    }

    let mut depths = BTreeMap::new();
    for c in candidates {
        if let Some(&bi) = inst_to_block.get(c.defining_inst_id.0 as usize)
            && bi != u32::MAX
        {
            let d = loop_depths.get(bi as usize).copied().unwrap_or(0);
            depths.insert(c.vreg, d);
        }
    }
    depths
}

/// LEVER A (aarch64 loop-depth population): write each block's natural-loop
/// nesting depth into `RegAllocBlock::loop_depth`, computed from the regalloc
/// CFG by the same dominator/back-edge analysis the remat hoist guard uses
/// ([`compute_loop_depths`]).
///
/// The aarch64 lowering pipeline never populates `loop_depth` (the
/// `ir_to_regalloc` adapter copies the IR block's field, which is a 0 stub on
/// this path), so [`compute_spill_weight`](crate::liveness) degenerates to a
/// static use-density metric — hot loop-body values weigh the same as
/// remat-eligible constants with many static uses. Calling this before
/// liveness restores the `10^depth` hot-loop weighting.
///
/// This is the aarch64 analogue of x86's `x86_block_loop_depths`. It is a pure,
/// deterministic (BTreeMap/bitset-based, no hash iteration into the output),
/// idempotent rewrite; the pipeline gates the call behind
/// `TCG_AARCH64_RA_LOOP_DEPTH` (default OFF) so default output is byte-identical
/// to HEAD. Very large functions (>4096 blocks) keep depth 0 — see
/// [`compute_loop_depths`] — bounding the added compile time.
pub fn populate_loop_depths(func: &mut MachFunction) {
    let depths = compute_loop_depths(func);
    for (bi, block) in func.blocks.iter_mut().enumerate() {
        block.loop_depth = depths.get(bi).copied().unwrap_or(0);
    }
}

/// Compute per-block loop nesting depth directly from the register-allocation
/// CFG, using dominator-based natural-loop detection.
///
/// The `RegAllocBlock::loop_depth` field is populated by the codegen pipeline
/// only in narrow cases and is otherwise a stub (0), so remat derives the depth
/// signal its hoist-preserving guard needs from the block CFG
/// (`preds`/`succs`/`entry_block`) that regalloc already maintains. A block's
/// depth is the number of natural loops whose body contains it.
///
/// Returns an all-zero vector (the conservative "unknown" signal that permits
/// rematerialization exactly as before) for empty or very large functions,
/// where the analysis is not worth the compile time.
fn compute_loop_depths(func: &MachFunction) -> Vec<u32> {
    let n = func.blocks.len();
    let loop_bodies = natural_loop_bodies(func);
    let mut depths = vec![0u32; n];
    for body in loop_bodies.values() {
        for &b in body {
            if b < n {
                depths[b] += 1;
            }
        }
    }
    depths
}

/// The dragon-book natural-loop bodies of `func`, keyed by loop header and
/// unioned per header (a header reached by several back edges owns one body).
/// Shared core of [`compute_loop_depths`] and [`compute_loop_info`]; returns an
/// EMPTY map for the bail-out cases the depth analysis skips (empty / >4096
/// blocks / out-of-range entry) so callers treat the function as loop-free.
fn natural_loop_bodies(func: &MachFunction) -> BTreeMap<usize, BTreeSet<usize>> {
    let n = func.blocks.len();
    // Conservative bail-out keeps the analysis's compile-time cost bounded.
    if n == 0 || n > 4096 {
        return BTreeMap::new();
    }
    let entry = func.entry_block.0 as usize;
    if entry >= n {
        return BTreeMap::new();
    }

    // --- Iterative dominators, one bitset row of `words` u64s per block. ---
    let words = n.div_ceil(64);
    // dom[b*words .. (b+1)*words] = the set of blocks that dominate `b`.
    // Non-entry rows start universal (dominated by everything) and shrink.
    let mut dom = vec![u64::MAX; n * words];
    let tail_mask = if n.is_multiple_of(64) {
        u64::MAX
    } else {
        (1u64 << (n % 64)) - 1
    };
    for b in 0..n {
        dom[b * words + (words - 1)] &= tail_mask;
    }
    // Entry is dominated only by itself.
    for w in 0..words {
        dom[entry * words + w] = 0;
    }
    dom[entry * words + entry / 64] = 1u64 << (entry % 64);

    // block_order is RPO-ish, which converges the fixpoint quickly.
    let order: Vec<usize> = if func.block_order.len() == n {
        func.block_order.iter().map(|b| b.0 as usize).collect()
    } else {
        (0..n).collect()
    };

    let mut scratch = vec![0u64; words];
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &order {
            if b == entry || b >= n {
                continue;
            }
            // new = ({b}) ∪ (∩ dom[p] over in-range predecessors p)
            let mut seen_pred = false;
            scratch.fill(u64::MAX);
            for pred in &func.blocks[b].preds {
                let p = pred.0 as usize;
                if p >= n {
                    continue;
                }
                for w in 0..words {
                    scratch[w] &= dom[p * words + w];
                }
                seen_pred = true;
            }
            if !seen_pred {
                // No in-range predecessor: dominated only by itself (do not
                // claim universal dominance for an unreachable block).
                scratch.fill(0);
            }
            scratch[b / 64] |= 1u64 << (b % 64);
            scratch[words - 1] &= tail_mask;

            let mut differs = false;
            for w in 0..words {
                if dom[b * words + w] != scratch[w] {
                    differs = true;
                    break;
                }
            }
            if differs {
                for w in 0..words {
                    dom[b * words + w] = scratch[w];
                }
                changed = true;
            }
        }
    }

    let dominates = |d: usize, b: usize| -> bool { (dom[b * words + d / 64] >> (d % 64)) & 1 == 1 };

    // --- Natural loops from back edges, unioned by header. ---
    let mut loop_bodies: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for u in 0..n {
        for succ in &func.blocks[u].succs {
            let v = succ.0 as usize;
            if v >= n {
                continue;
            }
            // Back edge: header `v` dominates its latch `u`.
            if dominates(v, u) {
                let body = loop_bodies.entry(v).or_default();
                collect_natural_loop_body(func, u, v, body);
            }
        }
    }

    loop_bodies
}

/// Add the dragon-book natural-loop body of back edge `latch -> header`:
/// the header plus every node that can reach `latch` without passing through
/// the header (backward reachability, stopping at the header).
fn collect_natural_loop_body(
    func: &MachFunction,
    latch: usize,
    header: usize,
    body: &mut BTreeSet<usize>,
) {
    body.insert(header);
    if body.insert(latch) {
        let mut stack = vec![latch];
        while let Some(m) = stack.pop() {
            for pred in &func.blocks[m].preds {
                let p = pred.0 as usize;
                if p < func.blocks.len() && body.insert(p) {
                    stack.push(p);
                }
            }
        }
    }
}

/// One dragon-book natural loop, keyed by its header block.
///
/// `forward_preds` are the header's predecessors that lie OUTSIDE the body — the
/// loop's forward ENTRY edges (a single such pred is a dedicated preheader and
/// DOMINATES the header, since every other predecessor is a latch/back edge from
/// within the body). STAGE-2 loop-reload placement uses this to place a reload
/// copy on the forward entry edge only, never a back edge (the header's
/// in-body predecessors).
#[derive(Debug, Clone)]
pub(crate) struct NaturalLoop {
    /// Header block index.
    pub header: usize,
    /// Every block in the natural loop body (includes the header and latches,
    /// and any nested-loop blocks).
    pub body: BTreeSet<usize>,
    /// Header predecessors outside the body: the forward ENTRY edges.
    pub forward_preds: Vec<usize>,
}

/// In-crate natural-loop query for the register allocator.
///
/// The regalloc crate has no dependency on `trust-cg-opt`, so loop structure is
/// derived here from the same dominator-based analysis that backs
/// [`compute_loop_depths`]. Built once per function and consulted by the
/// STAGE-2 loop-invariant reload selector in `split.rs`.
#[derive(Debug, Clone)]
pub(crate) struct LoopInfo {
    /// header block index -> its natural loop.
    loops: BTreeMap<usize, NaturalLoop>,
}

impl LoopInfo {
    /// True when the function has no natural loops (or the analysis bailed out).
    pub(crate) fn is_empty(&self) -> bool {
        self.loops.is_empty()
    }

    /// The natural loop headed by `header`, if any.
    pub(crate) fn get(&self, header: usize) -> Option<&NaturalLoop> {
        self.loops.get(&header)
    }

    /// Iterate every natural loop, in ascending header order (deterministic).
    pub(crate) fn iter(&self) -> impl Iterator<Item = &NaturalLoop> {
        self.loops.values()
    }

    /// The header of the SMALLEST natural loop whose body contains block `b` —
    /// i.e. the innermost loop `b` belongs to. `None` if `b` is in no loop.
    /// Ties on body size are broken by the smaller header index for a
    /// deterministic result.
    pub(crate) fn innermost_header_of(&self, b: usize) -> Option<usize> {
        self.loops
            .values()
            .filter(|l| l.body.contains(&b))
            .min_by_key(|l| (l.body.len(), l.header))
            .map(|l| l.header)
    }
}

/// Compute the [`LoopInfo`] for `func`: the natural loops plus each header's
/// forward-entry / back-edge predecessor split. Deterministic (BTree-backed).
pub(crate) fn compute_loop_info(func: &MachFunction) -> LoopInfo {
    let n = func.blocks.len();
    let bodies = natural_loop_bodies(func);
    let mut loops = BTreeMap::new();
    for (header, body) in bodies {
        let mut forward_preds = Vec::new();
        if let Some(hblk) = func.blocks.get(header) {
            for pred in &hblk.preds {
                let p = pred.0 as usize;
                if p >= n {
                    continue;
                }
                if !body.contains(&p) {
                    forward_preds.push(p);
                }
            }
        }
        loops.insert(
            header,
            NaturalLoop {
                header,
                body,
                forward_preds,
            },
        );
    }
    LoopInfo { loops }
}

fn prune_unreferenced_stack_slots(func: &mut MachFunction, candidate_slots: &[StackSlotId]) {
    if candidate_slots.is_empty() {
        return;
    }

    let referenced_slots = referenced_stack_slots(func);
    for slot in candidate_slots {
        if !referenced_slots.contains(slot) {
            func.stack_slots.remove(slot);
        }
    }
}

fn referenced_stack_slots(func: &MachFunction) -> std::collections::BTreeSet<StackSlotId> {
    func.blocks
        .iter()
        .flat_map(|block| block.insts.iter())
        .flat_map(|inst_id| {
            let inst = &func.insts[inst_id.0 as usize];
            inst.defs.iter().chain(inst.uses.iter())
        })
        .filter_map(|op| match op {
            MachOperand::StackSlot(slot) => Some(*slot),
            _ => None,
        })
        .collect()
}

/// Find the unique defining instruction for a VReg.
///
/// Scans all blocks for non-reload instructions that define the given full VReg
/// identity. Returns `None` if there are no definitions or more than one
/// definition.
fn find_single_defining_inst(func: &MachFunction, vreg: VReg) -> Option<InstId> {
    let mut found = None;
    for block in &func.blocks {
        for &inst_id in &block.insts {
            let inst = &func.insts[inst_id.0 as usize];
            if inst.opcode == PSEUDO_SPILL_LOAD {
                continue;
            }
            for def_op in &inst.defs {
                if let Some(def_vreg) = def_op.as_vreg()
                    && def_vreg == vreg
                {
                    if found.is_some() {
                        return None;
                    }
                    found = Some(inst_id);
                }
            }
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine_types::{
        BlockId, InstFlags, MachBlock, MachFunction, MachInst, MachOperand, PReg,
        RegAllocStackSlot, RegClass, StackSlotId, VReg,
    };
    use std::collections::BTreeMap;

    fn vreg_class(id: u32, class: RegClass) -> VReg {
        VReg { id, class }
    }

    fn vreg(id: u32) -> VReg {
        vreg_class(id, RegClass::Gpr64)
    }

    fn make_func(insts: Vec<MachInst>) -> MachFunction {
        let inst_ids: Vec<InstId> = (0..insts.len()).map(|i| InstId(i as u32)).collect();
        MachFunction {
            name: "test".into(),
            insts,
            blocks: vec![MachBlock {
                insts: inst_ids,
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 32,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        }
    }

    #[test]
    fn test_classify_free_remat() {
        // MOV Xd, #42 — only immediate uses.
        let inst = MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::Imm(42)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Free);
    }

    #[test]
    fn test_classify_cheap_remat() {
        // ADD Xd, Xn, #10 — one VReg + one immediate.
        let inst = MachInst {
            opcode: 2,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::VReg(vreg(1)), MachOperand::Imm(10)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Cheap);
    }

    #[test]
    fn test_classify_expensive_memory() {
        // LDR Xd, [Xn] — reads memory.
        let inst = MachInst {
            opcode: 3,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::VReg(vreg(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::READS_MEMORY,
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_classify_expensive_call() {
        let inst = MachInst {
            opcode: 4,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_CALL,
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_classify_expensive_multi_reg() {
        // ADD Xd, Xn, Xm — two VReg uses, no immediate.
        let inst = MachInst {
            opcode: 5,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::VReg(vreg(1)), MachOperand::VReg(vreg(2))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_find_remat_candidates() {
        let func = make_func(vec![
            // inst 0: MOV v0, #42 (Free remat)
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::Imm(42)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // inst 1: LDR v1, [v2] (Expensive)
            MachInst {
                opcode: 2,
                defs: vec![MachOperand::VReg(vreg(1))],
                uses: vec![MachOperand::VReg(vreg(2))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
        ]);

        let spilled = vec![vreg(0), vreg(1)];
        let candidates = find_remat_candidates(&func, &spilled);

        // Only v0 should be a candidate (Free remat).
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].vreg.id, 0);
        assert_eq!(candidates[0].cost, RematCost::Free);
    }

    #[test]
    fn test_find_remat_candidates_rejects_multiple_same_vreg_defs() {
        let func = make_func(vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::Imm(42)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::Imm(99)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ]);

        let candidates = find_remat_candidates(&func, &[vreg(0)]);

        assert!(
            candidates.is_empty(),
            "multiple non-reload definitions of the same full VReg must not rematerialize"
        );
    }

    #[test]
    fn test_find_remat_candidates_keeps_same_id_other_class_distinct() {
        let gpr_v0 = vreg_class(0, RegClass::Gpr64);
        let fpr_v0 = vreg_class(0, RegClass::Fpr64);
        let func = make_func(vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(gpr_v0)],
                uses: vec![MachOperand::Imm(42)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![MachOperand::VReg(fpr_v0)],
                uses: vec![MachOperand::FImm(1.25)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ]);

        let candidates = find_remat_candidates(&func, &[fpr_v0]);

        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].vreg, fpr_v0);
        assert_eq!(candidates[0].defining_inst_id, InstId(1));
    }

    #[test]
    fn test_apply_rematerialization() {
        let mut func = make_func(vec![
            // inst 0: MOV v0, #42 (defining instruction)
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::Imm(42)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // inst 1: SPILL_LOAD v0 from stack
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
            // inst 2: use v0
            MachInst {
                opcode: 3,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ]);

        let candidates = vec![RematCandidate {
            vreg: vreg(0),
            defining_inst_id: InstId(0),
            cost: RematCost::Free,
        }];

        let mut spill_infos = vec![SpillInfo {
            vreg: vreg(0),
            slot: StackSlotId(0),
        }];

        let count = apply_rematerialization(&mut func, &candidates, &mut spill_infos);

        assert_eq!(count, 1);
        assert!(spill_infos.is_empty()); // Spill info removed.

        // The spill load (inst position 1 in block) should be replaced.
        let replaced_inst_id = func.blocks[0].insts[1];
        let replaced_inst = &func.insts[replaced_inst_id.0 as usize];
        // Should now be a clone of the defining instruction (opcode 1, MOV).
        assert_eq!(replaced_inst.opcode, 1);
        assert_eq!(replaced_inst.uses.len(), 1);
        assert_eq!(replaced_inst.uses[0], MachOperand::Imm(42));
    }

    #[test]
    fn test_apply_remat_prunes_unreferenced_stack_slot_metadata() {
        let mut func = make_func(vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::Imm(42)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
        ]);
        func.stack_slots = BTreeMap::from([(StackSlotId(0), RegAllocStackSlot::new(8, 8))]);

        let candidates = vec![RematCandidate {
            vreg: vreg(0),
            defining_inst_id: InstId(0),
            cost: RematCost::Free,
        }];
        let mut spill_infos = vec![SpillInfo {
            vreg: vreg(0),
            slot: StackSlotId(0),
        }];

        let count = apply_rematerialization(&mut func, &candidates, &mut spill_infos);

        assert_eq!(count, 1);
        assert!(spill_infos.is_empty());
        assert!(!func.stack_slots.contains_key(&StackSlotId(0)));
    }

    #[test]
    fn test_apply_remat_keeps_stack_slot_metadata_when_still_referenced() {
        let mut func = make_func(vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::Imm(42)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(vreg(1))],
                uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
        ]);
        func.stack_slots = BTreeMap::from([(StackSlotId(0), RegAllocStackSlot::new(8, 8))]);

        let candidates = vec![RematCandidate {
            vreg: vreg(0),
            defining_inst_id: InstId(0),
            cost: RematCost::Free,
        }];
        let mut spill_infos = vec![
            SpillInfo {
                vreg: vreg(0),
                slot: StackSlotId(0),
            },
            SpillInfo {
                vreg: vreg(1),
                slot: StackSlotId(0),
            },
        ];

        let count = apply_rematerialization(&mut func, &candidates, &mut spill_infos);

        assert_eq!(count, 1);
        assert_eq!(spill_infos.len(), 1);
        assert_eq!(spill_infos[0].vreg, vreg(1));
        assert_eq!(spill_infos[0].slot, StackSlotId(0));
        assert!(func.stack_slots.contains_key(&StackSlotId(0)));
        let preserved_load_id = func.blocks[0].insts[2];
        assert_eq!(
            func.insts[preserved_load_id.0 as usize].opcode,
            PSEUDO_SPILL_LOAD
        );
    }

    // -----------------------------------------------------------------------
    // Additional edge-case and correctness tests (issue #139)
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_expensive_side_effects() {
        let inst = MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::Imm(0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::HAS_SIDE_EFFECTS,
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_classify_expensive_writes_memory() {
        let inst = MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::VReg(vreg(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::WRITES_MEMORY,
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_classify_expensive_phi() {
        let inst = MachInst {
            opcode: 0x00,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::VReg(vreg(1)), MachOperand::VReg(vreg(2))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_PHI,
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_classify_expensive_branch() {
        let inst = MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_classify_expensive_block_operand() {
        // Even without special flags, a Block operand makes it expensive.
        let inst = MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::Block(BlockId(0))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_classify_expensive_stack_slot_operand() {
        let inst = MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::StackSlot(StackSlotId(0))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_classify_free_fimm() {
        // FMOV Dd, #2.78 — float immediate, no register uses.
        let inst = MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::FImm(2.78)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Free);
    }

    #[test]
    fn test_classify_expensive_no_uses() {
        // No uses at all (and no immediates) -> Expensive (not Free).
        let inst = MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_classify_expensive_preg_use() {
        // Physical register use counts as a register use.
        let inst = MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::PReg(PReg::new(0))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        // One PReg use, zero imms -> Expensive (no imm for Cheap).
        assert_eq!(classify_remat_cost(&inst), RematCost::Expensive);
    }

    #[test]
    fn test_classify_cheap_preg_plus_imm() {
        // PReg + Imm counts as Cheap (one register + one immediate).
        let inst = MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::PReg(PReg::new(0)), MachOperand::Imm(5)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        assert_eq!(classify_remat_cost(&inst), RematCost::Cheap);
    }

    #[test]
    fn test_find_remat_candidates_no_spills() {
        let func = make_func(vec![MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::Imm(42)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }]);
        let candidates = find_remat_candidates(&func, &[]);
        assert!(candidates.is_empty());
    }

    #[test]
    fn test_apply_remat_multiple_loads() {
        // Two spill loads for the same vreg should both be replaced.
        let mut func = make_func(vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::Imm(99)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
            MachInst {
                opcode: 3,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
            MachInst {
                opcode: 4,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ]);

        let candidates = vec![RematCandidate {
            vreg: vreg(0),
            defining_inst_id: InstId(0),
            cost: RematCost::Free,
        }];
        let mut spill_infos = vec![SpillInfo {
            vreg: vreg(0),
            slot: StackSlotId(0),
        }];

        let count = apply_rematerialization(&mut func, &candidates, &mut spill_infos);
        assert_eq!(count, 2, "should rematerialize both spill loads");
        assert!(spill_infos.is_empty());
    }

    #[test]
    fn test_apply_remat_preserves_non_candidate_loads() {
        // v0 is a remat candidate, v1 is not. Only v0's loads should be replaced.
        let mut func = make_func(vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::Imm(42)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(vreg(1))],
                uses: vec![MachOperand::StackSlot(StackSlotId(1))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
        ]);

        let candidates = vec![RematCandidate {
            vreg: vreg(0),
            defining_inst_id: InstId(0),
            cost: RematCost::Free,
        }];
        let mut spill_infos = vec![
            SpillInfo {
                vreg: vreg(0),
                slot: StackSlotId(0),
            },
            SpillInfo {
                vreg: vreg(1),
                slot: StackSlotId(1),
            },
        ];

        let count = apply_rematerialization(&mut func, &candidates, &mut spill_infos);
        assert_eq!(count, 1, "only v0's load should be replaced");
        assert_eq!(spill_infos.len(), 1, "v1's spill info should remain");
        assert_eq!(spill_infos[0].vreg.id, 1);
    }

    #[test]
    fn test_remat_matches_full_vreg_identity() {
        let gpr_v0 = vreg_class(0, RegClass::Gpr64);
        let fpr_v0 = vreg_class(0, RegClass::Fpr64);
        let mut func = make_func(vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(gpr_v0)],
                uses: vec![MachOperand::Imm(42)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![MachOperand::VReg(fpr_v0)],
                uses: vec![MachOperand::FImm(1.25)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(fpr_v0)],
                uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(gpr_v0)],
                uses: vec![MachOperand::StackSlot(StackSlotId(1))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
        ]);

        let candidates = find_remat_candidates(&func, &[fpr_v0]);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].vreg, fpr_v0);
        assert_eq!(candidates[0].defining_inst_id, InstId(1));

        let mut spill_infos = vec![
            SpillInfo {
                vreg: fpr_v0,
                slot: StackSlotId(0),
            },
            SpillInfo {
                vreg: gpr_v0,
                slot: StackSlotId(1),
            },
        ];

        let count = apply_rematerialization(&mut func, &candidates, &mut spill_infos);
        assert_eq!(count, 1);
        assert_eq!(spill_infos.len(), 1);
        assert_eq!(spill_infos[0].vreg, gpr_v0);

        let fpr_load_replacement = func.blocks[0].insts[2];
        let gpr_load = func.blocks[0].insts[3];
        assert_eq!(func.insts[fpr_load_replacement.0 as usize].opcode, 2);
        assert_eq!(func.insts[gpr_load.0 as usize].opcode, PSEUDO_SPILL_LOAD);
    }

    // -----------------------------------------------------------------------
    // Additional edge-case tests (issue #404 — TL7 coverage expansion)
    // -----------------------------------------------------------------------

    #[test]
    fn test_apply_remat_cheap_cost_candidate() {
        // Test rematerialization with a Cheap candidate (one VReg + imm).
        let mut func = make_func(vec![
            // inst 0: ADD v0, v1, #10 (Cheap remat — one vreg + imm)
            MachInst {
                opcode: 2,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::VReg(vreg(1)), MachOperand::Imm(10)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // inst 1: SPILL_LOAD v0 from stack
            MachInst {
                opcode: PSEUDO_SPILL_LOAD,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::READS_MEMORY,
                tied_operands: vec![],
            },
            // inst 2: use v0
            MachInst {
                opcode: 3,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ]);

        let candidates = vec![RematCandidate {
            vreg: vreg(0),
            defining_inst_id: InstId(0),
            cost: RematCost::Cheap,
        }];

        let mut spill_infos = vec![SpillInfo {
            vreg: vreg(0),
            slot: StackSlotId(0),
        }];

        let count = apply_rematerialization(&mut func, &candidates, &mut spill_infos);
        assert_eq!(count, 1, "cheap candidate should be rematerialized");
        assert!(spill_infos.is_empty(), "spill info should be removed");

        // The replacement instruction should be a clone of the defining ADD.
        let replaced_id = func.blocks[0].insts[1];
        let replaced_inst = &func.insts[replaced_id.0 as usize];
        assert_eq!(replaced_inst.opcode, 2, "should be cloned ADD instruction");
        assert_eq!(replaced_inst.uses.len(), 2);
    }

    #[test]
    fn test_find_remat_no_defining_instruction() {
        // A spilled vreg with no definition in the function should not be a candidate.
        let func = make_func(vec![
            // Only uses v5, never defines it.
            MachInst {
                opcode: 3,
                defs: vec![],
                uses: vec![MachOperand::VReg(VReg {
                    id: 5,
                    class: RegClass::Gpr64,
                })],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ]);

        let candidates = find_remat_candidates(
            &func,
            &[VReg {
                id: 5,
                class: RegClass::Gpr64,
            }],
        );
        assert!(
            candidates.is_empty(),
            "vreg with no def should not be a remat candidate"
        );
    }

    // -----------------------------------------------------------------------
    // Loop-depth guard (hoist-preserving rematerialization)
    // -----------------------------------------------------------------------

    #[test]
    fn test_compute_loop_depths_nested() {
        // 0(entry) -> 1(outer hdr) -> 2(inner hdr, self-loop) -> 3(outer latch)
        //   -> 1 (back edge) / -> 4(exit). Depths: [0,1,2,1,0].
        let mb = |insts: Vec<InstId>, preds: Vec<BlockId>, succs: Vec<BlockId>| MachBlock {
            insts,
            preds,
            succs,
            loop_depth: 0,
        };
        let func = MachFunction {
            name: "nested".into(),
            insts: vec![],
            blocks: vec![
                mb(vec![], vec![], vec![BlockId(1)]),
                mb(vec![], vec![BlockId(0), BlockId(3)], vec![BlockId(2)]),
                mb(
                    vec![],
                    vec![BlockId(1), BlockId(2)],
                    vec![BlockId(2), BlockId(3)],
                ),
                mb(vec![], vec![BlockId(2)], vec![BlockId(1), BlockId(4)]),
                mb(vec![], vec![BlockId(3)], vec![]),
            ],
            block_order: (0..5).map(BlockId).collect(),
            entry_block: BlockId(0),
            next_vreg: 0,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        assert_eq!(compute_loop_depths(&func), vec![0, 1, 2, 1, 0]);
    }

    #[test]
    fn test_remat_suppressed_into_strictly_deeper_loop() {
        // A Free def (adrp-like) in the entry (loop depth 0) whose only spill
        // load sits in a self-looping body block (loop depth 1). Cloning the def
        // there would undo the hoist, so the guard SUPPRESSES the remat: the
        // spill reload stays and the spill slot/info are retained.
        let mb = |insts: Vec<InstId>, preds: Vec<BlockId>, succs: Vec<BlockId>| MachBlock {
            insts,
            preds,
            succs,
            loop_depth: 0,
        };
        let mut func = MachFunction {
            name: "remat_depth_guard".into(),
            insts: vec![
                // inst 0: Free def of v0 in the entry block.
                MachInst {
                    opcode: 1,
                    defs: vec![MachOperand::VReg(vreg(0))],
                    uses: vec![MachOperand::Imm(0)],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: InstFlags::default(),
                    tied_operands: vec![],
                },
                // inst 1: spill load of v0 inside the loop body.
                MachInst {
                    opcode: PSEUDO_SPILL_LOAD,
                    defs: vec![MachOperand::VReg(vreg(0))],
                    uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: InstFlags::READS_MEMORY,
                    tied_operands: vec![],
                },
                // inst 2: a use of v0 in the loop body.
                MachInst {
                    opcode: 3,
                    defs: vec![],
                    uses: vec![MachOperand::VReg(vreg(0))],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: InstFlags::default(),
                    tied_operands: vec![],
                },
            ],
            blocks: vec![
                mb(vec![InstId(0)], vec![], vec![BlockId(1)]),
                mb(
                    vec![InstId(1), InstId(2)],
                    vec![BlockId(0), BlockId(1)],
                    vec![BlockId(1), BlockId(2)],
                ),
                mb(vec![], vec![BlockId(1)], vec![]),
            ],
            block_order: (0..3).map(BlockId).collect(),
            entry_block: BlockId(0),
            next_vreg: 32,
            next_stack_slot: 1,
            stack_slots: BTreeMap::from([(StackSlotId(0), RegAllocStackSlot::new(8, 8))]),
        };

        let candidates = vec![RematCandidate {
            vreg: vreg(0),
            defining_inst_id: InstId(0),
            cost: RematCost::Free,
        }];
        let mut spill_infos = vec![SpillInfo {
            vreg: vreg(0),
            slot: StackSlotId(0),
        }];

        let count = apply_rematerialization(&mut func, &candidates, &mut spill_infos);
        assert_eq!(
            count, 0,
            "remat into a strictly deeper loop must be suppressed"
        );
        assert_eq!(spill_infos.len(), 1, "suppressed vreg keeps its spill info");
        assert!(
            func.stack_slots.contains_key(&StackSlotId(0)),
            "spill slot must be retained when the reload stays"
        );
        // The spill load in the loop body is unchanged (not a remat clone).
        let load_id = func.blocks[1].insts[0];
        assert_eq!(func.insts[load_id.0 as usize].opcode, PSEUDO_SPILL_LOAD);
    }

    #[test]
    fn test_remat_allowed_at_same_loop_depth() {
        // Same shape, but the def is INSIDE the loop body alongside its use (both
        // at loop depth 1). No deepening occurs, so remat proceeds as before.
        let mb = |insts: Vec<InstId>, preds: Vec<BlockId>, succs: Vec<BlockId>| MachBlock {
            insts,
            preds,
            succs,
            loop_depth: 0,
        };
        let mut func = MachFunction {
            name: "remat_same_depth".into(),
            insts: vec![
                // inst 0: Free def of v0 in the loop body.
                MachInst {
                    opcode: 1,
                    defs: vec![MachOperand::VReg(vreg(0))],
                    uses: vec![MachOperand::Imm(0)],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: InstFlags::default(),
                    tied_operands: vec![],
                },
                // inst 1: spill load of v0 in the same loop body.
                MachInst {
                    opcode: PSEUDO_SPILL_LOAD,
                    defs: vec![MachOperand::VReg(vreg(0))],
                    uses: vec![MachOperand::StackSlot(StackSlotId(0))],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: InstFlags::READS_MEMORY,
                    tied_operands: vec![],
                },
            ],
            blocks: vec![
                mb(vec![], vec![], vec![BlockId(1)]),
                mb(
                    vec![InstId(0), InstId(1)],
                    vec![BlockId(0), BlockId(1)],
                    vec![BlockId(1), BlockId(2)],
                ),
                mb(vec![], vec![BlockId(1)], vec![]),
            ],
            block_order: (0..3).map(BlockId).collect(),
            entry_block: BlockId(0),
            next_vreg: 32,
            next_stack_slot: 1,
            stack_slots: BTreeMap::from([(StackSlotId(0), RegAllocStackSlot::new(8, 8))]),
        };

        let candidates = vec![RematCandidate {
            vreg: vreg(0),
            defining_inst_id: InstId(0),
            cost: RematCost::Free,
        }];
        let mut spill_infos = vec![SpillInfo {
            vreg: vreg(0),
            slot: StackSlotId(0),
        }];

        let count = apply_rematerialization(&mut func, &candidates, &mut spill_infos);
        assert_eq!(count, 1, "remat at equal loop depth must proceed");
        assert!(
            spill_infos.is_empty(),
            "fully rematerialized vreg drops its spill info"
        );
    }

    #[test]
    fn test_apply_remat_empty_candidates() {
        // No candidates — nothing should happen.
        let mut func = make_func(vec![MachInst {
            opcode: PSEUDO_SPILL_LOAD,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::StackSlot(StackSlotId(0))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::READS_MEMORY,
            tied_operands: vec![],
        }]);

        let mut spill_infos = vec![SpillInfo {
            vreg: vreg(0),
            slot: StackSlotId(0),
        }];

        let count = apply_rematerialization(&mut func, &[], &mut spill_infos);
        assert_eq!(count, 0, "no candidates means no rematerialization");
        assert_eq!(spill_infos.len(), 1, "spill info should be preserved");
    }
}
