// trust-cg-regalloc/split.rs - Live interval splitting
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Live interval splitting for the register allocator.
//!
//! When a long interval is expensive to spill, we can split it around
//! uses instead of spilling the whole thing. This reduces spill code by
//! keeping the value in a register only where it's actually needed.
//!
//! The algorithm finds optimal split points by analyzing gaps between
//! consecutive use/def positions and splitting at the largest gap.
//!
//! Reference: LLVM `SplitKit.cpp` — simplified for our linear-scan context.

use crate::liveness::LiveInterval;
use crate::machine_types::{BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand, VReg};
use crate::phi_elim;

/// Describes where to split a live interval.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SplitDecision {
    /// No beneficial split exists.
    NoSplit,
    /// Split just before a use at the given instruction index.
    SplitBeforeUse(u32),
    /// Split just after a def at the given instruction index.
    SplitAfterDef(u32),
    /// Split around a region, creating a hole in [start, end).
    SplitAroundRegion { start: u32, end: u32 },
}

/// Result of splitting a live interval.
#[derive(Debug, Clone)]
pub struct SplitResult {
    /// The original virtual register (interval truncated).
    pub original_vreg: VReg,
    /// The new virtual register (covers the split-off portion).
    pub new_vreg: VReg,
    /// The truncated original interval, kept live through the boundary copy.
    pub original_interval: LiveInterval,
    /// The new interval (covers [split_point, orig_end)).
    pub new_interval: LiveInterval,
}

/// Reason an attempted split point cannot be materialized.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SplitError {
    /// The split point is outside the interval's overall extent.
    SplitPointOutOfRange {
        split_point: u32,
        interval_start: u32,
        interval_end: u32,
    },
    /// The split point falls in a hole where the source value is not live.
    SplitPointOutsideLiveRange { split_point: u32 },
    /// The split would require CFG copy placement that is not implemented yet.
    UnsafeCfg(SplitCfgSafetyError),
    /// One side of the split would be empty.
    EmptySplit,
    /// The split would leave one child identical to the parent interval.
    NonProgress,
}

/// CFG-specific reason split-copy insertion is unsafe.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SplitCfgSafetyError {
    /// A copy at the start of a multi-pred block must be placed on incoming edges.
    MultiPredBlockStart { block: BlockId, point: u32 },
    /// An incoming split copy would need a critical edge to be split first.
    CriticalEdgeCopyPlacement {
        predecessor: BlockId,
        successor: BlockId,
        point: u32,
    },
    /// An incoming split copy has no terminator position to anchor before.
    MissingEdgeCopyTerminator {
        predecessor: BlockId,
        successor: BlockId,
        point: u32,
    },
    /// The predecessor is laid out after the join, so linear live ranges would
    /// see the edge copy after the joined uses.
    NonLinearEdgeCopyLayout {
        predecessor: BlockId,
        successor: BlockId,
        copy_pos: u32,
        join_pos: u32,
    },
    /// An incoming split copy would need to be placed on a loop backedge.
    /// Linear intervals cannot model the next-iteration value yet.
    BackedgeCopyPlacement {
        predecessor: BlockId,
        successor: BlockId,
        copy_pos: u32,
        join_pos: u32,
    },
    /// A split in a cyclic block needs loop/backedge repair copies.
    LoopOrBackedgeBlock { block: BlockId, point: u32 },
    /// The insertion block does not dominate a rewritten use/def.
    NonDominatingPlacement {
        insertion_block: BlockId,
        rewrite_block: BlockId,
        rewrite_pos: u32,
    },
    /// The in-block point sits STRICTLY AFTER the block's first terminator
    /// (insertion is before-the-point, so equality still precedes the whole
    /// group). A machine conditional branch is a TWO-terminator group (x86
    /// `Jcc; Jmp`, aarch64 `B.cond; B`): a connector copy inserted between
    /// them executes ONLY on the fall-through edge, leaving the split child
    /// undefined on the taken edge — a silent miscompile (bug #66's exact
    /// mechanism; the taken-edge successor read overflow-check scraps as the
    /// split value). Terminator positions look like free "gap" to the
    /// midpoint chooser because branches use/def no vregs, so this must fail
    /// closed here.
    PointInsideTerminatorSequence {
        block: BlockId,
        point: u32,
        first_terminator_pos: u32,
    },
}

/// Analyze an interval for split candidates.
///
/// Returns a list of beneficial split decisions ordered by quality
/// (largest gap first). An empty list means no beneficial split exists.
pub fn analyze_split_candidates(
    interval: &LiveInterval,
    _active_intervals: &[&LiveInterval],
    _allocatable_count: usize,
) -> Vec<SplitDecision> {
    let mut decisions = Vec::new();

    // Collect all use/def positions and sort them.
    let mut positions: Vec<u32> = interval
        .use_positions
        .iter()
        .chain(interval.def_positions.iter())
        .copied()
        .collect();
    positions.sort_unstable();
    positions.dedup();

    if positions.len() < 2 {
        return decisions;
    }

    // Find gaps between consecutive positions and score them.
    let mut gaps: Vec<(u32, u32, u32)> = Vec::new(); // (gap_size, start, end)
    for window in positions.windows(2) {
        let gap_start = window[0] + 1;
        let gap_end = window[1];
        if gap_end > gap_start {
            gaps.push((gap_end - gap_start, gap_start, gap_end));
        }
    }

    // Sort by gap size descending (largest gaps first — best split candidates).
    gaps.sort_by_key(|gap| std::cmp::Reverse(gap.0));

    for (gap_size, gap_start, gap_end) in gaps {
        // Only consider splits where the gap is at least 2 instructions wide.
        if gap_size >= 2 {
            decisions.push(SplitDecision::SplitAroundRegion {
                start: gap_start,
                end: gap_end,
            });
        } else {
            decisions.push(SplitDecision::SplitBeforeUse(gap_end));
        }
    }

    if decisions.is_empty() {
        decisions.push(SplitDecision::NoSplit);
    }

    decisions
}

/// Find the optimal split point for a live interval.
///
/// The optimal split point is at the middle of the largest gap between
/// consecutive use/def positions, minimizing the register pressure on
/// both sides.
pub fn find_optimal_split_point(interval: &LiveInterval) -> Option<u32> {
    let mut positions: Vec<u32> = interval
        .use_positions
        .iter()
        .chain(interval.def_positions.iter())
        .copied()
        .collect();
    positions.sort_unstable();
    positions.dedup();

    if positions.len() < 2 {
        return None;
    }

    let mut best_gap = 0u32;
    let mut best_mid = None;

    for window in positions.windows(2) {
        let gap = window[1].saturating_sub(window[0]);
        if gap > best_gap {
            best_gap = gap;
            best_mid = Some(window[0] + gap / 2);
        }
    }

    // Only split if the gap is meaningful (at least 2 instructions).
    if best_gap >= 2 { best_mid } else { None }
}

/// Split a live interval at the given split point.
///
/// Creates two intervals:
/// - Original: covers ranges before the split point.
/// - New: covers ranges at and after the split point.
///
/// A `PSEUDO_COPY` instruction is inserted to connect them: the new VReg
/// is defined as a copy of the original at the split point.
///
/// Returns `None` if the split point is outside the interval or would
/// produce empty intervals.
pub fn split_interval(
    interval: &LiveInterval,
    split_point: u32,
    func: &mut MachFunction,
) -> Option<SplitResult> {
    split_interval_checked(interval, split_point, func).ok()
}

/// Split a live interval and report why unsupported split points fail.
pub fn split_interval_checked(
    interval: &LiveInterval,
    split_point: u32,
    func: &mut MachFunction,
) -> Result<SplitResult, SplitError> {
    // Validate: split point must be within the interval's overall extent.
    if split_point <= interval.start() || split_point >= interval.end() {
        return Err(SplitError::SplitPointOutOfRange {
            split_point,
            interval_start: interval.start(),
            interval_end: interval.end(),
        });
    }
    if !interval
        .ranges
        .iter()
        .any(|range| range.start < split_point && split_point < range.end)
    {
        return Err(SplitError::SplitPointOutsideLiveRange { split_point });
    }
    let rewrite_positions = split_rewrite_positions(interval, split_point);
    let copy_plan =
        split_copy_plan(func, split_point, &rewrite_positions).map_err(SplitError::UnsafeCfg)?;

    let original_vreg = interval.vreg;
    let new_vreg = func.alloc_vreg(original_vreg.class);

    // Build the two new intervals by partitioning ranges.
    let mut original_interval = LiveInterval::new(original_vreg);
    let mut new_interval = LiveInterval::new(new_vreg);

    for range in &interval.ranges {
        if range.end <= split_point {
            // Entirely before split.
            original_interval.add_range(range.start, range.end);
        } else if range.start >= split_point {
            // Entirely after split.
            new_interval.add_range(range.start, range.end);
        } else {
            // Range spans the split point. The split copy reads the original
            // vreg at the planned copy position, so keep the source live
            // through the in-block boundary copy or only up to the join when
            // copies are placed on incoming edges.
            original_interval.add_range(
                range.start,
                copy_plan.original_spanning_range_end(split_point),
            );
            new_interval.add_range(split_point, range.end);
        }
    }
    copy_plan.extend_intervals_for_copies(split_point, &mut original_interval, &mut new_interval);

    // Don't split if either side would be empty.
    if original_interval.ranges.is_empty() || new_interval.ranges.is_empty() {
        return Err(SplitError::EmptySplit);
    }
    if original_interval.ranges == interval.ranges || new_interval.ranges == interval.ranges {
        return Err(SplitError::NonProgress);
    }

    // Partition use/def positions.
    for &pos in &interval.use_positions {
        if pos < split_point {
            original_interval.use_positions.push(pos);
        } else {
            new_interval.use_positions.push(pos);
        }
    }
    for &pos in &interval.def_positions {
        if pos < split_point {
            original_interval.def_positions.push(pos);
        } else {
            new_interval.def_positions.push(pos);
        }
    }
    copy_plan.add_copy_positions_to_intervals(&mut original_interval, &mut new_interval);
    original_interval.use_positions.sort_unstable();
    original_interval.use_positions.dedup();
    new_interval.def_positions.sort_unstable();
    new_interval.def_positions.dedup();

    // `spill_weight` is used as an allocation priority/density, not a total
    // cost budget. Keep split children at the parent's priority so a useful
    // fragment is not made artificially cheap just because it got shorter.
    original_interval.spill_weight = interval.spill_weight;
    new_interval.spill_weight = interval.spill_weight;

    rewrite_split_operands(func, original_vreg, new_vreg, split_point, &new_interval);

    copy_plan.insert_copies(func, original_vreg, new_vreg);

    Ok(SplitResult {
        original_vreg,
        new_vreg,
        original_interval,
        new_interval,
    })
}

fn rewrite_split_operands(
    func: &mut MachFunction,
    original_vreg: VReg,
    new_vreg: VReg,
    split_point: u32,
    new_interval: &LiveInterval,
) {
    let mut rewrite_positions: Vec<u32> = new_interval
        .use_positions
        .iter()
        .chain(new_interval.def_positions.iter())
        .copied()
        .filter(|&pos| pos >= split_point)
        .collect();
    rewrite_positions.sort_unstable();
    rewrite_positions.dedup();

    if rewrite_positions.is_empty() {
        return;
    }

    let mut pos = 0u32;
    for &block_id in &func.block_order {
        let block_idx = block_id.0 as usize;
        let insts = func.blocks[block_idx].insts.clone();
        for inst_id in insts {
            let should_rewrite = rewrite_positions.binary_search(&pos).is_ok();
            if is_inserted_split_copy(func, inst_id) {
                if should_rewrite && let Some(inst) = func.insts.get_mut(inst_id.0 as usize) {
                    rewrite_vreg_operands(&mut inst.uses, original_vreg, new_vreg);
                }
                continue;
            }
            if should_rewrite && let Some(inst) = func.insts.get_mut(inst_id.0 as usize) {
                rewrite_vreg_operands(&mut inst.defs, original_vreg, new_vreg);
                rewrite_vreg_operands(&mut inst.uses, original_vreg, new_vreg);
            }
            pos += 1;
        }
    }
}

fn rewrite_vreg_operands(operands: &mut [MachOperand], original_vreg: VReg, new_vreg: VReg) {
    for operand in operands {
        if let MachOperand::VReg(vreg) = operand
            && *vreg == original_vreg
        {
            *vreg = new_vreg;
        }
    }
}

fn is_inserted_split_copy(func: &MachFunction, inst_id: InstId) -> bool {
    func.insts.get(inst_id.0 as usize).is_some_and(|inst| {
        inst.opcode == phi_elim::PSEUDO_COPY && inst.flags.contains(InstFlags::IS_PSEUDO)
    })
}

fn split_rewrite_positions(interval: &LiveInterval, split_point: u32) -> Vec<u32> {
    let mut rewrite_positions: Vec<u32> = interval
        .use_positions
        .iter()
        .chain(interval.def_positions.iter())
        .copied()
        .filter(|&pos| pos >= split_point)
        .collect();
    rewrite_positions.sort_unstable();
    rewrite_positions.dedup();
    rewrite_positions
}

#[derive(Debug, Clone)]
enum SplitCopyPlan {
    InBlock {
        point: u32,
    },
    JoinBlockStart {
        point: u32,
        original_live_through: Vec<BlockLiveSpan>,
    },
    IncomingEdges {
        copies: Vec<EdgeCopyPlacement>,
    },
}

#[derive(Debug, Clone)]
struct BlockLiveSpan {
    start: u32,
    end: u32,
}

#[derive(Debug, Clone)]
struct EdgeCopyPlacement {
    predecessor: BlockId,
    copy_pos: u32,
}

impl SplitCopyPlan {
    fn original_spanning_range_end(&self, split_point: u32) -> u32 {
        match self {
            SplitCopyPlan::InBlock { .. } | SplitCopyPlan::JoinBlockStart { .. } => split_point + 1,
            SplitCopyPlan::IncomingEdges { .. } => split_point,
        }
    }

    fn extend_intervals_for_copies(
        &self,
        split_point: u32,
        original_interval: &mut LiveInterval,
        new_interval: &mut LiveInterval,
    ) {
        match self {
            SplitCopyPlan::InBlock { .. } => {}
            SplitCopyPlan::JoinBlockStart {
                original_live_through,
                ..
            } => {
                for span in original_live_through {
                    original_interval.add_range(span.start, span.end);
                }
            }
            SplitCopyPlan::IncomingEdges { copies } => {
                for copy in copies {
                    original_interval.add_range(copy.copy_pos, copy.copy_pos + 1);
                    new_interval.add_range(copy.copy_pos, split_point + 1);
                }
            }
        }
    }

    fn add_copy_positions_to_intervals(
        &self,
        original_interval: &mut LiveInterval,
        new_interval: &mut LiveInterval,
    ) {
        match self {
            SplitCopyPlan::InBlock { point } | SplitCopyPlan::JoinBlockStart { point, .. } => {
                original_interval.use_positions.push(*point);
                new_interval.def_positions.push(*point);
            }
            SplitCopyPlan::IncomingEdges { copies } => {
                for copy in copies {
                    original_interval.use_positions.push(copy.copy_pos);
                    new_interval.def_positions.push(copy.copy_pos);
                }
            }
        }
    }

    fn insert_copies(&self, func: &mut MachFunction, original_vreg: VReg, new_vreg: VReg) {
        match self {
            SplitCopyPlan::InBlock { point } | SplitCopyPlan::JoinBlockStart { point, .. } => {
                let copy_id = push_split_copy(func, original_vreg, new_vreg);
                insert_copy_at_point(func, copy_id, *point);
            }
            SplitCopyPlan::IncomingEdges { copies } => {
                for copy in copies {
                    let copy_id = push_split_copy(func, original_vreg, new_vreg);
                    insert_copy_on_incoming_edge(func, copy_id, copy.predecessor);
                }
            }
        }
    }
}

fn push_split_copy(func: &mut MachFunction, original_vreg: VReg, new_vreg: VReg) -> InstId {
    let copy_inst = MachInst {
        opcode: phi_elim::PSEUDO_COPY,
        defs: vec![MachOperand::VReg(new_vreg)],
        uses: vec![MachOperand::VReg(original_vreg)],
        implicit_defs: Vec::new(),
        implicit_uses: Vec::new(),
        flags: InstFlags::IS_PSEUDO,
        tied_operands: vec![],
    };

    let copy_id = InstId(func.insts.len() as u32);
    func.insts.push(copy_inst);
    copy_id
}

fn split_copy_plan(
    func: &MachFunction,
    point: u32,
    rewrite_positions: &[u32],
) -> Result<SplitCopyPlan, SplitCfgSafetyError> {
    let Some((insertion_block, insertion_block_start, _)) = block_for_split_point(func, point)
    else {
        return Ok(SplitCopyPlan::InBlock { point });
    };
    let insertion = &func.blocks[insertion_block.0 as usize];

    let plan = if point == insertion_block_start && insertion.preds.len() > 1 {
        match incoming_edge_copy_placements(func, insertion_block, insertion_block_start, point) {
            Ok(copies) => SplitCopyPlan::IncomingEdges { copies },
            Err(err @ SplitCfgSafetyError::BackedgeCopyPlacement { .. }) => return Err(err),
            Err(_) => join_block_start_copy_plan(func, insertion_block, insertion_block_start)?,
        }
    } else {
        SplitCopyPlan::InBlock { point }
    };

    // An in-block connector must precede the block's FIRST terminator: after
    // it, the copy runs only on the fall-through edge of a multi-terminator
    // branch group (x86 `Jcc; Jmp`) and the split child is undefined on every
    // other edge. [`insert_copy_at_point`] inserts BEFORE the instruction at
    // the point, so `point == first_terminator_pos` still places the copy
    // ahead of the whole terminator group (safe — and the common entry-block
    // fallback split point); only a STRICTLY greater point lands inside the
    // group. The edge plans already anchor before the first terminator
    // ([`edge_copy_position`]); this closes the same hazard for the in-block
    // arm. Fail-closed: a declined split only costs code quality — greedy
    // falls back to spilling.
    if let SplitCopyPlan::InBlock { point: in_point } = plan
        && let Some(first_terminator_pos) = edge_copy_position(func, insertion_block)
        && in_point > first_terminator_pos
    {
        return Err(SplitCfgSafetyError::PointInsideTerminatorSequence {
            block: insertion_block,
            point: in_point,
            first_terminator_pos,
        });
    }

    if block_participates_in_cycle(func, insertion_block) {
        return Err(SplitCfgSafetyError::LoopOrBackedgeBlock {
            block: insertion_block,
            point,
        });
    }

    for pos in rewrite_positions.iter().copied() {
        if let Some((rewrite_block, _, _)) = block_for_split_point(func, pos)
            && !cfg_dominates_block(func, insertion_block, rewrite_block)
        {
            return Err(SplitCfgSafetyError::NonDominatingPlacement {
                insertion_block,
                rewrite_block,
                rewrite_pos: pos,
            });
        }
    }

    Ok(plan)
}

fn join_block_start_copy_plan(
    func: &MachFunction,
    join_block: BlockId,
    join_pos: u32,
) -> Result<SplitCopyPlan, SplitCfgSafetyError> {
    let join = &func.blocks[join_block.0 as usize];
    let mut original_live_through = Vec::new();

    for &predecessor in &join.preds {
        let Some(pred) = func.blocks.get(predecessor.0 as usize) else {
            return Err(SplitCfgSafetyError::CriticalEdgeCopyPlacement {
                predecessor,
                successor: join_block,
                point: join_pos,
            });
        };
        if !pred.succs.contains(&join_block) {
            return Err(SplitCfgSafetyError::CriticalEdgeCopyPlacement {
                predecessor,
                successor: join_block,
                point: join_pos,
            });
        }
        if edge_is_backedge(func, predecessor, join_block) {
            let copy_pos = edge_copy_position(func, predecessor)
                .or_else(|| block_layout_span(func, predecessor).map(|(_, end)| end))
                .unwrap_or(join_pos);
            return Err(SplitCfgSafetyError::BackedgeCopyPlacement {
                predecessor,
                successor: join_block,
                copy_pos,
                join_pos,
            });
        }

        let Some((pred_start, pred_end)) = block_layout_span(func, predecessor) else {
            return Err(SplitCfgSafetyError::CriticalEdgeCopyPlacement {
                predecessor,
                successor: join_block,
                point: join_pos,
            });
        };
        if pred_start >= join_pos && pred_end > pred_start {
            original_live_through.push(BlockLiveSpan {
                start: pred_start,
                end: pred_end,
            });
        }
    }

    Ok(SplitCopyPlan::JoinBlockStart {
        point: join_pos,
        original_live_through,
    })
}

fn incoming_edge_copy_placements(
    func: &MachFunction,
    join_block: BlockId,
    join_pos: u32,
    point: u32,
) -> Result<Vec<EdgeCopyPlacement>, SplitCfgSafetyError> {
    let join = &func.blocks[join_block.0 as usize];
    let mut copies = Vec::with_capacity(join.preds.len());

    for &predecessor in &join.preds {
        let pred_idx = predecessor.0 as usize;
        let Some(pred) = func.blocks.get(pred_idx) else {
            return Err(SplitCfgSafetyError::CriticalEdgeCopyPlacement {
                predecessor,
                successor: join_block,
                point,
            });
        };
        if pred.succs.len() != 1 || pred.succs[0] != join_block {
            return Err(SplitCfgSafetyError::CriticalEdgeCopyPlacement {
                predecessor,
                successor: join_block,
                point,
            });
        }

        let Some(copy_pos) = edge_copy_position(func, predecessor) else {
            return Err(SplitCfgSafetyError::MissingEdgeCopyTerminator {
                predecessor,
                successor: join_block,
                point,
            });
        };
        if copy_pos >= join_pos {
            if edge_is_backedge(func, predecessor, join_block) {
                return Err(SplitCfgSafetyError::BackedgeCopyPlacement {
                    predecessor,
                    successor: join_block,
                    copy_pos,
                    join_pos,
                });
            }
            return Err(SplitCfgSafetyError::NonLinearEdgeCopyLayout {
                predecessor,
                successor: join_block,
                copy_pos,
                join_pos,
            });
        }

        copies.push(EdgeCopyPlacement {
            predecessor,
            copy_pos,
        });
    }

    Ok(copies)
}

fn edge_is_backedge(func: &MachFunction, predecessor: BlockId, successor: BlockId) -> bool {
    predecessor == successor || cfg_reaches_block(func, successor, predecessor)
}

fn block_for_split_point(func: &MachFunction, point: u32) -> Option<(BlockId, u32, u32)> {
    let mut global_idx: u32 = 0;
    for &block_id in &func.block_order {
        let block = &func.blocks[block_id.0 as usize];
        let block_len = block
            .insts
            .iter()
            .filter(|&&inst_id| !is_inserted_split_copy(func, inst_id))
            .count() as u32;
        let block_start = global_idx;
        let block_end = global_idx + block_len;

        if point >= block_start && point < block_end {
            return Some((block_id, block_start, block_end));
        }

        global_idx = block_end;
    }

    None
}

fn block_layout_span(func: &MachFunction, target: BlockId) -> Option<(u32, u32)> {
    let mut global_idx: u32 = 0;
    for &block_id in &func.block_order {
        let block = &func.blocks[block_id.0 as usize];
        let block_len = block
            .insts
            .iter()
            .filter(|&&inst_id| !is_inserted_split_copy(func, inst_id))
            .count() as u32;
        let block_start = global_idx;
        let block_end = global_idx + block_len;

        if block_id == target {
            return Some((block_start, block_end));
        }

        global_idx = block_end;
    }

    None
}

fn edge_copy_position(func: &MachFunction, predecessor: BlockId) -> Option<u32> {
    let (block_start, _) = block_layout_span(func, predecessor)?;
    let block = func.blocks.get(predecessor.0 as usize)?;
    let mut counted = 0u32;

    for &inst_id in &block.insts {
        if is_inserted_split_copy(func, inst_id) {
            continue;
        }
        let pos = block_start + counted;
        let inst = func.insts.get(inst_id.0 as usize)?;
        if inst.flags.contains(InstFlags::IS_TERMINATOR) {
            return Some(pos);
        }
        counted += 1;
    }

    None
}

fn block_participates_in_cycle(func: &MachFunction, block_id: BlockId) -> bool {
    let Some(block) = func.blocks.get(block_id.0 as usize) else {
        return false;
    };

    block
        .succs
        .iter()
        .any(|&succ| succ == block_id || cfg_reaches_block(func, succ, block_id))
}

fn cfg_reaches_block(func: &MachFunction, start: BlockId, target: BlockId) -> bool {
    let mut stack = vec![start];
    let mut seen = vec![false; func.blocks.len()];

    while let Some(block_id) = stack.pop() {
        if block_id == target {
            return true;
        }
        let block_idx = block_id.0 as usize;
        if block_idx >= func.blocks.len() || seen[block_idx] {
            continue;
        }
        seen[block_idx] = true;
        stack.extend(func.blocks[block_idx].succs.iter().copied());
    }

    false
}

fn cfg_dominates_block(func: &MachFunction, dominator: BlockId, block: BlockId) -> bool {
    if dominator == block {
        return true;
    }

    let mut stack = vec![func.entry_block];
    let mut seen = vec![false; func.blocks.len()];

    while let Some(block_id) = stack.pop() {
        if block_id == dominator {
            continue;
        }
        if block_id == block {
            return false;
        }
        let block_idx = block_id.0 as usize;
        if block_idx >= func.blocks.len() || seen[block_idx] {
            continue;
        }
        seen[block_idx] = true;
        stack.extend(func.blocks[block_idx].succs.iter().copied());
    }

    true
}

/// Insert a copy instruction at the given program point.
///
/// Finds the block containing instructions around `point` and inserts
/// the copy before the instruction at that index.
fn insert_copy_at_point(func: &mut MachFunction, copy_id: InstId, point: u32) {
    // Walk blocks to find where to insert based on instruction numbering.
    let mut global_idx: u32 = 0;
    for &block_id in &func.block_order.clone() {
        let block_idx = block_id.0 as usize;
        let block_insts = func.blocks[block_idx].insts.clone();
        let block_start = global_idx;
        let block_len = block_insts
            .iter()
            .filter(|&&inst_id| !is_inserted_split_copy(func, inst_id))
            .count() as u32;
        let block_end = global_idx + block_len;

        if point >= block_start && point < block_end {
            let mut counted = 0u32;
            let mut local_pos = block_insts.len();
            for (idx, &inst_id) in block_insts.iter().enumerate() {
                if is_inserted_split_copy(func, inst_id) {
                    continue;
                }
                if block_start + counted == point {
                    local_pos = idx;
                    break;
                }
                counted += 1;
            }
            func.blocks[block_idx].insts.insert(local_pos, copy_id);
            return;
        }

        global_idx = block_end;
    }

    // Fallback: append to the last block.
    if let Some(last_block) = func.blocks.last_mut() {
        last_block.insts.push(copy_id);
    }
}

fn insert_copy_on_incoming_edge(func: &mut MachFunction, copy_id: InstId, predecessor: BlockId) {
    let Some(insert_pos) = func.blocks.get(predecessor.0 as usize).map(|pred_block| {
        pred_block
            .insts
            .iter()
            .position(|&inst_id| {
                func.insts
                    .get(inst_id.0 as usize)
                    .is_some_and(|inst| inst.flags.contains(InstFlags::IS_TERMINATOR))
            })
            .unwrap_or(pred_block.insts.len())
    }) else {
        return;
    };
    let Some(pred_block) = func.blocks.get_mut(predecessor.0 as usize) else {
        return;
    };
    pred_block.insts.insert(insert_pos, copy_id);
}

/// Find the best split point near an interference region.
///
/// Given an interval and the point where interference starts, find
/// the best split point that separates the interval into a part that
/// can be allocated and a part that can be re-enqueued.
///
/// Strategy: split just after the last use/def before the interference
/// point, so the first half is as long as possible while still
/// fitting in a register.
pub fn find_split_near_interference(
    interval: &LiveInterval,
    interference_start: u32,
) -> Option<u32> {
    let mut positions: Vec<u32> = interval
        .use_positions
        .iter()
        .chain(interval.def_positions.iter())
        .copied()
        .filter(|&p| p < interference_start)
        .collect();
    positions.sort_unstable();

    if positions.is_empty() {
        return None;
    }

    let last_before = *positions.last().unwrap();
    let split_point = last_before + 1;

    if split_point <= interval.start() || split_point >= interval.end() {
        return None;
    }

    Some(split_point)
}

/// Find split points between consecutive use/def positions.
///
/// This is the most aggressive splitting strategy. Each resulting
/// interval covers only a small region around its uses, making it
/// easy to allocate. The cost is more spill/reload traffic.
///
/// Returns a list of `(split_point, weight)` pairs for each viable
/// split, sorted by descending weight (most beneficial first).
/// Weight equals the gap size between the consecutive positions,
/// so larger gaps are preferred.
pub fn find_per_use_split_points(interval: &LiveInterval) -> Vec<(u32, f64)> {
    let mut positions: Vec<u32> = interval
        .use_positions
        .iter()
        .chain(interval.def_positions.iter())
        .copied()
        .collect();
    positions.sort_unstable();
    positions.dedup();

    if positions.len() < 2 {
        return Vec::new();
    }

    let mut splits = Vec::new();

    for window in positions.windows(2) {
        let gap = window[1].saturating_sub(window[0]);
        if gap >= 2 {
            let split_point = window[0] + 1;
            if split_point > interval.start() && split_point < interval.end() {
                splits.push((split_point, gap as f64));
            }
        }
    }

    splits.sort_by(|a, b| b.1.total_cmp(&a.1));
    splits
}

/// Call-aware split-point selector (LIVE-RANGE SPLITTING Stage 1).
///
/// A spilled interval that is live across a call cannot be colored to a
/// caller-saved register on the aarch64 AOT path: the call's `implicit_defs`
/// reserve every caller-saved preg at the call position, and
/// [`reserved_interferes`](crate::linear_scan) forbids any preg the interval
/// `is_live_at` that reservation. So a value that is hot *away* from the call —
/// e.g. a permutation/count base used all through a call-free inner loop — is
/// forced onto the scarce callee-saved pool or spilled outright, even though it
/// never actually occupies a register at the call.
///
/// This selector returns the split points that carve such a value into
/// call-free pieces around a short connector that carries it across each call.
/// For every call position `c` the interval is live across:
///
/// * **left boundary** `c - 1`: an in-block split at `c-1` gives the before
///   piece the range `[.., c)` — `split_interval_checked` sets
///   `original.end == split_point + 1`, so the truncated original is provably
///   NOT `is_live_at(c)` and may take a caller-saved register. Emitted only when
///   there is a use/def before the call worth protecting.
/// * **right boundary** `c + 1`: an in-block split at `c+1` gives the after
///   piece the range `[c+1, ..)` (`new.start == split_point`), again provably
///   not `is_live_at(c)`. Emitted only when there is a use/def after the call.
///
/// Applied in ascending order (the driver chains each split onto the previous
/// split's `new_interval`), these leave the piece that spans `c` — the
/// connector — as the only survivor `is_live_at(c)`; it is short and spills
/// cheaply. Points are clamped to the interval interior and to positions
/// strictly inside a live range (holes are skipped); `split_interval_checked`
/// still has final say and rejects (dropped by the driver) any point whose copy
/// placement is CFG-unsafe — notably any insertion block that participates in a
/// cycle, which is exactly what keeps this selector from ever splitting inside
/// (or separating a loop-carried copy of) a hot loop body.
///
/// Returns an empty vector when the interval crosses no call, or when every one
/// of its use/def positions coincides with a call (nothing to keep in a
/// register between calls) — the "has a use/def strictly between calls / between
/// a block boundary and a call" guard from the design.
pub fn call_aware_split_points(interval: &LiveInterval, call_positions: &[u32]) -> Vec<u32> {
    // Calls this interval is actually live across (holes handled by is_live_at).
    let crossed: Vec<u32> = call_positions
        .iter()
        .copied()
        .filter(|&c| interval.is_live_at(c))
        .collect();
    if crossed.is_empty() {
        return Vec::new();
    }

    let start = interval.start();
    let end = interval.end();
    let inside = |p: u32| -> bool {
        p > start && p < end && interval.ranges.iter().any(|r| r.start < p && p < r.end)
    };

    let mut usedef: Vec<u32> = interval
        .use_positions
        .iter()
        .chain(interval.def_positions.iter())
        .copied()
        .collect();
    usedef.sort_unstable();
    usedef.dedup();

    // Only worth splitting when there is register-resident work OFF the call
    // positions — a use/def that is not itself at a crossed call.
    if !usedef.iter().any(|&p| !crossed.contains(&p)) {
        return Vec::new();
    }

    let mut points: Vec<u32> = Vec::new();
    for &c in &crossed {
        // Left boundary: protect a value used before the call.
        if usedef.iter().any(|&p| p < c) {
            let l = c.saturating_sub(1);
            if inside(l) {
                points.push(l);
            }
        }
        // Right boundary: protect a value used after the call.
        if usedef.iter().any(|&p| p > c) && inside(c + 1) {
            points.push(c + 1);
        }
    }
    points.sort_unstable();
    points.dedup();
    points
}

// ===========================================================================
// STAGE 2 — LOOP-INVARIANT RELOAD PLACEMENT
// ===========================================================================
//
// A pre-alloc, loop-local reload for a pass-1 spill victim `V` that is PROVABLY
// LOOP-INVARIANT (never redefined in ANY natural-loop body — a def that
// dominates the loops) and used inside a loop `L`:
//
//   * allocate a fresh vreg `V_in`;
//   * insert a PSEUDO_COPY `V_in <- V` on `L`'s FORWARD entry edge(s) only
//     (before the preheader terminator — NEVER the latch/back edge);
//   * rewrite ONLY the victim's uses inside `L`'s innermost-loop body partition
//     to `V_in`, leaving the parent `V` fully intact (still spilled, still used
//     outside `L`).
//
// The existing STAGE-1 driver then re-runs LinearScan with transient loop-depth
// weights: `V_in` is a short depth->=1 interval whose spill weight towers over the
// cold remat constants squatting on callee-saved registers, so it wins a
// register; if none is free it spills, the KEEP-BETTER metric does not improve,
// and the driver self-rejects back to the pass-1 (HEAD) allocation.
//
// This mode DODGES the truncating split's CFG-cycle refusals
// (`block_participates_in_cycle`, `BackedgeCopyPlacement`): those exist because a
// linear interval cannot model a loop-carried value, but a loop-INVARIANT value
// has no next-iteration value to model. The INVARIANCE precondition replaces the
// cycle refusal — asserted, fail-closed, at both selection and injection.
//
// It also dodges validator gate (d) (`check_spill_discipline`): `V_in` is
// register-homed (never in the disciplined slot-homed set), and the single
// reload copy that reads the slot-homed parent `V` gets its adjacent
// PSEUDO_SPILL_LOAD from `insert_spill_code` like any other copy of a spilled
// value.

/// A STAGE-2 loop-invariant reload placement produced by
/// [`loop_invariant_reload_points`] and materialized by [`inject_loop_reload`].
#[derive(Debug, Clone)]
pub(crate) struct LoopReloadPoint {
    /// The loop-invariant spill victim to reload.
    pub victim: VReg,
    /// The header block index of the loop whose preheader receives the reload.
    /// The driver ranks placements by this loop's nesting depth so the HOTTEST
    /// reloads are materialized first under the per-function budget.
    pub header: usize,
    /// Forward-entry predecessor block(s) of the loop header to place the reload
    /// copy in
    /// (before the terminator). Phase A emits exactly one — a preheader that
    /// PROVABLY DOMINATES the header, so the single reload def reaches every
    /// rewritten use.
    pub forward_preds: Vec<BlockId>,
    /// Body blocks whose INNERMOST loop is `header`: the only blocks whose
    /// `victim` uses are rewritten to the reload vreg. Uses in a nested inner
    /// loop are rewritten by that inner loop's own reload, so each use is
    /// rewritten exactly once, at its deepest (hottest) loop.
    pub rewrite_blocks: Vec<usize>,
}

/// True when block `b` contains an instruction that USES `vreg` as a VReg
/// operand.
fn block_uses_vreg(func: &MachFunction, b: usize, vreg: VReg) -> bool {
    let Some(block) = func.blocks.get(b) else {
        return false;
    };
    block.insts.iter().any(|&inst_id| {
        func.insts
            .get(inst_id.0 as usize)
            .is_some_and(|inst| inst.vreg_uses().any(|u| u == vreg))
    })
}

/// True when block `b` contains an instruction that DEFINES `vreg`.
fn block_defs_vreg(func: &MachFunction, b: usize, vreg: VReg) -> bool {
    let Some(block) = func.blocks.get(b) else {
        return false;
    };
    block.insts.iter().any(|&inst_id| {
        func.insts
            .get(inst_id.0 as usize)
            .is_some_and(|inst| inst.vreg_defs().any(|d| d == vreg))
    })
}

/// STAGE-2 selector: the loop-invariant reload placements for one spill victim.
///
/// Structural (block-membership + vreg identity), so it is INDEPENDENT of the
/// interval numbering and stays valid after STAGE-1 call-aware splits have
/// already mutated `func` (in the combined default mode). For victim `V`:
///
/// 1. INVARIANCE (fail-closed): if ANY natural-loop body block defines `V`,
///    return no points — `V` is not loop-invariant, so a preheader reload (which
///    may itself sit inside an outer loop) could capture a stale value.
/// 2. For each innermost loop `L` that has `>= min_uses` STATIC uses of `V` in
///    its own-level body, require a SAFE forward placement: exactly one
///    forward-entry predecessor that PROVABLY DOMINATES the header (a preheader).
///    Multi-entry loops and non-dominating single preds are declined (Phase A).
///
/// `min_uses` is the amortization filter: a loop-invariant value used only ONCE
/// per iteration barely benefits from a register (one reload replaced by one
/// register read, minus the address recompute, plus a preheader copy executed on
/// every loop entry), and on a memory-bound loop this is a measured slight
/// regression (sieve). Values used MANY times per iteration (fannkuch's
/// permutation base: ~4 array touches) amortize the preheader copy and win.
/// `min_uses == 1` reproduces the "any in-loop use" selector.
pub(crate) fn loop_invariant_reload_points(
    func: &MachFunction,
    victim: VReg,
    loop_info: &crate::remat::LoopInfo,
    min_uses: usize,
) -> Vec<LoopReloadPoint> {
    // (1) Global loop-invariance: no definition of `victim` in ANY loop body.
    for l in loop_info.iter() {
        for &b in &l.body {
            if block_defs_vreg(func, b, victim) {
                return Vec::new();
            }
        }
    }

    // (2) Innermost loops that use `victim` in their own-level body. Attribute a
    // block's uses only to that block's innermost loop.
    let mut headers_with_use: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    for l in loop_info.iter() {
        for &b in &l.body {
            if loop_info.innermost_header_of(b) != Some(l.header) {
                continue;
            }
            if block_uses_vreg(func, b, victim) {
                headers_with_use.insert(l.header);
            }
        }
    }

    // (3) Emit a placement for each such loop that has a dominating preheader AND
    //     enough in-loop uses of `victim` to amortize the reload.
    let mut points = Vec::new();
    for h in headers_with_use {
        let Some(l) = loop_info.get(h) else {
            continue;
        };
        // Phase A: require a single forward-entry predecessor that dominates the
        // header. A dominating preheader guarantees the one reload def reaches
        // every rewritten use; `cfg_dominates_block` is a direct, sound check
        // (handles even irreducible CFGs) so we never rely on the structural
        // "single forward pred dominates" argument alone. Multi-entry loops are
        // declined rather than synthesizing a shared preheader.
        if l.forward_preds.len() != 1 {
            continue;
        }
        let pre = BlockId(l.forward_preds[0] as u32);
        let header_block = BlockId(h as u32);
        if !cfg_dominates_block(func, pre, header_block) {
            continue;
        }
        let rewrite_blocks: Vec<usize> = l
            .body
            .iter()
            .copied()
            .filter(|&b| loop_info.innermost_header_of(b) == Some(h))
            .collect();
        // Amortization filter: count the victim's STATIC use-operand occurrences
        // in the innermost-loop partition.
        let uses: usize = rewrite_blocks
            .iter()
            .map(|&b| count_vreg_uses_in_block(func, b, victim))
            .sum();
        if uses < min_uses.max(1) {
            continue;
        }
        points.push(LoopReloadPoint {
            victim,
            header: h,
            forward_preds: vec![pre],
            rewrite_blocks,
        });
    }
    points
}

/// Count the STATIC use-operand occurrences of `vreg` across block `b`.
fn count_vreg_uses_in_block(func: &MachFunction, b: usize, vreg: VReg) -> usize {
    let Some(block) = func.blocks.get(b) else {
        return 0;
    };
    block
        .insts
        .iter()
        .map(|&inst_id| {
            func.insts
                .get(inst_id.0 as usize)
                .map(|inst| inst.vreg_uses().filter(|&u| u == vreg).count())
                .unwrap_or(0)
        })
        .sum()
}

/// STAGE-2 injector: materialize one [`LoopReloadPoint`] into `func`.
///
/// Allocates `V_in`, places `V_in <- V` on each forward-entry edge (before the
/// preheader terminator), and rewrites the victim's uses in `rewrite_blocks` to
/// `V_in`. Returns `Some(V_in)` when a rewrite was made (a reload copy was
/// placed); `None` (a no-op — nothing inserted) when there is nothing to rewrite
/// or the INVARIANCE precondition fails for a rewrite block (fail-closed).
///
/// The returned `V_in` lets the driver's KEEP-BETTER metric distinguish the
/// deliberately-added reload temporary from an original spill victim: a `V_in`
/// that ends up spilled is a self-limiting no-op (it cannot make weighted
/// traffic improve), so it must not count against the spill-count guard.
///
/// The rewrite touches only USE operands (invariance guarantees `rewrite_blocks`
/// hold no def of the victim), and never the reload copy itself, which lives in
/// the forward predecessor — a block outside the loop body, so outside
/// `rewrite_blocks`.
pub(crate) fn inject_loop_reload(func: &mut MachFunction, point: &LoopReloadPoint) -> Option<VReg> {
    // Defensive: confirm there is at least one rewritable use (the selector
    // already guarantees this) so we never place a dead reload copy.
    if !point
        .rewrite_blocks
        .iter()
        .any(|&b| block_uses_vreg(func, b, point.victim))
    {
        return None;
    }
    // Fail-closed invariance assert: the reload copy defines `V_in` ONCE in the
    // preheader and is never re-established on the back edge, so a victim def
    // inside a rewrite block would make the rewritten uses read a value the
    // reload never carries. Refuse rather than miscompile.
    for &b in &point.rewrite_blocks {
        if block_defs_vreg(func, b, point.victim) {
            return None;
        }
    }

    let v_in = func.alloc_vreg(point.victim.class);
    // Place the reload copy on each forward entry edge (Phase A: exactly one).
    for &pred in &point.forward_preds {
        let copy_id = push_split_copy(func, point.victim, v_in);
        insert_copy_on_incoming_edge(func, copy_id, pred);
    }
    // Rewrite the victim's uses -> `V_in` in the innermost-loop partition blocks.
    let mut rewrote = false;
    for &b in &point.rewrite_blocks {
        let inst_ids = func
            .blocks
            .get(b)
            .map(|blk| blk.insts.clone())
            .unwrap_or_default();
        for inst_id in inst_ids {
            if let Some(inst) = func.insts.get_mut(inst_id.0 as usize) {
                for op in inst.uses.iter_mut() {
                    if let MachOperand::VReg(v) = op
                        && *v == point.victim
                    {
                        *v = v_in;
                        rewrote = true;
                    }
                }
            }
        }
    }
    if rewrote { Some(v_in) } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::liveness::LiveInterval;
    use crate::machine_types::{
        BlockId, InstFlags, InstId, MachBlock, MachFunction, MachInst, MachOperand, RegClass, VReg,
    };
    use std::collections::BTreeMap;

    fn vreg(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr64,
        }
    }

    fn make_interval(id: u32, ranges: &[(u32, u32)], uses: &[u32], defs: &[u32]) -> LiveInterval {
        let mut interval = LiveInterval::new(vreg(id));
        for &(start, end) in ranges {
            interval.add_range(start, end);
        }
        interval.use_positions = uses.to_vec();
        interval.def_positions = defs.to_vec();
        interval.spill_weight = 1.0;
        interval
    }

    fn make_test_func(num_insts: usize) -> MachFunction {
        let mut insts = Vec::new();
        let mut inst_ids = Vec::new();

        for i in 0..num_insts {
            let inst = MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(i as u32))],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            };
            inst_ids.push(InstId(i as u32));
            insts.push(inst);
        }

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
            next_vreg: num_insts as u32,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        }
    }

    fn make_inst(opcode: u16, defs: &[VReg], uses: &[VReg]) -> MachInst {
        MachInst {
            opcode,
            defs: defs.iter().copied().map(MachOperand::VReg).collect(),
            uses: uses.iter().copied().map(MachOperand::VReg).collect(),
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }
    }

    fn make_branch(targets: &[BlockId]) -> MachInst {
        MachInst {
            opcode: 0xBA,
            defs: Vec::new(),
            uses: targets.iter().copied().map(MachOperand::Block).collect(),
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        }
    }

    fn make_single_block_func(insts: Vec<MachInst>, next_vreg: u32) -> MachFunction {
        let inst_ids: Vec<InstId> = (0..insts.len()).map(|idx| InstId(idx as u32)).collect();
        MachFunction {
            name: "split_rewrite".into(),
            insts,
            blocks: vec![MachBlock {
                insts: inst_ids,
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        }
    }

    fn operand_refs_vreg(operand: &MachOperand, expected: VReg) -> bool {
        matches!(operand, MachOperand::VReg(vreg) if *vreg == expected)
    }

    fn inst_refs_vreg(inst: &MachInst, expected: VReg) -> bool {
        inst.defs
            .iter()
            .chain(inst.uses.iter())
            .any(|operand| operand_refs_vreg(operand, expected))
    }

    fn non_copy_refs_vreg(func: &MachFunction, expected: VReg) -> bool {
        func.insts
            .iter()
            .any(|inst| inst.opcode != phi_elim::PSEUDO_COPY && inst_refs_vreg(inst, expected))
    }

    #[test]
    fn test_find_optimal_split_point_large_gap() {
        // Interval: [0, 20) with uses at 2 and 18.
        // Largest gap: 2..18 (size 16), midpoint = 10.
        let interval = make_interval(0, &[(0, 20)], &[2, 18], &[0]);
        let split = find_optimal_split_point(&interval);
        assert_eq!(split, Some(10));
    }

    #[test]
    fn test_find_optimal_split_point_no_gap() {
        // Interval with consecutive uses — no meaningful gap.
        let interval = make_interval(0, &[(0, 3)], &[0, 1, 2], &[]);
        let split = find_optimal_split_point(&interval);
        assert_eq!(split, None);
    }

    #[test]
    fn test_find_optimal_split_point_single_use() {
        let interval = make_interval(0, &[(0, 10)], &[5], &[]);
        let split = find_optimal_split_point(&interval);
        // Only one position — can't split.
        assert_eq!(split, None);
    }

    #[test]
    fn test_analyze_split_candidates_returns_sorted() {
        // Uses at 0, 5, 15, 20.
        // Gaps: (5,1,5), (10,6,15), (5,16,20).
        // Largest gap is 6..15 (size 10).
        let interval = make_interval(0, &[(0, 25)], &[0, 5, 15, 20], &[]);
        let candidates = analyze_split_candidates(&interval, &[], 10);
        assert!(!candidates.is_empty());
        // The first candidate should be the largest gap.
        match &candidates[0] {
            SplitDecision::SplitAroundRegion { start, end } => {
                assert_eq!(*start, 6);
                assert_eq!(*end, 15);
            }
            other => panic!("Expected SplitAroundRegion, got {:?}", other),
        }
    }

    #[test]
    fn test_split_interval_basic() {
        let mut func = make_test_func(20);
        let interval = make_interval(0, &[(0, 20)], &[2, 18], &[0]);

        let result = split_interval(&interval, 10, &mut func);
        assert!(result.is_some());

        let result = result.unwrap();
        assert_eq!(result.original_vreg, vreg(0));
        assert_ne!(result.new_vreg, vreg(0));

        // Original interval remains live through the split copy at 10.
        assert_eq!(result.original_interval.start(), 0);
        assert_eq!(result.original_interval.end(), 11);

        // New interval should cover [10, 20).
        assert_eq!(result.new_interval.start(), 10);
        assert_eq!(result.new_interval.end(), 20);
    }

    #[test]
    fn test_split_interval_out_of_range() {
        let mut func = make_test_func(10);
        let interval = make_interval(0, &[(0, 10)], &[2, 8], &[0]);

        // Split at 0 (start boundary) should fail.
        assert!(split_interval(&interval, 0, &mut func).is_none());
        // Split at 10 (end boundary) should fail.
        assert!(split_interval(&interval, 10, &mut func).is_none());
        // Split beyond range should fail.
        assert!(split_interval(&interval, 15, &mut func).is_none());
    }

    #[test]
    fn test_split_interval_rejects_non_progress_boundary_tail() {
        let mut func = make_test_func(10);
        let interval = make_interval(0, &[(0, 2)], &[1], &[0]);

        assert!(
            split_interval(&interval, 1, &mut func).is_none(),
            "split must shrink both halves after copy-source boundary liveness"
        );
    }

    #[test]
    fn test_split_interval_with_holes() {
        let mut func = make_test_func(20);
        // Interval has a hole: [0,5) and [10,20).
        let interval = make_interval(0, &[(0, 5), (10, 20)], &[2, 15], &[0, 10]);

        let result = split_interval(&interval, 7, &mut func);
        assert!(
            result.is_none(),
            "split copy in a live-range hole would copy a value that is not live"
        );
    }

    // -----------------------------------------------------------------------
    // Additional edge-case and correctness tests (issue #139)
    // -----------------------------------------------------------------------

    #[test]
    fn test_find_optimal_split_point_two_uses() {
        // Uses at 2 and 10. Gap = 8, midpoint = 6.
        let interval = make_interval(0, &[(0, 15)], &[2, 10], &[]);
        let split = find_optimal_split_point(&interval);
        assert_eq!(split, Some(6));
    }

    #[test]
    fn test_find_optimal_split_point_equal_gaps() {
        // Uses at 0, 5, 10 — two gaps of size 5 each.
        let interval = make_interval(0, &[(0, 15)], &[0, 5, 10], &[]);
        let split = find_optimal_split_point(&interval);
        // Both gaps are 5, so should pick the first one found: mid of [0,5] = 2.
        assert!(split.is_some());
        let sp = split.unwrap();
        // Either gap midpoint is valid.
        assert!(
            sp == 2 || sp == 7,
            "split should be at midpoint of one gap: got {sp}"
        );
    }

    #[test]
    fn test_find_optimal_split_point_gap_size_1() {
        // Uses at 3 and 5. Gap = 2. Midpoint = 4. Gap >= 2 so should split.
        let interval = make_interval(0, &[(0, 10)], &[3, 5], &[]);
        let split = find_optimal_split_point(&interval);
        assert_eq!(split, Some(4));
    }

    #[test]
    fn test_find_optimal_split_point_empty_interval() {
        let interval = make_interval(0, &[], &[], &[]);
        let split = find_optimal_split_point(&interval);
        assert_eq!(split, None);
    }

    #[test]
    fn test_analyze_split_candidates_empty_positions() {
        let interval = make_interval(0, &[(0, 10)], &[], &[]);
        let candidates = analyze_split_candidates(&interval, &[], 10);
        assert!(candidates.is_empty() || candidates[0] == SplitDecision::NoSplit);
    }

    #[test]
    fn test_analyze_split_candidates_small_gap() {
        // Uses at 0 and 2. Gap = 2 but gap_start=1, gap_end=2 -> gap_size=1.
        // gap_size < 2 so should produce SplitBeforeUse.
        let interval = make_interval(0, &[(0, 5)], &[0, 2], &[]);
        let candidates = analyze_split_candidates(&interval, &[], 10);
        assert!(!candidates.is_empty());
        match &candidates[0] {
            SplitDecision::SplitBeforeUse(pos) => {
                assert_eq!(*pos, 2);
            }
            SplitDecision::SplitAroundRegion { .. } => {
                // Also acceptable if gap >= 2.
            }
            other => panic!("Unexpected decision: {:?}", other),
        }
    }

    #[test]
    fn test_analyze_split_candidates_multiple_decisions() {
        // Uses at 0, 10, 30, 35.
        // Gaps: (10, 1, 10) size=9, (20, 11, 30) size=19, (5, 31, 35) size=4.
        // Sorted: size 19 first, then 9, then 4.
        let interval = make_interval(0, &[(0, 40)], &[0, 10, 30, 35], &[]);
        let candidates = analyze_split_candidates(&interval, &[], 10);
        assert!(candidates.len() >= 3, "should have 3 candidates");
        // First should be the largest gap (11..30, size 19).
        match &candidates[0] {
            SplitDecision::SplitAroundRegion { start, end } => {
                assert_eq!(*start, 11);
                assert_eq!(*end, 30);
            }
            other => panic!("Expected largest gap first, got {:?}", other),
        }
    }

    #[test]
    fn test_split_interval_creates_copy_instruction() {
        let mut func = make_test_func(20);
        let interval = make_interval(0, &[(0, 20)], &[2, 18], &[0]);
        let insts_before = func.insts.len();

        let result = split_interval(&interval, 10, &mut func);
        assert!(result.is_some());

        // A PSEUDO_COPY instruction should have been inserted.
        assert!(
            func.insts.len() > insts_before,
            "should have added a copy instruction"
        );
        let copy_inst = &func.insts[insts_before];
        assert_eq!(copy_inst.opcode, crate::phi_elim::PSEUDO_COPY);
    }

    #[test]
    fn test_split_interval_rewrites_non_copy_use_to_new_vreg() {
        let original = vreg(0);
        let mut func = make_single_block_func(
            vec![
                make_inst(1, &[original], &[]),
                make_inst(2, &[vreg(1)], &[]),
                make_inst(3, &[], &[original]),
            ],
            2,
        );
        let interval = make_interval(0, &[(0, 3)], &[2], &[0]);

        let result = split_interval(&interval, 1, &mut func).unwrap();

        assert!(
            non_copy_refs_vreg(&func, result.new_vreg),
            "split-created vreg must be referenced by a non-copy instruction"
        );
        assert_eq!(func.insts[2].uses, vec![MachOperand::VReg(result.new_vreg)]);
        assert_eq!(
            func.insts[0].defs,
            vec![MachOperand::VReg(result.original_vreg)]
        );
    }

    #[test]
    fn test_split_interval_rewrites_split_use_across_blocks() {
        let original = vreg(0);
        let insts = vec![
            make_inst(1, &[original], &[]),
            MachInst {
                opcode: 0xBA,
                defs: vec![],
                uses: vec![MachOperand::Block(BlockId(1))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            make_inst(3, &[], &[original]),
            make_inst(4, &[], &[]),
        ];
        let mut func = MachFunction {
            name: "split_rewrite_multiblock".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2), InstId(3)],
                    preds: vec![BlockId(0)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let interval = make_interval(0, &[(0, 4)], &[2], &[0]);

        let result = split_interval(&interval, 2, &mut func).unwrap();

        assert!(
            non_copy_refs_vreg(&func, result.new_vreg),
            "successor block instruction must reference the split-created vreg"
        );
        assert_eq!(func.insts[2].uses, vec![MachOperand::VReg(result.new_vreg)]);
        let copy_id = func.blocks[1].insts[0];
        assert_eq!(func.insts[copy_id.0 as usize].opcode, phi_elim::PSEUDO_COPY);
        assert_eq!(func.blocks[1].insts[1], InstId(2));
        assert_eq!(func.blocks[1].insts[2], InstId(3));
    }

    #[test]
    fn test_split_interval_uses_block_order_for_rewrite_and_copy_insert() {
        let original = vreg(0);
        let insts = vec![
            make_inst(2, &[], &[original]),
            make_inst(3, &[], &[original]),
            make_inst(1, &[original], &[]),
        ];
        let mut func = MachFunction {
            name: "split_rewrite_block_order".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: vec![BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2)],
                    preds: Vec::new(),
                    succs: vec![BlockId(0)],
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(1), BlockId(0)],
            entry_block: BlockId(1),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let interval = make_interval(0, &[(0, 3)], &[1, 2], &[0]);

        let result = split_interval(&interval, 1, &mut func).unwrap();

        assert_eq!(
            func.insts[2].defs,
            vec![MachOperand::VReg(result.original_vreg)],
            "the block-order position-0 def must stay on the original vreg"
        );
        assert_eq!(
            func.insts[0].uses,
            vec![MachOperand::VReg(result.new_vreg)],
            "the block-order position-1 use must be rewritten to the split vreg"
        );
        assert_eq!(func.insts[1].uses, vec![MachOperand::VReg(result.new_vreg)]);
        let copy_id = func.blocks[0].insts[0];
        assert_eq!(func.insts[copy_id.0 as usize].opcode, phi_elim::PSEUDO_COPY);
        assert_eq!(func.blocks[0].insts[1], InstId(0));
        assert_eq!(func.blocks[0].insts[2], InstId(1));
    }

    #[test]
    fn test_split_interval_places_safe_multi_pred_block_start_edge_copies() {
        let original = vreg(0);
        let insts = vec![
            make_inst(1, &[original], &[]),
            make_branch(&[BlockId(1), BlockId(2)]),
            make_branch(&[BlockId(3)]),
            make_branch(&[BlockId(3)]),
            make_inst(5, &[], &[original]),
        ];
        let mut func = MachFunction {
            name: "split_places_multipred_block_start_edge_copies".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(3)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(4)],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let insts_before = func.insts.len();
        let interval = make_interval(0, &[(0, 5)], &[4], &[0]);

        let result = split_interval(&interval, 4, &mut func)
            .expect("single-successor predecessors can host incoming edge split copies");
        assert_eq!(
            func.insts.len(),
            insts_before + 2,
            "one split copy should be inserted on each incoming edge"
        );
        let arm1_copy = func.blocks[1].insts[0];
        let arm2_copy = func.blocks[2].insts[0];
        assert_eq!(
            func.insts[arm1_copy.0 as usize].opcode,
            phi_elim::PSEUDO_COPY
        );
        assert_eq!(
            func.insts[arm2_copy.0 as usize].opcode,
            phi_elim::PSEUDO_COPY
        );
        assert_eq!(
            func.insts[arm1_copy.0 as usize].defs,
            vec![MachOperand::VReg(result.new_vreg)]
        );
        assert_eq!(
            func.insts[arm2_copy.0 as usize].uses,
            vec![MachOperand::VReg(original)]
        );
        assert_eq!(func.blocks[1].insts[1], InstId(2));
        assert_eq!(func.blocks[2].insts[1], InstId(3));
        assert_eq!(func.blocks[3].insts, vec![InstId(4)]);
        assert_eq!(func.insts[4].uses, vec![MachOperand::VReg(result.new_vreg)]);
        assert!(result.original_interval.use_positions.contains(&2));
        assert!(result.original_interval.use_positions.contains(&3));
        assert!(result.new_interval.def_positions.contains(&2));
        assert!(result.new_interval.def_positions.contains(&3));
        assert_eq!(result.new_interval.start(), 2);
    }

    #[test]
    fn test_split_interval_places_critical_edge_join_block_start_copy() {
        let original = vreg(0);
        let insts = vec![
            make_inst(1, &[original], &[]),
            make_branch(&[BlockId(1), BlockId(2)]),
            make_branch(&[BlockId(2)]),
            make_inst(4, &[], &[original]),
            make_inst(5, &[], &[original]),
        ];
        let mut func = MachFunction {
            name: "split_places_critical_edge_join_block_start_copy".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(3), InstId(4)],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let insts_before = func.insts.len();
        let interval = make_interval(0, &[(0, 5)], &[3, 4], &[0]);

        let result = split_interval_checked(&interval, 3, &mut func)
            .expect("critical-edge joins can use a join-block-start split copy");
        assert_eq!(
            func.insts.len(),
            insts_before + 1,
            "critical-edge join repair should insert one join-block copy"
        );
        let copy_id = func.blocks[2].insts[0];
        assert_eq!(func.insts[copy_id.0 as usize].opcode, phi_elim::PSEUDO_COPY);
        assert_eq!(
            func.insts[copy_id.0 as usize].defs,
            vec![MachOperand::VReg(result.new_vreg)]
        );
        assert_eq!(func.blocks[2].insts[1..], [InstId(3), InstId(4)]);
        assert_eq!(func.insts[3].uses, vec![MachOperand::VReg(result.new_vreg)]);
        assert_eq!(func.insts[4].uses, vec![MachOperand::VReg(result.new_vreg)]);
        assert_eq!(result.original_interval.ranges[0].end, 4);
        assert!(result.original_interval.use_positions.contains(&3));
        assert!(result.new_interval.def_positions.contains(&3));
    }

    #[test]
    fn test_split_interval_places_non_linear_join_block_start_copy() {
        let original = vreg(0);
        let insts = vec![
            make_inst(1, &[original], &[]),
            make_branch(&[BlockId(1), BlockId(2)]),
            make_branch(&[BlockId(3)]),
            make_branch(&[BlockId(3)]),
            make_inst(5, &[], &[original]),
            make_inst(6, &[], &[original]),
            make_inst(7, &[], &[original]),
        ];
        let mut func = MachFunction {
            name: "split_places_non_linear_join_block_start_copy".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(3)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(4), InstId(5), InstId(6)],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(3), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let insts_before = func.insts.len();
        let interval = make_interval(0, &[(0, 7)], &[3, 4, 5], &[0]);

        let result = split_interval_checked(&interval, 3, &mut func)
            .expect("non-linear acyclic joins can use a join-block-start split copy");
        assert_eq!(
            func.insts.len(),
            insts_before + 1,
            "non-linear join repair should insert one join-block copy"
        );
        let copy_id = func.blocks[3].insts[0];
        assert_eq!(func.insts[copy_id.0 as usize].opcode, phi_elim::PSEUDO_COPY);
        assert_eq!(func.blocks[3].insts[1..], [InstId(4), InstId(5), InstId(6)]);
        assert_eq!(func.insts[4].uses, vec![MachOperand::VReg(result.new_vreg)]);
        assert_eq!(func.insts[5].uses, vec![MachOperand::VReg(result.new_vreg)]);
        assert_eq!(func.insts[6].uses, vec![MachOperand::VReg(result.new_vreg)]);
        assert_eq!(
            result
                .original_interval
                .ranges
                .iter()
                .map(|range| (range.start, range.end))
                .collect::<Vec<_>>(),
            vec![(0, 4), (6, 7)],
            "the original must stay live through the later-layout predecessor"
        );
    }

    #[test]
    fn test_split_interval_places_join_block_start_copy_without_terminator_anchor() {
        let original = vreg(0);
        let insts = vec![
            make_inst(1, &[original], &[]),
            make_branch(&[BlockId(1), BlockId(2)]),
            make_branch(&[BlockId(3)]),
            make_inst(4, &[], &[]),
            make_inst(5, &[], &[original]),
            make_inst(6, &[], &[original]),
        ];
        let mut func = MachFunction {
            name: "split_places_join_block_start_copy_without_terminator_anchor".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(3)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(4), InstId(5)],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let insts_before = func.insts.len();
        let interval = make_interval(0, &[(0, 6)], &[4, 5], &[0]);

        let result = split_interval_checked(&interval, 4, &mut func)
            .expect("join-block-start copies do not need predecessor terminator anchors");
        assert_eq!(
            func.insts.len(),
            insts_before + 1,
            "missing-anchor join repair should insert one join-block copy"
        );
        let copy_id = func.blocks[3].insts[0];
        assert_eq!(func.insts[copy_id.0 as usize].opcode, phi_elim::PSEUDO_COPY);
        assert_eq!(
            func.insts[copy_id.0 as usize].defs,
            vec![MachOperand::VReg(result.new_vreg)]
        );
        assert_eq!(func.blocks[3].insts[1], InstId(4));
        assert_eq!(func.insts[4].uses, vec![MachOperand::VReg(result.new_vreg)]);
        assert_eq!(func.insts[5].uses, vec![MachOperand::VReg(result.new_vreg)]);
    }

    #[test]
    fn test_split_interval_rejects_loop_header_backedge_copy() {
        let original = vreg(0);
        let insts = vec![
            make_inst(1, &[original], &[]),
            make_branch(&[BlockId(1)]),
            make_inst(3, &[], &[original]),
            make_branch(&[BlockId(2)]),
            make_branch(&[BlockId(1)]),
        ];
        let mut func = MachFunction {
            name: "split_rejects_loop_header_backedge_copy".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2), InstId(3)],
                    preds: vec![BlockId(0), BlockId(2)],
                    succs: vec![BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![InstId(4)],
                    preds: vec![BlockId(1)],
                    succs: vec![BlockId(1)],
                    loop_depth: 1,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let insts_before = func.insts.len();
        let interval = make_interval(0, &[(0, 5)], &[2], &[0]);

        let err = split_interval_checked(&interval, 2, &mut func)
            .expect_err("loop-header split copies need backedge repair");
        assert_eq!(
            err,
            SplitError::UnsafeCfg(SplitCfgSafetyError::BackedgeCopyPlacement {
                predecessor: BlockId(2),
                successor: BlockId(1),
                copy_pos: 4,
                join_pos: 2,
            })
        );
        assert_eq!(
            func.insts.len(),
            insts_before,
            "rejected backedge split must not insert a copy"
        );
        assert_eq!(
            func.next_vreg, 1,
            "rejected backedge split must not allocate a fresh vreg"
        );
    }

    #[test]
    fn test_split_interval_rejects_branch_copy_that_does_not_dominate_rewrites() {
        let original = vreg(0);
        let insts = vec![
            make_inst(1, &[original], &[]),
            MachInst {
                opcode: 0xBA,
                defs: vec![],
                uses: vec![
                    MachOperand::Block(BlockId(1)),
                    MachOperand::Block(BlockId(2)),
                ],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            make_inst(3, &[], &[original]),
            MachInst {
                opcode: 0xBA,
                defs: vec![],
                uses: vec![MachOperand::Block(BlockId(3))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            make_inst(5, &[], &[original]),
            MachInst {
                opcode: 0xBA,
                defs: vec![],
                uses: vec![MachOperand::Block(BlockId(3))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            make_inst(7, &[], &[original]),
        ];
        let mut func = MachFunction {
            name: "split_rejects_non_dominating_branch_copy".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2), InstId(3)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(4), InstId(5)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(6)],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let insts_before = func.insts.len();
        let interval = make_interval(0, &[(0, 7)], &[2, 4, 6], &[0]);

        let err = split_interval_checked(&interval, 2, &mut func)
            .expect_err("branch-local split copy should be rejected");
        assert_eq!(
            err,
            SplitError::UnsafeCfg(SplitCfgSafetyError::NonDominatingPlacement {
                insertion_block: BlockId(1),
                rewrite_block: BlockId(2),
                rewrite_pos: 4,
            }),
            "branch-local split rejection should identify the first non-dominated rewrite"
        );
        assert!(
            split_interval(&interval, 2, &mut func).is_none(),
            "a branch-local split copy must not feed rewritten uses on paths it does not dominate"
        );
        assert_eq!(
            func.insts.len(),
            insts_before,
            "rejected non-dominating split must not insert a copy"
        );
        assert_eq!(
            func.next_vreg, 1,
            "rejected non-dominating split must not allocate a fresh vreg"
        );
    }

    #[test]
    fn test_split_interval_rejects_loop_cycle_copy_without_backedge_repair() {
        let original = vreg(0);
        let insts = vec![
            make_inst(1, &[original], &[]),
            MachInst {
                opcode: 0xBA,
                defs: vec![],
                uses: vec![MachOperand::Block(BlockId(1))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            make_inst(3, &[], &[original]),
            make_inst(4, &[], &[original]),
            MachInst {
                opcode: 0xBA,
                defs: vec![],
                uses: vec![
                    MachOperand::Block(BlockId(1)),
                    MachOperand::Block(BlockId(2)),
                ],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            make_inst(6, &[], &[original]),
        ];
        let mut func = MachFunction {
            name: "split_rejects_loop_cycle".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2), InstId(3), InstId(4)],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![InstId(5)],
                    preds: vec![BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let insts_before = func.insts.len();
        let interval = make_interval(0, &[(0, 6)], &[2, 3, 5], &[0]);

        let err = split_interval_checked(&interval, 3, &mut func)
            .expect_err("loop-carried splits need backedge repair copies");
        assert_eq!(
            err,
            SplitError::UnsafeCfg(SplitCfgSafetyError::LoopOrBackedgeBlock {
                block: BlockId(1),
                point: 3,
            })
        );
        assert!(
            split_interval(&interval, 3, &mut func).is_none(),
            "loop-carried splits need backedge repair copies before they are CFG-safe"
        );
        assert_eq!(
            func.insts.len(),
            insts_before,
            "rejected loop split must not insert a copy"
        );
        assert_eq!(
            func.next_vreg, 1,
            "rejected loop split must not allocate a fresh vreg"
        );
    }

    #[test]
    fn test_split_interval_rewrites_def_at_split_point_to_new_vreg() {
        let original = vreg(0);
        let mut func = make_single_block_func(
            vec![
                make_inst(1, &[original], &[]),
                make_inst(2, &[original], &[original]),
                make_inst(3, &[], &[original]),
            ],
            1,
        );
        let interval = make_interval(0, &[(0, 3)], &[1, 2], &[0, 1]);

        let result = split_interval(&interval, 1, &mut func).unwrap();

        assert!(
            non_copy_refs_vreg(&func, result.new_vreg),
            "def at the split point must be rewritten to the split-created vreg"
        );
        assert_eq!(func.insts[1].defs, vec![MachOperand::VReg(result.new_vreg)]);
        assert_eq!(func.insts[1].uses, vec![MachOperand::VReg(result.new_vreg)]);
        assert!(
            !inst_refs_vreg(&func.insts[1], result.original_vreg),
            "the split-point def/use instruction should not keep referencing the original vreg"
        );
    }

    #[test]
    fn test_split_interval_repeated_split_ignores_inserted_copy_positions() {
        let original = vreg(0);
        let mut func = make_single_block_func(
            vec![
                make_inst(1, &[original], &[]),
                make_inst(2, &[], &[original]),
                make_inst(3, &[], &[original]),
                make_inst(4, &[], &[original]),
            ],
            1,
        );
        let interval = make_interval(0, &[(0, 4)], &[1, 2, 3], &[0]);

        let first = split_interval(&interval, 1, &mut func).unwrap();
        let second = split_interval(&first.new_interval, 2, &mut func).unwrap();

        assert_eq!(
            func.insts[1].uses,
            vec![MachOperand::VReg(first.new_vreg)],
            "the use before the second split point should remain on the first split vreg"
        );
        assert_eq!(
            func.insts[2].uses,
            vec![MachOperand::VReg(second.new_vreg)],
            "the original instruction at position 2 should be rewritten by the second split"
        );
        assert_eq!(func.insts[3].uses, vec![MachOperand::VReg(second.new_vreg)]);
        assert!(
            func.blocks[0]
                .insts
                .iter()
                .filter(|&&inst_id| func.insts[inst_id.0 as usize].opcode == phi_elim::PSEUDO_COPY)
                .all(|&inst_id| func.insts[inst_id.0 as usize]
                    .flags
                    .contains(InstFlags::IS_PSEUDO)),
            "split-created copies should be marked so later split point scans can ignore them"
        );
    }

    #[test]
    fn test_resplitting_original_half_rewrites_existing_split_copy_source() {
        let original = vreg(0);
        let mut func = make_single_block_func(
            vec![
                make_inst(1, &[original], &[]),
                make_inst(2, &[], &[original]),
                make_inst(3, &[], &[original]),
                make_inst(4, &[], &[original]),
                make_inst(5, &[], &[original]),
                make_inst(6, &[], &[original]),
            ],
            1,
        );
        let interval = make_interval(0, &[(0, 6)], &[1, 2, 3, 4, 5], &[0]);

        let first = split_interval(&interval, 4, &mut func).unwrap();
        let first_copy_id = func.blocks[0]
            .insts
            .iter()
            .copied()
            .find(|&id| {
                let inst = &func.insts[id.0 as usize];
                inst.opcode == phi_elim::PSEUDO_COPY
                    && inst.defs == vec![MachOperand::VReg(first.new_vreg)]
            })
            .unwrap();

        let second = split_interval(&first.original_interval, 2, &mut func).unwrap();

        assert_eq!(
            func.insts[first_copy_id.0 as usize].uses,
            vec![MachOperand::VReg(second.new_vreg)],
            "old outgoing split copy must read the child interval live at that boundary"
        );
    }

    #[test]
    fn test_split_interval_allocates_new_vreg() {
        let mut func = make_test_func(20);
        let original_next_vreg = func.next_vreg;
        let interval = make_interval(0, &[(0, 20)], &[2, 18], &[0]);

        let result = split_interval(&interval, 10, &mut func).unwrap();
        assert!(
            func.next_vreg > original_next_vreg,
            "should allocate a new vreg"
        );
        assert_eq!(result.new_vreg.id, original_next_vreg);
    }

    #[test]
    fn test_split_interval_use_positions_partitioned() {
        let mut func = make_test_func(20);
        let interval = make_interval(0, &[(0, 20)], &[2, 5, 12, 18], &[0]);

        let result = split_interval(&interval, 10, &mut func).unwrap();

        // Uses before split point go to original.
        assert!(result.original_interval.use_positions.contains(&2));
        assert!(result.original_interval.use_positions.contains(&5));
        // Uses at or after split point go to new.
        assert!(result.new_interval.use_positions.contains(&12));
        assert!(result.new_interval.use_positions.contains(&18));
    }

    #[test]
    fn test_split_interval_preserves_spill_weight_priority() {
        let mut func = make_test_func(20);
        let interval = make_interval(0, &[(0, 20)], &[2, 18], &[0]);

        let result = split_interval(&interval, 10, &mut func).unwrap();

        assert_eq!(result.original_interval.spill_weight, interval.spill_weight);
        assert_eq!(result.new_interval.spill_weight, interval.spill_weight);
    }

    #[test]
    fn test_split_interval_spanning_range() {
        // Split in the middle of a single range.
        let mut func = make_test_func(30);
        let interval = make_interval(0, &[(5, 25)], &[5, 24], &[5]);

        let result = split_interval(&interval, 15, &mut func).unwrap();
        assert_eq!(result.original_interval.start(), 5);
        assert_eq!(result.original_interval.end(), 16);
        assert_eq!(result.new_interval.start(), 15);
        assert_eq!(result.new_interval.end(), 25);
    }

    #[test]
    fn test_split_interval_many_small_ranges() {
        // Multiple small ranges: [0,3), [5,8), [10,13), [15,18).
        let mut func = make_test_func(20);
        let interval = make_interval(
            0,
            &[(0, 3), (5, 8), (10, 13), (15, 18)],
            &[1, 6, 11, 16],
            &[0, 5, 10, 15],
        );

        assert!(
            split_interval(&interval, 9, &mut func).is_none(),
            "split points in holes must not create boundary copies"
        );

        let result = split_interval(&interval, 11, &mut func).unwrap();

        assert_eq!(result.original_interval.ranges.len(), 3);
        assert_eq!(result.new_interval.ranges.len(), 2);
        assert_eq!(result.original_interval.end(), 12);
        assert_eq!(result.new_interval.start(), 11);
    }

    #[test]
    fn test_split_decision_enum_equality() {
        assert_eq!(SplitDecision::NoSplit, SplitDecision::NoSplit);
        assert_eq!(
            SplitDecision::SplitBeforeUse(5),
            SplitDecision::SplitBeforeUse(5)
        );
        assert_ne!(
            SplitDecision::SplitBeforeUse(5),
            SplitDecision::SplitBeforeUse(10)
        );
        assert_eq!(
            SplitDecision::SplitAroundRegion { start: 3, end: 7 },
            SplitDecision::SplitAroundRegion { start: 3, end: 7 }
        );
    }

    // -----------------------------------------------------------------------
    // Additional edge-case tests (issue #404 — TL7 coverage expansion)
    // -----------------------------------------------------------------------

    #[test]
    fn test_split_at_call_boundary() {
        // Simulate splitting an interval at a call boundary.
        // Interval: [0, 30) with uses at 5 and 25, call at position 15.
        // Splitting at 15 should produce two valid halves.
        let mut func = make_test_func(30);
        let interval = make_interval(0, &[(0, 30)], &[5, 25], &[0]);

        let result = split_interval(&interval, 15, &mut func);
        assert!(result.is_some());

        let result = result.unwrap();
        assert_eq!(result.original_interval.start(), 0);
        assert_eq!(result.original_interval.end(), 16);
        assert_eq!(result.new_interval.start(), 15);
        assert_eq!(result.new_interval.end(), 30);

        // Use at 5 should be in original, use at 25 in new.
        assert!(result.original_interval.use_positions.contains(&5));
        assert!(!result.original_interval.use_positions.contains(&25));
        assert!(result.new_interval.use_positions.contains(&25));
        assert!(!result.new_interval.use_positions.contains(&5));
    }

    // -----------------------------------------------------------------------
    // Call-aware split-point selector (LIVE-RANGE SPLITTING Stage 1)
    // -----------------------------------------------------------------------

    #[test]
    fn test_call_aware_selects_both_boundaries() {
        // Interval [0,30) crossing a call at 15, with uses at 5 (before) and 25
        // (after). The selector isolates both sides: split at 14 (before piece
        // ends at 15, exclusive) and 16 (after piece starts at 16).
        let interval = make_interval(0, &[(0, 30)], &[5, 25], &[0]);
        let points = call_aware_split_points(&interval, &[15]);
        assert_eq!(points, vec![14, 16]);
    }

    #[test]
    fn test_call_aware_isolation_leaves_pieces_call_free() {
        // Applying the selected points yields a before piece and an after piece
        // that are NOT live at the call; only the connector spans it.
        let mut func = make_test_func(30);
        let interval = make_interval(0, &[(0, 30)], &[5, 25], &[0]);
        let call = 15u32;
        let points = call_aware_split_points(&interval, &[call]);

        let first = split_interval(&interval, points[0], &mut func).unwrap();
        assert!(
            !first.original_interval.is_live_at(call),
            "before piece must be call-free"
        );
        let second = split_interval(&first.new_interval, points[1], &mut func).unwrap();
        assert!(
            !second.new_interval.is_live_at(call),
            "after piece must be call-free"
        );
        assert!(
            second.original_interval.is_live_at(call),
            "the connector is the only piece that spans the call"
        );
    }

    #[test]
    fn test_call_aware_empty_when_not_crossing() {
        // The call is outside the interval's live range: nothing to isolate.
        let interval = make_interval(0, &[(0, 10)], &[2, 8], &[0]);
        assert!(call_aware_split_points(&interval, &[20]).is_empty());
    }

    #[test]
    fn test_call_aware_empty_when_only_call_positions_used() {
        // Every use/def coincides with a call — no register-resident work to keep
        // off the call-clobbered lanes, so no split.
        let interval = make_interval(0, &[(0, 30)], &[10, 20], &[10]);
        assert!(call_aware_split_points(&interval, &[10, 20]).is_empty());
    }

    #[test]
    fn test_call_aware_only_right_when_nothing_before_call() {
        // Interval starts at 14 (its def), so the left boundary `14` is clamped
        // out (not strictly inside the interval) and only the right boundary is
        // emitted.
        let interval = make_interval(0, &[(14, 30)], &[25], &[14]);
        let points = call_aware_split_points(&interval, &[15]);
        assert_eq!(points, vec![16]);
    }

    #[test]
    fn test_split_produces_minimal_length_intervals() {
        // Split a [0, 4) interval at position 2. The original half also
        // covers the boundary copy source at position 2.
        let mut func = make_test_func(10);
        let interval = make_interval(0, &[(0, 4)], &[0, 3], &[0]);

        let result = split_interval(&interval, 2, &mut func);
        assert!(result.is_some());

        let result = result.unwrap();
        assert_eq!(result.original_interval.start(), 0);
        assert_eq!(result.original_interval.end(), 3);
        assert_eq!(result.new_interval.start(), 2);
        assert_eq!(result.new_interval.end(), 4);
    }

    #[test]
    fn test_split_def_at_exact_split_point_goes_to_new() {
        // A def position exactly at the split point should go to the new interval.
        let mut func = make_test_func(20);
        let interval = make_interval(0, &[(0, 20)], &[2, 15], &[0, 10]);

        let result = split_interval(&interval, 10, &mut func).unwrap();

        // def at 0 < 10 -> original; def at 10 >= 10 -> new
        assert!(result.original_interval.def_positions.contains(&0));
        assert!(!result.original_interval.def_positions.contains(&10));
        assert!(result.new_interval.def_positions.contains(&10));
        assert!(!result.new_interval.def_positions.contains(&0));
    }

    #[test]
    fn test_analyze_split_candidates_single_position_returns_empty() {
        // An interval with only one use/def position cannot be split.
        let interval = make_interval(0, &[(0, 20)], &[10], &[]);
        let candidates = analyze_split_candidates(&interval, &[], 10);
        assert!(
            candidates.is_empty(),
            "single position should produce no candidates"
        );
    }

    #[test]
    fn test_split_fpr_interval_preserves_class() {
        // Splitting an FPR interval should produce intervals of the same class.
        let mut func = make_test_func(20);
        let fpr_vreg = VReg {
            id: 0,
            class: RegClass::Fpr64,
        };
        let mut interval = LiveInterval::new(fpr_vreg);
        interval.add_range(0, 20);
        interval.use_positions = vec![2, 18];
        interval.def_positions = vec![0];
        interval.spill_weight = 2.0;

        let result = split_interval(&interval, 10, &mut func).unwrap();

        assert_eq!(result.original_vreg.class, RegClass::Fpr64);
        assert_eq!(result.new_vreg.class, RegClass::Fpr64);
        assert_eq!(result.original_interval.vreg.class, RegClass::Fpr64);
        assert_eq!(result.new_interval.vreg.class, RegClass::Fpr64);
    }

    // -----------------------------------------------------------------------
    // Tests for interference-aware and per-use splitting (issue #332)
    // -----------------------------------------------------------------------

    #[test]
    fn test_find_split_near_interference_basic() {
        // Interval [0, 20) with uses at 2, 8, 15 and def at 0.
        // Interference starts at position 10.
        // Should split after the last use before interference (use at 8) -> position 9.
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 20);
        iv.use_positions = vec![2, 8, 15];
        iv.def_positions = vec![0];

        let split = find_split_near_interference(&iv, 10);
        assert!(split.is_some());
        assert_eq!(split.unwrap(), 9);
    }

    #[test]
    fn test_find_split_near_interference_no_uses_before() {
        // All uses/defs are after the interference point.
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 20);
        iv.use_positions = vec![12, 18];
        iv.def_positions = vec![10];

        let split = find_split_near_interference(&iv, 5);
        assert!(
            split.is_none(),
            "no uses before interference, can't split usefully"
        );
    }

    #[test]
    fn test_find_split_near_interference_at_boundary() {
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 10);
        iv.use_positions = vec![0, 9];
        iv.def_positions = vec![0];

        // Interference at position 5.
        let split = find_split_near_interference(&iv, 5);
        assert!(split.is_some());
        let sp = split.unwrap();
        assert!(sp > iv.start() && sp < iv.end());
    }

    #[test]
    fn test_find_split_near_interference_def_only_before() {
        // Only a def before interference, no uses.
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 20);
        iv.use_positions = vec![15];
        iv.def_positions = vec![0];

        let split = find_split_near_interference(&iv, 10);
        assert!(split.is_some());
        // Should split after def at 0 -> position 1.
        assert_eq!(split.unwrap(), 1);
    }

    #[test]
    fn test_find_per_use_split_points_basic() {
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 30);
        iv.use_positions = vec![3, 7, 15, 25];
        iv.def_positions = vec![0];

        let splits = find_per_use_split_points(&iv);
        assert!(!splits.is_empty(), "should find split points between uses");

        // All split points should be within the interval.
        for (sp, _weight) in &splits {
            assert!(*sp > iv.start());
            assert!(*sp < iv.end());
        }

        // The first split should have the highest weight (largest gap).
        if splits.len() >= 2 {
            assert!(
                splits[0].1 >= splits[1].1,
                "splits should be sorted by weight descending"
            );
        }
    }

    #[test]
    fn test_find_per_use_split_points_empty() {
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 10);
        // Only one use -- can't split.
        iv.use_positions = vec![5];

        let splits = find_per_use_split_points(&iv);
        assert!(splits.is_empty());
    }

    #[test]
    fn test_find_per_use_split_points_consecutive_uses() {
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 10);
        // Uses at 3, 4, 5 -- gaps of 1, too small between uses.
        iv.use_positions = vec![3, 4, 5];
        iv.def_positions = vec![0];

        let splits = find_per_use_split_points(&iv);
        // Gap between def at 0 and use at 3 is 3, which is >= 2.
        assert!(
            !splits.is_empty(),
            "should find at least one split from def to first use"
        );
    }

    #[test]
    fn test_find_per_use_split_points_all_adjacent() {
        // All positions are adjacent -- no gaps >= 2.
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 5);
        iv.use_positions = vec![0, 1, 2, 3, 4];
        iv.def_positions = vec![];

        let splits = find_per_use_split_points(&iv);
        assert!(
            splits.is_empty(),
            "no gaps >= 2 means no viable split points"
        );
    }

    // ======================================================================
    // STAGE 2 — loop-invariant reload placement
    // ======================================================================

    /// Canonical single natural loop for the STAGE-2 tests:
    ///
    /// ```text
    ///   B0 (preheader): def v0 ;  br B1          preds []      succs [B1]
    ///   B1 (header)   : use v0 ;  cbr B2 / B3     preds [B0,B2] succs [B2,B3]
    ///   B2 (latch)    : <body>  ;  br  B1          preds [B1]    succs [B1]
    ///   B3 (exit)     : use v0 ;  ret             preds [B1]    succs []
    /// ```
    ///
    /// `body_inst` is placed in B2 (the latch/body); `header_use`/`exit_use`
    /// control whether v0 is used in the header (inside the loop) and in the exit
    /// (outside the loop). The natural loop body is {B1, B2}; B0 is the dedicated
    /// preheader (forward pred, single successor B1) and B3 is outside the loop.
    fn make_loop_func(body_inst: MachInst, header_use: bool, exit_use: bool) -> MachFunction {
        let v0 = vreg(0);
        let header_uses: &[VReg] = if header_use { &[v0] } else { &[] };
        let exit_uses: &[VReg] = if exit_use { &[v0] } else { &[] };
        let insts: Vec<MachInst> = vec![
            // B0: inst0 def v0, inst1 branch B1
            make_inst(1, &[v0], &[]),   // 0
            make_branch(&[BlockId(1)]), // 1
            // B1: inst2 header use, inst3 cond branch [B2,B3]
            make_inst(2, &[], header_uses),         // 2
            make_branch(&[BlockId(2), BlockId(3)]), // 3
            // B2: inst4 body, inst5 backedge branch B1
            body_inst,                  // 4
            make_branch(&[BlockId(1)]), // 5
            // B3: inst6 exit use, inst7 ret
            make_inst(6, &[], exit_uses), // 6
            make_branch(&[]),             // 7 (ret-like terminator)
        ];

        MachFunction {
            name: "loop_reload_test".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2), InstId(3)],
                    preds: vec![BlockId(0), BlockId(2)],
                    succs: vec![BlockId(2), BlockId(3)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![InstId(4), InstId(5)],
                    preds: vec![BlockId(1)],
                    succs: vec![BlockId(1)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![InstId(6), InstId(7)],
                    preds: vec![BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        }
    }

    #[test]
    fn stage2_invariant_value_gets_one_reload_point_on_the_preheader() {
        // v0 defined only in B0 (dominates the loop), used in the header (in-loop).
        let func = make_loop_func(make_inst(4, &[], &[]), true, false);
        let loop_info = crate::remat::compute_loop_info(&func);
        let points = loop_invariant_reload_points(&func, vreg(0), &loop_info, 1);
        assert_eq!(
            points.len(),
            1,
            "one innermost loop uses the invariant value"
        );
        // Placement is the forward-entry predecessor B0 (the preheader), NOT the
        // latch B2 (the back edge).
        assert_eq!(points[0].forward_preds, vec![BlockId(0)]);
        assert!(
            points[0].rewrite_blocks.contains(&1),
            "the header (an in-loop block) is a rewrite target"
        );
        assert!(
            !points[0].rewrite_blocks.contains(&3),
            "the exit (outside the loop) is never a rewrite target"
        );
    }

    #[test]
    fn stage2_def_inside_loop_refuses_reload() {
        // v0 REDEFINED in the loop body (B2): not loop-invariant. The selector
        // must return no points (fail-closed) — the invariance precondition
        // replaces the truncating split's cycle refusal.
        let redef = make_inst(4, &[vreg(0)], &[]); // defs v0 inside the loop
        let func = make_loop_func(redef, true, false);
        let loop_info = crate::remat::compute_loop_info(&func);
        let points = loop_invariant_reload_points(&func, vreg(0), &loop_info, 1);
        assert!(
            points.is_empty(),
            "a value redefined in the loop is not invariant and must be refused"
        );
    }

    #[test]
    fn stage2_min_uses_amortization_filter() {
        // Header uses v0 exactly ONCE. min_uses=1 => a point; min_uses=2 => none.
        let func1 = make_loop_func(make_inst(4, &[], &[]), true, false);
        let li1 = crate::remat::compute_loop_info(&func1);
        assert_eq!(
            loop_invariant_reload_points(&func1, vreg(0), &li1, 1).len(),
            1,
            "a single in-loop use qualifies at min_uses=1"
        );
        assert!(
            loop_invariant_reload_points(&func1, vreg(0), &li1, 2).is_empty(),
            "a single in-loop use is filtered out at min_uses=2 (amortization)"
        );

        // Header body uses v0 TWICE (put a second use in the latch B2): qualifies
        // at min_uses=2.
        let func2 = make_loop_func(make_inst(4, &[], &[vreg(0)]), true, false);
        let li2 = crate::remat::compute_loop_info(&func2);
        assert_eq!(
            loop_invariant_reload_points(&func2, vreg(0), &li2, 2).len(),
            1,
            "two in-loop uses qualify at min_uses=2"
        );
    }

    #[test]
    fn stage2_inject_rewrites_only_in_loop_uses_and_places_forward_copy() {
        // v0 used BOTH in the header (in-loop) and in the exit (outside-loop).
        let mut func = make_loop_func(make_inst(4, &[], &[]), true, true);
        let loop_info = crate::remat::compute_loop_info(&func);
        let points = loop_invariant_reload_points(&func, vreg(0), &loop_info, 1);
        assert_eq!(points.len(), 1);
        let next_vreg_before = func.next_vreg;
        let insts_before = func.insts.len();

        let v_in = inject_loop_reload(&mut func, &points[0])
            .expect("injection rewrites the in-loop use and returns the reload vreg");
        assert_eq!(
            v_in.id, next_vreg_before,
            "reload vreg is freshly allocated"
        );

        // A fresh reload vreg was allocated and a single copy inst added.
        assert_eq!(func.next_vreg, next_vreg_before + 1);
        assert_eq!(func.insts.len(), insts_before + 1);

        // The copy `v_in <- v0` sits in B0 (forward pred) BEFORE its terminator,
        // and NOT in the latch B2 (the back edge).
        let copy_id = *func.blocks[0]
            .insts
            .iter()
            .find(|&&id| func.insts[id.0 as usize].opcode == phi_elim::PSEUDO_COPY)
            .expect("reload copy is in the preheader B0");
        let copy = &func.insts[copy_id.0 as usize];
        assert_eq!(copy.defs, vec![MachOperand::VReg(v_in)]);
        assert_eq!(copy.uses, vec![MachOperand::VReg(vreg(0))]);
        // It precedes B0's terminator (the branch, InstId(1)).
        let copy_pos = func.blocks[0]
            .insts
            .iter()
            .position(|&id| id == copy_id)
            .unwrap();
        let term_pos = func.blocks[0]
            .insts
            .iter()
            .position(|&id| {
                func.insts[id.0 as usize]
                    .flags
                    .contains(InstFlags::IS_TERMINATOR)
            })
            .unwrap();
        assert!(copy_pos < term_pos, "reload copy precedes the terminator");
        assert!(
            !func.blocks[2]
                .insts
                .iter()
                .any(|&id| func.insts[id.0 as usize].opcode == phi_elim::PSEUDO_COPY),
            "no reload copy is ever placed on the latch/back edge"
        );

        // The header (in-loop) use of v0 was rewritten to v_in.
        assert_eq!(func.insts[2].uses, vec![MachOperand::VReg(v_in)]);
        // The exit (outside-loop) use of v0 was NOT rewritten — parent stays live.
        assert_eq!(func.insts[6].uses, vec![MachOperand::VReg(vreg(0))]);
    }

    #[test]
    fn stage2_no_in_loop_use_produces_no_point() {
        // v0 used only in the exit (outside the loop): nothing to reload.
        let func = make_loop_func(make_inst(4, &[], &[]), false, true);
        let loop_info = crate::remat::compute_loop_info(&func);
        let points = loop_invariant_reload_points(&func, vreg(0), &loop_info, 1);
        assert!(
            points.is_empty(),
            "a value with no in-loop use gets no reload point"
        );
    }

    #[test]
    fn stage2_multi_entry_loop_is_declined() {
        // Give the header TWO forward-entry predecessors (B0 and a new B4), so
        // there is no dedicated dominating preheader. Phase A declines rather
        // than synthesizing a shared preheader.
        let mut func = make_loop_func(make_inst(4, &[], &[]), true, false);
        // Add B4: br B1, entered from B0's other successor path. Simplest: make
        // B0 branch to both B1 and B4, and B4 branch to B1 — two forward entries.
        let b4 = BlockId(4);
        let jmp_to_header = InstId(func.insts.len() as u32);
        func.insts.push(make_branch(&[BlockId(1)]));
        func.blocks.push(MachBlock {
            insts: vec![jmp_to_header],
            preds: vec![BlockId(0)],
            succs: vec![BlockId(1)],
            loop_depth: 0,
        });
        // B0 now branches to B1 and B4; header B1 gains B4 as a forward pred.
        func.blocks[0].succs = vec![BlockId(1), b4];
        func.insts[1] = make_branch(&[BlockId(1), b4]);
        func.blocks[1].preds = vec![BlockId(0), BlockId(2), b4];
        func.block_order.push(b4);

        let loop_info = crate::remat::compute_loop_info(&func);
        let l = loop_info.get(1).expect("loop headed by B1");
        assert_eq!(
            l.forward_preds.len(),
            2,
            "header has two forward-entry predecessors"
        );
        let points = loop_invariant_reload_points(&func, vreg(0), &loop_info, 1);
        assert!(
            points.is_empty(),
            "a multi-entry loop with no dedicated preheader is declined (Phase A)"
        );
    }

    /// Bug #66 regression pin: an in-block split point AT or AFTER a block's
    /// first terminator must be REJECTED. A machine conditional branch is a
    /// TWO-terminator group (x86 `Jcc; Jmp`); a connector between them runs
    /// only on the fall-through edge, so the split child is undefined on the
    /// taken edge — the exact silent miscompile the repro shipped (the taken
    /// path read overflow-check scraps as v1/v3). Terminator positions look
    /// like free gap to the midpoint chooser (branches touch no vregs), which
    /// is precisely how the point got there.
    #[test]
    fn test_split_point_inside_terminator_sequence_is_rejected() {
        // B0: [def v0 @0, Jcc(->B1) @1, Jmp(->B2) @2]   (two-terminator tail)
        // B1: [use v0 @3, ret-ish @4]
        // B2: [use v0 @5, ret-ish @6]
        let insts = vec![
            make_inst(1, &[vreg(0)], &[]), // 0: def v0
            make_branch(&[BlockId(1)]),    // 1: Jcc  (first terminator)
            make_branch(&[BlockId(2)]),    // 2: Jmp  (second terminator)
            make_inst(2, &[], &[vreg(0)]), // 3: use v0 (taken path)
            make_inst(3, &[], &[]),        // 4
            make_inst(2, &[], &[vreg(0)]), // 5: use v0 (fall-through path)
            make_inst(3, &[], &[]),        // 6
        ];
        let mut func = MachFunction {
            name: "two_terminator_tail".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1), InstId(2)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(3), InstId(4)],
                    preds: vec![BlockId(0)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(5), InstId(6)],
                    preds: vec![BlockId(0)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let interval = make_interval(0, &[(0, 7)], &[3, 5], &[0]);

        // Point 2 = between Jcc and Jmp — the shipped-miscompile position.
        let err = split_interval_checked(&interval, 2, &mut func)
            .expect_err("a split point between the two terminators must be rejected");
        assert!(
            matches!(
                err,
                SplitError::UnsafeCfg(SplitCfgSafetyError::PointInsideTerminatorSequence {
                    block: BlockId(0),
                    point: 2,
                    first_terminator_pos: 1,
                })
            ),
            "unexpected error for the between-terminators point: {err:?}"
        );

        // Point 1 = AT the first terminator is SAFE: `insert_copy_at_point`
        // inserts BEFORE the instruction at the point, so the copy lands
        // ahead of the whole `Jcc; Jmp` group and dominates both successors.
        // (This is also the entry-block fallback split shape — it must stay
        // legal.)
        split_interval_checked(&interval, 1, &mut func)
            .expect("a split point AT the first terminator inserts before the group and is safe");
    }
}
