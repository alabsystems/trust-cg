// trust-cg-opt/pgo/profile_use.rs - Profile-use optimization pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-18-pgo-workflow.md
// Issue: #396

//! Profile-use pass plumbing.
//!
//! This pass proves that a loaded `.profdata` artifact reaches the O2/O3
//! optimization pipeline, computes profile hotness, and applies the first small
//! profile consumer: conservative block layout. Explicitly hot profiled
//! successors are preferred for layout-near chains. Normal AArch64 conditional
//! blocks with an implicit layout fallthrough are made explicit with a
//! `B <fallthrough>` only when a hot profile changes the layout, while
//! remaining layout-dependent CFGs are skipped.
//! Follow-up consumers can query the attached profile from here for additional
//! hotness-driven heuristics.

use std::collections::BTreeMap;

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
};

use crate::pass_manager::{AnalysisCache, MachinePass};

use super::schema::{FunctionProfile, ProfData};

/// Pass name used in pass-manager diagnostics and `TRUST_CG_DISABLE_PASSES`.
pub const PROFILE_USE_PASS_NAME: &str = "profile-use";

/// Kill switch for the profile-guided block layout: set `TCG_PGO_NO_LAYOUT`
/// (any value) to skip the hot-chain reordering while keeping the hotness
/// handout to downstream consumers (for PGO effect attribution A/B runs).
/// Inert without a profile.
fn pgo_layout_enabled() -> bool {
    std::env::var_os("TCG_PGO_NO_LAYOUT").is_none()
}

/// Opt-in decision log (`TCG_PGO_LAYOUT_LOG=1`): one stderr line per layout
/// chain pick, with the candidate hit counts, so profile-layout decisions can
/// be attributed program-by-program. Mirrors `TCG_LATCH_SPLIT_LOG`.
fn pgo_layout_log_enabled() -> bool {
    std::env::var_os("TCG_PGO_LAYOUT_LOG").is_some()
}

/// Kill switch for the zero-hit-span chain gate: set `TCG_PGO_LAYOUT_UNGATED`
/// (any value) to restore the pre-gate greedy hot-chain layout that may
/// displace executed blocks (for A/B attribution against the gated default).
///
/// The gate exists because the greedy chain was measured to be the entire
/// ~3% PGO-USE regression on Stanford/Puzzle: it hoisted the `Trial` k-scan
/// latch across 22 blocks (five of them warm, ~11M hits each), and even the
/// single residual pick that displaced one 5.2M-hit "relatively cold" block
/// reproduced the full 3%. The win it preserves (Stanford/Towers `Move`,
/// ~10%) only ever skips zero-hit error-guard blocks. See
/// `chain_deviation_allowed`.
fn pgo_layout_chain_gate_enabled() -> bool {
    std::env::var_os("TCG_PGO_LAYOUT_UNGATED").is_none()
}

fn profile_use_pass_id() -> PassId {
    PassId::new(PROFILE_USE_PASS_NAME)
}

/// Profile-use pass.
///
/// The pass owns a decoded [`ProfData`] so it can be scheduled in the normal
/// pass manager. It currently applies a conservative block-layout consumer:
/// materializable conditional fallthroughs are made explicit, and the resulting
/// explicit-control-flow functions are laid out by hot successor chains.
#[derive(Debug, Clone)]
pub struct ProfileUsePass {
    profile: ProfData,
    hotness: ProfileHotness,
}

impl ProfileUsePass {
    /// Create a profile-use pass from an already-decoded profile.
    pub fn new(profile: ProfData) -> Self {
        let hotness = ProfileHotness::from_profile(&profile);
        Self { profile, hotness }
    }

    /// Return the attached profile.
    pub fn profile(&self) -> &ProfData {
        &self.profile
    }

    /// Return the hotness summary computed from the attached profile.
    pub fn hotness(&self) -> &ProfileHotness {
        &self.hotness
    }

    /// Return aggregate profile-use statistics for diagnostics.
    pub fn stats(&self) -> &ProfileUseStats {
        self.hotness.stats()
    }

    /// Look up profile data for a machine function by symbol name.
    pub fn function_profile(&self, func: &MachFunction) -> Option<&FunctionProfile> {
        self.profile.function(&func.name)
    }

    /// Look up function hotness by machine function symbol name.
    pub fn function_hotness(&self, func: &MachFunction) -> Option<FunctionHotness> {
        self.hotness.function(&func.name)
    }

    /// Look up block hotness by machine function symbol name and block id.
    ///
    /// Missing block records inside a profiled function are reported as
    /// zero-hit cold blocks, matching the `.profdata` design contract.
    pub fn block_hotness(&self, func: &MachFunction, block: BlockId) -> Option<BlockHotness> {
        self.hotness.block(&func.name, block)
    }

    fn apply_profile_layout(&self, func: &mut MachFunction) -> bool {
        self.apply_profile_layout_impl(func, None)
    }

    fn apply_profile_layout_with_provenance(
        &self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.apply_profile_layout_impl(func, Some(provenance))
    }

    fn apply_profile_layout_impl(
        &self,
        func: &mut MachFunction,
        provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        if !pgo_layout_enabled() {
            return false;
        }
        if self.hotness.function(&func.name).is_none() || func.block_order.len() <= 1 {
            return false;
        }

        let original = func.block_order.clone();
        let Some(order) = self.compute_profile_layout(func, &original) else {
            return false;
        };
        if order == original {
            return false;
        }

        let Some(fallthroughs) = fallthrough_materialization_plan(func) else {
            return false;
        };
        if pgo_layout_log_enabled() {
            let new_pos: BTreeMap<BlockId, usize> =
                order.iter().enumerate().map(|(i, &b)| (b, i)).collect();
            for ft in &fallthroughs {
                let block_pos = new_pos.get(&ft.block).copied().unwrap_or(usize::MAX);
                let ft_pos = new_pos.get(&ft.fallthrough).copied().unwrap_or(usize::MAX);
                if ft_pos != block_pos.wrapping_add(1) {
                    eprintln!(
                        "pgo-layout: {} RESIDUAL nonadjacent ft: B{} (hits={}) -> b B{} (hits={} hot={})",
                        func.name,
                        ft.block.0,
                        self.block_hits(&func.name, ft.block),
                        ft.fallthrough.0,
                        self.block_hits(&func.name, ft.fallthrough),
                        self.is_hot_layout_block(&func.name, ft.fallthrough),
                    );
                }
            }
        }
        materialize_conditional_fallthroughs(func, fallthroughs, provenance);
        // Reordering block layout does not allocate, delete, or replace
        // instructions. Provenance remains keyed by stable InstIds, and codegen
        // records the post-layout binary offsets later.
        func.block_order = order;
        // Mark the profile order authoritative so the codegen-final static
        // branch layout does not re-derive (and silently drop) it.
        func.profile_ordered = true;
        true
    }

    fn compute_profile_layout(
        &self,
        func: &MachFunction,
        original: &[BlockId],
    ) -> Option<Vec<BlockId>> {
        let block_count = func.blocks.len();
        let entry_index = func.entry.0 as usize;
        if entry_index >= block_count || !original.contains(&func.entry) {
            return None;
        }

        let mut active = vec![false; block_count];
        let mut positions = vec![usize::MAX; block_count];
        for (index, &block) in original.iter().enumerate() {
            let block_index = block.0 as usize;
            if block_index >= block_count {
                return None;
            }
            active[block_index] = true;
            positions[block_index] = index;
        }

        let mut placed = vec![false; block_count];
        let mut order = Vec::with_capacity(original.len());
        placed[entry_index] = true;
        order.push(func.entry);

        let mut current = func.entry;
        if pgo_layout_log_enabled() {
            let table: Vec<String> = original
                .iter()
                .map(|b| {
                    format!(
                        "p{}:B{}={}{}",
                        positions[b.0 as usize],
                        b.0,
                        self.block_hits(&func.name, *b),
                        match self.hotness.block(&func.name, *b).map(|h| h.class) {
                            Some(HotnessClass::Hot) => "H",
                            Some(HotnessClass::Warm) => "W",
                            Some(HotnessClass::Cold) => "C",
                            _ => "?",
                        }
                    )
                })
                .collect();
            eprintln!(
                "pgo-layout: {} original order: {}",
                func.name,
                table.join(" ")
            );
        }
        while order.len() < original.len() {
            let succ_pick =
                self.pick_hottest_successor(func, current, &active, &placed, &positions, original);
            if pgo_layout_log_enabled() {
                let succ_hits: Vec<String> = func
                    .block(current)
                    .succs
                    .iter()
                    .map(|s| {
                        let placed_mark = if placed.get(s.0 as usize).copied().unwrap_or(false) {
                            "*"
                        } else {
                            ""
                        };
                        format!(
                            "B{}{}={}",
                            s.0,
                            placed_mark,
                            self.block_hits(&func.name, *s)
                        )
                    })
                    .collect();
                match succ_pick {
                    Some(next) => eprintln!(
                        "pgo-layout: {} chain B{} -> B{} (succs: {}) static-next-pos={} chosen-pos={}",
                        func.name,
                        current.0,
                        next.0,
                        succ_hits.join(" "),
                        original_position(&positions, current).saturating_add(1),
                        original_position(&positions, next),
                    ),
                    None => {
                        if !func.block(current).succs.is_empty() {
                            eprintln!(
                                "pgo-layout: {} chain-break at B{} (succs: {})",
                                func.name,
                                current.0,
                                succ_hits.join(" ")
                            );
                        }
                    }
                }
            }
            let next = succ_pick.or_else(|| self.pick_next_chain_head(original, &active, &placed));
            let Some(next) = next else {
                break;
            };
            placed[next.0 as usize] = true;
            order.push(next);
            current = next;
        }

        if order.len() == original.len() {
            Some(order)
        } else {
            None
        }
    }

    fn pick_hottest_successor(
        &self,
        func: &MachFunction,
        block: BlockId,
        active: &[bool],
        placed: &[bool],
        positions: &[usize],
        original: &[BlockId],
    ) -> Option<BlockId> {
        if !self.is_hot_layout_block(&func.name, block) {
            return None;
        }

        let candidates = func.block(block).succs.iter().copied().filter(|&succ| {
            let index = succ.0 as usize;
            active.get(index).copied().unwrap_or(false)
                && !placed.get(index).copied().unwrap_or(false)
                && self.is_hot_layout_block(&func.name, succ)
        });
        let best = self.pick_hottest_block(&func.name, candidates, positions)?;
        if !pgo_layout_chain_gate_enabled()
            || self.chain_deviation_allowed(func, block, best, active, placed, positions, original)
        {
            return Some(best);
        }
        // The hottest successor would displace live (non-cold) code: fall back
        // to the static-order successor when it is itself an eligible hot
        // chain candidate, otherwise end the chain and keep the static order.
        let static_next = original
            .get(original_position(positions, block).checked_add(1)?)
            .copied()?;
        let index = static_next.0 as usize;
        let eligible = active.get(index).copied().unwrap_or(false)
            && !placed.get(index).copied().unwrap_or(false)
            && self.is_hot_layout_block(&func.name, static_next)
            && func.block(block).succs.contains(&static_next);
        if pgo_layout_log_enabled() {
            eprintln!(
                "pgo-layout: {} chain gate REJECTED B{} -> B{} (skips live code); fallback {}",
                func.name,
                block.0,
                best.0,
                if eligible {
                    format!("static-next B{}", static_next.0)
                } else {
                    "chain-break".to_string()
                }
            );
        }
        eligible.then_some(static_next)
    }

    /// Zero-hit-span chain gate: a chain pick may deviate from the
    /// static-order successor only when every active, unplaced block it skips
    /// over (the original positions strictly between the current block and
    /// the pick) has ZERO profile hits. Sinking never-executed error guards
    /// out of the hot fallthrough path is exactly the measured PGO layout win
    /// (Towers `Move`, ~10%); displacing code that runs at all is exactly the
    /// measured loss — Puzzle `Trial` regressed ~3% from a single pick that
    /// skipped a 5.2M-hit block the relative classifier called "cold" (9.7%
    /// of the function maximum), so relative coldness is NOT a displacement
    /// license. Backward picks displace the entire abandoned suffix and are
    /// refused outright.
    #[allow(clippy::too_many_arguments)]
    fn chain_deviation_allowed(
        &self,
        func: &MachFunction,
        block: BlockId,
        chosen: BlockId,
        active: &[bool],
        placed: &[bool],
        positions: &[usize],
        original: &[BlockId],
    ) -> bool {
        let current_pos = original_position(positions, block);
        let chosen_pos = original_position(positions, chosen);
        if chosen_pos == current_pos.wrapping_add(1) {
            return true;
        }
        if chosen_pos <= current_pos {
            return false;
        }
        original[current_pos + 1..chosen_pos]
            .iter()
            .all(|&skipped| {
                let index = skipped.0 as usize;
                let live = active.get(index).copied().unwrap_or(false)
                    && !placed.get(index).copied().unwrap_or(false);
                !live
                    || matches!(
                        self.hotness.block(&func.name, skipped),
                        Some(hotness) if hotness.hits == 0
                    )
            })
    }

    fn pick_next_chain_head(
        &self,
        original: &[BlockId],
        active: &[bool],
        placed: &[bool],
    ) -> Option<BlockId> {
        original.iter().copied().find(|&block| {
            let index = block.0 as usize;
            active.get(index).copied().unwrap_or(false)
                && !placed.get(index).copied().unwrap_or(false)
        })
    }

    fn is_hot_layout_block(&self, function: &str, block: BlockId) -> bool {
        matches!(
            self.hotness.block(function, block),
            Some(hotness) if hotness.hits > 0 && hotness.class.is_hot()
        )
    }

    fn pick_hottest_block<I>(
        &self,
        function: &str,
        candidates: I,
        positions: &[usize],
    ) -> Option<BlockId>
    where
        I: IntoIterator<Item = BlockId>,
    {
        let mut best = None;
        for candidate in candidates {
            if best
                .map(|current| {
                    self.is_better_layout_candidate(function, candidate, current, positions)
                })
                .unwrap_or(true)
            {
                best = Some(candidate);
            }
        }
        best
    }

    fn is_better_layout_candidate(
        &self,
        function: &str,
        candidate: BlockId,
        current: BlockId,
        positions: &[usize],
    ) -> bool {
        let candidate_hits = self.block_hits(function, candidate);
        let current_hits = self.block_hits(function, current);
        candidate_hits > current_hits
            || (candidate_hits == current_hits
                && original_position(positions, candidate) < original_position(positions, current))
    }

    fn block_hits(&self, function: &str, block: BlockId) -> u64 {
        self.hotness
            .block(function, block)
            .map(|hotness| hotness.hits)
            .unwrap_or(0)
    }
}

impl MachinePass for ProfileUsePass {
    fn name(&self) -> &str {
        PROFILE_USE_PASS_NAME
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        self.apply_profile_layout(func)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.apply_profile_layout_with_provenance(func, provenance)
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_provenance(func, provenance)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ConditionalFallthrough {
    block: BlockId,
    branch: InstId,
    fallthrough: BlockId,
}

fn fallthrough_materialization_plan(func: &MachFunction) -> Option<Vec<ConditionalFallthrough>> {
    let mut fallthroughs = Vec::new();
    for (layout_index, &block) in func.block_order.iter().enumerate() {
        let mach_block = func.block(block);
        if mach_block.succs.is_empty() {
            continue;
        }

        let &last_inst_id = mach_block.insts.last()?;
        let last_inst = func.inst(last_inst_id);
        if last_inst.is_unconditional_branch() {
            continue;
        }
        if last_inst.is_conditional_branch() {
            fallthroughs.push(conditional_layout_fallthrough(
                func,
                block,
                layout_index,
                last_inst_id,
                last_inst,
            )?);
            continue;
        }
        return None;
    }
    Some(fallthroughs)
}

fn conditional_layout_fallthrough(
    func: &MachFunction,
    block: BlockId,
    layout_index: usize,
    branch_id: InstId,
    branch: &MachInst,
) -> Option<ConditionalFallthrough> {
    let mach_block = func.block(block);
    if mach_block.succs.len() != 2 {
        return None;
    }

    let fallthrough = *func.block_order.get(layout_index + 1)?;
    if !mach_block.succs.contains(&fallthrough) {
        return None;
    }

    let mut explicit_targets = branch.operands.iter().filter_map(|operand| match operand {
        MachOperand::Block(target) => Some(*target),
        _ => None,
    });
    let target = explicit_targets.next()?;
    if explicit_targets.next().is_some()
        || target == fallthrough
        || !mach_block.succs.contains(&target)
    {
        return None;
    }

    Some(ConditionalFallthrough {
        block,
        branch: branch_id,
        fallthrough,
    })
}

fn materialize_conditional_fallthroughs(
    func: &mut MachFunction,
    fallthroughs: Vec<ConditionalFallthrough>,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let mut changed = false;
    for fallthrough in fallthroughs {
        let mut branch = MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(fallthrough.fallthrough)],
        );
        branch.source_loc = func.inst(fallthrough.branch).source_loc;

        let branch_id = func.push_inst(branch);
        func.append_inst(fallthrough.block, branch_id);
        if let Some(provenance) = provenance.as_deref_mut() {
            record_materialized_fallthrough_provenance(provenance, fallthrough.branch, branch_id);
        }
        changed = true;
    }
    changed
}

fn record_materialized_fallthrough_provenance(
    provenance: &mut ProvenanceMap,
    source_branch: InstId,
    materialized_branch: InstId,
) {
    let pass = profile_use_pass_id();
    if provenance.get_entry(source_branch).is_some() {
        provenance.record_clone(source_branch, materialized_branch, pass);
    } else {
        provenance.record_creation(
            materialized_branch,
            pass,
            "profile-use materialized conditional fallthrough branch",
        );
    }
}

fn original_position(positions: &[usize], block: BlockId) -> usize {
    positions
        .get(block.0 as usize)
        .copied()
        .unwrap_or(usize::MAX)
}

/// Coarse profile hotness class for function and block consumers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HotnessClass {
    /// Counter is absent from the loaded profile.
    Unknown,
    /// Counter is zero or materially colder than the relevant entry count.
    Cold,
    /// Counter is present but not classified as hot or cold.
    Warm,
    /// Counter is close to the hottest relevant count.
    Hot,
}

impl HotnessClass {
    /// Returns true for [`HotnessClass::Hot`].
    pub fn is_hot(self) -> bool {
        matches!(self, Self::Hot)
    }

    /// Returns true for [`HotnessClass::Cold`].
    pub fn is_cold(self) -> bool {
        matches!(self, Self::Cold)
    }
}

/// Profile-wide hotness summary computed from a loaded [`ProfData`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileHotness {
    max_function_count: u64,
    stats: ProfileUseStats,
    functions: BTreeMap<String, FunctionHotnessData>,
}

impl ProfileHotness {
    /// Build a profile hotness summary from decoded profile data.
    pub fn from_profile(profile: &ProfData) -> Self {
        let max_function_count = profile
            .functions
            .iter()
            .map(function_count)
            .max()
            .unwrap_or(0);
        let functions = profile
            .functions
            .iter()
            .map(|function| {
                let function_hotness = classify_count(function_count(function), max_function_count);
                (
                    function.name.clone(),
                    FunctionHotnessData::from_function(function, function_hotness),
                )
            })
            .collect();
        let stats = ProfileUseStats::from_functions(max_function_count, &functions);

        Self {
            max_function_count,
            stats,
            functions,
        }
    }

    /// Hottest function count observed in the profile.
    pub fn max_function_count(&self) -> u64 {
        self.max_function_count
    }

    /// Aggregate stats derived from this hotness summary.
    pub fn stats(&self) -> &ProfileUseStats {
        &self.stats
    }

    /// Look up hotness for a function symbol.
    pub fn function(&self, name: &str) -> Option<FunctionHotness> {
        self.functions
            .get(name)
            .map(|data| data.function_hotness(self.max_function_count))
    }

    /// Look up hotness for a function block.
    ///
    /// Missing block records inside a profiled function return a zero-hit cold
    /// result. Missing functions return `None` so callers can distinguish a
    /// stale/partial profile from a genuinely cold block.
    pub fn block(&self, function: &str, block: BlockId) -> Option<BlockHotness> {
        self.functions
            .get(function)
            .map(|data| data.block_hotness(block))
    }

    /// Estimate the probability that the 2-way conditional branch terminating
    /// `block` transfers to `taken`, from block hit counts alone.
    ///
    /// Resolution order (first applicable wins), where `B = block` and
    /// `other` is `block`'s other successor:
    ///
    /// 1. `hits(B) > 0` is required — a block the canary never executed (or
    ///    one absent from the profile, e.g. minted by a later pass so its id
    ///    is unknown to the canary run) yields `None`, never a guess.
    /// 2. `taken` has `B` as its SOLE predecessor: `hits(taken) / hits(B)`.
    /// 3. `other` has `B` as its sole predecessor: `1 - hits(other) / hits(B)`.
    /// 4. Kirchhoff flow conservation: every OTHER predecessor `p` of `taken`
    ///    must have a statically-known edge flow into `taken` — which block
    ///    counters only give when `taken` is `p`'s sole successor
    ///    (`flow(p->taken) = hits(p)`). Then
    ///    `rate = (hits(taken) - sum(flow)) / hits(B)`, clamped to `[0, 1]`
    ///    (counter skew from non-atomic AOT increments can leave small
    ///    imbalances; clamping keeps the estimate a probability).
    /// 5. Otherwise `None` (fail-safe: callers must treat this as "no
    ///    profile evidence", not as 0 or 1).
    ///
    /// `function` selects the profile record (normally `func.name`); `func`
    /// supplies the CFG. `block` must have exactly two distinct successors,
    /// one of which is `taken`; anything else yields `None`.
    pub fn branch_taken_rate(
        &self,
        function: &str,
        func: &MachFunction,
        block: BlockId,
        taken: BlockId,
    ) -> Option<f64> {
        let hits = |b: BlockId| -> u64 { self.block(function, b).map(|h| h.hits).unwrap_or(0) };
        // Unprofiled function -> no evidence at all.
        self.functions.get(function)?;

        let hits_b = hits(block);
        if hits_b == 0 {
            return None;
        }

        // Exactly two distinct successors, one of them `taken`.
        let succs = &func.blocks.get(block.0 as usize)?.succs;
        if succs.len() != 2 || succs[0] == succs[1] || !succs.contains(&taken) {
            return None;
        }
        let other = if succs[0] == taken {
            succs[1]
        } else {
            succs[0]
        };

        let sole_pred_is_block = |b: BlockId| -> bool {
            func.blocks
                .get(b.0 as usize)
                .is_some_and(|blk| blk.preds.len() == 1 && blk.preds[0] == block)
        };

        if sole_pred_is_block(taken) {
            return Some(clamp01(hits(taken) as f64 / hits_b as f64));
        }
        if sole_pred_is_block(other) {
            return Some(clamp01(1.0 - hits(other) as f64 / hits_b as f64));
        }

        // Kirchhoff: subtract every other predecessor's edge flow into `taken`.
        // Block counters determine `flow(p -> taken)` only when `taken` is p's
        // sole successor; any other shape is unresolvable -> None.
        let taken_preds = &func.blocks.get(taken.0 as usize)?.preds;
        if !taken_preds.contains(&block) {
            return None;
        }
        let mut inflow: u64 = 0;
        for &p in taken_preds {
            if p == block {
                continue;
            }
            let p_succs = &func.blocks.get(p.0 as usize)?.succs;
            let sole_succ_is_taken = !p_succs.is_empty() && p_succs.iter().all(|&s| s == taken);
            if !sole_succ_is_taken {
                return None;
            }
            inflow = inflow.saturating_add(hits(p));
        }
        let from_block = hits(taken).saturating_sub(inflow);
        Some(clamp01(from_block as f64 / hits_b as f64))
    }
}

fn clamp01(x: f64) -> f64 {
    x.clamp(0.0, 1.0)
}

/// Aggregate profile-use statistics for diagnostics and tests.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ProfileUseStats {
    /// Number of function records in the loaded profile.
    pub profiled_functions: usize,
    /// Number of explicit block records in the loaded profile.
    pub profiled_blocks: usize,
    /// Functions classified as hot.
    pub hot_functions: usize,
    /// Functions classified as warm.
    pub warm_functions: usize,
    /// Functions classified as cold.
    pub cold_functions: usize,
    /// Explicit block records classified as hot within their function.
    pub hot_blocks: usize,
    /// Explicit block records classified as warm within their function.
    pub warm_blocks: usize,
    /// Explicit block records classified as cold within their function.
    pub cold_blocks: usize,
    /// Hottest effective function count observed in the profile.
    pub max_function_count: u64,
    /// Sum of effective function counts used for classification.
    pub total_function_count: u64,
    /// Sum of explicit block hit counts in the profile.
    pub total_block_hits: u64,
}

impl ProfileUseStats {
    fn from_functions(
        max_function_count: u64,
        functions: &BTreeMap<String, FunctionHotnessData>,
    ) -> Self {
        let mut stats = Self {
            max_function_count,
            profiled_functions: functions.len(),
            ..Self::default()
        };

        for function in functions.values() {
            stats.record_function(function);
        }

        stats
    }

    fn record_function(&mut self, function: &FunctionHotnessData) {
        self.total_function_count = self
            .total_function_count
            .saturating_add(function.call_count);
        self.record_function_class(function.class);

        let function_count = function.call_count.max(function.max_block_count);
        for hits in function.blocks.values().copied() {
            self.profiled_blocks += 1;
            self.total_block_hits = self.total_block_hits.saturating_add(hits);
            self.record_block_class(classify_count(hits, function_count));
        }
    }

    fn record_function_class(&mut self, class: HotnessClass) {
        match class {
            HotnessClass::Hot => self.hot_functions += 1,
            HotnessClass::Warm => self.warm_functions += 1,
            HotnessClass::Cold => self.cold_functions += 1,
            HotnessClass::Unknown => {}
        }
    }

    fn record_block_class(&mut self, class: HotnessClass) {
        match class {
            HotnessClass::Hot => self.hot_blocks += 1,
            HotnessClass::Warm => self.warm_blocks += 1,
            HotnessClass::Cold => self.cold_blocks += 1,
            HotnessClass::Unknown => {}
        }
    }
}

/// Hotness data for a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FunctionHotness {
    /// Function entry count, or the hottest block count if entry counters were
    /// not recorded separately.
    pub call_count: u64,
    /// Hottest function count observed in the loaded profile.
    pub max_function_count: u64,
    /// Coarse hotness classification for this function.
    pub class: HotnessClass,
}

/// Hotness data for a basic block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockHotness {
    /// Basic block id from [`trust_cg_ir::BlockId`].
    pub block: BlockId,
    /// Raw block hit count from the profile. Missing block records are `0`.
    pub hits: u64,
    /// Denominator used for intra-function classification.
    pub function_count: u64,
    /// Coarse hotness classification for this block.
    pub class: HotnessClass,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FunctionHotnessData {
    call_count: u64,
    max_block_count: u64,
    class: HotnessClass,
    blocks: BTreeMap<u32, u64>,
}

impl FunctionHotnessData {
    fn from_function(function: &FunctionProfile, class: HotnessClass) -> Self {
        let blocks = function
            .blocks
            .iter()
            .map(|block| (block.block_id, block.hits))
            .collect::<BTreeMap<_, _>>();
        Self {
            call_count: function_count(function),
            max_block_count: function
                .blocks
                .iter()
                .map(|block| block.hits)
                .max()
                .unwrap_or(0),
            class,
            blocks,
        }
    }

    fn function_hotness(&self, max_function_count: u64) -> FunctionHotness {
        FunctionHotness {
            call_count: self.call_count,
            max_function_count,
            class: self.class,
        }
    }

    fn block_hotness(&self, block: BlockId) -> BlockHotness {
        let hits = self.blocks.get(&block.0).copied().unwrap_or(0);
        let function_count = self.call_count.max(self.max_block_count);
        BlockHotness {
            block,
            hits,
            function_count,
            class: classify_count(hits, function_count),
        }
    }
}

fn function_count(function: &FunctionProfile) -> u64 {
    function.call_count.max(
        function
            .blocks
            .iter()
            .map(|block| block.hits)
            .max()
            .unwrap_or(0),
    )
}

fn classify_count(count: u64, hottest: u64) -> HotnessClass {
    if hottest == 0 || count == 0 {
        return HotnessClass::Cold;
    }
    let count = u128::from(count);
    let hottest = u128::from(hottest);
    if count * 100 >= hottest * 80 {
        HotnessClass::Hot
    } else if count * 100 <= hottest * 10 {
        HotnessClass::Cold
    } else {
        HotnessClass::Warm
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pgo::{BlockProfile, FunctionProfile};
    use trust_cg_ir::{
        AArch64Opcode, BlockId, MachInst, MachOperand, ProvenanceStatus, Signature, SourceLoc,
        TransformKind, TrustIrInstId,
    };

    fn append_inst(func: &mut MachFunction, block: BlockId, inst: MachInst) {
        let inst_id = func.push_inst(inst);
        func.append_inst(block, inst_id);
    }

    fn explicit_diamond_func(name: &str) -> MachFunction {
        let mut func = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let cold = func.create_block();
        let hot = func.create_block();
        let join = func.create_block();

        append_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::BCond, vec![MachOperand::Block(cold)]),
        );
        append_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(hot)]),
        );
        append_inst(
            &mut func,
            cold,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(join)]),
        );
        append_inst(
            &mut func,
            hot,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(join)]),
        );
        append_inst(&mut func, join, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(entry, cold);
        func.add_edge(entry, hot);
        func.add_edge(cold, join);
        func.add_edge(hot, join);
        func
    }

    fn implicit_conditional_diamond_func(name: &str) -> MachFunction {
        let mut func = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let cold = func.create_block();
        let hot = func.create_block();
        let join = func.create_block();

        append_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::BCond, vec![MachOperand::Block(cold)]),
        );
        append_inst(
            &mut func,
            cold,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(join)]),
        );
        append_inst(
            &mut func,
            hot,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(join)]),
        );
        append_inst(&mut func, join, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(entry, cold);
        func.add_edge(entry, hot);
        func.add_edge(cold, join);
        func.add_edge(hot, join);
        func.block_order = vec![entry, hot, cold, join];
        func
    }

    #[test]
    fn profile_use_pass_is_named_and_exposes_analysis() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("hot");
        function.call_count = 99;
        function.blocks.push(BlockProfile::new(0, 99));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let mut func = MachFunction::new("hot".to_string(), Signature::new(vec![], vec![]));

        assert_eq!(pass.name(), PROFILE_USE_PASS_NAME);
        assert_eq!(pass.function_profile(&func).unwrap().call_count, 99);
        assert_eq!(
            pass.function_hotness(&func).unwrap().class,
            HotnessClass::Hot
        );
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn profile_use_pass_missing_function_is_still_noop() {
        let mut pass = ProfileUsePass::new(ProfData::new(0));
        let mut func = MachFunction::new("cold".to_string(), Signature::new(vec![], vec![]));

        assert!(pass.function_profile(&func).is_none());
        assert!(pass.function_hotness(&func).is_none());
        assert!(pass.block_hotness(&func, BlockId(0)).is_none());
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn profile_use_pass_classifies_function_hotness() {
        let mut profile = ProfData::new(0x1234);
        let mut hot = FunctionProfile::new("hot_fn");
        hot.call_count = 10_000;
        hot.blocks.push(BlockProfile::new(0, 10_000));
        let mut warm = FunctionProfile::new("warm_fn");
        warm.call_count = 2_000;
        warm.blocks.push(BlockProfile::new(0, 2_000));
        let mut cold = FunctionProfile::new("cold_fn");
        cold.call_count = 0;
        cold.blocks.push(BlockProfile::new(0, 0));
        profile.functions.extend([hot, warm, cold]);

        let pass = ProfileUsePass::new(profile);
        let hot_func = MachFunction::new("hot_fn".to_string(), Signature::new(vec![], vec![]));
        let warm_func = MachFunction::new("warm_fn".to_string(), Signature::new(vec![], vec![]));
        let cold_func = MachFunction::new("cold_fn".to_string(), Signature::new(vec![], vec![]));

        assert_eq!(pass.hotness().max_function_count(), 10_000);
        assert_eq!(
            pass.function_hotness(&hot_func).unwrap().class,
            HotnessClass::Hot
        );
        assert_eq!(
            pass.function_hotness(&warm_func).unwrap().class,
            HotnessClass::Warm
        );
        assert_eq!(
            pass.function_hotness(&cold_func).unwrap().class,
            HotnessClass::Cold
        );
    }

    #[test]
    fn profile_use_pass_classifies_block_hotness() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("bfs_step");
        function.call_count = 10_000;
        function.blocks.push(BlockProfile::new(0, 10_000));
        function.blocks.push(BlockProfile::new(1, 5_000));
        function.blocks.push(BlockProfile::new(2, 250));
        profile.functions.push(function);

        let pass = ProfileUsePass::new(profile);
        let func = MachFunction::new("bfs_step".to_string(), Signature::new(vec![], vec![]));

        let hot = pass.block_hotness(&func, BlockId(0)).unwrap();
        assert_eq!(hot.hits, 10_000);
        assert_eq!(hot.function_count, 10_000);
        assert_eq!(hot.class, HotnessClass::Hot);

        let warm = pass.block_hotness(&func, BlockId(1)).unwrap();
        assert_eq!(warm.hits, 5_000);
        assert_eq!(warm.class, HotnessClass::Warm);

        let cold = pass.block_hotness(&func, BlockId(2)).unwrap();
        assert_eq!(cold.hits, 250);
        assert_eq!(cold.class, HotnessClass::Cold);
    }

    #[test]
    fn profile_use_stats_summarize_hotness() {
        let mut profile = ProfData::new(0x1234);
        let mut hot = FunctionProfile::new("hot_fn");
        hot.call_count = 100;
        hot.blocks.push(BlockProfile::new(0, 100));
        hot.blocks.push(BlockProfile::new(1, 50));
        hot.blocks.push(BlockProfile::new(2, 5));

        let mut warm = FunctionProfile::new("warm_fn");
        warm.call_count = 50;
        warm.blocks.push(BlockProfile::new(0, 50));

        let mut cold = FunctionProfile::new("cold_fn");
        cold.blocks.push(BlockProfile::new(0, 0));
        profile.functions.extend([hot, warm, cold]);

        let pass = ProfileUsePass::new(profile);
        let stats = pass.stats();

        assert_eq!(stats.profiled_functions, 3);
        assert_eq!(stats.profiled_blocks, 5);
        assert_eq!(stats.hot_functions, 1);
        assert_eq!(stats.warm_functions, 1);
        assert_eq!(stats.cold_functions, 1);
        assert_eq!(stats.hot_blocks, 2);
        assert_eq!(stats.warm_blocks, 1);
        assert_eq!(stats.cold_blocks, 2);
        assert_eq!(stats.max_function_count, 100);
        assert_eq!(stats.total_function_count, 150);
        assert_eq!(stats.total_block_hits, 205);
    }

    #[test]
    fn profile_use_pass_treats_missing_profiled_block_as_cold() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("bfs_step");
        function.call_count = 10_000;
        function.blocks.push(BlockProfile::new(0, 10_000));
        profile.functions.push(function);

        let pass = ProfileUsePass::new(profile);
        let func = MachFunction::new("bfs_step".to_string(), Signature::new(vec![], vec![]));

        let missing = pass.block_hotness(&func, BlockId(99)).unwrap();
        assert_eq!(missing.block, BlockId(99));
        assert_eq!(missing.hits, 0);
        assert_eq!(missing.function_count, 10_000);
        assert_eq!(missing.class, HotnessClass::Cold);
    }

    #[test]
    fn profile_use_pass_lays_out_hot_successor_chain() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("bfs_step");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        // Never-executed guard block: the zero-hit-span gate permits chaining
        // past it (a block with ANY hits would refuse the deviation).
        function.blocks.push(BlockProfile::new(1, 0));
        function.blocks.push(BlockProfile::new(2, 90));
        function.blocks.push(BlockProfile::new(3, 100));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let mut func = explicit_diamond_func("bfs_step");

        assert_eq!(
            func.block_order,
            vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)]
        );
        assert!(pass.run(&mut func));
        assert_eq!(
            func.block_order,
            vec![BlockId(0), BlockId(2), BlockId(3), BlockId(1)]
        );
        assert!(!pass.run(&mut func), "profile layout must be idempotent");
    }

    #[test]
    fn profile_use_pass_materializes_conditional_fallthrough_before_layout() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("bfs_step");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        // Zero hits so the layout-next deviation over this block still fires
        // under the zero-hit-span chain gate.
        function.blocks.push(BlockProfile::new(1, 0));
        function.blocks.push(BlockProfile::new(2, 90));
        function.blocks.push(BlockProfile::new(3, 100));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let mut func = implicit_conditional_diamond_func("bfs_step");

        assert_eq!(
            func.block_order,
            vec![BlockId(0), BlockId(2), BlockId(1), BlockId(3)]
        );
        assert_eq!(func.block(func.entry).insts.len(), 1);
        assert!(pass.run(&mut func));
        assert_eq!(
            func.block_order,
            vec![BlockId(0), BlockId(2), BlockId(3), BlockId(1)]
        );

        let entry_insts = &func.block(func.entry).insts;
        assert_eq!(entry_insts.len(), 2);
        let fallthrough_branch = func.inst(*entry_insts.last().unwrap());
        assert_eq!(fallthrough_branch.opcode, AArch64Opcode::B);
        assert_eq!(
            fallthrough_branch.operands,
            vec![MachOperand::Block(BlockId(2))]
        );
        assert!(!pass.run(&mut func), "profile layout must be idempotent");
    }

    #[test]
    fn profile_use_pass_preserves_layout_for_cold_successors() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("bfs_step");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        function.blocks.push(BlockProfile::new(1, 5));
        function.blocks.push(BlockProfile::new(2, 0));
        function.blocks.push(BlockProfile::new(3, 100));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let mut func = explicit_diamond_func("bfs_step");

        let original = func.block_order.clone();
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order, original);
    }

    #[test]
    fn profile_use_pass_preserves_layout_for_missing_successor_profiles() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("bfs_step");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let mut func = explicit_diamond_func("bfs_step");

        let original = func.block_order.clone();
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order, original);
    }

    #[test]
    fn profile_use_pass_preserves_implicit_fallthrough_layout_without_hot_successor() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("bfs_step");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        function.blocks.push(BlockProfile::new(1, 5));
        function.blocks.push(BlockProfile::new(2, 0));
        function.blocks.push(BlockProfile::new(3, 100));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let mut func = implicit_conditional_diamond_func("bfs_step");

        let original = func.block_order.clone();
        assert_eq!(func.block(func.entry).insts.len(), 1);
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order, original);
        assert_eq!(
            func.block(func.entry).insts.len(),
            1,
            "cold profile must not materialize layout fallthroughs"
        );
    }

    #[test]
    fn profile_use_provenance_clones_materialized_fallthrough_from_conditional_branch() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("bfs_step");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        function.blocks.push(BlockProfile::new(1, 0));
        function.blocks.push(BlockProfile::new(2, 90));
        function.blocks.push(BlockProfile::new(3, 100));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let mut func = implicit_conditional_diamond_func("bfs_step");
        let source_branch = func.block(func.entry).insts[0];
        let loc = SourceLoc {
            file: 7,
            line: 42,
            col: 3,
        };
        func.inst_mut(source_branch).source_loc = Some(loc);

        let source_origin = TrustIrInstId(55);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(source_origin, &[source_branch], PassId::new("isel"));

        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        let entry_insts = &func.block(func.entry).insts;
        let materialized_branch = *entry_insts.last().unwrap();
        assert_ne!(source_branch, materialized_branch);
        assert_eq!(func.inst(materialized_branch).opcode, AArch64Opcode::B);
        assert_eq!(func.inst(materialized_branch).source_loc, Some(loc));

        let entry = provenance
            .get_entry(materialized_branch)
            .expect("materialized fallthrough branch provenance");
        assert_eq!(entry.status, ProvenanceStatus::Active);
        assert_eq!(entry.trust_ir_origins, vec![source_origin]);
        assert_eq!(
            entry.transforms.last().map(|record| &record.kind),
            Some(&TransformKind::Cloned {
                source: source_branch
            })
        );
        assert_eq!(
            provenance.get_mach_insts(source_origin),
            Some([source_branch, materialized_branch].as_slice())
        );

        let inst_count = func.insts.len();
        assert!(
            !pass.run_with_provenance(&mut func, &mut provenance),
            "profile layout must stay idempotent with provenance enabled"
        );
        assert_eq!(func.insts.len(), inst_count);
    }

    #[test]
    fn profile_use_provenance_marks_materialized_fallthrough_generated_without_source() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("bfs_step");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        function.blocks.push(BlockProfile::new(1, 0));
        function.blocks.push(BlockProfile::new(2, 90));
        function.blocks.push(BlockProfile::new(3, 100));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let mut func = implicit_conditional_diamond_func("bfs_step");
        let mut provenance = ProvenanceMap::new();

        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        let materialized_branch = *func.block(func.entry).insts.last().unwrap();
        let entry = provenance
            .get_entry(materialized_branch)
            .expect("materialized branch should be recorded");
        match &entry.status {
            ProvenanceStatus::CompilerGenerated { pass, reason } => {
                assert_eq!(pass.name(), PROFILE_USE_PASS_NAME);
                assert!(reason.contains("materialized conditional fallthrough"));
            }
            other => panic!("expected compiler-generated provenance, got {other:?}"),
        }
        assert!(entry.trust_ir_origins.is_empty());
    }

    #[test]
    fn profile_use_pass_skips_layout_dependent_fallthrough() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("fallthrough");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        function.blocks.push(BlockProfile::new(1, 10));
        function.blocks.push(BlockProfile::new(2, 90));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let mut func = MachFunction::new("fallthrough".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let cold = func.create_block();
        let hot = func.create_block();
        append_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::BCond, vec![MachOperand::Block(cold)]),
        );
        append_inst(&mut func, cold, MachInst::new(AArch64Opcode::Ret, vec![]));
        append_inst(&mut func, hot, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.add_edge(entry, cold);
        func.add_edge(entry, hot);

        let original = func.block_order.clone();
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order, original);
    }

    /// Rotated-loop shape used by the AOT PGO branch-rate consumer tests:
    /// preheader(B0) -> header(B1); header -> {body(B2), exit(B3)};
    /// body -> header (latch). The header terminates in a 2-way branch.
    fn preheader_header_latch_exit_func(name: &str) -> MachFunction {
        let mut func = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
        let pre = func.entry;
        let header = func.create_block();
        let body = func.create_block();
        let exit = func.create_block();

        append_inst(
            &mut func,
            pre,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        append_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::BCond, vec![MachOperand::Block(body)]),
        );
        append_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(exit)]),
        );
        append_inst(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        append_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(pre, header);
        func.add_edge(header, body);
        func.add_edge(header, exit);
        func.add_edge(body, header);
        func
    }

    fn loop_profile(name: &str, pre: u64, header: u64, body: u64, exit: u64) -> ProfData {
        let mut profile = ProfData::new(0x5eed);
        let mut function = FunctionProfile::new(name);
        function.call_count = pre;
        function.blocks.push(BlockProfile::new(0, pre));
        function.blocks.push(BlockProfile::new(1, header));
        function.blocks.push(BlockProfile::new(2, body));
        function.blocks.push(BlockProfile::new(3, exit));
        profile.functions.push(function);
        profile
    }

    #[test]
    fn branch_taken_rate_sole_pred_taken_edge() {
        // header hit 101 times; body (sole-pred header) 100; exit 1.
        let hotness = ProfileHotness::from_profile(&loop_profile("f", 1, 101, 100, 1));
        let func = preheader_header_latch_exit_func("f");

        let to_body = hotness
            .branch_taken_rate("f", &func, BlockId(1), BlockId(2))
            .expect("body edge resolvable");
        assert!((to_body - 100.0 / 101.0).abs() < 1e-12, "got {to_body}");

        // The exit side: exit is ALSO sole-pred-header, resolved by rule 2.
        let to_exit = hotness
            .branch_taken_rate("f", &func, BlockId(1), BlockId(3))
            .expect("exit edge resolvable");
        assert!((to_exit - 1.0 / 101.0).abs() < 1e-12, "got {to_exit}");
    }

    #[test]
    fn branch_taken_rate_other_successor_sole_pred() {
        // Give `body` a second predecessor so rule 2 fails for `body` but the
        // exit (still sole-pred-header) resolves `body` through rule 3.
        let mut func = preheader_header_latch_exit_func("f");
        let extra = func.create_block();
        append_inst(
            &mut func,
            extra,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]),
        );
        func.add_edge(extra, BlockId(2));

        let mut profile = loop_profile("f", 1, 101, 110, 1);
        profile.functions[0].blocks.push(BlockProfile::new(4, 10));
        let hotness = ProfileHotness::from_profile(&profile);

        let to_body = hotness
            .branch_taken_rate("f", &func, BlockId(1), BlockId(2))
            .expect("body edge resolvable via 1 - exit rate");
        assert!(
            (to_body - (1.0 - 1.0 / 101.0)).abs() < 1e-12,
            "got {to_body}"
        );
    }

    #[test]
    fn branch_taken_rate_kirchhoff_multi_pred() {
        // header -> {body, exit}; exit also fed by `tail` whose SOLE successor
        // is exit. body gets a second pred too, so neither rule 2 nor rule 3
        // applies to (header -> exit); Kirchhoff subtracts tail's inflow.
        let mut func = preheader_header_latch_exit_func("f");
        let tail = func.create_block(); // BlockId(4), feeds exit
        append_inst(
            &mut func,
            tail,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(3))]),
        );
        func.add_edge(tail, BlockId(3));
        let extra = func.create_block(); // BlockId(5), feeds body
        append_inst(
            &mut func,
            extra,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]),
        );
        func.add_edge(extra, BlockId(2));

        let mut profile = loop_profile("f", 1, 100, 80, 30);
        profile.functions[0].blocks.push(BlockProfile::new(4, 10)); // tail
        profile.functions[0].blocks.push(BlockProfile::new(5, 5)); // extra
        let hotness = ProfileHotness::from_profile(&profile);

        // exit hits 30, tail contributes 10 -> header->exit flow 20 of 100.
        let to_exit = hotness
            .branch_taken_rate("f", &func, BlockId(1), BlockId(3))
            .expect("exit edge resolvable via Kirchhoff");
        assert!((to_exit - 0.2).abs() < 1e-12, "got {to_exit}");
    }

    #[test]
    fn branch_taken_rate_fails_safe() {
        let func = preheader_header_latch_exit_func("f");
        let hotness = ProfileHotness::from_profile(&loop_profile("f", 1, 101, 100, 1));

        // Unprofiled function -> None.
        assert_eq!(
            hotness.branch_taken_rate("missing", &func, BlockId(1), BlockId(2)),
            None
        );
        // Zero-hit source block -> None.
        let cold = ProfileHotness::from_profile(&loop_profile("f", 1, 0, 0, 0));
        assert_eq!(
            cold.branch_taken_rate("f", &func, BlockId(1), BlockId(2)),
            None
        );
        // Block absent from the profile (e.g. minted post-canary) -> None.
        let mut partial = ProfData::new(0x5eed);
        partial.functions.push(FunctionProfile::new("f"));
        let partial = ProfileHotness::from_profile(&partial);
        assert_eq!(
            partial.branch_taken_rate("f", &func, BlockId(1), BlockId(2)),
            None
        );
        // Non-2-way source block (preheader has 1 successor) -> None.
        assert_eq!(
            hotness.branch_taken_rate("f", &func, BlockId(0), BlockId(1)),
            None
        );
        // `taken` not a successor of `block` -> None.
        assert_eq!(
            hotness.branch_taken_rate("f", &func, BlockId(1), BlockId(0)),
            None
        );
        // Unresolvable Kirchhoff (other pred with 2 successors) -> None.
        let mut func2 = preheader_header_latch_exit_func("f");
        let twoway = func2.create_block(); // BlockId(4): 2 succs, feeds exit AND body
        append_inst(
            &mut func2,
            twoway,
            MachInst::new(AArch64Opcode::BCond, vec![MachOperand::Block(BlockId(3))]),
        );
        append_inst(
            &mut func2,
            twoway,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]),
        );
        func2.add_edge(twoway, BlockId(3));
        func2.add_edge(twoway, BlockId(2));
        let mut profile2 = loop_profile("f", 1, 100, 80, 30);
        profile2.functions[0].blocks.push(BlockProfile::new(4, 10));
        let hotness2 = ProfileHotness::from_profile(&profile2);
        assert_eq!(
            hotness2.branch_taken_rate("f", &func2, BlockId(1), BlockId(3)),
            None,
            "an other-pred whose edge flow is not statically known must fail safe"
        );
    }

    #[test]
    fn profile_use_pass_skips_single_successor_implicit_fallthrough() {
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("implicit");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        function.blocks.push(BlockProfile::new(1, 1));
        function.blocks.push(BlockProfile::new(2, 90));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let mut func = MachFunction::new("implicit".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let fallthrough = func.create_block();
        let hot = func.create_block();
        append_inst(&mut func, entry, MachInst::new(AArch64Opcode::Nop, vec![]));
        append_inst(
            &mut func,
            fallthrough,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(hot)]),
        );
        append_inst(&mut func, hot, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.add_edge(entry, fallthrough);
        func.add_edge(fallthrough, hot);

        let original = func.block_order.clone();
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order, original);
    }

    /// Four-block chain-gate shape: `entry -> {hot, exit}`, `hot -> mid`,
    /// `mid -> exit`, laid out `[entry, mid, hot, exit]` so chaining
    /// `entry -> hot` must skip over `mid`. All terminators are explicit.
    fn chain_gate_func(name: &str) -> (MachFunction, BlockId, BlockId, BlockId) {
        let mut func = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let mid = func.create_block();
        let hot = func.create_block();
        let exit = func.create_block();

        append_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::BCond, vec![MachOperand::Block(exit)]),
        );
        append_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(hot)]),
        );
        append_inst(
            &mut func,
            hot,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(mid)]),
        );
        append_inst(
            &mut func,
            mid,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(exit)]),
        );
        append_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(entry, exit);
        func.add_edge(entry, hot);
        func.add_edge(hot, mid);
        func.add_edge(mid, exit);
        (func, mid, hot, exit)
    }

    #[test]
    fn profile_use_chain_gate_refuses_warm_displacement() {
        // Chaining entry -> hot would displace the WARM `mid` block sitting
        // between them in the static order (the measured Puzzle/Trial loss
        // shape). The gate must refuse and keep the static order.
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("gate_warm");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        function.blocks.push(BlockProfile::new(1, 50)); // mid: warm
        function.blocks.push(BlockProfile::new(2, 90)); // hot successor
        function.blocks.push(BlockProfile::new(3, 0));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let (mut func, _, _, _) = chain_gate_func("gate_warm");
        let original = func.block_order.clone();
        assert!(
            !pass.run(&mut func),
            "warm displacement must be refused by the chain gate"
        );
        assert_eq!(func.block_order, original);
    }

    #[test]
    fn profile_use_chain_gate_allows_zero_hit_span_sink() {
        // Same shape, but `mid` never executed: skipping it to chain
        // entry -> hot is the classic never-taken-guard sink (the measured
        // Towers/Move win shape) and must still fire.
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("gate_cold");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        function.blocks.push(BlockProfile::new(1, 0)); // mid: never executed
        function.blocks.push(BlockProfile::new(2, 90)); // hot successor
        function.blocks.push(BlockProfile::new(3, 0));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let (mut func, mid, hot, exit) = chain_gate_func("gate_cold");
        let entry = func.entry;
        assert!(pass.run(&mut func), "zero-hit-span sink must still fire");
        assert_eq!(func.block_order, vec![entry, hot, mid, exit]);
        assert!(!pass.run(&mut func), "profile layout must be idempotent");
    }

    #[test]
    fn profile_use_chain_gate_refuses_low_hit_cold_class_displacement() {
        // `mid` runs rarely relative to the function maximum (cold CLASS) but
        // is not never-executed: relative coldness is not a displacement
        // license (the measured Puzzle/Trial 3% loss came from displacing a
        // 9.7%-of-max block), so the gate must refuse.
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("gate_lowhit");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        function.blocks.push(BlockProfile::new(1, 5)); // mid: cold-class, executed
        function.blocks.push(BlockProfile::new(2, 90)); // hot successor
        function.blocks.push(BlockProfile::new(3, 0));
        profile.functions.push(function);

        let mut pass = ProfileUsePass::new(profile);
        let (mut func, _, _, _) = chain_gate_func("gate_lowhit");
        let original = func.block_order.clone();
        assert!(
            !pass.run(&mut func),
            "displacing an executed cold-class block must be refused"
        );
        assert_eq!(func.block_order, original);
    }

    #[test]
    fn profile_use_chain_gate_falls_back_to_static_next_successor() {
        // Entry's hottest successor sits past its (also-hot) static-order
        // successor: the gate refuses the displacement and chains through the
        // static-next successor instead, which here reproduces the original
        // order (no churn between two hot successors).
        let mut profile = ProfData::new(0x1234);
        let mut function = FunctionProfile::new("gate_fallback");
        function.call_count = 100;
        function.blocks.push(BlockProfile::new(0, 100));
        function.blocks.push(BlockProfile::new(1, 85)); // static-next successor: hot
        function.blocks.push(BlockProfile::new(2, 90)); // hotter successor, further away
        function.blocks.push(BlockProfile::new(3, 0));
        profile.functions.push(function);

        let mut func =
            MachFunction::new("gate_fallback".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let near = func.create_block();
        let far = func.create_block();
        let exit = func.create_block();
        append_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::BCond, vec![MachOperand::Block(far)]),
        );
        append_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(near)]),
        );
        append_inst(
            &mut func,
            near,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(far)]),
        );
        append_inst(
            &mut func,
            far,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(exit)]),
        );
        append_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.add_edge(entry, near);
        func.add_edge(entry, far);
        func.add_edge(near, far);
        func.add_edge(far, exit);

        let mut pass = ProfileUsePass::new(profile);
        let original = func.block_order.clone();
        assert!(
            !pass.run(&mut func),
            "static-next fallback must reproduce the original order here"
        );
        assert_eq!(func.block_order, original);
    }
}
