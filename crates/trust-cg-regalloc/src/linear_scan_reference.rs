// trust-cg-regalloc/linear_scan_reference.rs - the linear scan as it was
// before the L14-P6 active-set index (test oracle)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The linear scan allocator as it was before the active-set index
//! ([`crate::linear_scan::LinearScan`], ledger row L14-P6), kept verbatim
//! (renamed, with two test-only pool helpers dropped) as the oracle of the
//! differential tests in `linear_scan.rs`: the indexed allocator must return
//! the same allocation, the same spilled VRegs in the same order and the same
//! free pools on every generated input. Compiled for tests only.

#![allow(dead_code)]

use crate::linear_scan::AllocationResult;
use crate::liveness::LiveInterval;
use crate::machine_types::{PReg, RegClass, VReg};
use std::collections::BTreeMap;
use trust_cg_ir::regs::preg_class;

pub use crate::error::AllocError;

pub(crate) struct ReferenceLinearScan {
    /// All live intervals, sorted by start position.
    intervals: Vec<LiveInterval>,
    /// Indices into `intervals` of currently active (allocated) intervals,
    /// sorted by end position.
    active: Vec<usize>,
    /// Available physical registers per register class (retained for future use
    /// in interval splitting and rematerialization).
    _allocatable: BTreeMap<RegClass, Vec<PReg>>,
    /// Current allocation: VReg -> PReg.
    allocation: BTreeMap<VReg, PReg>,
    /// VRegs that need spilling.
    spills: Vec<VReg>,
    /// Free register pool per class, kept in target preference order.
    free_regs: BTreeMap<RegClass, Vec<PReg>>,
    /// Physical registers reserved at specific instruction positions by
    /// implicit defs, such as call-clobbered ABI registers.
    reserved_regs: BTreeMap<PReg, Vec<u32>>,
    /// Per candidate register, the sorted, deduplicated union of the reserved
    /// positions of every reserved key overlapping it (memoized on first use;
    /// `reserved_regs` never changes after construction). The same memo the
    /// greedy allocator keeps (`GreedyAllocator::with_reserved_points`).
    reserved_union: std::cell::RefCell<BTreeMap<PReg, Vec<u32>>>,
    /// Copy-coalescing hints: preferred physical register(s) per VReg. Biases a
    /// vreg that is copy-related to a fixed ABI register (formal-argument copies
    /// `vreg <- preg`, return / outgoing-argument copies `preg <- vreg`, call
    /// results) onto that register, so the copy becomes an identity move that
    /// `post_ra_coalesce` deletes — closing the redundant arg/return `mov` gap
    /// vs LLVM. Preference ONLY: the interference checks in `try_alloc_free_reg`
    /// and the post-allocation translation validator still gate correctness.
    hints: BTreeMap<VReg, Vec<PReg>>,
    /// Per `(vreg, hinted register)` instruction positions to EXEMPT from the
    /// reserved-register interference check: only the copy points that relate
    /// that exact pair. Keying by vreg alone lets a value copied to several ABI
    /// registers borrow X1's copy-point exemption while considering X0, which
    /// can admit an allocation the translation validator correctly rejects.
    hint_exempt: BTreeMap<(VReg, PReg), Vec<u32>>,
}

impl ReferenceLinearScan {
    /// Create a new linear scan allocator.
    ///
    /// `intervals`: computed live intervals for the function.
    /// `target_regs`: allocatable physical registers, organized by class.
    pub fn new(intervals: Vec<LiveInterval>, target_regs: &BTreeMap<RegClass, Vec<PReg>>) -> Self {
        Self::new_with_reserved(intervals, target_regs, BTreeMap::new())
    }

    pub fn new_with_reserved(
        mut intervals: Vec<LiveInterval>,
        target_regs: &BTreeMap<RegClass, Vec<PReg>>,
        reserved_regs: BTreeMap<PReg, Vec<u32>>,
    ) -> Self {
        // Sort intervals by start position (ascending).
        intervals.sort_by_key(|i| i.start());

        let free_regs = target_regs.clone();

        Self {
            intervals,
            active: Vec::new(),
            _allocatable: target_regs.clone(),
            allocation: BTreeMap::new(),
            spills: Vec::new(),
            free_regs,
            reserved_regs,
            reserved_union: std::cell::RefCell::new(BTreeMap::new()),
            hints: BTreeMap::new(),
            hint_exempt: BTreeMap::new(),
        }
    }

    /// Supply copy-coalescing register hints (see the `hints` field) and the
    /// per-`(vreg, preg)` copy-point positions to exempt from reserved
    /// interference (see `hint_exempt`). Preference only; safe to call with any
    /// maps, including ones keyed by vregs that end up spilled.
    pub fn set_hints(
        &mut self,
        hints: BTreeMap<VReg, Vec<PReg>>,
        hint_exempt: BTreeMap<(VReg, PReg), Vec<u32>>,
    ) {
        self.hints = hints;
        self.hint_exempt = hint_exempt;
    }

    /// Run the linear scan allocation algorithm.
    pub fn allocate(&mut self) -> Result<AllocationResult, AllocError> {
        for i in 0..self.intervals.len() {
            let start = self.intervals[i].start();

            // Step 1: Expire old intervals.
            self.expire_old_intervals(start);

            // Step 2: Skip fixed intervals (already allocated).
            if self.intervals[i].is_fixed {
                continue;
            }

            let class = self.intervals[i].vreg.class;

            // Step 3: Try to allocate a free register.
            if let Some(preg) = self.try_alloc_free_reg(i, class) {
                self.allocation.insert(self.intervals[i].vreg, preg);
                // Remove aliasing registers from their respective free pools.
                // (Issue #336: mixed-width ABI register aliasing.)
                self.remove_aliases_from_free_pools(preg);
                self.insert_active(i);
            } else {
                // Step 4: No free register — spill something.
                self.allocate_blocked_reg(i)?;
            }
        }

        Ok(AllocationResult {
            allocation: self.allocation.clone(),
            spills: Vec::new(), // Spill info filled in by insert_spill_code
        })
    }

    /// Expire active intervals that end before `pos`.
    fn expire_old_intervals(&mut self, pos: u32) {
        let mut expired = Vec::new();
        // Collect expired intervals and their freed registers.
        let mut freed_pregs: Vec<(RegClass, PReg)> = Vec::new();

        for (active_idx, &interval_idx) in self.active.iter().enumerate() {
            if self.intervals[interval_idx].end() <= pos {
                expired.push(active_idx);
                // Collect the register to return to the free pool.
                let vreg = self.intervals[interval_idx].vreg;
                if let Some(&preg) = self.allocation.get(&vreg) {
                    freed_pregs.push((vreg.class, preg));
                }
            }
        }

        // Remove expired entries in reverse order to preserve indices.
        for idx in expired.into_iter().rev() {
            self.active.remove(idx);
        }

        // Return freed registers and their aliases to free pools after removing
        // expired intervals so remaining active aliases still block reuse.
        for (_class, preg) in freed_pregs {
            self.return_preg_and_aliases_to_free_pools(preg);
        }
    }

    /// Try to allocate a free register from the given class.
    fn try_alloc_free_reg(&mut self, interval_idx: usize, class: RegClass) -> Option<PReg> {
        // Prefer a hinted register when it is free and non-interfering. This
        // biases arg/return/call-boundary copy vregs onto their ABI register so
        // the copy becomes an identity move `post_ra_coalesce` removes. It is a
        // strict subset of the normal candidates (same reserved/active checks),
        // so it can never produce an allocation the plain scan wouldn't accept —
        // it only reorders the preference. Falls back to the pool scan.
        let vreg = self.intervals[interval_idx].vreg;
        let hinted: Vec<PReg> = self
            .hints
            .get(&vreg)
            .map(|h| {
                h.iter()
                    .copied()
                    .filter(|&p| preg_class(p) == class)
                    .collect()
            })
            .unwrap_or_default();
        for hint in hinted {
            let exempt = self
                .hint_exempt
                .get(&(vreg, hint))
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            let free_pos = self
                .free_regs
                .get(&class)
                .and_then(|pool| pool.iter().position(|&p| p == hint));
            if let Some(pos) = free_pos
                && !self.reserved_interferes_except(interval_idx, hint, exempt)
                && !self.active_allocation_overlaps(hint)
            {
                return Some(self.free_regs.get_mut(&class)?.remove(pos));
            }
        }

        let pool = self.free_regs.get(&class)?;
        let pos = pool.iter().position(|&preg| {
            !self.reserved_interferes(interval_idx, preg) && !self.active_allocation_overlaps(preg)
        })?;
        Some(self.free_regs.get_mut(&class)?.remove(pos))
    }

    fn reserved_interferes(&self, interval_idx: usize, preg: PReg) -> bool {
        self.reserved_interferes_except(interval_idx, preg, &[])
    }

    /// Like [`Self::reserved_interferes`], but ignoring reservations at the
    /// `exempt` positions — the copy points where `preg` is defined by the very
    /// copy that biases this interval toward it (kill-then-def boundary; see
    /// `hint_exempt`). Only used when honoring a hint, and it can only ever
    /// REMOVE interference at those specific positions, never add any.
    ///
    /// The existential "some reserved position of a key overlapping `preg` is
    /// live in the interval and not exempt" is searched from the RANGE side
    /// over the memoized sorted union of those positions: the positions inside
    /// one half-open range `[start, end)` are a contiguous slice found by two
    /// binary searches. `is_live_at(pos)` is exactly "some range contains
    /// `pos`", so this is the same existential over the same set as scanning
    /// every key's positions with `is_live_at` (the form this replaced, which
    /// cost one binary search per reserved position per candidate register);
    /// evaluation order is immaterial. Identical to the greedy allocator's
    /// `reserved_interferes_except`.
    fn reserved_interferes_except(&self, interval_idx: usize, preg: PReg, exempt: &[u32]) -> bool {
        let interval = &self.intervals[interval_idx];
        self.with_reserved_points(preg, |pts| {
            interval.ranges.iter().any(|r| {
                let lo = pts.partition_point(|&p| p < r.start);
                let hi = pts.partition_point(|&p| p < r.end);
                // One unit per range plus the positions inside it (L14-P6
                // cost-growth test; nothing outside `cfg(test)`).
                crate::scan_work::charge(1 + (hi - lo));
                pts[lo..hi].iter().any(|pos| !exempt.contains(pos))
            })
        })
    }

    /// Run `f` over the sorted union of reserved positions of every reserved
    /// key overlapping `preg` (memoized per candidate; see `reserved_union`).
    fn with_reserved_points<R>(&self, preg: PReg, f: impl FnOnce(&[u32]) -> R) -> R {
        if let Some(pts) = self.reserved_union.borrow().get(&preg) {
            return f(pts);
        }
        let mut pts: Vec<u32> = Vec::new();
        for (&reserved_preg, points) in &self.reserved_regs {
            if crate::greedy::allocator_pregs_overlap(reserved_preg, preg) {
                crate::scan_work::charge(points.len());
                pts.extend_from_slice(points);
            }
        }
        pts.sort_unstable();
        pts.dedup();
        let r = f(&pts);
        self.reserved_union.borrow_mut().insert(preg, pts);
        r
    }

    /// Remove aliasing registers from their respective free pools when a
    /// register is allocated.
    ///
    /// On AArch64, allocating X28 means W28 is no longer free (and vice versa).
    /// (Issue #336: mixed-width ABI register aliasing.)
    fn remove_aliases_from_free_pools(&mut self, preg: PReg) {
        use crate::greedy::aliasing_pregs;
        for alias in aliasing_pregs(preg) {
            let alias_class = preg_class(alias);
            if let Some(pool) = self.free_regs.get_mut(&alias_class) {
                pool.retain(|&p| p != alias);
            }
        }
    }

    /// Return a freed register and its aliases to free pools when no remaining
    /// active allocation overlaps them.
    ///
    /// (Issue #336: mixed-width ABI register aliasing.)
    fn return_preg_and_aliases_to_free_pools(&mut self, preg: PReg) {
        use crate::greedy::aliasing_pregs;
        self.return_preg_to_free_pool_if_unowned(preg);
        for alias in aliasing_pregs(preg) {
            self.return_preg_to_free_pool_if_unowned(alias);
        }
    }

    fn return_preg_to_free_pool_if_unowned(&mut self, preg: PReg) {
        if self.active_allocation_overlaps(preg) {
            return;
        }

        let class = preg_class(preg);
        if !self
            ._allocatable
            .get(&class)
            .is_some_and(|regs| regs.contains(&preg))
        {
            return;
        }

        let Some(allocatable) = self._allocatable.get(&class) else {
            return;
        };
        let Some(preferred_idx) = allocatable.iter().position(|&p| p == preg) else {
            return;
        };

        if let Some(pool) = self.free_regs.get_mut(&class) {
            if pool.contains(&preg) {
                return;
            }

            let insert_pos = pool
                .iter()
                .position(|&existing| {
                    allocatable
                        .iter()
                        .position(|&p| p == existing)
                        .is_none_or(|idx| idx > preferred_idx)
                })
                .unwrap_or(pool.len());
            pool.insert(insert_pos, preg);
        }
    }

    fn active_allocation_overlaps(&self, preg: PReg) -> bool {
        self.active_allocation_overlaps_except(preg, usize::MAX)
    }

    fn active_allocation_overlaps_except(&self, preg: PReg, except_interval_idx: usize) -> bool {
        self.active.iter().any(|&interval_idx| {
            if interval_idx == except_interval_idx {
                return false;
            }
            let vreg = self.intervals[interval_idx].vreg;
            self.allocation.get(&vreg).is_some_and(|&active_preg| {
                crate::greedy::allocator_pregs_overlap(active_preg, preg)
            })
        })
    }

    /// Handle the case where no free register is available.
    ///
    /// Spill the interval (current or active) with the lowest spill weight.
    fn allocate_blocked_reg(&mut self, current_idx: usize) -> Result<(), AllocError> {
        let current_weight = self.intervals[current_idx].spill_weight;

        match self.blocked_spill_candidate(current_idx) {
            Some((spill_idx, preg, spill_weight)) if spill_weight < current_weight => {
                // Spill the active interval and give its register to current.
                let spill_vreg = self.intervals[spill_idx].vreg;
                self.allocation.remove(&spill_vreg).ok_or_else(|| {
                    AllocError::Failed(format!("active interval {} has no allocation", spill_vreg))
                })?;

                self.spills.push(spill_vreg);
                self.allocation
                    .insert(self.intervals[current_idx].vreg, preg);
                self.remove_aliases_from_free_pools(preg);

                // Remove spilled interval from active.
                self.active.retain(|&idx| idx != spill_idx);
                self.insert_active(current_idx);

                Ok(())
            }
            _ => {
                // Spill the current interval.
                self.spills.push(self.intervals[current_idx].vreg);
                Ok(())
            }
        }
    }

    fn blocked_spill_candidate(&self, current_idx: usize) -> Option<(usize, PReg, f64)> {
        let current_class = self.intervals[current_idx].vreg.class;
        let allocatable = self._allocatable.get(&current_class)?;
        let mut best: Option<(usize, PReg, f64)> = None;

        for &candidate_preg in allocatable {
            if self.reserved_interferes(current_idx, candidate_preg) {
                continue;
            }

            for &active_interval_idx in &self.active {
                let active_interval = &self.intervals[active_interval_idx];
                if active_interval.is_fixed {
                    continue;
                }

                let Some(&active_preg) = self.allocation.get(&active_interval.vreg) else {
                    continue;
                };
                if !crate::greedy::allocator_pregs_overlap(active_preg, candidate_preg) {
                    continue;
                }
                if self.active_allocation_overlaps_except(candidate_preg, active_interval_idx) {
                    continue;
                }

                let active_weight = active_interval.spill_weight;
                if best.is_none_or(|(_, _, best_weight)| active_weight < best_weight) {
                    best = Some((active_interval_idx, candidate_preg, active_weight));
                }
            }
        }

        best
    }

    /// Insert an interval index into the active list, maintaining sort by end position.
    fn insert_active(&mut self, interval_idx: usize) {
        let end = self.intervals[interval_idx].end();
        let pos = self
            .active
            .iter()
            .position(|&idx| self.intervals[idx].end() > end)
            .unwrap_or(self.active.len());
        self.active.insert(pos, interval_idx);
    }

    /// Returns the list of VRegs that were spilled during allocation.
    pub fn spilled_vregs(&self) -> &[VReg] {
        &self.spills
    }

    /// The free pools, per class (added for the differential).
    pub(crate) fn free_pools(&self) -> &BTreeMap<RegClass, Vec<PReg>> {
        &self.free_regs
    }
}
