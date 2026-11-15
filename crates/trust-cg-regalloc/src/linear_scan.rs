// trust-cg-regalloc/linear_scan.rs - Linear scan register allocator
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Linear scan register allocator.
//!
//! Assigns physical registers to virtual registers by processing live
//! intervals sorted by start position. When no register is available,
//! the interval with the lowest spill weight is spilled.
//!
//! Reference: Poletto & Sarkar, "Linear Scan Register Allocation" (1999)
//! LLVM reference: `~/llvm-project-ref/llvm/lib/CodeGen/RegAllocGreedy.cpp`
//!
//! Linear scan does not split intervals here. It honors register hints and
//! physical-register reservations; the surrounding allocation pipeline owns
//! rematerialization and the greedy strategy's splitting policy.

use crate::liveness::LiveInterval;
use crate::machine_types::{PReg, RegClass, StackSlotId, VReg};
use std::collections::BTreeMap;
use trust_cg_ir::regs::preg_class;

// Preserve the existing module path while all phases share one error type.
pub use crate::error::AllocError;

/// Result of register allocation.
#[derive(Debug, Clone)]
pub struct AllocationResult {
    /// VReg -> PReg assignment for successfully allocated registers.
    pub allocation: BTreeMap<VReg, PReg>,
    /// VRegs that were spilled, with their assigned stack slots.
    pub spills: Vec<SpillInfo>,
}

/// Information about a spilled virtual register.
#[derive(Debug, Clone)]
pub struct SpillInfo {
    /// The spilled virtual register.
    pub vreg: VReg,
    /// The stack slot assigned for this spill.
    pub slot: StackSlotId,
}

/// Linear scan register allocator.
///
/// The algorithm processes intervals sorted by start position:
/// 1. For each interval starting at position `pos`:
///    a. Expire any active intervals that end before `pos`.
///    b. Try to find a free register from the allocatable set.
///    c. If no free register, spill the active interval with the lowest
///    spill weight (or the current interval if it's cheaper).
///
/// Reference: LLVM's RegAllocLinearScan (removed in favor of Greedy,
/// but the core algorithm is a useful starting point).
pub struct LinearScan {
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
    /// Per vreg, call positions where the call reads it for the last time
    /// (see [`Self::set_call_operand_exempt`]). Empty by default.
    call_operand_exempt: BTreeMap<VReg, Vec<u32>>,
    /// The registers the active intervals hold ([`ActiveHolders`]), or `None`
    /// when two intervals share a VReg, where the literal scans of `active`
    /// and `allocation` run instead.
    holders: Option<ActiveHolders>,
    /// Per class, each allocatable register's first position in its target
    /// list: the preference order the free pools are kept in. Built for a
    /// class the first time a register of it returns to its pool.
    preference_rank: BTreeMap<RegClass, BTreeMap<PReg, usize>>,
}

/// Which registers the active intervals hold (ledger row L14-P6).
///
/// For every candidate register of every interval, the allocation loop asks
/// whether some active interval holds a register overlapping it, and the
/// eviction search asks, per candidate, which active intervals do. The literal
/// answers walk the active set and look each entry's VReg up in the
/// allocation map, so the eviction search cost `O(registers * active)` map
/// lookups per blocked interval, and each of those lookups grows with the
/// function. On one long block of spilled values (the stack-tuple block of the
/// L14-P6 report: 3,303 spills at 2,000 store/load pairs, 14,542 at 8,000)
/// `LinearScan::allocate` was the top self-time frame and its stage grew 5.2x
/// per 4x step.
///
/// When every interval has its own VReg, an active interval's register is
/// `allocation[vreg]` for as long as it is active: it is inserted just before
/// the interval enters the active set, and removed only when the interval is
/// evicted from it. So the holdings are recorded here as intervals enter and
/// leave the set, and a question about a register reads the holdings of the
/// registers overlapping it (memoized per register over every register an
/// allocation can hold) instead of walking the set. The answers, and so the
/// allocation, are the literal ones (the differential
/// `indexed_linear_scan_matches_the_reference_allocator`).
struct ActiveHolders {
    /// The register each interval holds while it is active, by index into
    /// `LinearScan::intervals`.
    held: Vec<Option<PReg>>,
    /// Each register some active interval holds, with those intervals in the
    /// order they took it.
    by_register: BTreeMap<PReg, Vec<usize>>,
    /// Every register an allocation can hold: the union of the target's
    /// allocatable lists. `try_alloc_free_reg` takes only from the free
    /// pools, which only ever hold allocatable registers, and an eviction
    /// assigns only an allocatable candidate. Collected on first use (most
    /// functions never hold more than [`DIRECT_HOLDINGS_SCAN`] registers).
    universe: std::cell::OnceCell<Vec<PReg>>,
    /// Per queried register `q`, the registers `p` of `universe` with
    /// `allocator_pregs_overlap(p, q)`, built on first use.
    overlapping_registers: std::cell::RefCell<BTreeMap<PReg, Vec<PReg>>>,
}

/// At most this many held registers are compared one by one; above it a
/// question reads the memoized overlap list of its register. Both give the
/// same answer; the list costs one pass over `universe` to build, which a
/// small function would not recover.
const DIRECT_HOLDINGS_SCAN: usize = 6;

impl ActiveHolders {
    fn new(intervals: usize) -> Self {
        Self {
            held: vec![None; intervals],
            by_register: BTreeMap::new(),
            universe: std::cell::OnceCell::new(),
            overlapping_registers: std::cell::RefCell::new(BTreeMap::new()),
        }
    }

    fn hold(&mut self, interval_idx: usize, preg: PReg) {
        if let Some(slot) = self.held.get_mut(interval_idx) {
            *slot = Some(preg);
        }
        self.by_register.entry(preg).or_default().push(interval_idx);
    }

    fn release(&mut self, interval_idx: usize) {
        let Some(preg) = self.held.get_mut(interval_idx).and_then(Option::take) else {
            return;
        };
        if let Some(holders) = self.by_register.get_mut(&preg) {
            holders.retain(|&holder| holder != interval_idx);
            if holders.is_empty() {
                self.by_register.remove(&preg);
            }
        }
    }

    /// Build the memoized list of the registers of `universe` (the union of
    /// `allocatable`) overlapping `preg`, if it is not built yet.
    fn build_overlap_list(&self, preg: PReg, allocatable: &BTreeMap<RegClass, Vec<PReg>>) {
        if self.overlapping_registers.borrow().contains_key(&preg) {
            return;
        }
        let universe = self.universe.get_or_init(|| {
            let mut universe: Vec<PReg> = allocatable.values().flatten().copied().collect();
            universe.sort_unstable();
            universe.dedup();
            universe
        });
        crate::scan_work::charge(universe.len());
        let list: Vec<PReg> = universe
            .iter()
            .copied()
            .filter(|&held| crate::greedy::allocator_pregs_overlap(held, preg))
            .collect();
        self.overlapping_registers.borrow_mut().insert(preg, list);
    }

    /// Every active interval holding a register overlapping `preg`, in no
    /// particular order, passed to `visit` until it returns `false`.
    fn for_each_overlapping(
        &self,
        preg: PReg,
        allocatable: &BTreeMap<RegClass, Vec<PReg>>,
        mut visit: impl FnMut(usize) -> bool,
    ) {
        if self.by_register.len() <= DIRECT_HOLDINGS_SCAN {
            crate::scan_work::charge(self.by_register.len());
            for (&held, holders) in &self.by_register {
                if crate::greedy::allocator_pregs_overlap(held, preg) {
                    for &holder in holders {
                        if !visit(holder) {
                            return;
                        }
                    }
                }
            }
            return;
        }
        self.build_overlap_list(preg, allocatable);
        let lists = self.overlapping_registers.borrow();
        let Some(list) = lists.get(&preg) else {
            return;
        };
        crate::scan_work::charge(list.len());
        for held in list {
            for &holder in self.by_register.get(held).into_iter().flatten() {
                if !visit(holder) {
                    return;
                }
            }
        }
    }

    /// How many active intervals hold a register overlapping `preg`, counting
    /// no further than `limit`.
    fn overlapping(
        &self,
        preg: PReg,
        limit: usize,
        allocatable: &BTreeMap<RegClass, Vec<PReg>>,
    ) -> usize {
        let mut count = 0;
        self.for_each_overlapping(preg, allocatable, |_| {
            count += 1;
            count < limit
        });
        count
    }
}

impl LinearScan {
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
        let distinct_vregs = {
            let mut vregs: Vec<VReg> = intervals.iter().map(|interval| interval.vreg).collect();
            vregs.sort_unstable();
            vregs.windows(2).all(|pair| pair[0] != pair[1])
        };
        let holders = distinct_vregs.then(|| ActiveHolders::new(intervals.len()));

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
            call_operand_exempt: BTreeMap::new(),
            holders,
            preference_rank: BTreeMap::new(),
        }
    }

    /// The same allocator without [`ActiveHolders`]: every overlap question
    /// walks the active set (the literal scans), as a repeated VReg forces.
    #[cfg(test)]
    fn without_holders(mut self) -> Self {
        self.holders = None;
        self
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

    /// Supply, per vreg, the call positions at which it is read as the call's
    /// own operand for the last time (`crate::dying_call_operand_positions`):
    /// the call reads it before its clobbers take effect, so a caller-saved
    /// register reserved only by that call's clobber at that position does not
    /// interfere. Any register, hinted or not.
    pub fn set_call_operand_exempt(&mut self, exempt: BTreeMap<VReg, Vec<u32>>) {
        self.call_operand_exempt = exempt;
    }

    /// The dying-call-operand positions of this interval that are still its
    /// last point (`end == position + 1`), re-checked against the interval
    /// being allocated rather than trusted from the map.
    fn call_operand_exempt_for(&self, interval_idx: usize) -> Vec<u32> {
        let interval = &self.intervals[interval_idx];
        self.call_operand_exempt
            .get(&interval.vreg)
            .map(|positions| {
                positions
                    .iter()
                    .copied()
                    .filter(|&p| interval.end() == p + 1)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Run the linear scan allocation algorithm.
    pub fn allocate(&mut self) -> Result<AllocationResult, AllocError> {
        // Reuse retains the previous active/allocation state. An interval can
        // enter the active set again with a different register, so answer
        // overlap questions from the allocation map on these later calls.
        if !self.active.is_empty() {
            self.holders = None;
        }
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
            let interval_idx = self.active.remove(idx);
            if let Some(holders) = &mut self.holders {
                holders.release(interval_idx);
            }
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
        let call_exempt = self.call_operand_exempt_for(interval_idx);
        for hint in hinted {
            let mut exempt = self
                .hint_exempt
                .get(&(vreg, hint))
                .cloned()
                .unwrap_or_default();
            exempt.extend_from_slice(&call_exempt);
            let free_pos = self
                .free_regs
                .get(&class)
                .and_then(|pool| pool.iter().position(|&p| p == hint));
            if let Some(pos) = free_pos
                && !self.reserved_interferes_except(interval_idx, hint, &exempt)
                && !self.active_allocation_overlaps(hint)
            {
                return Some(self.free_regs.get_mut(&class)?.remove(pos));
            }
        }

        let pool = self.free_regs.get(&class)?;
        let pos = pool.iter().position(|&preg| {
            !self.reserved_interferes_except(interval_idx, preg, &call_exempt)
                && !self.active_allocation_overlaps(preg)
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

        // `preference_rank` holds each allocatable register's first position
        // in its class's target list, so this is the target-list search the
        // pool order is defined by, without a scan per pool entry.
        let class = preg_class(preg);
        let Some(allocatable) = self._allocatable.get(&class) else {
            return;
        };
        let ranks = self.preference_rank.entry(class).or_insert_with(|| {
            let mut ranks = BTreeMap::new();
            for (rank, &allocatable_preg) in allocatable.iter().enumerate() {
                ranks.entry(allocatable_preg).or_insert(rank);
            }
            ranks
        });
        let Some(&preferred_idx) = ranks.get(&preg) else {
            return;
        };

        if let Some(pool) = self.free_regs.get_mut(&class) {
            if pool.contains(&preg) {
                return;
            }

            let insert_pos = pool
                .iter()
                .position(|existing| ranks.get(existing).is_none_or(|&idx| idx > preferred_idx))
                .unwrap_or(pool.len());
            pool.insert(insert_pos, preg);
        }
    }

    fn active_allocation_overlaps(&self, preg: PReg) -> bool {
        self.active_allocation_overlaps_except(preg, usize::MAX)
    }

    fn active_allocation_overlaps_except(&self, preg: PReg, except_interval_idx: usize) -> bool {
        if let Some(holders) = &self.holders {
            let mut other = false;
            holders.for_each_overlapping(preg, &self._allocatable, |holder| {
                other = holder != except_interval_idx;
                !other
            });
            return other;
        }
        crate::scan_work::charge(self.active.len());
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

    #[cfg(test)]
    fn free_pool_contains(&self, preg: PReg) -> bool {
        let class = preg_class(preg);
        self.free_regs
            .get(&class)
            .is_some_and(|pool| pool.contains(&preg))
    }

    #[cfg(test)]
    fn free_pool_duplicate_count(&self, preg: PReg) -> usize {
        let class = preg_class(preg);
        self.free_regs
            .get(&class)
            .map(|pool| pool.iter().filter(|&&p| p == preg).count())
            .unwrap_or(0)
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
                if let Some(holders) = &mut self.holders {
                    holders.release(spill_idx);
                }
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

            if let Some(holders) = &self.holders {
                // The literal loop below considers an active interval only when
                // it holds a register overlapping the candidate and no OTHER
                // active interval does. So it considers one exactly when a
                // single active interval overlaps the candidate, and then that
                // one; with none, or with two or more, it considers nothing.
                let mut sole = None;
                if holders.overlapping(candidate_preg, 2, &self._allocatable) == 1 {
                    holders.for_each_overlapping(candidate_preg, &self._allocatable, |holder| {
                        sole = Some(holder);
                        false
                    });
                }
                if let Some(active_interval_idx) = sole
                    && !self.intervals[active_interval_idx].is_fixed
                {
                    let active_weight = self.intervals[active_interval_idx].spill_weight;
                    if best.is_none_or(|(_, _, best_weight)| active_weight < best_weight) {
                        best = Some((active_interval_idx, candidate_preg, active_weight));
                    }
                }
                continue;
            }

            crate::scan_work::charge(self.active.len());
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
        // Both callers insert the interval's allocation just before this.
        if let Some(holders) = &mut self.holders
            && let Some(&preg) = self.allocation.get(&self.intervals[interval_idx].vreg)
        {
            holders.hold(interval_idx, preg);
        }
    }

    /// The free pools, per class, in preference order.
    #[cfg(test)]
    fn free_pools(&self) -> &BTreeMap<RegClass, Vec<PReg>> {
        &self.free_regs
    }

    /// Make `active` the active set, holding the registers `allocation`
    /// already gives its intervals (for tests that set up a mid-allocation
    /// state by hand).
    #[cfg(test)]
    fn set_active(&mut self, active: Vec<usize>) {
        for &interval_idx in &self.active {
            if let Some(holders) = &mut self.holders {
                holders.release(interval_idx);
            }
        }
        self.active = active;
        for &interval_idx in &self.active {
            if let Some(holders) = &mut self.holders
                && let Some(&preg) = self.allocation.get(&self.intervals[interval_idx].vreg)
            {
                holders.hold(interval_idx, preg);
            }
        }
    }

    /// Returns the list of VRegs that were spilled during allocation.
    pub fn spilled_vregs(&self) -> &[VReg] {
        &self.spills
    }
}

/// Returns the default allocatable registers for AArch64 (Apple calling convention).
///
/// Caller-saved: X0-X7, X9-X15 (X8 is the indirect-result register, see below;
/// X18 is reserved on Apple).
/// Callee-saved: X19-X28.
/// X29 = FP, X30 = LR, X31 = SP/ZR — not allocatable.
///
/// FAIL-CLOSED ABI INVARIANT: X8 (and its W8 alias) is the AAPCS64 INDIRECT
/// RESULT LOCATION register. For a function returning an aggregate by memory,
/// the caller passes the destination pointer in X8, and ISel lowers the return
/// copy as a store through the *physical* register — `str vN, [X8, #imm]` —
/// with no entry `vX = copy X8` to give the pointer a virtual live range. X8 is
/// therefore live from function entry to the last of those stores, but that
/// lifetime is invisible to interval construction: `reserve_incoming_argument_-
/// spans` only sees live-in reads that occur in the ENTRY block, and these
/// stores sit in the return block. With X8 in the pool the allocator sees it as
/// free and, under enough pressure, colors an unrelated vreg to it (`add x8,
/// x0, #28`), destroying the incoming sret pointer; the return stores then write
/// through the clobbered pointer and the real return buffer is never written, so
/// the caller reads uninitialized stack — a wrong answer that varies run to run.
/// This is exactly why the canonical [`trust_cg_ir::aarch64_regs::ALLOCATABLE_-
/// GPRS`] excludes X8; this pool must agree with it (see the pool-agreement
/// test below). Keeping X8 out of the pool costs one scratch register and makes
/// the class unreachable rather than relying on the allocator never running out.
pub fn aarch64_allocatable_regs() -> BTreeMap<RegClass, Vec<PReg>> {
    let mut regs = BTreeMap::new();

    // GPR64: X0-X7, X9-X15, X19-X28
    // (skip X8 indirect-result, X16-X17 scratch, X18 reserved, X29 FP, X30 LR)
    // PReg encoding: X registers are 0..=30
    let gpr64: Vec<PReg> = (0u16..=7)
        .chain(9u16..=15)
        .chain(19u16..=28)
        .map(PReg::new)
        .collect();
    regs.insert(RegClass::Gpr64, gpr64.clone());

    // GPR32: same set (W registers are the lower 32 bits of X registers), so W8
    // is excluded for the same reason X8 is — it is the same architectural
    // register and writing W8 zero-extends over the whole sret pointer.
    // PReg encoding: W registers are 32..=62
    let gpr32: Vec<PReg> = (32u16..=39)
        .chain(41u16..=47)
        .chain(51u16..=60)
        .map(PReg::new)
        .collect();
    regs.insert(RegClass::Gpr32, gpr32);

    // FPR scratch aliases V16/V17, D16/D17, S16/S17, and H16/H17 are
    // reserved for post-allocation spill materialization.
    // FPR128: V0-V7, V18-V31 (encoded as 64-71, 82-95).
    //
    // FAIL-CLOSED ABI INVARIANT: V8-V15 (enc 72-79) are intentionally EXCLUDED
    // from the 128-bit pool. AAPCS64 preserves only the LOWER 64 bits of V8-V15
    // across a call; the upper 64 are caller-clobbered, and the frame save path
    // (lower64_fpr_alias -> D8..D15 STP/LDP) stores only those lower 64. So a
    // 128-bit value placed in V8-V15 and live across a call would lose its
    // upper 64 bits — a miscompile. By dropping V8-V15 from the Fpr128 pool, any
    // Fpr128 value can only land in V0-V7/V16-V31 (all fully caller-clobbered, so
    // the call-clobber reservations force a full-width 16-byte save/restore
    // around the call) — never in a partially-preserved register. The Fpr64
    // (D8-D15), Fpr32 (S8-S15), and Fpr16 (H8-H15) aliases below STAY allocatable
    // and sound: their entire value IS the lower 64 bits the D-register save
    // preserves.
    let fpr128: Vec<PReg> = (64u16..=71).chain(82u16..=95).map(PReg::new).collect();
    regs.insert(RegClass::Fpr128, fpr128);

    // FPR64: D0-D15, D18-D31 (encoded as 96-127).
    let fpr64: Vec<PReg> = (96u16..=111).chain(114u16..=127).map(PReg::new).collect();
    regs.insert(RegClass::Fpr64, fpr64);

    // FPR32: S0-S15, S18-S31 (encoded as 128-159).
    let fpr32: Vec<PReg> = (128u16..=143).chain(146u16..=159).map(PReg::new).collect();
    regs.insert(RegClass::Fpr32, fpr32);

    // FPR16: H0-H15, H18-H31 (encoded as 165-196).
    let fpr16: Vec<PReg> = (165u16..=180).chain(183u16..=196).map(PReg::new).collect();
    regs.insert(RegClass::Fpr16, fpr16);

    regs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_aarch64_allocatable_regs() {
        let regs = aarch64_allocatable_regs();
        // 25 GPRs: X0-X7 (8) + X9-X15 (7) + X19-X28 (10) = 25.
        // X8 is the AAPCS64 indirect-result register and is NOT allocatable.
        assert_eq!(regs[&RegClass::Gpr64].len(), 25);
        // 30 FPR64 regs: D16/D17 are reserved spill scratches.
        assert_eq!(regs[&RegClass::Fpr64].len(), 30);
        assert!(!regs[&RegClass::Fpr64].contains(&PReg::new(112)));
        assert!(!regs[&RegClass::Fpr64].contains(&PReg::new(113)));
    }

    /// The GPR pool must agree with the canonical AAPCS64 register-class list in
    /// `trust-cg-ir`. The two drifted once: `ALLOCATABLE_GPRS` correctly omitted
    /// X8 (indirect result location) while this pool still contained X8/W8, so
    /// the allocator colored ordinary vregs to the incoming sret pointer under
    /// register pressure and the aggregate return value was written through a
    /// clobbered pointer — a nondeterministic wrong answer, because the real
    /// return buffer was left holding whatever the stack happened to contain.
    #[test]
    fn test_gpr_pool_matches_canonical_aapcs64_allocatable_set() {
        use trust_cg_ir::aarch64_regs::{ALLOCATABLE_GPRS, W8, X8};

        let regs = aarch64_allocatable_regs();
        let gpr64 = &regs[&RegClass::Gpr64];
        let gpr32 = &regs[&RegClass::Gpr32];

        // X8 / W8 are the same architectural register; neither may be handed out.
        assert!(
            !gpr64.contains(&PReg::new(X8.encoding())),
            "X8 (indirect result location) must not be allocatable"
        );
        assert!(
            !gpr32.contains(&PReg::new(W8.encoding())),
            "W8 (alias of the indirect result location) must not be allocatable"
        );

        // The 64-bit pool must be exactly the canonical list.
        let canonical: Vec<u16> = {
            let mut v: Vec<u16> = ALLOCATABLE_GPRS.iter().map(|p| p.encoding()).collect();
            v.sort_unstable();
            v
        };
        let pool: Vec<u16> = {
            let mut v: Vec<u16> = gpr64.iter().map(|p| p.encoding()).collect();
            v.sort_unstable();
            v
        };
        assert_eq!(
            pool, canonical,
            "linear_scan GPR64 pool drifted from trust_cg_ir::ALLOCATABLE_GPRS"
        );

        // The 32-bit pool is the W alias of the same set (W_n = PReg(32 + n)).
        let pool32: Vec<u16> = {
            let mut v: Vec<u16> = gpr32.iter().map(|p| p.encoding() - 32).collect();
            v.sort_unstable();
            v
        };
        assert_eq!(
            pool32, canonical,
            "linear_scan GPR32 pool is not the W alias of ALLOCATABLE_GPRS"
        );
    }

    #[test]
    fn test_simple_allocation() {
        let regs = aarch64_allocatable_regs();
        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 10);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(5, 15);
                i.spill_weight = 2.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");
        // Both should be allocated to different registers (plenty available).
        assert_eq!(result.allocation.len(), 2);
        let preg0 = result.allocation[&VReg {
            id: 0,
            class: RegClass::Gpr64,
        }];
        let preg1 = result.allocation[&VReg {
            id: 1,
            class: RegClass::Gpr64,
        }];
        assert_ne!(preg0, preg1);
    }

    #[test]
    fn test_aarch64_prefers_caller_saved_before_callee_saved() {
        let regs = aarch64_allocatable_regs();
        let mut interval64 = LiveInterval::new(VReg {
            id: 0,
            class: RegClass::Gpr64,
        });
        interval64.add_range(0, 5);
        interval64.spill_weight = 1.0;

        let mut interval32 = LiveInterval::new(VReg {
            id: 1,
            class: RegClass::Gpr32,
        });
        interval32.add_range(0, 5);
        interval32.spill_weight = 1.0;

        let mut scan64 = LinearScan::new(vec![interval64], &regs);
        let result64 = scan64.allocate().expect("GPR64 allocation should succeed");
        assert_eq!(
            result64.allocation[&VReg {
                id: 0,
                class: RegClass::Gpr64,
            }],
            PReg::new(0),
            "first GPR64 allocation should use caller-saved X0"
        );

        let mut scan32 = LinearScan::new(vec![interval32], &regs);
        let result32 = scan32.allocate().expect("GPR32 allocation should succeed");
        assert_eq!(
            result32.allocation[&VReg {
                id: 1,
                class: RegClass::Gpr32,
            }],
            PReg::new(32),
            "first GPR32 allocation should use caller-saved W0"
        );
    }

    #[test]
    fn test_returned_register_keeps_preference_order() {
        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let v1 = VReg {
            id: 1,
            class: RegClass::Gpr64,
        };
        let v2 = VReg {
            id: 2,
            class: RegClass::Gpr64,
        };

        let mut first = LiveInterval::new(v0);
        first.add_range(0, 5);
        first.spill_weight = 1.0;

        let mut second = LiveInterval::new(v1);
        second.add_range(0, 10);
        second.spill_weight = 1.0;

        let mut third = LiveInterval::new(v2);
        third.add_range(5, 8);
        third.spill_weight = 1.0;

        let mut regs = BTreeMap::new();
        regs.insert(
            RegClass::Gpr64,
            vec![PReg::new(0), PReg::new(1), PReg::new(19)],
        );

        let mut scan = LinearScan::new(vec![first, second, third], &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation[&v0], PReg::new(0));
        assert_eq!(result.allocation[&v1], PReg::new(1));
        assert_eq!(
            result.allocation[&v2],
            PReg::new(0),
            "expired caller-saved X0 should be reused before selecting callee-saved X19"
        );
    }

    #[test]
    fn test_reserved_reg_point_avoids_live_interval() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0), PReg::new(19)]);

        let mut interval = LiveInterval::new(VReg {
            id: 0,
            class: RegClass::Gpr64,
        });
        interval.add_range(0, 10);
        interval.spill_weight = 1.0;

        let mut reserved = BTreeMap::new();
        reserved.insert(PReg::new(0), vec![5]);

        let mut scan = LinearScan::new_with_reserved(vec![interval], &regs, reserved);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(
            result.allocation[&VReg {
                id: 0,
                class: RegClass::Gpr64,
            }],
            PReg::new(19),
            "live interval must avoid a physical register reserved inside its range"
        );
    }

    #[test]
    fn test_reserved_alias_point_avoids_live_interval() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let mut interval = LiveInterval::new(VReg {
            id: 0,
            class: RegClass::Gpr64,
        });
        interval.add_range(0, 10);
        interval.spill_weight = 1.0;

        let mut reserved = BTreeMap::new();
        reserved.insert(PReg::new(32), vec![5]); // W0 aliases X0.

        let mut scan = LinearScan::new_with_reserved(vec![interval], &regs, reserved);
        let result = scan.allocate().expect("allocation should succeed");

        assert!(result.allocation.is_empty());
        assert_eq!(scan.spilled_vregs().len(), 1);
    }

    /// The reservation checks visit only the reserved positions inside an
    /// interval's ranges, over a union built once per candidate register:
    /// `n` intervals, each checked against one register reserved at `n` call
    /// positions, cost `O(n)`. Asking `is_live_at` at every position per
    /// interval, or rebuilding the union per check, costs `O(n^2)` and fails
    /// this bound (see `crate::scan_work`).
    #[test]
    fn reservation_checks_cost_grows_linearly() {
        let x0 = PReg::new(0);
        crate::scan_work::assert_near_linear("LinearScan reservation checks", 256, |n| {
            let mut regs = BTreeMap::new();
            regs.insert(RegClass::Gpr64, vec![x0]);
            let intervals: Vec<LiveInterval> = (0..n as u32)
                .map(|i| {
                    let mut interval = LiveInterval::new(VReg {
                        id: i,
                        class: RegClass::Gpr64,
                    });
                    // Live strictly between two reserved positions.
                    interval.add_range(4 * i + 1, 4 * i + 3);
                    interval
                })
                .collect();
            let mut reserved = BTreeMap::new();
            // Listed descending: the memoized union sorts the positions.
            reserved.insert(x0, (0..n as u32).rev().map(|i| 4 * i).collect());
            let scan = LinearScan::new_with_reserved(intervals, &regs, reserved);
            let (interfering, units) = crate::scan_work::measure(|| {
                (0..n)
                    .filter(|&idx| {
                        scan.reserved_interferes(idx, x0)
                            || scan.reserved_interferes_except(idx, x0, &[])
                    })
                    .count()
            });
            assert_eq!(interfering, 0);
            units
        });
    }

    #[test]
    fn test_expiring_mixed_width_alias_keeps_active_alias_reserved() {
        let x0_vreg = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let w0_vreg = VReg {
            id: 1,
            class: RegClass::Gpr32,
        };

        let mut x0_interval = LiveInterval::new(x0_vreg);
        x0_interval.add_range(0, 5);
        x0_interval.spill_weight = 1.0;

        let mut w0_interval = LiveInterval::new(w0_vreg);
        w0_interval.add_range(0, 10);
        w0_interval.spill_weight = 1.0;

        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);
        regs.insert(RegClass::Gpr32, vec![PReg::new(32)]);

        let mut scan = LinearScan::new(vec![x0_interval, w0_interval], &regs);
        scan.free_regs.insert(RegClass::Gpr64, Vec::new());
        scan.free_regs.insert(RegClass::Gpr32, Vec::new());
        scan.allocation.insert(x0_vreg, PReg::new(0));
        scan.allocation.insert(w0_vreg, PReg::new(32));
        scan.set_active(vec![0, 1]);

        scan.expire_old_intervals(5);

        assert_eq!(scan.active, vec![1]);
        assert_eq!(scan.allocation.get(&w0_vreg), Some(&PReg::new(32)));
        assert!(
            !scan.free_pool_contains(PReg::new(0)),
            "X0 must not be returned while active W0 still owns its alias"
        );
        assert!(
            !scan.free_pool_contains(PReg::new(32)),
            "W0 must not be returned while its interval remains active"
        );

        scan.expire_old_intervals(10);

        assert!(scan.active.is_empty());
        assert!(scan.free_pool_contains(PReg::new(0)));
        assert!(scan.free_pool_contains(PReg::new(32)));
        assert_eq!(scan.free_pool_duplicate_count(PReg::new(0)), 1);
        assert_eq!(scan.free_pool_duplicate_count(PReg::new(32)), 1);
    }

    #[test]
    fn test_try_alloc_skips_stale_free_alias_of_active_interval() {
        let active_w0 = VReg {
            id: 0,
            class: RegClass::Gpr32,
        };
        let candidate_x = VReg {
            id: 1,
            class: RegClass::Gpr64,
        };

        let mut w_interval = LiveInterval::new(active_w0);
        w_interval.add_range(0, 10);
        w_interval.spill_weight = 1.0;

        let mut x_interval = LiveInterval::new(candidate_x);
        x_interval.add_range(5, 8);
        x_interval.spill_weight = 1.0;

        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr32, vec![PReg::new(32)]);
        regs.insert(RegClass::Gpr64, vec![PReg::new(0), PReg::new(1)]);

        let mut scan = LinearScan::new(vec![w_interval, x_interval], &regs);
        scan.allocation.insert(active_w0, PReg::new(32));
        scan.set_active(vec![0]);
        assert!(
            scan.free_pool_contains(PReg::new(0)),
            "test intentionally leaves stale X0 in the free pool"
        );

        let allocated = scan
            .try_alloc_free_reg(1, RegClass::Gpr64)
            .expect("non-aliasing X1 should still be available");

        assert_eq!(allocated, PReg::new(1));
        assert!(
            scan.free_pool_contains(PReg::new(0)),
            "stale X0 must remain unselected while W0 is active"
        );
    }

    #[test]
    fn test_blocked_alloc_does_not_evict_into_active_alias() {
        let active_x0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let active_w0 = VReg {
            id: 1,
            class: RegClass::Gpr32,
        };
        let current_x = VReg {
            id: 2,
            class: RegClass::Gpr64,
        };

        let mut x_interval = LiveInterval::new(active_x0);
        x_interval.add_range(0, 10);
        x_interval.spill_weight = 1.0;

        let mut w_interval = LiveInterval::new(active_w0);
        w_interval.add_range(0, 10);
        w_interval.spill_weight = 10.0;

        let mut current_interval = LiveInterval::new(current_x);
        current_interval.add_range(5, 8);
        current_interval.spill_weight = 100.0;

        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);
        regs.insert(RegClass::Gpr32, vec![PReg::new(32)]);

        let mut scan = LinearScan::new(vec![x_interval, w_interval, current_interval], &regs);
        scan.free_regs.insert(RegClass::Gpr64, Vec::new());
        scan.free_regs.insert(RegClass::Gpr32, Vec::new());
        scan.allocation.insert(active_x0, PReg::new(0));
        scan.allocation.insert(active_w0, PReg::new(32));
        scan.set_active(vec![0, 1]);

        scan.allocate_blocked_reg(2)
            .expect("blocked allocation should complete by spilling current");

        assert_eq!(scan.allocation.get(&current_x), None);
        assert_eq!(scan.allocation.get(&active_x0), Some(&PReg::new(0)));
        assert_eq!(scan.allocation.get(&active_w0), Some(&PReg::new(32)));
        assert_eq!(scan.spilled_vregs(), &[current_x]);
    }

    #[test]
    fn test_blocked_alloc_evicts_lower_weight_active_alias() {
        let active_w0 = VReg {
            id: 0,
            class: RegClass::Gpr32,
        };
        let current_x0 = VReg {
            id: 1,
            class: RegClass::Gpr64,
        };

        let mut w_interval = LiveInterval::new(active_w0);
        w_interval.add_range(0, 10);
        w_interval.spill_weight = 1.0;

        let mut x_interval = LiveInterval::new(current_x0);
        x_interval.add_range(5, 8);
        x_interval.spill_weight = 10.0;

        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr32, vec![PReg::new(32)]);
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let mut scan = LinearScan::new(vec![w_interval, x_interval], &regs);
        scan.free_regs.insert(RegClass::Gpr32, Vec::new());
        scan.free_regs.insert(RegClass::Gpr64, Vec::new());
        scan.allocation.insert(active_w0, PReg::new(32));
        scan.set_active(vec![0]);

        scan.allocate_blocked_reg(1)
            .expect("blocked allocation should evict the lower-weight aliased active interval");

        assert_eq!(scan.allocation.get(&current_x0), Some(&PReg::new(0)));
        assert_eq!(scan.allocation.get(&active_w0), None);
        assert_eq!(scan.active, vec![1]);
        assert_eq!(scan.spilled_vregs(), &[active_w0]);
    }

    #[test]
    fn test_non_overlapping_intervals_reuse_register() {
        let regs = aarch64_allocatable_regs();
        // Two intervals that don't overlap can use the same register.
        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 5);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(5, 10); // starts exactly where first ends
                i.spill_weight = 1.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");
        assert_eq!(result.allocation.len(), 2);
        // With plenty of registers, they may or may not reuse — the important
        // thing is both are allocated successfully.
    }

    #[test]
    fn test_spill_under_register_pressure() {
        // Create a situation with only 2 registers and 3 overlapping intervals.
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0), PReg::new(1)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 1.0; // low weight = spill candidate
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 5.0; // high weight
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 2,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 10.0; // highest weight
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");
        // Only 2 registers for 3 overlapping intervals — one must be spilled.
        assert_eq!(result.allocation.len(), 2, "should allocate 2");
        assert_eq!(scan.spilled_vregs().len(), 1, "should spill 1");

        // The spilled VReg should be the one with the lowest spill weight (v0).
        let spilled = scan.spilled_vregs();
        assert_eq!(spilled[0].id, 0, "lowest weight vreg should be spilled");
    }

    #[test]
    fn test_spill_current_if_cheaper() {
        // When the current interval has lower weight than all active intervals,
        // the current interval itself should be spilled.
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 10.0; // high weight, allocated first
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(5, 15);
                i.spill_weight = 1.0; // low weight, arrives later
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");
        assert_eq!(result.allocation.len(), 1);
        assert_eq!(scan.spilled_vregs().len(), 1);
        // v1 (the cheaper one) should be spilled since v0 is already active
        // and has higher weight.
        assert_eq!(scan.spilled_vregs()[0].id, 1);
    }

    #[test]
    fn test_expire_old_intervals_frees_registers() {
        // Two non-overlapping intervals + one overlapping should work with 1 register.
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 5);
                i.spill_weight = 1.0;
                i
            },
            {
                // Starts after v0 ends — register should be freed.
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(5, 10);
                i.spill_weight = 1.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");
        // Both should be allocated (same register, sequentially).
        assert_eq!(result.allocation.len(), 2);
        assert!(scan.spilled_vregs().is_empty());
    }

    #[test]
    fn test_fixed_intervals_skipped() {
        let regs = aarch64_allocatable_regs();
        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 10);
                i.is_fixed = true; // should be skipped
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 10);
                i.spill_weight = 1.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");
        // Fixed interval should NOT appear in allocation.
        assert!(!result.allocation.contains_key(&VReg {
            id: 0,
            class: RegClass::Gpr64
        }));
        // Non-fixed interval should be allocated.
        assert!(result.allocation.contains_key(&VReg {
            id: 1,
            class: RegClass::Gpr64
        }));
    }

    #[test]
    fn test_multiple_register_classes() {
        let regs = aarch64_allocatable_regs();
        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 10);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Fpr64,
                });
                i.add_range(0, 10);
                i.spill_weight = 1.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");
        // Both should be allocated — they use different register classes.
        assert_eq!(result.allocation.len(), 2);
        let preg_gpr = result.allocation[&VReg {
            id: 0,
            class: RegClass::Gpr64,
        }];
        let preg_fpr = result.allocation[&VReg {
            id: 1,
            class: RegClass::Fpr64,
        }];
        // GPR and FPR registers should have different encodings.
        assert_ne!(preg_gpr, preg_fpr);
    }

    #[test]
    fn test_many_sequential_intervals_no_spill() {
        // 100 intervals that don't overlap should all be allocated with 1 register.
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let intervals: Vec<LiveInterval> = (0..100)
            .map(|i| {
                let mut interval = LiveInterval::new(VReg {
                    id: i,
                    class: RegClass::Gpr64,
                });
                interval.add_range(i * 10, i * 10 + 5);
                interval.spill_weight = 1.0;
                interval
            })
            .collect();

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");
        assert_eq!(result.allocation.len(), 100);
        assert!(scan.spilled_vregs().is_empty());
    }

    #[test]
    fn test_empty_intervals() {
        let regs = aarch64_allocatable_regs();
        let intervals: Vec<LiveInterval> = Vec::new();
        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("empty should succeed");
        assert!(result.allocation.is_empty());
        assert!(result.spills.is_empty());
    }

    #[test]
    fn test_aarch64_regs_gpr32_count() {
        let regs = aarch64_allocatable_regs();
        // GPR32: W0-W7 (8) + W9-W15 (7) + W19-W28 (10) = 25.
        // W8 is excluded with X8 — the same architectural register, which
        // AAPCS64 reserves for the indirect result location.
        assert_eq!(regs[&RegClass::Gpr32].len(), 25);
    }

    #[test]
    fn test_aarch64_regs_fpr128_count() {
        let regs = aarch64_allocatable_regs();
        // FPR128: V16/V17 are reserved aliases of spill scratches, and V8-V15
        // are excluded (AAPCS64 preserves only their lower 64 bits, so a 128-bit
        // value there would lose its upper 64 across a call).
        // V0-V7 (8) + V18-V31 (14) = 22.
        assert_eq!(regs[&RegClass::Fpr128].len(), 22);
        assert!(!regs[&RegClass::Fpr128].contains(&PReg::new(80)));
        assert!(!regs[&RegClass::Fpr128].contains(&PReg::new(81)));
        // SOUNDNESS: V8-V15 (enc 72-79) must never be allocatable as Fpr128.
        assert!(
            !regs[&RegClass::Fpr128].contains(&PReg::new(72)),
            "V8 must not be Fpr128-allocatable"
        );
        assert!(
            !regs[&RegClass::Fpr128].contains(&PReg::new(79)),
            "V15 must not be Fpr128-allocatable"
        );
        // Sanity: V7 (71) and V18 (82) remain allocatable around the gap.
        assert!(regs[&RegClass::Fpr128].contains(&PReg::new(71)));
        assert!(regs[&RegClass::Fpr128].contains(&PReg::new(82)));
    }

    /// SOUNDNESS: the Fpr64/Fpr32/Fpr16 aliases of V8-V15 (D8-D15 enc 104-111,
    /// S8-S15 enc 136-143, H8-H15 enc 173-180) must STAY allocatable — their
    /// entire value is the lower 64 bits AAPCS64 preserves and the D-register
    /// STP/LDP fully saves. Only the 128-bit view is unsound. Guard against
    /// accidentally over-restricting them along with the Fpr128 drop.
    #[test]
    fn test_aarch64_v8_v15_lower_aliases_stay_allocatable() {
        let regs = aarch64_allocatable_regs();
        for d in 104u16..=111 {
            assert!(
                regs[&RegClass::Fpr64].contains(&PReg::new(d)),
                "D-reg {d} must stay allocatable"
            );
        }
        for s in 136u16..=143 {
            assert!(
                regs[&RegClass::Fpr32].contains(&PReg::new(s)),
                "S-reg {s} must stay allocatable"
            );
        }
        for h in 173u16..=180 {
            assert!(
                regs[&RegClass::Fpr16].contains(&PReg::new(h)),
                "H-reg {h} must stay allocatable"
            );
        }
    }

    #[test]
    fn test_aarch64_regs_fpr32_count() {
        let regs = aarch64_allocatable_regs();
        // FPR32: S16/S17 are reserved aliases of spill scratches.
        assert_eq!(regs[&RegClass::Fpr32].len(), 30);
        assert!(!regs[&RegClass::Fpr32].contains(&PReg::new(144)));
        assert!(!regs[&RegClass::Fpr32].contains(&PReg::new(145)));
    }

    #[test]
    fn test_aarch64_regs_fpr16_count() {
        let regs = aarch64_allocatable_regs();
        // FPR16: H16/H17 are reserved aliases of spill scratches.
        assert_eq!(regs[&RegClass::Fpr16].len(), 30);
        assert!(!regs[&RegClass::Fpr16].contains(&PReg::new(181)));
        assert!(!regs[&RegClass::Fpr16].contains(&PReg::new(182)));
    }

    // -----------------------------------------------------------------------
    // Additional edge-case tests (issue #139)
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_intervals_fixed_nothing_to_allocate() {
        let regs = BTreeMap::new();
        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 10);
                i.is_fixed = true;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Fpr32,
                });
                i.add_range(3, 12);
                i.is_fixed = true;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 2,
                    class: RegClass::Gpr32,
                });
                i.add_range(12, 20);
                i.is_fixed = true;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan
            .allocate()
            .expect("all-fixed allocation should succeed");

        assert!(result.allocation.is_empty());
        assert!(scan.spilled_vregs().is_empty());
    }

    #[test]
    fn test_single_interval_with_zero_spill_weight() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let intervals = vec![{
            let mut i = LiveInterval::new(VReg {
                id: 0,
                class: RegClass::Gpr64,
            });
            i.add_range(0, 10);
            i.spill_weight = 0.0;
            i
        }];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation.len(), 1);
        assert_eq!(
            result.allocation[&VReg {
                id: 0,
                class: RegClass::Gpr64,
            }],
            PReg::new(0)
        );
        assert!(scan.spilled_vregs().is_empty());
    }

    #[test]
    fn test_extreme_register_pressure_spills_exactly_one_interval() {
        let mut regs = BTreeMap::new();
        regs.insert(
            RegClass::Gpr64,
            vec![PReg::new(0), PReg::new(1), PReg::new(2), PReg::new(3)],
        );

        let intervals: Vec<LiveInterval> = (0u32..=4)
            .map(|id| {
                let mut i = LiveInterval::new(VReg {
                    id,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = (id + 1) as f64;
                i
            })
            .collect();

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation.len(), 4);
        assert_eq!(
            scan.spilled_vregs(),
            &[VReg {
                id: 0,
                class: RegClass::Gpr64,
            }]
        );
        for id in 1u32..=4 {
            assert!(result.allocation.contains_key(&VReg {
                id,
                class: RegClass::Gpr64,
            }));
        }
    }

    #[test]
    fn test_intervals_sorted_in_reverse_order_are_processed_by_start() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(10, 20);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 5);
                i.spill_weight = 1.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation.len(), 2);
        assert!(scan.spilled_vregs().is_empty());
        assert_eq!(
            result.allocation[&VReg {
                id: 0,
                class: RegClass::Gpr64,
            }],
            result.allocation[&VReg {
                id: 1,
                class: RegClass::Gpr64,
            }]
        );
    }

    #[test]
    fn test_very_long_interval_vs_many_short_intervals() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let mut intervals = vec![{
            let mut i = LiveInterval::new(VReg {
                id: 0,
                class: RegClass::Gpr64,
            });
            i.add_range(0, 1000);
            i.spill_weight = 1.0;
            i
        }];

        for id in 1u32..=5 {
            let mut i = LiveInterval::new(VReg {
                id,
                class: RegClass::Gpr64,
            });
            i.add_range(id * 100, id * 100 + 10);
            i.spill_weight = 10.0;
            intervals.push(i);
        }

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(
            scan.spilled_vregs(),
            &[VReg {
                id: 0,
                class: RegClass::Gpr64,
            }]
        );
        assert_eq!(result.allocation.len(), 5);
        for id in 1u32..=5 {
            assert!(result.allocation.contains_key(&VReg {
                id,
                class: RegClass::Gpr64,
            }));
            assert_eq!(
                result.allocation[&VReg {
                    id,
                    class: RegClass::Gpr64,
                }],
                PReg::new(0)
            );
        }
    }

    #[test]
    fn test_spill_with_equal_weights_is_deterministic() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 5.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(5, 15);
                i.spill_weight = 5.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation.len(), 1);
        assert_eq!(
            scan.spilled_vregs(),
            &[VReg {
                id: 1,
                class: RegClass::Gpr64,
            }]
        );
        assert!(result.allocation.contains_key(&VReg {
            id: 0,
            class: RegClass::Gpr64,
        }));
        assert!(!result.allocation.contains_key(&VReg {
            id: 1,
            class: RegClass::Gpr64,
        }));
    }

    #[test]
    fn test_allocation_with_only_fpr32_class_registers() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Fpr32, vec![PReg::new(128), PReg::new(129)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Fpr32,
                });
                i.add_range(0, 10);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Fpr32,
                });
                i.add_range(0, 10);
                i.spill_weight = 2.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        let allowed = [PReg::new(128), PReg::new(129)];
        let preg0 = result.allocation[&VReg {
            id: 0,
            class: RegClass::Fpr32,
        }];
        let preg1 = result.allocation[&VReg {
            id: 1,
            class: RegClass::Fpr32,
        }];

        assert_eq!(result.allocation.len(), 2);
        assert!(scan.spilled_vregs().is_empty());
        assert_ne!(preg0, preg1);
        assert!(allowed.contains(&preg0));
        assert!(allowed.contains(&preg1));
    }

    #[test]
    fn test_three_way_register_pressure_with_mixed_fixed_and_non_fixed_intervals() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.is_fixed = true;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 2,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 10.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation.len(), 1);
        assert!(!result.allocation.contains_key(&VReg {
            id: 0,
            class: RegClass::Gpr64,
        }));
        assert_eq!(
            scan.spilled_vregs(),
            &[VReg {
                id: 1,
                class: RegClass::Gpr64,
            }]
        );
        assert_eq!(
            result.allocation[&VReg {
                id: 2,
                class: RegClass::Gpr64,
            }],
            PReg::new(0)
        );
    }

    #[test]
    fn test_sequential_intervals_with_gaps_free_register_properly() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 2);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(4, 6);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 2,
                    class: RegClass::Gpr64,
                });
                i.add_range(9, 11);
                i.spill_weight = 1.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation.len(), 3);
        assert!(scan.spilled_vregs().is_empty());
        assert_eq!(
            result.allocation[&VReg {
                id: 0,
                class: RegClass::Gpr64,
            }],
            PReg::new(0)
        );
        assert_eq!(
            result.allocation[&VReg {
                id: 1,
                class: RegClass::Gpr64,
            }],
            PReg::new(0)
        );
        assert_eq!(
            result.allocation[&VReg {
                id: 2,
                class: RegClass::Gpr64,
            }],
            PReg::new(0)
        );
    }

    #[test]
    fn test_adjacent_intervals_with_exact_matching_boundaries() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 5);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(5, 10);
                i.spill_weight = 1.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation.len(), 2);
        assert!(scan.spilled_vregs().is_empty());
        assert_eq!(
            result.allocation[&VReg {
                id: 0,
                class: RegClass::Gpr64,
            }],
            PReg::new(0)
        );
        assert_eq!(
            result.allocation[&VReg {
                id: 1,
                class: RegClass::Gpr64,
            }],
            PReg::new(0)
        );
    }

    #[test]
    fn test_very_short_intervals_length_one_interleaved_with_long_ones() {
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0), PReg::new(1)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 100);
                i.spill_weight = 100.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 100);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 2,
                    class: RegClass::Gpr64,
                });
                i.add_range(10, 11);
                i.spill_weight = 10.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 3,
                    class: RegClass::Gpr64,
                });
                i.add_range(50, 51);
                i.spill_weight = 10.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 4,
                    class: RegClass::Gpr64,
                });
                i.add_range(90, 91);
                i.spill_weight = 10.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(
            scan.spilled_vregs(),
            &[VReg {
                id: 1,
                class: RegClass::Gpr64,
            }]
        );
        assert_eq!(result.allocation.len(), 4);
        assert!(result.allocation.contains_key(&VReg {
            id: 0,
            class: RegClass::Gpr64,
        }));
        assert!(result.allocation.contains_key(&VReg {
            id: 2,
            class: RegClass::Gpr64,
        }));
        assert!(result.allocation.contains_key(&VReg {
            id: 3,
            class: RegClass::Gpr64,
        }));
        assert!(result.allocation.contains_key(&VReg {
            id: 4,
            class: RegClass::Gpr64,
        }));
    }

    // -----------------------------------------------------------------------
    // Additional edge-case tests (issue #404 — TL7 coverage expansion)
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_registers_exhausted_cascading_spills() {
        // With 2 registers and 5 overlapping intervals, 3 must spill.
        // Verifies cascading spill behavior under extreme pressure.
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0), PReg::new(1)]);

        let intervals: Vec<LiveInterval> = (0u32..5)
            .map(|id| {
                let mut i = LiveInterval::new(VReg {
                    id,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 50);
                i.spill_weight = (id + 1) as f64; // 1.0, 2.0, 3.0, 4.0, 5.0
                i
            })
            .collect();

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation.len(), 2, "only 2 registers available");
        assert_eq!(scan.spilled_vregs().len(), 3, "3 intervals must spill");

        // The lowest-weight intervals (v0, v1, v2) should be spilled.
        let spilled_ids: Vec<u32> = scan.spilled_vregs().iter().map(|v| v.id).collect();
        for id in [0, 1, 2] {
            assert!(
                spilled_ids.contains(&id),
                "v{id} (weight {}) should be spilled",
                id + 1
            );
        }
        // Highest-weight intervals (v3, v4) should be allocated.
        for id in [3, 4] {
            assert!(
                result.allocation.contains_key(&VReg {
                    id,
                    class: RegClass::Gpr64
                }),
                "v{id} should be allocated"
            );
        }
    }

    #[test]
    fn test_mixed_gpr_and_fpr_simultaneous_pressure() {
        // GPR and FPR allocation are independent — filling one class
        // should not affect the other.
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);
        regs.insert(RegClass::Fpr64, vec![PReg::new(96)]);

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 1.0;
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Fpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 1.0;
                i
            },
            {
                // Second GPR interval overlaps — must spill one.
                let mut i = LiveInterval::new(VReg {
                    id: 2,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 5.0;
                i
            },
            {
                // Second FPR interval overlaps — must spill one.
                let mut i = LiveInterval::new(VReg {
                    id: 3,
                    class: RegClass::Fpr64,
                });
                i.add_range(0, 20);
                i.spill_weight = 5.0;
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        // 2 allocated (one per class), 2 spilled (one per class).
        assert_eq!(result.allocation.len(), 2);
        assert_eq!(scan.spilled_vregs().len(), 2);

        // The lower-weight interval in each class should be spilled.
        let spilled_ids: Vec<u32> = scan.spilled_vregs().iter().map(|v| v.id).collect();
        assert!(
            spilled_ids.contains(&0),
            "v0 (GPR, weight 1.0) should be spilled"
        );
        assert!(
            spilled_ids.contains(&1),
            "v1 (FPR, weight 1.0) should be spilled"
        );
    }

    #[test]
    fn test_interleaved_short_and_long_no_spill_single_reg() {
        // One register, intervals that exactly interleave without overlap.
        // Tests that expire_old_intervals works correctly at boundaries.
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        // [0,3), [3,6), [6,9), ... — each starts exactly where previous ends.
        let intervals: Vec<LiveInterval> = (0u32..20)
            .map(|id| {
                let mut i = LiveInterval::new(VReg {
                    id,
                    class: RegClass::Gpr64,
                });
                i.add_range(id * 3, id * 3 + 3);
                i.spill_weight = 1.0;
                i
            })
            .collect();

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation.len(), 20);
        assert!(
            scan.spilled_vregs().is_empty(),
            "no spills needed with non-overlapping intervals"
        );
    }

    #[test]
    fn test_spill_eviction_replaces_lowest_weight_active() {
        // 3 registers, 4 overlapping intervals. The first 3 fill registers,
        // the 4th (high weight) evicts the lowest-weight active interval.
        let mut regs = BTreeMap::new();
        regs.insert(
            RegClass::Gpr64,
            vec![PReg::new(0), PReg::new(1), PReg::new(2)],
        );

        let intervals = vec![
            {
                let mut i = LiveInterval::new(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 30);
                i.spill_weight = 3.0; // medium — will be evicted
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 1,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 30);
                i.spill_weight = 10.0; // high
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 2,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 30);
                i.spill_weight = 7.0; // medium-high
                i
            },
            {
                let mut i = LiveInterval::new(VReg {
                    id: 3,
                    class: RegClass::Gpr64,
                });
                i.add_range(0, 30);
                i.spill_weight = 20.0; // highest — arrives last, evicts v0
                i
            },
        ];

        let mut scan = LinearScan::new(intervals, &regs);
        let result = scan.allocate().expect("allocation should succeed");

        assert_eq!(result.allocation.len(), 3);
        assert_eq!(scan.spilled_vregs().len(), 1);
        // v0 has the lowest weight among active intervals, so it should be evicted.
        assert_eq!(scan.spilled_vregs()[0].id, 0);
    }

    /// The per-position scan `reserved_interferes_except` used before the
    /// memoized range-side search, verbatim, as the oracle.
    fn reference_reserved_interferes_except(
        scan: &LinearScan,
        interval_idx: usize,
        preg: PReg,
        exempt: &[u32],
    ) -> bool {
        let interval = &scan.intervals[interval_idx];
        scan.reserved_regs.iter().any(|(&reserved_preg, points)| {
            crate::greedy::allocator_pregs_overlap(reserved_preg, preg)
                && points
                    .iter()
                    .any(|&pos| interval.is_live_at(pos) && !exempt.contains(&pos))
        })
    }

    #[test]
    fn range_side_reserved_search_equals_the_position_scan() {
        let mut seed = 0x0dd0_2023_c0de_5eedu64;
        let mut next = move |bound: u32| -> u32 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % u64::from(bound.max(1))) as u32
        };
        // X0-X18 and their W views, V0-V7 / D0-D7: overlapping keys and views.
        let pregs: Vec<PReg> = (0..19u16)
            .chain(32..51)
            .chain(64..72)
            .chain(96..104)
            .map(PReg::new)
            .collect();
        let mut interfering = 0usize;
        for _case in 0..3_000 {
            let mut reserved: BTreeMap<PReg, Vec<u32>> = BTreeMap::new();
            for _ in 0..next(12) {
                let preg = pregs[next(pregs.len() as u32) as usize];
                let points = reserved.entry(preg).or_default();
                for _ in 0..next(20) {
                    points.push(next(200));
                }
            }
            let intervals: Vec<LiveInterval> = (0..6)
                .map(|v| {
                    let mut interval = LiveInterval::new(VReg::new(v, RegClass::Gpr64));
                    let mut pos = next(40);
                    for _ in 0..1 + next(4) {
                        let len = next(30);
                        interval.ranges.push(crate::liveness::LiveRange {
                            start: pos,
                            end: pos + len,
                        });
                        pos += len + next(30);
                    }
                    interval
                })
                .collect();
            let scan = LinearScan::new_with_reserved(intervals, &BTreeMap::new(), reserved);
            for interval_idx in 0..scan.intervals.len() {
                for &preg in &pregs {
                    let exempt: Vec<u32> = (0..next(3)).map(|_| next(200)).collect();
                    let expected =
                        reference_reserved_interferes_except(&scan, interval_idx, preg, &exempt);
                    assert_eq!(
                        scan.reserved_interferes_except(interval_idx, preg, &exempt),
                        expected
                    );
                    assert_eq!(
                        scan.reserved_interferes(interval_idx, preg),
                        reference_reserved_interferes_except(&scan, interval_idx, preg, &[])
                    );
                    interfering += usize::from(expected);
                }
            }
        }
        assert!(interfering > 10_000, "{interfering}");
    }

    // -----------------------------------------------------------------------
    // L14-P6: the active-set holdings against the allocator they replaced
    // -----------------------------------------------------------------------

    /// A deterministic xorshift stream for the generated inputs.
    struct Stream(u64);

    impl Stream {
        fn next(&mut self, bound: u32) -> u32 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % u64::from(bound.max(1))) as u32
        }

        fn chance(&mut self, percent: u32) -> bool {
            self.next(100) < percent
        }
    }

    /// One generated allocation problem.
    struct Problem {
        intervals: Vec<LiveInterval>,
        regs: BTreeMap<RegClass, Vec<PReg>>,
        reserved: BTreeMap<PReg, Vec<u32>>,
        hints: BTreeMap<VReg, Vec<PReg>>,
        hint_exempt: BTreeMap<(VReg, PReg), Vec<u32>>,
    }

    /// Intervals over the aarch64 or x86-64 register file (sometimes cut to a
    /// few registers per class, so most intervals are blocked), in classes
    /// whose registers alias each other, with holes, ties and odd spill
    /// weights, fixed intervals, reservations, hints and exemptions. With
    /// `repeat_vregs`, some intervals share a VReg.
    fn generate(stream: &mut Stream, repeat_vregs: bool) -> Problem {
        let x86 = stream.chance(25);
        let full = if x86 {
            crate::x86_adapter::x86_64_allocatable_regs()
        } else {
            aarch64_allocatable_regs()
        };
        let keep = if stream.chance(60) {
            1 + stream.next(5) as usize
        } else {
            usize::MAX
        };
        let regs: BTreeMap<RegClass, Vec<PReg>> = full
            .iter()
            .map(|(&class, pool)| (class, pool.iter().copied().take(keep).collect()))
            .collect();
        let classes: Vec<RegClass> = regs.keys().copied().collect();
        let universe: Vec<PReg> = full.values().flatten().copied().collect();
        let count = 1 + stream.next(120) as usize;
        let span = 20 + stream.next(400);
        let mut intervals = Vec::with_capacity(count);
        for id in 0..count {
            let id = if repeat_vregs && id > 0 && stream.chance(20) {
                stream.next(id as u32)
            } else {
                id as u32
            };
            let class = classes[stream.next(classes.len() as u32) as usize];
            let mut interval = LiveInterval::new(VReg { id, class });
            let mut position = stream.next(span);
            for _ in 0..1 + stream.next(3) {
                let length = 1 + stream.next(60);
                interval.add_range(position, position + length);
                position += length + stream.next(40);
            }
            interval.spill_weight = match stream.next(10) {
                0 => 1.0,
                1 => f64::INFINITY,
                2 => 0.0,
                _ => f64::from(stream.next(50)) / 7.0,
            };
            interval.is_fixed = stream.chance(3);
            intervals.push(interval);
        }
        let mut reserved: BTreeMap<PReg, Vec<u32>> = BTreeMap::new();
        for _ in 0..stream.next(6) {
            let preg = universe[stream.next(universe.len() as u32) as usize];
            let points = reserved.entry(preg).or_default();
            for _ in 0..1 + stream.next(8) {
                points.push(stream.next(span + 100));
            }
            points.sort_unstable();
            points.dedup();
        }
        let mut hints: BTreeMap<VReg, Vec<PReg>> = BTreeMap::new();
        let mut hint_exempt: BTreeMap<(VReg, PReg), Vec<u32>> = BTreeMap::new();
        for interval in &intervals {
            if stream.chance(30) {
                let preg = universe[stream.next(universe.len() as u32) as usize];
                hints.entry(interval.vreg).or_default().push(preg);
                if stream.chance(50) {
                    hint_exempt
                        .entry((interval.vreg, preg))
                        .or_default()
                        .push(interval.start());
                }
            }
        }
        Problem {
            intervals,
            regs,
            reserved,
            hints,
            hint_exempt,
        }
    }

    /// What an allocator returned, in full: the result (or its error), the
    /// spilled VRegs in order and the free pools it ended with.
    type Outcome = (
        Result<BTreeMap<VReg, PReg>, String>,
        Vec<VReg>,
        BTreeMap<RegClass, Vec<PReg>>,
    );

    fn run_indexed(problem: &Problem, holders: bool) -> Outcome {
        let mut scan = LinearScan::new_with_reserved(
            problem.intervals.clone(),
            &problem.regs,
            problem.reserved.clone(),
        );
        if !holders {
            scan = scan.without_holders();
        }
        scan.set_hints(problem.hints.clone(), problem.hint_exempt.clone());
        let result = scan
            .allocate()
            .map(|result| result.allocation)
            .map_err(|error| error.to_string());
        (
            result,
            scan.spilled_vregs().to_vec(),
            scan.free_pools().clone(),
        )
    }

    fn run_reference(problem: &Problem) -> Outcome {
        let mut scan = crate::linear_scan_reference::ReferenceLinearScan::new_with_reserved(
            problem.intervals.clone(),
            &problem.regs,
            problem.reserved.clone(),
        );
        scan.set_hints(problem.hints.clone(), problem.hint_exempt.clone());
        let result = scan
            .allocate()
            .map(|result| result.allocation)
            .map_err(|error| error.to_string());
        (
            result,
            scan.spilled_vregs().to_vec(),
            scan.free_pools().clone(),
        )
    }

    /// Reusing a scanner preserves its historical stateful result. The
    /// second call moves A from X0 to X1 before B evicts it; a stale X0
    /// holding would assign B differently and spuriously spill D.
    #[test]
    fn repeated_allocate_preserves_reference_allocations_and_spills() {
        let intervals: Vec<_> = [(0, 0, 100, 3.0), (1, 1, 2, 4.0), (2, 3, 100, 2.0)]
            .into_iter()
            .map(|(id, start, end, weight)| {
                let mut interval = LiveInterval::new(VReg::new(id, RegClass::Gpr64));
                interval.add_range(start, end);
                interval.spill_weight = weight;
                interval
            })
            .collect();
        let regs = BTreeMap::from([(RegClass::Gpr64, vec![PReg::new(0), PReg::new(1)])]);
        let mut current = LinearScan::new(intervals.clone(), &regs);
        let mut reference =
            crate::linear_scan_reference::ReferenceLinearScan::new(intervals, &regs);
        for call in 0..2 {
            let actual = current.allocate().expect("current allocation").allocation;
            let expected = reference
                .allocate()
                .expect("reference allocation")
                .allocation;
            assert_eq!(actual, expected, "allocation call {call}");
            assert_eq!(
                current.spilled_vregs(),
                reference.spilled_vregs(),
                "spills call {call}"
            );
            assert_eq!(
                current.free_pools(),
                reference.free_pools(),
                "pools call {call}"
            );
            if call == 0 {
                assert!(current.spilled_vregs().is_empty());
            } else {
                assert_eq!(
                    actual,
                    BTreeMap::from([
                        (VReg::new(1, RegClass::Gpr64), PReg::new(1)),
                        (VReg::new(2, RegClass::Gpr64), PReg::new(1)),
                    ])
                );
                assert_eq!(
                    current.spilled_vregs(),
                    &[VReg::new(2, RegClass::Gpr64), VReg::new(0, RegClass::Gpr64),]
                );
            }
        }
    }

    /// The indexed allocator returns what the allocator it replaced returns
    /// (`linear_scan_reference`, verbatim): the same allocation, the same
    /// spilled VRegs in the same order and the same free pools, on 3,000
    /// generated problems with distinct VRegs (the holdings path) and 1,000
    /// with repeated ones (the literal path), and the literal path agrees
    /// with the holdings path too.
    #[test]
    fn indexed_linear_scan_matches_the_reference_allocator() {
        let mut stream = Stream(0x9e37_79b9_7f4a_7c15);
        let mut spilled = 0usize;
        let mut evictions_possible = 0usize;
        for case in 0..4_000 {
            let repeat_vregs = case >= 3_000;
            let problem = generate(&mut stream, repeat_vregs);
            let reference = run_reference(&problem);
            let indexed = run_indexed(&problem, true);
            let literal = run_indexed(&problem, false);
            assert_eq!(indexed, reference, "case {case}: holdings path");
            assert_eq!(literal, reference, "case {case}: literal path");
            spilled += reference.1.len();
            evictions_possible += usize::from(!reference.1.is_empty());
        }
        // The problems exercise the blocked path, not only free registers.
        assert!(spilled > 20_000, "{spilled}");
        assert!(evictions_possible > 1_500, "{evictions_possible}");
    }

    /// One long block of short, overlapping values, as the stack-tuple block
    /// of the L14-P6 report allocates: `n` values live three positions each,
    /// with `pressure` more constants materialized early and used late, on
    /// the aarch64 register file.
    fn spill_block(n: usize, pressure: usize) -> Vec<LiveInterval> {
        let mut intervals = Vec::with_capacity(n * (1 + pressure));
        let mut id = 0u32;
        for step in 0..n as u32 {
            let base = step * 4;
            let mut value = LiveInterval::new(VReg::new(id, RegClass::Gpr64));
            value.add_range(base, base + 3);
            value.spill_weight = 2.0;
            intervals.push(value);
            id += 1;
            for early in 0..pressure as u32 {
                let mut constant = LiveInterval::new(VReg::new(id, RegClass::Gpr64));
                constant.add_range(base + 1, base + 40 + early);
                constant.spill_weight = 1.0 / f64::from(early + 1);
                intervals.push(constant);
                id += 1;
            }
        }
        intervals
    }

    /// Cost bound (L14-P6): allocating a block that keeps every register
    /// busy examines a bounded number of active-set holdings per interval,
    /// so the work grows linearly with the block. Charged units are the
    /// holdings and active entries the overlap questions examine
    /// (`scan_work`). The literal scans of `active` and `allocation` charge
    /// the same units per entry; routed back through them, the eviction
    /// search examines `registers * active` entries per blocked interval.
    #[test]
    fn blocked_allocation_cost_grows_linearly() {
        let regs = aarch64_allocatable_regs();
        let work = |n: usize, holders: bool| -> (u64, usize) {
            let mut scan = LinearScan::new(spill_block(n, 8), &regs);
            if !holders {
                scan = scan.without_holders();
            }
            let ((), units) = crate::scan_work::measure(|| {
                scan.allocate().expect("allocates");
            });
            (units, scan.spilled_vregs().len())
        };
        crate::scan_work::assert_near_linear("blocked linear-scan allocation", 64, |n| {
            work(n, true).0
        });
        // Per interval, the holdings path examines far fewer entries than
        // the literal scans it replaced on the same input.
        let (indexed, spilled) = work(1_024, true);
        let (literal, literal_spilled) = work(1_024, false);
        eprintln!(
            "blocked linear-scan allocation, 1,024 steps: {spilled} spilled; holdings {indexed} \
             units, literal {literal} units"
        );
        assert_eq!(spilled, literal_spilled);
        assert!(spilled > 1_000, "the block is register-bound: {spilled}");
        assert!(
            indexed * 4 < literal,
            "holdings {indexed} units against literal {literal}"
        );
    }

    /// The eviction search's holdings path picks what the literal scan picks
    /// when active intervals hold overlapping registers (`Xn` and `Wn` at
    /// once, or one register twice), with the holdings compared one by one
    /// and through the overlap lists. The allocator never builds such an
    /// active set itself, so the generated problems above never reach the
    /// branch that finds two holders of one candidate; the sets are made by
    /// hand, as `test_blocked_alloc_does_not_evict_into_active_alias` makes
    /// one.
    #[test]
    fn blocked_spill_candidate_matches_the_literal_scan_on_overlapping_holdings() {
        let mut stream = Stream(0x5eed_a11a_5c0f_fee5);
        let full = aarch64_allocatable_regs();
        let (mut shared_direct, mut shared_listed, mut chosen) = (0usize, 0usize, 0usize);
        for case in 0..3_000 {
            let keep = 1 + stream.next(8) as usize;
            let regs: BTreeMap<RegClass, Vec<PReg>> = full
                .iter()
                .map(|(&class, pool)| (class, pool.iter().copied().take(keep).collect()))
                .collect();
            let classes: Vec<RegClass> = regs.keys().copied().collect();
            let active = 2 + stream.next(24) as usize;
            let mut intervals = Vec::with_capacity(active + 1);
            let mut held = Vec::with_capacity(active);
            for id in 0..=active {
                let class = classes[stream.next(classes.len() as u32) as usize];
                let mut interval = LiveInterval::new(VReg {
                    id: id as u32,
                    class,
                });
                interval.add_range(0, 100);
                interval.spill_weight = f64::from(stream.next(20));
                interval.is_fixed = id < active && stream.chance(10);
                if id < active {
                    let pool = &regs[&class];
                    held.push((interval.vreg, pool[stream.next(pool.len() as u32) as usize]));
                }
                intervals.push(interval);
            }
            let current = active;
            let current_class = intervals[current].vreg.class;
            let scan_for = |holders: bool| {
                let mut scan = LinearScan::new(intervals.clone(), &regs);
                if !holders {
                    scan = scan.without_holders();
                }
                for &(vreg, preg) in &held {
                    scan.allocation.insert(vreg, preg);
                }
                scan.set_active((0..active).collect());
                scan
            };
            let indexed = scan_for(true);
            let literal = scan_for(false);
            let holders = indexed
                .holders
                .as_ref()
                .expect("distinct VRegs keep holdings");
            let shared = regs[&current_class]
                .iter()
                .any(|&candidate| holders.overlapping(candidate, 3, &regs) >= 2);
            if shared {
                if holders.by_register.len() <= DIRECT_HOLDINGS_SCAN {
                    shared_direct += 1;
                } else {
                    shared_listed += 1;
                }
            }
            let expected = literal.blocked_spill_candidate(current);
            assert_eq!(
                indexed.blocked_spill_candidate(current),
                expected,
                "case {case}"
            );
            chosen += usize::from(expected.is_some());
        }
        assert!(
            shared_direct > 200 && shared_listed > 200,
            "{shared_direct} direct, {shared_listed} listed"
        );
        assert!(chosen > 500, "{chosen}");
    }
}
