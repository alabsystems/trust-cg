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
//! Current implementation: basic linear scan without interval splitting.
//! Future work (Phase 2): interval splitting, rematerialization, hints.

use crate::liveness::LiveInterval;
use crate::machine_types::{PReg, RegClass, StackSlotId, VReg};
use std::collections::BTreeMap;
use thiserror::Error;
use trust_cg_ir::regs::preg_class;

/// Errors that can occur during register allocation.
#[derive(Debug, Error)]
pub enum AllocError {
    #[error("cannot spill fixed interval for {0}")]
    CannotSpillFixed(String),
    #[error("no allocatable registers for class {0:?}")]
    NoRegistersForClass(RegClass),
    #[error("register allocation failed: {0}")]
    Failed(String),
    #[error("register allocation translation validation failed: {0}")]
    ValidationFailed(String),
}

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

        Self {
            intervals,
            active: Vec::new(),
            _allocatable: target_regs.clone(),
            allocation: BTreeMap::new(),
            spills: Vec::new(),
            free_regs,
            reserved_regs,
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
        let interval = &self.intervals[interval_idx];
        self.reserved_regs.iter().any(|(&reserved_preg, points)| {
            crate::greedy::allocator_pregs_overlap(reserved_preg, preg)
                && points.iter().any(|&pos| interval.is_live_at(pos))
        })
    }

    /// Like [`Self::reserved_interferes`], but ignoring reservations at the
    /// `exempt` positions — the copy points where `preg` is defined by the very
    /// copy that biases this interval toward it (kill-then-def boundary; see
    /// `hint_exempt`). Only used when honoring a hint, and it can only ever
    /// REMOVE interference at those specific positions, never add any.
    fn reserved_interferes_except(&self, interval_idx: usize, preg: PReg, exempt: &[u32]) -> bool {
        let interval = &self.intervals[interval_idx];
        self.reserved_regs.iter().any(|(&reserved_preg, points)| {
            crate::greedy::allocator_pregs_overlap(reserved_preg, preg)
                && points
                    .iter()
                    .any(|&pos| interval.is_live_at(pos) && !exempt.contains(&pos))
        })
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
}

/// Returns the default allocatable registers for AArch64 (Apple calling convention).
///
/// Caller-saved: X0-X15 (excluding X18 which is reserved on Apple).
/// Callee-saved: X19-X28.
/// X29 = FP, X30 = LR, X31 = SP/ZR — not allocatable.
pub fn aarch64_allocatable_regs() -> BTreeMap<RegClass, Vec<PReg>> {
    let mut regs = BTreeMap::new();

    // GPR64: X0-X15, X19-X28 (skip X16-X17 scratch, X18 reserved, X29 FP, X30 LR)
    // PReg encoding: X registers are 0..=30
    let gpr64: Vec<PReg> = (0u16..=15).chain(19u16..=28).map(PReg::new).collect();
    regs.insert(RegClass::Gpr64, gpr64.clone());

    // GPR32: same set (W registers are the lower 32 bits of X registers).
    // PReg encoding: W registers are 32..=62
    let gpr32: Vec<PReg> = (32u16..=47).chain(51u16..=60).map(PReg::new).collect();
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
        // 26 GPRs: X0-X15 (16) + X19-X28 (10) = 26
        assert_eq!(regs[&RegClass::Gpr64].len(), 26);
        // 30 FPR64 regs: D16/D17 are reserved spill scratches.
        assert_eq!(regs[&RegClass::Fpr64].len(), 30);
        assert!(!regs[&RegClass::Fpr64].contains(&PReg::new(112)));
        assert!(!regs[&RegClass::Fpr64].contains(&PReg::new(113)));
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
        scan.active = vec![0, 1];

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
        scan.active = vec![0];
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
        scan.active = vec![0, 1];

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
        scan.active = vec![0];

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
        // GPR32: W0-W15 (16) + W19-W28 (10) = 26
        assert_eq!(regs[&RegClass::Gpr32].len(), 26);
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
}
