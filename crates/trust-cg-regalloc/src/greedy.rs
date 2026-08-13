// trust-cg-regalloc/greedy.rs - Greedy register allocator
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Greedy register allocator (Phase 2).
//!
//! LLVM-style greedy allocator that processes live intervals by spill weight
//! (highest first) and uses eviction, splitting, and cascade limiting for
//! better code quality than the linear scan allocator.
//!
//! ## Algorithm Overview
//!
//! 1. **Priority queue**: intervals are processed in decreasing spill weight
//!    order.  High-weight intervals (hot loops, frequently used values) get
//!    first pick of registers.
//!
//! 2. **Register hints**: when available, the allocator tries hint registers
//!    (from coalescing or ABI conventions) before scanning the full set.
//!
//! 3. **Interference checking**: for each candidate physical register, we
//!    check whether any already-assigned interval overlaps the current one.
//!
//! 4. **Eviction**: when no register is free, the allocator finds the
//!    lowest-weight interfering interval.  If its weight is less than the
//!    current interval's weight, it evicts the interferer and re-enqueues
//!    it for later processing.
//!
//! 5. **Cascade limiting**: each eviction assigns a *cascade number* to the
//!    evicted interval.  An interval can only be evicted by a strictly
//!    higher cascade number, preventing infinite eviction loops.  The
//!    maximum cascade depth is configurable (default 10).
//!
//! 6. **Splitting**: before giving up and spilling, the allocator tries to
//!    split the interval around its largest gap.  Both halves are
//!    re-enqueued as new intervals.
//!
//! 7. **Spilling**: intervals that cannot be assigned, evicted, or split
//!    are marked for spilling.
//!
//! ## Stage Progression
//!
//! Each interval progresses through stages:
//! `New -> Evict -> Split -> Spill -> Done`
//!
//! An interval only attempts eviction in the `New`/`Evict` stages, splitting
//! in the `Split` stage, and is spilled in the `Spill` stage.
//!
//! Reference: LLVM `RegAllocGreedy.cpp`
//!            Poletto & Sarkar, "Linear Scan Register Allocation" (1999)

use crate::linear_scan::{AllocError, AllocationResult};
use crate::liveness::{LiveInterval, LiveRange};
use crate::machine_types::{MachFunction, PReg, RegClass, VReg};
use crate::split;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap};

// ---------------------------------------------------------------------------
// Sub-register aliasing support (issue #336)
// ---------------------------------------------------------------------------

/// Maximum number of aliasing physical registers any single `PReg` can have.
///
/// On AArch64 the widest case is an FPR view (V/D/S/H/B) which has at most four
/// other-width aliases. On x86-64 a GPR has a single 32-bit/64-bit counterpart.
/// SP and other registers have none. Four covers every case.
const MAX_ALIASES: usize = 4;

/// A stack-allocated, fixed-capacity container of aliasing physical registers.
///
/// This replaces the per-call `Vec<PReg>` previously returned by
/// [`aliasing_pregs`], which is hot in linear scan. The set of registers it
/// holds is identical to the old `Vec`; only the backing storage changed
/// (inline `[PReg; MAX_ALIASES]` instead of a heap allocation).
///
/// It `Deref`s to `&[PReg]`, so all slice operations used by callers
/// (`len`, indexing, `contains`, iteration over `&AliasVec`) work unchanged,
/// and it implements [`IntoIterator`] by value for `for alias in aliasing_pregs(..)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AliasVec {
    regs: [PReg; MAX_ALIASES],
    len: usize,
}

impl AliasVec {
    #[inline]
    const fn new() -> Self {
        // PReg::new is const; use encoding 0 as a never-read placeholder for
        // the unused tail (only the first `len` entries are ever observable).
        Self {
            regs: [PReg::new(0); MAX_ALIASES],
            len: 0,
        }
    }

    #[inline]
    fn push(&mut self, preg: PReg) {
        debug_assert!(self.len < MAX_ALIASES, "AliasVec capacity exceeded");
        self.regs[self.len] = preg;
        self.len += 1;
    }

    #[inline]
    pub fn as_slice(&self) -> &[PReg] {
        &self.regs[..self.len]
    }
}

impl std::ops::Deref for AliasVec {
    type Target = [PReg];

    #[inline]
    fn deref(&self) -> &[PReg] {
        self.as_slice()
    }
}

impl<'a> IntoIterator for &'a AliasVec {
    type Item = &'a PReg;
    type IntoIter = std::slice::Iter<'a, PReg>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl IntoIterator for AliasVec {
    type Item = PReg;
    type IntoIter = std::iter::Take<std::array::IntoIter<PReg, MAX_ALIASES>>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.regs.into_iter().take(self.len)
    }
}

/// Return true if two allocator PRegs share physical storage.
pub(crate) fn allocator_pregs_overlap(a: PReg, b: PReg) -> bool {
    if crate::x86_adapter::is_x86_preg(a) || crate::x86_adapter::is_x86_preg(b) {
        crate::x86_adapter::x86_pregs_overlap(a, b)
    } else {
        trust_cg_ir::regs::regs_overlap(a, b)
    }
}

/// Returns all physical registers that alias the given register (in different
/// register classes).
///
/// On AArch64, W-registers are the lower 32 bits of X-registers, and
/// D/S/H/B-registers are sub-views of V-registers. On x86-64, E-registers
/// are 32-bit views of R-registers. Writing to any alias clobbers the others,
/// so the allocator must treat them as conflicting.
///
/// Does NOT include the input register itself.
pub fn aliasing_pregs(preg: PReg) -> AliasVec {
    use trust_cg_ir::regs::{
        fpr32_to_fpr128, fpr64_to_fpr128, fpr128_to_fpr8, fpr128_to_fpr16, fpr128_to_fpr32,
        fpr128_to_fpr64, gpr32_to_gpr64, gpr64_to_gpr32,
    };
    if crate::x86_adapter::is_x86_preg(preg) {
        let mut aliases = AliasVec::new();
        for alias in crate::x86_adapter::x86_preg_aliases(preg) {
            if alias != preg {
                aliases.push(alias);
            }
        }
        return aliases;
    }

    let mut aliases = AliasVec::new();
    let e = preg.encoding();
    match e {
        0..=30 => {
            // GPR64 X0-X30 -> alias is the corresponding W register
            if let Some(w) = gpr64_to_gpr32(preg) {
                aliases.push(w);
            }
        }
        32..=62 => {
            // GPR32 W0-W30 -> alias is the corresponding X register
            if let Some(x) = gpr32_to_gpr64(preg) {
                aliases.push(x);
            }
        }
        64..=95 => {
            // FPR128 V0-V31 -> aliases are D, S, H, and B sub-registers.
            if let Some(d) = fpr128_to_fpr64(preg) {
                aliases.push(d);
            }
            if let Some(s) = fpr128_to_fpr32(preg) {
                aliases.push(s);
            }
            if let Some(h) = fpr128_to_fpr16(preg) {
                aliases.push(h);
            }
            if let Some(b) = fpr128_to_fpr8(preg) {
                aliases.push(b);
            }
        }
        96..=127 => {
            // FPR64 D0-D31 -> aliases are V (parent) and narrower siblings.
            if let Some(v) = fpr64_to_fpr128(preg) {
                aliases.push(v);
                if let Some(s) = fpr128_to_fpr32(v) {
                    aliases.push(s);
                }
                if let Some(h) = fpr128_to_fpr16(v) {
                    aliases.push(h);
                }
                if let Some(b) = fpr128_to_fpr8(v) {
                    aliases.push(b);
                }
            }
        }
        128..=159 => {
            // FPR32 S0-S31 -> aliases are V (parent), D, H, and B siblings.
            if let Some(v) = fpr32_to_fpr128(preg) {
                aliases.push(v);
                if let Some(d) = fpr128_to_fpr64(v) {
                    aliases.push(d);
                }
                if let Some(h) = fpr128_to_fpr16(v) {
                    aliases.push(h);
                }
                if let Some(b) = fpr128_to_fpr8(v) {
                    aliases.push(b);
                }
            }
        }
        165..=196 => {
            // FPR16 H0-H31 -> aliases are V/D/S parents and B sibling.
            let v = PReg::new(e - 101);
            aliases.push(v);
            if let Some(d) = fpr128_to_fpr64(v) {
                aliases.push(d);
            }
            if let Some(s) = fpr128_to_fpr32(v) {
                aliases.push(s);
            }
            if let Some(b) = fpr128_to_fpr8(v) {
                aliases.push(b);
            }
        }
        197..=228 => {
            // FPR8 B0-B31 -> aliases are V/D/S/H parents and siblings.
            let v = PReg::new(e - 133);
            aliases.push(v);
            if let Some(d) = fpr128_to_fpr64(v) {
                aliases.push(d);
            }
            if let Some(s) = fpr128_to_fpr32(v) {
                aliases.push(s);
            }
            if let Some(h) = fpr128_to_fpr16(v) {
                aliases.push(h);
            }
        }
        _ => {}
    }
    aliases
}

// ---------------------------------------------------------------------------
// Stage tracking
// ---------------------------------------------------------------------------

/// Allocation stage for a live interval.
///
/// Intervals progress through stages in order; each stage unlocks a
/// different recovery strategy when a free register is unavailable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Stage {
    /// First time in the queue -- try assignment then eviction.
    New = 0,
    /// Failed assignment; try eviction (second chance).
    Evict = 1,
    /// Eviction failed; try splitting.
    Split = 2,
    /// Splitting failed; will be spilled.
    Spill = 3,
    /// Terminal state.
    Done = 4,
}

/// A failed split point recorded while greedy splitting searches for fallback
/// candidates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SplitAttemptFailure {
    pub vreg_id: u32,
    pub split_point: u32,
    pub error: split::SplitError,
}

// ---------------------------------------------------------------------------
// Priority queue entry
// ---------------------------------------------------------------------------

/// An entry in the priority queue, ordered by spill weight (descending).
///
/// We use `total_cmp` for a total order on f64 (NaN-safe).
#[derive(Debug, Clone)]
struct PriorityEntry {
    vreg: VReg,
    weight: f64,
}

impl PartialEq for PriorityEntry {
    fn eq(&self, other: &Self) -> bool {
        self.vreg == other.vreg
    }
}

impl Eq for PriorityEntry {}

impl PartialOrd for PriorityEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PriorityEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // Higher weight = higher priority.  Break ties by lower full VReg
        // identity (deterministic ordering across register classes).
        self.weight
            .total_cmp(&other.weight)
            .then_with(|| other.vreg.cmp(&self.vreg))
    }
}

// ---------------------------------------------------------------------------
// Greedy allocator
// ---------------------------------------------------------------------------

/// LLVM-style greedy register allocator.
///
/// See module-level documentation for algorithm details.
pub struct GreedyAllocator {
    // -- configuration --
    /// Allocatable physical registers per register class.
    allocatable_regs: BTreeMap<RegClass, Vec<PReg>>,
    /// Register hints: preferred physical registers per virtual register.
    hints: BTreeMap<VReg, Vec<PReg>>,
    /// Per `(vreg, hinted register)` instruction positions to EXEMPT from the
    /// reserved-register check when — and only when — evaluating that exact
    /// hint pair: the identity-copy points that relate the two (see
    /// [`Self::set_hint_exempt`]). Empty by default, which reproduces the
    /// historical hint behavior exactly.
    hint_exempt: BTreeMap<(VReg, PReg), Vec<u32>>,
    /// Physical registers reserved at specific instruction positions by
    /// implicit defs, such as call-clobbered ABI registers.
    reserved_regs: BTreeMap<PReg, Vec<u32>>,
    /// Maximum eviction cascade depth (default 10).
    max_cascade_depth: u32,

    // -- per-interval state --
    /// Live intervals keyed by full VReg identity.
    intervals: BTreeMap<VReg, LiveInterval>,
    /// Current VReg -> PReg assignment.
    assignment: BTreeMap<VReg, PReg>,
    /// Reverse map: PReg -> set of VRegs currently assigned to it.
    preg_assignments: BTreeMap<PReg, Vec<VReg>>,
    /// Time-indexed view of `preg_assignments`: for each preg entry (the
    /// assigned preg and each of its aliases), every live range of every
    /// vreg assigned there, keyed by range start -> (range end, vreg).
    ///
    /// Ranges within one entry are pairwise disjoint because the allocator
    /// only assigns a preg after clearing interference on it; that makes
    /// point/overlap queries O(log n) instead of a walk over every assigned
    /// vreg. Disjointness is re-validated on every insert: a segment that
    /// would overlap an existing one goes to `segment_overflow` instead
    /// (scanned linearly, normally empty), so queries stay exact even if
    /// the invariant were ever violated.
    preg_segments: BTreeMap<PReg, BTreeMap<u32, (u32, VReg)>>,
    /// Segments that could not be inserted disjointly (see `preg_segments`).
    segment_overflow: Vec<(PReg, u32, u32, VReg)>,
    /// Cascade number per VReg.
    cascade: BTreeMap<VReg, u32>,
    /// Next cascade number to hand out.
    next_cascade: u32,
    /// Allocation stage per VReg.
    stage: BTreeMap<VReg, Stage>,
    /// VRegs that have been spilled (final output).
    spilled: Vec<VReg>,
    /// Typed failures encountered while trying split candidates.
    split_attempt_failures: Vec<SplitAttemptFailure>,
    /// Main priority queue.
    worklist: BinaryHeap<PriorityEntry>,

    // -- KILL-OR-COMMIT stats recording (docs/per-use-splitting-plan.md) --
    // Inert unless TCG_AY_KILLCOMMIT is set; never affects any allocation
    // decision — it only remembers what the allocator did so the stats probe
    // can embed greedy's realized solution.
    /// Whether to record realized splits (env-gated at construction).
    killcommit_recording: bool,
    /// Realized splits as (vreg id being split, split point).
    killcommit_splits: Vec<(u32, u32)>,
    /// Split parentage: new piece vreg id -> the vreg id it was split from.
    killcommit_parent: BTreeMap<u32, u32>,
}

impl GreedyAllocator {
    /// Create a new greedy allocator.
    ///
    /// * `intervals` -- live intervals computed by liveness analysis.
    /// * `allocatable` -- physical registers available per class.
    /// * `hints` -- optional per-VReg register preferences.
    pub fn new(
        intervals: Vec<LiveInterval>,
        allocatable: &BTreeMap<RegClass, Vec<PReg>>,
        hints: BTreeMap<VReg, Vec<PReg>>,
    ) -> Self {
        Self::new_with_reserved(intervals, allocatable, hints, BTreeMap::new())
    }

    pub fn new_with_reserved(
        intervals: Vec<LiveInterval>,
        allocatable: &BTreeMap<RegClass, Vec<PReg>>,
        hints: BTreeMap<VReg, Vec<PReg>>,
        reserved_regs: BTreeMap<PReg, Vec<u32>>,
    ) -> Self {
        let mut interval_map: BTreeMap<VReg, LiveInterval> = BTreeMap::new();
        let mut worklist = BinaryHeap::new();
        let mut stage_map: BTreeMap<VReg, Stage> = BTreeMap::new();

        for iv in intervals {
            if iv.is_fixed {
                // Fixed intervals are pre-assigned and never enter the queue.
                continue;
            }
            let vreg = iv.vreg;
            worklist.push(PriorityEntry {
                vreg,
                weight: iv.spill_weight,
            });
            stage_map.insert(vreg, Stage::New);
            interval_map.insert(vreg, iv);
        }

        Self {
            allocatable_regs: allocatable.clone(),
            hints,
            hint_exempt: BTreeMap::new(),
            reserved_regs,
            max_cascade_depth: 10,
            intervals: interval_map,
            assignment: BTreeMap::new(),
            preg_assignments: BTreeMap::new(),
            preg_segments: BTreeMap::new(),
            segment_overflow: Vec::new(),
            cascade: BTreeMap::new(),
            next_cascade: 1,
            stage: stage_map,
            worklist,
            spilled: Vec::new(),
            split_attempt_failures: Vec::new(),
            killcommit_recording: crate::killcommit::recording_enabled(),
            killcommit_splits: Vec::new(),
            killcommit_parent: BTreeMap::new(),
        }
    }

    /// Supply the per-`(vreg, hinted register)` identity-copy positions that a
    /// hint for that exact pair may ignore in the RESERVED-register check.
    ///
    /// This is the greedy-side twin of `LinearScan::set_hints`' `hint_exempt`
    /// (see `crate::copy_register_hints`). `implicit_def_reservations` reserves
    /// the destination physical register of every instruction that defs it —
    /// including the ABI copy `Copy x0 <- v` itself — so the copy's own def of
    /// x0 reserves x0 at the copy point and blocks `v` (live there) from ever
    /// being colored x0. But that overlap IS the kill-then-def boundary of the
    /// copy: reading `v` and writing the same physical register at one
    /// instruction is exactly what makes the copy an identity move. Only those
    /// positions, only for that pair, are skipped.
    ///
    /// SCOPE OF THE RELAXATION — it touches the reserved (physical-register
    /// model) check ONLY, and only along the hint path:
    /// * vreg-vs-vreg interference (`interferes_with_preg`) stays at full
    ///   strength, so a hint can never overlay a live value;
    /// * the eviction path ([`Self::try_evict`]) keeps the STRICT check, so a
    ///   hint never buys its register by evicting someone;
    /// * `crate::regalloc_validator` applies the identical carve-out
    ///   (`identity_copy_exempts_reservation`) and still rejects a reservation
    ///   at any NON-copy position, so a wrong allocation fails the compile
    ///   rather than shipping.
    ///
    /// Empty (the default) reproduces the historical behavior byte for byte.
    pub fn set_hint_exempt(&mut self, hint_exempt: BTreeMap<(VReg, PReg), Vec<u32>>) {
        self.hint_exempt = hint_exempt;
    }

    /// Returns typed split failures observed while searching split candidates.
    ///
    /// The allocator keeps this history so callers and focused tests can
    /// distinguish invalid split points from CFG placements that deliberately
    /// fail closed before a later candidate succeeds.
    pub fn split_attempt_failures(&self) -> &[SplitAttemptFailure] {
        &self.split_attempt_failures
    }

    /// Run the greedy allocation algorithm **without** splitting.
    ///
    /// This performs priority-queue-ordered assignment with eviction and
    /// cascade limiting.  Intervals that cannot be assigned are spilled.
    pub fn allocate(&mut self) -> Result<AllocationResult, AllocError> {
        while let Some(entry) = self.worklist.pop() {
            let vreg = entry.vreg;

            // Skip if this interval was already assigned (e.g. re-enqueued
            // after a failed eviction but later assigned via another path).
            if self.is_assigned(vreg) {
                continue;
            }

            // Skip if already spilled in a prior round.
            if self.is_spilled(vreg) {
                continue;
            }

            let current_stage = self.stage.get(&vreg).copied().unwrap_or(Stage::New);
            if current_stage == Stage::Done {
                continue;
            }

            // Step 1: try direct assignment (prefer hints).
            if let Some(preg) = self.try_assign(vreg) {
                self.assign(vreg, preg);
                self.advance_stage(vreg, Stage::Done);
                continue;
            }

            // Step 2: try eviction (only in New/Evict stages).
            if current_stage <= Stage::Evict {
                if let Some(preg) = self.try_evict(vreg) {
                    self.assign(vreg, preg);
                    self.advance_stage(vreg, Stage::Done);
                    continue;
                }
                // Advance to Split stage for next attempt.
                self.advance_stage(vreg, Stage::Split);
                self.worklist.push(PriorityEntry {
                    vreg,
                    weight: entry.weight,
                });
                continue;
            }

            // Step 3: splitting not available in basic `allocate()`.
            // Advance to Spill.
            if current_stage <= Stage::Split {
                self.advance_stage(vreg, Stage::Spill);
                self.worklist.push(PriorityEntry {
                    vreg,
                    weight: entry.weight,
                });
                continue;
            }

            // Step 4: spill.
            self.do_spill(vreg);
        }

        Ok(self.build_result())
    }

    /// Run the greedy allocation algorithm **with** interval splitting.
    ///
    /// Same as [`allocate`] but before spilling, attempts to split the
    /// interval around its largest gap and re-enqueues both halves.
    pub fn allocate_with_splitting(
        &mut self,
        func: &mut MachFunction,
    ) -> Result<AllocationResult, AllocError> {
        while let Some(entry) = self.worklist.pop() {
            let vreg = entry.vreg;

            if self.is_assigned(vreg) || self.is_spilled(vreg) {
                continue;
            }

            let current_stage = self.stage.get(&vreg).copied().unwrap_or(Stage::New);
            if current_stage == Stage::Done {
                continue;
            }

            // Step 1: try direct assignment.
            if let Some(preg) = self.try_assign(vreg) {
                self.assign(vreg, preg);
                self.advance_stage(vreg, Stage::Done);
                continue;
            }

            // Step 2: try eviction.
            if current_stage <= Stage::Evict {
                if let Some(preg) = self.try_evict(vreg) {
                    self.assign(vreg, preg);
                    self.advance_stage(vreg, Stage::Done);
                    continue;
                }
                self.advance_stage(vreg, Stage::Split);
                self.worklist.push(PriorityEntry {
                    vreg,
                    weight: entry.weight,
                });
                continue;
            }

            // Step 3: try splitting.
            if current_stage == Stage::Split {
                if self.try_split(vreg, func) {
                    // Both halves have been re-enqueued; do not spill.
                    continue;
                }
                self.advance_stage(vreg, Stage::Spill);
                self.worklist.push(PriorityEntry {
                    vreg,
                    weight: entry.weight,
                });
                continue;
            }

            // Step 4: spill.
            self.do_spill(vreg);
        }

        Ok(self.build_result())
    }

    // -----------------------------------------------------------------------
    // Assignment
    // -----------------------------------------------------------------------

    /// Try to assign a free register to `vreg`.
    ///
    /// Checks hint registers first, then the full allocatable set for the
    /// interval's register class.  Returns `Some(preg)` if a non-interfering
    /// register is found.
    fn try_assign(&self, vreg: VReg) -> Option<PReg> {
        let interval = self.intervals.get(&vreg)?;
        let class = interval.vreg.class;
        let allocatable = self.allocatable_regs.get(&class)?;

        // Try hint registers first. A hint is a PREFERENCE: it is checked
        // against the same interference model as any other candidate, with the
        // single identity-copy carve-out described on `set_hint_exempt` (empty
        // exemptions => bit-identical to the historical check).
        if let Some(hint_regs) = self.hints.get(&interval.vreg) {
            for &preg in hint_regs {
                if allocatable.contains(&preg) && !self.hinted_interferes(vreg, preg) {
                    return Some(preg);
                }
            }
        }

        // Try all allocatable registers.
        allocatable
            .iter()
            .find(|&&preg| !self.interferes(vreg, preg))
            .copied()
    }

    /// [`Self::interferes`] for a candidate reached via a HINT: identical except
    /// that the reserved-register check skips the identity-copy positions
    /// recorded for this exact `(vreg, preg)` pair. See [`Self::set_hint_exempt`]
    /// for why that is sound and what stays at full strength.
    fn hinted_interferes(&self, vreg: VReg, preg: PReg) -> bool {
        let Some(interval) = self.intervals.get(&vreg) else {
            return false;
        };
        let exempt = self
            .hint_exempt
            .get(&(vreg, preg))
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        if self.reserved_interferes_except(interval, preg, exempt) {
            return true;
        }
        self.interferes_with_preg(vreg, preg, interval)
    }

    /// Check whether assigning `preg` to `vreg` would interfere with
    /// any interval already assigned to overlapping physical storage.
    fn interferes(&self, vreg: VReg, preg: PReg) -> bool {
        let interval = match self.intervals.get(&vreg) {
            Some(iv) => iv,
            None => return false,
        };

        if self.reserved_interferes(interval, preg) {
            return true;
        }

        self.interferes_with_preg(vreg, preg, interval)
    }

    fn reserved_interferes(&self, interval: &LiveInterval, preg: PReg) -> bool {
        self.reserved_interferes_except(interval, preg, &[])
    }

    /// [`Self::reserved_interferes`] ignoring reservations at the `exempt`
    /// positions. Called with a non-empty `exempt` ONLY from
    /// [`Self::hinted_interferes`]; it can only ever REMOVE interference at
    /// those exact positions, never add any, and `exempt = &[]` is the
    /// unmodified strict check.
    fn reserved_interferes_except(
        &self,
        interval: &LiveInterval,
        preg: PReg,
        exempt: &[u32],
    ) -> bool {
        self.reserved_regs.iter().any(|(&reserved_preg, points)| {
            allocator_pregs_overlap(reserved_preg, preg)
                && points
                    .iter()
                    .any(|&pos| interval.is_live_at(pos) && !exempt.contains(&pos))
        })
    }

    /// Visit every assigned vreg whose physical storage overlaps `preg`
    /// without materializing a deduplicated list. A vreg recorded under
    /// several aliasing pregs is visited more than once, which is harmless
    /// for the boolean "does anything interfere" queries this serves.
    /// Returns true as soon as `f` returns true.
    fn any_assigned_vreg_overlapping(&self, preg: PReg, mut f: impl FnMut(VReg) -> bool) -> bool {
        for (&assigned_preg, assigned_vregs) in &self.preg_assignments {
            if allocator_pregs_overlap(assigned_preg, preg) {
                for &v in assigned_vregs {
                    if f(v) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Check whether any interval assigned to a specific `preg` overlaps `interval`.
    fn interferes_with_preg(&self, vreg: VReg, preg: PReg, interval: &LiveInterval) -> bool {
        for (&key_preg, entry) in &self.preg_segments {
            if !allocator_pregs_overlap(key_preg, preg) {
                continue;
            }
            for r in &interval.ranges {
                // Any segment starting inside [start, end) overlaps; so does
                // a predecessor that reaches past `start`. Entry segments are
                // pairwise disjoint, so no earlier segment can reach further
                // than the predecessor does.
                if entry
                    .range(r.start..r.end)
                    .any(|(_, &(_, seg_vreg))| seg_vreg != vreg)
                {
                    return true;
                }
                if entry
                    .range(..r.start)
                    .next_back()
                    .is_some_and(|(_, &(end, seg_vreg))| end > r.start && seg_vreg != vreg)
                {
                    return true;
                }
            }
        }
        self.segment_overflow
            .iter()
            .any(|&(key_preg, start, end, seg_vreg)| {
                seg_vreg != vreg
                    && allocator_pregs_overlap(key_preg, preg)
                    && interval
                        .ranges
                        .iter()
                        .any(|r| start < r.end && r.start < end)
            })
    }

    /// Collect the distinct vregs (other than `exclude`) assigned to storage
    /// overlapping `preg` whose live intervals time-overlap `interval`,
    /// sorted by VReg order (the order the pre-segment-store code visited
    /// them in).
    fn vregs_interfering_on_preg(
        &self,
        preg: PReg,
        exclude: VReg,
        interval: &LiveInterval,
    ) -> Vec<VReg> {
        let mut found: Vec<VReg> = Vec::new();
        for (&key_preg, entry) in &self.preg_segments {
            if !allocator_pregs_overlap(key_preg, preg) {
                continue;
            }
            for r in &interval.ranges {
                for (_, &(_, seg_vreg)) in entry.range(r.start..r.end) {
                    if seg_vreg != exclude {
                        found.push(seg_vreg);
                    }
                }
                if let Some((_, &(end, seg_vreg))) = entry.range(..r.start).next_back()
                    && end > r.start
                    && seg_vreg != exclude
                {
                    found.push(seg_vreg);
                }
            }
        }
        for &(key_preg, start, end, seg_vreg) in &self.segment_overflow {
            if seg_vreg != exclude
                && allocator_pregs_overlap(key_preg, preg)
                && interval
                    .ranges
                    .iter()
                    .any(|r| start < r.end && r.start < end)
            {
                found.push(seg_vreg);
            }
        }
        found.sort_unstable();
        found.dedup();
        found
    }

    /// Record the assignment of `vreg` to `preg`.
    ///
    /// Also records the assignment against all aliasing registers so that
    /// interference checks on aliased registers will find this interval.
    /// (Issue #336: mixed-width ABI register aliasing.)
    fn assign(&mut self, vreg: VReg, preg: PReg) {
        if self.intervals.contains_key(&vreg) {
            self.assignment.insert(vreg, preg);
        }
        self.preg_assignments.entry(preg).or_default().push(vreg);
        // Also record in aliasing registers.
        for alias in aliasing_pregs(preg) {
            self.preg_assignments.entry(alias).or_default().push(vreg);
        }
        // Mirror the assignment into the time-indexed segment store.
        if let Some(iv) = self.intervals.get(&vreg) {
            let ranges: Vec<LiveRange> = iv.ranges.clone();
            self.add_segments(preg, vreg, &ranges);
            for alias in aliasing_pregs(preg) {
                self.add_segments(alias, vreg, &ranges);
            }
        }
    }

    /// Insert `vreg`'s live ranges into the segment entry for `key_preg`,
    /// diverting any range that would break the entry's disjointness
    /// invariant to `segment_overflow` (queries scan it linearly).
    fn add_segments(&mut self, key_preg: PReg, vreg: VReg, ranges: &[LiveRange]) {
        let entry = self.preg_segments.entry(key_preg).or_default();
        for r in ranges {
            let pred_overlaps = entry
                .range(..r.start)
                .next_back()
                .is_some_and(|(_, &(end, _))| end > r.start);
            let succ_overlaps = entry.range(r.start..r.end).next().is_some();
            if pred_overlaps || succ_overlaps {
                debug_assert!(
                    false,
                    "greedy: overlapping same-storage segments for v{} on {key_preg:?}",
                    vreg.id
                );
                self.segment_overflow.push((key_preg, r.start, r.end, vreg));
            } else {
                entry.insert(r.start, (r.end, vreg));
            }
        }
    }

    /// Remove the assignment of `vreg`.
    ///
    /// Also removes from all aliasing registers.
    /// (Issue #336: mixed-width ABI register aliasing.)
    fn unassign(&mut self, vreg: VReg) {
        if self.intervals.contains_key(&vreg)
            && let Some(preg) = self.assignment.remove(&vreg)
        {
            if let Some(list) = self.preg_assignments.get_mut(&preg) {
                list.retain(|&assigned_vreg| assigned_vreg != vreg);
            }
            // Also remove from aliasing registers.
            for alias in aliasing_pregs(preg) {
                if let Some(list) = self.preg_assignments.get_mut(&alias) {
                    list.retain(|&assigned_vreg| assigned_vreg != vreg);
                }
            }
            // Drop the vreg's segments. Removal is by value (not by the
            // interval's current range starts) so it stays correct even if
            // the interval were mutated while assigned.
            if let Some(entry) = self.preg_segments.get_mut(&preg) {
                entry.retain(|_, &mut (_, seg_vreg)| seg_vreg != vreg);
            }
            for alias in aliasing_pregs(preg) {
                if let Some(entry) = self.preg_segments.get_mut(&alias) {
                    entry.retain(|_, &mut (_, seg_vreg)| seg_vreg != vreg);
                }
            }
            self.segment_overflow
                .retain(|&(_, _, _, seg_vreg)| seg_vreg != vreg);
        }
    }

    fn is_assigned(&self, vreg: VReg) -> bool {
        self.intervals.contains_key(&vreg) && self.assignment.contains_key(&vreg)
    }

    fn is_spilled(&self, vreg: VReg) -> bool {
        self.intervals.contains_key(&vreg) && self.spilled.contains(&vreg)
    }

    // -----------------------------------------------------------------------
    // Eviction
    // -----------------------------------------------------------------------

    /// Try to evict a lower-weight interval to make room for `vreg`.
    ///
    /// For each allocatable register, collects all interfering intervals.
    /// If every interferer has a lower spill weight and a cascade number
    /// lower than the current interval's, the interferers are evicted and
    /// the register is returned.
    fn try_evict(&mut self, vreg: VReg) -> Option<PReg> {
        let interval = self.intervals.get(&vreg)?;
        let class = interval.vreg.class;
        let weight = interval.spill_weight;
        let my_cascade = self.cascade.get(&vreg).copied().unwrap_or(0);

        let allocatable = self.allocatable_regs.get(&class)?.clone();

        // Try hint registers first for eviction too.
        let hint_regs: Vec<PReg> = self.hints.get(&interval.vreg).cloned().unwrap_or_default();

        let candidates: Vec<PReg> = hint_regs
            .iter()
            .chain(allocatable.iter())
            .copied()
            .collect();

        let mut best_preg: Option<PReg> = None;
        let mut best_evict_cost: f64 = f64::MAX;

        for &preg in &candidates {
            if !allocatable.contains(&preg) {
                continue;
            }
            if self.reserved_interferes(interval, preg) {
                continue;
            }

            if !self.any_assigned_vreg_overlapping(preg, |_| true) {
                // No assignments -- free register (should have been
                // caught by try_assign, but handle gracefully).
                return Some(preg);
            }

            // Collect interferers for this preg.
            let mut interferers: Vec<(VReg, f64, u32)> = Vec::new(); // (vreg, weight, cascade)
            let mut can_evict = true;
            let mut total_cost = 0.0_f64;

            for other_vreg in self.vregs_interfering_on_preg(preg, vreg, interval) {
                if let Some(other_iv) = self.intervals.get(&other_vreg) {
                    let other_weight = other_iv.spill_weight;
                    let other_cascade = self.cascade.get(&other_vreg).copied().unwrap_or(0);

                    // Cannot evict a heavier interval.
                    if other_weight >= weight {
                        can_evict = false;
                        break;
                    }
                    // Cannot evict if cascade would be exceeded.
                    if other_cascade >= my_cascade && my_cascade >= self.max_cascade_depth {
                        can_evict = false;
                        break;
                    }

                    total_cost += other_weight;
                    interferers.push((other_vreg, other_weight, other_cascade));
                }
            }

            if can_evict && !interferers.is_empty() && total_cost < best_evict_cost {
                best_evict_cost = total_cost;
                best_preg = Some(preg);
            }
        }

        // Perform the eviction for the best register found.
        if let Some(preg) = best_preg {
            self.evict_interference(preg, vreg);
            return Some(preg);
        }

        None
    }

    /// Evict all intervals assigned to `preg` that interfere with `new_vreg`.
    ///
    /// Evicted intervals are unassigned, get a new cascade number, and are
    /// pushed back onto the worklist.
    fn evict_interference(&mut self, preg: PReg, new_vreg: VReg) {
        let new_cascade = self.next_cascade;
        self.next_cascade += 1;
        self.cascade.insert(new_vreg, new_cascade);

        let interval = match self.intervals.get(&new_vreg) {
            Some(iv) => iv.clone(),
            None => return,
        };

        for other_vreg in self.vregs_interfering_on_preg(preg, new_vreg, &interval) {
            let other_weight = self
                .intervals
                .get(&other_vreg)
                .map_or(0.0, |iv| iv.spill_weight);

            self.unassign(other_vreg);
            self.cascade.insert(other_vreg, new_cascade);
            // Reset stage to Evict so it can try assignment again.
            self.stage.insert(other_vreg, Stage::Evict);
            self.worklist.push(PriorityEntry {
                vreg: other_vreg,
                weight: other_weight,
            });
        }
    }

    // -----------------------------------------------------------------------
    // Splitting
    // -----------------------------------------------------------------------

    /// Try to split `vreg`'s interval using multiple strategies.
    ///
    /// Strategies are attempted in order of increasing aggressiveness:
    /// 1. **Gap-based**: split at the midpoint of gaps between consecutive
    ///    use/def positions, trying lower-ranked gaps if the best point is
    ///    rejected as invalid or CFG-unsafe.
    /// 2. **Interference-aware**: find where register pressure is highest
    ///    and split just before that region, keeping the first half in a
    ///    register.
    /// 3. **Per-use**: split between consecutive use/def positions,
    ///    creating short intervals that are easy to allocate individually.
    ///
    /// If any strategy succeeds, both halves are inserted into the
    /// interval map and enqueued on the worklist.  Returns `true` if
    /// a split was performed.
    fn try_split(&mut self, vreg: VReg, func: &mut MachFunction) -> bool {
        let interval = match self.intervals.get(&vreg) {
            Some(iv) => iv.clone(),
            None => return false,
        };

        let mut attempted = BTreeSet::new();

        // Strategy 1: gap-based split (least aggressive, best quality).
        for split_point in Self::gap_split_points_by_quality(&interval) {
            if attempted.insert(split_point)
                && self.try_split_at(vreg, &interval, split_point, func)
            {
                return true;
            }
        }

        // Strategy 2: interference-aware split.
        if let Some(interference_start) = self.find_interference_start(vreg)
            && let Some(split_point) =
                split::find_split_near_interference(&interval, interference_start)
            && attempted.insert(split_point)
            && self.try_split_at(vreg, &interval, split_point, func)
        {
            return true;
        }

        // Strategy 3: per-use split (most aggressive).
        let per_use_splits = split::find_per_use_split_points(&interval);
        for (split_point, _weight) in per_use_splits {
            if attempted.insert(split_point)
                && self.try_split_at(vreg, &interval, split_point, func)
            {
                return true;
            }
        }

        false
    }

    pub(crate) fn gap_split_points_by_quality(interval: &LiveInterval) -> Vec<u32> {
        let mut positions: Vec<u32> = interval
            .use_positions
            .iter()
            .chain(interval.def_positions.iter())
            .copied()
            .collect();
        positions.sort_unstable();
        positions.dedup();

        let mut candidates: Vec<(u32, u32)> = positions
            .windows(2)
            .filter_map(|window| {
                let gap = window[1].saturating_sub(window[0]);
                if gap < 2 {
                    return None;
                }

                let split_point = window[0] + gap / 2;
                (split_point > interval.start() && split_point < interval.end())
                    .then_some((gap, split_point))
            })
            .collect();
        candidates.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
        candidates.dedup_by_key(|(_, split_point)| *split_point);

        candidates
            .into_iter()
            .map(|(_, split_point)| split_point)
            .collect()
    }

    fn try_split_at(
        &mut self,
        vreg: VReg,
        interval: &LiveInterval,
        split_point: u32,
        func: &mut MachFunction,
    ) -> bool {
        match split::split_interval_checked(interval, split_point, func) {
            Ok(result) => {
                if self.killcommit_recording {
                    // Stats-only (docs/per-use-splitting-plan.md): remember the
                    // realized split point + piece parentage. Positions are in
                    // the phase-5-entry numbering (the split machinery skips
                    // its own inserted copies when interpreting positions).
                    self.killcommit_splits.push((vreg.id, split_point));
                    self.killcommit_parent.insert(result.new_vreg.id, vreg.id);
                }
                self.apply_split(vreg, result);
                true
            }
            Err(error) => {
                self.split_attempt_failures.push(SplitAttemptFailure {
                    vreg_id: vreg.id,
                    split_point,
                    error,
                });
                false
            }
        }
    }

    /// Apply a split result: remove the old interval, insert both halves,
    /// and enqueue them on the worklist.
    fn apply_split(&mut self, vreg: VReg, result: split::SplitResult) {
        // Remove the old interval.
        self.intervals.remove(&vreg);
        self.stage.remove(&vreg);

        // Insert the original (truncated) half.
        let orig_vreg = result.original_vreg;
        let orig_weight = result.original_interval.spill_weight;
        self.intervals.insert(orig_vreg, result.original_interval);
        self.stage.insert(orig_vreg, Stage::New);
        self.worklist.push(PriorityEntry {
            vreg: orig_vreg,
            weight: orig_weight,
        });

        // Insert the new half.
        let new_vreg = result.new_vreg;
        let new_weight = result.new_interval.spill_weight;
        self.intervals.insert(new_vreg, result.new_interval);
        self.stage.insert(new_vreg, Stage::New);
        self.worklist.push(PriorityEntry {
            vreg: new_vreg,
            weight: new_weight,
        });
    }

    // -----------------------------------------------------------------------
    // Interference analysis (for splitting)
    // -----------------------------------------------------------------------

    /// Find the earliest point where all allocatable registers for
    /// `vreg`'s class are occupied by other assigned intervals.
    ///
    /// This identifies where register pressure is highest, guiding
    /// the interference-aware split strategy.  Returns `None` if
    /// there is no fully-blocked point (meaning direct assignment
    /// should have succeeded).
    fn find_interference_start(&self, vreg: VReg) -> Option<u32> {
        let interval = self.intervals.get(&vreg)?;
        let class = interval.vreg.class;
        let allocatable = self.allocatable_regs.get(&class)?;

        for range in &interval.ranges {
            for pos in range.start..range.end {
                let all_interfere = allocatable
                    .iter()
                    .all(|&preg| self.is_occupied_at(preg, pos, vreg));
                if all_interfere {
                    return Some(pos);
                }
            }
        }

        None
    }

    /// Check whether a physical register is occupied at a specific
    /// program point by any interval other than `exclude_vreg_id`.
    fn is_occupied_at(&self, preg: PReg, pos: u32, exclude_vreg: VReg) -> bool {
        if self.reserved_regs.iter().any(|(&reserved_preg, points)| {
            allocator_pregs_overlap(reserved_preg, preg) && points.contains(&pos)
        }) {
            return true;
        }

        // Segments within an entry are pairwise disjoint, so at most one can
        // contain `pos`: the one with the greatest start <= pos.
        for (&key_preg, entry) in &self.preg_segments {
            if !allocator_pregs_overlap(key_preg, preg) {
                continue;
            }
            if entry
                .range(..=pos)
                .next_back()
                .is_some_and(|(_, &(end, seg_vreg))| end > pos && seg_vreg != exclude_vreg)
            {
                return true;
            }
        }
        self.segment_overflow
            .iter()
            .any(|&(key_preg, start, end, seg_vreg)| {
                seg_vreg != exclude_vreg
                    && allocator_pregs_overlap(key_preg, preg)
                    && start <= pos
                    && pos < end
            })
    }

    // -----------------------------------------------------------------------
    // Spilling
    // -----------------------------------------------------------------------

    /// Mark `vreg` as spilled.
    fn do_spill(&mut self, vreg: VReg) {
        if let Some(iv) = self.intervals.get(&vreg) {
            self.spilled.push(iv.vreg);
        }
        self.advance_stage(vreg, Stage::Done);
    }

    /// Return the list of spilled VRegs.
    pub fn spilled_vregs(&self) -> &[VReg] {
        &self.spilled
    }

    /// KILL-OR-COMMIT (stats-only): fold the final allocation state back onto
    /// the ORIGINAL (root) vregs — realized split points + final pieces with
    /// their locations — for the per-use-splitting stats probe to embed.
    /// Read-only over the allocator; only called when the harness env is set
    /// (or from tests).
    pub(crate) fn killcommit_record(&self) -> crate::killcommit::GreedyRecord {
        use crate::killcommit::{GreedyPiece, GreedyRecord};
        let root_of = |mut id: u32| -> u32 {
            while let Some(&p) = self.killcommit_parent.get(&id) {
                id = p;
            }
            id
        };
        let mut rec = GreedyRecord::default();
        for (vreg, iv) in &self.intervals {
            if iv.ranges.is_empty() || iv.is_fixed {
                continue;
            }
            let loc = if self.spilled.contains(vreg) {
                None
            } else {
                self.assignment.get(vreg).copied()
            };
            if loc.is_none() {
                rec.spill_pieces += 1;
            }
            rec.pieces
                .entry(root_of(vreg.id))
                .or_default()
                .push(GreedyPiece {
                    start: iv.start(),
                    end: iv.end(),
                    loc,
                });
        }
        for &(vid, pt) in &self.killcommit_splits {
            rec.split_points.entry(root_of(vid)).or_default().push(pt);
        }
        for pieces in rec.pieces.values_mut() {
            pieces.sort_by_key(|p| p.start);
        }
        for pts in rec.split_points.values_mut() {
            pts.sort_unstable();
            pts.dedup();
        }
        rec
    }

    /// Test hook: enable killcommit recording without the env var.
    #[cfg(all(test, feature = "ay-regalloc"))]
    pub(crate) fn killcommit_enable_recording(&mut self) {
        self.killcommit_recording = true;
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /// Advance `vreg` to at least `target` stage.
    fn advance_stage(&mut self, vreg: VReg, target: Stage) {
        let current = self.stage.get(&vreg).copied().unwrap_or(Stage::New);
        if target > current {
            self.stage.insert(vreg, target);
        }
    }

    /// Build the final [`AllocationResult`].
    fn build_result(&self) -> AllocationResult {
        AllocationResult {
            allocation: self.assignment.clone(),
            spills: Vec::new(), // Spill info filled in by insert_spill_code
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::liveness::LiveInterval;
    use crate::machine_types::{
        BlockId, InstFlags, InstId, MachBlock, MachFunction, MachInst, MachOperand, PReg, RegClass,
        VReg,
    };
    use crate::phi_elim;
    use std::collections::BTreeMap;

    // -- helpers --

    fn vreg(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr64,
        }
    }

    fn vreg_class(id: u32, class: RegClass) -> VReg {
        VReg { id, class }
    }

    fn make_interval(id: u32, ranges: &[(u32, u32)], weight: f64) -> LiveInterval {
        make_interval_for(vreg(id), ranges, weight)
    }

    fn make_interval_for(vreg: VReg, ranges: &[(u32, u32)], weight: f64) -> LiveInterval {
        let mut iv = LiveInterval::new(vreg);
        for &(start, end) in ranges {
            iv.add_range(start, end);
        }
        iv.spill_weight = weight;
        // Add use/def positions at range boundaries for split tests.
        if let Some(&(s, _)) = ranges.first() {
            iv.def_positions.push(s);
        }
        for &(_, e) in ranges {
            iv.use_positions.push(e.saturating_sub(1));
        }
        iv
    }

    fn one_gpr_regs() -> BTreeMap<RegClass, Vec<PReg>> {
        let mut m = BTreeMap::new();
        m.insert(RegClass::Gpr64, vec![PReg::new(0)]);
        m
    }

    fn two_gpr_regs() -> BTreeMap<RegClass, Vec<PReg>> {
        let mut m = BTreeMap::new();
        m.insert(RegClass::Gpr64, vec![PReg::new(0), PReg::new(1)]);
        m
    }

    fn many_gpr_regs() -> BTreeMap<RegClass, Vec<PReg>> {
        let mut m = BTreeMap::new();
        // 26 GPR64 regs matching AArch64.
        let regs: Vec<PReg> = (0u16..=15).chain(19u16..=28).map(PReg::new).collect();
        m.insert(RegClass::Gpr64, regs);
        m
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

    // -- tests --

    #[test]
    fn test_greedy_simple_allocation() {
        // Two overlapping intervals, 26 GPRs -> both allocated.
        let intervals = vec![
            make_interval(0, &[(0, 10)], 1.0),
            make_interval(1, &[(5, 15)], 2.0),
        ];
        let regs = many_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 2);
        let p0 = result.allocation[&vreg(0)];
        let p1 = result.allocation[&vreg(1)];
        assert_ne!(p0, p1);
        assert!(alloc.spilled.is_empty());
    }

    #[test]
    fn test_greedy_reserved_reg_point_avoids_live_interval() {
        let intervals = vec![make_interval(0, &[(0, 10)], 1.0)];
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0), PReg::new(19)]);

        let mut reserved = BTreeMap::new();
        reserved.insert(PReg::new(0), vec![5]);

        let mut alloc =
            GreedyAllocator::new_with_reserved(intervals, &regs, BTreeMap::new(), reserved);
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation[&vreg(0)], PReg::new(19));
        assert!(alloc.spilled.is_empty());
    }

    #[test]
    fn test_greedy_reserved_alias_point_avoids_live_interval() {
        let intervals = vec![make_interval(0, &[(0, 10)], 1.0)];
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let mut reserved = BTreeMap::new();
        reserved.insert(PReg::new(32), vec![5]); // W0 aliases X0.

        let mut alloc =
            GreedyAllocator::new_with_reserved(intervals, &regs, BTreeMap::new(), reserved);
        let result = alloc.allocate().unwrap();

        assert!(result.allocation.is_empty());
        assert_eq!(alloc.spilled.len(), 1);
    }

    #[test]
    fn test_greedy_non_overlapping_same_reg() {
        // Two non-overlapping intervals with 1 reg -> both get the same reg.
        let intervals = vec![
            make_interval(0, &[(0, 5)], 1.0),
            make_interval(1, &[(5, 10)], 1.0),
        ];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 2);
        assert_eq!(result.allocation[&vreg(0)], result.allocation[&vreg(1)]);
    }

    #[test]
    fn test_greedy_eviction() {
        // 3 overlapping intervals, only 1 register.
        // Weights: v0=1.0, v1=5.0, v2=3.0 (all overlap [0,10)).
        // v1 (highest weight) processes first, gets the register.
        // v2 tries eviction but v1 is heavier -> cannot evict.
        // v0 tries eviction but v1 is heavier -> cannot evict.
        // v2 and v0 are spilled.
        let intervals = vec![
            make_interval(0, &[(0, 10)], 1.0),
            make_interval(1, &[(0, 10)], 5.0),
            make_interval(2, &[(0, 10)], 3.0),
        ];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // v1 wins the register.
        assert!(result.allocation.contains_key(&vreg(1)));
        // v0 and v2 are spilled.
        assert_eq!(alloc.spilled.len(), 2);
        let spilled_ids: Vec<u32> = alloc.spilled.iter().map(|v| v.id).collect();
        assert!(spilled_ids.contains(&0));
        assert!(spilled_ids.contains(&2));
    }

    #[test]
    fn test_greedy_eviction_low_weight_evicted() {
        // 2 overlapping intervals, 1 register.
        // v0 (weight=1.0) goes first by queue ordering but v1 (weight=5.0)
        // has higher priority.  v1 should evict v0.
        let intervals = vec![
            make_interval(0, &[(0, 10)], 1.0),
            make_interval(1, &[(0, 10)], 5.0),
        ];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // v1 (higher weight) should be assigned.
        assert!(result.allocation.contains_key(&vreg(1)));
        // v0 (lower weight) should be spilled.
        assert_eq!(alloc.spilled.len(), 1);
        assert_eq!(alloc.spilled[0].id, 0);
    }

    #[test]
    fn test_greedy_cascade_limit() {
        // Create a chain of intervals with decreasing weights and 1 register.
        // Each evicts the previous. With max_cascade_depth=3, eviction
        // should stop after 3 levels.
        let intervals = vec![
            make_interval(0, &[(0, 20)], 1.0),
            make_interval(1, &[(0, 20)], 2.0),
            make_interval(2, &[(0, 20)], 3.0),
            make_interval(3, &[(0, 20)], 4.0),
            make_interval(4, &[(0, 20)], 5.0),
        ];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        alloc.max_cascade_depth = 3;
        let result = alloc.allocate().unwrap();

        // The highest weight interval (v4) should be assigned.
        assert!(result.allocation.contains_key(&vreg(4)));
        // The rest should be spilled.
        assert_eq!(alloc.spilled.len(), 4);
    }

    #[test]
    fn test_greedy_with_hints() {
        // Two non-overlapping intervals.  v0 has a hint for PReg(5).
        let intervals = vec![
            make_interval(0, &[(0, 5)], 1.0),
            make_interval(1, &[(5, 10)], 1.0),
        ];
        let regs = many_gpr_regs();
        let mut hints = BTreeMap::new();
        hints.insert(vreg(0), vec![PReg::new(5)]);

        let mut alloc = GreedyAllocator::new(intervals, &regs, hints);
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 2);
        // v0 should have received its hint register.
        assert_eq!(result.allocation[&vreg(0)], PReg::new(5));
    }

    /// A hint toward a register that is RESERVED inside the interval is refused
    /// without an exemption, and honored once the reserving position is named as
    /// this exact pair's identity-copy point. This is the whole ABI-biasing
    /// mechanism: the ABI copy `Copy x0 <- v` reserves x0 at its own position,
    /// which would otherwise permanently block v from ever being colored x0.
    #[test]
    fn hint_exemption_unblocks_only_the_named_copy_position() {
        let hinted = PReg::new(5);
        let build = |exempt: Option<Vec<u32>>| {
            let intervals = vec![make_interval(0, &[(0, 5)], 1.0)];
            let regs = many_gpr_regs();
            let mut hints = BTreeMap::new();
            hints.insert(vreg(0), vec![hinted]);
            let mut reserved = BTreeMap::new();
            // The copy's own def of the hinted register, at pos 3, inside [0,5).
            reserved.insert(hinted, vec![3u32]);
            let mut alloc = GreedyAllocator::new_with_reserved(intervals, &regs, hints, reserved);
            if let Some(points) = exempt {
                let mut m = BTreeMap::new();
                m.insert((vreg(0), hinted), points);
                alloc.set_hint_exempt(m);
            }
            alloc.allocate().unwrap().allocation[&vreg(0)]
        };

        assert_ne!(
            build(None),
            hinted,
            "with no exemption the reserved position must block the hint (the historical behavior)"
        );
        assert_eq!(
            build(Some(vec![3])),
            hinted,
            "naming pos 3 as this pair's identity-copy point must let the hint through"
        );
        assert_ne!(
            build(Some(vec![4])),
            hinted,
            "an exemption at a DIFFERENT position must not unblock pos 3"
        );
    }

    /// The exemption relaxes the RESERVED-register model only. Interference with
    /// a real live vreg already assigned to the hinted register is untouched, so
    /// a hint can never overlay another value.
    #[test]
    fn hint_exemption_never_overrides_a_live_vreg() {
        let hinted = PReg::new(0);
        // v1 has the higher weight, so greedy assigns it first and takes PReg(0)
        // (the first register in the pool). v0 overlaps it and is hinted there.
        let intervals = vec![
            make_interval(0, &[(0, 10)], 1.0),
            make_interval(1, &[(0, 10)], 9.0),
        ];
        let regs = many_gpr_regs();
        let mut hints = BTreeMap::new();
        hints.insert(vreg(0), vec![hinted]);
        let mut alloc = GreedyAllocator::new(intervals, &regs, hints);
        let mut m = BTreeMap::new();
        // Exempt EVERY position in the range; it must still change nothing,
        // because vreg-vs-vreg interference is not part of the reserved model.
        m.insert((vreg(0), hinted), (0..10).collect::<Vec<u32>>());
        alloc.set_hint_exempt(m);
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation[&vreg(1)], hinted);
        assert_ne!(
            result.allocation[&vreg(0)],
            hinted,
            "the exemption must not let a hint share a register with a live vreg"
        );
    }

    /// Exemptions are keyed by `(vreg, preg)`. A vreg copied into several ABI
    /// registers must not let one register borrow another's copy-point
    /// exemption — the hazard the pair keying exists for.
    #[test]
    fn hint_exemption_is_specific_to_its_physical_register() {
        let p0 = PReg::new(0);
        let p1 = PReg::new(1);
        let intervals = vec![make_interval(0, &[(0, 8)], 1.0)];
        let regs = many_gpr_regs();
        let mut hints = BTreeMap::new();
        hints.insert(vreg(0), vec![p0, p1]);
        let mut reserved = BTreeMap::new();
        reserved.insert(p0, vec![2u32]);
        reserved.insert(p1, vec![4u32]);
        let mut alloc = GreedyAllocator::new_with_reserved(intervals, &regs, hints, reserved);
        // Only p1's copy point is exempt. p0 is hinted FIRST but stays blocked.
        let mut m = BTreeMap::new();
        m.insert((vreg(0), p1), vec![4u32]);
        alloc.set_hint_exempt(m);
        let result = alloc.allocate().unwrap();

        assert_eq!(
            result.allocation[&vreg(0)],
            p1,
            "p0 must not borrow p1's exemption; only the pair that owns the copy point is unblocked"
        );
    }

    #[test]
    fn test_greedy_spill_when_no_eviction_possible() {
        // All overlapping, all same weight, 1 register -> only first wins.
        let intervals = vec![
            make_interval(0, &[(0, 10)], 1.0),
            make_interval(1, &[(0, 10)], 1.0),
            make_interval(2, &[(0, 10)], 1.0),
        ];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // Exactly one should be allocated.
        assert_eq!(result.allocation.len(), 1);
        // Two should be spilled.
        assert_eq!(alloc.spilled.len(), 2);
    }

    #[test]
    fn test_greedy_split_before_spill() {
        // An interval [0, 20) with uses at 2 and 18.  Large gap in the
        // middle.  With only 1 register and an overlapping interval [8,12),
        // splitting should produce two halves that can each fit.
        let mut iv0 = LiveInterval::new(vreg(0));
        iv0.add_range(0, 20);
        iv0.spill_weight = 3.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![2, 18];

        let iv1 = make_interval(1, &[(8, 12)], 5.0);

        let intervals = vec![iv0, iv1];
        let regs = two_gpr_regs();
        let mut func = make_test_func(20);

        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate_with_splitting(&mut func).unwrap();

        // After splitting, all halves should be assignable (2 regs, and the
        // split halves don't fully overlap).  No spills expected.
        assert!(
            alloc.spilled.is_empty(),
            "expected no spills but got {} spills: {:?}",
            alloc.spilled.len(),
            alloc.spilled
        );
        // We should have allocations for: v1, plus the two halves of v0.
        assert!(result.allocation.len() >= 2);
    }

    #[test]
    fn test_greedy_many_intervals_no_spill() {
        // 10 non-overlapping intervals with 26 regs -> all allocated.
        let intervals: Vec<LiveInterval> = (0..10)
            .map(|i| make_interval(i, &[(i * 5, i * 5 + 3)], 1.0))
            .collect();
        let regs = many_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 10);
        assert!(alloc.spilled.is_empty());
    }

    #[test]
    fn test_greedy_high_pressure_spill() {
        // 30 simultaneously-live intervals with 26 GPRs.
        let intervals: Vec<LiveInterval> = (0..30)
            .map(|i| make_interval(i, &[(0, 100)], (i + 1) as f64))
            .collect();
        let regs = many_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // At most 26 can be assigned.
        assert!(result.allocation.len() <= 26);
        // At least 4 must be spilled.
        assert!(alloc.spilled.len() >= 4);
        // The lowest-weight intervals should be spilled.
        for v in &alloc.spilled {
            // Spilled intervals should have weight <= 26.0 (the cutoff for 26 regs).
            // The top-26 weights are 5..30, so spilled weights should be 1..4.
            assert!(
                v.id < 26,
                "expected low-weight interval to be spilled, got v{}",
                v.id
            );
        }
    }

    #[test]
    fn test_greedy_fixed_intervals_skipped() {
        // Fixed intervals are skipped (not enqueued).
        let mut iv0 = make_interval(0, &[(0, 10)], 1.0);
        iv0.is_fixed = true;

        let iv1 = make_interval(1, &[(0, 10)], 2.0);

        let intervals = vec![iv0, iv1];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // Only v1 should be in the allocation (v0 is fixed, skipped).
        assert_eq!(result.allocation.len(), 1);
        assert!(result.allocation.contains_key(&vreg(1)));
    }

    #[test]
    fn test_greedy_empty_intervals() {
        let intervals: Vec<LiveInterval> = Vec::new();
        let regs = many_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        assert!(result.allocation.is_empty());
        assert!(alloc.spilled.is_empty());
    }

    #[test]
    fn test_priority_entry_ordering() {
        // Higher weight = higher priority.
        let a = PriorityEntry {
            vreg: vreg(0),
            weight: 1.0,
        };
        let b = PriorityEntry {
            vreg: vreg(1),
            weight: 5.0,
        };
        assert!(b > a);

        // Equal weight: lower full VReg identity = higher priority.
        let c = PriorityEntry {
            vreg: vreg(2),
            weight: 5.0,
        };
        assert!(b > c);
    }

    // =====================================================================
    // Additional coverage tests
    // =====================================================================

    #[test]
    fn test_basic_allocation_no_spills() {
        // 4 non-overlapping intervals with 2 registers.
        // Each pair shares a register since they don't overlap.
        let intervals = vec![
            make_interval(0, &[(0, 5)], 1.0),
            make_interval(1, &[(5, 10)], 1.0),
            make_interval(2, &[(10, 15)], 1.0),
            make_interval(3, &[(15, 20)], 1.0),
        ];
        let regs = two_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 4);
        assert!(
            alloc.spilled.is_empty(),
            "no spills expected with non-overlapping intervals"
        );
    }

    #[test]
    fn test_allocation_requiring_spills_more_live_than_regs() {
        // 3 simultaneously-live intervals with only 2 registers.
        // The lowest-weight one must be spilled.
        let intervals = vec![
            make_interval(0, &[(0, 20)], 1.0),
            make_interval(1, &[(0, 20)], 3.0),
            make_interval(2, &[(0, 20)], 5.0),
        ];
        let regs = two_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // Top-2 weights get assigned.
        assert_eq!(result.allocation.len(), 2);
        assert!(result.allocation.contains_key(&vreg(1)));
        assert!(result.allocation.contains_key(&vreg(2)));
        // Lowest weight is spilled.
        assert_eq!(alloc.spilled.len(), 1);
        assert_eq!(alloc.spilled[0].id, 0);
    }

    #[test]
    fn test_interference_graph_correctness() {
        // Test that the allocator correctly detects interference between
        // overlapping intervals and assigns different registers.
        let intervals = vec![
            make_interval(0, &[(0, 10)], 1.0),
            make_interval(1, &[(5, 15)], 1.0),
            make_interval(2, &[(10, 20)], 1.0),
        ];
        let regs = two_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // v0 and v1 overlap -> different regs.
        let p0 = result.allocation[&vreg(0)];
        let p1 = result.allocation[&vreg(1)];
        assert_ne!(p0, p1, "overlapping intervals must get different regs");

        // v1 and v2 overlap -> different regs.
        let p2 = result.allocation[&vreg(2)];
        assert_ne!(p1, p2, "overlapping intervals must get different regs");

        // v0 and v2 do NOT overlap (0..10 and 10..20 are adjacent, not overlapping)
        // so they CAN share a register.
        assert!(alloc.spilled.is_empty());
    }

    #[test]
    fn test_spill_weight_determines_spill_victim() {
        // 5 overlapping intervals, 2 registers. The 3 lowest-weight
        // intervals should be spilled.
        let intervals = vec![
            make_interval(0, &[(0, 100)], 10.0),
            make_interval(1, &[(0, 100)], 50.0),
            make_interval(2, &[(0, 100)], 30.0),
            make_interval(3, &[(0, 100)], 20.0),
            make_interval(4, &[(0, 100)], 40.0),
        ];
        let regs = two_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // Top-2 by weight: v1 (50.0) and v4 (40.0)
        assert_eq!(result.allocation.len(), 2);
        assert!(
            result.allocation.contains_key(&vreg(1)),
            "highest weight should be allocated"
        );
        assert!(
            result.allocation.contains_key(&vreg(4)),
            "second highest should be allocated"
        );

        // The other 3 should be spilled.
        assert_eq!(alloc.spilled.len(), 3);
        let spilled_ids: Vec<u32> = alloc.spilled.iter().map(|v| v.id).collect();
        assert!(spilled_ids.contains(&0));
        assert!(spilled_ids.contains(&2));
        assert!(spilled_ids.contains(&3));
    }

    #[test]
    fn test_call_clobber_handling_live_across_call() {
        // Simulate live range across a call instruction.
        // v0 spans the entire function including a "call" at instruction 10.
        // v1 only spans post-call. With 1 register, eviction should
        // keep the higher-weight one.
        let intervals = vec![
            make_interval(0, &[(0, 20)], 2.0),  // crosses "call" at 10
            make_interval(1, &[(10, 20)], 5.0), // starts at call
        ];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // v1 has higher weight, so it gets the register.
        assert!(result.allocation.contains_key(&vreg(1)));
        // v0 must be spilled (lower weight, can't share the register).
        assert_eq!(alloc.spilled.len(), 1);
        assert_eq!(alloc.spilled[0].id, 0);
    }

    #[test]
    fn test_multiple_register_classes_independent() {
        // GPR and FPR intervals use disjoint PReg sets and don't interfere.
        // AArch64 encoding: GPR64 = PReg 0-30, FPR64 = PReg 96-127.
        let gpr_iv = {
            let mut iv = LiveInterval::new(VReg {
                id: 0,
                class: RegClass::Gpr64,
            });
            iv.add_range(0, 10);
            iv.spill_weight = 1.0;
            iv.def_positions.push(0);
            iv.use_positions.push(9);
            iv
        };
        let fpr_iv = {
            let mut iv = LiveInterval::new(VReg {
                id: 1,
                class: RegClass::Fpr64,
            });
            iv.add_range(0, 10);
            iv.spill_weight = 1.0;
            iv.def_positions.push(0);
            iv.use_positions.push(9);
            iv
        };

        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);
        regs.insert(RegClass::Fpr64, vec![PReg::new(96)]); // D0 — disjoint from GPR

        let intervals = vec![gpr_iv, fpr_iv];
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // Both should be allocated to their respective class registers.
        assert_eq!(result.allocation.len(), 2);
        assert!(alloc.spilled.is_empty());
    }

    #[test]
    fn test_same_id_different_register_classes_are_distinct() {
        let gpr = vreg_class(0, RegClass::Gpr64);
        let fpr = vreg_class(0, RegClass::Fpr64);
        let intervals = vec![
            make_interval_for(gpr, &[(0, 10)], 1.0),
            make_interval_for(fpr, &[(0, 10)], 1.0),
        ];

        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);
        regs.insert(RegClass::Fpr64, vec![PReg::new(96)]);

        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        assert_eq!(alloc.intervals.len(), 2);
        assert!(alloc.intervals.contains_key(&gpr));
        assert!(alloc.intervals.contains_key(&fpr));

        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 2);
        assert_eq!(result.allocation[&gpr], PReg::new(0));
        assert_eq!(result.allocation[&fpr], PReg::new(96));
        assert!(alloc.spilled.is_empty());
    }

    #[test]
    fn test_spilled_same_id_peer_does_not_skip_allocatable_class() {
        let gpr = vreg_class(0, RegClass::Gpr64);
        let fpr = vreg_class(0, RegClass::Fpr64);
        let intervals = vec![
            make_interval_for(fpr, &[(0, 10)], 10.0),
            make_interval_for(gpr, &[(0, 10)], 1.0),
        ];

        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]);

        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 1);
        assert_eq!(result.allocation[&gpr], PReg::new(0));
        assert!(!result.allocation.contains_key(&fpr));
        assert_eq!(alloc.spilled, vec![fpr]);
        assert!(!alloc.is_spilled(gpr));
    }

    #[test]
    fn test_eviction_cascade_respects_weight_ordering() {
        // Chain: v0(1.0) assigned first, v1(2.0) evicts v0,
        // v2(3.0) evicts v1, etc. All overlapping, 1 register.
        let intervals = vec![
            make_interval(0, &[(0, 10)], 1.0),
            make_interval(1, &[(0, 10)], 2.0),
            make_interval(2, &[(0, 10)], 3.0),
        ];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // The highest weight (v2) should win.
        assert!(result.allocation.contains_key(&vreg(2)));
        assert_eq!(alloc.spilled.len(), 2);
    }

    #[test]
    fn test_hint_conflicts_with_existing_allocation() {
        // v0 gets PReg(0). v1 has a hint for PReg(0) but overlaps v0,
        // so it should fall back to PReg(1).
        let intervals = vec![
            make_interval(0, &[(0, 10)], 5.0),
            make_interval(1, &[(0, 10)], 3.0),
        ];
        let regs = two_gpr_regs();
        let mut hints = BTreeMap::new();
        hints.insert(vreg(1), vec![PReg::new(0)]);

        let mut alloc = GreedyAllocator::new(intervals, &regs, hints);
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 2);
        // Both should be allocated to different regs despite the hint conflict.
        let p0 = result.allocation[&vreg(0)];
        let p1 = result.allocation[&vreg(1)];
        assert_ne!(p0, p1);
    }

    #[test]
    fn test_single_instruction_interval() {
        // An interval that spans exactly one instruction.
        let intervals = vec![make_interval(0, &[(5, 6)], 1.0)];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 1);
        assert!(alloc.spilled.is_empty());
    }

    #[test]
    fn test_interleaved_intervals_no_overlap() {
        // Intervals that alternate: v0=[0,5), v1=[5,10), v2=[10,15), etc.
        // All should fit in 1 register.
        let intervals: Vec<LiveInterval> = (0..5)
            .map(|i| make_interval(i, &[(i * 5, i * 5 + 5)], 1.0))
            .collect();
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 5);
        assert!(alloc.spilled.is_empty());
        // All should get the same register.
        let preg0 = result.allocation[&vreg(0)];
        for i in 1..5 {
            assert_eq!(result.allocation[&vreg(i)], preg0);
        }
    }

    #[test]
    fn test_stage_progression_new_to_done() {
        // Verify that a successfully allocated interval goes from New to Done.
        let intervals = vec![make_interval(0, &[(0, 5)], 1.0)];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let _ = alloc.allocate().unwrap();

        // After allocation, the stage should be Done.
        assert_eq!(*alloc.stage.get(&vreg(0)).unwrap(), Stage::Done);
    }

    #[test]
    fn test_spilled_vregs_accessor() {
        // 2 overlapping same-weight intervals, 1 register.
        let intervals = vec![
            make_interval(0, &[(0, 10)], 1.0),
            make_interval(1, &[(0, 10)], 1.0),
        ];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let _ = alloc.allocate().unwrap();

        // One gets allocated, one gets spilled.
        let spilled = alloc.spilled_vregs();
        assert_eq!(spilled.len(), 1);
        assert_eq!(spilled[0].class, RegClass::Gpr64);
    }

    #[test]
    fn test_max_cascade_depth_zero_disables_eviction() {
        // With max_cascade_depth=0, eviction should be impossible.
        let intervals = vec![
            make_interval(0, &[(0, 10)], 1.0),
            make_interval(1, &[(0, 10)], 5.0),
        ];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        alloc.max_cascade_depth = 0;
        let result = alloc.allocate().unwrap();

        // v1 gets allocated first (higher priority). v0 cannot evict
        // because cascade depth is 0, so it spills.
        assert!(result.allocation.contains_key(&vreg(1)));
        assert_eq!(alloc.spilled.len(), 1);
        assert_eq!(alloc.spilled[0].id, 0);
    }

    #[test]
    fn test_disjoint_live_ranges_same_vreg() {
        // An interval with multiple disjoint ranges (hole in the middle).
        let intervals = vec![
            make_interval(0, &[(0, 5), (15, 20)], 1.0),
            make_interval(1, &[(5, 15)], 2.0),
        ];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // The two intervals don't overlap (v0 has a hole where v1 lives).
        assert_eq!(result.allocation.len(), 2);
        assert!(alloc.spilled.is_empty());
    }

    #[test]
    fn test_greedy_all_same_weight_deterministic_spill_order() {
        // 4 overlapping intervals with identical weight and 2 registers.
        // The allocator should be deterministic: lower vreg_id breaks ties
        // in the priority queue (higher priority for lower id with same weight).
        let intervals = vec![
            make_interval(0, &[(0, 20)], 3.0),
            make_interval(1, &[(0, 20)], 3.0),
            make_interval(2, &[(0, 20)], 3.0),
            make_interval(3, &[(0, 20)], 3.0),
        ];
        let regs = two_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // Exactly 2 should be allocated, 2 spilled.
        assert_eq!(result.allocation.len(), 2);
        assert_eq!(alloc.spilled.len(), 2);
    }

    #[test]
    fn test_greedy_hundred_non_overlapping_one_register() {
        // 100 sequential non-overlapping intervals should all fit in 1 register.
        let intervals: Vec<LiveInterval> = (0..100)
            .map(|i| make_interval(i, &[(i * 10, i * 10 + 5)], 1.0))
            .collect();
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        assert_eq!(result.allocation.len(), 100);
        assert!(alloc.spilled.is_empty());
        // All should share the single register.
        let preg0 = result.allocation[&vreg(0)];
        for i in 1..100 {
            assert_eq!(result.allocation[&vreg(i)], preg0);
        }
    }

    // =====================================================================
    // Live range splitting tests (issue #332)
    // =====================================================================

    #[test]
    fn test_greedy_split_at_interference() {
        // v0: [0, 20) with uses at 0, 5, 10, 15, 19 (no large gap for
        // gap-based split). v1: [4, 12) weight 10.0 (blocks the middle).
        // 2 registers. After eviction fails (v1 heavier), splitting v0
        // around interference should produce two halves.
        let mut iv0 = LiveInterval::new(vreg(0));
        iv0.add_range(0, 20);
        iv0.spill_weight = 2.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![5, 10, 15, 19];

        let iv1 = make_interval(1, &[(4, 12)], 10.0);

        let intervals = vec![iv0, iv1];
        let regs = two_gpr_regs();
        let mut func = make_test_func(20);

        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate_with_splitting(&mut func).unwrap();

        // Should complete without panic and account for all original intervals.
        let total = result.allocation.len() + alloc.spilled.len();
        assert!(total >= 2, "all original intervals should be accounted for");
    }

    #[test]
    fn test_greedy_per_use_split() {
        // An interval with many closely-spaced uses and high pressure.
        // Two blockers occupy both registers over different halves.
        let mut iv0 = LiveInterval::new(vreg(0));
        iv0.add_range(0, 30);
        iv0.spill_weight = 1.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![3, 7, 12, 18, 25, 29];

        let iv1 = make_interval(1, &[(0, 15)], 5.0);
        let iv2 = make_interval(2, &[(10, 30)], 5.0);

        let intervals = vec![iv0, iv1, iv2];
        let regs = two_gpr_regs();
        let mut func = make_test_func(30);

        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let _result = alloc.allocate_with_splitting(&mut func).unwrap();

        // Verify allocation completed (may have spills, that's OK).
        // The key is that splitting was attempted before spilling.
    }

    #[test]
    fn test_split_near_interference_from_greedy() {
        // Test find_split_near_interference via the split module.
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 20);
        iv.use_positions = vec![2, 8, 15];
        iv.def_positions = vec![0];

        let sp = split::find_split_near_interference(&iv, 10);
        assert!(sp.is_some());
        assert_eq!(
            sp.unwrap(),
            9,
            "should split at 9 (after last use at 8 before interference at 10)"
        );
    }

    #[test]
    fn test_per_use_split_points_from_greedy() {
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 30);
        iv.use_positions = vec![3, 7, 15, 25];
        iv.def_positions = vec![0];

        let splits = split::find_per_use_split_points(&iv);
        assert!(!splits.is_empty(), "should find split points between uses");

        for (sp, _weight) in &splits {
            assert!(*sp > iv.start());
            assert!(*sp < iv.end());
        }

        // Sorted by weight descending (largest gaps first).
        if splits.len() >= 2 {
            assert!(
                splits[0].1 >= splits[1].1,
                "splits should be sorted by weight descending"
            );
        }
    }

    #[test]
    fn test_apply_split_helper() {
        // Test that apply_split properly re-enqueues both halves.
        let iv0 = make_interval(0, &[(0, 20)], 3.0);
        let intervals = vec![iv0.clone()];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());

        let mut func = make_test_func(20);
        let result = split::split_interval(&iv0, 10, &mut func).unwrap();

        // Drain the worklist first.
        while alloc.worklist.pop().is_some() {}

        alloc.apply_split(vreg(0), result);

        // Both halves should be in the worklist now.
        let mut found = 0;
        while alloc.worklist.pop().is_some() {
            found += 1;
        }
        assert_eq!(found, 2, "both split halves should be enqueued");
    }

    #[test]
    fn test_greedy_split_uses_join_block_start_after_cfg_repair() {
        let mut iv0 = LiveInterval::new(vreg(0));
        iv0.add_range(0, 20);
        iv0.spill_weight = 3.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![10, 18];

        let intervals = vec![iv0.clone()];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let mut func = make_test_func(20);
        func.blocks = vec![
            MachBlock {
                insts: (0..5).map(InstId).collect(),
                preds: Vec::new(),
                succs: vec![BlockId(1), BlockId(2)],
                loop_depth: 0,
            },
            MachBlock {
                insts: (5..20).map(InstId).collect(),
                preds: vec![BlockId(0), BlockId(2)],
                succs: Vec::new(),
                loop_depth: 0,
            },
            MachBlock {
                insts: Vec::new(),
                preds: vec![BlockId(0)],
                succs: vec![BlockId(1)],
                loop_depth: 0,
            },
        ];
        func.block_order = vec![BlockId(0), BlockId(1), BlockId(2)];

        let mut checked_func = func.clone();
        let checked = split::split_interval(&iv0, 5, &mut checked_func)
            .expect("multi-pred block starts can use a join-block-start split copy");
        let checked_copy = checked_func.blocks[1].insts[0];
        assert_eq!(
            checked_func.insts[checked_copy.0 as usize].defs,
            vec![MachOperand::VReg(checked.new_vreg)]
        );

        while alloc.worklist.pop().is_some() {}
        assert!(
            alloc.try_split(vreg(0), &mut func),
            "greedy splitting should use the best repaired join-start gap"
        );

        let original = alloc
            .intervals
            .get(&vreg(0))
            .expect("original split half should remain tracked");
        assert_eq!(
            original.end(),
            6,
            "greedy should choose split point 5 at the repaired join start"
        );
        assert!(original.use_positions.contains(&5));
    }

    #[test]
    fn test_greedy_split_tries_dominating_gap_after_branch_local_cfg_reject() {
        let original = vreg(0);
        let mut iv0 = LiveInterval::new(original);
        iv0.add_range(0, 9);
        iv0.spill_weight = 3.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![2, 7];

        let intervals = vec![iv0.clone()];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let mut func = MachFunction {
            name: "greedy_split_branch_local_reject_fallback".into(),
            insts: vec![
                make_inst(1, &[original], &[]),
                make_branch(&[BlockId(1), BlockId(2)]),
                make_inst(3, &[], &[original]),
                make_inst(4, &[], &[]),
                make_inst(5, &[], &[]),
                make_branch(&[BlockId(3)]),
                make_branch(&[BlockId(3)]),
                make_inst(8, &[], &[original]),
                make_inst(9, &[], &[]),
            ],
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2), InstId(3), InstId(4), InstId(5)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(6)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(7), InstId(8)],
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

        let err = split::split_interval_checked(&iv0, 4, &mut func)
            .expect_err("branch-local split copy should be rejected");
        assert_eq!(
            err,
            split::SplitError::UnsafeCfg(split::SplitCfgSafetyError::NonDominatingPlacement {
                insertion_block: BlockId(1),
                rewrite_block: BlockId(3),
                rewrite_pos: 7,
            }),
            "largest gap is branch-local and must be rejected before greedy falls back"
        );

        while alloc.worklist.pop().is_some() {}
        assert!(
            alloc.try_split(vreg(0), &mut func),
            "greedy splitting should fall back to the entry-block split point that dominates both arms"
        );

        let original_interval = alloc
            .intervals
            .get(&vreg(0))
            .expect("original split half should remain tracked");
        assert_eq!(
            original_interval.end(),
            2,
            "fallback should choose split point 1, not the branch-local point 4"
        );
        assert!(original_interval.use_positions.contains(&1));

        let split_vreg = alloc
            .intervals
            .keys()
            .copied()
            .find(|&candidate| candidate != vreg(0))
            .expect("split-created interval should be tracked");
        let copy_id = func.blocks[0].insts[1];
        assert_eq!(
            func.insts[copy_id.0 as usize].defs,
            vec![MachOperand::VReg(split_vreg)]
        );
        assert_eq!(
            func.insts[copy_id.0 as usize].uses,
            vec![MachOperand::VReg(original)]
        );
        assert_eq!(func.insts[2].uses, vec![MachOperand::VReg(split_vreg)]);
        assert_eq!(func.insts[7].uses, vec![MachOperand::VReg(split_vreg)]);
    }

    #[test]
    fn test_greedy_split_places_safe_join_edge_copies() {
        let original = vreg(0);
        let mut iv0 = LiveInterval::new(original);
        iv0.add_range(0, 9);
        iv0.spill_weight = 3.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![8];

        let intervals = vec![iv0];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let mut func = MachFunction {
            name: "greedy_split_join_edge_copies".into(),
            insts: vec![
                make_inst(1, &[original], &[]),
                make_branch(&[BlockId(1), BlockId(2)]),
                make_branch(&[BlockId(3)]),
                make_branch(&[BlockId(3)]),
                make_inst(5, &[], &[]),
                make_inst(6, &[], &[]),
                make_inst(7, &[], &[]),
                make_inst(8, &[], &[]),
                make_inst(9, &[], &[original]),
            ],
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
                    insts: vec![InstId(4), InstId(5), InstId(6), InstId(7), InstId(8)],
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

        while alloc.worklist.pop().is_some() {}
        assert!(
            alloc.try_split(vreg(0), &mut func),
            "greedy splitting should materialize safe join-start copies on incoming edges"
        );

        let original_interval = alloc
            .intervals
            .get(&vreg(0))
            .expect("original split half should remain tracked");
        assert_eq!(
            original_interval.end(),
            4,
            "the chosen split point should be the join block start"
        );

        let split_vreg = alloc
            .intervals
            .keys()
            .copied()
            .find(|&candidate| candidate != vreg(0))
            .expect("split-created interval should be tracked");
        let arm1_copy = func.blocks[1].insts[0];
        let arm2_copy = func.blocks[2].insts[0];
        assert_eq!(
            func.insts[arm1_copy.0 as usize].opcode,
            crate::phi_elim::PSEUDO_COPY
        );
        assert_eq!(
            func.insts[arm2_copy.0 as usize].opcode,
            crate::phi_elim::PSEUDO_COPY
        );
        assert_eq!(
            func.insts[arm1_copy.0 as usize].defs,
            vec![MachOperand::VReg(split_vreg)]
        );
        assert_eq!(
            func.insts[arm2_copy.0 as usize].uses,
            vec![MachOperand::VReg(original)]
        );
        assert_eq!(func.blocks[1].insts[1], InstId(2));
        assert_eq!(func.blocks[2].insts[1], InstId(3));
        assert_eq!(func.insts[8].uses, vec![MachOperand::VReg(split_vreg)]);
    }

    #[test]
    fn test_greedy_split_places_join_block_start_copy_without_terminator_anchor() {
        let original = vreg(0);
        let mut iv0 = LiveInterval::new(original);
        iv0.add_range(0, 9);
        iv0.spill_weight = 3.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![8];

        let intervals = vec![iv0];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let mut func = MachFunction {
            name: "greedy_split_missing_join_terminator_reject".into(),
            insts: vec![
                make_inst(1, &[original], &[]),
                make_branch(&[BlockId(1), BlockId(2)]),
                make_branch(&[BlockId(3)]),
                make_inst(4, &[], &[]),
                make_inst(5, &[], &[]),
                make_inst(6, &[], &[]),
                make_inst(7, &[], &[]),
                make_inst(8, &[], &[]),
                make_inst(9, &[], &[original]),
            ],
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
                    insts: vec![InstId(4), InstId(5), InstId(6), InstId(7), InstId(8)],
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

        let mut checked_func = func.clone();
        let checked = split::split_interval_checked(
            alloc
                .intervals
                .get(&vreg(0))
                .expect("interval should be present"),
            4,
            &mut checked_func,
        )
        .expect("join-start split should use a block-start copy without an edge anchor");
        let checked_copy = checked_func.blocks[3].insts[0];
        assert_eq!(
            checked_func.insts[checked_copy.0 as usize].opcode,
            phi_elim::PSEUDO_COPY
        );
        assert_eq!(
            checked_func.insts[8].uses,
            vec![MachOperand::VReg(checked.new_vreg)]
        );

        while alloc.worklist.pop().is_some() {}
        assert!(
            alloc.try_split(vreg(0), &mut func),
            "greedy splitting should materialize a join-block-start split copy"
        );

        let original_interval = alloc
            .intervals
            .get(&vreg(0))
            .expect("original split half should remain tracked");
        assert_eq!(
            original_interval.end(),
            5,
            "greedy should choose the join-start split point"
        );
        assert!(original_interval.use_positions.contains(&4));

        let split_vreg = alloc
            .intervals
            .keys()
            .copied()
            .find(|&candidate| candidate != vreg(0))
            .expect("split-created interval should be tracked");
        let copy_id = func.blocks[3].insts[0];
        assert_eq!(
            func.insts[copy_id.0 as usize].defs,
            vec![MachOperand::VReg(split_vreg)]
        );
        assert_eq!(
            func.insts[copy_id.0 as usize].uses,
            vec![MachOperand::VReg(original)]
        );
        assert_eq!(func.insts[8].uses, vec![MachOperand::VReg(split_vreg)]);
    }

    #[test]
    fn test_greedy_split_places_critical_edge_join_block_start_copy() {
        let original = vreg(0);
        let mut iv0 = LiveInterval::new(original);
        iv0.add_range(0, 9);
        iv0.spill_weight = 3.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![8];

        let intervals = vec![iv0];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let mut func = MachFunction {
            name: "greedy_split_critical_edge_join_reject".into(),
            insts: vec![
                make_inst(1, &[original], &[]),
                make_branch(&[BlockId(1), BlockId(2)]),
                make_inst(3, &[], &[]),
                make_branch(&[BlockId(2)]),
                make_inst(5, &[], &[]),
                make_inst(6, &[], &[]),
                make_inst(7, &[], &[]),
                make_inst(8, &[], &[]),
                make_inst(9, &[], &[original]),
            ],
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
                    succs: vec![BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(4), InstId(5), InstId(6), InstId(7), InstId(8)],
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

        let mut checked_func = func.clone();
        let checked = split::split_interval_checked(
            alloc
                .intervals
                .get(&vreg(0))
                .expect("interval should be present"),
            4,
            &mut checked_func,
        )
        .expect("critical-edge join split should use a join-block-start copy");
        let checked_copy = checked_func.blocks[2].insts[0];
        assert_eq!(
            checked_func.insts[checked_copy.0 as usize].opcode,
            phi_elim::PSEUDO_COPY
        );
        assert_eq!(
            checked_func.insts[8].uses,
            vec![MachOperand::VReg(checked.new_vreg)]
        );

        while alloc.worklist.pop().is_some() {}
        assert!(
            alloc.try_split(vreg(0), &mut func),
            "greedy splitting should materialize a critical-edge join-block copy"
        );

        let original_interval = alloc
            .intervals
            .get(&vreg(0))
            .expect("original split half should remain tracked");
        assert_eq!(
            original_interval.end(),
            5,
            "greedy should choose the critical-edge join split point"
        );
        assert!(original_interval.use_positions.contains(&4));

        let split_vreg = alloc
            .intervals
            .keys()
            .copied()
            .find(|&candidate| candidate != vreg(0))
            .expect("split-created interval should be tracked");
        let copy_id = func.blocks[2].insts[0];
        assert_eq!(
            func.insts[copy_id.0 as usize].defs,
            vec![MachOperand::VReg(split_vreg)]
        );
        assert_eq!(
            func.insts[copy_id.0 as usize].uses,
            vec![MachOperand::VReg(original)]
        );
        assert_eq!(func.insts[8].uses, vec![MachOperand::VReg(split_vreg)]);
    }

    #[test]
    fn test_greedy_split_places_non_linear_join_block_start_copy() {
        let original = vreg(0);
        let mut iv0 = LiveInterval::new(original);
        iv0.add_range(0, 8);
        iv0.spill_weight = 3.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![6];

        let intervals = vec![iv0];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let mut func = MachFunction {
            name: "greedy_split_non_linear_join_layout_reject".into(),
            insts: vec![
                make_inst(1, &[original], &[]),
                make_branch(&[BlockId(1), BlockId(2)]),
                make_branch(&[BlockId(3)]),
                make_branch(&[BlockId(3)]),
                make_inst(5, &[], &[]),
                make_inst(6, &[], &[]),
                make_inst(7, &[], &[]),
                make_inst(8, &[], &[original]),
            ],
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
                    insts: vec![InstId(4), InstId(5), InstId(6), InstId(7)],
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

        let mut checked_func = func.clone();
        let checked = split::split_interval_checked(
            alloc
                .intervals
                .get(&vreg(0))
                .expect("interval should be present"),
            3,
            &mut checked_func,
        )
        .expect("non-linear join split should use a join-block-start copy");
        let checked_copy = checked_func.blocks[3].insts[0];
        assert_eq!(
            checked_func.insts[checked_copy.0 as usize].opcode,
            phi_elim::PSEUDO_COPY
        );
        assert_eq!(
            checked_func.insts[7].uses,
            vec![MachOperand::VReg(checked.new_vreg)]
        );

        while alloc.worklist.pop().is_some() {}
        assert!(
            alloc.try_split(vreg(0), &mut func),
            "greedy splitting should materialize a non-linear join-block copy"
        );

        let original_interval = alloc
            .intervals
            .get(&vreg(0))
            .expect("original split half should remain tracked");
        assert_eq!(
            original_interval
                .ranges
                .iter()
                .map(|range| (range.start, range.end))
                .collect::<Vec<_>>(),
            vec![(0, 4), (7, 8)],
            "the original split half should stay live through the later-layout predecessor"
        );
        assert!(original_interval.use_positions.contains(&3));

        let split_vreg = alloc
            .intervals
            .keys()
            .copied()
            .find(|&candidate| candidate != vreg(0))
            .expect("split-created interval should be tracked");
        let copy_id = func.blocks[3].insts[0];
        assert_eq!(
            func.insts[copy_id.0 as usize].defs,
            vec![MachOperand::VReg(split_vreg)]
        );
        assert_eq!(
            func.insts[copy_id.0 as usize].uses,
            vec![MachOperand::VReg(original)]
        );
        assert_eq!(func.insts[7].uses, vec![MachOperand::VReg(split_vreg)]);
    }

    #[test]
    fn test_greedy_split_falls_back_after_loop_header_backedge_reject() {
        let original = vreg(0);
        let mut iv0 = LiveInterval::new(original);
        iv0.add_range(0, 6);
        iv0.spill_weight = 3.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![4];

        let intervals = vec![iv0];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let mut func = MachFunction {
            name: "greedy_split_loop_header_backedge_reject".into(),
            insts: vec![
                make_inst(1, &[original], &[]),
                make_branch(&[BlockId(1)]),
                make_inst(3, &[], &[]),
                make_branch(&[BlockId(2)]),
                make_inst(5, &[], &[original]),
                make_branch(&[BlockId(1)]),
            ],
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
                    insts: vec![InstId(4), InstId(5)],
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

        let err = split::split_interval_checked(
            alloc
                .intervals
                .get(&vreg(0))
                .expect("interval should be present"),
            2,
            &mut func,
        )
        .expect_err("loop-header split must be rejected before greedy fallback");
        assert_eq!(
            err,
            split::SplitError::UnsafeCfg(split::SplitCfgSafetyError::BackedgeCopyPlacement {
                predecessor: BlockId(2),
                successor: BlockId(1),
                copy_pos: 5,
                join_pos: 2,
            })
        );

        while alloc.worklist.pop().is_some() {}
        assert!(
            alloc.try_split(vreg(0), &mut func),
            "greedy splitting should fall back to a preheader split point"
        );

        let original_interval = alloc
            .intervals
            .get(&vreg(0))
            .expect("original split half should remain tracked");
        assert_eq!(
            original_interval.end(),
            2,
            "fallback should choose split point 1, not the loop header point 2"
        );
        assert!(original_interval.use_positions.contains(&1));

        let split_vreg = alloc
            .intervals
            .keys()
            .copied()
            .find(|&candidate| candidate != vreg(0))
            .expect("split-created interval should be tracked");
        let copy_id = func.blocks[0].insts[1];
        assert_eq!(
            func.insts[copy_id.0 as usize].defs,
            vec![MachOperand::VReg(split_vreg)]
        );
        assert_eq!(
            func.insts[copy_id.0 as usize].uses,
            vec![MachOperand::VReg(original)]
        );
        assert_eq!(func.insts[4].uses, vec![MachOperand::VReg(split_vreg)]);
    }

    #[test]
    fn test_greedy_records_loop_cycle_reject_before_fallback() {
        let original = vreg(0);
        let mut iv0 = LiveInterval::new(original);
        iv0.add_range(0, 9);
        iv0.spill_weight = 3.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![2, 8];

        let intervals = vec![iv0];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let mut func = MachFunction {
            name: "greedy_split_records_loop_cycle_reject".into(),
            insts: vec![
                make_inst(1, &[original], &[]),
                make_branch(&[BlockId(1)]),
                make_inst(3, &[], &[original]),
                make_inst(4, &[], &[]),
                make_inst(5, &[], &[]),
                make_branch(&[BlockId(1), BlockId(2)]),
                make_inst(7, &[], &[]),
                make_inst(8, &[], &[]),
                make_inst(9, &[], &[original]),
            ],
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2), InstId(3), InstId(4), InstId(5)],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![InstId(6), InstId(7), InstId(8)],
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

        while alloc.worklist.pop().is_some() {}
        assert!(
            alloc.try_split(vreg(0), &mut func),
            "greedy splitting should record the loop rejection and fall back to a preheader split"
        );

        assert_eq!(
            alloc.split_attempt_failures(),
            &[SplitAttemptFailure {
                vreg_id: 0,
                split_point: 5,
                error: split::SplitError::UnsafeCfg(
                    split::SplitCfgSafetyError::LoopOrBackedgeBlock {
                        block: BlockId(1),
                        point: 5,
                    },
                ),
            }]
        );

        let original_interval = alloc
            .intervals
            .get(&vreg(0))
            .expect("original split half should remain tracked");
        assert_eq!(
            original_interval.end(),
            2,
            "fallback should choose split point 1, not the loop-body point 5"
        );
        assert!(original_interval.use_positions.contains(&1));

        let split_vreg = alloc
            .intervals
            .keys()
            .copied()
            .find(|&candidate| candidate != vreg(0))
            .expect("split-created interval should be tracked");
        let copy_id = func.blocks[0].insts[1];
        assert_eq!(
            func.insts[copy_id.0 as usize].defs,
            vec![MachOperand::VReg(split_vreg)]
        );
        assert_eq!(
            func.insts[copy_id.0 as usize].uses,
            vec![MachOperand::VReg(original)]
        );
        assert_eq!(func.insts[2].uses, vec![MachOperand::VReg(split_vreg)]);
        assert_eq!(func.insts[8].uses, vec![MachOperand::VReg(split_vreg)]);
    }

    #[test]
    fn test_greedy_split_attempts_before_spill() {
        // Verify that splitting is attempted and produces split intervals
        // when there is a large gap.  With 2 registers and a blocker in
        // the middle, the split halves of v0 should be allocable.
        let mut iv0 = LiveInterval::new(vreg(0));
        iv0.add_range(0, 30);
        iv0.spill_weight = 2.0;
        iv0.def_positions = vec![0];
        iv0.use_positions = vec![2, 28];

        let iv1 = make_interval(1, &[(10, 20)], 10.0);

        let intervals = vec![iv0, iv1];
        let regs = two_gpr_regs();
        let mut func = make_test_func(30);

        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate_with_splitting(&mut func).unwrap();

        // With 2 registers, the split halves of v0 don't fully overlap
        // v1, so everything should be allocable without spills.
        assert!(
            alloc.spilled.is_empty(),
            "with 2 regs and a split, expected no spills but got {} spills: {:?}",
            alloc.spilled.len(),
            alloc.spilled
        );
        // v1 plus the two halves of v0 should all be allocated.
        assert!(result.allocation.len() >= 2);
    }

    #[test]
    fn test_split_copy_source_interferes_at_boundary() {
        let mut iv = LiveInterval::new(vreg(0));
        iv.add_range(0, 20);
        iv.spill_weight = 8.0;
        iv.def_positions = vec![0];
        iv.use_positions = vec![19];

        let mut func = make_test_func(20);
        let result = split::split_interval(&iv, 10, &mut func).unwrap();

        assert!(
            result.original_interval.is_live_at(10),
            "split copy source must be live at the split boundary"
        );
        assert!(
            result.original_interval.overlaps(&result.new_interval),
            "split copy source and destination must interfere at the boundary"
        );

        let mut alloc = GreedyAllocator::new(
            vec![result.original_interval, result.new_interval],
            &one_gpr_regs(),
            BTreeMap::new(),
        );
        let alloc_result = alloc.allocate().unwrap();

        assert_eq!(
            alloc_result.allocation.len(),
            1,
            "one physical register cannot hold both interfering split halves"
        );
        assert_eq!(alloc.spilled.len(), 1);
    }

    #[test]
    fn test_find_interference_start() {
        // Set up an allocator where one register is occupied, then
        // query find_interference_start.
        let iv0 = make_interval(0, &[(0, 20)], 1.0);
        let iv1 = make_interval(1, &[(5, 15)], 5.0);

        let intervals = vec![iv0, iv1];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());

        // Manually assign v1 to the only register.
        alloc.assign(vreg(1), PReg::new(0));

        // v0 should find interference starting at position 5 (where v1 starts).
        let start = alloc.find_interference_start(vreg(0));
        assert!(start.is_some());
        assert_eq!(start.unwrap(), 5);
    }

    #[test]
    fn test_is_occupied_at() {
        let iv0 = make_interval(0, &[(0, 10)], 1.0);
        let iv1 = make_interval(1, &[(3, 8)], 2.0);

        let intervals = vec![iv0, iv1];
        let regs = one_gpr_regs();
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());

        // Assign v1 to PReg(0).
        alloc.assign(vreg(1), PReg::new(0));

        // PReg(0) should be occupied at position 5 (v1 is [3,8)).
        assert!(alloc.is_occupied_at(PReg::new(0), 5, vreg(0)));
        // PReg(0) should NOT be occupied at position 1 (before v1).
        assert!(!alloc.is_occupied_at(PReg::new(0), 1, vreg(0)));
        // PReg(0) should NOT be occupied at position 9 (after v1).
        assert!(!alloc.is_occupied_at(PReg::new(0), 9, vreg(0)));
    }

    // =====================================================================
    // Issue #336: Mixed-width ABI register aliasing tests
    // =====================================================================

    #[test]
    fn test_issue_336_mixed_width_gpr_aliasing() {
        // A Gpr64 interval (i64) and a Gpr32 interval (i32) that are
        // simultaneously live MUST NOT be assigned to aliasing registers
        // (e.g., X0/W0 share the same physical storage).
        let gpr64_iv = {
            let mut iv = LiveInterval::new(VReg {
                id: 0,
                class: RegClass::Gpr64,
            });
            iv.add_range(0, 10);
            iv.spill_weight = 1.0;
            iv.def_positions.push(0);
            iv.use_positions.push(9);
            iv
        };
        let gpr32_iv = {
            let mut iv = LiveInterval::new(VReg {
                id: 1,
                class: RegClass::Gpr32,
            });
            iv.add_range(0, 10);
            iv.spill_weight = 1.0;
            iv.def_positions.push(0);
            iv.use_positions.push(9);
            iv
        };

        // Provide X0 for Gpr64 and W0 for Gpr32 (they alias!).
        // The allocator must NOT assign both — one should be detected as
        // interfering with the other's alias.
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0), PReg::new(1)]); // X0, X1
        regs.insert(RegClass::Gpr32, vec![PReg::new(32), PReg::new(33)]); // W0, W1

        let intervals = vec![gpr64_iv, gpr32_iv];
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // Both should be allocated (we have 2 regs in each class).
        assert_eq!(result.allocation.len(), 2);
        assert!(alloc.spilled.is_empty());

        // Critical: they must NOT alias!
        let p0 = result.allocation[&VReg {
            id: 0,
            class: RegClass::Gpr64,
        }];
        let p1 = result.allocation[&VReg {
            id: 1,
            class: RegClass::Gpr32,
        }];
        assert!(
            !trust_cg_ir::regs::regs_overlap(p0, p1),
            "X register {:?} and W register {:?} must not alias! \
             This is the issue #336 regression.",
            p0,
            p1
        );
    }

    #[test]
    fn test_issue_336_mixed_width_only_one_reg_available() {
        // If we only have X0 for Gpr64 and W0 for Gpr32 (they alias),
        // the allocator cannot assign both simultaneously-live intervals.
        // One must be spilled.
        let gpr64_iv = {
            let mut iv = LiveInterval::new(VReg {
                id: 0,
                class: RegClass::Gpr64,
            });
            iv.add_range(0, 10);
            iv.spill_weight = 2.0;
            iv.def_positions.push(0);
            iv.use_positions.push(9);
            iv
        };
        let gpr32_iv = {
            let mut iv = LiveInterval::new(VReg {
                id: 1,
                class: RegClass::Gpr32,
            });
            iv.add_range(0, 10);
            iv.spill_weight = 1.0;
            iv.def_positions.push(0);
            iv.use_positions.push(9);
            iv
        };

        // Only one physical register pair available: X0/W0 (they alias).
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]); // X0
        regs.insert(RegClass::Gpr32, vec![PReg::new(32)]); // W0 (aliases X0!)

        let intervals = vec![gpr64_iv, gpr32_iv];
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // Cannot both be allocated — one must be spilled.
        assert_eq!(
            result.allocation.len(),
            1,
            "only one can be allocated when registers alias"
        );
        assert_eq!(alloc.spilled.len(), 1, "one must be spilled");
        // The higher-weight interval (v0, weight=2.0) should be allocated.
        assert!(result.allocation.contains_key(&VReg {
            id: 0,
            class: RegClass::Gpr64
        }));
    }

    #[test]
    fn test_issue_336_aliasing_pregs_function() {
        // Verify the aliasing_pregs helper function.
        use super::aliasing_pregs;

        // X0 (PReg(0)) aliases W0 (PReg(32))
        let aliases_x0 = aliasing_pregs(PReg::new(0));
        assert_eq!(aliases_x0.len(), 1);
        assert_eq!(aliases_x0[0], PReg::new(32)); // W0

        // W0 (PReg(32)) aliases X0 (PReg(0))
        let aliases_w0 = aliasing_pregs(PReg::new(32));
        assert_eq!(aliases_w0.len(), 1);
        assert_eq!(aliases_w0[0], PReg::new(0)); // X0

        // X28 (PReg(28)) aliases W28 (PReg(60))
        let aliases_x28 = aliasing_pregs(PReg::new(28));
        assert_eq!(aliases_x28.len(), 1);
        assert_eq!(aliases_x28[0], PReg::new(60)); // W28

        // V0 (PReg(64)) aliases D0, S0, H0, and B0.
        let aliases_v0 = aliasing_pregs(PReg::new(64));
        assert_eq!(aliases_v0.len(), 4);
        assert!(aliases_v0.contains(&PReg::new(96))); // D0
        assert!(aliases_v0.contains(&PReg::new(128))); // S0
        assert!(aliases_v0.contains(&PReg::new(165))); // H0
        assert!(aliases_v0.contains(&PReg::new(197))); // B0

        // D0 (PReg(96)) aliases V0, S0, H0, and B0.
        let aliases_d0 = aliasing_pregs(PReg::new(96));
        assert_eq!(aliases_d0.len(), 4);
        assert!(aliases_d0.contains(&PReg::new(64))); // V0
        assert!(aliases_d0.contains(&PReg::new(128))); // S0
        assert!(aliases_d0.contains(&PReg::new(165))); // H0
        assert!(aliases_d0.contains(&PReg::new(197))); // B0

        // S0 (PReg(128)) aliases V0, D0, H0, and B0.
        let aliases_s0 = aliasing_pregs(PReg::new(128));
        assert_eq!(aliases_s0.len(), 4);
        assert!(aliases_s0.contains(&PReg::new(64))); // V0
        assert!(aliases_s0.contains(&PReg::new(96))); // D0
        assert!(aliases_s0.contains(&PReg::new(165))); // H0
        assert!(aliases_s0.contains(&PReg::new(197))); // B0

        let aliases_h0 = aliasing_pregs(PReg::new(165));
        assert_eq!(aliases_h0.len(), 4);
        assert!(aliases_h0.contains(&PReg::new(64))); // V0
        assert!(aliases_h0.contains(&PReg::new(96))); // D0
        assert!(aliases_h0.contains(&PReg::new(128))); // S0
        assert!(aliases_h0.contains(&PReg::new(197))); // B0

        // SP (PReg(31)) has no aliases in our alias function: encoding 31
        // falls outside 0..=30 (X0-X30) and 32..=62 (W0-W30), so the match
        // returns nothing. SP is not allocatable — this is by design.
        let aliases_sp = aliasing_pregs(PReg::new(31));
        assert_eq!(aliases_sp.len(), 0);
    }

    #[test]
    fn test_issue_336_non_overlapping_mixed_width_ok() {
        // Non-overlapping intervals of different widths CAN share the
        // same physical register pair (no conflict).
        let gpr64_iv = {
            let mut iv = LiveInterval::new(VReg {
                id: 0,
                class: RegClass::Gpr64,
            });
            iv.add_range(0, 5);
            iv.spill_weight = 1.0;
            iv.def_positions.push(0);
            iv.use_positions.push(4);
            iv
        };
        let gpr32_iv = {
            let mut iv = LiveInterval::new(VReg {
                id: 1,
                class: RegClass::Gpr32,
            });
            iv.add_range(5, 10);
            iv.spill_weight = 1.0;
            iv.def_positions.push(5);
            iv.use_positions.push(9);
            iv
        };

        // Only X0/W0 available (they alias, but intervals don't overlap).
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0)]); // X0
        regs.insert(RegClass::Gpr32, vec![PReg::new(32)]); // W0

        let intervals = vec![gpr64_iv, gpr32_iv];
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());
        let result = alloc.allocate().unwrap();

        // Both should be allocated since they don't overlap in time.
        assert_eq!(result.allocation.len(), 2);
        assert!(alloc.spilled.is_empty());
    }

    /// The segment-store interference queries must agree exactly with a
    /// brute-force recomputation from `preg_assignments` + `intervals` (the
    /// pre-segment-store implementation) at every allocator state reachable
    /// through assign/unassign, including eviction churn and aliased pregs.
    #[test]
    fn test_segment_store_matches_brute_force() {
        // Deterministic pseudo-random workload: 60 vregs with 1-3 ranges
        // each, assigned/unassigned against aliased preg pairs.
        let mut state: u64 = 0x9E3779B97F4A7C15;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };

        let mut intervals = Vec::new();
        for id in 0..60u32 {
            let n_ranges = 1 + (next() % 3) as usize;
            let mut ranges = Vec::new();
            let mut pos = (next() % 40) as u32;
            for _ in 0..n_ranges {
                let len = 1 + (next() % 12) as u32;
                ranges.push((pos, pos + len));
                pos += len + 1 + (next() % 9) as u32;
            }
            intervals.push(make_interval(id, &ranges, 1.0 + f64::from(id)));
        }
        let probe_intervals = intervals.clone();

        // X0/W0 and X1/W1: alias pairs exercise the multi-key union.
        let mut regs = BTreeMap::new();
        regs.insert(RegClass::Gpr64, vec![PReg::new(0), PReg::new(1)]);
        let mut alloc = GreedyAllocator::new(intervals, &regs, BTreeMap::new());

        let brute_force =
            |alloc: &GreedyAllocator, preg: PReg, exclude: VReg, iv: &LiveInterval| {
                let mut hits = std::collections::BTreeSet::new();
                for (&assigned_preg, vregs) in &alloc.preg_assignments {
                    if allocator_pregs_overlap(assigned_preg, preg) {
                        for &v in vregs {
                            if v != exclude
                                && alloc
                                    .intervals
                                    .get(&v)
                                    .is_some_and(|other| iv.overlaps(other))
                            {
                                hits.insert(v);
                            }
                        }
                    }
                }
                hits.into_iter().collect::<Vec<_>>()
            };

        let probe_pregs = [PReg::new(0), PReg::new(1), PReg::new(32), PReg::new(33)];
        let mut assigned_now: Vec<VReg> = Vec::new();
        for step in 0..300u32 {
            let choice = next();
            if choice % 3 != 0 || assigned_now.is_empty() {
                // Assign a random not-yet-assigned vreg to a random preg,
                // clearing interference first as every production assign
                // site does (this is the disjointness invariant).
                let v = vreg((next() % 60) as u32);
                if !assigned_now.contains(&v) {
                    let preg = probe_pregs[(next() % 2) as usize];
                    let iv = alloc.intervals.get(&v).unwrap().clone();
                    for other in alloc.vregs_interfering_on_preg(preg, v, &iv) {
                        alloc.unassign(other);
                        assigned_now.retain(|&a| a != other);
                    }
                    alloc.assign(v, preg);
                    assigned_now.push(v);
                }
            } else {
                let idx = (next() as usize) % assigned_now.len();
                let v = assigned_now.swap_remove(idx);
                alloc.unassign(v);
            }

            // Cross-check every query shape the allocator issues.
            let probe_iv = &probe_intervals[(step % 60) as usize];
            for &preg in &probe_pregs {
                let expected = brute_force(&alloc, preg, probe_iv.vreg, probe_iv);
                let got = alloc.vregs_interfering_on_preg(preg, probe_iv.vreg, probe_iv);
                assert_eq!(got, expected, "step {step} preg {preg:?}");
                assert_eq!(
                    alloc.interferes_with_preg(probe_iv.vreg, preg, probe_iv),
                    !expected.is_empty(),
                    "step {step} preg {preg:?} (bool)"
                );
                for pos in [0u32, 7, 19, 33, 61] {
                    let mut expected_occ = false;
                    for (&assigned_preg, vregs) in &alloc.preg_assignments {
                        if allocator_pregs_overlap(assigned_preg, preg) {
                            for &v in vregs {
                                if v != probe_iv.vreg
                                    && alloc
                                        .intervals
                                        .get(&v)
                                        .is_some_and(|other| other.is_live_at(pos))
                                {
                                    expected_occ = true;
                                }
                            }
                        }
                    }
                    assert_eq!(
                        alloc.is_occupied_at(preg, pos, probe_iv.vreg),
                        expected_occ,
                        "step {step} preg {preg:?} pos {pos}"
                    );
                }
            }
        }
        assert!(
            alloc.segment_overflow.is_empty(),
            "assign-after-clearing must never hit the overflow path"
        );
    }
}
