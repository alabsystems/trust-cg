// trust-cg-regalloc - AY-PBO optimal register allocation (STAGE 3)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AY-PBO optimal register allocation.
//!
//! This is the first STAGE-3 lane of the "beat-LLVM" plan: an *optimal*
//! register allocator that offloads the assignment/spill decision to the AY
//! pseudo-Boolean optimizer ([`ay_pb`]). AY minimizes total spill cost exactly
//! (min `sum(spill_cost_v * spilled_v)`), where greedy is heuristic and leaves
//! avoidable spills + copies.
//!
//! ## Correctness model (the whole point)
//!
//! AY is **UNTRUSTED**. A wrong AY allocation can NEVER miscompile because it is
//! subject to the exact same gates greedy passes:
//!
//! 1. This module re-checks AY's decoded assignment against the interference /
//!    class / reserved-register invariants it encoded (a solver bug that
//!    violates a constraint is caught here and rejected).
//! 2. The result then flows, unchanged, through the always-on translation
//!    validator ([`crate::regalloc_validator::validate_allocation`]) that
//!    certifies every allocation — greedy or AY — against the SSA input.
//! 3. Downstream, the per-instruction certs + TV-4 `post_regalloc_recheck`
//!    re-certify the final machine stream regardless of which allocator ran.
//!
//! On ANY problem (oversize function, timeout with no feasible incumbent,
//! infeasible base, a self-check failure, or a downstream validator rejection)
//! the caller falls back to the greedy allocation. So the AY path is a pure
//! *quality* lever: it can only ever produce an allocation that is at least as
//! verified as greedy's, or be discarded.
//!
//! ## Gating
//!
//! Compiled only under the `ay-regalloc` cargo feature (default OFF), and even
//! then entered only when the `TCG_AY_REGALLOC` env var is set — an opt-in
//! behind a high `-O` tier, since the PBO solve is a compile-time cost. With the
//! feature off, or the env unset, the pipeline is byte-identical to origin.
//! The PER-SEGMENT live-range-split model (steps 4-6 of
//! docs/ay-regalloc-splitting-plan.md) is a second opt-in on top:
//! `TCG_AY_REGALLOC_SEGMENTS` (requires `TCG_AY_REGALLOC`), default OFF and
//! byte-identical when off.
//!
//! ## Encoding (regalloc as PBO)
//!
//! For each non-fixed virtual register `v` (class `c`) and each allocatable
//! physical register `r` in `c` that no reserved point forbids over `v`'s live
//! range, a boolean `x_{v,r}`. Plus a spill indicator `s_v`.
//!
//! * exactly-one:  `sum_r x_{v,r} + s_v = 1`
//! * interference: for overlapping `v,w` and aliasing pregs `r_v,r_w`,
//!   `~x_{v,r_v} + ~x_{w,r_w} >= 1`  (i.e. `x_{v,r_v} + x_{w,r_w} <= 1`)
//! * move-coalescing: for each copy `d <- s`, a `diff_{d,s}` forced to 1 when
//!   d,s land on different pregs (`diff >= x_{d,r} - x_{s,r}` for each r).
//! * objective:    `min  sum_v traffic(v) * s_v  +  MOVE_W * sum_c diff_c`
//!   where `traffic(v)` is the loop-depth-weighted reload/store count of `v`'s
//!   references (`SPILL_W * 10^depth` per use/def) — the COMMENSURABLE traffic
//!   currency the KILLCOMMIT control measurement (f51f487) used when it proved
//!   strictly-better whole-vreg allocations exist on real corpus functions.
//!   A spill op is ~4x a move; there is deliberately NO lexicographic
//!   spills-dominate-copies scaling (that mismatch is what hid the wins).
//!
//! Spilling is always feasible (an unconstrained `s_v`), so the base formula is
//! never infeasible; the optimizer just searches for the min-cost set of spills.
//!
//! ## Greedy-as-incumbent warm start
//!
//! When the caller passes the baseline (greedy) record, its realized solution
//! is evaluated under the same traffic currency to get `G`, and a HARD
//! constraint `objective <= G-1` is added (the ay-pb
//! `strictly_better_than_incumbent` negated-Ge row, emitted directly — the
//! KILLCOMMIT gadget reused verbatim). The solve therefore starts AT greedy in
//! bound terms and can only improve on it: any model is strictly better than
//! greedy in the shared currency, and an `Unsatisfiable`/`Unknown` result is a
//! clean DECLINE to greedy — never a worse allocation.

use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use ay_pb::{
    PbCdclResult, PbCdclSolver, PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm,
};

use crate::greedy::allocator_pregs_overlap;
use crate::killcommit::GreedyRecord;
use crate::linear_scan::AllocationResult;
use crate::liveness::LiveInterval;
use crate::machine_types::{BlockId, PReg, RegAllocFunction, RegClass, VReg};

/// Environment gate: the AY-PBO allocator is only attempted when this is set.
/// Independent of the cargo feature (which controls whether the code is even
/// compiled in) so the opt-in stays a runtime `-O`-tier decision.
#[must_use]
pub fn enabled() -> bool {
    crate::env_lock::var_os("TCG_AY_REGALLOC").is_some()
}

/// Environment gate for the PER-SEGMENT live-range-split PB model (STAGE 3,
/// live-range-split lane, plan steps 4-6). `TCG_AY_REGALLOC_SEGMENTS` is the
/// primary name; the legacy `TCG_AY_REGALLOC_SPLIT` is honored as an alias (it
/// gated the first cut of the same path). Requires [`enabled`] too — this gate
/// is only consulted inside [`try_allocate`], which the caller only enters
/// under `TCG_AY_REGALLOC`. When BOTH are unset (the default) the AY path is
/// byte-identical to the whole-vreg model (no `func` mutation, no re-solve).
/// When set, the spill-delta vregs are segmented per basic block, the
/// per-segment PB is solved, and the decoded assignment is materialized by
/// splitting — a pure quality lever gated by the identical downstream
/// correctness gates (self-check, always-on translation validator, TV-4,
/// run-both-keep-better) plus the segment-level checks in this module.
#[must_use]
pub fn split_enabled() -> bool {
    crate::env_lock::var_os("TCG_AY_REGALLOC_SEGMENTS").is_some()
        || crate::env_lock::var_os("TCG_AY_REGALLOC_SPLIT").is_some()
}

/// Max distinct live-range segments the split model may introduce before the
/// split path declines (falls back to the whole-vreg result / greedy). Bounds
/// the re-solve instance so the PBO stays tractable on a small box.
pub(crate) fn max_split_segments() -> usize {
    env_usize("TCG_AY_REGALLOC_MAX_SEGMENTS", 200)
}

/// Read a `usize` bound from `var`, falling back to `default`.
pub(crate) fn env_usize(var: &str, default: usize) -> usize {
    crate::env_lock::var(var)
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(default)
}

/// Wall-clock cap for the anytime solve (default 200ms). The best feasible
/// incumbent found within the cap is used; if none is found we fall back.
fn time_cap() -> Duration {
    Duration::from_millis(env_usize("TCG_AY_REGALLOC_MS", 200) as u64)
}

/// Max modeled vregs. Above this we fall back to greedy so the PBO stays
/// tractable on a small box.
pub(crate) fn max_vregs() -> usize {
    env_usize("TCG_AY_REGALLOC_MAX_VREGS", 64)
}

/// Max interfering vreg pairs before bailing (bounds the clause count).
pub(crate) fn max_pairs() -> usize {
    env_usize("TCG_AY_REGALLOC_MAX_PAIRS", 4000)
}

/// Spill-op (reload/store) weight relative to a register move in the
/// commensurable TRAFFIC objective — the KILLCOMMIT currency (a spill op costs
/// ~4x a register move; docs/per-use-splitting-plan.md).
pub(crate) const SPILL_W: i128 = 4;
/// Register-move weight in the traffic objective.
pub(crate) const MOVE_W: i128 = 1;

/// Loop-depth factor: `10^depth` (capped) — the same base the KILLCOMMIT
/// control measurement used, so "hot" means the same thing here as in the data
/// that motivated this objective.
pub(crate) fn depth_factor(depth: u32) -> i128 {
    10i128.pow(depth.min(4))
}

/// Position -> loop-depth factor lookup over the linear instruction numbering
/// (the numbering `compute_live_intervals` assigns). Positions outside every
/// block span (e.g. synthetic intervals in unit tests, or an empty function)
/// get factor 1 — the traffic cost degrades to a flat per-reference count.
pub(crate) struct DepthMap {
    /// `(start, end, factor)` per non-empty block span, ascending by start.
    spans: Vec<(u32, u32, i128)>,
}

impl DepthMap {
    pub(crate) fn new(func: &RegAllocFunction) -> Self {
        let spans = block_spans(func)
            .into_iter()
            .map(|(b, s, e)| {
                let depth = func
                    .blocks
                    .get(b.0 as usize)
                    .map_or(0, |blk| blk.loop_depth);
                (s, e, depth_factor(depth))
            })
            .collect();
        DepthMap { spans }
    }

    /// The loop-depth factor of the block containing `pos` (1 if none does).
    pub(crate) fn factor_at(&self, pos: u32) -> i128 {
        self.spans
            .binary_search_by(|&(s, e, _)| {
                if e <= pos {
                    std::cmp::Ordering::Less
                } else if s > pos {
                    std::cmp::Ordering::Greater
                } else {
                    std::cmp::Ordering::Equal
                }
            })
            .map_or(1, |i| self.spans[i].2)
    }
}

/// Loop-depth-weighted spill TRAFFIC of an interval if spilled: every def is a
/// store and every use a reload (`SPILL_W` each), weighted by the loop-depth
/// factor of the reference position. This replaces the old flat
/// `uses + defs + 1` whole-vreg spill cost so the objective minimizes the SAME
/// currency the KILLCOMMIT control measurement used when it found
/// strictly-better-than-greedy whole-vreg allocations on real corpus functions
/// (b01 traffic 16 vs greedy 24 etc.).
pub(crate) fn spill_traffic(iv: &LiveInterval, dm: &DepthMap) -> i128 {
    iv.use_positions
        .iter()
        .chain(iv.def_positions.iter())
        .map(|&p| SPILL_W * dm.factor_at(p))
        .sum()
}

/// Greedy's realized traffic cost `G` under the SAME currency as the whole-vreg
/// objective, evaluated from the baseline record (pieces in phase-5-entry
/// numbering, the KILLCOMMIT recording):
///
/// * spilled-piece references: `SPILL_W * depth_factor` per use/def whose
///   covering piece is spilled;
/// * piece-boundary transitions: reg->reg' costs `MOVE_W`, a spill-side
///   transition costs `SPILL_W`, both times the boundary's depth factor
///   (greedy's split copies / spill boundaries, priced like the KILLCOMMIT
///   transition gadgets);
/// * move diffs over the SAME modeled copy pairs the objective prices
///   (`MOVE_W` when the endpoints' locations differ; endpoint locations are
///   collapsed to the piece covering the vreg's start — exact for unsplit
///   vregs, an approximation for split ones; the keep-metric recompute in
///   `allocate` remains the final arbiter either way).
///
/// Returns `None` when a modeled vreg is missing from the record (no bound —
/// the solve proceeds unbounded and the keep criterion still gates the result).
fn greedy_traffic_from_record(
    rec: &GreedyRecord,
    vregs: &[&LiveInterval],
    move_pairs: &[(usize, usize)],
    dm: &DepthMap,
) -> Option<i128> {
    let mut g = 0i128;
    let mut first_loc: Vec<Option<PReg>> = Vec::with_capacity(vregs.len());
    for iv in vregs {
        let pieces = rec.pieces.get(&iv.vreg.id)?;
        if pieces.is_empty() {
            return None;
        }
        // Location of a position: the last piece whose extent starts at or
        // before it (pieces are sorted by start and partition the extent).
        let loc_at = |p: u32| -> Option<PReg> {
            let mut loc = pieces.first().and_then(|pc| pc.loc);
            for pc in pieces {
                if pc.start <= p {
                    loc = pc.loc;
                } else {
                    break;
                }
            }
            loc
        };
        for &p in iv.use_positions.iter().chain(iv.def_positions.iter()) {
            if loc_at(p).is_none() {
                g += SPILL_W * dm.factor_at(p);
            }
        }
        for w in pieces.windows(2) {
            let df = dm.factor_at(w[1].start);
            match (w[0].loc, w[1].loc) {
                (Some(x), Some(y)) if x != y => g += MOVE_W * df,
                (Some(_), None) | (None, Some(_)) => g += SPILL_W * df,
                _ => {}
            }
        }
        first_loc.push(pieces.first().and_then(|pc| pc.loc));
    }
    for &(di, si) in move_pairs {
        if first_loc[di] != first_loc[si] {
            g += MOVE_W;
        }
    }
    Some(g)
}

/// Whether any reserved point (an implicit-def / ABI clobber recorded in
/// `reserved_regs`) forbids `preg` for `iv` — i.e. some reserved reg aliasing
/// `preg` is live at a point inside `iv`'s range. Mirrors
/// `LinearScan::reserved_interferes` exactly so the AY model agrees with the
/// baseline allocator's notion of a legal assignment.
pub(crate) fn reserved_forbids(
    iv: &LiveInterval,
    preg: PReg,
    reserved_regs: &BTreeMap<PReg, Vec<u32>>,
) -> bool {
    reserved_regs.iter().any(|(&reserved_preg, points)| {
        allocator_pregs_overlap(reserved_preg, preg) && points.iter().any(|&pos| iv.is_live_at(pos))
    })
}

/// Optional per-function stats (spill/copy delta) under `TCG_AY_REGALLOC_STATS`.
fn stats_enabled() -> bool {
    crate::env_lock::var_os("TCG_AY_REGALLOC_STATS").is_some()
}

/// Whether the greedy-incumbent PHASE seeding (warm-start form (b)) is active.
/// On by default whenever the AY path runs; `TCG_AY_REGALLOC_NO_SEED` opts out
/// (the A/B measurement lever). Purely a solver-search bias — disabling it can
/// change which strictly-better allocation is found, never correctness.
fn seed_enabled() -> bool {
    crate::env_lock::var_os("TCG_AY_REGALLOC_NO_SEED").is_none()
}

/// Greedy-as-incumbent WARM-START form (b): translate the baseline record into
/// `(pb_var, polarity)` phase seeds over the whole-vreg encoding, so the
/// solver's first descent lands in greedy's neighborhood instead of the
/// over-optimistic all-in-registers corner (form (a)'s hard `<= G-1` bound
/// makes greedy itself infeasible; the seed makes the search START there and
/// spend the 200ms improving it).
///
/// Each vreg's greedy pieces are collapsed to the FIRST piece's location — the
/// same collapse [`greedy_traffic_from_record`] uses for its move-diff term —
/// so the seed and the bound describe the same whole-vreg shadow of greedy's
/// (possibly split) solution:
///
/// * `Some(r)` with `r` in the candidate pool: `x_{v,r}` seeded true, every
///   other `x_{v,r'}` and `s_v` false;
/// * `None` (spilled) or `r` outside the pool (e.g. reserved-forbidden after
///   collapse): `s_v` seeded true, all `x_{v,*}` false;
/// * move `diff` vars: seeded to whether the endpoints' collapsed locations
///   differ.
///
/// SOUNDNESS-NEUTRAL BY CONSTRUCTION: phase seeds bias only the solver's
/// decision polarity ([`PbCdclSolver::seed_phases`]); the hard exactly-one /
/// interference / class / reserved constraints, the decode, the self-check and
/// the downstream validator are unchanged, so a (even wildly wrong) seed can
/// never admit an illegal allocation — only steer WHICH legal one is found.
/// Vregs missing from the record are simply left unseeded.
fn greedy_phase_seeds(
    rec: &GreedyRecord,
    vregs: &[&LiveInterval],
    candidates: &[Vec<PReg>],
    x_var: &[Vec<u32>],
    s_var: &[u32],
    move_pairs: &[(usize, usize)],
    diff_var: &[u32],
) -> Vec<(u32, bool)> {
    let n = vregs.len();
    let mut seeds: Vec<(u32, bool)> = Vec::new();
    let mut first_loc: Vec<Option<Option<PReg>>> = vec![None; n];
    for vi in 0..n {
        let Some(pieces) = rec.pieces.get(&vregs[vi].vreg.id) else {
            continue; // unrecorded vreg: leave unseeded
        };
        let Some(first) = pieces.first() else {
            continue;
        };
        first_loc[vi] = Some(first.loc);
        // The candidate index greedy's collapsed location maps to, if any.
        let ci_of_loc = first
            .loc
            .and_then(|r| candidates[vi].iter().position(|&c| c == r));
        for (ci, &xv) in x_var[vi].iter().enumerate() {
            seeds.push((xv, Some(ci) == ci_of_loc));
        }
        seeds.push((s_var[vi], ci_of_loc.is_none()));
    }
    for (mp, &(di, si)) in move_pairs.iter().enumerate() {
        // Seed a move diff only when BOTH endpoints were recorded.
        if let (Some(dl), Some(sl)) = (first_loc[di], first_loc[si]) {
            seeds.push((diff_var[mp], dl != sl));
        }
    }
    seeds
}

/// Solve the WHOLE-VREG AY-PBO assignment for `intervals` (one preg per vreg for
/// its whole live range) and return `Some((allocation, spilled))` — the decoded,
/// self-checked assignment map plus the spilled vregs — or `None` to signal
/// "fall back" for ANY reason (oversize, no feasible incumbent within the cap,
/// infeasible/unknown, a self-check failure, or a fixed interval we do not
/// model). `None` NEVER means a correctness failure: the caller runs the
/// baseline allocator.
///
/// This function never mutates the machine function — `func` is read ONLY for
/// block spans / loop depths (the traffic objective's depth weighting).
///
/// `incumbent` is the baseline (greedy) record: when present, its realized
/// solution is evaluated to `G` under the same traffic currency and a HARD
/// `objective <= G-1` constraint is added — the greedy-as-incumbent warm start.
/// Any model then found is strictly better than greedy in the shared currency;
/// `Unsatisfiable` (greedy optimal over the whole-vreg closure) and `Unknown`
/// (time-starved) are clean declines. When `G == 0` greedy is unbeatable and we
/// decline without solving. `None` (or a fall-back-worthy record mismatch)
/// simply drops the bound — the run-both-keep-better criterion in `allocate`
/// still gates the result either way.
pub(crate) fn solve_whole_vreg(
    func: &RegAllocFunction,
    intervals: &[LiveInterval],
    allocatable: &BTreeMap<RegClass, Vec<PReg>>,
    reserved_regs: &BTreeMap<PReg, Vec<u32>>,
    copies: &[(VReg, VReg)],
    incumbent: Option<&GreedyRecord>,
) -> Option<(BTreeMap<VReg, PReg>, Vec<VReg>)> {
    // Fixed intervals do not arise in the production pipeline; if one appears,
    // bail rather than model a pre-colored preg incorrectly.
    if intervals.iter().any(|iv| iv.is_fixed) {
        return None;
    }

    // Model the non-empty intervals. Distinct vreg ids are assumed (SSA).
    let vregs: Vec<&LiveInterval> = intervals
        .iter()
        .filter(|iv| !iv.ranges.is_empty())
        .collect();
    let n = vregs.len();
    if n == 0 || n > max_vregs() {
        return None;
    }

    // Candidate pregs per vreg: the class pool minus reserved-forbidden regs.
    // A vreg whose class has no pool, or whose entire pool is reserved-forbidden
    // over its range, still models fine — it is simply forced to spill.
    let mut candidates: Vec<Vec<PReg>> = Vec::with_capacity(n);
    for iv in &vregs {
        let pool = allocatable.get(&iv.vreg.class)?;
        let cand: Vec<PReg> = pool
            .iter()
            .copied()
            .filter(|&r| !reserved_forbids(iv, r, reserved_regs))
            .collect();
        candidates.push(cand);
    }

    // Assign 1-indexed PB variable ids: x_{vi,ci} then a spill var s_{vi}.
    let mut next_var: u32 = 1;
    let mut x_var: Vec<Vec<u32>> = Vec::with_capacity(n);
    let mut s_var: Vec<u32> = Vec::with_capacity(n);
    for candidate_row in &candidates {
        let mut row = Vec::with_capacity(candidate_row.len());
        for _ in candidate_row {
            row.push(next_var);
            next_var += 1;
        }
        x_var.push(row);
        s_var.push(next_var);
        next_var += 1;
    }

    // Move-coalescing model. For each copy `d <- s` whose BOTH endpoints are
    // modeled here and share a register class, a boolean `diff` that the
    // objective PAYS when d and s land on DIFFERENT pregs — so the optimizer
    // co-assigns the copy's endpoints (coalescing the move away) whenever
    // feasible. This shapes ONLY the objective: the hard exactly-one /
    // interference / class / reserved constraints are unchanged, and the
    // downstream self-check + always-on translation validator gate the result
    // regardless, so a wrong move-cost encoding can NEVER miscompile — at worst
    // it picks a suboptimal but still-valid allocation.
    let index_of: BTreeMap<VReg, usize> = (0..n).map(|vi| (vregs[vi].vreg, vi)).collect();
    let mut move_pairs: Vec<(usize, usize)> = Vec::new();
    for &(d, s) in copies {
        let (Some(&di), Some(&si)) = (index_of.get(&d), index_of.get(&s)) else {
            continue;
        };
        // Same-class, distinct endpoints only: a cross-class or self copy can
        // never be coalesced into a shared preg, so it carries no move cost.
        if di == si || vregs[di].vreg.class != vregs[si].vreg.class {
            continue;
        }
        move_pairs.push((di, si));
    }
    // One `diff` variable per modeled copy, numbered after the x_/s_ vars.
    let mut diff_var: Vec<u32> = Vec::with_capacity(move_pairs.len());
    for _ in 0..move_pairs.len() {
        diff_var.push(next_var);
        next_var += 1;
    }
    let num_vars = next_var - 1;

    let mut constraints: Vec<PbConstraint> = Vec::new();

    // exactly-one:  sum_r x_{vi,r} + s_{vi} = 1
    for vi in 0..n {
        let mut terms: Vec<PbTerm> = Vec::with_capacity(x_var[vi].len() + 1);
        for &v in &x_var[vi] {
            terms.push(pos_term(v));
        }
        terms.push(pos_term(s_var[vi]));
        constraints.push(PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs: 1,
        });
    }

    // interference: for overlapping (vi,vj) and aliasing candidate pregs,
    // ~x_{vi,ci} + ~x_{vj,cj} >= 1   (both cannot take aliasing regs at once).
    let mut pair_count = 0usize;
    for vi in 0..n {
        for vj in (vi + 1)..n {
            if !vregs[vi].overlaps(vregs[vj]) {
                continue;
            }
            pair_count += 1;
            if pair_count > max_pairs() {
                return None;
            }
            for (ci, &ri) in candidates[vi].iter().enumerate() {
                for (cj, &rj) in candidates[vj].iter().enumerate() {
                    if allocator_pregs_overlap(ri, rj) {
                        constraints.push(PbConstraint {
                            terms: vec![neg_term(x_var[vi][ci]), neg_term(x_var[vj][cj])],
                            rel: PbRel::Ge,
                            rhs: 1,
                        });
                    }
                }
            }
        }
    }

    // move constraints: force `diff >= (d and s take different pregs)`.
    // For each candidate reg r of d:  diff + ~x_{d,r} [+ x_{s,r}] >= 1
    //   == diff >= x_{d,r} - x_{s,r}
    // and symmetrically for each candidate reg r of s. `diff` is a free boolean
    // the objective drives to 0 (co-assigned, no move) whenever the constraints
    // allow — i.e. whenever d and s can share a register.
    for (mp, &(di, si)) in move_pairs.iter().enumerate() {
        add_move_constraints(&mut constraints, diff_var[mp], di, si, &candidates, &x_var);
    }

    // objective: min  sum_vi traffic(vi) * s_{vi}  +  MOVE_W * sum_c diff_c
    // — the COMMENSURABLE loop-depth-weighted traffic currency (spill-op ~4x
    // move, no lexicographic scaling; the KILLCOMMIT objective fix).
    let dm = DepthMap::new(func);
    let mut obj_terms: Vec<PbTerm> = Vec::with_capacity(n + diff_var.len());
    for vi in 0..n {
        let c = spill_traffic(vregs[vi], &dm);
        if c > 0 {
            obj_terms.push(PbTerm {
                coeff: c,
                lits: vec![lit(s_var[vi])],
            });
        }
    }
    for &dv in &diff_var {
        obj_terms.push(PbTerm {
            coeff: MOVE_W,
            lits: vec![lit(dv)],
        });
    }
    let objective = PbObjective {
        terms: obj_terms.clone(),
    };

    // Greedy-as-incumbent warm start (form (a)): evaluate greedy's realized
    // solution to G in the same currency and add the HARD `objective <= G-1`
    // bound (the ay-pb strictly_better_than_incumbent negated-Ge row, emitted
    // directly — the KILLCOMMIT gadget verbatim). Strictly-better-or-decline:
    // any model beats greedy; UNSAT/Unknown under the bound falls back cleanly.
    let g = incumbent.and_then(|rec| greedy_traffic_from_record(rec, &vregs, &move_pairs, &dm));
    if let Some(g) = g {
        if g == 0 {
            // Cost is non-negative, so `<= -1` is trivially unsatisfiable:
            // greedy is unbeatable here — decline without spending the cap.
            if stats_enabled() {
                eprintln!("[ay-regalloc] incumbent G=0 -> decline (greedy unbeatable)");
            }
            return None;
        }
        constraints.push(PbConstraint {
            terms: obj_terms
                .iter()
                .map(|t| PbTerm {
                    coeff: -t.coeff,
                    lits: t.lits.clone(),
                })
                .collect(),
            rel: PbRel::Ge,
            rhs: -(g - 1),
        });
    }

    let instance = PbInstance {
        num_vars,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: Some(objective.clone()),
    };

    // Anytime solve with a wall-clock deadline. `new_interruptible` bounds
    // preprocessing; `solve_optimize_interruptible` bounds the search and returns
    // the best feasible incumbent found so far when the deadline trips. Both an
    // `Optimal` (proven minimum) and a `Feasible` (best-so-far) result are a
    // *valid* satisfying assignment of the hard constraints — the caller compares
    // its spill count against greedy and keeps whichever is smaller, so a merely-
    // feasible incumbent can never make the result worse than greedy.
    let deadline = Instant::now() + time_cap();
    let mut solver = PbCdclSolver::new_interruptible(&instance, || Instant::now() >= deadline);

    // Warm-start form (b): seed the decision phases at greedy's (collapsed)
    // solution so the anytime search improves a known-good point instead of
    // repairing the all-in-registers start. See [`greedy_phase_seeds`] for the
    // soundness argument (pure polarity bias; every hard gate unchanged).
    if seed_enabled()
        && let Some(rec) = incumbent
    {
        let seeds = greedy_phase_seeds(
            rec,
            &vregs,
            &candidates,
            &x_var,
            &s_var,
            &move_pairs,
            &diff_var,
        );
        if !seeds.is_empty() {
            solver.seed_phases(&seeds);
        }
    }

    let result =
        solver.solve_optimize_interruptible(&objective, None, || Instant::now() >= deadline);

    let g_str = g.map_or_else(|| "-".to_string(), |g| g.to_string());
    let (model, cost) = match result {
        PbCdclResult::Optimal(model, cost) => {
            if stats_enabled() {
                eprintln!("[ay-regalloc] result=Optimal cost={cost} G={g_str}");
            }
            (model, cost)
        }
        PbCdclResult::Feasible(model, cost) => {
            if stats_enabled() {
                eprintln!("[ay-regalloc] result=Feasible cost={cost} G={g_str}");
            }
            (model, cost)
        }
        // Unsatisfiable: only possible under the incumbent bound (spilling is
        // always feasible in the base formula) — greedy is optimal over the
        // whole-vreg closure; a clean decline.
        PbCdclResult::Unsatisfiable => {
            if stats_enabled() {
                eprintln!("[ay-regalloc] result=UNSAT G={g_str} -> greedy optimal, decline");
            }
            return None;
        }
        // Unknown = interrupted before any (bound-satisfying) incumbent;
        // anything else (non_exhaustive) -> fall back to greedy.
        _ => {
            if stats_enabled() {
                eprintln!("[ay-regalloc] result=Unknown G={g_str} -> decline");
            }
            return None;
        }
    };

    // Decode the model into an assignment + spill set.
    let mut allocation: BTreeMap<VReg, PReg> = BTreeMap::new();
    let mut spilled: Vec<VReg> = Vec::new();
    for vi in 0..n {
        let vreg = vregs[vi].vreg;
        let mut assigned: Option<PReg> = None;
        for (ci, &var) in x_var[vi].iter().enumerate() {
            if model_at(&model, var) {
                assigned = Some(candidates[vi][ci]);
                break;
            }
        }
        let spill = model_at(&model, s_var[vi]);
        match (assigned, spill) {
            (Some(r), false) => {
                allocation.insert(vreg, r);
            }
            (None, true) => spilled.push(vreg),
            // exactly-one violated (untrusted solver returned an inconsistent
            // model): reject the whole allocation and fall back.
            _ => return None,
        }
    }

    // Independent self-check of AY's (untrusted) output against the invariants we
    // encoded. This is the first correctness gate; the always-on translation
    // validator downstream is the second.
    if !self_check(&vregs, &allocation, allocatable, reserved_regs) {
        return None;
    }

    if stats_enabled() {
        eprintln!(
            "[ay-regalloc] vregs={n} allocated={} spilled={} spill_cost={cost} (cap={:?})",
            allocation.len(),
            spilled.len(),
            time_cap(),
        );
    }

    Some((allocation, spilled))
}

/// Attempt to allocate `intervals` optimally via AY-PBO, optionally applying
/// LIVE-RANGE SPLITTING when [`split_enabled`] is set.
///
/// `incumbent` is the baseline (greedy) pass's realized solution when available
/// — the greedy-as-incumbent warm start: the whole-vreg solve adds a hard
/// `objective <= G-1` bound so it can only return strictly-better-than-greedy
/// allocations (in the shared traffic currency) or decline. See
/// [`solve_whole_vreg`].
///
/// Returns `Some((result, spilled))` — the same tuple shape the greedy /
/// linear-scan phase-5 arms produce — when AY yields a self-checked, valid
/// assignment; `None` to fall back to greedy.
///
/// ## Whole-vreg (split disabled)
///
/// When `TCG_AY_REGALLOC_SEGMENTS` (and the legacy alias `TCG_AY_REGALLOC_SPLIT`)
/// is unset this is exactly [`solve_whole_vreg`] wrapped in the result tuple:
/// `func` is NOT mutated and the behaviour is byte-identical to the pre-split
/// allocator.
///
/// ## Per-segment live-range split (segments enabled — plan steps 4-6)
///
/// The spill-delta vregs (whole-vreg AY spills ∪ greedy's own split-or-spilled
/// roots) are segmented per basic block, the per-segment PB
/// ([`solve_segmented`]: `x_{v,seg,r}` / `s_{v,seg}`, true-overlap-only
/// interference, boundary transition costs, the commensurable traffic
/// objective, greedy-incumbent hard bound + phase seeds) is solved, and the
/// decoded assignment is materialized ([`materialize_segments`]) by splitting
/// `func` via [`crate::split::split_interval_checked`] at exactly the BB
/// boundaries where the decoded location changes, recomputing liveness before
/// each split. Any `SplitError` / unexpected shape DROPS the whole AY solution.
/// The split copies are ordinary value-propagation the always-on translation
/// validator already certifies (identically to greedy's own splits), and the
/// post-materialization self-check re-verifies the concrete assignment against
/// freshly recomputed liveness, so a wrong split can never ship.
///
/// Materialization runs on a CLONE of `func`; `func` is overwritten ONLY after
/// the split stream passes every segment gate, so a rejected split solution
/// leaves `func` pristine and the whole-vreg result (or greedy) still ships. A
/// mutated-but-rejected stream is never observed downstream.
pub(crate) fn try_allocate(
    func: &mut RegAllocFunction,
    intervals: &[LiveInterval],
    allocatable: &BTreeMap<RegClass, Vec<PReg>>,
    reserved_regs: &BTreeMap<PReg, Vec<u32>>,
    copies: &[(VReg, VReg)],
    incumbent: Option<&GreedyRecord>,
) -> Option<(AllocationResult, Vec<VReg>)> {
    let wv = solve_whole_vreg(
        func,
        intervals,
        allocatable,
        reserved_regs,
        copies,
        incumbent,
    );

    // Wrap a raw (allocation, spilled) pair into the phase-5 result tuple.
    let wrap = |(allocation, spilled): (BTreeMap<VReg, PReg>, Vec<VReg>)| {
        (
            AllocationResult {
                allocation,
                spills: Vec::new(), // filled in later by insert_spill_code
            },
            spilled,
        )
    };

    // Whole-vreg path (split gate unset): byte-identical to origin. `func` is
    // never mutated on this path.
    if !split_enabled() {
        return Some(wrap(wv?));
    }

    // === STEPS 4-6: PER-SEGMENT PB LIVE-RANGE SPLITTING. ===
    //
    // The SPILL-DELTA set is the vregs the whole-vreg model spills (when it
    // produced a solution) UNION the vregs the baseline (greedy) itself split or
    // spilled (`split_or_spilled_roots` — eviction cascades split non-delta
    // vregs, and when the bounded whole-vreg solve DECLINED, greedy's own split
    // set is exactly where splitting pays). We segment ONLY those vregs per
    // basic block (every other vreg stays whole-vreg), encode the per-segment PB
    // (`x_{v,seg,r}` / `s_{v,seg}` + boundary transition costs), solve with the
    // greedy incumbent as warm start + hard strictly-better bound, and
    // materialize the decoded assignment by splitting `func` at the BB
    // boundaries where the decoded location changes.
    //
    // Crucially this runs EVEN when `solve_whole_vreg` declined (UNSAT under its
    // own `<= G-1` bound): greedy beats whole-vreg AY precisely BECAUSE greedy
    // splits, so the segmented model is the one that can recover those wins.
    //
    // A wrong split can NEVER ship: (1) a segment-level self-check rejects an
    // inconsistent solver model BEFORE materializing; (2) any SplitError or
    // unexpected shape during materialization DROPS the whole split solution
    // (materialized on a clone -> the whole-vreg result or greedy is kept —
    // never a partially-split hybrid); (3) a post-
    // materialization whole-vreg self-check (recomputed against the actual split
    // stream) re-verifies class / reserved / interference legality — the
    // correct-by-construction backstop for the validator's PROVEN numbering-
    // drift blind spot; (4) the always-on translation validator gates the result
    // downstream; (5) the run-both-keep-better keep criterion keeps AY only if
    // it VALIDATES and beats greedy in the recomputed traffic currency. Every
    // split reuses `split_interval_checked` VERBATIM (CFG-unsafe -> SplitError
    // -> drop, never a wrong copy) and derives its split point from FRESH
    // liveness / block spans recomputed before each split, so instruction
    // numbering is never stale (the LRSPLIT-1 de-risk-spike drift lesson).

    // A spill-free whole-vreg optimum cannot be improved by splitting
    // (boundaries only ever ADD cost): keep it, `func` unmutated.
    if let Some((_, spilled)) = &wv
        && spilled.is_empty()
    {
        return wv.map(wrap);
    }

    // Guards the whole-vreg solve normally provides but which must hold here
    // independently (it may have declined for these same reasons): fixed
    // intervals are not modeled; oversize functions decline to greedy.
    if intervals.iter().any(|iv| iv.is_fixed) {
        return wv.map(wrap);
    }
    let vregs: Vec<&LiveInterval> = intervals
        .iter()
        .filter(|iv| !iv.ranges.is_empty())
        .collect();
    let n = vregs.len();
    if n == 0 || n > max_vregs() {
        return wv.map(wrap);
    }

    // The spill-delta set (see above).
    let modeled_ids: BTreeSet<u32> = vregs.iter().map(|iv| iv.vreg.id).collect();
    let mut delta: BTreeSet<u32> = wv
        .as_ref()
        .map(|(_, sp)| sp.iter().map(|v| v.id).collect())
        .unwrap_or_default();
    if let Some(rec) = incumbent {
        delta.extend(rec.split_or_spilled_roots());
    }
    delta.retain(|id| modeled_ids.contains(id));
    if delta.is_empty() {
        if stats_enabled() {
            eprintln!("[ay-regalloc] segments: empty delta set; whole-vreg kept");
        }
        return wv.map(wrap);
    }

    // Per-BB segmentation of the delta-set vregs (>= 2 segments only — a single-
    // block vreg cannot relieve register pressure by splitting, so keep it whole).
    let spans = block_spans(func);
    let seg_of: Vec<Option<Vec<Segment>>> = vregs
        .iter()
        .map(|iv| {
            if delta.contains(&iv.vreg.id) {
                let segs = per_bb_segments(iv, &spans);
                (segs.len() >= 2).then_some(segs)
            } else {
                None
            }
        })
        .collect();

    let total_units: usize = seg_of.iter().map(|s| s.as_ref().map_or(1, Vec::len)).sum();
    let any_segmented = seg_of.iter().any(Option::is_some);

    // Nothing multi-block to segment: keep the whole-vreg result unchanged
    // (`func` is NOT mutated) — a clean decline, byte-identical downstream.
    if !any_segmented {
        if stats_enabled() {
            eprintln!("[ay-regalloc] segments: no multi-block delta vregs; whole-vreg kept");
        }
        return wv.map(wrap);
    }
    // Over the segment cap: decline the segmented model. `func` is still
    // unmutated here, so falling back to the whole-vreg result (or greedy) is
    // clean.
    if total_units > max_split_segments() {
        if stats_enabled() {
            eprintln!(
                "[ay-regalloc] segments: {total_units} units > cap {}; declined",
                max_split_segments()
            );
        }
        return wv.map(wrap);
    }

    // STEPS 4-5: encode + solve the per-segment PB (greedy-incumbent warm start
    // + hard strictly-better bound) + segment-level self-check. `None` =>
    // decline (oversize / UNSAT under the bound / time-starved / inconsistent
    // model) -> the whole-vreg result (or greedy). `func` is still unmutated.
    let Some(decode) = solve_segmented(
        func,
        &vregs,
        &seg_of,
        allocatable,
        reserved_regs,
        copies,
        incumbent,
    ) else {
        return wv.map(wrap);
    };

    // STEP 6: materialize the decoded per-segment assignment onto a CLONE of
    // `func` (splits driven by the DECODED pregs, fresh liveness before each
    // split) and build the final (allocation, spilled) over the post-split
    // vregs. ANY SplitError or unexpected shape (e.g. a run boundary landing
    // outside the current live extent after earlier splits shifted positions, a
    // non-dominating diamond-arm boundary, a loop-participating block) drops
    // the ENTIRE split solution. Materializing on a clone means `func` itself
    // is untouched on the drop path, so the already-validated whole-vreg result
    // still ships (or greedy, when there is none) — a doomed materialization
    // never torpedoes the whole-vreg win. `func` is overwritten only after
    // every gate below passes.
    let mut split_func = func.clone();
    let Some((allocation, spilled)) =
        materialize_segments(&mut split_func, &vregs, &seg_of, &decode)
    else {
        if stats_enabled() {
            eprintln!(
                "[ay-regalloc] segments: materialization dropped (SplitError) -> whole-vreg/greedy"
            );
        }
        return wv.map(wrap);
    };

    // FINAL correctness gate (the always-on validator has a numbering-drift blind
    // spot, so DO NOT rely on it alone): recompute liveness + reservations against
    // the actual post-split stream and re-run the whole-vreg self-check over the
    // concrete assignment (every allocated preg legal; no two overlapping vregs on
    // aliasing pregs), plus a coverage check that every live vreg is assigned or
    // spilled. Any inconsistency -> drop the split solution -> whole-vreg/greedy.
    let post = crate::liveness::compute_live_intervals(&split_func);
    let post_reserved = crate::implicit_def_reservations(&split_func, &post.inst_numbering);
    let post_intervals: Vec<&LiveInterval> = post.intervals.values().collect();
    if !self_check(&post_intervals, &allocation, allocatable, &post_reserved) {
        if stats_enabled() {
            eprintln!(
                "[ay-regalloc] segments: post-materialization self-check REJECTED -> \
                 whole-vreg/greedy"
            );
        }
        return wv.map(wrap);
    }
    let spilled_set: BTreeSet<u32> = spilled.iter().map(|v| v.id).collect();
    for iv in &post_intervals {
        if !allocation.contains_key(&iv.vreg) && !spilled_set.contains(&iv.vreg.id) {
            if stats_enabled() {
                eprintln!(
                    "[ay-regalloc] segments: vreg {} neither allocated nor spilled -> \
                     whole-vreg/greedy",
                    iv.vreg.id
                );
            }
            return wv.map(wrap);
        }
    }

    if stats_enabled() {
        eprintln!(
            "[ay-regalloc] segments: segmented={} delta={} -> allocated={} spilled={}",
            seg_of.iter().filter(|s| s.is_some()).count(),
            delta.len(),
            allocation.len(),
            spilled.len(),
        );
    }

    // Every segment gate passed: commit the split stream.
    *func = split_func;

    Some((
        AllocationResult {
            allocation,
            spills: Vec::new(),
        },
        spilled,
    ))
}

/// A modeled allocation unit: a whole vreg, or one per-BB segment of a segmented
/// vreg. Used only inside [`solve_segmented`].
struct SegUnit {
    /// Index into the modeled `vregs` this unit belongs to.
    vi: usize,
    /// This unit's liveness (whole-vreg ranges, or the single segment range) plus
    /// its use/def positions (for spill cost + reserved checks).
    iv: LiveInterval,
    /// Candidate pregs: class pool minus reserved-forbidden over the unit's range.
    candidates: Vec<PReg>,
}

/// Candidate pregs for a unit: its class pool minus reserved-forbidden regs over
/// the unit's own range. `None` only if the class has no pool at all (decline).
/// An empty result (all reserved) is fine — the unit is simply forced to spill.
pub(crate) fn unit_candidates(
    iv: &LiveInterval,
    allocatable: &BTreeMap<RegClass, Vec<PReg>>,
    reserved_regs: &BTreeMap<PReg, Vec<u32>>,
) -> Option<Vec<PReg>> {
    let pool = allocatable.get(&iv.vreg.class)?;
    Some(
        pool.iter()
            .copied()
            .filter(|&r| !reserved_forbids(iv, r, reserved_regs))
            .collect(),
    )
}

/// Solve the PER-SEGMENT PB for the split path (steps 4-5). `seg_of[vi]` is
/// `Some(segments)` for a segmented vreg (per-BB segments, length >= 2) or `None`
/// for a whole-vreg vreg. Returns, per modeled vreg `vi`, the decoded assignment
/// as a `Vec<Option<PReg>>` — length 1 for a whole vreg, `segments.len()` for a
/// segmented vreg, a `None` entry meaning "spill that unit". `None` overall means
/// decline (oversize / UNSAT under the incumbent bound / time-starved /
/// inconsistent model) -> the caller keeps the whole-vreg result or greedy.
///
/// The encoding mirrors [`solve_whole_vreg`] but per UNIT: exactly-one per unit
/// (`x_{v,seg,r}` + `s_{v,seg}`), interference ONLY for truly-overlapping units
/// of different vregs (same-vreg segments are disjoint by construction —
/// skipped), plus per-boundary TRANSITION indicators (`t_store` / `t_reload` /
/// `t_move`, one triple per adjacent same-vreg segment pair) forced to 1 by
/// one-sided gadgets when the boundary realizes a reg->spill store, a
/// spill->reg reload, or a reg->reg' move respectively (see
/// [`add_transition_constraints`]).
///
/// The objective is the COMMENSURABLE loop-depth-weighted traffic currency the
/// whole-vreg solve and the run-both keep-metric use (the KILLCOMMIT fix — the
/// first cut's strict-lexicographic spills>>boundaries scaling made split
/// copies effectively free relative to spills and is exactly the mismatch that
/// hid wins): spilled unit references cost `SPILL_W * 10^depth` each, boundary
/// stores/reloads `SPILL_W * 10^depth`, boundary moves `MOVE_W * 10^depth`,
/// surviving-copy move diffs `MOVE_W`.
///
/// Greedy-as-incumbent warm start: when `incumbent` is present, greedy's
/// realized solution is EMBEDDED into the unit space (each unit takes the
/// location of the greedy piece covering its start — greedy's arbitrary-point
/// splits projected onto BB boundaries), evaluated to `G` in the same currency,
/// and a HARD `objective <= G-1` bound is added, so the solve is
/// strictly-better-or-decline; the embedding also seeds the solver's decision
/// phases ([`PbCdclSolver::seed_phases`], a soundness-neutral polarity bias) so
/// the anytime search starts at greedy's neighborhood instead of the
/// all-in-registers corner. The embedding being an approximation is
/// QUALITY-only either way: the final arbiter is `allocate`'s recomputed
/// ground-truth traffic comparison, and every hard legality gate is unchanged.
///
/// AY is untrusted: the segment-level self-check ([`segment_self_check`]) here,
/// the post-materialization whole-vreg self-check, and the always-on validator
/// downstream gate the result, so a wrong model can only ever be discarded.
fn solve_segmented(
    func: &RegAllocFunction,
    vregs: &[&LiveInterval],
    seg_of: &[Option<Vec<Segment>>],
    allocatable: &BTreeMap<RegClass, Vec<PReg>>,
    reserved_regs: &BTreeMap<PReg, Vec<u32>>,
    copies: &[(VReg, VReg)],
    incumbent: Option<&GreedyRecord>,
) -> Option<Vec<Vec<Option<PReg>>>> {
    let n = vregs.len();

    // Build the modeling units and record each vreg's unit index range.
    let mut units: Vec<SegUnit> = Vec::new();
    let mut unit_range: Vec<(usize, usize)> = Vec::with_capacity(n);
    for vi in 0..n {
        let start = units.len();
        match &seg_of[vi] {
            None => {
                let iv = (*vregs[vi]).clone();
                let candidates = unit_candidates(&iv, allocatable, reserved_regs)?;
                units.push(SegUnit { vi, iv, candidates });
            }
            Some(segs) => {
                for seg in segs {
                    let mut iv = LiveInterval::new(vregs[vi].vreg);
                    iv.add_range(seg.start, seg.end);
                    iv.use_positions = seg.use_positions.clone();
                    iv.def_positions = seg.def_positions.clone();
                    let candidates = unit_candidates(&iv, allocatable, reserved_regs)?;
                    units.push(SegUnit { vi, iv, candidates });
                }
            }
        }
        unit_range.push((start, units.len()));
    }
    let m = units.len();

    // PB vars: x_{u,c} then a spill var s_u per unit.
    let mut next_var: u32 = 1;
    let mut x_var: Vec<Vec<u32>> = Vec::with_capacity(m);
    let mut s_var: Vec<u32> = Vec::with_capacity(m);
    for unit in &units {
        let mut row = Vec::with_capacity(unit.candidates.len());
        for _ in &unit.candidates {
            row.push(next_var);
            next_var += 1;
        }
        x_var.push(row);
        s_var.push(next_var);
        next_var += 1;
    }

    // Move-coalescing pairs — ONLY between WHOLE-vreg units. A segmented vreg is
    // being split, so its copies are not modeled; move cost is pure objective
    // shaping (a tiebreaker), so this restriction affects only quality.
    let whole_unit_of: BTreeMap<VReg, usize> = (0..n)
        .filter(|&vi| seg_of[vi].is_none())
        .map(|vi| (vregs[vi].vreg, unit_range[vi].0))
        .collect();
    let mut move_pairs: Vec<(usize, usize)> = Vec::new();
    for &(d, s) in copies {
        let (Some(&du), Some(&su)) = (whole_unit_of.get(&d), whole_unit_of.get(&s)) else {
            continue;
        };
        if du == su || units[du].iv.vreg.class != units[su].iv.vreg.class {
            continue;
        }
        move_pairs.push((du, su));
    }

    // Boundary transitions — each adjacent segment pair of a segmented vreg,
    // priced at the later segment's start position (same block as where
    // materialization places the split copy, so the same loop-depth factor).
    let mut transitions: Vec<(usize, usize, u32)> = Vec::new();
    for vi in 0..n {
        if seg_of[vi].is_some() {
            let (s, e) = unit_range[vi];
            for u in s..(e.saturating_sub(1)) {
                transitions.push((u, u + 1, units[u + 1].iv.start()));
            }
        }
    }

    // diff vars: move diffs, then a (t_store, t_reload, t_move) triple per
    // boundary transition.
    let mut move_diff: Vec<u32> = Vec::with_capacity(move_pairs.len());
    for _ in 0..move_pairs.len() {
        move_diff.push(next_var);
        next_var += 1;
    }
    let mut trans_vars: Vec<(u32, u32, u32)> = Vec::with_capacity(transitions.len());
    for _ in 0..transitions.len() {
        trans_vars.push((next_var, next_var + 1, next_var + 2));
        next_var += 3;
    }
    let num_vars = next_var - 1;

    // Loop-depth factors for the commensurable traffic currency.
    let dm = DepthMap::new(func);

    // Unit-indexed candidates + x_var for the constraint helpers.
    let candidates: Vec<Vec<PReg>> = units.iter().map(|u| u.candidates.clone()).collect();

    let mut constraints: Vec<PbConstraint> = Vec::new();

    // exactly-one per unit: sum_c x_{u,c} + s_u = 1.
    for u in 0..m {
        let mut terms: Vec<PbTerm> = Vec::with_capacity(x_var[u].len() + 1);
        for &v in &x_var[u] {
            terms.push(pos_term(v));
        }
        terms.push(pos_term(s_var[u]));
        constraints.push(PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs: 1,
        });
    }

    // interference: for truly-overlapping units of DIFFERENT vregs and aliasing
    // candidate pregs, ~x_{u,ci} + ~x_{w,cj} >= 1. Same-vreg segments are disjoint
    // by construction (skipped). Sparse: only overlapping pairs emit clauses.
    let mut pair_count = 0usize;
    for u in 0..m {
        for w in (u + 1)..m {
            if units[u].vi == units[w].vi || !units[u].iv.overlaps(&units[w].iv) {
                continue;
            }
            pair_count += 1;
            if pair_count > max_pairs() {
                return None;
            }
            for (ci, &ri) in candidates[u].iter().enumerate() {
                for (cj, &rj) in candidates[w].iter().enumerate() {
                    if allocator_pregs_overlap(ri, rj) {
                        constraints.push(PbConstraint {
                            terms: vec![neg_term(x_var[u][ci]), neg_term(x_var[w][cj])],
                            rel: PbRel::Ge,
                            rhs: 1,
                        });
                    }
                }
            }
        }
    }

    // move + transition gadgets (all one-sided — the two-sided move gadget on a
    // non-interfering same-vreg pair trips the ay-pb dense-conflict debug
    // assertion; see [`add_transition_constraints`]).
    for (mp, &(du, su)) in move_pairs.iter().enumerate() {
        add_move_constraints(&mut constraints, move_diff[mp], du, su, &candidates, &x_var);
    }
    for (ti, &(au, bu, _pos)) in transitions.iter().enumerate() {
        add_transition_constraints(
            &mut constraints,
            trans_vars[ti],
            au,
            bu,
            s_var[au],
            s_var[bu],
            &candidates,
            &x_var,
        );
    }

    // objective: the commensurable loop-depth-weighted traffic currency.
    //   spilled unit: SPILL_W * 10^depth per use/def reference in the unit;
    //   boundary store/reload: SPILL_W * 10^depth at the boundary;
    //   boundary move: MOVE_W * 10^depth at the boundary;
    //   surviving-copy move diff: MOVE_W (flat, as in the whole-vreg objective).
    let mut obj_terms: Vec<PbTerm> = Vec::new();
    for u in 0..m {
        let c = spill_traffic(&units[u].iv, &dm);
        if c > 0 {
            obj_terms.push(PbTerm {
                coeff: c,
                lits: vec![lit(s_var[u])],
            });
        }
    }
    for (ti, &(_au, _bu, pos)) in transitions.iter().enumerate() {
        let df = dm.factor_at(pos);
        let (t_store, t_reload, t_move) = trans_vars[ti];
        obj_terms.push(PbTerm {
            coeff: SPILL_W * df,
            lits: vec![lit(t_store)],
        });
        obj_terms.push(PbTerm {
            coeff: SPILL_W * df,
            lits: vec![lit(t_reload)],
        });
        obj_terms.push(PbTerm {
            coeff: MOVE_W * df,
            lits: vec![lit(t_move)],
        });
    }
    for &dv in &move_diff {
        obj_terms.push(PbTerm {
            coeff: MOVE_W,
            lits: vec![lit(dv)],
        });
    }
    let objective = PbObjective {
        terms: obj_terms.clone(),
    };

    // Greedy-as-incumbent warm start: embed greedy into the unit space,
    // evaluate G in the objective's own currency, add the HARD `<= G-1` bound
    // (strictly-better-or-decline), and remember the embedding for phase seeds.
    let embed: Option<Vec<Option<PReg>>> =
        incumbent.and_then(|rec| embed_record_into_units(rec, &units));
    let g = embed.as_ref().map(|locs| {
        let mut g = 0i128;
        for (u, loc) in locs.iter().enumerate() {
            if loc.is_none() {
                g += spill_traffic(&units[u].iv, &dm);
            }
        }
        for &(au, bu, pos) in &transitions {
            let df = dm.factor_at(pos);
            match (locs[au], locs[bu]) {
                (Some(x), Some(y)) if x != y => g += MOVE_W * df,
                (Some(_), None) | (None, Some(_)) => g += SPILL_W * df,
                _ => {}
            }
        }
        for &(du, su) in &move_pairs {
            if locs[du] != locs[su] {
                g += MOVE_W;
            }
        }
        g
    });
    if let Some(g) = g {
        if g == 0 {
            // Cost is non-negative: greedy is unbeatable here — decline
            // without spending the solve budget.
            if stats_enabled() {
                eprintln!("[ay-regalloc] segments: incumbent G=0 -> decline");
            }
            return None;
        }
        constraints.push(PbConstraint {
            terms: obj_terms
                .iter()
                .map(|t| PbTerm {
                    coeff: -t.coeff,
                    lits: t.lits.clone(),
                })
                .collect(),
            rel: PbRel::Ge,
            rhs: -(g - 1),
        });
    }

    let instance = PbInstance {
        num_vars,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: Some(objective.clone()),
    };

    let deadline = Instant::now() + time_cap();
    let mut solver = PbCdclSolver::new_interruptible(&instance, || Instant::now() >= deadline);

    // Warm-start form (b): seed the decision phases at greedy's embedded
    // solution. Soundness-neutral by construction — a (even wildly wrong) seed
    // only biases WHICH model the search visits first; every hard constraint,
    // the decode, the self-checks and the downstream validator are unchanged.
    if seed_enabled()
        && let Some(locs) = &embed
    {
        let mut seeds: Vec<(u32, bool)> = Vec::new();
        for u in 0..m {
            let ci_of_loc = locs[u].and_then(|r| candidates[u].iter().position(|&c| c == r));
            for (ci, &xv) in x_var[u].iter().enumerate() {
                seeds.push((xv, Some(ci) == ci_of_loc));
            }
            seeds.push((s_var[u], ci_of_loc.is_none()));
        }
        for (ti, &(au, bu, _pos)) in transitions.iter().enumerate() {
            let (t_store, t_reload, t_move) = trans_vars[ti];
            let (a, b) = (locs[au], locs[bu]);
            seeds.push((t_store, a.is_some() && b.is_none()));
            seeds.push((t_reload, a.is_none() && b.is_some()));
            seeds.push((t_move, matches!((a, b), (Some(x), Some(y)) if x != y)));
        }
        for (mp, &(du, su)) in move_pairs.iter().enumerate() {
            seeds.push((move_diff[mp], locs[du] != locs[su]));
        }
        solver.seed_phases(&seeds);
    }

    let result =
        solver.solve_optimize_interruptible(&objective, None, || Instant::now() >= deadline);
    let g_str = g.map_or_else(|| "-".to_string(), |g| g.to_string());
    let model = match result {
        PbCdclResult::Optimal(model, cost) => {
            if stats_enabled() {
                eprintln!("[ay-regalloc] segments: result=Optimal cost={cost} G={g_str}");
            }
            model
        }
        PbCdclResult::Feasible(model, cost) => {
            if stats_enabled() {
                eprintln!("[ay-regalloc] segments: result=Feasible cost={cost} G={g_str}");
            }
            model
        }
        PbCdclResult::Unsatisfiable => {
            if stats_enabled() {
                eprintln!("[ay-regalloc] segments: result=UNSAT G={g_str} -> greedy optimal");
            }
            return None;
        }
        _ => {
            if stats_enabled() {
                eprintln!("[ay-regalloc] segments: result=Unknown G={g_str} -> decline");
            }
            return None;
        }
    };

    // Decode per unit (exactly-one enforced here).
    let mut unit_assign: Vec<Option<PReg>> = Vec::with_capacity(m);
    for u in 0..m {
        let mut assigned: Option<PReg> = None;
        for (ci, &var) in x_var[u].iter().enumerate() {
            if model_at(&model, var) {
                assigned = Some(candidates[u][ci]);
                break;
            }
        }
        let spill = model_at(&model, s_var[u]);
        match (assigned, spill) {
            (Some(r), false) => unit_assign.push(Some(r)),
            (None, true) => unit_assign.push(None),
            // exactly-one violated (inconsistent untrusted model): decline.
            _ => return None,
        }
    }

    // STEP 5: the segment-level self-check — rejects an inconsistent solver
    // model before anything is materialized.
    if !segment_self_check(&units, vregs, &unit_assign, allocatable, reserved_regs) {
        if stats_enabled() {
            eprintln!("[ay-regalloc] segments: segment self-check REJECTED -> decline");
        }
        return None;
    }

    // Scatter unit assigns back into per-vreg decode vectors.
    let mut decode: Vec<Vec<Option<PReg>>> = Vec::with_capacity(n);
    for &(s, e) in &unit_range {
        decode.push(unit_assign[s..e].to_vec());
    }
    Some(decode)
}

/// Embed the baseline (greedy) record into the segment-unit space: each unit
/// takes the location of the greedy piece covering the unit's start position
/// (pieces are sorted by start and partition the vreg's extent). Returns `None`
/// when any modeled vreg is missing from the record — the caller then solves
/// without a bound or seeds (the run-both keep criterion still gates).
fn embed_record_into_units(rec: &GreedyRecord, units: &[SegUnit]) -> Option<Vec<Option<PReg>>> {
    let mut embed: Vec<Option<PReg>> = Vec::with_capacity(units.len());
    for u in units {
        let pieces = rec.pieces.get(&u.iv.vreg.id)?;
        if pieces.is_empty() {
            return None;
        }
        let lo = u.iv.start();
        let mut loc = pieces.first().and_then(|p| p.loc);
        for p in pieces {
            if p.start <= lo {
                loc = p.loc;
            } else {
                break;
            }
        }
        embed.push(loc);
    }
    Some(embed)
}

/// STEP 5 — the SEGMENT-LEVEL extension of the allocator self-check, run on the
/// decoded (untrusted) per-unit assignment BEFORE materialization:
///
/// 1. **Reference coverage** (the numbering-drift refutation): every use and
///    every def position of every modeled vreg must fall inside the extent of
///    EXACTLY ONE of that vreg's units — so each reference "sees" a
///    well-defined per-segment location, and a drifted/misaligned segmentation
///    (stale numbering, a use bucketed into a hole or into two segments) is
///    rejected here rather than silently mis-assigned.
/// 2. **Class + reserved legality** per assigned unit (over the unit's OWN
///    extent, so a reservation inside one segment cannot be masked by another).
/// 3. **Interference**: no two TRULY-overlapping units of different vregs may
///    hold aliasing pregs. Same-vreg segments are disjoint by construction and
///    connected by explicit split copies, so they are exempt.
///
/// Returns `false` to reject (caller declines to greedy). Purely a read-only
/// check — the always-on translation validator + the post-materialization
/// whole-vreg self-check remain the downstream gates.
fn segment_self_check(
    units: &[SegUnit],
    vregs: &[&LiveInterval],
    unit_assign: &[Option<PReg>],
    allocatable: &BTreeMap<RegClass, Vec<PReg>>,
    reserved_regs: &BTreeMap<PReg, Vec<u32>>,
) -> bool {
    let m = units.len();
    debug_assert_eq!(m, unit_assign.len());

    // (1) every use/def of each modeled vreg lands in exactly one of its units.
    for (vi, iv) in vregs.iter().enumerate() {
        for &p in iv.use_positions.iter().chain(iv.def_positions.iter()) {
            let covering = units
                .iter()
                .filter(|u| u.vi == vi && u.iv.start() <= p && p < u.iv.end())
                .count();
            if covering != 1 {
                return false;
            }
        }
    }

    // (2) class + reserved legality per assigned unit.
    for u in 0..m {
        if let Some(r) = unit_assign[u] {
            let ok_class = allocatable
                .get(&units[u].iv.vreg.class)
                .is_some_and(|pool| pool.contains(&r));
            if !ok_class || reserved_forbids(&units[u].iv, r, reserved_regs) {
                return false;
            }
        }
    }

    // (3) no two truly-overlapping units of different vregs on aliasing pregs.
    for u in 0..m {
        let Some(ri) = unit_assign[u] else { continue };
        for w in (u + 1)..m {
            let Some(rj) = unit_assign[w] else { continue };
            if units[u].vi != units[w].vi
                && allocator_pregs_overlap(ri, rj)
                && units[u].iv.overlaps(&units[w].iv)
            {
                return false;
            }
        }
    }
    true
}

/// Materialize the decoded per-segment assignment (step 6): split `func` at each
/// BB boundary where the decoded preg (or spill-state) changes, DRIVEN BY THE
/// DECODED PREGS (never the transition indicator slack), recomputing liveness /
/// block spans fresh before every split so the split point is always
/// correct-by-construction against the current (already-split) stream — the
/// LRSPLIT-1 numbering-drift lesson. Any `SplitError` (CFG-unsafe boundary) or
/// unexpected shape (a vreg or block span missing from the fresh recompute)
/// returns `None`: the caller DROPS the entire AY solution and greedy is kept —
/// never a partially-split hybrid allocation. On success returns the final
/// (allocation, spilled) over the post-split vregs.
fn materialize_segments(
    func: &mut RegAllocFunction,
    vregs: &[&LiveInterval],
    seg_of: &[Option<Vec<Segment>>],
    decode: &[Vec<Option<PReg>>],
) -> Option<(BTreeMap<VReg, PReg>, Vec<VReg>)> {
    let mut allocation: BTreeMap<VReg, PReg> = BTreeMap::new();
    let mut spilled: Vec<VReg> = Vec::new();

    let assign =
        |alloc: &mut BTreeMap<VReg, PReg>, sp: &mut Vec<VReg>, v: VReg, a: Option<PReg>| match a {
            Some(p) => {
                alloc.insert(v, p);
            }
            None => sp.push(v),
        };

    for vi in 0..vregs.len() {
        let vreg = vregs[vi].vreg;
        match &seg_of[vi] {
            // Whole vreg: single decode entry, unchanged in `func`.
            None => assign(&mut allocation, &mut spilled, vreg, decode[vi][0]),
            // Segmented vreg: group consecutive same-assign segments into runs and
            // split at each run boundary (the first block of the next run).
            Some(segs) => {
                // runs: (first_block_of_run, assign).
                let mut runs: Vec<(BlockId, Option<PReg>)> = Vec::new();
                for (k, seg) in segs.iter().enumerate() {
                    let a = decode[vi][k];
                    if runs.last().map(|r| r.1) != Some(a) {
                        runs.push((seg.block, a));
                    }
                }
                let mut current = vreg;
                for r in 1..runs.len() {
                    // FRESH liveness + spans: numbering may have drifted from
                    // prior splits (of this or another vreg). Derive the split
                    // point as the CURRENT start position of the next run's first
                    // block, so it is correct-by-construction.
                    let live = crate::liveness::compute_live_intervals(func);
                    let iv = live.intervals.get(&current.id).cloned()?;
                    let spans = block_spans(func);
                    let &(_, split_point, _) = spans.iter().find(|(b, _, _)| *b == runs[r].0)?;
                    // CFG-unsafe / holey boundary -> SplitError -> DROP the whole
                    // AY solution (the caller keeps greedy). Never a wrong copy,
                    // never a partial hybrid.
                    let res = match crate::split::split_interval_checked(&iv, split_point, func) {
                        Ok(res) => res,
                        Err(e) => {
                            if stats_enabled() {
                                eprintln!(
                                    "[ay-regalloc] segments: split of vreg {} at {split_point} \
                                     failed: {e:?}",
                                    current.id
                                );
                            }
                            return None;
                        }
                    };
                    // The truncated original id now covers the previous run.
                    assign(&mut allocation, &mut spilled, current, runs[r - 1].1);
                    current = res.new_vreg;
                }
                assign(
                    &mut allocation,
                    &mut spilled,
                    current,
                    runs[runs.len() - 1].1,
                );
            }
        }
    }

    Some((allocation, spilled))
}

/// Re-verify an AY assignment is legal without trusting the solver:
/// - every allocated preg is in its vreg's class pool and not reserved-forbidden;
/// - no two overlapping allocated vregs occupy aliasing pregs.
fn self_check(
    vregs: &[&LiveInterval],
    allocation: &BTreeMap<VReg, PReg>,
    allocatable: &BTreeMap<RegClass, Vec<PReg>>,
    reserved_regs: &BTreeMap<PReg, Vec<u32>>,
) -> bool {
    // Class + reserved legality.
    for iv in vregs {
        if let Some(&r) = allocation.get(&iv.vreg) {
            let ok_class = allocatable
                .get(&iv.vreg.class)
                .is_some_and(|pool| pool.contains(&r));
            if !ok_class || reserved_forbids(iv, r, reserved_regs) {
                return false;
            }
        }
    }
    // Pairwise interference legality.
    for i in 0..vregs.len() {
        let Some(&ri) = allocation.get(&vregs[i].vreg) else {
            continue;
        };
        for j in (i + 1)..vregs.len() {
            let Some(&rj) = allocation.get(&vregs[j].vreg) else {
                continue;
            };
            if allocator_pregs_overlap(ri, rj) && vregs[i].overlaps(vregs[j]) {
                return false;
            }
        }
    }
    true
}

/// Emit the linear "different-register" constraints for a copy `d <- s` onto
/// its `diff` boolean. `diff` is forced to 1 whenever the assignments of `d`
/// (index `di`) and `s` (index `si`) disagree on any candidate register, and is
/// left free (so the minimizing objective sets it to 0) exactly when they take
/// the same register or both spill. Purely objective-shaping — it adds no
/// constraint over the x_/s_ variables' feasible set.
pub(crate) fn add_move_constraints(
    constraints: &mut Vec<PbConstraint>,
    diff: u32,
    di: usize,
    si: usize,
    candidates: &[Vec<PReg>],
    x_var: &[Vec<u32>],
) {
    let x_of = |vi: usize, r: PReg| -> Option<u32> {
        candidates[vi]
            .iter()
            .position(|&c| c == r)
            .map(|ci| x_var[vi][ci])
    };
    // diff >= x_{d,r} - x_{s,r}  for each candidate r of d.
    for (ci, &r) in candidates[di].iter().enumerate() {
        let mut terms = vec![pos_term(diff), neg_term(x_var[di][ci])];
        if let Some(sv) = x_of(si, r) {
            terms.push(pos_term(sv));
        }
        constraints.push(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: 1,
        });
    }
    // diff >= x_{s,r} - x_{d,r}  for each candidate r of s.
    for (ci, &r) in candidates[si].iter().enumerate() {
        let mut terms = vec![pos_term(diff), neg_term(x_var[si][ci])];
        if let Some(dv) = x_of(di, r) {
            terms.push(pos_term(dv));
        }
        constraints.push(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: 1,
        });
    }
}

/// Emit the "which-transition" constraints for an adjacent SEGMENT pair of one
/// vreg onto its `(t_store, t_reload, t_move)` indicator triple, so the
/// objective can price each transition kind at its real cost (store/reload =
/// `SPILL_W`, move = `MOVE_W`, both loop-depth-weighted):
///
/// * `t_store  >= s_{bu} - s_{au}`                — reg->spill (a boundary store);
/// * `t_reload >= s_{au} - s_{bu}`                — spill->reg (a boundary reload);
/// * `t_move   >= x_{au,r} - x_{bu,r} - s_{bu}`   — reg->different-reg (a move),
///   one clause per candidate `r` of the earlier segment (the `- s_{bu}` term
///   exempts the reg->spill case, which `t_store` already prices).
///
/// spill->spill leaves all three free (the minimizing objective sets them 0) —
/// adjacent spilled segments share the slot, no boundary op. All gadgets are
/// ONE-SIDED: the two-sided move gadget on a non-interfering same-vreg segment
/// pair trips a debug-only soundness assertion in the shared ay-pb dense
/// conflict analysis (the original `add_boundary_constraints` lesson, kept by
/// the killcommit probe encoding this mirrors). Purely objective-shaping: adds
/// no constraint over the x_/s_ feasible set.
#[allow(clippy::too_many_arguments)]
fn add_transition_constraints(
    constraints: &mut Vec<PbConstraint>,
    (t_store, t_reload, t_move): (u32, u32, u32),
    au: usize,
    bu: usize,
    s_au: u32,
    s_bu: u32,
    candidates: &[Vec<PReg>],
    x_var: &[Vec<u32>],
) {
    let x_of = |vi: usize, r: PReg| -> Option<u32> {
        candidates[vi]
            .iter()
            .position(|&c| c == r)
            .map(|ci| x_var[vi][ci])
    };
    // t_store >= s_{bu} - s_{au}
    constraints.push(PbConstraint {
        terms: vec![pos_term(t_store), neg_term(s_bu), pos_term(s_au)],
        rel: PbRel::Ge,
        rhs: 1,
    });
    // t_reload >= s_{au} - s_{bu}
    constraints.push(PbConstraint {
        terms: vec![pos_term(t_reload), neg_term(s_au), pos_term(s_bu)],
        rel: PbRel::Ge,
        rhs: 1,
    });
    // t_move >= x_{au,r} - x_{bu,r} - s_{bu}  for each candidate r of au. (When
    // bu cannot take r at all the `- x_{bu,r}` term is absent: au-on-r then
    // always transitions unless bu spills.)
    for (ci, &r) in candidates[au].iter().enumerate() {
        let mut terms = vec![pos_term(t_move), neg_term(x_var[au][ci]), pos_term(s_bu)];
        if let Some(bv) = x_of(bu, r) {
            terms.push(pos_term(bv));
        }
        constraints.push(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: 1,
        });
    }
}

// ===========================================================================
// STEP 3 — PER-BASIC-BLOCK SEGMENTATION (the split PB encoding's soundness input)
// ===========================================================================
//
// A `Segment` is the intersection of a modeled vreg's live ranges with ONE
// block's contiguous global inst-position span. The per-segment PB encoding
// (steps 4-6) will introduce `x_{v,seg,r}` / `s_{v,seg}` variables per segment
// and interfere only truly-overlapping segment pairs. The LOAD-BEARING soundness
// property, unit-tested below, is that every use and every def of the vreg maps
// to EXACTLY ONE segment: a use/def sits at one instruction, which sits in one
// block (blocks partition the instruction stream), whose span contains exactly
// one of the vreg's segments. A boundary error here would let the encoding miss
// an interference or place a split copy on the wrong side — a miscompile — so it
// is validated in isolation before any encoding consumes it.

/// A per-basic-block live-range segment of a modeled vreg.
// Consumed by the split PB encoding (steps 4-6) + the segmentation unit tests;
// allow(dead_code) until the encoding wires it into the non-test path.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Segment {
    /// The block this segment lives in.
    pub block: BlockId,
    /// Inclusive global start position (the covered intersection's low bound).
    pub start: u32,
    /// Exclusive global end position (the covered intersection's high bound).
    pub end: u32,
    /// Use positions of the vreg that fall inside this block's span.
    pub use_positions: Vec<u32>,
    /// Def positions of the vreg that fall inside this block's span.
    pub def_positions: Vec<u32>,
}

/// The contiguous global inst-position span `[start, end)` of each block, in
/// `block_order`. This mirrors EXACTLY the linear numbering
/// `compute_live_intervals` assigns (walk `block_order`, then each block's
/// `insts`), so a segment's positions line up with the `use_positions` /
/// `def_positions` the interval carries. Empty blocks contribute no span.
#[allow(dead_code)]
pub(crate) fn block_spans(func: &RegAllocFunction) -> Vec<(BlockId, u32, u32)> {
    let mut spans = Vec::with_capacity(func.block_order.len());
    let mut idx = 0u32;
    for &block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id.0 as usize) else {
            continue;
        };
        let start = idx;
        idx += block.insts.len() as u32;
        if idx > start {
            spans.push((block_id, start, idx));
        }
    }
    spans
}

/// Partition `iv` into per-basic-block segments over `spans`: for each block
/// whose span intersects one of `iv`'s live ranges, one segment covering that
/// intersection and carrying the use/def positions that fall in the block. The
/// returned segments are in ascending program order and their extents are
/// pairwise disjoint (blocks partition the stream). Every one of `iv`'s use/def
/// positions lands in exactly one returned segment.
#[allow(dead_code)]
pub(crate) fn per_bb_segments(iv: &LiveInterval, spans: &[(BlockId, u32, u32)]) -> Vec<Segment> {
    let mut segments: Vec<Segment> = Vec::new();
    for &(block, bstart, bend) in spans {
        // Covered extent = union over ranges of (range ∩ block span). A block
        // holds one contiguous covered sub-span per intersecting range; take the
        // min/max so the segment brackets every covered position in the block.
        let mut seg_start = u32::MAX;
        let mut seg_end = 0u32;
        for r in &iv.ranges {
            let lo = r.start.max(bstart);
            let hi = r.end.min(bend);
            if lo < hi {
                seg_start = seg_start.min(lo);
                seg_end = seg_end.max(hi);
            }
        }
        if seg_start < seg_end {
            // A use/def sits at one instruction in one block, so bucketing by the
            // block span assigns it to exactly this block's (unique) segment.
            let use_positions: Vec<u32> = iv
                .use_positions
                .iter()
                .copied()
                .filter(|&p| bstart <= p && p < bend)
                .collect();
            let def_positions: Vec<u32> = iv
                .def_positions
                .iter()
                .copied()
                .filter(|&p| bstart <= p && p < bend)
                .collect();
            segments.push(Segment {
                block,
                start: seg_start,
                end: seg_end,
                use_positions,
                def_positions,
            });
        }
    }
    segments
}

/// The index of the segment whose covered extent `[start, end)` contains `pos`,
/// or `None` if `pos` is in a hole. Segments are ordered and disjoint, so this is
/// a binary search — the encoding uses it to route a use/def or an interference
/// point to its segment.
#[allow(dead_code)]
pub(crate) fn covering_segment(segments: &[Segment], pos: u32) -> Option<usize> {
    segments
        .binary_search_by(|seg| {
            if seg.end <= pos {
                std::cmp::Ordering::Less
            } else if seg.start > pos {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        })
        .ok()
}

#[inline]
pub(crate) fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

#[inline]
pub(crate) fn pos_term(var: u32) -> PbTerm {
    PbTerm {
        coeff: 1,
        lits: vec![lit(var)],
    }
}

#[inline]
pub(crate) fn neg_term(var: u32) -> PbTerm {
    PbTerm {
        coeff: 1,
        lits: vec![PbLit { var, negated: true }],
    }
}

/// Value of a 1-indexed PB variable in the model (`false` if out of range).
#[inline]
pub(crate) fn model_at(model: &[bool], var: u32) -> bool {
    model.get((var - 1) as usize).copied().unwrap_or(false)
}

#[cfg(test)]
mod traffic_tests {
    //! The commensurable TRAFFIC objective + greedy-as-incumbent warm start
    //! (the KILLCOMMIT f51f487 follow-up): the whole-vreg solve must minimize
    //! loop-depth-weighted spill traffic (not flat ref counts), and with an
    //! incumbent it must be strictly-better-or-decline.

    use std::collections::BTreeMap;

    use super::*;
    use crate::killcommit::record_from_whole;
    use crate::machine_types::{BlockId, InstFlags, InstId, MachInst, RegAllocBlock, RegClass};

    fn vreg(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr64,
        }
    }

    /// A function whose only role is to carry block spans + loop depths for
    /// the traffic objective: blocks of the given `(len, loop_depth)` in order.
    fn span_func(blocks: &[(u32, u32)]) -> RegAllocFunction {
        let nop = || MachInst {
            opcode: 1,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let total: u32 = blocks.iter().map(|&(n, _)| n).sum();
        let insts = (0..total).map(|_| nop()).collect();
        let mut ra_blocks = Vec::new();
        let mut base = 0u32;
        for &(n, depth) in blocks {
            ra_blocks.push(RegAllocBlock {
                insts: (base..base + n).map(InstId).collect(),
                preds: vec![],
                succs: vec![],
                loop_depth: depth,
            });
            base += n;
        }
        RegAllocFunction {
            name: "traffic_test".to_string(),
            insts,
            blocks: ra_blocks,
            block_order: (0..blocks.len() as u32).map(BlockId).collect(),
            entry_block: BlockId(0),
            next_vreg: 8,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        }
    }

    fn interval(id: u32, ranges: &[(u32, u32)], uses: &[u32], defs: &[u32]) -> LiveInterval {
        let mut iv = LiveInterval::new(vreg(id));
        for &(s, e) in ranges {
            iv.add_range(s, e);
        }
        iv.use_positions = uses.to_vec();
        iv.def_positions = defs.to_vec();
        iv
    }

    /// The two-vreg pressure shape the objective tests share: b0 [0,6) depth 0,
    /// b1 [6,12) depth 1; v0 is HOT (2 uses inside the loop, traffic 84), v1 is
    /// COLD (3 uses outside, traffic 16, but MORE refs than v0 — the old flat
    /// `uses+defs+1` cost ranks it as the more expensive spill). One register.
    fn hot_cold_instance() -> (
        RegAllocFunction,
        Vec<LiveInterval>,
        BTreeMap<RegClass, Vec<PReg>>,
    ) {
        let func = span_func(&[(6, 0), (6, 1)]);
        let intervals = vec![
            interval(0, &[(0, 12)], &[6, 7], &[0]), // hot: 4*(1+10+10) = 84
            interval(1, &[(0, 12)], &[2, 3, 4], &[1]), // cold: 4*(1+1+1+1) = 16
        ];
        let mut allocatable: BTreeMap<RegClass, Vec<PReg>> = BTreeMap::new();
        allocatable.insert(RegClass::Gpr64, vec![PReg::new(19)]);
        (func, intervals, allocatable)
    }

    /// THE OBJECTIVE FIX: with both vregs overlapping on one register, the
    /// traffic objective must spill the COLD vreg (traffic 16) and keep the
    /// HOT one (traffic 84) in the register — the OLD flat `uses+defs+1` cost
    /// ranked them the other way (cold 5 > hot 4) and spilled the hot one.
    #[test]
    fn traffic_objective_spills_cold_not_hot() {
        let (mut func, intervals, allocatable) = hot_cold_instance();
        let (result, spilled) = try_allocate(
            &mut func,
            &intervals,
            &allocatable,
            &BTreeMap::new(),
            &[],
            None,
        )
        .expect("AY must allocate the 2-vreg instance");
        assert_eq!(
            spilled,
            vec![vreg(1)],
            "the loop-cold vreg must be the spill under the traffic objective"
        );
        assert_eq!(
            result.allocation.get(&vreg(0)),
            Some(&PReg::new(19)),
            "the loop-hot vreg must keep the register"
        );
    }

    /// Warm start, decline half: when greedy already made the traffic-optimal
    /// choice (spilled the cold vreg, G = 16), the hard `<= G-1` bound is
    /// UNSATISFIABLE and the solve declines — greedy is kept, never re-derived.
    #[test]
    fn incumbent_bound_declines_when_greedy_optimal() {
        let (mut func, intervals, allocatable) = hot_cold_instance();
        let mut greedy_alloc: BTreeMap<VReg, PReg> = BTreeMap::new();
        greedy_alloc.insert(vreg(0), PReg::new(19));
        let rec = record_from_whole(&intervals, &greedy_alloc, &[vreg(1)]);
        assert!(
            try_allocate(
                &mut func,
                &intervals,
                &allocatable,
                &BTreeMap::new(),
                &[],
                Some(&rec),
            )
            .is_none(),
            "greedy optimal (G=16) => UNSAT under the hard bound => clean decline"
        );
    }

    /// Warm start, win half: when greedy made the traffic-SUBOPTIMAL choice
    /// (spilled the hot vreg, G = 84), the bounded solve finds the strictly
    /// better allocation (spill cold, traffic 16 <= G-1) and returns it.
    #[test]
    fn incumbent_bound_finds_strict_win() {
        let (mut func, intervals, allocatable) = hot_cold_instance();
        let mut greedy_alloc: BTreeMap<VReg, PReg> = BTreeMap::new();
        greedy_alloc.insert(vreg(1), PReg::new(19));
        let rec = record_from_whole(&intervals, &greedy_alloc, &[vreg(0)]);
        let (result, spilled) = try_allocate(
            &mut func,
            &intervals,
            &allocatable,
            &BTreeMap::new(),
            &[],
            Some(&rec),
        )
        .expect("a strictly-better whole-vreg allocation exists (16 < 84)");
        assert_eq!(
            spilled,
            vec![vreg(1)],
            "AY must spill the cold vreg instead"
        );
        assert_eq!(result.allocation.get(&vreg(0)), Some(&PReg::new(19)));
    }

    /// Warm start, nothing-to-beat half: greedy spilled nothing and has no
    /// move copies (G = 0) — the solve declines immediately (cost is
    /// non-negative, `<= -1` cannot be satisfied), spending none of the cap.
    #[test]
    fn incumbent_bound_declines_on_zero_g() {
        let func = span_func(&[(6, 0)]);
        let intervals = vec![
            interval(0, &[(0, 6)], &[2], &[0]),
            interval(1, &[(0, 6)], &[3], &[1]),
        ];
        let mut allocatable: BTreeMap<RegClass, Vec<PReg>> = BTreeMap::new();
        allocatable.insert(RegClass::Gpr64, vec![PReg::new(19), PReg::new(20)]);
        let mut greedy_alloc: BTreeMap<VReg, PReg> = BTreeMap::new();
        greedy_alloc.insert(vreg(0), PReg::new(19));
        greedy_alloc.insert(vreg(1), PReg::new(20));
        let rec = record_from_whole(&intervals, &greedy_alloc, &[]);
        let mut f = func;
        assert!(
            try_allocate(
                &mut f,
                &intervals,
                &allocatable,
                &BTreeMap::new(),
                &[],
                Some(&rec),
            )
            .is_none(),
            "G=0 => greedy unbeatable => decline without solving"
        );
    }

    /// Warm-start form (b) seed translation: the baseline record maps onto the
    /// PB variable space exactly — reg-assigned vreg (its candidate true, the
    /// rest + spill false), spilled vreg (spill true), a collapsed location
    /// OUTSIDE the candidate pool (treated as spilled), an UNRECORDED vreg
    /// (left unseeded), and a move `diff` seeded to whether the endpoints'
    /// collapsed locations differ.
    #[test]
    fn greedy_phase_seeds_translate_record() {
        use crate::killcommit::{GreedyPiece, GreedyRecord};

        let intervals = [
            interval(0, &[(0, 8)], &[4], &[0]), // greedy: PReg 20
            interval(1, &[(0, 8)], &[5], &[1]), // greedy: spilled
            interval(2, &[(0, 8)], &[6], &[2]), // greedy: PReg 21 (not a candidate)
            interval(3, &[(0, 8)], &[7], &[3]), // unrecorded
        ];
        let vregs: Vec<&LiveInterval> = intervals.iter().collect();
        let candidates: Vec<Vec<PReg>> = vec![
            vec![PReg::new(19), PReg::new(20)],
            vec![PReg::new(19)],
            vec![PReg::new(19), PReg::new(20)],
            vec![PReg::new(19)],
        ];
        // Realistic numbering: x-row then s per vreg, diffs after all.
        let x_var: Vec<Vec<u32>> = vec![vec![1, 2], vec![4], vec![6, 7], vec![9]];
        let s_var: Vec<u32> = vec![3, 5, 8, 10];
        let move_pairs: Vec<(usize, usize)> = vec![(0, 1), (0, 3)];
        let diff_var: Vec<u32> = vec![11, 12];

        let mut rec = GreedyRecord::default();
        let piece = |loc: Option<PReg>| GreedyPiece {
            start: 0,
            end: 8,
            loc,
        };
        rec.pieces.insert(0, vec![piece(Some(PReg::new(20)))]);
        rec.pieces.insert(1, vec![piece(None)]);
        rec.pieces.insert(2, vec![piece(Some(PReg::new(21)))]);

        let seeds = greedy_phase_seeds(
            &rec,
            &vregs,
            &candidates,
            &x_var,
            &s_var,
            &move_pairs,
            &diff_var,
        );
        assert_eq!(
            seeds,
            vec![
                // v0: PReg 20 = candidate index 1
                (1, false),
                (2, true),
                (3, false),
                // v1: spilled
                (4, false),
                (5, true),
                // v2: collapsed loc outside the pool -> seeded as spilled
                (6, false),
                (7, false),
                (8, true),
                // v3 unrecorded: NO seeds for vars 9/10.
                // move (v0, v1): Some(20) vs None differ -> diff true.
                (11, true),
                // move (v0, v3): v3 unrecorded -> no diff seed for var 12.
            ]
        );
    }

    /// REFUTATION: an ADVERSARIAL record whose whole-vreg collapse is an
    /// ILLEGAL allocation (both overlapping vregs claimed on the single
    /// register — the shape a split-heavy greedy record can collapse to)
    /// seeds the solver toward an infeasible corner, yet the result is still
    /// legal and strictly better than G: the hard interference constraints +
    /// the `<= G-1` bound + the self-check dominate the polarity bias. Also
    /// pins determinism of the seeded path (same input -> same allocation).
    #[test]
    fn adversarial_seed_cannot_corrupt_the_result() {
        use crate::killcommit::{GreedyPiece, GreedyRecord};

        let (mut func, intervals, allocatable) = hot_cold_instance();
        // v0 whole on PReg 19; v1 ALSO claims PReg 19 in its first piece
        // (illegal with v0 — they overlap), then spills its tail. The
        // collapse seeds BOTH x_{v,19} true. G = one spill-side transition
        // at pos 6 (depth 1) = SPILL_W * 10 = 40 > the true optimum 16.
        let mut rec = GreedyRecord::default();
        rec.pieces.insert(
            0,
            vec![GreedyPiece {
                start: 0,
                end: 12,
                loc: Some(PReg::new(19)),
            }],
        );
        rec.pieces.insert(
            1,
            vec![
                GreedyPiece {
                    start: 0,
                    end: 6,
                    loc: Some(PReg::new(19)),
                },
                GreedyPiece {
                    start: 6,
                    end: 12,
                    loc: None,
                },
            ],
        );

        let run = |func: &mut RegAllocFunction| {
            try_allocate(
                func,
                &intervals,
                &allocatable,
                &BTreeMap::new(),
                &[],
                Some(&rec),
            )
        };
        let (result, spilled) = run(&mut func)
            .expect("a strictly-better legal allocation exists (spill cold = 16 < G = 40)");
        // Legality despite the colliding seed: exactly one of the two
        // overlapping vregs holds the register, the other is spilled.
        assert_eq!(spilled, vec![vreg(1)], "the cold vreg is the cheaper spill");
        assert_eq!(result.allocation.get(&vreg(0)), Some(&PReg::new(19)));
        assert_eq!(result.allocation.get(&vreg(1)), None);

        // Determinism of the seeded path.
        let mut func2 = hot_cold_instance().0;
        let (result2, spilled2) = run(&mut func2).expect("deterministic rerun");
        assert_eq!(result.allocation, result2.allocation);
        assert_eq!(spilled, spilled2);
    }

    /// The depth map itself: positions map to their block's `10^depth` factor,
    /// and out-of-span positions degrade to factor 1.
    #[test]
    fn depth_map_factors() {
        let func = span_func(&[(3, 0), (4, 2), (2, 1)]);
        let dm = DepthMap::new(&func);
        assert_eq!(dm.factor_at(0), 1);
        assert_eq!(dm.factor_at(2), 1);
        assert_eq!(dm.factor_at(3), 100);
        assert_eq!(dm.factor_at(6), 100);
        assert_eq!(dm.factor_at(7), 10);
        assert_eq!(dm.factor_at(8), 10);
        assert_eq!(dm.factor_at(9), 1, "past the last span -> factor 1");
        let iv = interval(0, &[(0, 9)], &[2, 3, 8], &[0]);
        // 4*(1 + 1 + 100 + 10)
        assert_eq!(spill_traffic(&iv, &dm), 448);
    }
}

#[cfg(test)]
mod segment_tests {
    use super::*;
    use crate::liveness::LiveInterval;
    use crate::machine_types::{BlockId, InstId, RegAllocBlock, RegAllocFunction, RegClass, VReg};
    use std::collections::BTreeMap;

    fn iv(id: u32, ranges: &[(u32, u32)], uses: &[u32], defs: &[u32]) -> LiveInterval {
        let mut iv = LiveInterval::new(VReg {
            id,
            class: RegClass::Gpr64,
        });
        for &(s, e) in ranges {
            iv.add_range(s, e);
        }
        iv.use_positions = uses.to_vec();
        iv.def_positions = defs.to_vec();
        iv
    }

    /// THE LOAD-BEARING SOUNDNESS PROPERTY (plan step 3): every use and every def
    /// of a vreg maps to EXACTLY ONE per-BB segment, across straight-line, holey,
    /// single-block, and one-segment-per-block layouts. A miss here would let the
    /// encoding drop an interference or split-copy on the wrong side.
    #[test]
    fn every_use_def_in_exactly_one_segment() {
        // Three blocks partition positions: [0,4), [4,10), [10,14).
        let spans = vec![
            (BlockId(0), 0, 4),
            (BlockId(1), 4, 10),
            (BlockId(2), 10, 14),
        ];
        let cases = [
            iv(0, &[(0, 14)], &[2, 5, 9, 11], &[0]), // live-through all blocks
            iv(1, &[(1, 4), (6, 12)], &[3, 7, 11], &[1, 6]), // holey (hole [4,6))
            iv(2, &[(10, 13)], &[12], &[10]),        // single block
            iv(3, &[(0, 2), (4, 6), (10, 12)], &[1, 5, 11], &[0, 4, 10]), // one seg / block
        ];
        for case in &cases {
            let segs = per_bb_segments(case, &spans);
            // (a) each use maps to exactly one segment, and covering_segment agrees.
            for &u in &case.use_positions {
                let hits = segs.iter().filter(|s| s.use_positions.contains(&u)).count();
                assert_eq!(
                    hits, 1,
                    "use {u} of vreg {} must land in exactly one segment (got {hits}); segs={segs:?}",
                    case.vreg.id
                );
                let ci = covering_segment(&segs, u).expect("use position must be covered");
                assert!(
                    segs[ci].use_positions.contains(&u),
                    "covering_segment routed use {u} to a segment that does not own it"
                );
            }
            // (b) each def maps to exactly one segment.
            for &d in &case.def_positions {
                let hits = segs.iter().filter(|s| s.def_positions.contains(&d)).count();
                assert_eq!(
                    hits, 1,
                    "def {d} of vreg {} must land in exactly one segment (got {hits}); segs={segs:?}",
                    case.vreg.id
                );
            }
            // (c) segment extents are ordered and pairwise disjoint (blocks
            //     partition the stream — same-vreg segments never interfere).
            for w in segs.windows(2) {
                assert!(
                    w[0].end <= w[1].start,
                    "segments overlap or are unordered: {segs:?}"
                );
            }
            // (d) every segment extent lies within its block's span.
            for s in &segs {
                let (_, bs, be) = *spans.iter().find(|(b, _, _)| *b == s.block).unwrap();
                assert!(
                    bs <= s.start && s.end <= be,
                    "segment {s:?} escapes its block span [{bs},{be})"
                );
            }
        }
    }

    /// END-TO-END of the per-segment split path (steps 4-6): a `live-through-
    /// but-unused-in-the-middle` vreg under register pressure is segmented, the
    /// per-segment PB spills its cheap middle segment, and the DECODED-preg-driven
    /// materialization splits the function and produces an allocation that stays
    /// LEGAL against the actual post-split stream and covers every live vreg.
    #[test]
    fn segmented_solve_and_materialize_stays_legal() {
        use crate::machine_types::{InstFlags, MachInst, MachOperand};
        // 3 blocks. A(v0) is defined in block0, used in block2, LIVE-THROUGH block1
        // but UNUSED there. B(v1), C(v2) are defined + used twice in block1 (higher
        // spill cost than A). With only 2 registers, block1 has A+B+C live (pressure
        // 3), so whole-vreg AY spills the cheapest whole vreg (A) -> A is the spill-
        // delta vreg and gets per-BB segmented; the per-segment PB should spill A's
        // cheap live-through-unused MIDDLE segment and keep A in a register in the
        // outer blocks. Whatever it decides, the materialized allocation MUST stay
        // legal (self-check) and cover every live vreg.
        let a = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let b = VReg {
            id: 1,
            class: RegClass::Gpr64,
        };
        let c = VReg {
            id: 2,
            class: RegClass::Gpr64,
        };
        let mov = |d: VReg, imm: i64| MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(d)],
            uses: vec![MachOperand::Imm(imm)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let useop = |vs: &[VReg]| MachInst {
            opcode: 2,
            defs: vec![],
            uses: vs.iter().map(|&v| MachOperand::VReg(v)).collect(),
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let br = |target: u32| MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(target))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        };
        // 0:A=imm 1:br1 | 2:B=imm 3:C=imm 4:use(B,C) 5:use(B,C) 6:use(B,C) 7:br2
        // | 8:use(A) 9:use(A)
        // (TWO tail uses so a reload boundary at block2's start is not the
        // interval's final instruction — a single-use tail makes the spill->reg
        // split degenerate [NonProgress] and the whole solution is DROPPED; that
        // shape is pinned by `materialize_drops_on_degenerate_tail_boundary`.
        // THREE B/C uses so A [traffic 12] is strictly the cheapest whole-vreg
        // spill vs B/C [16] and stays the delta vreg deterministically.)
        let insts = vec![
            mov(a, 0),
            br(1),
            mov(b, 1),
            mov(c, 2),
            useop(&[b, c]),
            useop(&[b, c]),
            useop(&[b, c]),
            br(2),
            useop(&[a]),
            useop(&[a]),
        ];
        let blocks = vec![
            RegAllocBlock {
                insts: vec![InstId(0), InstId(1)],
                preds: vec![],
                succs: vec![BlockId(1)],
                loop_depth: 0,
            },
            RegAllocBlock {
                insts: vec![
                    InstId(2),
                    InstId(3),
                    InstId(4),
                    InstId(5),
                    InstId(6),
                    InstId(7),
                ],
                preds: vec![BlockId(0)],
                succs: vec![BlockId(2)],
                loop_depth: 0,
            },
            RegAllocBlock {
                insts: vec![InstId(8), InstId(9)],
                preds: vec![BlockId(1)],
                succs: vec![],
                loop_depth: 0,
            },
        ];
        let mut func = RegAllocFunction {
            name: "seg_pressure".to_string(),
            insts,
            blocks,
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let mut allocatable: BTreeMap<RegClass, Vec<PReg>> = BTreeMap::new();
        allocatable.insert(RegClass::Gpr64, vec![PReg::new(19), PReg::new(20)]); // 2 regs
        let reserved: BTreeMap<PReg, Vec<u32>> = BTreeMap::new();
        let copies: Vec<(VReg, VReg)> = Vec::new();

        // Whole-vreg solve -> spill-delta set.
        let live = crate::liveness::compute_live_intervals(&func);
        let intervals: Vec<LiveInterval> = live.intervals.values().cloned().collect();
        let (_wv_alloc, wv_spilled) =
            solve_whole_vreg(&func, &intervals, &allocatable, &reserved, &copies, None)
                .expect("whole-vreg");
        assert!(
            !wv_spilled.is_empty(),
            "register pressure must force a spill"
        );

        // Segment the delta set (per-BB, >= 2 segments).
        let vregs: Vec<&LiveInterval> = intervals
            .iter()
            .filter(|iv| !iv.ranges.is_empty())
            .collect();
        let spans = block_spans(&func);
        let delta: BTreeSet<u32> = wv_spilled.iter().map(|v| v.id).collect();
        let seg_of: Vec<Option<Vec<Segment>>> = vregs
            .iter()
            .map(|iv| {
                if delta.contains(&iv.vreg.id) {
                    let segs = per_bb_segments(iv, &spans);
                    (segs.len() >= 2).then_some(segs)
                } else {
                    None
                }
            })
            .collect();
        assert!(
            seg_of.iter().any(Option::is_some),
            "the spill-delta vreg should be multi-block and get segmented"
        );

        // Solve + materialize the per-segment PB (no incumbent: unbounded solve).
        let decode = solve_segmented(
            &func,
            &vregs,
            &seg_of,
            &allocatable,
            &reserved,
            &copies,
            None,
        )
        .expect("segmented solve");
        let (allocation, spilled) = materialize_segments(&mut func, &vregs, &seg_of, &decode)
            .expect("materialization must succeed on this straight-line CFG");

        // The materialized allocation must be LEGAL against the post-split stream
        // and cover every live vreg — the correct-by-construction invariant.
        let post = crate::liveness::compute_live_intervals(&func);
        let post_reserved = crate::implicit_def_reservations(&func, &post.inst_numbering);
        let post_intervals: Vec<&LiveInterval> = post.intervals.values().collect();
        assert!(
            self_check(&post_intervals, &allocation, &allocatable, &post_reserved),
            "post-materialization self-check must pass: alloc={allocation:?} spilled={spilled:?}"
        );
        let spilled_set: BTreeSet<u32> = spilled.iter().map(|v| v.id).collect();
        for iv in &post_intervals {
            assert!(
                allocation.contains_key(&iv.vreg) || spilled_set.contains(&iv.vreg.id),
                "vreg {} neither allocated nor spilled",
                iv.vreg.id
            );
        }
        // A split must have been materialized (a sub-vreg created), proving the
        // segmented path actually split the live-through vreg.
        assert!(func.next_vreg > 3, "expected a split to create a sub-vreg");
    }

    /// REFUTATION (step 6 drop semantics): a decode whose spill->reg boundary
    /// lands on the interval's FINAL instruction cannot be materialized
    /// (`split_interval_checked` returns `NonProgress` — the original would keep
    /// its whole extent). `materialize_segments` must return `None` — DROP the
    /// entire AY solution — never a partially-split hybrid, even though earlier
    /// boundaries of the same vreg already split fine (the caller then discards
    /// the mutated clone and keeps greedy).
    #[test]
    fn materialize_drops_on_degenerate_tail_boundary() {
        use crate::machine_types::{InstFlags, MachInst, MachOperand};
        let a = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let mov = |d: VReg| MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(d)],
            uses: vec![MachOperand::Imm(7)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let useop = |v: VReg| MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let br = |t: u32| MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(t))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        };
        // 0:A=imm 1:br1 | 2:nop 3:nop 4:br2 | 5:use(A)   (single-use tail!)
        let nop = || MachInst {
            opcode: 1,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let insts = vec![mov(a), br(1), nop(), nop(), br(2), useop(a)];
        let blocks = vec![
            RegAllocBlock {
                insts: vec![InstId(0), InstId(1)],
                preds: vec![],
                succs: vec![BlockId(1)],
                loop_depth: 0,
            },
            RegAllocBlock {
                insts: vec![InstId(2), InstId(3), InstId(4)],
                preds: vec![BlockId(0)],
                succs: vec![BlockId(2)],
                loop_depth: 0,
            },
            RegAllocBlock {
                insts: vec![InstId(5)],
                preds: vec![BlockId(1)],
                succs: vec![],
                loop_depth: 0,
            },
        ];
        let mut func = RegAllocFunction {
            name: "degenerate_tail".to_string(),
            insts,
            blocks,
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let live = crate::liveness::compute_live_intervals(&func);
        let iv0 = live.intervals.get(&0).cloned().expect("A is live");
        let vregs: Vec<&LiveInterval> = vec![&iv0];
        let spans = block_spans(&func);
        let segs = per_bb_segments(&iv0, &spans);
        assert_eq!(segs.len(), 3);
        let seg_of = vec![Some(segs)];
        // Hand-built decode: reg / spill / reg — the tail boundary is degenerate.
        let decode = vec![vec![Some(PReg::new(19)), None, Some(PReg::new(19))]];
        assert!(
            materialize_segments(&mut func, &vregs, &seg_of, &decode).is_none(),
            "a degenerate boundary must DROP the whole solution, not spill a remainder"
        );
    }

    /// A vreg live in only one block yields exactly one segment, for that block.
    #[test]
    fn segments_only_where_live() {
        let spans = vec![
            (BlockId(0), 0, 4),
            (BlockId(1), 4, 10),
            (BlockId(2), 10, 14),
        ];
        let case = iv(0, &[(5, 9)], &[8], &[5]); // live only inside block 1
        let segs = per_bb_segments(&case, &spans);
        assert_eq!(segs.len(), 1, "one live block => one segment");
        assert_eq!(segs[0].block, BlockId(1));
        assert_eq!((segs[0].start, segs[0].end), (5, 9));
        assert_eq!(segs[0].use_positions, vec![8]);
        assert_eq!(segs[0].def_positions, vec![5]);
        // A position in a hole is covered by no segment.
        assert!(covering_segment(&segs, 2).is_none());
    }

    /// `block_spans` reproduces the linear numbering `compute_live_intervals`
    /// assigns (walk block_order, then each block's insts). Blocks of sizes
    /// 2,3,1 in order 0,1,2 give spans [0,2),[2,5),[5,6); an empty block yields
    /// no span.
    #[test]
    fn block_spans_match_linear_numbering() {
        let mk = |ninsts: u32, base: u32| RegAllocBlock {
            insts: (base..base + ninsts).map(InstId).collect(),
            preds: Vec::new(),
            succs: Vec::new(),
            loop_depth: 0,
        };
        let func = RegAllocFunction {
            name: "spans".to_string(),
            insts: Vec::new(), // block_spans reads only block.insts.len()
            blocks: vec![mk(2, 0), mk(3, 2), mk(0, 5), mk(1, 5)],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 0,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let spans = block_spans(&func);
        // Block 2 is empty => contributes no span; the rest are contiguous.
        assert_eq!(
            spans,
            vec![(BlockId(0), 0, 2), (BlockId(1), 2, 5), (BlockId(3), 5, 6)]
        );
    }

    /// Build a `SegUnit` for the self-check refutation tests.
    fn unit(vi: usize, id: u32, range: (u32, u32), uses: &[u32], defs: &[u32]) -> SegUnit {
        let iv = iv(id, &[range], uses, defs);
        SegUnit {
            vi,
            candidates: vec![PReg::new(19), PReg::new(20)],
            iv,
        }
    }

    fn gpr_pool() -> BTreeMap<RegClass, Vec<PReg>> {
        let mut allocatable: BTreeMap<RegClass, Vec<PReg>> = BTreeMap::new();
        allocatable.insert(RegClass::Gpr64, vec![PReg::new(19), PReg::new(20)]);
        allocatable
    }

    /// REFUTATION (step 5): two TRULY-overlapping segments of different vregs on
    /// the SAME preg must be rejected by the segment-level self-check; the same
    /// shape on different pregs passes. An untrusted solver model that violates
    /// its own interference constraints can therefore never be materialized.
    #[test]
    fn segment_self_check_rejects_overlapping_same_preg() {
        let iv0 = iv(0, &[(0, 8)], &[2], &[0]);
        let iv1 = iv(1, &[(4, 12)], &[6], &[4]);
        let vregs: Vec<&LiveInterval> = vec![&iv0, &iv1];
        let units = vec![
            unit(0, 0, (0, 8), &[2], &[0]),
            unit(1, 1, (4, 12), &[6], &[4]),
        ];
        let allocatable = gpr_pool();
        let reserved: BTreeMap<PReg, Vec<u32>> = BTreeMap::new();

        // Same preg on overlapping units of different vregs: REJECT.
        assert!(
            !segment_self_check(
                &units,
                &vregs,
                &[Some(PReg::new(19)), Some(PReg::new(19))],
                &allocatable,
                &reserved,
            ),
            "overlapping segments of different vregs on one preg must be rejected"
        );
        // Different pregs: legal.
        assert!(segment_self_check(
            &units,
            &vregs,
            &[Some(PReg::new(19)), Some(PReg::new(20))],
            &allocatable,
            &reserved,
        ));
        // One spilled: legal.
        assert!(segment_self_check(
            &units,
            &vregs,
            &[Some(PReg::new(19)), None],
            &allocatable,
            &reserved,
        ));
        // A preg outside the class pool: REJECT.
        assert!(!segment_self_check(
            &units,
            &vregs,
            &[Some(PReg::new(7)), None],
            &allocatable,
            &reserved,
        ));
    }

    /// REFUTATION (the numbering-drift catch): a segmentation whose units MISS a
    /// use position of their vreg — the shape a stale instruction numbering
    /// produces (segments derived from one numbering, references from another)
    /// — must be rejected by the segment-level self-check, and a DOUBLE-covered
    /// reference (overlapping same-vreg units) likewise. The aligned control
    /// passes.
    #[test]
    fn segment_self_check_rejects_drifted_segmentation() {
        let iv0 = iv(0, &[(0, 14)], &[2, 5], &[0]);
        let vregs: Vec<&LiveInterval> = vec![&iv0];
        let allocatable = gpr_pool();
        let reserved: BTreeMap<PReg, Vec<u32>> = BTreeMap::new();
        let assign = [Some(PReg::new(19)), Some(PReg::new(19))];

        // DRIFTED: units [0,4) + [6,14) — use@5 is covered by NO unit.
        let drifted = vec![
            unit(0, 0, (0, 4), &[2], &[0]),
            unit(0, 0, (6, 14), &[], &[]),
        ];
        assert!(
            !segment_self_check(&drifted, &vregs, &assign, &allocatable, &reserved),
            "a use position outside every segment (numbering drift) must be rejected"
        );

        // DOUBLE-COVERED: units [0,8) + [4,14) — use@5 is covered by TWO units.
        let doubled = vec![
            unit(0, 0, (0, 8), &[2, 5], &[0]),
            unit(0, 0, (4, 14), &[5], &[]),
        ];
        assert!(
            !segment_self_check(&doubled, &vregs, &assign, &allocatable, &reserved),
            "a use position covered by two same-vreg segments must be rejected"
        );

        // ALIGNED control: units [0,4) + [4,14) cover every reference once.
        let aligned = vec![
            unit(0, 0, (0, 4), &[2], &[0]),
            unit(0, 0, (4, 14), &[5], &[]),
        ];
        assert!(segment_self_check(
            &aligned,
            &vregs,
            &assign,
            &allocatable,
            &reserved
        ));
    }

    /// BOUNDARY-COST CORRECTNESS at the gadget level: on a minimal 2-unit
    /// instance, force each of the four adjacent-location cases and assert the
    /// minimized objective pays exactly the intended transition cost —
    /// reg->reg' = MOVE_W, reg->spill = SPILL_W (t_store), spill->reg = SPILL_W
    /// (t_reload), same-reg / spill->spill = 0.
    #[test]
    fn transition_gadget_prices_each_case_exactly() {
        // Vars: unit a: x19=1, x20=2, s=3; unit b: x19=4, x20=5, s=6;
        // t_store=7, t_reload=8, t_move=9.
        let candidates: Vec<Vec<PReg>> = vec![
            vec![PReg::new(19), PReg::new(20)],
            vec![PReg::new(19), PReg::new(20)],
        ];
        let x_var: Vec<Vec<u32>> = vec![vec![1, 2], vec![4, 5]];
        let (s_a, s_b) = (3u32, 6u32);

        // (forced-a, forced-b, expected minimized cost) where a/b force is the
        // 1-indexed var that must be TRUE for that unit.
        let cases: [(u32, u32, i128); 5] = [
            (1, 5, MOVE_W),  // r19 -> r20: a move
            (1, 6, SPILL_W), // r19 -> spill: a store
            (3, 4, SPILL_W), // spill -> r19: a reload
            (1, 4, 0),       // r19 -> r19: free
            (3, 6, 0),       // spill -> spill: free
        ];
        for (fa, fb, expected) in cases {
            let mut constraints: Vec<PbConstraint> = Vec::new();
            // exactly-one per unit.
            for vars in [[1u32, 2, 3], [4u32, 5, 6]] {
                constraints.push(PbConstraint {
                    terms: vars.iter().map(|&v| pos_term(v)).collect(),
                    rel: PbRel::Eq,
                    rhs: 1,
                });
            }
            // Force the case's locations.
            for v in [fa, fb] {
                constraints.push(PbConstraint {
                    terms: vec![pos_term(v)],
                    rel: PbRel::Eq,
                    rhs: 1,
                });
            }
            add_transition_constraints(
                &mut constraints,
                (7, 8, 9),
                0,
                1,
                s_a,
                s_b,
                &candidates,
                &x_var,
            );
            let obj_terms = vec![
                PbTerm {
                    coeff: SPILL_W,
                    lits: vec![lit(7)],
                },
                PbTerm {
                    coeff: SPILL_W,
                    lits: vec![lit(8)],
                },
                PbTerm {
                    coeff: MOVE_W,
                    lits: vec![lit(9)],
                },
            ];
            let objective = PbObjective { terms: obj_terms };
            let instance = PbInstance {
                num_vars: 9,
                num_constraints: constraints.len() as u32,
                constraints,
                objective: Some(objective.clone()),
            };
            let mut solver = PbCdclSolver::new(&instance);
            match solver.solve_optimize(&objective, None) {
                PbCdclResult::Optimal(_, cost) => assert_eq!(
                    cost, expected,
                    "case force({fa},{fb}) must price the boundary at {expected}"
                ),
                other => panic!("case force({fa},{fb}): expected Optimal, got {other:?}"),
            }
        }
    }

    /// BOUNDARY-COST CORRECTNESS end-to-end + ADVERSARIAL WARM START: with free
    /// registers everywhere, a segmented vreg must come out in ONE location
    /// across all its segments (transitions cost > 0), even when the incumbent
    /// record EMBEDS a location change (r19 in the first piece, r20 after) and
    /// therefore seeds the solver at the fragmented corner: the hard `<= G-1`
    /// bound (G = the embedded move) forces the solver to REPAIR to the stable
    /// zero-transition assignment. Pins that G-evaluation, the transition
    /// objective, and the seeds all price the same currency.
    #[test]
    fn segmented_solve_repairs_fragmented_incumbent() {
        use crate::killcommit::{GreedyPiece, GreedyRecord};

        // Three blocks [0,4) [4,10) [10,14), no loops; one vreg live across all
        // three with a use in each; two free registers.
        let func = {
            let mk = |n: u32, base: u32| RegAllocBlock {
                insts: (base..base + n).map(InstId).collect(),
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            };
            RegAllocFunction {
                name: "stable".to_string(),
                insts: Vec::new(),
                blocks: vec![mk(4, 0), mk(6, 4), mk(4, 10)],
                block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
                entry_block: BlockId(0),
                next_vreg: 1,
                next_stack_slot: 0,
                stack_slots: BTreeMap::new(),
            }
        };
        let iv0 = iv(0, &[(0, 14)], &[2, 5, 11], &[0]);
        let vregs: Vec<&LiveInterval> = vec![&iv0];
        let spans = block_spans(&func);
        let segs = per_bb_segments(&iv0, &spans);
        assert_eq!(segs.len(), 3);
        let seg_of = vec![Some(segs)];
        let allocatable = gpr_pool();
        let reserved: BTreeMap<PReg, Vec<u32>> = BTreeMap::new();

        // Adversarial incumbent: r19 for [0,4), then r20 — one embedded move
        // (G = MOVE_W) and seeds pointing at the fragmented corner.
        let mut rec = GreedyRecord::default();
        rec.pieces.insert(
            0,
            vec![
                GreedyPiece {
                    start: 0,
                    end: 4,
                    loc: Some(PReg::new(19)),
                },
                GreedyPiece {
                    start: 4,
                    end: 14,
                    loc: Some(PReg::new(20)),
                },
            ],
        );

        let decode = solve_segmented(
            &func,
            &vregs,
            &seg_of,
            &allocatable,
            &reserved,
            &[],
            Some(&rec),
        )
        .expect("a strictly-better (stable, zero-transition) assignment exists");
        let locs = &decode[0];
        assert_eq!(locs.len(), 3);
        assert!(locs[0].is_some(), "free registers: nothing may spill");
        assert!(
            locs.iter().all(|l| *l == locs[0]),
            "boundary costs must force ONE stable location, got {locs:?}"
        );
    }

    /// THE PER-BB SPLIT WIN SHAPE (the reserved-call block): one register, a
    /// vreg live through three blocks with a hot middle, and a reserved point
    /// (an ABI clobber / call) in the LAST block that forbids the register
    /// there. Whole-vreg must spill everything (the pool is empty over the full
    /// range); the segmented model must keep the register in the first two
    /// blocks and spill ONLY the last segment, beating the whole-spill
    /// incumbent under the hard G-1 bound.
    #[test]
    fn segmented_solve_isolates_reserved_block() {
        use crate::killcommit::record_from_whole;

        let func = {
            let mk = |n: u32, base: u32, depth: u32| RegAllocBlock {
                insts: (base..base + n).map(InstId).collect(),
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: depth,
            };
            RegAllocFunction {
                name: "reserved_block".to_string(),
                insts: Vec::new(),
                blocks: vec![mk(3, 0, 0), mk(3, 3, 1), mk(5, 6, 0)],
                block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
                entry_block: BlockId(0),
                next_vreg: 1,
                next_stack_slot: 0,
                stack_slots: BTreeMap::new(),
            }
        };
        // def@0, hot uses@3,4 (depth 1), use@10 after the reserved point@8.
        let iv0 = iv(0, &[(0, 11)], &[3, 4, 10], &[0]);
        let vregs: Vec<&LiveInterval> = vec![&iv0];
        let mut allocatable: BTreeMap<RegClass, Vec<PReg>> = BTreeMap::new();
        allocatable.insert(RegClass::Gpr64, vec![PReg::new(19)]);
        let mut reserved: BTreeMap<PReg, Vec<u32>> = BTreeMap::new();
        reserved.insert(PReg::new(19), vec![8]);

        // Whole-vreg control: the single reg is reserved-forbidden over the full
        // range -> forced whole spill.
        let intervals = vec![iv0.clone()];
        let (wv_alloc, wv_spilled) =
            solve_whole_vreg(&func, &intervals, &allocatable, &reserved, &[], None)
                .expect("whole-vreg models (forced spill)");
        assert!(wv_alloc.is_empty());
        assert_eq!(wv_spilled, vec![iv0.vreg]);

        // Segmented with the whole-spill incumbent (G = 4*(1+10+10+1) = 88).
        let spans = block_spans(&func);
        let segs = per_bb_segments(&iv0, &spans);
        assert_eq!(segs.len(), 3);
        let seg_of = vec![Some(segs)];
        let rec = record_from_whole(&intervals, &BTreeMap::new(), &[iv0.vreg]);
        let decode = solve_segmented(
            &func,
            &vregs,
            &seg_of,
            &allocatable,
            &reserved,
            &[],
            Some(&rec),
        )
        .expect("isolating the reserved block strictly beats the whole spill");
        assert_eq!(
            decode[0],
            vec![Some(PReg::new(19)), Some(PReg::new(19)), None],
            "keep the reg through the hot blocks, spill only the reserved block"
        );
    }
}
