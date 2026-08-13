// trust-cg-regalloc - PER-USE SPLITTING KILL-OR-COMMIT stats harness
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! KILL-OR-COMMIT measurement for PER-USE live-range splitting
//! (docs/per-use-splitting-plan.md, "THE KILL-OR-COMMIT FIRST SLICE").
//!
//! STATS-ONLY, INERT BY DEFAULT: everything here is gated on the
//! `TCG_AY_KILLCOMMIT` env var, and even when enabled nothing in this module
//! ever changes an allocation — the probe builds a SEPARATE PB instance, solves
//! it, logs one line, and DISCARDS the result. The shipping objective, the
//! run-both-keep-better criterion, and every allocator path are untouched.
//!
//! ## The question this answers with data
//!
//! Greedy's reactive splitting picks split points from a statically enumerable
//! closure ({gap midpoints} U {p+1 post-use points}; reactivity only SELECTS
//! from that set). If we hand the AY-PBO model that same closure (plus
//! call-site boundaries and greedy's own realized points), embed greedy's
//! solution to get its cost G under a commensurable loop-depth-weighted
//! TRAFFIC objective, and add a hard constraint `objective <= G-1`:
//!
//! * SAT      => a strictly-better allocation EXISTS at per-use granularity
//!   (the full per-use build is worth doing);
//! * UNSAT    => greedy is already optimal over the per-use candidate closure
//!   (shelve the build, question answered);
//! * Unknown  => time-starved at the probe cap.
//!
//! ## Mechanics
//!
//! 1. The baseline (greedy / linear-scan) pass records its realized split
//!    points + final piece->location map into a thread-local ([`GreedyRecord`];
//!    greedy runs before AY inside [`crate::allocate`], same thread).
//! 2. On the AY pass, [`probe::stats_probe`] segments `delta U greedy-split-or-
//!    spilled` vregs at the per-use candidate boundaries, embeds greedy's
//!    solution into the unit space (self-checked), evaluates G, and solves
//!    under the hard G-1 bound.
//!
//! Positions everywhere are in the PHASE-5-ENTRY instruction numbering: the
//! greedy and AY passes run on clones of the same input through deterministic
//! phases 1-4, and greedy's split machinery interprets positions in a stream
//! walk that SKIPS its own inserted split copies (see
//! `split::rewrite_split_operands`), so greedy's recorded split points line up
//! with the AY-side intervals without any drift correction.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use crate::liveness::LiveInterval;
use crate::machine_types::{PReg, VReg};

/// Env gate for the whole harness. When unset (the default) every hook in the
/// allocator is a single cheap boolean check and nothing is recorded, solved,
/// or logged. A value starting with `/` additionally APPENDS each log line to
/// that file (so corpus sweeps through wrappers that eat stderr still collect).
#[must_use]
pub(crate) fn enabled() -> bool {
    std::env::var_os("TCG_AY_KILLCOMMIT").is_some()
}

/// Whether the BASELINE pass should record greedy's realized solution: the
/// killcommit stats probe wants it, and — feature-gated — the AY whole-vreg
/// solve consumes it as the greedy-as-incumbent warm start (the hard `<= G-1`
/// bound). With both env gates unset this is false and every hook stays a
/// single cheap boolean check (default-path byte-identical).
#[must_use]
pub(crate) fn recording_enabled() -> bool {
    if enabled() {
        return true;
    }
    #[cfg(feature = "ay-regalloc")]
    {
        crate::ay_regalloc::enabled()
    }
    #[cfg(not(feature = "ay-regalloc"))]
    {
        false
    }
}

/// One final allocation piece of a baseline (greedy/linear-scan) vreg.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GreedyPiece {
    /// Piece extent start (phase-5-entry numbering).
    pub start: u32,
    /// Piece extent end (exclusive).
    pub end: u32,
    /// Final location: `Some(preg)` or `None` = spilled.
    pub loc: Option<PReg>,
}

/// The baseline allocator's realized solution, keyed by ORIGINAL (root) vreg
/// id. Split pieces are folded back onto their root via the parentage chain.
#[derive(Debug, Clone, Default)]
pub(crate) struct GreedyRecord {
    /// root vreg id -> realized split points (sorted, deduped).
    pub split_points: BTreeMap<u32, Vec<u32>>,
    /// root vreg id -> final pieces sorted by extent start.
    pub pieces: BTreeMap<u32, Vec<GreedyPiece>>,
    /// Total spilled pieces (the old keep-metric currency, for the log).
    pub spill_pieces: usize,
}

impl GreedyRecord {
    /// Baseline vreg ids that were split or had any piece spilled — the set
    /// that MUST be segmented for greedy's solution to embed exactly.
    #[cfg_attr(not(feature = "ay-regalloc"), allow(dead_code))]
    pub(crate) fn split_or_spilled_roots(&self) -> BTreeSet<u32> {
        let mut roots: BTreeSet<u32> = self.split_points.keys().copied().collect();
        for (&id, pieces) in &self.pieces {
            if pieces.iter().any(|p| p.loc.is_none()) {
                roots.insert(id);
            }
        }
        roots
    }
}

thread_local! {
    /// The most recent baseline record on this thread. `allocate` runs the
    /// baseline pass, then the AY pass, sequentially on one thread, so a simple
    /// store/take pair per function is race-free.
    static RECORD: RefCell<Option<GreedyRecord>> = const { RefCell::new(None) };
}

/// Store the baseline record for the AY-pass probe to consume.
pub(crate) fn store_record(rec: GreedyRecord) {
    RECORD.with(|r| *r.borrow_mut() = Some(rec));
}

/// Take (consume) the stored baseline record.
#[cfg_attr(not(feature = "ay-regalloc"), allow(dead_code))]
pub(crate) fn take_record() -> Option<GreedyRecord> {
    RECORD.with(|r| r.borrow_mut().take())
}

/// Build a whole-vreg record (no splits) from a baseline allocation — the
/// linear-scan / no-splitting arms.
pub(crate) fn record_from_whole(
    intervals: &[LiveInterval],
    allocation: &BTreeMap<VReg, PReg>,
    spilled: &[VReg],
) -> GreedyRecord {
    let spilled_ids: BTreeSet<u32> = spilled.iter().map(|v| v.id).collect();
    let mut rec = GreedyRecord::default();
    for iv in intervals {
        if iv.ranges.is_empty() || iv.is_fixed {
            continue;
        }
        let loc = if spilled_ids.contains(&iv.vreg.id) {
            None
        } else {
            allocation.get(&iv.vreg).copied()
        };
        if loc.is_none() {
            rec.spill_pieces += 1;
        }
        rec.pieces.entry(iv.vreg.id).or_default().push(GreedyPiece {
            start: iv.start(),
            end: iv.end(),
            loc,
        });
    }
    rec
}

/// Append `line` to the file named by `TCG_AY_KILLCOMMIT` when its value is an
/// absolute path, in addition to stderr.
#[cfg_attr(not(feature = "ay-regalloc"), allow(dead_code))]
pub(crate) fn log_line(line: &str) {
    eprintln!("{line}");
    if let Some(v) = std::env::var_os("TCG_AY_KILLCOMMIT") {
        let s = v.to_string_lossy();
        if s.starts_with('/') {
            use std::io::Write;
            if let Ok(mut f) = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(s.as_ref())
            {
                let _ = writeln!(f, "{line}");
            }
        }
    }
}

#[cfg(feature = "ay-regalloc")]
pub(crate) mod probe {
    //! The stats solve: per-use unit segmentation, greedy embedding, the
    //! commensurable traffic objective, and the hard `<= G-1` bound.

    use std::collections::{BTreeMap, BTreeSet};
    use std::time::{Duration, Instant};

    use ay_pb::{PbCdclResult, PbCdclSolver, PbConstraint, PbInstance, PbObjective, PbRel, PbTerm};

    use super::{GreedyRecord, log_line};
    use crate::ay_regalloc::{
        add_move_constraints, block_spans, env_usize, lit, max_pairs, max_split_segments,
        max_vregs, model_at, neg_term, pos_term, reserved_forbids, solve_whole_vreg,
        unit_candidates,
    };
    use crate::greedy::GreedyAllocator;
    use crate::liveness::LiveInterval;
    use crate::machine_types::{PReg, RegAllocFunction, RegClass, VReg};
    use crate::split;

    /// Spill-op (reload/store) weight relative to a register move (plan: 3-4x).
    const SPILL_W: i128 = 4;
    /// Register-move weight.
    const MOVE_W: i128 = 1;

    /// Loop-depth factor: 10^depth (capped) — the same base the liveness
    /// spill_weight uses, so "hot" means the same thing on both sides.
    fn depth_factor(depth: u32) -> i128 {
        10i128.pow(depth.min(4))
    }

    /// Probe solve budget (ms). Defaults to the shipping 200ms anytime cap so
    /// the verdict is read against the budget the real allocator would have.
    fn probe_ms() -> u64 {
        env_usize("TCG_AY_KILLCOMMIT_MS", 200) as u64
    }

    /// Per-vreg candidate-boundary cap (greedy's own realized points are never
    /// dropped — they are required for the exact embedding).
    fn max_bounds_per_vreg() -> usize {
        env_usize("TCG_AY_KILLCOMMIT_MAX_BOUNDS", 12)
    }

    /// The probe verdict for one function.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub(crate) enum Verdict {
        /// A strictly-better allocation EXISTS: the solver found a model under
        /// the hard `<= G-1` bound. `cost` is recomputed from the DECODED
        /// assignment (ground truth, not the solver's claim); `verified` means
        /// the decoded assignment passed the legality self-check AND its
        /// recomputed cost really is `<= G-1`.
        Sat {
            claimed: i128,
            cost: i128,
            delta: i128,
            /// Decoded-model cost breakdown (spill, transition, move). The
            /// SPILL component is the cross-run-comparable currency: the move
            /// universe differs between segmented and whole-vreg-control runs.
            parts: (i128, i128, i128),
            verified: bool,
        },
        /// Greedy is optimal over the per-use candidate closure.
        Unsat,
        /// Time-starved at the probe cap (no conclusion).
        Unknown,
        /// Not measured (reason in the log line).
        Skip(String),
        /// Greedy's solution did not embed feasibly into the unit space — a
        /// model-mismatch FINDING, logged loudly.
        EmbedInfeasible(String),
    }

    /// Everything the probe measured for one function (logged as one line).
    #[derive(Debug, Clone)]
    pub(crate) struct ProbeReport {
        pub verdict: Verdict,
        pub n_vregs: usize,
        pub n_seg: usize,
        pub n_units: usize,
        pub n_pairs: usize,
        pub greedy_pieces: usize,
        pub greedy_spill_pieces: usize,
        pub g: i128,
        pub g_spill: i128,
        pub g_trans: i128,
        pub g_move: i128,
        pub wv_declined: bool,
        pub tier: usize,
        pub greedy_pts_dropped: usize,
        pub solve_ms: u128,
    }

    impl ProbeReport {
        fn skip(reason: &str) -> Self {
            ProbeReport {
                verdict: Verdict::Skip(reason.to_string()),
                n_vregs: 0,
                n_seg: 0,
                n_units: 0,
                n_pairs: 0,
                greedy_pieces: 0,
                greedy_spill_pieces: 0,
                g: 0,
                g_spill: 0,
                g_trans: 0,
                g_move: 0,
                wv_declined: false,
                tier: 0,
                greedy_pts_dropped: 0,
                solve_ms: 0,
            }
        }
    }

    /// One modeled allocation unit: a whole vreg, or one per-use-bounded piece
    /// of a segmented vreg.
    struct KUnit {
        /// Index into the modeled `vregs`.
        vi: usize,
        /// The unit's liveness (exact range intersection, not bracketed) plus
        /// the use/def positions falling inside `[lo, hi)`.
        iv: LiveInterval,
        /// Candidate pregs (class pool minus reserved-forbidden over the unit).
        candidates: Vec<PReg>,
    }

    /// The env-gated wrapper `allocate_core` calls on the AY pass. Takes the
    /// baseline record (the caller owns the thread-local take, shared with the
    /// warm-start incumbent), runs the probe, logs one line, DISCARDS the
    /// result.
    pub(crate) fn stats_probe(
        func: &RegAllocFunction,
        intervals: &[LiveInterval],
        allocatable: &BTreeMap<RegClass, Vec<PReg>>,
        reserved_regs: &BTreeMap<PReg, Vec<u32>>,
        copies: &[(VReg, VReg)],
        rec: Option<&GreedyRecord>,
    ) {
        let Some(rec) = rec else {
            log_line(&format!(
                "[killcommit] fn={} result=SKIP:no-baseline-record",
                func.name
            ));
            return;
        };
        let report = probe_instance(func, intervals, allocatable, reserved_regs, copies, rec);
        let verdict = match &report.verdict {
            Verdict::Sat {
                claimed,
                cost,
                delta,
                parts,
                verified,
            } => format!(
                "SAT claimed={claimed} cost={cost} (spill={} trans={} move={}) delta={delta} verified={}",
                parts.0,
                parts.1,
                parts.2,
                if *verified { "yes" } else { "NO" }
            ),
            Verdict::Unsat => "UNSAT".to_string(),
            Verdict::Unknown => "UNKNOWN".to_string(),
            Verdict::Skip(r) => format!("SKIP:{r}"),
            Verdict::EmbedInfeasible(r) => format!("EMBED-INFEASIBLE:{r}"),
        };
        log_line(&format!(
            "[killcommit] fn={} vregs={} seg={} units={} pairs={} gpieces={} gspillpieces={} \
             G={} (spill={} trans={} move={}) wv_declined={} tier={} gpts_dropped={} \
             result={} ms={}",
            func.name,
            report.n_vregs,
            report.n_seg,
            report.n_units,
            report.n_pairs,
            report.greedy_pieces,
            report.greedy_spill_pieces,
            report.g,
            report.g_spill,
            report.g_trans,
            report.g_move,
            report.wv_declined,
            report.tier,
            report.greedy_pts_dropped,
            verdict,
            report.solve_ms,
        ));
    }

    /// The whole measurement for one function. Pure with respect to the
    /// allocator: reads the phase-5-entry state + the baseline record, returns
    /// a report. Never mutates anything.
    pub(crate) fn probe_instance(
        func: &RegAllocFunction,
        intervals: &[LiveInterval],
        allocatable: &BTreeMap<RegClass, Vec<PReg>>,
        reserved_regs: &BTreeMap<PReg, Vec<u32>>,
        copies: &[(VReg, VReg)],
        rec: &GreedyRecord,
    ) -> ProbeReport {
        let greedy_pieces: usize = rec.pieces.values().map(Vec::len).sum();
        let base = |mut r: ProbeReport| {
            r.greedy_pieces = greedy_pieces;
            r.greedy_spill_pieces = rec.spill_pieces;
            r
        };

        if intervals.iter().any(|iv| iv.is_fixed) {
            return base(ProbeReport::skip("fixed-interval"));
        }
        // Model EXACTLY the vregs `solve_whole_vreg` models (same filter/order).
        let vregs: Vec<&LiveInterval> = intervals
            .iter()
            .filter(|iv| !iv.ranges.is_empty())
            .collect();
        let n = vregs.len();
        if n == 0 {
            return base(ProbeReport::skip("no-vregs"));
        }
        if n > max_vregs() {
            let mut r = ProbeReport::skip("oversize-vregs");
            r.n_vregs = n;
            return base(r);
        }

        // The AY whole-vreg spill delta (the discarded stats solve of record;
        // unbounded — the probe's own hard bound is built below).
        let wv = solve_whole_vreg(func, intervals, allocatable, reserved_regs, copies, None);
        let wv_declined = wv.is_none();
        let delta: BTreeSet<u32> = wv
            .map(|(_, spilled)| spilled.iter().map(|v| v.id).collect())
            .unwrap_or_default();

        // Segmentation set: delta U greedy-split-or-spilled (the widening the
        // exact embedding requires — eviction cascades split non-delta vregs).
        let modeled_ids: BTreeSet<u32> = vregs.iter().map(|iv| iv.vreg.id).collect();
        let mut seg_set: BTreeSet<u32> = delta;
        seg_set.extend(rec.split_or_spilled_roots());
        seg_set.retain(|id| modeled_ids.contains(id));

        if seg_set.is_empty() {
            let mut r = ProbeReport::skip("no-pressure");
            r.n_vregs = n;
            r.wv_declined = wv_declined;
            return base(r);
        }

        // Build units, widening tiers until the global segment cap fits:
        // tier 0 = greedy pts U call boundaries U top-3 gap midpoints U per-use
        // post-use points; tier 1 = greedy pts U call boundaries; tier 2 =
        // greedy pts only (embedding always preserved).
        let mut tier = 0usize;
        let built = loop {
            let Some(built) = build_units(&vregs, &seg_set, rec, allocatable, reserved_regs, tier)
            else {
                return base(ProbeReport::skip("no-class-pool"));
            };
            if built.units.len() <= max_split_segments() || tier == 2 {
                break built;
            }
            tier += 1;
        };
        let BuiltUnits {
            units,
            unit_range,
            transitions,
            greedy_pts_dropped,
        } = built;
        let m = units.len();
        if m > max_split_segments() {
            let mut r = ProbeReport::skip("oversize-units");
            r.n_vregs = n;
            r.n_seg = seg_set.len();
            r.n_units = m;
            r.tier = tier;
            return base(r);
        }

        // Interference pairs (truly-overlapping units of different vregs).
        let mut inter_pairs: Vec<(usize, usize)> = Vec::new();
        for u in 0..m {
            for w in (u + 1)..m {
                if units[u].vi == units[w].vi || !units[u].iv.overlaps(&units[w].iv) {
                    continue;
                }
                inter_pairs.push((u, w));
                if inter_pairs.len() > max_pairs() {
                    let mut r = ProbeReport::skip("oversize-pairs");
                    r.n_vregs = n;
                    r.n_seg = seg_set.len();
                    r.n_units = m;
                    r.n_pairs = inter_pairs.len();
                    r.tier = tier;
                    return base(r);
                }
            }
        }

        // Move-coalescing pairs between single-unit (whole) vregs, mirroring
        // solve_segmented (copies touching segmented vregs are excluded from
        // BOTH the objective and G — commensurable).
        let whole_unit_of: BTreeMap<VReg, usize> = (0..n)
            .filter(|&vi| unit_range[vi].1 - unit_range[vi].0 == 1)
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

        // Loop-depth lookup over the phase-5-entry numbering.
        let spans = block_spans(func);
        let depth_of = |pos: u32| -> u32 {
            for &(b, s, e) in &spans {
                if s <= pos && pos < e {
                    return func
                        .blocks
                        .get(b.0 as usize)
                        .map_or(0, |blk| blk.loop_depth);
                }
            }
            0
        };
        let unit_spill_cost = |iv: &LiveInterval| -> i128 {
            iv.use_positions
                .iter()
                .chain(iv.def_positions.iter())
                .map(|&p| SPILL_W * depth_factor(depth_of(p)))
                .sum()
        };

        // ---- Embed greedy's solution into the unit space. ----
        let mut embed: Vec<Option<PReg>> = Vec::with_capacity(m);
        for u in &units {
            let root = vregs[u.vi].vreg.id;
            let Some(pieces) = rec.pieces.get(&root) else {
                let mut r = ProbeReport::skip("");
                r.verdict =
                    Verdict::EmbedInfeasible(format!("vreg {root} missing from baseline record"));
                r.n_vregs = n;
                r.n_seg = seg_set.len();
                r.n_units = m;
                r.tier = tier;
                return base(r);
            };
            // The unit's start position lands inside exactly one greedy piece
            // (greedy's realized split points are all unit boundaries): the
            // last piece whose extent starts at or before it.
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

        // Embedding legality self-check: class/reserved per unit + pairwise
        // interference. An infeasible embedding is a model-mismatch FINDING.
        for (ui, u) in units.iter().enumerate() {
            let Some(r) = embed[ui] else { continue };
            let ok_class = allocatable
                .get(&u.iv.vreg.class)
                .is_some_and(|pool| pool.contains(&r));
            if !ok_class || reserved_forbids(&u.iv, r, reserved_regs) {
                let mut rep = ProbeReport::skip("");
                rep.verdict = Verdict::EmbedInfeasible(format!(
                    "unit {ui} (vreg {}) on {r:?}: class/reserved",
                    u.iv.vreg.id
                ));
                rep.n_vregs = n;
                rep.n_seg = seg_set.len();
                rep.n_units = m;
                rep.tier = tier;
                return base(rep);
            }
        }
        for &(u, w) in &inter_pairs {
            if let (Some(ru), Some(rw)) = (embed[u], embed[w])
                && crate::greedy::allocator_pregs_overlap(ru, rw)
            {
                let mut rep = ProbeReport::skip("");
                rep.verdict = Verdict::EmbedInfeasible(format!(
                    "units {u}/{w} (vregs {}/{}) collide on {ru:?}/{rw:?}",
                    units[u].iv.vreg.id, units[w].iv.vreg.id
                ));
                rep.n_vregs = n;
                rep.n_seg = seg_set.len();
                rep.n_units = m;
                rep.tier = tier;
                return base(rep);
            }
        }

        // ---- The commensurable traffic cost (shared evaluator). ----
        let eval = |locs: &[Option<PReg>]| -> (i128, i128, i128) {
            let mut c_spill = 0i128;
            let mut c_trans = 0i128;
            let mut c_move = 0i128;
            for (ui, u) in units.iter().enumerate() {
                if locs[ui].is_none() {
                    c_spill += unit_spill_cost(&u.iv);
                }
            }
            for &(a, b, pos) in &transitions {
                let df = depth_factor(depth_of(pos));
                match (locs[a], locs[b]) {
                    (Some(x), Some(y)) if x != y => c_trans += MOVE_W * df,
                    (Some(_), None) | (None, Some(_)) => c_trans += SPILL_W * df,
                    _ => {}
                }
            }
            for &(du, su) in &move_pairs {
                if locs[du] != locs[su] {
                    c_move += MOVE_W;
                }
            }
            (c_spill, c_trans, c_move)
        };
        let (g_spill, g_trans, g_move) = eval(&embed);
        let g = g_spill + g_trans + g_move;

        let mut report = ProbeReport {
            verdict: Verdict::Unknown,
            n_vregs: n,
            n_seg: seg_set.len(),
            n_units: m,
            n_pairs: inter_pairs.len(),
            greedy_pieces,
            greedy_spill_pieces: rec.spill_pieces,
            g,
            g_spill,
            g_trans,
            g_move,
            wv_declined,
            tier,
            greedy_pts_dropped,
            solve_ms: 0,
        };

        if g == 0 {
            // Nothing to beat: cost is non-negative, so `<= -1` is trivially
            // unsatisfiable. Greedy is optimal here by inspection.
            report.verdict = Verdict::Unsat;
            return report;
        }

        // ---- PB encoding: exactly-one, interference, transition costs. ----
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
        // Per transition: t_store (reg->spill), t_reload (spill->reg), t_move
        // (reg->different-reg). One-sided gadgets only (the two-sided move
        // gadget on same-vreg pairs trips the ay-pb dense-conflict debug
        // assertion — the add_boundary_constraints lesson).
        let mut trans_vars: Vec<(u32, u32, u32)> = Vec::with_capacity(transitions.len());
        for _ in 0..transitions.len() {
            trans_vars.push((next_var, next_var + 1, next_var + 2));
            next_var += 3;
        }
        let mut move_diff: Vec<u32> = Vec::with_capacity(move_pairs.len());
        for _ in 0..move_pairs.len() {
            move_diff.push(next_var);
            next_var += 1;
        }
        let num_vars = next_var - 1;

        let candidates: Vec<Vec<PReg>> = units.iter().map(|u| u.candidates.clone()).collect();
        let mut constraints: Vec<PbConstraint> = Vec::new();

        // exactly-one per unit.
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
        // interference.
        for &(u, w) in &inter_pairs {
            for (ci, &ri) in candidates[u].iter().enumerate() {
                for (cj, &rj) in candidates[w].iter().enumerate() {
                    if crate::greedy::allocator_pregs_overlap(ri, rj) {
                        constraints.push(PbConstraint {
                            terms: vec![neg_term(x_var[u][ci]), neg_term(x_var[w][cj])],
                            rel: PbRel::Ge,
                            rhs: 1,
                        });
                    }
                }
            }
        }
        // transition gadgets.
        let x_of = |candidates: &[Vec<PReg>], x_var: &[Vec<u32>], u: usize, r: PReg| {
            candidates[u]
                .iter()
                .position(|&c| c == r)
                .map(|ci| x_var[u][ci])
        };
        for (ti, &(a, b, _pos)) in transitions.iter().enumerate() {
            let (t_store, t_reload, t_move) = trans_vars[ti];
            // t_store >= s_b - s_a   (a allocated, b spilled: the boundary store)
            constraints.push(PbConstraint {
                terms: vec![pos_term(t_store), neg_term(s_var[b]), pos_term(s_var[a])],
                rel: PbRel::Ge,
                rhs: 1,
            });
            // t_reload >= s_a - s_b  (a spilled, b allocated: the boundary reload)
            constraints.push(PbConstraint {
                terms: vec![pos_term(t_reload), neg_term(s_var[a]), pos_term(s_var[b])],
                rel: PbRel::Ge,
                rhs: 1,
            });
            // t_move >= x_{a,r} - x_{b,r} - s_b  for each candidate r of a
            // (both allocated, different regs: the boundary move).
            for (ci, &r) in candidates[a].iter().enumerate() {
                let mut terms = vec![pos_term(t_move), neg_term(x_var[a][ci]), pos_term(s_var[b])];
                if let Some(bv) = x_of(&candidates, &x_var, b, r) {
                    terms.push(pos_term(bv));
                }
                constraints.push(PbConstraint {
                    terms,
                    rel: PbRel::Ge,
                    rhs: 1,
                });
            }
        }
        // move gadgets (identical shape to the shipping encoding).
        for (mp, &(du, su)) in move_pairs.iter().enumerate() {
            add_move_constraints(&mut constraints, move_diff[mp], du, su, &candidates, &x_var);
        }

        // The commensurable traffic objective (the STATS objective — the
        // shipping lexicographic objective is untouched).
        let mut obj_terms: Vec<PbTerm> = Vec::new();
        for u in 0..m {
            let c = unit_spill_cost(&units[u].iv);
            if c > 0 {
                obj_terms.push(PbTerm {
                    coeff: c,
                    lits: vec![lit(s_var[u])],
                });
            }
        }
        for (ti, &(_a, _b, pos)) in transitions.iter().enumerate() {
            let df = depth_factor(depth_of(pos));
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

        // HARD bound: objective <= G-1, encoded as the negated-Ge row (the
        // ay-pb strictly_better_than_incumbent_constraint gadget, emitted
        // directly): sum(-c_i * x_i) >= -(G-1).
        let bound = PbConstraint {
            terms: obj_terms
                .iter()
                .map(|t| PbTerm {
                    coeff: -t.coeff,
                    lits: t.lits.clone(),
                })
                .collect(),
            rel: PbRel::Ge,
            rhs: -(g - 1),
        };
        constraints.push(bound);

        let instance = PbInstance {
            num_vars,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };

        let t0 = Instant::now();
        let deadline = t0 + Duration::from_millis(probe_ms());
        let mut solver = PbCdclSolver::new_interruptible(&instance, || Instant::now() >= deadline);
        let result =
            solver.solve_optimize_interruptible(&objective, None, || Instant::now() >= deadline);
        report.solve_ms = t0.elapsed().as_millis();

        let (model, claimed) = match result {
            PbCdclResult::Optimal(model, cost) | PbCdclResult::Feasible(model, cost) => {
                (model, cost)
            }
            PbCdclResult::Satisfiable(model) => (model, i128::MIN), // decision-only model
            PbCdclResult::Unsatisfiable => {
                report.verdict = Verdict::Unsat;
                return report;
            }
            _ => {
                report.verdict = Verdict::Unknown;
                return report;
            }
        };

        // Decode + VERIFY the (untrusted) SAT model before believing the
        // verdict: exactly-one per unit, legality, and the recomputed cost
        // really beating G. A failure here is an encoding gap, not a win.
        let mut decoded: Vec<Option<PReg>> = Vec::with_capacity(m);
        let mut consistent = true;
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
                (Some(r), false) => decoded.push(Some(r)),
                (None, true) => decoded.push(None),
                _ => {
                    decoded.push(None);
                    consistent = false;
                }
            }
        }
        let mut legal = consistent;
        if legal {
            'legality: for (ui, u) in units.iter().enumerate() {
                if let Some(r) = decoded[ui] {
                    let ok_class = allocatable
                        .get(&u.iv.vreg.class)
                        .is_some_and(|pool| pool.contains(&r));
                    if !ok_class || reserved_forbids(&u.iv, r, reserved_regs) {
                        legal = false;
                        break 'legality;
                    }
                }
            }
            if legal {
                for &(u, w) in &inter_pairs {
                    if let (Some(ru), Some(rw)) = (decoded[u], decoded[w])
                        && crate::greedy::allocator_pregs_overlap(ru, rw)
                    {
                        legal = false;
                        break;
                    }
                }
            }
        }
        let (c_spill, c_trans, c_move) = eval(&decoded);
        let cost = c_spill + c_trans + c_move;
        report.verdict = Verdict::Sat {
            claimed,
            cost,
            delta: g - cost,
            parts: (c_spill, c_trans, c_move),
            verified: legal && cost < g,
        };
        report
    }

    /// Units + bookkeeping produced by [`build_units`].
    struct BuiltUnits {
        units: Vec<KUnit>,
        /// Per modeled vreg: `[start, end)` unit index range.
        unit_range: Vec<(usize, usize)>,
        /// Adjacent same-vreg unit pairs `(a, b, boundary_pos)`.
        transitions: Vec<(usize, usize, u32)>,
        /// Greedy realized points that fell outside the vreg's live ranges
        /// (copy-extension artifacts) and were dropped from the boundary set.
        greedy_pts_dropped: usize,
    }

    /// Build the modeling units: per-use-bounded segments for `seg_set` vregs,
    /// whole units for the rest. Returns `None` if a class has no pool.
    fn build_units(
        vregs: &[&LiveInterval],
        seg_set: &BTreeSet<u32>,
        rec: &GreedyRecord,
        allocatable: &BTreeMap<RegClass, Vec<PReg>>,
        reserved_regs: &BTreeMap<PReg, Vec<u32>>,
        tier: usize,
    ) -> Option<BuiltUnits> {
        let mut units: Vec<KUnit> = Vec::new();
        let mut unit_range: Vec<(usize, usize)> = Vec::with_capacity(vregs.len());
        let mut transitions: Vec<(usize, usize, u32)> = Vec::new();
        let mut greedy_pts_dropped = 0usize;

        for (vi, iv) in vregs.iter().enumerate() {
            let start = units.len();
            let bounds = if seg_set.contains(&iv.vreg.id) {
                let (bounds, dropped) = candidate_boundaries(
                    iv,
                    reserved_regs,
                    rec.split_points
                        .get(&iv.vreg.id)
                        .map_or(&[][..], Vec::as_slice),
                    tier,
                );
                greedy_pts_dropped += dropped;
                bounds
            } else {
                Vec::new()
            };

            if bounds.is_empty() {
                let unit_iv = (*iv).clone();
                let candidates = unit_candidates(&unit_iv, allocatable, reserved_regs)?;
                units.push(KUnit {
                    vi,
                    iv: unit_iv,
                    candidates,
                });
            } else {
                let mut cuts: Vec<u32> = Vec::with_capacity(bounds.len() + 2);
                cuts.push(iv.start());
                cuts.extend(bounds.iter().copied());
                cuts.push(iv.end());
                let mut prev_unit: Option<usize> = None;
                for w in cuts.windows(2) {
                    let (lo, hi) = (w[0], w[1]);
                    let mut unit_iv = LiveInterval::new(iv.vreg);
                    for r in &iv.ranges {
                        let s = r.start.max(lo);
                        let e = r.end.min(hi);
                        if s < e {
                            unit_iv.add_range(s, e);
                        }
                    }
                    if unit_iv.ranges.is_empty() {
                        continue;
                    }
                    unit_iv.use_positions = iv
                        .use_positions
                        .iter()
                        .copied()
                        .filter(|&p| lo <= p && p < hi)
                        .collect();
                    unit_iv.def_positions = iv
                        .def_positions
                        .iter()
                        .copied()
                        .filter(|&p| lo <= p && p < hi)
                        .collect();
                    let candidates = unit_candidates(&unit_iv, allocatable, reserved_regs)?;
                    let ui = units.len();
                    units.push(KUnit {
                        vi,
                        iv: unit_iv,
                        candidates,
                    });
                    if let Some(pu) = prev_unit {
                        // The boundary separating the two units is the later
                        // unit's cut (`lo`) — where the split copy would sit.
                        transitions.push((pu, ui, lo));
                    }
                    prev_unit = Some(ui);
                }
                if prev_unit.is_none() {
                    // All windows were empty (cannot happen for boundaries
                    // strictly inside live ranges, but stay total): model whole.
                    let unit_iv = (*iv).clone();
                    let candidates = unit_candidates(&unit_iv, allocatable, reserved_regs)?;
                    units.push(KUnit {
                        vi,
                        iv: unit_iv,
                        candidates,
                    });
                }
            }
            unit_range.push((start, units.len()));
        }

        Some(BuiltUnits {
            units,
            unit_range,
            transitions,
            greedy_pts_dropped,
        })
    }

    /// Per-vreg candidate boundary set (docs/per-use-splitting-plan.md):
    /// greedy's recorded realized points (NEVER dropped — required for the
    /// exact embedding) U call-site boundaries `{p, p+1}` from reserved points
    /// live inside the range U top-3 gap midpoints
    /// (`gap_split_points_by_quality` verbatim) U per-use post-use points
    /// (`find_per_use_split_points` verbatim), deduped, capped per-vreg.
    /// Higher `tier` narrows the sources (1 = no gap/per-use, 2 = greedy only).
    /// Returns `(sorted boundaries, greedy points dropped as outside-live-range)`.
    fn candidate_boundaries(
        iv: &LiveInterval,
        reserved_regs: &BTreeMap<PReg, Vec<u32>>,
        greedy_pts: &[u32],
        tier: usize,
    ) -> (Vec<u32>, usize) {
        let strictly_inside = |p: u32| iv.ranges.iter().any(|r| r.start < p && p < r.end);
        let kmax = max_bounds_per_vreg();
        let mut chosen: Vec<u32> = Vec::new();
        let mut dropped = 0usize;
        for &p in greedy_pts {
            if strictly_inside(p) {
                if !chosen.contains(&p) {
                    chosen.push(p); // exempt from kmax: embedding requires them
                }
            } else {
                dropped += 1;
            }
        }
        let push = |chosen: &mut Vec<u32>, p: u32| {
            if strictly_inside(p) && !chosen.contains(&p) && chosen.len() < kmax {
                chosen.push(p);
            }
        };
        if tier <= 1 {
            let mut call_pts: BTreeSet<u32> = BTreeSet::new();
            for points in reserved_regs.values() {
                for &p in points {
                    if iv.is_live_at(p) {
                        call_pts.insert(p);
                        call_pts.insert(p + 1);
                    }
                }
            }
            for p in call_pts {
                push(&mut chosen, p);
            }
        }
        if tier == 0 {
            for p in GreedyAllocator::gap_split_points_by_quality(iv)
                .into_iter()
                .take(3)
            {
                push(&mut chosen, p);
            }
            for (p, _weight) in split::find_per_use_split_points(iv) {
                push(&mut chosen, p);
            }
        }
        chosen.sort_unstable();
        chosen.dedup();
        (chosen, dropped)
    }
}

// ===========================================================================
// Tests — the harness's own correctness (recording, embedding, G, the bound).
// The suite runs with the `ay-regalloc` feature; without it the harness is
// inert and covered by the default suite staying green.
// ===========================================================================
#[cfg(all(test, feature = "ay-regalloc"))]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::probe::{Verdict, probe_instance};
    use super::*;
    use crate::greedy::GreedyAllocator;
    use crate::liveness::compute_live_intervals;
    use crate::machine_types::{
        BlockId, InstFlags, InstId, MachInst, MachOperand, PReg, RegAllocBlock, RegAllocFunction,
        RegClass, VReg,
    };

    fn vreg(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr64,
        }
    }

    fn nop_inst() -> MachInst {
        MachInst {
            opcode: 1,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }
    }

    /// A function whose only role is to carry block spans + loop depths for the
    /// probe: blocks of the given (len, loop_depth) in order.
    fn span_func(blocks: &[(u32, u32)]) -> RegAllocFunction {
        let total: u32 = blocks.iter().map(|&(n, _)| n).sum();
        let insts = (0..total).map(|_| nop_inst()).collect();
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
            name: "killcommit_test".to_string(),
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

    /// THE SPILL-AROUND-CALL SHAPE, the plan's canonical strict win: a value
    /// defined before a hot loop, used inside it, live across a call, used
    /// after. The whole-vreg baseline must spill it (the only preg is reserved
    /// at the call point), paying loop-weighted reloads; per-use units can keep
    /// it in the preg everywhere except a ref-free unit spanning the call —
    /// store+load around the call only. The probe must find that model (SAT),
    /// verify it, and report the delta against the embedded baseline G.
    #[test]
    fn probe_finds_strict_win_on_spill_around_call() {
        // b0 [0,3) depth 0: def@0 | b1 [3,6) depth 1: uses@3,4 | b2 [6,11)
        // depth 0: call@8 (reserved), use@10.
        let func = span_func(&[(3, 0), (3, 1), (5, 0)]);
        let intervals = vec![interval(0, &[(0, 11)], &[3, 4, 10], &[0])];
        let mut allocatable: BTreeMap<RegClass, Vec<PReg>> = BTreeMap::new();
        allocatable.insert(RegClass::Gpr64, vec![PReg::new(19)]);
        let mut reserved: BTreeMap<PReg, Vec<u32>> = BTreeMap::new();
        reserved.insert(PReg::new(19), vec![8]);

        // Baseline: the whole vreg spilled (what linear-scan/greedy-without-a-
        // usable-split does when the pool is reserved-forbidden over the range).
        let rec = record_from_whole(&intervals, &BTreeMap::new(), &[vreg(0)]);
        assert_eq!(rec.spill_pieces, 1);
        assert_eq!(rec.split_or_spilled_roots(), BTreeSet::from([0]));

        let report = probe_instance(&func, &intervals, &allocatable, &reserved, &[], &rec);
        // G: spilled refs def@0 (df 1) + uses@3,4 (df 10) + use@10 (df 1)
        //    = 4*(1+10+10+1) = 88; no transitions/moves in a whole-spill embed.
        assert_eq!(report.g_spill, 88, "embedded baseline spill traffic");
        assert_eq!((report.g_trans, report.g_move), (0, 0));
        match report.verdict {
            Verdict::Sat {
                cost,
                delta,
                verified,
                ..
            } => {
                assert!(verified, "SAT model must decode legal and beat G");
                // The known-best model: store@8 + reload@9 = 4 + 4.
                assert_eq!(cost, 8, "per-use optimum spills only around the call");
                assert_eq!(delta, 80);
            }
            other => panic!("expected SAT (a strictly-better allocation exists): {other:?}"),
        }
        assert!(
            report.n_units >= 3,
            "the call must be isolated in its own unit"
        );
    }

    /// When the baseline is already optimal over the closure, the hard G-1
    /// bound must come back UNSAT — the shelve verdict. Same shape as above but
    /// no loop and no call: spilling costs the same wherever you cut, and a
    /// 2-vreg overlap on 1 reg forces exactly one spill.
    #[test]
    fn probe_reports_unsat_when_baseline_optimal() {
        // One block, depth 0. v0: def@0, use@9 (long, cheap). v1: def@2,
        // use@3..6 (short, hot-by-count). One reg: someone spills.
        let func = span_func(&[(10, 0)]);
        let intervals = vec![
            interval(0, &[(0, 10)], &[9], &[0]),
            interval(1, &[(2, 7)], &[3, 4, 5, 6], &[2]),
        ];
        let mut allocatable: BTreeMap<RegClass, Vec<PReg>> = BTreeMap::new();
        allocatable.insert(RegClass::Gpr64, vec![PReg::new(19)]);
        let reserved: BTreeMap<PReg, Vec<u32>> = BTreeMap::new();

        // Baseline: v1 keeps the reg (more refs), v0 spills — greedy's answer.
        let mut allocation: BTreeMap<VReg, PReg> = BTreeMap::new();
        allocation.insert(vreg(1), PReg::new(19));
        let rec = record_from_whole(&intervals, &allocation, &[vreg(0)]);

        let report = probe_instance(&func, &intervals, &allocatable, &reserved, &[], &rec);
        // G = 4*(def@0 + use@9) = 8. Any split of v0 still pays >= a store +
        // reload (8) to cross v1's region, and spilling v1 instead pays
        // 4*5 = 20 > 8; per-use fragments cannot beat 8.
        assert_eq!(report.g, 8);
        assert_eq!(
            report.verdict,
            Verdict::Unsat,
            "baseline already optimal over the per-use closure -> UNSAT"
        );
    }

    /// End-to-end with the REAL greedy allocator doing the recording: the
    /// seg_pressure shape (a live-through vreg under 2-reg pressure) makes
    /// greedy split or spill; the record must fold pieces onto root ids, and
    /// greedy's embedded solution must be FEASIBLE in the probe's unit space
    /// (the load-bearing exact-embedding claim), yielding a real verdict.
    #[test]
    fn greedy_record_embeds_feasibly() {
        use crate::machine_types::MachFunction;
        let a = vreg(0);
        let b = vreg(1);
        let c = vreg(2);
        let mov = |d: VReg| MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(d)],
            uses: vec![MachOperand::Imm(7)],
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
        let br = |t: u32| MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(t))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        };
        // 0:A=imm 1:br1 | 2:B=imm 3:C=imm 4:use(B,C) 5:use(B,C) 6:br2 | 7:use(A)
        let insts = vec![
            mov(a),
            br(1),
            mov(b),
            mov(c),
            useop(&[b, c]),
            useop(&[b, c]),
            br(2),
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
                insts: vec![InstId(2), InstId(3), InstId(4), InstId(5), InstId(6)],
                preds: vec![BlockId(0)],
                succs: vec![BlockId(2)],
                loop_depth: 0,
            },
            RegAllocBlock {
                insts: vec![InstId(7)],
                preds: vec![BlockId(1)],
                succs: vec![],
                loop_depth: 0,
            },
        ];
        let mut func = MachFunction {
            name: "kc_seg_pressure".to_string(),
            insts,
            blocks,
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let pristine = func.clone();

        let mut allocatable: BTreeMap<RegClass, Vec<PReg>> = BTreeMap::new();
        allocatable.insert(RegClass::Gpr64, vec![PReg::new(19), PReg::new(20)]);

        let live = compute_live_intervals(&func);
        let intervals: Vec<LiveInterval> = live.intervals.values().cloned().collect();
        let mut greedy = GreedyAllocator::new_with_reserved(
            intervals.clone(),
            &allocatable,
            BTreeMap::new(),
            BTreeMap::new(),
        );
        greedy.killcommit_enable_recording();
        greedy
            .allocate_with_splitting(&mut func)
            .expect("greedy allocates");
        let rec = greedy.killcommit_record();

        // Every piece folds onto an ORIGINAL vreg id (roots < pristine
        // next_vreg), even though splits allocate fresh ids.
        assert!(!rec.pieces.is_empty());
        for &root in rec.pieces.keys() {
            assert!(root < 3, "piece keyed by non-root vreg id {root}");
        }
        for (&root, pts) in &rec.split_points {
            assert!(root < 3, "split points keyed by non-root id {root}");
            assert!(pts.windows(2).all(|w| w[0] < w[1]), "points sorted+deduped");
        }
        // Greedy did something recordable under 2-reg pressure.
        assert!(
            !rec.split_points.is_empty() || rec.spill_pieces > 0,
            "pressure must force a split or a spill: {rec:?}"
        );

        // The probe must accept the embedding (no EmbedInfeasible/Skip) and
        // reach a real verdict on the PRISTINE (phase-5-entry) stream.
        let report = probe_instance(
            &pristine,
            &intervals,
            &allocatable,
            &BTreeMap::new(),
            &[],
            &rec,
        );
        match report.verdict {
            Verdict::Sat { verified, .. } => assert!(verified, "SAT must verify"),
            Verdict::Unsat | Verdict::Unknown => {}
            other => panic!("embedding/probe must not be rejected: {other:?}"),
        }
    }

    /// Inert by default: with the env unset, a full `allocate()` (the public
    /// entry, greedy strategy with splitting) records NOTHING.
    #[test]
    fn no_record_without_env() {
        if enabled() {
            return; // an explicit TCG_AY_KILLCOMMIT run — nothing to assert
        }
        let _ = take_record();
        let func = span_func(&[(4, 0)]);
        let mut f = func.clone();
        let mut allocatable: BTreeMap<RegClass, Vec<PReg>> = BTreeMap::new();
        allocatable.insert(RegClass::Gpr64, vec![PReg::new(19), PReg::new(20)]);
        let config = crate::AllocConfig {
            allocatable_regs: allocatable,
            strategy: crate::AllocStrategy::Greedy,
            enable_coalescing: true,
            enable_remat: true,
            enable_critical_edge_splitting: true,
            enable_splitting: true,
            enable_spill_code: true,
            enable_spill_slot_reuse: true,
            hints: BTreeMap::new(),
            coalesce_tuning: Default::default(),
        };
        let _ = crate::allocate(&mut f, &config);
        assert!(
            take_record().is_none(),
            "killcommit must record nothing when the env gate is unset"
        );
    }
}
