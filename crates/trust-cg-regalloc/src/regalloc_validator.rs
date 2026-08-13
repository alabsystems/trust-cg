// trust-cg-regalloc/regalloc_validator.rs - Register-allocation translation validator
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Register-allocation translation validation (Rideau-Leroy style).
//!
//! P3b deliverable: a *checker* that proves a single allocation result is
//! semantically equivalent to its SSA input **without re-running allocation**.
//! It closes the splitter / regalloc miscompile class (#52 / #53 / #63 / #64)
//! by validating the concrete output instead of trusting the allocator.
//!
//! ## What it consumes
//!
//! Three artifacts produced by [`crate::allocate`]:
//!
//! 1. The **PRE-alloc** [`RegAllocFunction`] (SSA form, still carrying `IS_PHI`
//!    instructions). This is the spec.
//! 2. The **POST-alloc** [`RegAllocFunction`] — the same function after
//!    `split_critical_edges` -> `eliminate_phis` -> liveness -> coalesce ->
//!    `LinearScan`/`Greedy` -> spill code. Phis are gone; parallel-copy,
//!    spill-store (`PSEUDO_SPILL_STORE`), and spill-load (`PSEUDO_SPILL_LOAD`)
//!    pseudos have been inserted. VReg operands are NOT rewritten to PRegs in
//!    this crate — the `VReg -> PReg` map is carried separately in the result.
//! 3. The [`AllocationResult`]: `allocation: BTreeMap<VReg, PReg>` plus
//!    `spills: Vec<SpillInfo>` (the spilled vregs and their stack slots).
//!
//! ## What it proves
//!
//! Three independent properties (Rideau & Leroy, "Tilting at Windmills with
//! Coq: Formal Verification of a Compilation Algorithm for Parallel Moves",
//! and Leroy's CompCert translation-validation framing):
//!
//! * **(a) Value-flow equivalence.** Assign each [`Location`] (a physical
//!   register or a stack slot) a *symbolic value* — the id of the original SSA
//!   VReg whose definition currently occupies it. Walk the post-alloc code in
//!   program order; copies / spill-stores / spill-loads *propagate* a symbolic
//!   value between locations, every other def *overwrites* its destination
//!   location with a fresh symbolic value naming that def. At each ORIGINAL
//!   (non-inserted) use of an SSA vreg `v`, the location assigned to `v` must
//!   currently hold the symbolic value `v`. The #64 join clobber — a value
//!   overwritten on the join path before its use — fails here.
//!
//! * **(b) Interference soundness.** Recompute simultaneous liveness from the
//!   PRE-alloc SSA. No two vregs that are live at the same program point may be
//!   assigned the same physical register, and no two simultaneously-live
//!   spilled vregs may share a stack slot. (#52 / #53: a clobbered argument
//!   register / overlapping assignment.)
//!
//! * **(c) Phi / parallel-copy correctness.** For every original phi
//!   `dest = [.. src_i from pred_i ..]`, the copies the allocator inserted on
//!   edge `pred_i -> phi_block` must make `dest`'s location hold `src_i`'s value
//!   at the end of that edge — including the critical-edge / call-free-join
//!   cases #64 exposed (where the greedy splitter placed the realizing copy on
//!   the wrong side of the join). The transfer obligation is checked **per
//!   incoming edge**: for every `(dest, pred, src)` triple, `pred`'s EXIT state
//!   must hold exactly `src.id` in `dest`'s assigned location on THAT edge.
//!   Phi-realizing copies are modeled as ordinary value propagation (a copy
//!   `dest <- src` propagates `src`'s symbolic value), so a copy that reads the
//!   WRONG predecessor's source — e.g. `dest <- src_B2` placed on the `B1` edge
//!   — leaves `dest`'s location holding `src_B2.id` on `B1`'s exit and is
//!   rejected. There is deliberately NO per-dest "acceptable union" set: a
//!   source that is correct on one edge does not excuse it on another.
//!
//! The validator is *sound but conservative*: it walks an over-approximating
//! linear-then-CFG schedule. On any structure it cannot prove equivalent it
//! returns `Err`, never a false `Ok`. Treat it as a fail-closed gate.
//!
//! ## Trust boundary: spill-reload temporary registers
//!
//! A spilled vreg's authoritative home is its stack slot (see
//! [`build_location_map`]). When the allocator reloads a spilled value, it emits
//! a `PSEUDO_SPILL_LOAD` whose destination is a scratch *physical* register that
//! the [`AllocationResult`] does NOT name (it is not in `allocation`, only the
//! slot is). The symbolic walk therefore cannot see which PReg a reload landed
//! in, so it cannot validate the subsequent use against that reload register —
//! the historical blind spot: a reload whose scratch value crossed another
//! instruction (which could clobber it) still validated against the slot.
//!
//! Property **(d)** ([`check_spill_discipline`]) now closes the exploitable
//! part structurally, WITHOUT naming the scratch: a disciplined slot-homed
//! use must be immediately preceded by its reload, and a spill store must
//! immediately follow its def, so the unnamed scratch's live range never
//! crosses any other instruction. What remains outside the trust boundary is
//! only the per-site scratch CHOICE (reserved, never-allocatable registers,
//! e.g. x16/x17), which the spill materializer owns and its tests cover.

use crate::linear_scan::AllocationResult;
use crate::liveness::compute_live_intervals;
use crate::machine_types::{
    BlockId, InstId, MachFunction, PReg, RegAllocInst, RegAllocOperand, StackSlotId, VReg,
};
use crate::phi_elim::{IR_COPY_OPCODE, PSEUDO_COPY};
use crate::spill::{PSEUDO_SPILL_LOAD, PSEUDO_SPILL_STORE};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::rc::Rc;

// ---------------------------------------------------------------------------
// Location: where a value physically lives after allocation.
// ---------------------------------------------------------------------------

/// A physical storage location: a register or a stack slot.
///
/// Two distinct vregs sharing the same `Location` while simultaneously live is
/// the interference bug class (#52/#53). The validator tracks one symbolic
/// value per `Location`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Location {
    /// Assigned physical register (from `AllocationResult::allocation`).
    Reg(PReg),
    /// Spill stack slot (from `AllocationResult::spills`).
    Slot(StackSlotId),
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Location::Reg(p) => write!(f, "{p}"),
            Location::Slot(s) => write!(f, "slot{}", s.0),
        }
    }
}

/// A symbolic value: the id of the original SSA VReg whose definition produced
/// the value currently in a location. `None` means "unknown / never written
/// on this path".
///
/// This is the REPORTING currency (used in [`ValidationError`] diagnostics) and
/// the projection of the richer [`Sym`] dataflow lattice element down to a single
/// id: `Defined(v) -> Some(v)`, `Conflict(_) -> None`. The accept/reject decision
/// for the value-flow property is made on the FULL [`Sym`] (so two CONFLICTs with
/// different source SETS compare UNEQUAL — see residual (a)), not on this
/// projection.
type SymVal = Option<u32>;

/// A symbolic value-flow lattice element carried per [`Location`] (POST walk) or
/// per [`VReg`] (PRE/spec walk).
///
/// Ordered by information content (descending = losing information):
///
/// ```text
///   Top   (ABSENT from the state map)  = "no path has written this yet"
///    │
///   Defined(v)                         = "every reaching path delivers SSA value v"
///    │
///   Conflict({a, b, ..})               = "reaching paths disagree; the SET of all
///                                          distinct source ids reaching here"  (bottom)
/// ```
///
/// ## Why a SET, not a bare `None` (residual (a))
///
/// The earlier model collapsed every disagreement to a single bottom (`None`), so
/// two merge points that disagreed over DIFFERENT source sets compared EQUAL. A
/// wrong latch / merge copy that kept POST at "conflict" but threaded a DIFFERENT
/// second source than the spec was therefore NOT pinned by the value-flow property
/// directly — it relied on the interference backstop. Carrying the full set of
/// reaching source ids makes `Conflict({a, b})` and `Conflict({a, c})` UNEQUAL, so
/// the value-flow check rejects a POST whose conflict disagrees with the spec's
/// conflict on its own. The set only ever GROWS as paths merge (`Conflict(S) ⊑
/// Conflict(T)` iff `S ⊆ T`), over the finite universe of SSA ids, so the dataflow
/// fixpoint still terminates.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Sym {
    /// Exactly one SSA value reaches here on every path.
    Defined(u32),
    /// Reaching paths disagree; carries the SET of all distinct reaching ids.
    Conflict(BTreeSet<u32>),
}

impl Sym {
    /// Project to the single-id reporting currency: a definite id, or `None` for a
    /// conflict (matching the historical `SymVal` semantics used in diagnostics).
    fn to_sym_val(&self) -> SymVal {
        match self {
            Sym::Defined(v) => Some(*v),
            Sym::Conflict(_) => None,
        }
    }

    /// Information-meet (greatest lower bound) of two PRESENT reaching values.
    /// `Top` is the absent map entry and handled by the callers (meet with Top is
    /// the identity), so this only combines two present values.
    ///
    /// * `meet(Defined(a), Defined(a)) = Defined(a)` — agreement preserved.
    /// * `meet(Defined(a), Defined(b)) = Conflict({a, b})` for `a != b`.
    /// * `meet(Defined(a), Conflict(S)) = Conflict(S ∪ {a})`.
    /// * `meet(Conflict(S), Conflict(T)) = Conflict(S ∪ T)`.
    fn meet(&self, other: &Sym) -> Sym {
        match (self, other) {
            (Sym::Defined(a), Sym::Defined(b)) => {
                if a == b {
                    Sym::Defined(*a)
                } else {
                    Sym::Conflict([*a, *b].into_iter().collect())
                }
            }
            (Sym::Defined(a), Sym::Conflict(s)) | (Sym::Conflict(s), Sym::Defined(a)) => {
                let mut set = s.clone();
                set.insert(*a);
                Sym::Conflict(set)
            }
            (Sym::Conflict(s), Sym::Conflict(t)) => Sym::Conflict(s.union(t).copied().collect()),
        }
    }
}

// ---------------------------------------------------------------------------
// Result types.
// ---------------------------------------------------------------------------

/// A single validation failure.
#[derive(Debug, Clone, PartialEq)]
pub enum ValidationError {
    /// (a) An original use read a location that did not hold the right value.
    ///
    /// `block`/`inst` locate the use; `vreg` is the SSA value expected; `loc`
    /// is where it was assigned; `found` is the symbolic value actually present.
    ValueFlowMismatch {
        block: BlockId,
        inst: InstId,
        vreg: VReg,
        loc: Location,
        found: SymVal,
    },
    /// (a) An original use referenced a vreg with no assigned location at all.
    UnmappedVReg {
        block: BlockId,
        inst: InstId,
        vreg: VReg,
    },
    /// (b) Two simultaneously-live vregs share a physical location.
    InterferenceViolation {
        a: VReg,
        b: VReg,
        loc: Location,
        point: u32,
    },
    /// (b') A vreg is assigned a physical register that carries a distinct value
    /// (an incoming argument, an explicit fixed-register operand, or a call
    /// clobber) at a point inside the vreg's live range — i.e. the vreg clobbers,
    /// or is clobbered by, that reserved register. `point` is the reserved
    /// position that falls within `vreg`'s range.
    PhysRegInterference {
        vreg: VReg,
        preg: PReg,
        reserved: PReg,
        point: u32,
    },
    /// (c) The copies on a phi edge do not realize the phi's value transfer.
    PhiTransferBroken {
        phi_dest: VReg,
        phi_src: VReg,
        pred: BlockId,
        phi_block: BlockId,
        found: SymVal,
    },
    /// A phi survived into the post-alloc code (phi elimination dropped it).
    PhiNotEliminated { block: BlockId, inst: InstId },
    /// (d) Spill-materialization discipline broken: a slot-homed value's data
    /// path crosses an unnamed scratch register that an intervening instruction
    /// could clobber (reload not immediately before its consumer, or store not
    /// immediately after its def). See the trust-boundary note in the module
    /// header — this check closes that reload-register blind spot.
    SpillDisciplineViolation {
        block: BlockId,
        inst: InstId,
        vreg: VReg,
        reason: &'static str,
    },
    /// (e) A spill-slot RELOAD reads a slot that is not DEFINITELY INITIALIZED:
    /// some path from the function entry reaches this reload without first
    /// passing a store to the slot, so the reload observes garbage (or a value
    /// from an unrelated prior frame). The aarch64 per-use-site spill
    /// materialization assumes a spilled vreg's store DOMINATES every reload —
    /// true for a whole-vreg spill (one store right after the single SSA def),
    /// FALSE for a live-range SPLIT connector piece whose store sits on only one
    /// CFG path. This is the split-connector miscompile class (gcc-c-torture
    /// 990628-1.c: `load_data`'s slot stored only on the non-loop path, reloaded
    /// uninitialized on the loop-exit path; ReedSolomon `rsdec_204`: a slot
    /// reloads a NULL heap base on a path the store does not dominate). Fail
    /// CLOSED.
    ///
    /// `block`/`inst` locate the reload; `slot` is the uninitialized slot;
    /// `uninit_pred` is a predecessor block whose exit leaves the slot
    /// uninitialized (the offending path arrives through it), or `None` if the
    /// slot is uninitialized at the function entry reaching `block` with no
    /// in-block store — the "offending path shape."
    SpillSlotUninitializedReload {
        block: BlockId,
        inst: InstId,
        slot: StackSlotId,
        uninit_pred: Option<BlockId>,
    },
    /// Structural mismatch the validator cannot reason about (fail closed).
    Unsupported(String),
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValidationError::ValueFlowMismatch {
                block,
                inst,
                vreg,
                loc,
                found,
            } => write!(
                f,
                "value-flow: use of {vreg} at {block:?}/{inst:?} reads {loc}, \
                 which holds {found:?}, not v{}",
                vreg.id
            ),
            ValidationError::UnmappedVReg { block, inst, vreg } => write!(
                f,
                "value-flow: use of {vreg} at {block:?}/{inst:?} has no assigned location"
            ),
            ValidationError::InterferenceViolation { a, b, loc, point } => write!(
                f,
                "interference: {a} and {b} are both live at point {point} but share {loc}"
            ),
            ValidationError::PhysRegInterference {
                vreg,
                preg,
                reserved,
                point,
            } => write!(
                f,
                "phys-reg interference: {vreg} is assigned {preg} but reserved register \
                 {reserved} (aliasing {preg}) carries a live value at point {point} inside \
                 {vreg}'s range"
            ),
            ValidationError::PhiTransferBroken {
                phi_dest,
                phi_src,
                pred,
                phi_block,
                found,
            } => write!(
                f,
                "phi: edge {pred:?}->{phi_block:?} must move {phi_src} into {phi_dest}'s \
                 location, but it holds {found:?}"
            ),
            ValidationError::PhiNotEliminated { block, inst } => {
                write!(f, "phi at {block:?}/{inst:?} was not eliminated")
            }
            ValidationError::SpillDisciplineViolation {
                block,
                inst,
                vreg,
                reason,
            } => write!(
                f,
                "spill-discipline: {vreg} at {block:?}/{inst:?}: {reason}"
            ),
            ValidationError::SpillSlotUninitializedReload {
                block,
                inst,
                slot,
                uninit_pred,
            } => match uninit_pred {
                Some(pred) => write!(
                    f,
                    "spill-slot init: reload of slot{} at {block:?}/{inst:?} is not \
                     definitely initialized — control reaches it via predecessor \
                     {pred:?} on a path with no dominating store to slot{} \
                     (split-connector placement)",
                    slot.0, slot.0
                ),
                None => write!(
                    f,
                    "spill-slot init: reload of slot{} at {block:?}/{inst:?} is not \
                     definitely initialized — a path from function entry reaches it \
                     with no dominating store to slot{} (split-connector placement)",
                    slot.0, slot.0
                ),
            },
            ValidationError::Unsupported(m) => write!(f, "unsupported: {m}"),
        }
    }
}

/// Aggregate validation outcome. Empty `errors` means the allocation validated.
#[derive(Debug, Clone, Default)]
pub struct ValidationReport {
    pub errors: Vec<ValidationError>,
}

impl ValidationReport {
    pub fn is_valid(&self) -> bool {
        self.errors.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Public entry point.
// ---------------------------------------------------------------------------

/// Validate one allocation result against its SSA input.
///
/// `pre` is the SSA+phi function as it entered [`crate::allocate`]; `post` is
/// the same function after the full pipeline mutated it in place; `result`
/// carries the `VReg -> PReg` map and spill slots. Returns a [`ValidationReport`]
/// — empty `errors` proves equivalence (modulo the documented conservatism).
///
/// IMPORTANT: pass a *clone* of the pre-alloc function captured BEFORE calling
/// `allocate`, since `allocate` mutates its argument into `post`. If copy
/// coalescing rewrote VRegs, use [`validate_allocation_coalesced`] with the
/// ORIGINAL (unrewritten) snapshot and the rewrite map instead — replaying the
/// rewrite onto the spec yourself would make a WRONG merge mutate both sides
/// and pass trivially (the self-certification flaw this API split closes).
pub fn validate_allocation(
    pre: &MachFunction,
    post: &MachFunction,
    result: &AllocationResult,
) -> ValidationReport {
    validate_allocation_coalesced(pre, post, result, &BTreeMap::new())
}

/// Validate an allocation whose pipeline included copy coalescing, against the
/// ORIGINAL (pre-coalesce, unrewritten) spec.
///
/// `coalesce_rewrites` is the VReg rewrite map [`crate::coalesce::coalesce_copies`]
/// produced and [`crate::coalesce::apply_coalescing`] applied to `post`. It is
/// used ONLY as namespace bookkeeping — to look up the physical location the
/// implementation gave a merged-away vreg (its representative's location). The
/// MERGE DECISIONS themselves are NOT trusted: the value-flow walk names every
/// value by its ORIGINAL spec id (taken from `pre.insts[i]`, positionally paired
/// with the rewritten operands of the surviving original instruction `post.insts[i]`),
/// so a WRONG merge of two interfering vregs leaves the shared register holding
/// the other vreg's spec id at some original use and is REJECTED — even though
/// both post operands carry the same representative name.
///
/// (The historical implementation replayed `coalesce_rewrites` onto the spec
/// before validating, which rewrote both sides and certified any merge — the
/// self-certification flaw. See `adversarial_wrong_coalesce_*` tests.)
pub fn validate_allocation_coalesced(
    pre: &MachFunction,
    post: &MachFunction,
    result: &AllocationResult,
    coalesce_rewrites: &BTreeMap<VReg, VReg>,
) -> ValidationReport {
    let mut report = ValidationReport::default();

    // Build the VReg -> Location map: allocated vregs -> Reg, spilled -> Slot.
    // Then COMPOSE with the coalesce rewrite: a merged-away original vreg's
    // location is its representative's. This lets the spec-named walk and the
    // phi machinery look up locations for ORIGINAL vregs while post operands
    // (rewritten to representatives) resolve through the base entries.
    let mut locations = build_location_map(result);
    if !coalesce_rewrites.is_empty() {
        let mut composed: Vec<(VReg, Location)> = Vec::new();
        for &old in coalesce_rewrites.keys() {
            let rep = resolve_coalesce_rep(old, coalesce_rewrites);
            if let Some(&loc) = locations.get(&rep) {
                composed.push((old, loc));
            }
        }
        for (old, loc) in composed {
            locations.entry(old).or_insert(loc);
        }
    }

    // (c) phi correctness is checked against the symbolic walk; but first ensure
    // no phi survived (a basic phi-elimination sanity guard).
    check_phis_eliminated(post, &mut report);

    // (b) interference is independent of the symbolic walk.
    //
    // Liveness is recomputed over `post` — the ACTUAL allocated program (after
    // critical-edge splitting, phi elimination, coalescing and spill insertion) —
    // NOT over `pre`. The allocator's interference relation is defined on that
    // post-pipeline program; `pre` is the pre-split SSA-with-phis function whose
    // instruction numbering and live ranges differ (it lacks the realizing copies
    // that separate a phi source's range from the phi result's), so checking
    // interference against `pre`'s liveness would both miss real overlaps and
    // FALSE-POSITIVE on values the realizing copies actually keep apart. We still
    // do not trust the allocator's own liveness: we recompute it ourselves from
    // `post`. Only vregs that have a `Location` (allocated reps / spilled-to-slot)
    // participate; reload/remat temporaries are absent from `locations` and are
    // skipped (their scratch registers are outside the trust boundary).
    check_interference(post, &locations, result, &mut report);

    // (b') physical-register interference — an INDEPENDENT gate for the class the
    // vreg-vreg check (b) structurally cannot see: a vreg colored to a physical
    // register that already carries a distinct live value (an incoming argument, a
    // fixed-register operand, or a call clobber). Recomputed over `post` from the
    // same reserved-point model the allocator is REQUIRED to respect, so it can
    // never reject an allocation a correct allocator (greedy, or a correct AY)
    // would produce, yet it catches a solver allocation that clobbers a reserved
    // register — including the incoming-argument clobber the AY self-check and the
    // vreg-vreg interference check both missed (LRSPLIT-2).
    check_physreg_interference(post, &locations, &mut report);

    // (a) + (c): one symbolic value-flow walk over the post-alloc code, using
    // the original SSA phis as the spec for cross-edge transfers.
    check_value_flow(pre, post, &locations, &mut report);

    // (d) spill-materialization discipline: a slot-homed value's reload must sit
    // immediately before its consumer, and a slot-homed def's store immediately
    // after its def. Closes the documented reload-register blind spot: the
    // value-flow walk validates spilled uses against the SLOT home, but the
    // machine routes the value through an unnamed scratch register between the
    // reload and the use — any intervening instruction could clobber it.
    check_spill_discipline(post, &locations, &mut report);

    // (e) spill-slot INITIALIZATION dominance: every spill-slot reload must be
    // dominated by a store to that slot on EVERY path from entry (a
    // slot-definitely-initialized forward dataflow over the post-RA CFG). Gate
    // (d) checks store/reload ADJACENCY within a block but NOT
    // initialization-before-use ACROSS the CFG; this gate closes the
    // split-connector placement class the value-flow walk explicitly carves out
    // as the splitter's own responsibility (the TRUST-BOUNDARY note in
    // `check_value_flow`). Arch-generic (operates on the shared
    // PSEUDO_SPILL_LOAD/STORE pseudos), so it covers x86 and aarch64,
    // LinearScan and Greedy, identically.
    check_slot_init_dominance(post, &mut report);

    report
}

/// Follow a coalesce rewrite chain to its representative (mirrors
/// `coalesce::resolve_rewrite`, with the same cycle guard).
fn resolve_coalesce_rep(mut vreg: VReg, rewrites: &BTreeMap<VReg, VReg>) -> VReg {
    let mut steps = 0usize;
    while let Some(&next) = rewrites.get(&vreg) {
        if next == vreg || steps >= rewrites.len() {
            break;
        }
        vreg = next;
        steps += 1;
    }
    vreg
}

// ---------------------------------------------------------------------------
// Location map.
// ---------------------------------------------------------------------------

/// Map every vreg that has a home to its [`Location`].
fn build_location_map(result: &AllocationResult) -> BTreeMap<VReg, Location> {
    let mut map = BTreeMap::new();
    for (&vreg, &preg) in &result.allocation {
        map.insert(vreg, Location::Reg(preg));
    }
    for spill in &result.spills {
        // A spilled vreg lives in its slot. If the allocator ALSO put it in a
        // register (it should not), the spill slot is the authoritative home of
        // the long-lived value; the register copies are short-lived reload
        // temporaries handled by the symbolic walk.
        map.insert(spill.vreg, Location::Slot(spill.slot));
    }
    map
}

// ---------------------------------------------------------------------------
// (b) Interference soundness.
// ---------------------------------------------------------------------------

/// No two simultaneously-live vregs may share a physical location.
///
/// Liveness is recomputed (we do not trust the allocator's own) over the
/// post-pipeline program `post` — the program the allocation actually describes.
/// For each pair of intervals that overlap, if both have the same assigned
/// `Location`, that is an interference violation (#52/#53).
fn check_interference(
    post: &MachFunction,
    locations: &BTreeMap<VReg, Location>,
    result: &AllocationResult,
    report: &mut ValidationReport,
) {
    let liveness = compute_live_intervals(post);
    let intervals: Vec<_> = liveness.intervals.values().collect();

    // EXACT replacement of the historical all-pairs scan, restructured for
    // scale (TY's fused-BFS parent loop: ~7,300 blocks / ~30,000 intervals at
    // O0 made the O(intervals²) loop the dominant compile cost — ~75s).
    //
    // The historical all-pairs loop reported a pair (i < j, in `intervals`
    // order) iff
    //   (1) both vregs have an assigned `Location`,
    //   (2) loc_i and loc_j share physical storage (see ALIAS-AWARENESS below),
    //   (3) vreg_i != vreg_j, and
    //   (4) the two intervals overlap (some range of i overlaps some range of j,
    //       half-open [start, end) semantics — `LiveRange::overlaps`).
    //
    // Condition (2) means only SHARED-storage pairs can ever be reported, so we
    // bucket interval indices into overlap classes and find the overlapping
    // pairs inside each bucket with a sweep line over the member ranges (sorted
    // by start; a range starting at `s` overlaps exactly the earlier-sorted
    // ranges whose end is > `s`). On a VALID allocation no two
    // shared-storage ranges overlap, so the sweep's active set is empty at every
    // step and the whole check is O(R log R) in the number of ranges. On a
    // violating allocation the extra work is proportional to the violating
    // pairs — the report that gets returned anyway.
    //
    // Within a bucket the violating-pair detection is unchanged: overlap is
    // detected per range pair, deduplicated per interval pair, condition (3) is
    // applied at emission, `overlap_point` is the SAME function on the SAME two
    // intervals, and `BTreeSet<(usize, usize)>` yields ascending (i, j) order.
    //
    // ALIAS-AWARENESS (rank-4 soundness fix): condition (2) above used to be
    // EXACT-`Location` equality, which made the bucketing blind to sub-register
    // aliasing — two simultaneously-live vregs assigned aliasing-but-distinct
    // pregs (AArch64 X0/W0, or Q8/D8/S8/H8 all over V8; x86 RAX/EAX) bucketed
    // separately and were never paired, so the backstop missed the exact
    // sub-register-overlap miscompile class. We now bucket `Location::Reg`
    // intervals by their OVERLAP CLASS (any two pregs that share physical
    // storage land in the same bucket) via `crate::greedy::allocator_pregs_overlap`,
    // which dispatches per-arch (AArch64 root-tuple overlap, x86 RAX/EAX +
    // XMM). Genuinely-disjoint pregs (X0 vs X1, V0 vs V1, RAX vs RCX, and any
    // cross-group / cross-arch pair) do NOT overlap and stay in distinct
    // classes, so no FALSE interference is introduced. Stack `Location::Slot`s
    // never alias each other, so they keep their exact key.
    //
    // The overlap relation is not a strict partition in general, but for the
    // register classes the allocator emits it behaves as one (overlap is an
    // equivalence within a single root group), so a "first matching
    // representative" assignment is well-defined: each Reg interval joins the
    // first already-seen class whose representative it overlaps, else it starts
    // a new class. Representatives are kept in first-seen order; the resulting
    // bucket order does not affect the violating-pair SET (each pair is found
    // within its shared class) and `BTreeSet` still yields ascending (i, j).
    let mut by_location: BTreeMap<Location, Vec<usize>> = BTreeMap::new();
    // Overlap classes for register locations: representative preg + members.
    let mut reg_classes: Vec<(PReg, Vec<usize>)> = Vec::new();
    for (idx, interval) in intervals.iter().enumerate() {
        match locations.get(&interval.vreg) {
            Some(&Location::Reg(preg)) => {
                let class = reg_classes
                    .iter_mut()
                    .find(|(rep, _)| crate::greedy::allocator_pregs_overlap(*rep, preg));
                match class {
                    Some((_, members)) => members.push(idx),
                    None => reg_classes.push((preg, vec![idx])),
                }
            }
            Some(&loc @ Location::Slot(_)) => {
                by_location.entry(loc).or_default().push(idx);
            }
            None => {}
        }
    }

    let mut violating_pairs: BTreeSet<(usize, usize)> = BTreeSet::new();
    let member_buckets = by_location
        .values()
        .chain(reg_classes.iter().map(|(_, members)| members));
    for members in member_buckets {
        if members.len() < 2 {
            continue;
        }
        // (start, end, interval index) for every live range in the bucket.
        let mut events: Vec<(u32, u32, usize)> = Vec::new();
        for &idx in members {
            for range in &intervals[idx].ranges {
                events.push((range.start, range.end, idx));
            }
        }
        events.sort_unstable();

        // Min-heap on range end: retires every active range with end <= start
        // before pairing, so the remaining active ranges r' satisfy
        // r'.start <= start < r'.end — exactly `LiveRange::overlaps` for a
        // nonempty current range. (A degenerate empty range [s, s) pairs with
        // active ranges holding s strictly inside — also exactly the
        // historical predicate, which treats [s, s) as overlapping [a, b)
        // iff a < s < b.)
        let mut active: std::collections::BinaryHeap<std::cmp::Reverse<(u32, usize)>> =
            std::collections::BinaryHeap::new();
        for (start, end, idx) in events {
            while let Some(&std::cmp::Reverse((active_end, _))) = active.peek() {
                if active_end <= start {
                    active.pop();
                } else {
                    break;
                }
            }
            for &std::cmp::Reverse((_, other)) in active.iter() {
                if other != idx {
                    violating_pairs.insert((other.min(idx), other.max(idx)));
                }
            }
            active.push(std::cmp::Reverse((end, idx)));
        }
    }

    for (i, j) in violating_pairs {
        let (a, b) = (intervals[i], intervals[j]);
        if a.vreg == b.vreg {
            continue;
        }
        // Both vregs are present in `locations` (they were bucketed). After
        // alias-aware bucketing the two locations may be DISTINCT-but-aliasing
        // pregs (e.g. X0 vs W0); we report `a`'s location for the diagnostic.
        // The interference is real regardless of which alias we name.
        let loc = locations[&a.vreg];
        // Report the earliest overlapping point for diagnostics.
        let point = overlap_point(a, b).unwrap_or(0);
        report.errors.push(ValidationError::InterferenceViolation {
            a: a.vreg,
            b: b.vreg,
            loc,
            point,
        });
    }

    // Extra guard: a spilled vreg must not also be present in the register
    // allocation map under a different location (would mean two homes).
    for spill in &result.spills {
        if let Some(&preg) = result.allocation.get(&spill.vreg) {
            report.errors.push(ValidationError::Unsupported(format!(
                "{} is both spilled to slot{} and allocated to {} — ambiguous home",
                spill.vreg, spill.slot.0, preg
            )));
        }
    }
}

/// (b') No allocated vreg may be colored to a physical register that carries a
/// DISTINCT live value at a point inside the vreg's range.
///
/// The vreg-vreg check [`check_interference`] only sees conflicts between two
/// modeled vregs; it is structurally blind to a vreg clobbering (or being
/// clobbered by) a value that lives in a physical register WITHOUT a vreg — an
/// incoming ABI argument register live from entry, an explicit fixed-register
/// operand (e.g. a shift count in RCX, a return value in RAX), or a call-clobbered
/// caller-saved register across a call. Those live physical ranges are exactly the
/// "reserved points" the allocator enumerates in
/// [`crate::implicit_def_reservations`] and is REQUIRED to respect (greedy via
/// `reserved_interferes`, AY via candidate filtering + `self_check`). This gate
/// re-derives that reserved-point model INDEPENDENTLY from `post` and rejects any
/// allocation in which a vreg's live range covers a reserved point of an aliasing
/// register.
///
/// SOUNDNESS / no-false-reject: the predicate is exactly the allocator's own
/// `reserved_forbids` (`reserved point of an aliasing preg inside the vreg's live
/// range`). Every correct allocation — greedy's, and any AY allocation the fixed
/// encoding actually proposes — satisfies `!reserved_forbids` for every vreg by
/// construction, so this check cannot reject one. It fires ONLY on a solver
/// allocation that violates the reserved model, which is precisely the wrong-
/// allocation class this gate exists to catch (LRSPLIT-2's incoming-argument
/// clobber, now that [`crate::implicit_def_reservations`] models the arg register's
/// live-in span).
fn check_physreg_interference(
    post: &MachFunction,
    locations: &BTreeMap<VReg, Location>,
    report: &mut ValidationReport,
) {
    let liveness = compute_live_intervals(post);
    let reserved = crate::implicit_def_reservations(post, &liveness.inst_numbering);
    if reserved.is_empty() {
        return;
    }

    // Reverse the instruction numbering so a reserved position can be mapped back
    // to its instruction, to recognize the identity-copy carve-out below.
    let pos_to_inst: BTreeMap<u32, InstId> = liveness
        .inst_numbering
        .iter()
        .map(|(&id, &pos)| (pos, id))
        .collect();

    for interval in liveness.intervals.values() {
        let Some(&Location::Reg(preg)) = locations.get(&interval.vreg) else {
            continue;
        };
        for (&reserved_preg, points) in &reserved {
            if !crate::greedy::allocator_pregs_overlap(reserved_preg, preg) {
                continue;
            }
            // A reserved position inside the vreg's range is interference UNLESS it
            // is the boundary of an identity copy relating this vreg to the
            // reserved register — where the vreg and the register hold the SAME
            // value (the coalesced-argument / return hint). That single point is
            // exempt exactly as the linear-scan allocator's `hint_exempt` exempts
            // it; a reservation at any NON-copy position is still a real clobber.
            if let Some(&point) = points.iter().find(|&&pos| {
                interval.is_live_at(pos)
                    && !identity_copy_exempts_reservation(
                        post,
                        &pos_to_inst,
                        pos,
                        interval.vreg,
                        reserved_preg,
                    )
            }) {
                report.errors.push(ValidationError::PhysRegInterference {
                    vreg: interval.vreg,
                    preg,
                    reserved: reserved_preg,
                    point,
                });
                break;
            }
        }
    }
}

/// Whether the reserved position `pos` is the boundary of an IDENTITY COPY that
/// relates `vreg` to a physical register aliasing `reserved_preg` — a
/// `copy vreg <- p` (formal-argument / call-result materialization) or
/// `copy p <- vreg` (return / outgoing-argument) with `p` aliasing
/// `reserved_preg`. At such a copy the vreg and the reserved register hold the
/// SAME value, so coloring the vreg to that register turns the copy into a no-op
/// (`post_ra_coalesce` deletes it) rather than clobbering a distinct live value.
///
/// This is the exact carve-out the linear-scan allocator applies via the
/// copy-register hints' `hint_exempt` positions when biasing an argument / return
/// vreg onto its ABI register (see `copy_register_hints`): the allocator only ever
/// colors a vreg onto a reserved register at such an identity-copy point, so
/// mirroring the exemption here keeps `check_physreg_interference` in exact
/// agreement with the allocator's own `reserved_forbids` (it still rejects a
/// reservation of `reserved_preg` at any NON-copy position inside the vreg's
/// range — the genuine clobber class, including LRSPLIT-2's).
fn identity_copy_exempts_reservation(
    post: &MachFunction,
    pos_to_inst: &BTreeMap<u32, InstId>,
    pos: u32,
    vreg: VReg,
    reserved_preg: PReg,
) -> bool {
    let Some(&inst_id) = pos_to_inst.get(&pos) else {
        return false;
    };
    let Some(inst) = post.insts.get(inst_id.0 as usize) else {
        return false;
    };
    if !crate::phi_elim::is_copy_opcode(inst.opcode) {
        return false;
    }
    let (Some(def), Some(src)) = (inst.defs.first(), inst.uses.first()) else {
        return false;
    };
    // `copy vreg <- p` (formal-arg / call-result MATERIALIZATION — vreg's DEF).
    // A def writes vreg's home register, so exempting it is only sound when the
    // source preg aliases `reserved_preg` itself: then the copy is the identity
    // write `R <- R`-equivalent that populates vreg from R (the value R already
    // held). A def of vreg homed in R from a DIFFERENT preg would clobber R, so
    // the alias requirement is kept for this (writing) direction.
    if def.as_vreg() == Some(vreg)
        && src
            .as_preg()
            .is_some_and(|p| crate::greedy::allocator_pregs_overlap(p, reserved_preg))
    {
        return true;
    }
    // `copy p <- vreg` (return / outgoing-argument / duplicate call argument —
    // vreg is READ into `p`). Reading vreg — which lives in `reserved_preg` — does
    // NOT write `reserved_preg`, so it can never clobber the reserved value; the
    // reservation at such a point is necessarily a PROTECTIVE span (a call- or
    // incoming-argument span guarding the value already placed in `reserved_preg`)
    // whose intended occupant IS this vreg. This is exactly what the linear-scan
    // allocator's `hint_exempt` exempts: `copy_register_hints` records EVERY copy
    // position at which `vreg` is an endpoint (not only those targeting
    // `reserved_preg`), so when it biases `vreg` onto `reserved_preg` its
    // `reserved_interferes_except` skips this position too. Mirroring that keeps
    // the validator in exact agreement with the allocator — without it a value
    // passed into two argument registers (`f(a, a, ..)`: `Copy x0 <- v`, then
    // `Copy x1 <- v` inside x0's call-arg span) is spuriously rejected even though
    // the second copy only READS x0. `p` NOT aliasing `reserved_preg` is the whole
    // point; a genuine clobber (a NON-copy reservation, or a copy DEFINING a
    // distinct value into `reserved_preg`) is still rejected below.
    if src.as_vreg() == Some(vreg) && def.as_preg().is_some() {
        return true;
    }
    false
}

/// Find the first instruction index where two intervals are both live.
fn overlap_point(
    a: &crate::liveness::LiveInterval,
    b: &crate::liveness::LiveInterval,
) -> Option<u32> {
    for ra in &a.ranges {
        for rb in &b.ranges {
            if ra.overlaps(rb) {
                return Some(ra.start.max(rb.start));
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Phi-elimination guard.
// ---------------------------------------------------------------------------

fn check_phis_eliminated(post: &MachFunction, report: &mut ValidationReport) {
    for &block_id in &post.block_order {
        let Some(block) = post.blocks.get(block_id.0 as usize) else {
            continue;
        };
        for &inst_id in &block.insts {
            let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                continue;
            };
            if inst.flags.is_phi() {
                report.errors.push(ValidationError::PhiNotEliminated {
                    block: block_id,
                    inst: inst_id,
                });
            }
        }
    }
}

// ---------------------------------------------------------------------------
// (d) Spill-materialization discipline.
// ---------------------------------------------------------------------------

/// Enforce the spill-materialization adjacency contract (property d).
///
/// A spilled vreg's authoritative home is its stack slot, but the MACHINE data
/// path at a use goes slot -> unnamed scratch register (the reload) -> consumer,
/// and at a def goes producer -> unnamed scratch -> slot (the store). The
/// value-flow walk (a) validates spilled uses against the SLOT, so it is blind
/// to anything that happens to the scratch register in between — the documented
/// reload-register trust boundary. This check closes the exploitable part of
/// that boundary structurally: the scratch's lifetime must not cross ANY other
/// real instruction, i.e.
///
///  * every use of a disciplined slot-homed vreg must be immediately preceded
///    (modulo other spill pseudos serving the same consumer) by its
///    `PSEUDO_SPILL_LOAD` in the same block, and
///  * every `PSEUDO_SPILL_STORE` must immediately follow (modulo sibling spill
///    stores) the real instruction that defined its vreg.
///
/// `insert_spill_code` emits exactly this shape (loads directly before each
/// consumer, stores directly after each def), so a violation means some later
/// transform moved or deleted a pseudo — a reload/store whose scratch value
/// would cross a potentially-clobbering instruction. Fail closed.
///
/// DISCIPLINED vregs: only slot-homed vregs that have at least one spill pseudo
/// in the function. The x86-64 pipeline runs with `enable_spill_code = false`
/// (no pseudos at all — the encoder materializes slot operands at each site
/// itself), and rematerialized vregs have their loads replaced; both legitimately
/// carry slot-homed operands with no adjacent pseudo and are out of scope here.
fn check_spill_discipline(
    post: &MachFunction,
    locations: &BTreeMap<VReg, Location>,
    report: &mut ValidationReport,
) {
    let slot_homed = |v: &VReg| matches!(locations.get(v), Some(Location::Slot(_)));

    // Collect the disciplined set: slot-homed vregs touched by any spill pseudo.
    let mut disciplined: BTreeSet<VReg> = BTreeSet::new();
    for &block_id in &post.block_order {
        let Some(block) = post.blocks.get(block_id.0 as usize) else {
            continue;
        };
        for &inst_id in &block.insts {
            let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                continue;
            };
            let touched = match inst.opcode {
                PSEUDO_SPILL_LOAD => first_vreg(&inst.defs),
                PSEUDO_SPILL_STORE => first_vreg(&inst.uses),
                _ => None,
            };
            if let Some(v) = touched
                && slot_homed(&v)
            {
                disciplined.insert(v);
            }
        }
    }
    if disciplined.is_empty() {
        return;
    }

    for &block_id in &post.block_order {
        let Some(block) = post.blocks.get(block_id.0 as usize) else {
            continue;
        };
        // Reloads whose value is available for the NEXT real instruction.
        let mut pending_reloads: BTreeSet<VReg> = BTreeSet::new();
        // Defs awaiting their immediately-following spill store.
        let mut pending_stores: BTreeSet<VReg> = BTreeSet::new();
        let mut last_inst = InstId(u32::MAX);

        for &inst_id in &block.insts {
            let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                continue;
            };
            last_inst = inst_id;
            match inst.opcode {
                PSEUDO_SPILL_LOAD => {
                    // Loads for the next consumer must not interpose between a
                    // def and its store (the load's own scratch could collide
                    // with the pending store's scratch).
                    for &v in &pending_stores {
                        report
                            .errors
                            .push(ValidationError::SpillDisciplineViolation {
                                block: block_id,
                                inst: inst_id,
                                vreg: v,
                                reason: "spill store does not immediately follow its def \
                                     (a reload interposed)",
                            });
                    }
                    pending_stores.clear();
                    if let Some(v) = first_vreg(&inst.defs) {
                        pending_reloads.insert(v);
                    }
                }
                PSEUDO_SPILL_STORE => {
                    // A store invalidates pending reloads conservatively (its
                    // materialization may use the same scratch pool).
                    pending_reloads.clear();
                    if let Some(v) = first_vreg(&inst.uses)
                        && disciplined.contains(&v)
                        && !pending_stores.remove(&v)
                    {
                        report
                            .errors
                            .push(ValidationError::SpillDisciplineViolation {
                                block: block_id,
                                inst: inst_id,
                                vreg: v,
                                reason: "spill store is not adjacent to the def it commits",
                            });
                    }
                }
                _ => {
                    // A real instruction: check its disciplined uses were
                    // reloaded IMMEDIATELY before it.
                    for u in inst.vreg_uses() {
                        if disciplined.contains(&u) && !pending_reloads.contains(&u) {
                            report
                                .errors
                                .push(ValidationError::SpillDisciplineViolation {
                                    block: block_id,
                                    inst: inst_id,
                                    vreg: u,
                                    reason: "use of a spilled value without an immediately \
                                         preceding reload (scratch would cross another \
                                         instruction)",
                                });
                        }
                    }
                    // Any real instruction between a def and its store breaks
                    // the store's scratch lifetime.
                    for &v in &pending_stores {
                        report
                            .errors
                            .push(ValidationError::SpillDisciplineViolation {
                                block: block_id,
                                inst: inst_id,
                                vreg: v,
                                reason: "spill store does not immediately follow its def \
                                     (a real instruction interposed)",
                            });
                    }
                    pending_stores.clear();
                    pending_reloads.clear();
                    for d in inst.vreg_defs() {
                        if disciplined.contains(&d) {
                            pending_stores.insert(d);
                        }
                    }
                }
            }
        }

        // A def at block end whose store never arrived.
        for &v in &pending_stores {
            report
                .errors
                .push(ValidationError::SpillDisciplineViolation {
                    block: block_id,
                    inst: last_inst,
                    vreg: v,
                    reason: "def of a spilled value with no following spill store in its block",
                });
        }
    }
}

// ---------------------------------------------------------------------------
// (e) Spill-slot initialization dominance.
// ---------------------------------------------------------------------------

/// A compact fixed-width bitset over the analysis universe of validated slots
/// (dense-indexed `0..k`). Keeps the O(blocks × passes) slot-init fixpoint
/// word-parallel at TY-O0 scale (thousands of slots × thousands of blocks)
/// instead of cloning `BTreeSet`s per block per pass. All operations assume a
/// common width `k`; padding bits above `k` are held at 0 so equality and the
/// `full` seed compare canonically.
#[derive(Clone, PartialEq, Eq)]
struct SlotBits {
    words: Vec<u64>,
}

impl SlotBits {
    fn empty(k: usize) -> Self {
        SlotBits {
            words: vec![0u64; k.div_ceil(64)],
        }
    }
    /// The optimistic seed: every slot marked initialized (padding bits cleared).
    fn full(k: usize) -> Self {
        let mut b = SlotBits {
            words: vec![u64::MAX; k.div_ceil(64)],
        };
        let rem = k % 64;
        if rem != 0
            && let Some(last) = b.words.last_mut()
        {
            *last = (1u64 << rem) - 1;
        }
        b
    }
    #[inline]
    fn get(&self, i: usize) -> bool {
        (self.words[i / 64] >> (i % 64)) & 1 == 1
    }
    #[inline]
    fn set(&mut self, i: usize) {
        self.words[i / 64] |= 1u64 << (i % 64);
    }
    /// `self &= other` (same width).
    #[inline]
    fn intersect_with(&mut self, other: &SlotBits) {
        for (a, b) in self.words.iter_mut().zip(&other.words) {
            *a &= *b;
        }
    }
    /// `self |= other` (same width).
    #[inline]
    fn union_with(&mut self, other: &SlotBits) {
        for (a, b) in self.words.iter_mut().zip(&other.words) {
            *a |= *b;
        }
    }
}

/// (e) Slot-initialization dominance: prove every spill-slot RELOAD is
/// DEFINITELY INITIALIZED — reachable only along paths that first pass a store
/// to that slot. Converts the split-connector miscompile class from fail-SILENT
/// to fail-CLOSED. See [`ValidationError::SpillSlotUninitializedReload`].
///
/// ## Slot provenance / scoping
///
/// Only slots that carry at least one `PSEUDO_SPILL_LOAD` reload are validated.
/// That set is exactly the allocator-created spill slots:
///   * whole-vreg spills (`spill::insert_spill_code`) and live-range SPLIT-piece
///     spills both reload through `PSEUDO_SPILL_LOAD`;
///   * call-save/restore slots (`call_clobber`) reload through the same pseudo
///     (and their store sits in the same block right before the reload, so they
///     satisfy dominance trivially);
///   * local/alloca frame slots, prologue callee-saved register saves, and
///     outgoing stack-argument slots are NOT reloaded via the pseudo — they are
///     lowered to concrete loads/stores AFTER this validator runs — so they are
///     never in the validated set (no false positive on a non-spill frame slot).
///
/// The ONLY store form that initializes a validated slot in the post-RA stream
/// this validator sees is `PSEUDO_SPILL_STORE`: no non-pseudo instruction
/// writes a `StackSlot` operand before frame lowering, so enumerating that one
/// form captures every legitimate initializer (a missed initializer would be a
/// false positive; there is none).
///
/// ## Dataflow
///
/// A forward MUST analysis over the post-RA CFG. `GEN[b]` = validated slots
/// stored anywhere in block `b`; there is no KILL (a stored slot stays
/// initialized to block exit). `IN[b] = ⋂ OUT[p]` over reachable predecessors
/// `p` (function entry: `IN = ∅`); `OUT[b] = IN[b] ∪ GEN[b]`. Non-entry `OUT`
/// is seeded OPTIMISTIC (all slots initialized) and iterated to the greatest
/// fixpoint in reverse-post-order, so:
///   * a loop back-edge cannot spuriously mark a slot uninitialized at a header
///     its preheader store dominates (the correct loop-carried case validates);
///   * a slot stored ONLY inside the loop is correctly uninitialized on the
///     first iteration and a reload before the in-loop store is REJECTED;
///   * a reload that only exists on paths where the store happened is
///     definite-init and ACCEPTED (a genuinely dead-on-other-paths slot).
///
/// Whole-vreg LinearScan spills trivially satisfy this: the single store sits
/// right after the single SSA def, which dominates every use hence every
/// reload, so the gate is silent on them.
///
/// Predecessors and reachability are recomputed from the `succs` lists (the
/// same CFG the rest of the validator walks) rather than trusted from a possibly
/// stale `preds` list — so a dropped incoming edge cannot hide an uninitialized
/// path (a false negative). Everything is recomputed from `post`, independent of
/// the allocator's / splitter's own bookkeeping.
fn check_slot_init_dominance(post: &MachFunction, report: &mut ValidationReport) {
    let n = post.blocks.len();
    if n == 0 {
        return;
    }

    // --- 1. Scope: validated slots = slots with >= 1 PSEUDO_SPILL_LOAD reload.
    let mut validated_set: BTreeSet<StackSlotId> = BTreeSet::new();
    for block in &post.blocks {
        for &inst_id in &block.insts {
            let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                continue;
            };
            if inst.opcode == PSEUDO_SPILL_LOAD
                && let Some(slot) = first_slot(&inst.uses)
            {
                validated_set.insert(slot);
            }
        }
    }
    if validated_set.is_empty() {
        return; // No allocator spill-slot reloads to validate — fast path.
    }
    let slot_idx: BTreeMap<StackSlotId, usize> = validated_set
        .iter()
        .enumerate()
        .map(|(i, &s)| (s, i))
        .collect();
    let k = validated_set.len();

    // --- 2. Reachability (DFS from entry over succs). cfg_reverse_post_order
    // appends UNREACHABLE blocks after the reachable ones, so re-derive the
    // reachable set explicitly: unreachable blocks never execute, so their
    // reloads must neither constrain the meet nor be flagged.
    let entry = post.entry_block;
    let mut reachable = vec![false; n];
    if (entry.0 as usize) < n {
        let mut stack = vec![entry];
        reachable[entry.0 as usize] = true;
        while let Some(b) = stack.pop() {
            for &s in &post.blocks[b.0 as usize].succs {
                if (s.0 as usize) < n && !reachable[s.0 as usize] {
                    reachable[s.0 as usize] = true;
                    stack.push(s);
                }
            }
        }
    }

    // Predecessors recomputed from succs (single CFG source of truth).
    let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); n];
    for (bi, block) in post.blocks.iter().enumerate() {
        if !reachable[bi] {
            continue;
        }
        for &s in &block.succs {
            if (s.0 as usize) < n {
                preds[s.0 as usize].push(BlockId(bi as u32));
            }
        }
    }

    // --- 3. GEN[b] = validated slots stored anywhere in reachable block b.
    let mut gen_sets: Vec<SlotBits> = vec![SlotBits::empty(k); n];
    for (bi, block) in post.blocks.iter().enumerate() {
        if !reachable[bi] {
            continue;
        }
        for &inst_id in &block.insts {
            let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                continue;
            };
            if inst.opcode == PSEUDO_SPILL_STORE
                && let Some(slot) = first_slot(&inst.uses)
                && let Some(&i) = slot_idx.get(&slot)
            {
                gen_sets[bi].set(i);
            }
        }
    }

    // IN[b] = ⋂ OUT[p] over reachable predecessors (entry: ∅).
    let in_state = |bi: usize, out: &[SlotBits]| -> SlotBits {
        if BlockId(bi as u32) == entry {
            return SlotBits::empty(k);
        }
        let mut it = preds[bi].iter().filter(|p| reachable[p.0 as usize]);
        match it.next() {
            // Reachable with no reachable predecessor cannot happen for a
            // non-entry block; treat defensively as entry-uninitialized.
            None => SlotBits::empty(k),
            Some(&first) => {
                let mut acc = out[first.0 as usize].clone();
                for p in it {
                    acc.intersect_with(&out[p.0 as usize]);
                }
                acc
            }
        }
    };

    // --- 4. Forward MUST fixpoint. Entry's OUT = GEN[entry] (IN = ∅); every
    // other reachable OUT seeded FULL (optimistic) so back-edges converge
    // downward to the greatest fixpoint.
    let mut out: Vec<SlotBits> = (0..n)
        .map(|bi| {
            if BlockId(bi as u32) == entry || !reachable[bi] {
                gen_sets[bi].clone()
            } else {
                SlotBits::full(k)
            }
        })
        .collect();

    let rpo = cfg_reverse_post_order(post);
    loop {
        let mut changed = false;
        for &b in &rpo {
            let bi = b.0 as usize;
            if bi >= n || !reachable[bi] || b == entry {
                continue;
            }
            let mut new_out = in_state(bi, &out);
            new_out.union_with(&gen_sets[bi]);
            if new_out != out[bi] {
                out[bi] = new_out;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // --- 5. Check pass: replay each reachable block from its converged IN and
    // flag every reload whose slot is not initialized at that program point.
    for &b in &rpo {
        let bi = b.0 as usize;
        if bi >= n || !reachable[bi] {
            continue;
        }
        let mut cur = in_state(bi, &out);
        for &inst_id in &post.blocks[bi].insts {
            let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                continue;
            };
            match inst.opcode {
                PSEUDO_SPILL_STORE => {
                    if let Some(slot) = first_slot(&inst.uses)
                        && let Some(&i) = slot_idx.get(&slot)
                    {
                        cur.set(i);
                    }
                }
                PSEUDO_SPILL_LOAD => {
                    if let Some(slot) = first_slot(&inst.uses)
                        && let Some(&i) = slot_idx.get(&slot)
                        && !cur.get(i)
                    {
                        // Uninitialized reload. Name the offending path shape: a
                        // reachable predecessor whose exit lacks the slot, else
                        // `None` (uninitialized straight from function entry).
                        let uninit_pred = preds[bi]
                            .iter()
                            .copied()
                            .find(|p| reachable[p.0 as usize] && !out[p.0 as usize].get(i));
                        report
                            .errors
                            .push(ValidationError::SpillSlotUninitializedReload {
                                block: b,
                                inst: inst_id,
                                slot,
                                uninit_pred,
                            });
                    }
                }
                _ => {}
            }
        }
    }
}

// ---------------------------------------------------------------------------
// (a) + (c) Value-flow walk.
// ---------------------------------------------------------------------------

/// The symbolic register/slot file at one program point. Absent key = lattice
/// `Top`; a present [`Sym`] is `Defined(v)` or `Conflict(set)`.
type LocState = BTreeMap<Location, Sym>;

/// Walk every block of the post-alloc code in program order, threading a
/// per-block entry state derived from predecessors. Records value-flow
/// mismatches (a) at original uses and phi-transfer breakage (c) at edge ends.
fn check_value_flow(
    pre: &MachFunction,
    post: &MachFunction,
    locations: &BTreeMap<VReg, Location>,
    report: &mut ValidationReport,
) {
    // The original phi specification: phi_specs[phi_block] = Vec<(dest, [(pred, src)])>.
    // The phi dest/sources come from `pre` (the SSA spec); the *realizing
    // predecessor* for each incoming source is taken from `post`, because
    // `split_critical_edges` may have interposed a fresh single-pred/single-succ
    // jump block on a critical edge and placed that edge's realizing copy there.
    let phi_specs = collect_phi_specs(pre, post);

    // Identify which original instructions survived into `post`, so the walk can
    // distinguish ORIGINAL uses (which must validate) from inserted spill/copy
    // pseudos (which only propagate). An instruction is "inserted" iff its
    // InstId did not exist in the pre-alloc function.
    let original_inst_count = pre.insts.len() as u32;

    // TRUST-BOUNDARY (spill reload / rematerialization temporaries).
    //
    // A spilled-then-reloaded value, and a rematerialized value, are produced by
    // INSERTED instructions (`PSEUDO_SPILL_LOAD`, or a remat clone of the
    // defining instruction) whose destination is a scratch *physical* register
    // that the `AllocationResult` does NOT name — for a rematerialized vreg the
    // spiller even DROPS it from `result.spills`, so it has no `Location` at all.
    // Assigning those reload/remat temporaries is the spill-code inserter's job
    // (`crate::spill` / `crate::remat`), covered by their own tests, and is
    // EXPLICITLY outside this validator's value-flow trust boundary (see the
    // module header). The symbolic walk cannot see which PReg such a reload/remat
    // landed in, so it must not assert against it.
    //
    // We therefore collect every vreg that (a) has NO `Location` (neither
    // allocated nor spilled) yet (b) is DEFINED by an inserted instruction in
    // `post`. A use of such a vreg is served by an out-of-scope reload/remat temp
    // and is SKIPPED by the value-flow check. Crucially this is narrow: a vreg
    // that is unmapped AND never defined by an inserted instruction (a genuinely
    // dropped live value — a real allocator bug) is NOT in this set and still
    // fails closed as `UnmappedVReg`. Interference (b) and per-edge phi-transfer
    // (c) remain fully fail-closed for these vregs as well.
    let remat_reload_temps = collect_remat_reload_temps(post, locations, original_inst_count);

    // TRUST-BOUNDARY (greedy live-range SPLIT temporaries).
    //
    // The greedy allocator's live-range splitter rewrites an original SSA value
    // into a CHAIN of fresh half-vregs joined by realizing copies (`v_lo <- v_hi`),
    // and rewrites the original use to read the post-split half. Those fresh
    // vregs (`v30`, `v31`, ... above the snapshot's namespace) carry the SAME
    // architectural value but under brand-new ids the symbolic value-flow model —
    // which checks that a use of vreg `X` finds `X.id` in `X`'s location — cannot
    // tie back to the original SSA value (a split copy `X <- Y` makes `X`'s
    // location hold `Y.id`, not `X.id`). Splitter correctness (that each split
    // copy preserves the value across the split point) is the SPLITTER's own
    // verified responsibility (`crate::split`, `crate::greedy`), with its own
    // tests; it is outside THIS validator's value-flow trust boundary, exactly
    // like a spill-reload temporary.
    //
    // We identify these by namespace: a use vreg that does NOT appear anywhere in
    // the (coalesce-rewritten) `pre` spec is a post-pipeline-introduced
    // split/reload temporary. Computing the original-vreg set directly from `pre`
    // (rather than trusting `next_vreg` hygiene) makes the criterion robust. The
    // carve-out is NARROW: it only relaxes property (a) for these synthetic
    // vregs; interference (b, over `post`) and per-edge phi-transfer (c) — which
    // together cover the #52/#53/#63/#64 regalloc/splitter miscompile class —
    // remain FULLY fail-closed, including for the split temporaries.
    let pre_vregs: BTreeSet<VReg> = collect_function_vregs(pre);

    // SCOPE (documented). Property (a) follows each original SSA value to its uses
    // and requires the POST allocation to deliver, into that value's assigned home,
    // exactly the symbolic id the SPEC's own value-flow delivers there — with ONE
    // narrowly-scoped report-only carve-out (R3) for the cross-block copy-alias the
    // block-local numbering genuinely cannot resolve on the non-SSA x86 IR.
    //
    //  * AArch64 path (SSA-with-phis): the spec carries PHI instructions, which
    //    anchor join / loop recurrences. Property (a) uses the block-local
    //    value-numbering `expected` (the SSA identity of a normal def, or the
    //    aliased source of a two-address fixup copy) and stays FULLY fail-closed,
    //    with per-edge phi-transfer (c) closing the #63/#64 splitter/join class.
    //    The phi-bearing path takes NONE of the relaxations below.
    //
    //  * x86-64 path (PHI-FREE): ISel lowers phis to copies before regalloc, so
    //    the spec is a non-SSA machine IR. The required value at each use is the
    //    SPEC's OWN value-flow at that exact (inst, vreg), computed over the
    //    phi-free PRE program by [`compute_pre_expected`] — a vreg-keyed fixpoint
    //    that propagates copies (so a loop-carried `v_iv <- v_next` latch copy
    //    makes the loop-header meet of the preheader id and the latch id collapse
    //    to CONFLICT in the SPEC) and re-establishes phi dests (a no-op on x86).
    //    POST must reproduce that spec value. The fail-closed obligations, keyed on
    //    the use's exact (inst, vreg) spec value (never a whole-function flag):
    //
    //      - spec DEFINITE(v) but POST CONFLICT(None) — a forward-merge clobber
    //        (#53) overwrote the value on one merge edge. REJECTED. This stays
    //        fail-closed even when the function ALSO contains an unrelated loop,
    //        because the obligation is per-use.
    //
    //      - spec CONFLICT(None) but POST DEFINITE(Some(w)) — a wrong latch / merge
    //        copy that STOPS a legitimate recurrence (#63/#64), e.g. `v_iv <- v0`
    //        so the induction variable never advances. The spec value-flow is
    //        CONFLICT at the in-loop use (the latch threads `v_next`), POST holds a
    //        single definite id; `found != expected`, REJECTED.
    //
    //      - spec CONFLICT(None) and POST CONFLICT(None) — a valid loop recurrence
    //        (both edges thread their own source). `found == expected`, ACCEPTED:
    //        the allocation is "no more ambiguous than the spec."
    //
    //    Two NARROW, per-use relaxations remain on the phi-free path:
    //
    //   (R2) POST use reading lattice-TOP (a home NEVER written on any path) is
    //        SKIPPED — a live-in argument vreg or a dead two-address self-use of an
    //        undefined LHS. NOT a clobber (a clobber reads CONFLICT, not TOP), so
    //        the forward-merge clobber stays fail-closed under (R2).
    //
    //   (R3) DEFINITE-vs-DEFINITE cross-block copy-alias (spec DEFINITE(v), POST
    //        DEFINITE(Some(w)), w != v) is REPORT-ONLY. A realizing copy `v <- w`
    //        interposed in a PREDECESSOR block (phi elimination / a two-address
    //        fixup), or a coalesced representative, leaves `v`'s home holding `w`'s
    //        id. The POST walk is LOCATION-keyed and block-local for non-phi copy
    //        aliasing; the spec walk is VREG-keyed; on the non-SSA post-phi-elim
    //        x86 IR these can legitimately disagree on the concrete id while the
    //        machine code is correct. PROVEN by box_i32 (a phi-free ACYCLIC
    //        Drop-diamond): its `main` reads the boxed constant flowed through a
    //        cross-block copy where the spec id differs — a false positive on
    //        byte-identical machine code that has matched the LLVM oracle for the
    //        entire project. R3 is the MINIMAL carve-out: it relaxes ONLY the case
    //        where BOTH found and expected are DEFINITE-but-different. The two
    //        recurrence-stopping / merge-clobber directions above (one side a
    //        CONFLICT) are NOT relaxed and STILL fail closed, as do interference
    //        (b) and per-edge phi-transfer (c). A genuine two-live-vregs-share-a-
    //        home clobber that could surface as a definite mismatch is independently
    //        caught by interference (b), and the x86 path is backstopped by
    //        stream-replay + the clang/LLVM differential oracle.
    //
    //    RESIDUAL (honest): (i) because the lattice carries a single id (or
    //    CONFLICT), two CONFLICTs with DIFFERENT source SETS compare equal, so a
    //    wrong latch that keeps POST at CONFLICT but threads a different SECOND
    //    source is not pinned by (a) — confined to the spec-already-CONFLICT
    //    (in-/post-loop recurrence) points, covered by interference (b) and the e2e
    //    oracle. (ii) R3 admits a DEFINITE-vs-DEFINITE mismatch report-only; a real
    //    such clobber is caught by interference (b) and the differential oracle.
    //
    // INTERFERENCE (b, recomputed over `post`) — the #52/#53 register-overlap class
    // — and per-edge phi-transfer (c) stay FULLY fail-closed in ALL cases.
    let phi_free = !pre_has_phis(pre);
    // (R2) applies to any phi-free function (acyclic or loop).
    let skip_top_reads = phi_free;
    // (R3) the DEFINITE-vs-DEFINITE cross-block copy-alias report-only carve-out.
    let relax_definite_alias = phi_free;
    // ORIGINAL copies coalesced away: since the spec is UNREWRITTEN (the
    // self-certification fix), a use of such a copy's dest legitimately reads
    // its source's ORIGINAL id from the shared location. The obligation for
    // those uses (and for phi edges whose source is such a dest) is the SPEC's
    // OWN value-flow — still derived purely from `pre`, trusting nothing the
    // allocator did.
    let removed_copy_dsts = collect_removed_original_copy_dsts(pre, post);
    // The SPEC's own value-flow at each original use: the primary obligation on
    // the phi-free x86 path, and the removed-original-copy fallback (plus the
    // per-edge phi obligation) on the phi-bearing AArch64 path.
    let spec_flow = if phi_free || !removed_copy_dsts.is_empty() {
        Some(compute_pre_spec_flow(pre))
    } else {
        None
    };
    let empty_expected = PreExpected::new();
    let pre_expected = spec_flow
        .as_ref()
        .map(|f| &f.expected)
        .unwrap_or(&empty_expected);
    // Generalized per-edge phi obligation (spec value of the edge source at the
    // PRE pred's exit) — only needed when original copies were merged away;
    // otherwise the exact `Defined(src.id)` obligation applies.
    let spec_exit = if !phi_free && !removed_copy_dsts.is_empty() {
        spec_flow.as_ref().map(|f| &f.exit_states)
    } else {
        None
    };
    if phi_free && std::env::var("TRUST_CG_DEBUG_VALIDATOR").is_ok() {
        eprintln!(
            "regalloc-validator: {}: phi-free value-flow is FAIL-CLOSED via spec \
             value-flow (skip-top-reads={skip_top_reads}, definite-alias \
             report-only={relax_definite_alias}); interference + per-edge \
             phi-transfer also fail-closed",
            pre.name
        );
    }

    // Compute each block's exit state as a FIXPOINT of the forward value-flow
    // dataflow, then validate against the converged states.
    //
    // Why a fixpoint and not a single forward pass: a loop header's predecessors
    // include a back-edge from the latch, which appears LATER than the header in
    // `block_order`. A single in-order pass reaches the header before the latch,
    // so the latch's exit state is missing when the header is first processed.
    // The old single-pass code collapsed every location to None across such an
    // unwalked back-edge, which left a loop-header phi's destination location at
    // None — producing a SPURIOUS value-flow mismatch at every in-loop use of a
    // correctly loop-carried phi (a false positive that blocked valid loop
    // allocations).
    //
    // Instead we iterate the forward pass to a fixpoint. The per-location lattice
    // descends optimistic-unknown (absent from the map = "no path has written it
    // yet", treated as Top) -> Some(v) -> None (conflicting). The transfer
    // function ([`apply_inst`]) and the meet ([`meet_pred_states`] /
    // [`intersect_agreement`]) are monotone in this lattice, so iteration
    // converges to the greatest fixpoint. That GFP is anchored by each block's
    // NON-back-edge predecessors (whose exit states are computed without circular
    // assumption), so it cannot optimistically "invent" a value that does not
    // actually reach the header on every incoming edge: a location keeps a value
    // only if EVERY predecessor (preheader AND latch) delivers it. This makes a
    // correct loop-carried phi validate while a wrong loop-carried copy — where
    // the latch threads the wrong source into the phi-dest location — still leaves
    // the dest location holding the wrong id on the latch edge and is rejected by
    // the per-edge phi-transfer check below (and the phi-establishment refuses to
    // assert `dest.id`, so in-loop uses also fail closed).
    let exit_states = compute_exit_states_fixpoint(pre, post, locations, &phi_specs, spec_exit);

    // (R4) copy-equivalence for the spurious identity-recurrence conflict carve-out
    // — only the phi-free path takes the value-flow relaxations, so only build it
    // there (keeps the O(vregs) build off the phi-bearing hot path).
    let copy_equiv = if phi_free {
        Some(CopyEquiv::build(pre))
    } else {
        None
    };

    check_value_flow_final(CheckValueFlowFinalInputs {
        pre,
        post,
        locations,
        phi_specs: &phi_specs,
        exit_states: &exit_states,
        pre_expected,
        spec_exit,
        removed_copy_dsts: &removed_copy_dsts,
        original_inst_count,
        remat_reload_temps: &remat_reload_temps,
        pre_vregs: &pre_vregs,
        phi_free,
        skip_top_reads,
        relax_definite_alias,
        copy_equiv: copy_equiv.as_ref(),
        report,
    });
}

/// Destinations of ORIGINAL vreg-source copy instructions that coalescing
/// removed from the post block lists (only `apply_coalescing` removes original
/// non-phi instructions; phi instructions are removed by `eliminate_phis` and
/// excluded here). Uses of these vregs — and phi edges sourced from them — take
/// the spec-value-flow obligation instead of the plain SSA-identity one, since
/// the (sound) merge makes the shared location legitimately carry the copy
/// SOURCE's original id.
fn collect_removed_original_copy_dsts(pre: &MachFunction, post: &MachFunction) -> BTreeSet<VReg> {
    let mut listed: BTreeSet<u32> = BTreeSet::new();
    for block in &post.blocks {
        for inst_id in &block.insts {
            listed.insert(inst_id.0);
        }
    }
    let mut dsts = BTreeSet::new();
    for (i, inst) in pre.insts.iter().enumerate() {
        if inst.flags.is_phi() {
            continue;
        }
        if inst.opcode != PSEUDO_COPY && inst.opcode != IR_COPY_OPCODE {
            continue;
        }
        if listed.contains(&(i as u32)) {
            continue;
        }
        if let (Some(dst), Some(_src)) = (first_vreg(&inst.defs), first_vreg(&inst.uses)) {
            dsts.insert(dst);
        }
    }
    dsts
}

/// The SPEC value the phi edge `spec_pred -> phi_block` must deliver for source
/// `src`: the spec's own value-flow for `src` at `spec_pred`'s exit when the
/// generalized obligation is active, else exactly `Defined(src.id)`. An absent
/// key defaults to `Defined(src.id)` (the sparse spec walk leaves untracked /
/// unobservable vregs at their own id — see [`pre_tracked_vregs`]).
fn phi_edge_expected(
    spec_exit: Option<&BTreeMap<BlockId, Rc<PreState>>>,
    spec_pred: BlockId,
    src: VReg,
) -> Sym {
    spec_exit
        .and_then(|m| m.get(&spec_pred))
        .and_then(|s| s.get(&src).cloned())
        .unwrap_or(Sym::Defined(src.id))
}

/// Spec-side view of instruction `inst_id`: the ORIGINAL instruction (with
/// unrewritten operands) when it survived from the pre-alloc snapshot, `None`
/// for pipeline-inserted instructions.
fn spec_inst(
    pre: &MachFunction,
    inst_id: InstId,
    original_inst_count: u32,
) -> Option<&RegAllocInst> {
    if inst_id.0 < original_inst_count {
        pre.insts.get(inst_id.0 as usize)
    } else {
        None
    }
}

/// Inputs to [`check_value_flow_final`] — the error-recording tail of
/// [`check_value_flow`], factored out so the test-side dense REFERENCE
/// implementations of the two fixpoint products ([`compute_pre_expected`] /
/// [`compute_exit_states_fixpoint`]) can drive the IDENTICAL recording code
/// for decision-identity testing.
struct CheckValueFlowFinalInputs<'a> {
    pre: &'a MachFunction,
    post: &'a MachFunction,
    locations: &'a BTreeMap<VReg, Location>,
    phi_specs: &'a PhiSpecs,
    exit_states: &'a BTreeMap<BlockId, LocState>,
    pre_expected: &'a PreExpected,
    /// SPEC value-flow exit states for the generalized phi-edge obligation
    /// (`None` = exact `Defined(src.id)` obligation).
    spec_exit: Option<&'a BTreeMap<BlockId, Rc<PreState>>>,
    /// Dests of original copies coalesced away — their uses take the
    /// spec-value-flow fallback on the phi-bearing path.
    removed_copy_dsts: &'a BTreeSet<VReg>,
    original_inst_count: u32,
    remat_reload_temps: &'a BTreeSet<VReg>,
    pre_vregs: &'a BTreeSet<VReg>,
    phi_free: bool,
    skip_top_reads: bool,
    relax_definite_alias: bool,
    /// Copy-equivalence for the spurious identity-recurrence conflict carve-out
    /// (R4); `Some` only on the phi-free path.
    copy_equiv: Option<&'a CopyEquiv>,
    report: &'a mut ValidationReport,
}

/// The error-recording tail of [`check_value_flow`]: the final per-block walk
/// over the CONVERGED exit states (property a) and the per-edge phi-transfer
/// check (property c).
fn check_value_flow_final(inputs: CheckValueFlowFinalInputs<'_>) {
    let CheckValueFlowFinalInputs {
        pre,
        post,
        locations,
        phi_specs,
        exit_states,
        pre_expected,
        spec_exit,
        removed_copy_dsts,
        original_inst_count,
        remat_reload_temps,
        pre_vregs,
        phi_free,
        skip_top_reads,
        relax_definite_alias,
        copy_equiv,
        report,
    } = inputs;
    // ---- (a) value-flow at original uses, over the CONVERGED exit states ----
    // Re-run the per-block transfer one final time using the fixpoint entry
    // states; errors are recorded only on this final pass so a transient mismatch
    // seen mid-iteration (before the back-edge state was available) is never
    // reported.
    for &block_id in &post.block_order {
        let Some(block) = post.blocks.get(block_id.0 as usize) else {
            continue;
        };
        let mut state = block_entry_state(
            block,
            exit_states,
            locations,
            phi_specs,
            block_id,
            spec_exit,
        );

        // Block-local VALUE-NUMBERING for non-phi value-defining copies.
        //
        // An ordinary (non-phi) copy `dst <- src` — e.g. an x86 two-address fixup
        // move or an ISel reg-reg `mov` that coalescing could NOT remove because
        // `src` and `dst` interfere — makes `dst` a FRESH SSA value whose content
        // equals `src`'s. The symbolic walk writes `src`'s value into `dst`'s
        // location, so at a later use of `dst` the location holds `src.id`, not
        // `dst.id`. `vreg_val` records, per vreg, the symbolic value that vreg is
        // currently DEFINED to equal: a generic def sets it to the vreg's own id;
        // a non-phi copy aliases `dst` to `src`'s expected value; a two-address
        // op that redefines the vreg resets it to its own id. A use of `v` is then
        // checked against `vreg_val[v]` (defaulting to `Some(v.id)`), which is the
        // SSA identity for a normal def and the aliased source for a copy.
        //
        // This is BLOCK-LOCAL: at block entry every live-in defaults to its own
        // id, which is correct because copy aliases are local two-address fixups
        // while cross-block values are genuine SSA defs (`Some(id)`); a copy alias
        // that somehow escaped its block would simply default to `Some(v.id)` and
        // fail CLOSED (conservative). Phi-realizing copies are NOT aliased here —
        // their dest identity is re-established at the join (`block_entry_state`).
        let mut vreg_val: BTreeMap<VReg, Sym> = BTreeMap::new();

        for &inst_id in &block.insts {
            let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                continue;
            };
            let is_inserted = inst_id.0 >= original_inst_count;
            // The SPEC view of this instruction: original operands (pre-coalesce,
            // pre-split ids) for surviving original insts, None for inserted ones.
            // Machine LOCATIONS come from the POST operands (what codegen encodes);
            // symbolic VALUES are named by the SPEC operands — so a wrong coalesce
            // (two interfering spec values merged onto one location) is visible as
            // the wrong spec id at a use, instead of self-certifying.
            let spec = spec_inst(pre, inst_id, original_inst_count);

            // ---- (a) check original uses BEFORE applying this inst's defs ----
            if !is_inserted && !inst.flags.is_phi() {
                for (idx, op) in inst.uses.iter().enumerate() {
                    let Some(vreg) = op.as_vreg() else { continue };
                    // Skip uses served by an out-of-scope reload/remat temporary
                    // (documented trust boundary): the value lives in a scratch
                    // register the AllocationResult does not name.
                    if remat_reload_temps.contains(&vreg) {
                        continue;
                    }
                    // Skip uses rewritten to a greedy live-range SPLIT temporary
                    // (a vreg absent from the original `pre` namespace): the split
                    // chain carries the value under fresh ids the value-flow model
                    // cannot tie to the original SSA value. Splitter correctness is
                    // covered by its own tests; interference + phi-transfer stay
                    // fail-closed for these vregs.
                    if !pre_vregs.contains(&vreg) {
                        continue;
                    }
                    // The ORIGINAL (spec) vreg this use denotes: positionally
                    // paired from the pre snapshot (coalescing/splitting rewrite
                    // operands in place, preserving arity). Defensive default:
                    // the post operand itself (historical behavior).
                    let spec_vreg = spec
                        .and_then(|s| s.uses.get(idx))
                        .and_then(|sop| sop.as_vreg())
                        .unwrap_or(vreg);
                    // On the phi-free x86 path the REQUIRED value at this use is the
                    // SPEC's own value-flow at this exact (inst, vreg) — the
                    // principled, whole-function, fail-closed obligation. On the
                    // phi-bearing AArch64 path we keep the block-local value-number.
                    let expected = if phi_free {
                        pre_expected
                            .get(&(inst_id, spec_vreg))
                            .cloned()
                            .unwrap_or(Sym::Defined(spec_vreg.id))
                    } else {
                        vreg_val
                            .get(&spec_vreg)
                            .cloned()
                            .unwrap_or(Sym::Defined(spec_vreg.id))
                    };
                    // Phi-bearing path, use of a coalesced-away original copy's
                    // dest: the shared location legitimately holds the copy
                    // SOURCE's original id — the spec's own value-flow at this
                    // use. Accept that spec-derived value as well (sound: it is
                    // computed purely from `pre`; a wrong merge still mismatches
                    // both obligations).
                    let spec_fallback = if !phi_free && removed_copy_dsts.contains(&spec_vreg) {
                        pre_expected.get(&(inst_id, spec_vreg))
                    } else {
                        None
                    };
                    check_original_use(
                        vreg,
                        spec_vreg,
                        block_id,
                        inst_id,
                        locations,
                        &state,
                        &expected,
                        spec_fallback,
                        skip_top_reads,
                        relax_definite_alias,
                        copy_equiv,
                        report,
                    );
                }
            }

            // ---- transfer function: update the symbolic location file ----
            apply_inst(inst, spec, locations, &mut state);
            // ---- value-numbering transfer (mirrors apply_inst's defs) ----
            update_vreg_val(inst, spec, &mut vreg_val);
        }
    }

    // ---- (c) phi-transfer correctness at edge ends, PER INCOMING EDGE ----
    // For each original phi (dest, [(pred, src)]) and each predecessor `pred`,
    // `pred`'s EXIT state must place EXACTLY `src.id` (the source named for THAT
    // edge) in `dest`'s assigned location. Phi-realizing copies were modeled as
    // ordinary value propagation, so this directly detects:
    //   * #64 — a missing/clobbered realizing copy on a call-free join, leaving
    //     `dest_loc` holding a stale value (or None) on the affected edge; and
    //   * a copy reading the WRONG predecessor's source (e.g. `dest <- src_B2`
    //     emitted on the `B1` edge), leaving `dest_loc` = `src_B2.id` on `B1`'s
    //     exit — caught because the obligation is per-edge, not a per-dest union.
    // There is intentionally no "acceptable source" set: a source correct on one
    // edge does not satisfy a different edge's obligation.
    for (phi_block, specs) in phi_specs {
        for (dest, sources) in specs {
            let Some(&dest_loc) = locations.get(dest) else {
                report.errors.push(ValidationError::UnmappedVReg {
                    block: *phi_block,
                    inst: InstId(u32::MAX),
                    vreg: *dest,
                });
                continue;
            };
            for edge in sources {
                let Some(exit) = exit_states.get(&edge.realizing_pred) else {
                    continue; // unreachable / not-yet-walked pred: skip (conservative)
                };
                // The edge must deliver the SPEC value of `src` on this edge —
                // exactly `Defined(src.id)` in the default case, or the spec's
                // own value-flow at the PRE pred's exit when original copies
                // were coalesced away (a merged copy dest legitimately carries
                // its source's original id). Any other value is broken.
                let expected = phi_edge_expected(spec_exit, edge.spec_pred, edge.src);
                let ok = exit.get(&dest_loc) == Some(&expected);
                if !ok {
                    report.errors.push(ValidationError::PhiTransferBroken {
                        phi_dest: *dest,
                        phi_src: edge.src,
                        pred: edge.realizing_pred,
                        phi_block: *phi_block,
                        found: exit.get(&dest_loc).and_then(Sym::to_sym_val),
                    });
                }
            }
        }
    }
}

/// Check one original use against the current symbolic state (property a).
///
/// `expected` is the symbolic value this use is REQUIRED to read — on the x86
/// phi-free path it is the SPEC's own value-flow at this exact (inst, vreg)
/// (see [`compute_pre_expected`]); on the AArch64 phi-bearing path it is the
/// block-local value-number (`Defined(v.id)` for a normal def, or the aliased
/// source value for a non-phi value-defining copy — see [`check_value_flow`]).
/// The use is REJECTED iff POST's home for `vreg` does not hold `expected`,
/// except for the two narrowly-scoped phi-free relaxations below.
///
/// Both `found` (POST's home) and `expected` (the SPEC) are FULL [`Sym`] lattice
/// elements, so the comparison is exact: `Defined(a) != Defined(b)` for a != b,
/// `Defined(_) != Conflict(_)`, and — crucially for residual (a) — two
/// `Conflict`s with DIFFERENT source sets compare UNEQUAL. A wrong latch/merge copy
/// that keeps POST at a conflict but threads a different second source than the
/// spec's conflict is therefore caught HERE by value-flow, not only by the
/// interference backstop.
///
/// `skip_top_reads` (relaxation R2, phi-free inputs) suppresses the report when
/// the use reads lattice-TOP — a location NEVER written on any path (absent from
/// `state`), i.e. a live-in argument vreg or a dead two-address self-use of an
/// undefined LHS. This is distinguished from a CONFLICT (`state[loc]` is a
/// `Conflict` — paths disagree), which is a genuine merge clobber and stays
/// fail-closed.
///
/// `relax_definite_alias` (relaxation R3, phi-free inputs) suppresses the report
/// when BOTH `found` and `expected` are DEFINITE but different (`found = Defined(w)`,
/// `expected = Defined(v)`, w != v) — the cross-block copy-alias class the
/// block-local value-numbering cannot resolve on the non-SSA post-phi-elim x86 IR
/// (see R3 in [`check_value_flow`]). Crucially R3 does NOT fire when EITHER side is
/// a CONFLICT: spec CONFLICT vs POST DEFINITE is the wrong-latch / recurrence-
/// stopping bug (#63/#64), spec DEFINITE vs POST CONFLICT is the forward-merge
/// clobber (#53), and (after residual (a)) CONFLICT vs differing CONFLICT is the
/// wrong-second-source latch — all three STILL fail closed.
#[allow(clippy::too_many_arguments)]
fn check_original_use(
    vreg: VReg,
    spec_vreg: VReg,
    block_id: BlockId,
    inst_id: InstId,
    locations: &BTreeMap<VReg, Location>,
    state: &LocState,
    expected: &Sym,
    spec_fallback: Option<&Sym>,
    skip_top_reads: bool,
    relax_definite_alias: bool,
    copy_equiv: Option<&CopyEquiv>,
    report: &mut ValidationReport,
) {
    // The MACHINE location read is the POST operand's (`vreg`, possibly a
    // coalesced representative); the VALUE required is the SPEC's (`spec_vreg`).
    let Some(&loc) = locations.get(&vreg) else {
        report.errors.push(ValidationError::UnmappedVReg {
            block: block_id,
            inst: inst_id,
            vreg: spec_vreg,
        });
        return;
    };
    // `state.get(&loc)`: None = TOP (never written on any path) ;
    // Some(Conflict(..)) = paths disagree ; Some(Defined(v)) = DEFINED(v).
    let raw = state.get(&loc);
    if skip_top_reads && raw.is_none() {
        // (R2) live-in / undefined-self read of an unwritten location: out of
        // scope for phi-free value flow (NOT a clobber — that reads CONFLICT).
        return;
    }
    // Absent (Top) projects to None for both the comparison and the diagnostic.
    let found_sym = raw.cloned();
    let matches = found_sym.as_ref() == Some(expected)
        || (spec_fallback.is_some() && found_sym.as_ref() == spec_fallback);
    if !matches {
        // POST's home for `vreg` does NOT hold the value the SPEC's own value-flow
        // delivers here. The mismatch falls into one of these cases on the phi-free
        // x86 path; ONLY the DEFINITE-vs-DEFINITE one (R3) is relaxed:
        //
        //   * spec CONFLICT, POST DEFINITE — a wrong latch / merge copy that STOPS a
        //     legitimate recurrence (#63/#64). R3 does NOT fire -> REJECTED.
        //   * spec DEFINITE, POST CONFLICT — a forward-merge clobber (#53). R3 does
        //     NOT fire -> REJECTED.
        //   * spec CONFLICT(S), POST CONFLICT(T), S != T — a wrong-second-source
        //     latch (residual (a), now pinned). R3 does NOT fire (neither side is
        //     DEFINITE) -> REJECTED.
        //   * spec DEFINITE(v), POST DEFINITE(w), w != v — the cross-block copy-alias
        //     the id-based model cannot tie back to `vreg` (box_i32). BOTH definite:
        //     R3 fires -> report-only (skip). See the residual (b) note in
        //     [`check_value_flow`] for why this cannot be eliminated soundly.
        let both_definite =
            matches!(found_sym, Some(Sym::Defined(_))) && matches!(expected, Sym::Defined(_));
        if relax_definite_alias && both_definite {
            return;
        }
        // (R4) spurious identity-recurrence conflict: POST holds a single
        // `Defined(w)` while the sparse spec walk synthesized `Conflict(S)` for a
        // loop-carried value threaded through a PURE COPY CYCLE, where `w` and every
        // source in `S` reach the SAME single copy root. The conflict is illusory
        // (all name one architectural value); POST is correct. A real recurrence
        // (non-copy update) has distinct roots and does NOT collapse — still fails
        // closed. See [`CopyEquiv`]. Gated to the phi-free relaxation set.
        if relax_definite_alias
            && let (Some(ce), Sym::Conflict(cset), Some(Sym::Defined(w))) =
                (copy_equiv, expected, found_sym.as_ref())
            && ce.is_spurious_copy_conflict(*w, cset)
        {
            return;
        }
        // (R5) copy-intermediate root-closure reconciliation. POST's home for `v`
        // and the SPEC's own value-flow for `v` denote the SAME set of
        // architectural value SOURCES (the union of non-copy [`CopyEquiv`] roots),
        // but name it with a DIFFERENT set of copy-intermediate ids. This is the
        // MIRROR/EXTENSION of R4 for the CONFLICT-vs-CONFLICT (and
        // CONFLICT-vs-DEFINITE) shapes: the sparse spec walk
        // ([`compute_pre_spec_flow`]) reintroduces an intermediate copy-dest id `c`
        // (dropped to Top by the persisted-exit retain, then defaulted back to its
        // raw id via `unwrap_or(Defined(src.id))`) whose ROOT is already among the
        // POST location's roots, while the POST location — fed through the coalesced
        // spill home the copy chain lands in — carries the resolved roots directly.
        // Example (`LineProgramHeader::parse`, gimli, AArch64 O0/O1): a `0/1`
        // predicate value spilled to a shared slot reads
        // `found = Conflict({229, 2667, 3276})` while the spec expects
        // `Conflict({229, 2667, 3276, 3535})` — `3535` is a copy of the same merge
        // (`reach(3535) ⊆ {229, 2667, 3276}`), so both name value sources
        // `{229, 2667, 3276}`.
        //
        // SOUNDNESS. A copy provably cannot change a value (the R4 lemma), so equal
        // root closures ⇒ the two symbols denote the same architectural value at
        // every point. A GENUINE clobber changes the ROOT set: a forward-merge
        // clobber (#53) or an alien reuse writes a value whose root is NOT in the
        // spec's roots (`roots(found) ⊋ roots(expected)`); a recurrence-stopping /
        // wrong-latch copy (#63/#64) drops a DISTINCT non-copy root the spec
        // requires (`roots(found) ⊊ roots(expected)`). Both leave the closures
        // UNEQUAL, so R5 stays fail-closed — see the adversarial tests
        // `r5_*_rejected`. Interference (b) independently proves the roots are not
        // simultaneously live in the shared home, so per-path the use reads its own
        // live range's value (the conflict is a flow-merge artifact of slot
        // sharing, not a live overlap). Gated to the phi-free relaxation set
        // (`copy_equiv` is `Some` there), exactly like R2/R3/R4.
        if let Some(ce) = copy_equiv
            && let Some(fs) = found_sym.as_ref()
            && ce.root_closure(fs) == ce.root_closure(expected)
        {
            return;
        }
        report.errors.push(ValidationError::ValueFlowMismatch {
            block: block_id,
            inst: inst_id,
            vreg: spec_vreg,
            loc,
            found: found_sym.and_then(|s| s.to_sym_val()),
        });
    }
}

/// Block-local value-numbering transfer: mirror an instruction's DEFS into the
/// `vreg_val` map (the symbolic value each vreg is currently defined to equal).
///
/// * A non-phi value-defining copy `dst <- src` aliases `dst` to `src`'s current
///   expected value (`vreg_val[src]`, defaulting to `Defined(src.id)`).
/// * A spill-load `dst <- slot` reloads the spilled value; we conservatively give
///   `dst` its own id (its uses are skipped as reload temporaries anyway).
/// * Any other def (including a two-address op that redefines a copy-aliased
///   vreg) makes the def a fresh value: `vreg_val[def] = Defined(def.id)`.
///
/// `spec` is the ORIGINAL instruction for surviving original insts: the value
/// numbering is kept in the SPEC namespace (original ids), matching the expected
/// lookup at uses; inserted insts fall back to their post operands.
fn update_vreg_val(
    inst: &RegAllocInst,
    spec: Option<&RegAllocInst>,
    vreg_val: &mut BTreeMap<VReg, Sym>,
) {
    let view = spec.unwrap_or(inst);
    let opcode = inst.opcode;
    if (opcode == PSEUDO_COPY || opcode == IR_COPY_OPCODE)
        && let (Some(dst), Some(src)) = (first_vreg(&view.defs), first_vreg(&view.uses))
    {
        let src_val = vreg_val.get(&src).cloned().unwrap_or(Sym::Defined(src.id));
        vreg_val.insert(dst, src_val);
        return;
    }
    // A copy whose source is a PReg (e.g. an argument load `v <- RDI`) defines
    // `v` as a fresh value — fall through to the generic def handling.
    for def in view.vreg_defs() {
        vreg_val.insert(def, Sym::Defined(def.id));
    }
}

/// Apply one post-alloc instruction's effect to the symbolic location file.
///
/// * A copy (`PSEUDO_COPY` / `IR_COPY_OPCODE`) and a spill-load
///   (`PSEUDO_SPILL_LOAD`) PROPAGATE the source location's symbolic value into
///   the destination location. This includes phi-realizing copies: a copy
///   `dest <- src` simply propagates `src`'s symbolic value, so a copy reading
///   the wrong predecessor's source is visible as the wrong id in `dest`'s
///   location on that edge (caught by the per-edge phi-transfer check). The
///   phi-result identity (`dest.id`) is re-established separately at the join
///   block's entry once every incoming edge is confirmed correct.
/// * A spill-store (`PSEUDO_SPILL_STORE`) propagates the source vreg's location
///   value into its slot.
/// * Any other def OVERWRITES its destination location with a fresh symbolic
///   value naming that def's SPEC vreg (`spec` = the surviving original
///   instruction with unrewritten operands; the write TARGET is the post
///   operand's location — machine truth — while the NAME is the original SSA
///   id, which is what lets a wrong coalesce surface as a value-flow mismatch).
/// * Call clobbers (implicit_defs) invalidate caller-saved physical locations.
fn apply_inst(
    inst: &RegAllocInst,
    spec: Option<&RegAllocInst>,
    locations: &BTreeMap<VReg, Location>,
    state: &mut LocState,
) {
    let opcode = inst.opcode;

    // Helper: write `val` (a full lattice element, `None` = Top) into `loc`.
    // Top is represented by ABSENCE, so writing Top removes the key.
    fn write(state: &mut LocState, loc: Location, val: Option<Sym>) {
        match val {
            Some(sym) => {
                state.insert(loc, sym);
            }
            None => {
                state.remove(&loc);
            }
        }
    }

    if opcode == PSEUDO_COPY || opcode == IR_COPY_OPCODE {
        if let (Some(dst), Some(src)) = (first_vreg(&inst.defs), first_vreg(&inst.uses)) {
            // Propagate the source location's FULL lattice element (Defined,
            // Conflict-with-set, or Top), so a copy of a CONFLICT carries the
            // conflicting source SET forward (residual (a)). This models the
            // ordinary move / coalescing copy AND the phi-realizing copy alike:
            // there is no per-dest "acceptable union" that could let a wrong-edge
            // source slip through, and a wrong-second-source latch propagates a
            // conflict with the WRONG set, caught at the use.
            let src_val = locations.get(&src).and_then(|loc| state.get(loc).cloned());
            let Some(&dst_loc) = locations.get(&dst) else {
                return;
            };
            write(state, dst_loc, src_val);
            return;
        }
    } else if opcode == PSEUDO_SPILL_LOAD {
        // defs = [vreg], uses = [StackSlot]. The slot's value flows into the
        // vreg's *register* location. The spilled vreg's authoritative home is
        // the slot, but a reload may target a register location; honor the
        // operand's destination location.
        if let (Some(dst), Some(slot)) = (first_vreg(&inst.defs), first_slot(&inst.uses)) {
            let val = state.get(&Location::Slot(slot)).cloned();
            if let Some(&dst_loc) = locations.get(&dst) {
                write(state, dst_loc, val);
            }
            // Also keep the slot coherent (idempotent).
            return;
        }
    } else if opcode == PSEUDO_SPILL_STORE {
        // uses = [vreg, StackSlot]; vreg's current value flows into the slot.
        if let (Some(src), Some(slot)) = (first_vreg(&inst.uses), first_slot(&inst.uses)) {
            let val = locations.get(&src).and_then(|loc| state.get(loc).cloned());
            write(state, Location::Slot(slot), val);
            return;
        }
    }

    // Generic instruction: caller-clobbers first, then fresh defs.
    //
    // A call clobber invalidates a caller-saved register: model it as a fresh
    // unnamed value. Use a singleton `Conflict` over a reserved sentinel id so it
    // is DISTINCT from any real SSA value AND from a Top read — a subsequent use
    // reading a clobbered location compares unequal to its `Defined(v.id)` /
    // `Conflict(set)` expectation and fails closed (it is not Top, so R2 does not
    // skip it). `u32::MAX` is the sentinel (the allocator never mints it as a real
    // vreg id; an extra guard below asserts that).
    for &preg in &inst.implicit_defs {
        state.insert(
            Location::Reg(preg),
            Sym::Conflict(BTreeSet::from([CLOBBER_SENTINEL])),
        );
    }
    for (idx, def_op) in inst.defs.iter().enumerate() {
        let Some(def) = def_op.as_vreg() else {
            continue;
        };
        debug_assert!(
            def.id != CLOBBER_SENTINEL,
            "vreg id collides with clobber sentinel"
        );
        // Value NAME: the positionally-paired SPEC def (original id); location:
        // the POST def operand's home. Defensive default: the post vreg itself.
        let name = spec
            .and_then(|s| s.defs.get(idx))
            .and_then(|sop| sop.as_vreg())
            .unwrap_or(def);
        if let Some(&loc) = locations.get(&def) {
            state.insert(loc, Sym::Defined(name.id));
        }
    }
}

/// Reserved sentinel id for a call-clobbered (caller-saved) physical location.
/// Distinct from any real SSA vreg id, so a use reading a clobber fails closed.
const CLOBBER_SENTINEL: u32 = u32::MAX;

/// Meet (intersection-of-agreement) of all predecessor exit states.
///
/// A location keeps a value only if EVERY predecessor that has an exit state
/// exits with that same value in it; disagreement collapses it to None. A
/// predecessor with NO exit state yet is the optimistic-unknown (`Top`) lattice
/// element and contributes nothing to the meet — it neither asserts nor refutes
/// any value. Under the fixpoint driver ([`compute_exit_states_fixpoint`]) this
/// is sound: on the seeding pass a not-yet-computed back-edge predecessor is
/// `Top`, and successive passes lower it monotonically to its true exit state,
/// at which point it DOES participate in the meet. The result is the greatest
/// fixpoint, anchored by each block's non-back-edge predecessors, so it never
/// invents a value that fails to reach the block on some incoming edge. The
/// entry block (no preds) starts empty.
fn meet_pred_states(
    block: &crate::machine_types::RegAllocBlock,
    exit_states: &BTreeMap<BlockId, LocState>,
) -> LocState {
    if block.preds.is_empty() {
        return LocState::new();
    }

    // Collect predecessor states that have been computed at least once. A
    // predecessor with no state is Top (unknown) and is skipped.
    let mut known: Vec<&LocState> = Vec::new();
    for pred in &block.preds {
        if let Some(s) = exit_states.get(pred) {
            known.push(s);
        }
    }

    if known.is_empty() {
        return LocState::new();
    }

    // Start from the first known predecessor, then intersect agreement.
    let mut result: LocState = known[0].clone();
    for s in &known[1..] {
        result = intersect_agreement(&result, s);
    }
    result
}

/// Compute a block's symbolic entry state: the meet of predecessor exit states,
/// with loop-header phi-result identities re-established across every (now
/// available) incoming edge.
///
/// This is shared by the fixpoint iteration and the final error-recording pass
/// so both see IDENTICAL entry states.
///
/// ## Phi-result establishment (property c, loop-aware)
///
/// A phi `dest = [.. src_i from pred_i ..]` creates a NEW SSA value at the join.
/// Each pred's realizing copy is modeled as ordinary propagation, so pred_i exits
/// with `src_i.id` (not a shared value) in `dest`'s location — across distinct
/// edges the meet therefore collapses `dest`'s location to Conflict. We re-derive
/// `dest.id` here, but ONLY if EVERY incoming edge that currently has an exit
/// state delivered the EXACT expected source (`src_i.id`) into `dest`'s location
/// on THAT edge, and at least one edge was confirmed. Modeling the back-edge
/// through the fixpoint means a CORRECT loop-carried phi (the latch threads the
/// updated source) is confirmed once the latch's exit state has been computed, so
/// in-loop uses of `dest` validate (closing the loop-header false positive). A
/// WRONG loop-carried copy (the latch threads the wrong source) leaves `dest`'s
/// location holding the wrong id on the latch edge: the establishment refuses to
/// assert `dest.id` and the per-edge phi-transfer check rejects it outright.
///
/// When an edge is unconfirmed — because it delivered a wrong id, OR because its
/// (back-edge) predecessor has no exit state yet in this fixpoint iteration — the
/// `dest` location is left at lattice `Top` (REMOVED from the state), NOT written
/// to the absorbing Conflict bottom. Writing bottom on an early pass (before the
/// back-edge is seeded) would be sticky: the meet `meet(Defined, Conflict) =
/// Conflict` could never recover once a later pass establishes the true value,
/// re-introducing the loop-header false positive. Leaving it `Top` keeps the
/// per-location lattice descending monotonically (`Top -> Defined(dest.id)`) and
/// still fails any in-loop use closed (an absent location reads as None at a
/// use), so it is conservative — never a false Ok.
fn block_entry_state(
    block: &crate::machine_types::RegAllocBlock,
    exit_states: &BTreeMap<BlockId, LocState>,
    locations: &BTreeMap<VReg, Location>,
    phi_specs: &PhiSpecs,
    block_id: BlockId,
    spec_exit: Option<&BTreeMap<BlockId, Rc<PreState>>>,
) -> LocState {
    let mut state = meet_pred_states(block, exit_states);

    if let Some(specs) = phi_specs.get(&block_id) {
        for (dest, sources) in specs {
            let Some(&dest_loc) = locations.get(dest) else {
                continue; // unmapped dest is reported by the per-edge check
            };
            let mut all_ok = !sources.is_empty();
            let mut saw_confirmed = false;
            for edge in sources {
                let Some(exit) = exit_states.get(&edge.realizing_pred) else {
                    // Predecessor not yet computed in the fixpoint: cannot
                    // confirm this edge.
                    all_ok = false;
                    continue;
                };
                saw_confirmed = true;
                // The edge must deliver the SPEC value of `src` on this edge
                // (exactly `Defined(src.id)` unless original copies were
                // coalesced away — same criterion as the per-edge transfer
                // check in `check_value_flow_final`).
                let expected = phi_edge_expected(spec_exit, edge.spec_pred, edge.src);
                let ok = exit.get(&dest_loc) == Some(&expected);
                if !ok {
                    all_ok = false;
                }
            }
            if all_ok && saw_confirmed {
                // Every incoming edge delivered its exact source: the phi result
                // genuinely holds `dest.id` at the join entry.
                state.insert(dest_loc, Sym::Defined(dest.id));
            } else {
                // Unconfirmed (an edge delivered the wrong id, OR a back-edge
                // predecessor has no exit state yet in this fixpoint iteration).
                // Leave the dest location as the optimistic-unknown lattice top
                // (ABSENT) rather than the conflicting-bottom:
                //
                //   * Soundness — an absent (Top) location at an original use
                //     compares unequal to the expected `Defined(dest.id)` (and is
                //     only R2-skipped when `dest.id` is genuinely live-in/undefined),
                //     so an unconfirmed phi still fails its in-loop uses CLOSED,
                //     and the per-edge phi-transfer check independently rejects a
                //     genuinely wrong loop-carried copy.
                //   * Monotonicity — writing the absorbing bottom here on an early
                //     fixpoint pass (before the back-edge predecessor is seeded)
                //     would be STICKY: the meet `meet(Some(v), bottom) = bottom`
                //     could never recover once a later pass establishes the true
                //     value, re-introducing the very loop-header false positive
                //     this fix removes. Leaving it top lets the GFP descend
                //     top -> `Some(dest.id)` exactly once the back-edge is known.
                state.remove(&dest_loc);
            }
        }
    }

    state
}

/// Iterate the forward value-flow transfer to a fixpoint, returning each block's
/// converged EXIT state.
///
/// The per-location lattice descends `Top` (absent from the map) -> `Some(v)` ->
/// `None` (conflicting). [`block_entry_state`] (meet + phi establishment) and
/// [`apply_inst`] (the transfer) are monotone in this lattice, so repeatedly
/// recomputing every block's exit state converges. A back-edge predecessor —
/// whose exit state is missing on the first pass — is `Top` then, contributes
/// nothing, and is lowered to its true state on the next pass, so a loop
/// header's entry stabilizes to the meet-over-predecessors that INCLUDES the
/// back-edge.
///
/// SEEDING ORDER MATTERS (x86 read_encoded_offset false positive, 2026-07-17):
/// the walk MUST visit blocks in CFG reverse post-order
/// ([`cfg_reverse_post_order`]), NOT raw `block_order`. `block_order` is a
/// LAYOUT order and may place a block after its successors (the x86-64 switch
/// lowering appends its range-dispatch blocks at the end of the function while
/// their successor arms sit earlier). Under such an order the first pass reads
/// a forward-edge predecessor that has not been visited yet, treats it as
/// `Top`, and the block computes a transiently-wrong exit. The conflict point
/// of the lattice is ABSORBING inside a cycle — once a loop's blocks meet a
/// stale transient against the refreshed value, the header descends to
/// conflict and the backedge re-delivers it forever — so a transient caused
/// purely by visit order becomes a PERMANENT spurious conflict, i.e. the
/// converged point depends on the order. RPO guarantees every non-back-edge
/// predecessor is visited before its successor on every pass, so first-pass
/// `Top` reads happen only across genuine back edges (the optimistic seed the
/// loop-header design above relies on), and the walk converges to the intended
/// anchored fixpoint.
///
/// Termination: each location's lattice value can only descend (Top -> Some ->
/// None), and there are finitely many (block, location) pairs, so the total
/// information is monotone non-increasing and bounded. The loop stops as soon as
/// a full pass leaves every exit state unchanged. A hard iteration cap (a
/// multiple of the block count) is an extra safety net: if it is ever hit, the
/// states are returned as-is — any block whose value-flow has not yet stabilized
/// will simply read more conservatively at the use sites (fail closed), never a
/// false Ok.
/// CFG reverse post-order over `func`'s successor edges, starting at
/// `entry_block`, followed by any blocks unreachable from the entry in their
/// `block_order` position (so the walk's block COVERAGE is identical to the
/// historical `block_order` iteration — only the visit ORDER of the reachable
/// subgraph changes).
///
/// Both forward value-flow fixpoints in this module seed from this order. RPO
/// guarantees that on every pass each block's non-back-edge predecessors have
/// already been visited, so a first-pass `Top` (absent) predecessor read
/// happens only across a genuine back edge — the optimistic seed the loop
/// convergence argument relies on. Raw `block_order` is a LAYOUT order and
/// does not provide this (x86-64 switch lowering appends dispatch blocks
/// after their successor arms), and because the lattices' conflict points are
/// absorbing inside cycles, a wrong seeding order changes the CONVERGED
/// state, not just the pass count.
fn cfg_reverse_post_order(func: &MachFunction) -> Vec<BlockId> {
    let n = func.blocks.len();
    let mut visited = vec![false; n];
    let mut postorder: Vec<BlockId> = Vec::with_capacity(n);
    let entry = func.entry_block;
    if (entry.0 as usize) < n {
        // Iterative DFS: (block, next successor index to explore).
        let mut stack: Vec<(BlockId, usize)> = vec![(entry, 0)];
        visited[entry.0 as usize] = true;
        while let Some((block, succ_idx)) = stack.pop() {
            let succs = &func.blocks[block.0 as usize].succs;
            if succ_idx < succs.len() {
                stack.push((block, succ_idx + 1));
                let succ = succs[succ_idx];
                if (succ.0 as usize) < n && !visited[succ.0 as usize] {
                    visited[succ.0 as usize] = true;
                    stack.push((succ, 0));
                }
            } else {
                postorder.push(block);
            }
        }
    }
    postorder.reverse();
    let mut order = postorder;
    // Blocks unreachable from the entry (or with out-of-range ids, which the
    // walk loops skip anyway) keep their historical relative placement.
    for &block in &func.block_order {
        if (block.0 as usize) >= n {
            order.push(block);
            continue;
        }
        if !visited[block.0 as usize] {
            visited[block.0 as usize] = true;
            order.push(block);
        }
    }
    order
}

fn compute_exit_states_fixpoint(
    pre: &MachFunction,
    post: &MachFunction,
    locations: &BTreeMap<VReg, Location>,
    phi_specs: &PhiSpecs,
    spec_exit: Option<&BTreeMap<BlockId, Rc<PreState>>>,
) -> BTreeMap<BlockId, LocState> {
    let original_inst_count = pre.insts.len() as u32;
    let mut exit_states: BTreeMap<BlockId, LocState> = BTreeMap::new();

    // SPARSE persistence (pure performance; observation-equivalent — see the
    // proof on [`post_live_out_locations`]). On TY's fused-BFS parent loop
    // (~7,300 blocks, thousands of spill slots at O0) the dense exit states
    // accumulated every written location in every block, making each pass
    // O(blocks x locations) in BTreeMap clones. Only locations whose persisted
    // exit value can actually be READ downstream — at some block entry before
    // that block rewrites them, or directly at a predecessor exit by the phi
    // machinery — need to survive into `exit_states`, and only at the blocks
    // they are live-out of.
    let live_out = post_live_out_locations(post, locations, phi_specs);

    // Bound the number of passes. The dataflow needs at most (loop nesting depth
    // + 1) passes to stabilize; a multiple of the block count is a generous,
    // always-sufficient cap that also guarantees termination on any input.
    let max_passes = post.block_order.len().saturating_mul(2).saturating_add(2);

    // CFG reverse post-order, NOT layout order — see the doc comment above for
    // why the converged point itself depends on the seeding order.
    let walk_order = cfg_reverse_post_order(post);

    for _ in 0..max_passes {
        let mut changed = false;
        for &block_id in &walk_order {
            let Some(block) = post.blocks.get(block_id.0 as usize) else {
                continue;
            };

            let mut state = block_entry_state(
                block,
                &exit_states,
                locations,
                phi_specs,
                block_id,
                spec_exit,
            );

            for &inst_id in &block.insts {
                let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                    continue;
                };
                // The fixpoint only computes states; it records no use errors
                // (those are recorded once, against the converged states, by the
                // final pass in `check_value_flow`).
                let spec = spec_inst(pre, inst_id, original_inst_count);
                apply_inst(inst, spec, locations, &mut state);
            }

            // Persist only the keys live-out of THIS block (the in-block
            // working state above keeps EVERY key, so in-block reads after
            // in-block writes are untouched by this restriction).
            match live_out.get(&block_id) {
                Some(live) => state.retain(|loc, _| live.contains(loc)),
                None => state.clear(),
            }
            match exit_states.get(&block_id) {
                Some(prev) if *prev == state => {}
                _ => {
                    exit_states.insert(block_id, state);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    exit_states
}

/// Per-block sets of locations LIVE-OUT in the validator's read/write model:
/// the locations whose persisted exit-state value at that block can influence
/// a recorded error. Computed by a standard backward may-liveness over
/// per-block (GEN = read-before-first-write, KILL = written-anywhere) summaries
/// where:
///
///  * READS are over-approximated as every vreg use's mapped location (a
///    superset of the reads in [`apply_inst`] — copy / spill-store sources —
///    and the [`check_original_use`] lookup) plus every spill-load's source
///    slot, plus — modeled as an entry read of the PHI BLOCK — every phi
///    destination's location, which the phi-establishment in
///    [`block_entry_state`] and the per-edge phi-transfer check (property c)
///    read DIRECTLY from each predecessor's exit state;
///  * WRITES mirror [`apply_inst`]'s write targets exactly (a key removal — a
///    Top write — is also a write). Over-approximating reads or
///    under-approximating writes only ever KEEPS more keys (conservative).
///
/// EXACTNESS (why restricting block B's persisted exit state to live-out(B) is
/// observation-equivalent to the historical dense fixpoint): a dropped key is
/// Top at every successor's entry meet ([`intersect_agreement`]: `meet(Top, x)
/// = x` — an absent key contributes nothing), so its absence can only change
/// behavior at a READ of the propagated value. L ∉ live-out(B) means NO path
/// from B reads L before writing it (per-edge: L ∉ live-in(S) for every
/// successor S, where live-in(S) = GEN(S) ∪ (live-out(S) − KILL(S))), and the
/// phi machinery's direct exit reads are covered because a phi dest's location
/// is in GEN of the phi block, hence in live-out of EVERY predecessor the
/// establishment / property-(c) check consults. The persisted keys form a
/// closed subsystem — a live-out key's next-pass exit value depends only on
/// in-block writes whose source reads are either in-block values (identical in
/// both walks) or entry reads of GEN-keys (live-out at every predecessor,
/// hence persisted) — so the per-pass trajectory restricted to persisted keys
/// is identical to the dense walk's, convergence happens at the same pass (or
/// earlier, with identical restricted values thereafter), and the final
/// recording pass reads identical values at every read site.
fn post_live_out_locations(
    post: &MachFunction,
    locations: &BTreeMap<VReg, Location>,
    phi_specs: &PhiSpecs,
) -> BTreeMap<BlockId, BTreeSet<Location>> {
    // Per-block GEN (read before first write) / KILL (written) summaries.
    let mut gen_sets: BTreeMap<BlockId, BTreeSet<Location>> = BTreeMap::new();
    let mut kill_sets: BTreeMap<BlockId, BTreeSet<Location>> = BTreeMap::new();

    for &block_id in &post.block_order {
        let Some(block) = post.blocks.get(block_id.0 as usize) else {
            continue;
        };
        let mut gen_set: BTreeSet<Location> = BTreeSet::new();
        let mut written: BTreeSet<Location> = BTreeSet::new();
        for &inst_id in &block.insts {
            let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                continue;
            };

            // READS first (matching the walk: the use-check and the transfer's
            // source reads happen before the transfer's writes).
            for v in inst.vreg_uses() {
                if let Some(&loc) = locations.get(&v)
                    && !written.contains(&loc)
                {
                    gen_set.insert(loc);
                }
            }
            if inst.opcode == PSEUDO_SPILL_LOAD
                && let Some(slot) = first_slot(&inst.uses)
            {
                let loc = Location::Slot(slot);
                if !written.contains(&loc) {
                    gen_set.insert(loc);
                }
            }

            // WRITES: mirror `apply_inst`'s write targets.
            let opcode = inst.opcode;
            if opcode == PSEUDO_COPY || opcode == IR_COPY_OPCODE {
                if let (Some(dst), Some(_src)) = (first_vreg(&inst.defs), first_vreg(&inst.uses)) {
                    if let Some(&dst_loc) = locations.get(&dst) {
                        written.insert(dst_loc);
                    }
                    continue;
                }
                // PReg/imm-source copy: falls through to the generic def
                // handling, exactly like `apply_inst`.
            } else if opcode == PSEUDO_SPILL_LOAD {
                if let (Some(dst), Some(_slot)) = (first_vreg(&inst.defs), first_slot(&inst.uses)) {
                    if let Some(&dst_loc) = locations.get(&dst) {
                        written.insert(dst_loc);
                    }
                    continue;
                }
            } else if opcode == PSEUDO_SPILL_STORE
                && let (Some(_src), Some(slot)) = (first_vreg(&inst.uses), first_slot(&inst.uses))
            {
                written.insert(Location::Slot(slot));
                continue;
            }
            for &preg in &inst.implicit_defs {
                written.insert(Location::Reg(preg));
            }
            for def in inst.vreg_defs() {
                if let Some(&loc) = locations.get(&def) {
                    written.insert(loc);
                }
            }
        }
        gen_sets.insert(block_id, gen_set);
        kill_sets.insert(block_id, written);
    }

    // Phi destination locations are read directly from PREDECESSOR exit
    // states; model each as an entry read (GEN) of the phi block so liveness
    // carries it into live-out of every consulted predecessor. (GEN-only is
    // conservative: the establishment also writes the location at entry, but
    // ignoring that write only keeps the key live longer.)
    for (phi_block, specs) in phi_specs {
        let gen_set = gen_sets.entry(*phi_block).or_default();
        for (dest, _sources) in specs {
            if let Some(&loc) = locations.get(dest) {
                gen_set.insert(loc);
            }
        }
    }

    // Backward may-liveness to a fixpoint:
    //   live-in(B)  = GEN(B) ∪ (live-out(B) − KILL(B))
    //   live-out(B) = ∪ over successors S of live-in(S)
    // Monotone (sets only grow) over a finite universe; the pass cap matches
    // the forward fixpoints' generous safety net.
    let mut live_in: BTreeMap<BlockId, BTreeSet<Location>> = BTreeMap::new();
    let mut live_out: BTreeMap<BlockId, BTreeSet<Location>> = BTreeMap::new();
    for &block_id in &post.block_order {
        live_in.insert(
            block_id,
            gen_sets.get(&block_id).cloned().unwrap_or_default(),
        );
        live_out.insert(block_id, BTreeSet::new());
    }
    let max_passes = post.block_order.len().saturating_mul(2).saturating_add(2);
    for _ in 0..max_passes {
        let mut changed = false;
        for &block_id in post.block_order.iter().rev() {
            let Some(block) = post.blocks.get(block_id.0 as usize) else {
                continue;
            };
            let mut out: BTreeSet<Location> = BTreeSet::new();
            for succ in &block.succs {
                if let Some(succ_in) = live_in.get(succ) {
                    out.extend(succ_in.iter().copied());
                }
            }
            let kill = kill_sets.get(&block_id);
            let mut inn = gen_sets.get(&block_id).cloned().unwrap_or_default();
            for &loc in &out {
                if kill.map(|k| k.contains(&loc)) != Some(true) {
                    inn.insert(loc);
                }
            }
            if live_out.get(&block_id) != Some(&out) {
                live_out.insert(block_id, out);
                changed = true;
            }
            if live_in.get(&block_id) != Some(&inn) {
                live_in.insert(block_id, inn);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    live_out
}

/// Pointwise meet (greatest-lower-bound) of two symbolic location files.
///
/// The per-location lattice, ordered by information, is:
///
/// ```text
///   Top  (absent from the map)        = "no path has written this location yet"
///    │
///   Defined(v)                        = "this location holds SSA value v"
///    │
///   Conflict({a, b, ..})              = "paths disagree; SET of reaching ids"  (bottom)
/// ```
///
/// and the meet is (see [`Sym::meet`] for the present/present cases):
///
/// * `meet(Top, x)            = x`            — an unwritten predecessor neither
///   asserts nor refutes a value, so it contributes nothing. This is the key to
///   the loop fixpoint: a back-edge predecessor that has not yet been analyzed
///   (Top) must NOT collapse a location the other predecessors agree on, or a
///   loop header's value would be lost on every iteration (the residual bug).
///   It is sound because at any ORIGINAL use the used vreg is live-in, hence
///   defined on every predecessor path, so its location is never Top at a use.
/// * `meet(Defined(a), Defined(a)) = Defined(a)` — agreement is preserved.
/// * `meet(Defined(a), Defined(b)) = Conflict({a, b})` for `a != b` — a real merge
///   disagreement (e.g. the #64 join clobber) collapses to bottom, CARRYING the
///   disagreeing source set so two distinct conflicts stay distinct (residual (a)),
///   and fails the downstream use closed.
/// * `meet(Conflict(S), x)    = Conflict(S ∪ ids(x))` — bottom is absorbing but the
///   set grows monotonically, preserving termination over the finite id universe.
fn intersect_agreement(a: &LocState, b: &LocState) -> LocState {
    let mut out = LocState::new();
    // Iterate the union of keys; a key absent in one side is Top there.
    for (loc, va) in a {
        match b.get(loc) {
            // Present in both: information-meet of the two lattice elements.
            Some(vb) => {
                out.insert(*loc, va.meet(vb));
            }
            // Top in `b`: meet(va, Top) = va.
            None => {
                out.insert(*loc, va.clone());
            }
        }
    }
    // Locations present only in `b` are Top in `a`: meet(Top, vb) = vb.
    for (loc, vb) in b {
        out.entry(*loc).or_insert_with(|| vb.clone());
    }
    out
}

/// Whether `pre` contains any phi instruction. The value-flow property (a) is an
/// SSA-value-flow check that needs phis to anchor join / loop recurrences; a
/// phi-free input (the x86-64 ISel path lowers phis to copies before regalloc)
/// triggers the documented relaxations — see the SCOPE note in
/// [`check_value_flow`].
fn pre_has_phis(pre: &MachFunction) -> bool {
    pre.insts.iter().any(|inst| inst.flags.is_phi())
}

// ---------------------------------------------------------------------------
// PRE-spec value-flow (the SSA-value-identity reaching-value of the SPEC).
// ---------------------------------------------------------------------------

/// The symbolic vreg-keyed value file at one program point of the PRE spec.
///
/// Unlike [`LocState`] (keyed on physical [`Location`]s of the allocated POST
/// program), the PRE walk keys on the VReg itself: in the pre-allocation spec
/// every vreg IS its own home, so `pre_state[v]` is the [`Sym`] the SPEC's
/// value-flow currently assigns to `v` (`Defined(w)` = "v holds w's value here",
/// `Conflict(set)` = paths disagree over `set`, absent = TOP).
type PreState = BTreeMap<VReg, Sym>;

/// The expected (spec) symbolic value at each ORIGINAL use, keyed by the use's
/// (instruction, vreg). This is the value-flow IDENTITY the POST allocation must
/// reproduce in that vreg's assigned home at that use (property a). Carries the
/// full [`Sym`] so a spec conflict's source SET is compared against POST's
/// (residual (a)).
type PreExpected = BTreeMap<(InstId, VReg), Sym>;

/// Apply one PRE instruction's effect to the vreg-keyed symbolic value file.
///
/// Mirror of [`apply_inst`] but on the PRE namespace (vreg = its own home):
///
/// * A copy `dst <- src` (`PSEUDO_COPY` / `IR_COPY_OPCODE`) PROPAGATES `src`'s
///   current symbolic value into `dst` — exactly as the realizing / two-address
///   / latch copies in the phi-free x86 spec do. This is what makes a
///   loop-carried `v_iv` legitimately hold `v_next`'s id after the latch copy,
///   so the loop-header meet of the preheader (`v_init.id`) and latch
///   (`v_next.id`) values collapses to CONFLICT in the SPEC — which the POST
///   walk must REPRODUCE (a correct allocation does; a wrong latch copy that
///   re-threads the init makes POST hold a DEFINITE id and mismatch).
/// * Any other def makes `dst` a fresh value naming itself (`Defined(dst.id)`).
///
/// Phi instructions are handled by the caller (their dest is established at the
/// join via [`pre_block_entry_state`]); a phi here is skipped.
/// `tracked` is the SPARSE key domain of the walk (see [`pre_tracked_vregs`]):
/// every vreg whose symbolic value can ever deviate from the trivial
/// `Defined(own id)`. Untracked defs are NOT inserted — every read of an
/// untracked vreg (the copy-source read below, and the use-recording in
/// [`compute_pre_expected`]) defaults an absent key to `Defined(v.id)`, which
/// is exactly the value the dense walk would deliver (proof at
/// [`pre_tracked_vregs`]), so dropping those inserts is observation-equivalent.
fn apply_inst_pre(inst: &RegAllocInst, state: &mut PreState, tracked: &BTreeSet<VReg>) {
    if inst.flags.is_phi() {
        return;
    }
    let opcode = inst.opcode;
    if (opcode == PSEUDO_COPY || opcode == IR_COPY_OPCODE)
        && let (Some(dst), Some(src)) = (first_vreg(&inst.defs), first_vreg(&inst.uses))
    {
        // `dst` is in `tracked` by construction; keep the membership test
        // for local robustness.
        if tracked.contains(&dst) {
            let src_val = state.get(&src).cloned().unwrap_or(Sym::Defined(src.id));
            state.insert(dst, src_val);
        }
        return;
    }
    // A copy whose source is a PReg/imm defines `dst` as a fresh value: fall
    // through to the generic def handling.
    for def in inst.vreg_defs() {
        if tracked.contains(&def) {
            state.insert(def, Sym::Defined(def.id));
        }
    }
}

/// Meet the PRE exit states of a block's predecessors (vreg-keyed analogue of
/// [`meet_pred_states`] / [`intersect_agreement`]). A vreg keeps a value only if
/// every KNOWN predecessor agrees; disagreement is `Conflict(set)` (carrying the
/// reaching ids); a not-yet-computed predecessor is TOP and contributes nothing.
// Reference-oracle meet (the historical clone-and-fold). The shipped
// `compute_pre_expected` now takes the ref-counted shared path
// ([`pre_entry_shared`]); this exact semantics is retained as the INDEPENDENT
// dense reference driven by the decision-identity oracle, so it is used only
// under `#[cfg(test)]`.
#[cfg_attr(not(test), allow(dead_code))]
fn pre_meet_preds(
    block: &crate::machine_types::RegAllocBlock,
    exit_states: &BTreeMap<BlockId, PreState>,
) -> PreState {
    let mut known: Vec<&PreState> = Vec::new();
    for pred in &block.preds {
        if let Some(s) = exit_states.get(pred) {
            known.push(s);
        }
    }
    if known.is_empty() {
        return PreState::new();
    }
    let mut result: PreState = known[0].clone();
    for s in &known[1..] {
        let mut out = PreState::new();
        for (v, va) in &result {
            match s.get(v) {
                Some(vb) => {
                    out.insert(*v, va.meet(vb));
                }
                None => {
                    out.insert(*v, va.clone());
                }
            }
        }
        for (v, vb) in *s {
            out.entry(*v).or_insert_with(|| vb.clone());
        }
        result = out;
    }
    result
}

/// Compute a PRE block's entry state: meet of predecessor exit states, with any
/// PHI dests re-established to their own id (a phi defines a fresh SSA value at
/// the join — the AArch64 spec carries phis; the x86 spec is phi-free so this is
/// a no-op there).
#[cfg_attr(not(test), allow(dead_code))]
fn pre_block_entry_state(
    block: &crate::machine_types::RegAllocBlock,
    exit_states: &BTreeMap<BlockId, PreState>,
    pre: &MachFunction,
    block_id: BlockId,
    tracked: &BTreeSet<VReg>,
) -> PreState {
    let mut state = pre_meet_preds(block, exit_states);
    // Establish phi dests (phi-bearing AArch64 spec): a phi `dest = [..]` is a
    // fresh value at the join, so it holds its own id regardless of the meet.
    // An UNTRACKED phi dest's establishment value is its own id — the default
    // every read of an absent key already supplies — so it needs no insert.
    if let Some(b) = pre.blocks.get(block_id.0 as usize) {
        for &inst_id in &b.insts {
            let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                continue;
            };
            if inst.flags.is_phi() {
                for def in inst.vreg_defs() {
                    if tracked.contains(&def) {
                        state.insert(def, Sym::Defined(def.id));
                    }
                }
            }
        }
    }
    state
}

/// Meet an ordered list of KNOWN predecessor exit states into a fresh owned
/// [`PreState`]. Byte-for-byte the fold performed by [`pre_meet_preds`] (the
/// vreg-keyed reference meet), factored so the shared-state driver
/// ([`pre_entry_shared`]) reuses the EXACT same union-with-pointwise-meet. Only
/// reached with `known.len() >= 2` (the 0/1 cases are handled by sharing).
fn pre_meet_owned(known: &[&PreState]) -> PreState {
    let mut result: PreState = known[0].clone();
    for s in &known[1..] {
        let mut out = PreState::new();
        for (v, va) in &result {
            match s.get(v) {
                Some(vb) => {
                    out.insert(*v, va.meet(vb));
                }
                None => {
                    out.insert(*v, va.clone());
                }
            }
        }
        for (v, vb) in *s {
            out.entry(*v).or_insert_with(|| vb.clone());
        }
        result = out;
    }
    result
}

/// Compute a PRE block's ENTRY value file as a REFERENCE-COUNTED snapshot,
/// sharing the predecessor's exit allocation when the entry equals it — the
/// CT-3 clone elimination.
///
/// Equivalence to [`pre_meet_preds`] (which clones `known[0]` and folds): the
/// CONTENTS returned are identical.
///   * 0 known predecessors → the empty file (== `PreState::new()`).
///   * 1 known predecessor → that predecessor's exit UNCHANGED — so we hand back
///     an `Rc::clone` of its snapshot (O(1)) instead of a deep `clone_subtree`.
///     This is the dominant case (straight-line / single-pred flow), and is where
///     the historical per-block `BTreeMap<VReg,Sym>` clone is eliminated.
///   * >=2 known predecessors (a join) → the pointwise meet, which genuinely
///     > differs from any single predecessor, so it is materialized once
///     > ([`pre_meet_owned`]) and wrapped fresh.
///
/// A not-yet-computed predecessor is lattice-Top and contributes nothing
/// (skipped), exactly as in [`pre_meet_preds`].
fn pre_entry_shared(
    block: &crate::machine_types::RegAllocBlock,
    exit_states: &BTreeMap<BlockId, Rc<PreState>>,
    empty: &Rc<PreState>,
) -> Rc<PreState> {
    let mut known: Vec<&Rc<PreState>> = Vec::new();
    for pred in &block.preds {
        if let Some(s) = exit_states.get(pred) {
            known.push(s);
        }
    }
    match known.as_slice() {
        [] => Rc::clone(empty),
        [one] => Rc::clone(one),
        rest => {
            let refs: Vec<&PreState> = rest.iter().map(|r| r.as_ref()).collect();
            Rc::new(pre_meet_owned(&refs))
        }
    }
}

/// Establish a block's PHI dests in `state` (fresh SSA value at the join): the
/// phi-dest half of [`pre_block_entry_state`]. On the phi-free x86 path (the only
/// caller of [`compute_pre_expected`]) this is a no-op; it is replicated here so
/// the shared-state driver stays a faithful drop-in on a phi-bearing spec.
fn pre_establish_phis(
    pre: &MachFunction,
    block_id: BlockId,
    tracked: &BTreeSet<VReg>,
    state: &mut PreState,
) {
    if let Some(b) = pre.blocks.get(block_id.0 as usize) {
        for &inst_id in &b.insts {
            let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                continue;
            };
            if inst.flags.is_phi() {
                for def in inst.vreg_defs() {
                    if tracked.contains(&def) {
                        state.insert(def, Sym::Defined(def.id));
                    }
                }
            }
        }
    }
}

/// Compute the PRE spec's value-flow to a fixpoint and record, for every
/// ORIGINAL use, the symbolic value the SPEC assigns to the used vreg right
/// BEFORE that use.
///
/// This is the value-flow IDENTITY a correct register allocation must reproduce
/// in each vreg's assigned home (property a, x86 phi-free path). It is the
/// principled, whole-function replacement for the old whole-function
/// `value_flow_report_only` carve-out: instead of turning property (a) OFF
/// for any phi-free looping function, we compute what the SPEC's value-flow
/// delivers at each use (including loop-carried CONFLICTs from a `v_iv <- v_next`
/// latch copy) and require POST to deliver EXACTLY that — fail-closed (with the
/// single narrow report-only carve-out R3 for the DEFINITE-vs-DEFINITE
/// cross-block copy-alias, applied in [`check_original_use`]).
///
/// Termination/monotonicity mirror [`compute_exit_states_fixpoint`]: each
/// vreg's lattice value only descends TOP -> Defined(v) -> Conflict(set), and a
/// Conflict's set only GROWS (a subset relation) over the finite id universe, so
/// over finitely many (block, vreg) pairs iteration converges; a generous pass cap
/// is a safety net.
///
/// Returns both the per-use expected map and the converged per-block EXIT
/// states (used for the generalized per-edge phi obligation when original
/// copies were coalesced away).
struct PreSpecFlow {
    expected: PreExpected,
    exit_states: BTreeMap<BlockId, Rc<PreState>>,
}

/// DIAGNOSTIC (default off, `TCG_TIME_RA=1`): accumulated time in this fixpoint
/// so its share of prepare::regalloc is measured rather than argued.
pub(crate) static PSF_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static PSF_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn psf_timing() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TCG_TIME_RA").is_some())
}

fn compute_pre_spec_flow(pre: &MachFunction) -> PreSpecFlow {
    if psf_timing() {
        let t = std::time::Instant::now();
        let r = compute_pre_spec_flow_inner(pre);
        PSF_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        PSF_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        eprintln!(
            "TCG_TIME_RA psf_cum={}us calls={}",
            PSF_NANOS.load(std::sync::atomic::Ordering::Relaxed) / 1000,
            PSF_CALLS.load(std::sync::atomic::Ordering::Relaxed),
        );
        return r;
    }
    compute_pre_spec_flow_inner(pre)
}

fn compute_pre_spec_flow_inner(pre: &MachFunction) -> PreSpecFlow {
    // SPARSE key domains (a pure-performance restriction of the historical
    // dense walk — observation-equivalent, see the proofs on the two helpers).
    // On TY's fused-BFS parent loop (~7,300 blocks / ~65,000 insts at O0) the
    // dense walk carried every defined vreg (~30,000) in every block's exit
    // state, making each fixpoint pass O(blocks x vregs) in BTreeMap clones —
    // tens of seconds. Only copy destinations can ever carry a non-default
    // value, and each block persists only the keys LIVE-OUT of it.
    //
    // The live-out restriction is PER-BLOCK on purpose. The previous retain
    // pruned against a single GLOBAL entry-observable set, so a tracked vreg
    // read anywhere stayed in EVERY exit state from its def to the end of the
    // function: on many-block functions with short live ranges (the many_fns
    // scaling shape) exit-state width ramped to Theta(blocks) and each
    // fixpoint pass cost Theta(blocks^2) in deep clones/compares/meets.
    // Per-block liveness bounds each persisted exit by what some path can
    // still read, exactly like [`post_live_out_locations`] does for the POST
    // walk.
    let tracked = pre_tracked_vregs(pre);
    let live_out = pre_live_out_tracked(pre, &tracked);

    // CT-3 clone elimination. A block whose transfer NEVER writes the tracked
    // value file — i.e. it defines no tracked vreg (equivalently: contains no
    // vreg-source copy [whose dest is tracked by construction] and no tracked
    // generic/phi def) — leaves the entry file UNCHANGED: `apply_inst_pre` is a
    // no-op for it (every mutating arm inserts a tracked def) and phi
    // establishment touches only tracked phi dests. Such a block's EXIT
    // therefore EQUALS its ENTRY, and — via [`pre_entry_shared`] — a
    // single-predecessor entry IS the predecessor's exit snapshot. So these
    // blocks (the common straight-line / flow-through case, and the whole cost
    // of the TY fused-BFS parent loop) share the predecessor's `Rc<PreState>`
    // in O(1) instead of cloning the whole map AND skip the retain entirely:
    // they persist a SUPERSET of their own live-out restriction (their preds'
    // persisted keys), which is harmless — any per-block retain family that
    // keeps at least live-out(B) is observation-equivalent (the dense walk
    // keeps everything; see the proof on [`pre_live_out_tracked`]) — and keeps
    // the share O(1). Blocks that DO write the tracked file take the
    // historical owned path (one deep clone via `Rc::make_mut`, then transfer
    // + retain) — no change for them.
    let mut block_writes_tracked = vec![false; pre.blocks.len()];
    for (bidx, block) in pre.blocks.iter().enumerate() {
        for &inst_id in &block.insts {
            let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                continue;
            };
            if inst.vreg_defs().any(|d| tracked.contains(&d)) {
                block_writes_tracked[bidx] = true;
                break;
            }
        }
    }

    let empty: Rc<PreState> = Rc::new(PreState::new());

    // Fixpoint over PRE exit states (vreg-keyed), snapshots ref-counted so the
    // no-write flow-through blocks share instead of clone.
    //
    // Walked in CFG reverse post-order for the same reason as
    // [`compute_exit_states_fixpoint`]: under a layout `block_order` that
    // places a block after its successors (x86-64 switch dispatch blocks), a
    // first-pass copy read of a not-yet-visited FORWARD predecessor defaults
    // to `Defined(src.id)`, and that transient — trapped in a loop cycle by
    // the absorbing conflict point — converges to a spurious
    // `Conflict({real_root, src.id})` for a plainly loop-invariant copy web.
    // That poisoned SPEC then rejects a correct maximally-coalesced POST
    // (`found = Defined(real_root)`), which is exactly the
    // std::sys::personality::dwarf::eh::read_encoded_offset x86 false
    // positive this walk-order fix closes.
    let mut exit_states: BTreeMap<BlockId, Rc<PreState>> = BTreeMap::new();
    let max_passes = pre.block_order.len().saturating_mul(2).saturating_add(2);
    let walk_order = cfg_reverse_post_order(pre);
    for _ in 0..max_passes {
        let mut changed = false;
        for &block_id in &walk_order {
            let Some(block) = pre.blocks.get(block_id.0 as usize) else {
                continue;
            };
            let exit: Rc<PreState> = if !block_writes_tracked[block_id.0 as usize] {
                // SHARE: exit == entry (no tracked write => no-op transfer, and the
                // entry is already observable-only => no-op retain).
                pre_entry_shared(block, &exit_states, &empty)
            } else {
                // OWN: materialize the entry (one deep clone iff shared), establish
                // phis, apply the transfer, then retain to observable keys.
                let mut rc = pre_entry_shared(block, &exit_states, &empty);
                {
                    let state = Rc::make_mut(&mut rc);
                    pre_establish_phis(pre, block_id, &tracked, state);
                    for &inst_id in &block.insts {
                        let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                            continue;
                        };
                        apply_inst_pre(inst, state, &tracked);
                    }
                    // Persist only the keys LIVE-OUT of THIS block (the
                    // in-block working state above keeps EVERY key, so
                    // in-block reads after in-block writes are untouched by
                    // this restriction — see [`pre_live_out_tracked`]).
                    match live_out.get(&block_id) {
                        Some(live) => state.retain(|v, _| live.contains(v)),
                        None => state.clear(),
                    }
                }
                rc
            };
            match exit_states.get(&block_id) {
                // `ptr_eq` is a sound fast path (same allocation => same contents);
                // otherwise the deep contents compare, identical to the historical
                // `*prev == state`.
                Some(prev) if Rc::ptr_eq(prev, &exit) || **prev == *exit => {}
                _ => {
                    exit_states.insert(block_id, exit);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Final pass: record the spec value of each ORIGINAL use, computed BEFORE the
    // use's instruction (matching the POST walk which checks uses before applying
    // the inst's defs). Flow-through (no tracked write) blocks record directly off
    // the shared entry snapshot with no clone; only writing blocks materialize.
    let mut expected: PreExpected = BTreeMap::new();
    for &block_id in &pre.block_order {
        let Some(block) = pre.blocks.get(block_id.0 as usize) else {
            continue;
        };
        let entry = pre_entry_shared(block, &exit_states, &empty);
        if !block_writes_tracked[block_id.0 as usize] {
            // State is CONSTANT across this block (== entry): read uses directly.
            for &inst_id in &block.insts {
                let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                    continue;
                };
                if !inst.flags.is_phi() {
                    for op in &inst.uses {
                        if let Some(v) = op.as_vreg() {
                            let val = entry.get(&v).cloned().unwrap_or(Sym::Defined(v.id));
                            expected.insert((inst_id, v), val);
                        }
                    }
                }
            }
        } else {
            let mut state: PreState = (*entry).clone();
            pre_establish_phis(pre, block_id, &tracked, &mut state);
            for &inst_id in &block.insts {
                let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                    continue;
                };
                if !inst.flags.is_phi() {
                    for op in &inst.uses {
                        if let Some(v) = op.as_vreg() {
                            let val = state.get(&v).cloned().unwrap_or(Sym::Defined(v.id));
                            expected.insert((inst_id, v), val);
                        }
                    }
                }
                apply_inst_pre(inst, &mut state, &tracked);
            }
        }
    }
    PreSpecFlow {
        expected,
        exit_states,
    }
}

/// The vregs whose PRE-spec symbolic value can EVER differ from the trivial
/// `Defined(own id)`: destinations of vreg-source copies.
///
/// EXACTNESS (why restricting the walk's key domain to this set is
/// observation-equivalent to the historical dense walk over all vregs):
///
/// The dense walk's transfer ([`apply_inst_pre`]) writes a non-default value
/// (`Defined(w)` with `w != v.id`, and transitively `Conflict`) into `state[v]`
/// ONLY through the vreg-source-copy arm — every other def inserts
/// `Defined(v.id)`. The meet ([`pre_meet_preds`]) is pointwise per key, and
/// `meet(Top, x) = x`, `meet(Defined(a), Defined(a)) = Defined(a)`, so by
/// induction a vreg that is NEVER a vreg-source-copy destination has dense
/// value in `{Top, Defined(v.id)}` at EVERY program point. Both read sites —
/// the copy-source read in [`apply_inst_pre`] and the use-recording in
/// [`compute_pre_expected`] — map an ABSENT key to `Defined(v.id)` via
/// `unwrap_or`, i.e. Top and `Defined(v.id)` are indistinguishable at every
/// read. Therefore never inserting those vregs (leaving them Top) delivers
/// exactly the dense walk's value at every read, and the tracked keys' values
/// form a closed subsystem (their transfers read only tracked keys' values
/// plus constants), so they converge to the identical fixpoint in the same
/// per-pass trajectory.
fn pre_tracked_vregs(pre: &MachFunction) -> BTreeSet<VReg> {
    let mut tracked = BTreeSet::new();
    for inst in &pre.insts {
        if inst.flags.is_phi() {
            continue;
        }
        let opcode = inst.opcode;
        if (opcode == PSEUDO_COPY || opcode == IR_COPY_OPCODE)
            && let (Some(dst), Some(_src)) = (first_vreg(&inst.defs), first_vreg(&inst.uses))
        {
            tracked.insert(dst);
        }
    }
    tracked
}

/// Copy-equivalence of the PRE spec (relaxation R4 — spurious identity-recurrence
/// conflict).
///
/// A pure vreg-to-vreg move (`PSEUDO_COPY` / `IR_COPY_OPCODE`) is value-preserving
/// BY DEFINITION: after `dst <- src`, `dst` holds EXACTLY `src`'s architectural
/// value. Transitively, every vreg in a copy-connected web holds the value of the
/// non-copy definition(s) — the ROOT(s) — that feed that web.
///
/// [`reach`] maps each vreg id to the SET of root ids it can hold, computed by
/// following copy edges `dst -> src` to a fixpoint (cycle-safe via a visited set).
/// A vreg is a ROOT (a value source, traversal stops) when it has ANY def that is
/// NOT a pure vreg-copy (an arithmetic/load/etc. def, or a copy from a PReg/imm),
/// or it has no def at all (a live-in / argument). A vreg with a mixed def set is
/// conservatively treated as its own root — that only ever KEEPS more distinct
/// roots, i.e. fails closed.
///
/// ## Why this is a SOUND acceptance for `spec CONFLICT(S)` vs `POST DEFINITE(w)`
///
/// The sparse PRE value-flow ([`compute_pre_spec_flow`]) can synthesize a SPURIOUS
/// `Conflict({r, c})` at a loop header when the loop-carried value is threaded
/// through a PURE COPY CYCLE (an *identity* recurrence — the value is copied
/// around unchanged, e.g. a `GapGuardRaw` pointer parked across an EH-bearing
/// comparator loop): a copy-dest source dropped by the persisted-exit retain reads
/// as lattice-Top and the `unwrap_or(Defined(src.id))` default REINTRODUCES the
/// intermediate's raw id `c` instead of its root `r`. The DENSE walk would collapse
/// the cycle to `Defined(r)`, exactly what a correct POST delivers.
///
/// So when POST is `Defined(w)` and the spec is `Conflict(S)` and ALL of `S ∪ {w}`
/// reach the SAME single root `r`, every id in the conflict names the SAME
/// architectural value (`r`'s), the conflict is illusory, and POST is CORRECT.
/// A GENUINE loop recurrence updates its value with a NON-copy op (`v_next = v_iv
/// + 1`), so `v_init` and `v_next` are DISTINCT roots — the conflict does NOT
///   collapse and the recurrence-stopping bug (#63/#64) STILL fails closed. Copies
///   cannot change a value, so R4 can never accept a real clobber.
struct CopyEquiv {
    /// vreg id -> the set of non-copy ROOT value ids it can architecturally hold.
    reach: BTreeMap<u32, BTreeSet<u32>>,
}

impl CopyEquiv {
    fn build(pre: &MachFunction) -> CopyEquiv {
        // Copy edges (id -> its pure-vreg-copy source ids) and the root set.
        let mut copy_srcs: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
        let mut is_root: BTreeSet<u32> = BTreeSet::new();
        let mut all_ids: BTreeSet<u32> = BTreeSet::new();
        for inst in &pre.insts {
            for u in inst.vreg_uses() {
                all_ids.insert(u.id);
            }
            let is_copy = !inst.flags.is_phi()
                && (inst.opcode == PSEUDO_COPY || inst.opcode == IR_COPY_OPCODE);
            let copy_src = if is_copy {
                first_vreg(&inst.uses)
            } else {
                None
            };
            for def in inst.vreg_defs() {
                all_ids.insert(def.id);
                match copy_src {
                    // A pure vreg-copy def contributes a copy edge.
                    Some(src) => copy_srcs.entry(def.id).or_default().push(src.id),
                    // Any non-(pure-vreg-copy) def makes this vreg a value root.
                    None => {
                        is_root.insert(def.id);
                    }
                }
            }
        }
        // A vreg that is never defined (a live-in / argument) is a root too.
        for &id in &all_ids {
            if !copy_srcs.contains_key(&id) {
                is_root.insert(id);
            }
        }
        let root_of = |start: u32| -> BTreeSet<u32> {
            let mut roots = BTreeSet::new();
            let mut visited = BTreeSet::new();
            let mut stack = vec![start];
            while let Some(u) = stack.pop() {
                if !visited.insert(u) {
                    continue;
                }
                // A root (or mixed-def vreg) is a definite value source: stop.
                if is_root.contains(&u) {
                    roots.insert(u);
                    continue;
                }
                match copy_srcs.get(&u) {
                    Some(srcs) => stack.extend(srcs.iter().copied()),
                    None => {
                        roots.insert(u);
                    }
                }
            }
            roots
        };
        let mut reach = BTreeMap::new();
        for &id in &all_ids {
            reach.insert(id, root_of(id));
        }
        CopyEquiv { reach }
    }

    /// The union of non-copy ROOT value ids reachable from every id in `sym`
    /// (`Defined(x)` -> reach(x); `Conflict(S)` -> ⋃ reach(s)). An id absent from
    /// `reach` (should not happen for tracked ids) contributes itself, failing
    /// closed. This is the set of architectural VALUE SOURCES the symbol can name.
    fn root_closure(&self, sym: &Sym) -> BTreeSet<u32> {
        let mut out = BTreeSet::new();
        let add = |id: u32, out: &mut BTreeSet<u32>| match self.reach.get(&id) {
            Some(r) => out.extend(r.iter().copied()),
            None => {
                out.insert(id);
            }
        };
        match sym {
            Sym::Defined(x) => add(*x, &mut out),
            Sym::Conflict(s) => {
                for id in s {
                    add(*id, &mut out);
                }
            }
        }
        out
    }

    /// True iff a `spec Conflict(conflict)` vs `POST Defined(found)` mismatch is a
    /// spurious identity-copy-recurrence conflict: `found` and every conflict
    /// source reach the SAME single copy root.
    fn is_spurious_copy_conflict(&self, found: u32, conflict: &BTreeSet<u32>) -> bool {
        let Some(rw) = self.reach.get(&found) else {
            return false;
        };
        if rw.len() != 1 {
            return false;
        }
        conflict
            .iter()
            .all(|s| self.reach.get(s).is_some_and(|rs| rs == rw))
    }
}

/// Per-block sets of TRACKED vregs LIVE-OUT in the PRE walk's read/write
/// model: the vregs whose persisted exit-state value at that block can
/// influence an observation of [`compute_pre_spec_flow`]'s result. The PRE
/// analogue of [`post_live_out_locations`]: a standard backward may-liveness
/// over per-block (GEN = read-before-first-write, KILL = written-anywhere)
/// summaries where:
///
///  * READS are every NON-phi instruction's tracked vreg uses — which covers
///    BOTH read sites of the walk: the copy-source read in [`apply_inst_pre`]
///    and the use-recording in the final pass, each of which reads the working
///    state BEFORE the instruction's defs are applied — plus, modeled as an
///    ENTRY read of the PHI BLOCK, every phi instruction's SOURCE vregs.
///    [`phi_edge_expected`] (the ONLY consumer of the returned `exit_states`
///    outside the fixpoint) reads a phi source DIRECTLY from the exit state of
///    each spec predecessor — `pre.blocks[phi_block].preds[i]`, see
///    [`collect_phi_specs`] — so a phi source goes into GEN unconditionally
///    (never masked by in-block writes; the read happens outside this block),
///    and liveness carries it into live-out of every predecessor the per-edge
///    obligation consults.
///  * WRITES mirror the walk's write sites exactly: [`pre_establish_phis`]
///    writes every tracked phi dest at BLOCK ENTRY (before any in-block read,
///    so phi dests seed the kill set), and every mutating arm of
///    [`apply_inst_pre`] inserts exactly a tracked def (a copy dest — tracked
///    by construction — or a tracked generic def). Blocks are straight-line,
///    so "written anywhere in the block" is "written on every path through the
///    block": the block-level KILL is exact, and over-approximating reads only
///    ever KEEPS more keys (conservative).
///
/// EXACTNESS (why restricting block B's persisted exit state to live-out(B) is
/// observation-equivalent to the historical dense walk): a dropped key is Top
/// at every successor's entry meet ([`pre_meet_owned`]: an absent key
/// contributes nothing), so its absence can only change behavior at a READ of
/// the propagated value. There are exactly two read channels out of a
/// persisted exit state: (1) an entry read (use-before-write) in some
/// downstream block D — then the key is in GEN(D) ⊆ live-in(D) ⊆ live-out(P)
/// for EVERY predecessor P of D, so it was persisted at every consulted
/// predecessor and the entry meet delivers the identical value; (2) the
/// per-edge phi read of [`phi_edge_expected`] at a spec predecessor's exit —
/// covered because the phi block's source-GEN puts the key in live-in of the
/// phi block, hence in live-out of every predecessor. The persisted keys form
/// a closed subsystem — a live-out key's next-pass exit value depends only on
/// in-block writes whose source reads are either in-block values (identical in
/// both walks) or entry reads of GEN keys (live-out at every predecessor,
/// hence persisted) — so the per-pass trajectory restricted to live-out keys
/// is identical to the dense walk's, convergence lands on the same restricted
/// values, and the recording pass and every [`phi_edge_expected`] lookup read
/// identical `Sym`s. Flow-through (no-tracked-write) blocks persist their
/// shared ENTRY snapshot unpruned — a SUPERSET of their live-out restriction —
/// which is covered by the same argument (any retain family keeping at least
/// live-out(B) sits between this restriction and the dense walk, and the extra
/// keys are read nowhere: a key read out of a flow-through exit is in its
/// live-in, hence in every pred's live-out, hence carries the restricted
/// trajectory's value).
fn pre_live_out_tracked(
    pre: &MachFunction,
    tracked: &BTreeSet<VReg>,
) -> BTreeMap<BlockId, BTreeSet<VReg>> {
    // Per-block GEN (read before first write) / KILL (written) summaries.
    let mut gen_sets: BTreeMap<BlockId, BTreeSet<VReg>> = BTreeMap::new();
    let mut kill_sets: BTreeMap<BlockId, BTreeSet<VReg>> = BTreeMap::new();

    for &block_id in &pre.block_order {
        let Some(block) = pre.blocks.get(block_id.0 as usize) else {
            continue;
        };
        let mut gen_set: BTreeSet<VReg> = BTreeSet::new();
        let mut written: BTreeSet<VReg> = BTreeSet::new();

        // Phi dests first: [`pre_establish_phis`] writes them at BLOCK ENTRY,
        // before any in-block read, wherever the phi sits in the inst list.
        for &inst_id in &block.insts {
            let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                continue;
            };
            if inst.flags.is_phi() {
                for def in inst.vreg_defs() {
                    if tracked.contains(&def) {
                        written.insert(def);
                    }
                }
            }
        }

        for &inst_id in &block.insts {
            let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                continue;
            };
            if inst.flags.is_phi() {
                // Phi sources: entry reads (see the doc comment), never masked.
                for v in inst.vreg_uses() {
                    if tracked.contains(&v) {
                        gen_set.insert(v);
                    }
                }
                continue;
            }
            // READS first (matching the walk: the copy-source read and the
            // use-recording happen before the instruction's defs are applied).
            for v in inst.vreg_uses() {
                if tracked.contains(&v) && !written.contains(&v) {
                    gen_set.insert(v);
                }
            }
            // WRITES: mirror `apply_inst_pre`'s write targets (tracked defs).
            for def in inst.vreg_defs() {
                if tracked.contains(&def) {
                    written.insert(def);
                }
            }
        }
        gen_sets.insert(block_id, gen_set);
        kill_sets.insert(block_id, written);
    }

    // Backward may-liveness to a fixpoint (same shape and pass cap as
    // [`post_live_out_locations`]):
    //   live-in(B)  = GEN(B) ∪ (live-out(B) − KILL(B))
    //   live-out(B) = ∪ over successors S of live-in(S)
    // Monotone (sets only grow) over a finite universe.
    let mut live_in: BTreeMap<BlockId, BTreeSet<VReg>> = BTreeMap::new();
    let mut live_out: BTreeMap<BlockId, BTreeSet<VReg>> = BTreeMap::new();
    for &block_id in &pre.block_order {
        live_in.insert(
            block_id,
            gen_sets.get(&block_id).cloned().unwrap_or_default(),
        );
        live_out.insert(block_id, BTreeSet::new());
    }
    let max_passes = pre.block_order.len().saturating_mul(2).saturating_add(2);
    for _ in 0..max_passes {
        let mut changed = false;
        for &block_id in pre.block_order.iter().rev() {
            let Some(block) = pre.blocks.get(block_id.0 as usize) else {
                continue;
            };
            let mut out: BTreeSet<VReg> = BTreeSet::new();
            for succ in &block.succs {
                if let Some(succ_in) = live_in.get(succ) {
                    out.extend(succ_in.iter().copied());
                }
            }
            let kill = kill_sets.get(&block_id);
            let mut inn = gen_sets.get(&block_id).cloned().unwrap_or_default();
            for &v in &out {
                if kill.map(|k| k.contains(&v)) != Some(true) {
                    inn.insert(v);
                }
            }
            if live_out.get(&block_id) != Some(&out) {
                live_out.insert(block_id, out);
                changed = true;
            }
            if live_in.get(&block_id) != Some(&inn) {
                live_in.insert(block_id, inn);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    live_out
}

/// Collect every VReg that appears (as a def or use operand) anywhere in `func`.
/// Used to recognize the ORIGINAL SSA-value namespace of the `pre` snapshot so
/// the value-flow walk can tell an original value from a post-pipeline split /
/// reload temporary (see the SPLIT trust-boundary note in [`check_value_flow`]).
fn collect_function_vregs(func: &MachFunction) -> BTreeSet<VReg> {
    let mut set = BTreeSet::new();
    for inst in &func.insts {
        for op in inst.defs.iter().chain(inst.uses.iter()) {
            if let Some(v) = op.as_vreg() {
                set.insert(v);
            }
        }
    }
    set
}

/// Collect the vregs that are (a) absent from `locations` (neither allocated nor
/// spilled to a named slot) and (b) DEFINED by an inserted instruction in `post`
/// (`InstId >= original_inst_count`). These are exactly the spill-reload /
/// rematerialization temporaries whose physical home the `AllocationResult` does
/// not name — outside the validator's value-flow trust boundary (see the module
/// header and the call site). A use of one of these is skipped by property (a);
/// a vreg unmapped for ANY OTHER reason (never defined by an inserted inst) is a
/// genuine dropped value and stays fail-closed.
fn collect_remat_reload_temps(
    post: &MachFunction,
    locations: &BTreeMap<VReg, Location>,
    original_inst_count: u32,
) -> BTreeSet<VReg> {
    let mut temps = BTreeSet::new();
    for &block_id in &post.block_order {
        let Some(block) = post.blocks.get(block_id.0 as usize) else {
            continue;
        };
        for &inst_id in &block.insts {
            if inst_id.0 < original_inst_count {
                continue; // only inserted instructions define reload/remat temps
            }
            let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                continue;
            };
            for def in inst.vreg_defs() {
                if !locations.contains_key(&def) {
                    temps.insert(def);
                }
            }
        }
    }
    temps
}

// ---------------------------------------------------------------------------
// Phi spec extraction from the PRE-alloc SSA.
// ---------------------------------------------------------------------------

/// One incoming phi edge: the POST block whose exit must realize the transfer
/// (the split block if the edge was split), the PRE predecessor the spec's
/// value-flow is evaluated at (for the generalized spec-value obligation when
/// original copies were coalesced away), and the source vreg (ORIGINAL id).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PhiEdge {
    realizing_pred: BlockId,
    spec_pred: BlockId,
    src: VReg,
}

/// One phi's specification: its destination vreg and the incoming edges.
type PhiSpec = (VReg, Vec<PhiEdge>);

/// All phi specs of the function, keyed by the block the phis live in.
type PhiSpecs = BTreeMap<BlockId, Vec<PhiSpec>>;

/// For each phi block, collect (dest, [(pred_block, src_vreg)]).
///
/// Phi format (matching `phi_elim::eliminate_phis`): `defs = [dest]`,
/// `uses[i]` is the value coming from `block.preds[i]`.
///
/// ## Pre/post predecessor reconciliation (critical-edge splitting)
///
/// The phi node itself only exists in `pre` (phi elimination removes it from
/// `post`), so `dest` and the per-edge `src` vregs MUST come from `pre`. But the
/// realizing copy `dest <- src_i` is emitted by `eliminate_phis` at the END of
/// the i-th predecessor edge — and `split_critical_edges`, which runs FIRST, may
/// have interposed a fresh single-pred/single-succ jump block S on that edge,
/// rewiring `post.blocks[phi_block].preds[i]` from the original pred Q to S and
/// placing the copy in S. The pre-edge predecessor (Q) is then no longer a
/// direct predecessor of the phi block in `post`, so checking Q's exit state for
/// the transfer would spuriously fail.
///
/// `split_critical_edges` replaces a split predecessor IN PLACE in the phi
/// block's `preds` list (same index, same length) and `eliminate_phis` never
/// reorders `preds`, so `post.blocks[phi_block].preds[i]` is exactly the block
/// whose EXIT must realize `pre`'s i-th phi source. We therefore pair each `pre`
/// source `uses[i]` with the POST predecessor at the same index. When `post`
/// lacks the block (it always has it here) we fall back to `pre`'s pred so the
/// validator stays conservative rather than dropping the obligation.
fn collect_phi_specs(pre: &MachFunction, post: &MachFunction) -> PhiSpecs {
    let mut specs: PhiSpecs = BTreeMap::new();

    for &block_id in &pre.block_order {
        let Some(block) = pre.blocks.get(block_id.0 as usize) else {
            continue;
        };
        // The phi-source -> realizing-predecessor mapping is index-aligned with
        // the POST phi block's `preds` (which carries any split-block rewiring).
        let post_preds = post
            .blocks
            .get(block_id.0 as usize)
            .map(|b| b.preds.as_slice())
            .unwrap_or(&[]);
        for &inst_id in &block.insts {
            let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                continue;
            };
            if !inst.flags.is_phi() {
                continue;
            }
            let Some(dest) = inst.defs.first().and_then(|op| op.as_vreg()) else {
                continue;
            };
            let mut sources = Vec::new();
            for (i, &pre_pred_id) in block.preds.iter().enumerate() {
                if let Some(src) = inst.uses.get(i).and_then(|op| op.as_vreg()) {
                    // Use the POST predecessor at this index (the split block, if
                    // the edge was split); fall back to the PRE pred if `post`
                    // somehow lacks it. The PRE pred is kept alongside: the SPEC
                    // value of `src` on this edge is its value at the PRE pred's
                    // exit (a split block contains no spec instructions).
                    let realizing_pred = post_preds.get(i).copied().unwrap_or(pre_pred_id);
                    sources.push(PhiEdge {
                        realizing_pred,
                        spec_pred: pre_pred_id,
                        src,
                    });
                }
            }
            specs.entry(block_id).or_default().push((dest, sources));
        }
    }

    specs
}

// ---------------------------------------------------------------------------
// Small operand helpers.
// ---------------------------------------------------------------------------

fn first_vreg(ops: &[RegAllocOperand]) -> Option<VReg> {
    ops.iter().find_map(|op| op.as_vreg())
}

fn first_slot(ops: &[RegAllocOperand]) -> Option<StackSlotId> {
    ops.iter().find_map(|op| match op {
        RegAllocOperand::StackSlot(s) => Some(*s),
        _ => None,
    })
}

/// Set of all locations currently bound to a vreg (utility for diagnostics /
/// future extensions; kept public-in-module for the test harness).
#[allow(dead_code)]
fn bound_locations(locations: &BTreeMap<VReg, Location>) -> BTreeSet<Location> {
    locations.values().copied().collect()
}

// trust-cg-regalloc/regalloc_validator_tests.rs - tests for the RA validator
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// These tests live in the `#[cfg(test)] mod tests` of regalloc_validator.rs
// when integrated (see integration_edits). They are written as a standalone
// `mod` here so the file is self-contained for review.

#[cfg(test)]
mod tests {
    use super::{Location, Sym, ValidationError, validate_allocation};
    use crate::linear_scan::AllocationResult;
    use crate::machine_types::*;
    use crate::phi_elim::PSEUDO_COPY;
    use crate::{AllocConfig, allocate};
    use std::collections::BTreeMap;

    fn vreg(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr64,
        }
    }

    // -----------------------------------------------------------------------
    // (a) A correct small allocation VALIDATES.
    //
    // Run the REAL pipeline on a straight-line function with low pressure, then
    // validate the (pre, post, result) triple. Locks in: the validator does not
    // reject sound allocations the production allocator actually produces.
    // -----------------------------------------------------------------------
    #[test]
    fn correct_allocation_validates() {
        // def v0=imm0; def v1=imm1; use v0; use v1.
        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::Imm(0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vreg(1))],
            uses: vec![MachOperand::Imm(1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(vreg(0))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i3 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(vreg(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "ok".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![i0, i1, i2, i3],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // Capture the SSA spec BEFORE allocate() mutates the function.
        let pre_snapshot = pre.clone();
        let mut post = pre;
        let config = AllocConfig::default_aarch64();
        let result = allocate(&mut post, &config).expect("allocation should succeed");

        let report = validate_allocation(&pre_snapshot, &post, &result);
        assert!(
            report.is_valid(),
            "a correct allocation must validate, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // (b) Overlapping-location assignment is REJECTED.
    //
    // Hand-build an allocation that puts two simultaneously-live vregs (v0, v1
    // both live at the final use of v0) into the SAME PReg. Locks in: the
    // interference-soundness check (#52/#53 clobber class).
    // -----------------------------------------------------------------------
    #[test]
    fn overlapping_location_rejected() {
        // def v0; def v1; use v0; use v1  — v0 and v1 are simultaneously live
        // at instruction 2 (use v0, with v1 still pending).
        let insts = vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::Imm(0)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(1))],
                uses: vec![MachOperand::Imm(1)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0)), MachOperand::VReg(vreg(1))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ];

        let pre = MachFunction {
            name: "interf".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // Inject the bug: v0 and v1 both assigned X0.
        let mut allocation = BTreeMap::new();
        allocation.insert(vreg(0), PReg::new(0));
        allocation.insert(vreg(1), PReg::new(0)); // SAME register — overlapping!
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        // post == pre here (no transform needed to exercise interference check).
        let report = validate_allocation(&pre, &pre, &result);
        assert!(
            !report.is_valid(),
            "overlapping assignment must be rejected"
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::InterferenceViolation { loc: Location::Reg(p), .. }
                    if *p == PReg::new(0)
            )),
            "expected an interference violation on X0, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // (b') LRSPLIT-2 REGRESSION: an INCOMING-ARGUMENT-register clobber is
    // REJECTED by the phys-reg interference gate.
    //
    // The entry block reads two incoming argument registers: `v0 <- RDI` (whose
    // register copy is DEAD after — live only `[0,1)`) and `v1 <- RSI`. The AY
    // whole-vreg solver colored the dead `v0` to RSI, so the emitted `mov RSI,
    // RDI` at position 0 destroyed the RSI argument BEFORE `v1 <- RSI` (position 1)
    // read it — a wrong value (exit 208/144 vs 35) that BOTH the AY self-check and
    // the always-on validator missed: `v0`'s range `[0,1)` does not touch RSI's
    // pos-1 read, so the old point-only reservation left `reserved_forbids(v0,
    // RSI)` false, and the vreg-vreg interference check never sees a value that
    // lives in a physical register without a vreg. The fix reserves RSI's live-in
    // span `[entry, read)` (position 0) AND adds the independent phys-reg gate.
    // -----------------------------------------------------------------------
    #[test]
    fn incoming_argument_register_clobber_rejected() {
        // SysV x86-64 GPR64 encodings (see x86_adapter): RAX=512, RCX=513,
        // RDX=514, RSI=518, RDI=519.
        let (rax, rcx, rdx, rsi, rdi) = (
            PReg::new(512),
            PReg::new(513),
            PReg::new(514),
            PReg::new(518),
            PReg::new(519),
        );

        let insts = vec![
            // pos 0: v0 <- RDI (reads the 1st incoming arg; v0 unused afterwards).
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: vec![rdi],
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // pos 1: v1 <- RSI (reads the 2nd incoming arg).
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(1))],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: vec![rsi],
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // pos 2: return v1 (RAX clobber) — keeps v1 live [1,3).
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(1))],
                implicit_defs: vec![rax],
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ];
        let func = MachFunction {
            name: "incoming_arg_clobber".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // (1) The reservation model must reserve RSI over its live-in span
        // [entry, read) — position 0 — not merely at its pos-1 read.
        let liveness = crate::liveness::compute_live_intervals(&func);
        let reserved = crate::implicit_def_reservations(&func, &liveness.inst_numbering);
        assert!(
            reserved.get(&rsi).is_some_and(|p| p.contains(&0)),
            "RSI's incoming-argument live-in span [entry, read) must be reserved at \
             position 0; got {reserved:?}"
        );

        // (2) The WRONG allocation (dead v0 colored to RSI) is REJECTED by the
        // phys-reg gate — the exact clobber the AY solver produced.
        let mut bad = BTreeMap::new();
        bad.insert(vreg(0), rsi);
        bad.insert(vreg(1), rdx);
        let bad_result = AllocationResult {
            allocation: bad,
            spills: Vec::new(),
        };
        let report = validate_allocation(&func, &func, &bad_result);
        assert!(
            report.errors.iter().any(|e| matches!(e,
                ValidationError::PhysRegInterference { vreg: v, reserved: r, .. }
                    if *v == vreg(0) && *r == rsi)),
            "the incoming-argument clobber (v0->RSI) must be rejected by the phys-reg \
             gate; got: {:?}",
            report.errors
        );

        // (3) A clobber-free allocation (v0 in a scratch, v1 elsewhere) still
        // VALIDATES — no false rejection.
        let mut good = BTreeMap::new();
        good.insert(vreg(0), rcx);
        good.insert(vreg(1), rdx);
        let good_result = AllocationResult {
            allocation: good,
            spills: Vec::new(),
        };
        let report = validate_allocation(&func, &func, &good_result);
        assert!(
            report.is_valid(),
            "a clobber-free allocation must validate, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // (b') DUPLICATE CALL ARGUMENT REGRESSION: a value passed into TWO argument
    // registers, homed in the FIRST of them, must VALIDATE (it is not a clobber).
    //
    // `f(a, a, ..)` (e.g. std::intrinsics::rotate_left's funnel-shift call) lowers
    // to `Copy x0 <- v`, `Copy x1 <- v`, `Bl`. The AAPCS64 allocator homes `v` in
    // x0 (its arg0 register), so `Copy x0 <- v` is an identity move and `Copy x1
    // <- v` is a real `x1 <- x0`. The call-argument SPAN reservation guards x0
    // across `[arg0-setup+1, call)` — which covers the `Copy x1 <- v` position —
    // to stop an UNRELATED vreg being parked in x0 before the call. But `v` (homed
    // x0) IS x0's intended occupant there, and `Copy x1 <- v` only READS x0, so it
    // is not a clobber. The allocator's `hint_exempt` already exempts that
    // position (it is a copy with `v` as an endpoint); the validator must mirror
    // it, else a valid allocation is spuriously rejected as `PhysRegInterference`.
    // -----------------------------------------------------------------------
    #[test]
    fn duplicate_call_argument_in_home_register_validates() {
        use crate::phi_elim::PSEUDO_COPY;
        // AArch64 GPR64 encodings: x0 = 0, x1 = 1.
        let (x0, x1) = (PReg::new(0), PReg::new(1));

        let insts = vec![
            // pos 0: v0 <- x0 (formal-arg materialization).
            MachInst {
                opcode: PSEUDO_COPY,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::PReg(x0)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // pos 1: x0 <- v0 (arg0 setup — identity when v0 is homed x0).
            MachInst {
                opcode: PSEUDO_COPY,
                defs: vec![MachOperand::PReg(x0)],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // pos 2: x1 <- v0 (arg1 setup — the DUPLICATE; reads x0, no clobber).
            MachInst {
                opcode: PSEUDO_COPY,
                defs: vec![MachOperand::PReg(x1)],
                uses: vec![MachOperand::VReg(vreg(0))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            // pos 3: Bl (reads x0, x1; clobbers x0, x1).
            MachInst {
                opcode: 99,
                defs: vec![],
                uses: vec![],
                implicit_defs: vec![x0, x1],
                implicit_uses: vec![x0, x1],
                flags: InstFlags::IS_CALL,
                tied_operands: vec![],
            },
        ];
        let func = MachFunction {
            name: "dup_call_arg".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2), InstId(3)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // The call-argument span for x0 DOES reserve the `Copy x1 <- v0` position
        // (2) — this is what makes the test meaningful: the reservation is present,
        // yet validation must still pass because v0 is the reserved register's
        // legitimate occupant there.
        let liveness = compute_live_intervals(&func);
        let reserved = crate::implicit_def_reservations(&func, &liveness.inst_numbering);
        assert!(
            reserved.get(&x0).is_some_and(|p| p.contains(&2)),
            "x0's call-argument span must reserve position 2; got {reserved:?}"
        );

        // v0 homed in x0: the correct AAPCS64 allocation. Must validate.
        let mut allocation = BTreeMap::new();
        allocation.insert(vreg(0), x0);
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };
        let report = validate_allocation(&func, &func, &result);
        assert!(
            !report.errors.iter().any(|e| matches!(
                e,
                ValidationError::PhysRegInterference { vreg: v, reserved: r, .. }
                    if *v == vreg(0) && *r == x0
            )),
            "v0 passed into two argument registers and homed in x0 must NOT be \
             flagged as a phys-reg clobber of x0; got: {:?}",
            report.errors
        );
        assert!(
            report.is_valid(),
            "the duplicate-call-argument allocation must validate, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // (b') RANK 4: alias-aware interference. Two simultaneously-live vregs
    // assigned ALIASING-but-distinct pregs (e.g. X0/W0, V8/D8, RAX/EAX) must be
    // reported as interfering; genuinely-disjoint pregs (X0/X1, V0/V1, RAX/RCX)
    // must NOT be flagged.
    //
    // Builds the canonical interference shape (def v0; def v1; use v0,v1 — both
    // live at inst 2), hand-injects v0->`pa`, v1->`pb`, and validates. Returns
    // whether an InterferenceViolation was reported.
    // -----------------------------------------------------------------------
    fn run_interference_two_regs(pa: PReg, pb: PReg) -> bool {
        let insts = vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(0))],
                uses: vec![MachOperand::Imm(0)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(1))],
                uses: vec![MachOperand::Imm(1)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(0)), MachOperand::VReg(vreg(1))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ];
        let pre = MachFunction {
            name: "alias_interf".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let mut allocation = BTreeMap::new();
        allocation.insert(vreg(0), pa);
        allocation.insert(vreg(1), pb);
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };
        let report = validate_allocation(&pre, &pre, &result);
        report
            .errors
            .iter()
            .any(|e| matches!(e, ValidationError::InterferenceViolation { .. }))
    }

    #[test]
    fn aliasing_subregisters_rejected() {
        // AArch64 GPR: X0 (enc 0) and W0 (enc 32) share physical X0.
        assert!(
            run_interference_two_regs(PReg::new(0), PReg::new(32)),
            "X0/W0 (aliasing) must be reported as interfering"
        );
        // AArch64 FPR: V8 (enc 72) and D8 (enc 104) share physical V8.
        assert!(
            run_interference_two_regs(PReg::new(72), PReg::new(104)),
            "V8/D8 (aliasing) must be reported as interfering"
        );
        // AArch64 FPR: D8 (enc 104) and H8 (enc 173) share physical V8.
        assert!(
            run_interference_two_regs(PReg::new(104), PReg::new(173)),
            "D8/H8 (aliasing) must be reported as interfering"
        );
        // x86 GPR: RAX (enc 512) and EAX (enc 528) share physical RAX. The
        // shared validator dispatches x86 pregs to x86_pregs_overlap.
        assert!(
            run_interference_two_regs(PReg::new(512), PReg::new(528)),
            "RAX/EAX (aliasing) must be reported as interfering"
        );
    }

    #[test]
    fn disjoint_registers_not_flagged() {
        // PRIME DIRECTIVE rank 4: genuinely-disjoint registers must NOT be made
        // to falsely interfere.
        // AArch64 GPR: X0 (enc 0) vs X1 (enc 1) — distinct roots.
        assert!(
            !run_interference_two_regs(PReg::new(0), PReg::new(1)),
            "X0/X1 (disjoint) must NOT be flagged as interfering"
        );
        // AArch64 FPR: V0 (enc 64) vs V1 (enc 65) — distinct roots.
        assert!(
            !run_interference_two_regs(PReg::new(64), PReg::new(65)),
            "V0/V1 (disjoint) must NOT be flagged as interfering"
        );
        // AArch64 FPR: H8 (enc 173) vs H9 (enc 174) — distinct roots V8 vs V9.
        assert!(
            !run_interference_two_regs(PReg::new(173), PReg::new(174)),
            "H8/H9 (disjoint) must NOT be flagged as interfering"
        );
        // x86 GPR: RAX (enc 512) vs RCX (enc 513) — distinct roots.
        assert!(
            !run_interference_two_regs(PReg::new(512), PReg::new(513)),
            "RAX/RCX (disjoint) must NOT be flagged as interfering"
        );
        // Cross-group: an AArch64 GPR (X0=0) vs an FPR (V0=64) never share
        // storage.
        assert!(
            !run_interference_two_regs(PReg::new(0), PReg::new(64)),
            "X0/V0 (cross-group) must NOT be flagged as interfering"
        );
    }

    // -----------------------------------------------------------------------
    // (c) An injected #64-shape splitter bug is REJECTED.
    //
    // Shape: a join where the realizing copy lands on the WRONG side. We model a
    // phi `v2 = [v0 from pred A, v1 from pred B]` lowered into copies, but the
    // bug overwrites v2's location on pred A's exit with the wrong value before
    // the join (the call-free-join clobber of #64). The validator must catch
    // that pred A's exit does not place v0 into v2's location.
    //
    // Locks in: phi/parallel-copy correctness at a join (#64).
    // -----------------------------------------------------------------------
    #[test]
    fn join_clobber_64_rejected() {
        // PRE (SSA + phi):
        //  B0: def v0; def v1; cbranch -> B1, B2
        //  B1: branch -> B3
        //  B2: branch -> B3
        //  B3: phi v2 = [v0 (from B1), v1 (from B2)]; use v2
        let v0 = vreg(0);
        let v1 = vreg(1);
        let v2 = vreg(2);

        let mut insts = Vec::new();
        // B0
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(10)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::Imm(20)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v0),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        // B1 -> B3
        let i3 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        // B2 -> B3
        let i4 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        // B3: phi v2 = [v0, v1]; use v2
        let i5 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0x00,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::VReg(v0), MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_PHI,
            tied_operands: vec![],
        });
        let i6 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v2)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "join64".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i1, i2],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i3],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i4],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i5, i6],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // Build a BUGGY POST by hand. Assignment: v0->X0, v1->X1, v2->X2.
        // CORRECT lowering inserts on B1's exit `X2 <- X0` (copy v2<-v0) and on
        // B2's exit `X2 <- X1`. The #64 bug DROPS B1's copy (the realizing copy
        // landed past the join), so B1 exits with v2's location (X2) NEVER
        // written — holding a stale/unknown value, not v0.
        //
        // We mirror what eliminate_phis would have produced, minus the B1 copy.
        let mut post = pre.clone();
        // Remove the phi from B3 (phi elimination removes it).
        post.blocks[3].insts.retain(|&id| id != i5);

        // Insert ONLY B2's copy (v2 <- v1), before B2's terminator.
        let copy_b2 = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        // B2 currently has [i4]; insert copy before the terminator i4.
        post.blocks[2].insts.insert(0, copy_b2);
        // (B1 deliberately gets NO copy — the injected #64 join clobber.)

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v1, PReg::new(1));
        allocation.insert(v2, PReg::new(2));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "#64 join clobber (missing edge copy) must be rejected"
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::PhiTransferBroken { phi_dest, phi_src, pred, .. }
                    if *phi_dest == v2 && *phi_src == v0 && *pred == BlockId(1)
            )),
            "expected a broken v2<-v0 transfer on the B1 edge, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // (c') The CORRECT phi lowering (both edge copies present) VALIDATES.
    //
    // Same diamond as the #64 test but with BOTH realizing copies inserted.
    // Locks in: the validator accepts a sound phi lowering (no false positive).
    // -----------------------------------------------------------------------
    #[test]
    fn correct_phi_lowering_validates() {
        let v0 = vreg(0);
        let v1 = vreg(1);
        let v2 = vreg(2);

        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(10)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::Imm(20)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v0),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i3 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i4 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i5 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0x00,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::VReg(v0), MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_PHI,
            tied_operands: vec![],
        });
        let i6 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v2)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "join_ok".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i1, i2],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i3],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i4],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i5, i6],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let mut post = pre.clone();
        post.blocks[3].insts.retain(|&id| id != i5);

        // B1 exit: v2 <- v0.
        let copy_b1 = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[1].insts.insert(0, copy_b1);

        // B2 exit: v2 <- v1.
        let copy_b2 = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[2].insts.insert(0, copy_b2);

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v1, PReg::new(1));
        allocation.insert(v2, PReg::new(2));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            report.is_valid(),
            "correct phi lowering must validate, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // Bonus: a clobber-before-use within a single block (no phi) is rejected.
    // Models the #53 arg-register clobber shape at the value-flow level: a value
    // is overwritten in its assigned location before its later use.
    // -----------------------------------------------------------------------
    #[test]
    fn straight_line_clobber_before_use_rejected() {
        // def v0; def v1; use v0  — but allocate v0 and v1 to X0, and let v1's
        // def overwrite X0 before v0's use. (Same as interference, but checked
        // through value-flow: v0's location X0 holds v1 at the use.)
        let v0 = vreg(0);
        let v1 = vreg(1);
        let insts = vec![
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(v0)],
                uses: vec![MachOperand::Imm(0)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(v1)],
                uses: vec![MachOperand::Imm(1)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(v0)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
        ];

        let pre = MachFunction {
            name: "clobber".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2)],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v1, PReg::new(0)); // both X0
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &pre, &result);
        assert!(!report.is_valid(), "clobber-before-use must be rejected");
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::ValueFlowMismatch { vreg, .. } if *vreg == v0
            )) || report
                .errors
                .iter()
                .any(|e| matches!(e, ValidationError::InterferenceViolation { .. })),
            "expected value-flow or interference rejection, got: {:?}",
            report.errors
        );
    }

    // Build the standard #64 diamond PRE (SSA + a single phi v2 = [v0,v1]) used
    // by the per-edge phi tests below. Returns (pre, v0, v1, v2, phi InstId).
    //
    //  B0: def v0; def v1; cbranch -> B1, B2
    //  B1: branch -> B3
    //  B2: branch -> B3
    //  B3: phi v2 = [v0 (from B1), v1 (from B2)]; use v2
    fn diamond_phi_pre() -> (MachFunction, VReg, VReg, VReg, InstId) {
        let v0 = vreg(0);
        let v1 = vreg(1);
        let v2 = vreg(2);

        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(10)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::Imm(20)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v0),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i3 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i4 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i5 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0x00,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::VReg(v0), MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_PHI,
            tied_operands: vec![],
        });
        let i6 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v2)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "diamond".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i1, i2],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i3],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i4],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i5, i6],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        (pre, v0, v1, v2, i5)
    }

    // -----------------------------------------------------------------------
    // ROOT-CAUSE REGRESSION (1): a phi-realizing copy that reads the WRONG
    // predecessor's source must be REJECTED.
    //
    // Diamond `v2 = [v0 from B1, v1 from B2]`. The CORRECT B1-edge copy is
    // `v2 <- v0`; we inject `v2 <- v1` on the B1 edge instead. (B2's correct
    // copy `v2 <- v1` is present.) The flat per-dest acceptable-set bug accepted
    // this because v1 appears as a source on the B2 edge — so v1 was "acceptable"
    // for v2 everywhere. The per-EDGE obligation must reject: B1 must deliver
    // v0, not v1, into v2's location.
    //
    // Before the fix this PASSED (false negative); after, it is rejected with
    // PhiTransferBroken { pred: B1 }.
    // -----------------------------------------------------------------------
    #[test]
    fn wrong_source_copy_on_b1_edge_rejected() {
        let (pre, v0, v1, v2, phi_id) = diamond_phi_pre();

        let mut post = pre.clone();
        // Phi elimination removes the phi from B3.
        post.blocks[3].insts.retain(|&id| id != phi_id);

        // B1 edge: inject the WRONG realizing copy `v2 <- v1` (should be v2<-v0).
        let copy_b1 = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::VReg(v1)], // WRONG: reads B2's source on B1.
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[1].insts.insert(0, copy_b1);

        // B2 edge: the CORRECT realizing copy `v2 <- v1`.
        let copy_b2 = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[2].insts.insert(0, copy_b2);

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v1, PReg::new(1));
        allocation.insert(v2, PReg::new(2));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "a wrong-predecessor-source phi copy must be rejected"
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::PhiTransferBroken { phi_dest, phi_src, pred, .. }
                    if *phi_dest == v2 && *phi_src == v0 && *pred == BlockId(1)
            )),
            "expected a broken v2<-v0 transfer on the B1 edge, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // ROOT-CAUSE REGRESSION (2): a cross-phi SWAP on a shared edge must be
    // REJECTED.
    //
    // Two phis in the join, sharing predecessor edges:
    //   v4 = [v0 from B1, v0 from B2]
    //   v5 = [v1 from B1, v1 from B2]
    // CORRECT B1-edge copies: `v4 <- v0`, `v5 <- v1`. We inject the SWAP
    // `v4 <- v1`, `v5 <- v0` on the B1 edge. The flat acceptable-set bug accepted
    // each copy (v0 and v1 are both "acceptable" somewhere for these dests via
    // the union), masking the swap. The per-edge obligation rejects it: B1 must
    // deliver v0 into v4 and v1 into v5.
    // -----------------------------------------------------------------------
    #[test]
    fn cross_phi_swap_on_shared_edge_rejected() {
        let v0 = vreg(0);
        let v1 = vreg(1);
        let v4 = vreg(4);
        let v5 = vreg(5);

        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(10)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::Imm(20)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v0),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i3 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i4 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        // B3: two phis, then a use of each.
        let i5 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0x00,
            defs: vec![MachOperand::VReg(v4)],
            uses: vec![MachOperand::VReg(v0), MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_PHI,
            tied_operands: vec![],
        });
        let i6 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0x00,
            defs: vec![MachOperand::VReg(v5)],
            uses: vec![MachOperand::VReg(v1), MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_PHI,
            tied_operands: vec![],
        });
        let i7 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v4), MachOperand::VReg(v5)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "cross_phi".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i1, i2],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i3],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i4],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i5, i6, i7],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 6,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let mut post = pre.clone();
        post.blocks[3].insts.retain(|&id| id != i5 && id != i6);

        // B1 edge: SWAPPED copies `v4 <- v1`, `v5 <- v0` (correct = v4<-v0, v5<-v1).
        let b1_v4 = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v4)],
            uses: vec![MachOperand::VReg(v1)], // WRONG
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let b1_v5 = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v5)],
            uses: vec![MachOperand::VReg(v0)], // WRONG
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[1].insts.insert(0, b1_v5);
        post.blocks[1].insts.insert(0, b1_v4);

        // B2 edge: CORRECT copies `v4 <- v0`, `v5 <- v1`.
        let b2_v4 = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v4)],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let b2_v5 = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v5)],
            uses: vec![MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[2].insts.insert(0, b2_v5);
        post.blocks[2].insts.insert(0, b2_v4);

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v1, PReg::new(1));
        allocation.insert(v4, PReg::new(4));
        allocation.insert(v5, PReg::new(5));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "a cross-phi swap on the B1 edge must be rejected"
        );
        // Both phi obligations on the B1 edge are violated; assert at least the
        // v4<-v0 one is flagged.
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::PhiTransferBroken { phi_dest, phi_src, pred, .. }
                    if *phi_dest == v4 && *phi_src == v0 && *pred == BlockId(1)
            )),
            "expected a broken v4<-v0 transfer on the B1 edge, got: {:?}",
            report.errors
        );
    }

    // Build a counted self-loop PRE (SSA + a loop-carried phi) used by the loop
    // tests below. Returns (pre, v0, v1, v2, phi InstId, use-of-v1 InstId).
    //
    //  B0 (preheader): def v0 = 0; branch -> B1
    //  B1 (header):    phi v1 = [v0 (from B0), v2 (from B1)]   ; loop-carried
    //                  use v1                                   ; ORIGINAL use
    //                  def v2 = step(v1)                        ; v2 is next iv
    //                  cbranch v1 -> B1 (back-edge), B2 (exit)
    //  B2 (exit):      ret
    //
    // The phi's SECOND incoming source (v2) arrives on the BACK-EDGE B1->B1, so a
    // single forward pass over block_order can never see v2's value when it first
    // reaches B1's header — the residual this fix closes.
    fn self_loop_phi_pre() -> (MachFunction, VReg, VReg, VReg, InstId, InstId) {
        let v0 = vreg(0); // loop-invariant init
        let v1 = vreg(1); // induction variable (phi dest)
        let v2 = vreg(2); // next induction value

        let mut insts = Vec::new();
        // B0: def v0 = 0
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        // B0: branch -> B1
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        // B1: phi v1 = [v0 (from B0), v2 (from B1)]
        let i_phi = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0x00,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::VReg(v0), MachOperand::VReg(v2)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_PHI,
            tied_operands: vec![],
        });
        // B1: use v1  (ORIGINAL use of the loop-carried value)
        let i_use = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        // B1: def v2 = step(v1)
        let i_step = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 3,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::VReg(v1), MachOperand::Imm(1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        // B1: cbranch v2 -> B1 (back-edge), B2 (exit)
        //
        // The branch condition reads v2 (the freshly computed next value), NOT
        // v1: the back-edge realizing copy `v1 <- v2` must be placed before this
        // terminator and would overwrite v1's location, so a real allocator never
        // leaves a v1 use after that copy. v1's only original use is `i_use`,
        // above the step/copy, where the loop-carried value must validate.
        let i_cbr = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v2),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        // B2: ret
        let i_ret = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBC,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_TERMINATOR,
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "self_loop".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i1],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i_phi, i_use, i_step, i_cbr],
                    // Self-loop: B1 is its own predecessor via the back-edge.
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![i_ret],
                    preds: vec![BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        (pre, v0, v1, v2, i_phi, i_use)
    }

    // -----------------------------------------------------------------------
    // RESIDUAL CLOSED (a): a CORRECT loop with a loop-carried phi VALIDATES.
    //
    // The phi `v1 = [v0 from B0, v2 from B1]` is realized by a copy `v1 <- v0`
    // on the preheader edge and `v1 <- v2` on the BACK-EDGE (placed at B1's
    // exit, before the cbranch). Assignment v0->X0, v1->X1, v2->X2.
    //
    // Under the OLD single-forward-pass walk, B1's back-edge predecessor (itself)
    // was unwalked when the header was first processed, so the meet collapsed
    // X1 to None and the phi-establishment could not confirm the v2 edge — the
    // in-loop `use v1` then read None and produced a SPURIOUS ValueFlowMismatch
    // (the false positive that blocked valid loop allocations). The fixpoint
    // establishment now confirms the back-edge once B1's exit state is computed,
    // so this validates.
    // -----------------------------------------------------------------------
    #[test]
    fn correct_loop_carried_phi_validates() {
        let (pre, v0, v1, v2, phi_id, _use_id) = self_loop_phi_pre();

        let mut post = pre.clone();
        // Phi elimination removes the phi from B1's header.
        post.blocks[1].insts.retain(|&id| id != phi_id);

        // Preheader edge realizing copy `v1 <- v0`, before B0's branch.
        let copy_pre = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        // B0 currently has [i0, i1]; insert before the terminator i1 (index 1).
        post.blocks[0].insts.insert(1, copy_pre);

        // Back-edge realizing copy `v1 <- v2`, at B1's exit (before the cbranch).
        // After the phi removal B1 is [use, step, cbranch]; insert before cbranch.
        let copy_back = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::VReg(v2)], // CORRECT: thread the updated iv.
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let cbr_idx = post.blocks[1].insts.len() - 1;
        post.blocks[1].insts.insert(cbr_idx, copy_back);

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v1, PReg::new(1));
        allocation.insert(v2, PReg::new(2));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            report.is_valid(),
            "a correct loop-carried phi must validate (loop-header fixpoint), got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // RESIDUAL CLOSED (b): a WRONG loop-carried phi is still REJECTED.
    //
    // Same self-loop, but the BACK-EDGE realizing copy threads the WRONG source:
    // `v1 <- v0` (the preheader's invariant init) instead of `v1 <- v2` (the
    // updated induction value). This is a genuine loop miscompile — the induction
    // variable never advances. The per-edge phi-transfer obligation must reject
    // it: the B1 back-edge must deliver v2 into v1's location, not v0. The
    // fixpoint must NOT mask this (no false negative): leaving the back-edge
    // unwalked is no longer an excuse to skip the obligation.
    // -----------------------------------------------------------------------
    #[test]
    fn wrong_loop_carried_phi_rejected() {
        let (pre, v0, v1, v2, phi_id, _use_id) = self_loop_phi_pre();

        let mut post = pre.clone();
        post.blocks[1].insts.retain(|&id| id != phi_id);

        // Preheader edge: CORRECT `v1 <- v0`.
        let copy_pre = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[0].insts.insert(1, copy_pre);

        // Back-edge: WRONG `v1 <- v0` (should be v1 <- v2).
        let copy_back = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::VReg(v0)], // WRONG: re-threads the init, not v2.
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let cbr_idx = post.blocks[1].insts.len() - 1;
        post.blocks[1].insts.insert(cbr_idx, copy_back);

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v1, PReg::new(1));
        allocation.insert(v2, PReg::new(2));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "a wrong loop-carried phi copy (back-edge threads v0, not v2) must be rejected"
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::PhiTransferBroken { phi_dest, phi_src, pred, .. }
                    if *phi_dest == v1 && *phi_src == v2 && *pred == BlockId(1)
            )),
            "expected a broken v1<-v2 transfer on the B1 back-edge, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // RESIDUAL CLOSED (a, nested): a CORRECT 2-deep nested loop with BOTH an
    // outer and an inner loop-carried phi VALIDATES.
    //
    // This exercises the GENERAL fixpoint (more than a single re-derivation): the
    // OUTER header's phi depends on the OUTER latch's exit, which appears late in
    // block_order and itself reads the outer loop-carried value — so the outer
    // identity only stabilizes after the outer-latch exit has been recomputed in
    // a later fixpoint pass. A naive seed-then-establish-once scheme would still
    // false-positive on the outer phi's in-loop use.
    //
    //  B0 (preheader): def vc = 0; copy vo <- vc          ; -> B1
    //  B1 (outer hdr): phi vo = [vc from B0, von from B3]  ; copy vi <- vo ; -> B2
    //  B2 (inner hdr): phi vi = [vo from B1, vin from B2]
    //                  use vi                              ; ORIGINAL inner use
    //                  def vin = step(vi)                  ; copy vi <- vin (back)
    //                  cbranch vin -> B2 (inner back), B3 (inner exit)
    //  B3 (outer ltc): use vo                              ; ORIGINAL outer use
    //                  def von = step(vo)                  ; copy vo <- von (back)
    //                  cbranch von -> B1 (outer back), B4 (exit)
    //  B4 (exit):      ret
    //
    // Allocation: vc->X0, vo->X1, vi->X3, vin->X4, von->X5. (Distinct registers so
    // no interference; each loop-carried value lives in its own location and is
    // re-threaded into the phi-DEST location by an explicit edge copy.)
    // -----------------------------------------------------------------------
    #[test]
    fn correct_nested_loop_carried_phis_validate() {
        let vc = vreg(0); // outer init constant
        let vo = vreg(1); // outer induction variable (outer phi dest)
        let vi = vreg(3); // inner induction variable (inner phi dest)
        let vin = vreg(4); // inner next value
        let von = vreg(5); // outer next value

        let mut insts = Vec::new();
        // B0
        let b0_def = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(vc)],
            uses: vec![MachOperand::Imm(0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let b0_br = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        // B1: outer phi
        let outer_phi = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0x00,
            defs: vec![MachOperand::VReg(vo)],
            uses: vec![MachOperand::VReg(vc), MachOperand::VReg(von)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_PHI,
            tied_operands: vec![],
        });
        let b1_br = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(2))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        // B2: inner phi (inner init is the outer iv `vo` directly)
        let inner_phi = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0x00,
            defs: vec![MachOperand::VReg(vi)],
            uses: vec![MachOperand::VReg(vo), MachOperand::VReg(vin)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_PHI,
            tied_operands: vec![],
        });
        let inner_use = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(vi)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let inner_step = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 3,
            defs: vec![MachOperand::VReg(vin)],
            uses: vec![MachOperand::VReg(vi), MachOperand::Imm(1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let inner_cbr = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(vin),
                MachOperand::Block(BlockId(2)),
                MachOperand::Block(BlockId(3)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        // B3: outer latch
        let outer_use = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(vo)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let outer_step = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 3,
            defs: vec![MachOperand::VReg(von)],
            uses: vec![MachOperand::VReg(vo), MachOperand::Imm(1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let outer_cbr = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(von),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(4)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        // B4: ret
        let b4_ret = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBC,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_TERMINATOR,
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "nested_loop".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![b0_def, b0_br],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![outer_phi, b1_br],
                    preds: vec![BlockId(0), BlockId(3)],
                    succs: vec![BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![inner_phi, inner_use, inner_step, inner_cbr],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: vec![BlockId(2), BlockId(3)],
                    loop_depth: 2,
                },
                MachBlock {
                    insts: vec![outer_use, outer_step, outer_cbr],
                    preds: vec![BlockId(2)],
                    succs: vec![BlockId(1), BlockId(4)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![b4_ret],
                    preds: vec![BlockId(3)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3), BlockId(4)],
            entry_block: BlockId(0),
            next_vreg: 6,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let mut post = pre.clone();
        post.blocks[1].insts.retain(|&id| id != outer_phi);
        post.blocks[2].insts.retain(|&id| id != inner_phi);

        // Helper to push a copy `dst <- src` and return its InstId.
        let push_copy = |post: &mut MachFunction, dst: VReg, src: VReg| -> InstId {
            let id = InstId(post.insts.len() as u32);
            post.insts.push(MachInst {
                opcode: PSEUDO_COPY,
                defs: vec![MachOperand::VReg(dst)],
                uses: vec![MachOperand::VReg(src)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            });
            id
        };

        // B0 edge realizes outer phi's B0 source: vo <- vc, before B0's branch.
        let c = push_copy(&mut post, vo, vc);
        post.blocks[0].insts.insert(1, c);

        // B1 edge realizes inner phi's B1 source into the inner-phi DEST location:
        // vi <- vo, before B1's branch.
        let c = push_copy(&mut post, vi, vo);
        let b1_idx = post.blocks[1].insts.len() - 1;
        post.blocks[1].insts.insert(b1_idx, c);

        // B2 back-edge realizes inner phi's B2 source: vi <- vin, before inner cbr.
        let c = push_copy(&mut post, vi, vin);
        let b2_idx = post.blocks[2].insts.len() - 1;
        post.blocks[2].insts.insert(b2_idx, c);

        // B3 back-edge realizes outer phi's B3 source: vo <- von, before outer cbr.
        let c = push_copy(&mut post, vo, von);
        let b3_idx = post.blocks[3].insts.len() - 1;
        post.blocks[3].insts.insert(b3_idx, c);

        let mut allocation = BTreeMap::new();
        allocation.insert(vc, PReg::new(0));
        allocation.insert(vo, PReg::new(1));
        allocation.insert(vi, PReg::new(3));
        allocation.insert(vin, PReg::new(4));
        allocation.insert(von, PReg::new(5));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            report.is_valid(),
            "a correct 2-deep nested loop must validate (general fixpoint), got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // SOUNDNESS GUARD for the relaxed meet: a value live across a merge that is
    // CLOBBERED on one incoming edge must still be REJECTED.
    //
    // The loop fix relaxed the meet so that `meet(Defined(v), Top) = Defined(v)`
    // (an unwritten/back-edge predecessor contributes nothing). This test pins
    // that the relaxation did NOT weaken real merge-conflict detection: a clobber
    // writes `Defined(other)` into the location (it is NOT `Top`), so the meet of
    // the two edges is `meet(Defined(v0), Defined(v1)) = Conflict`, and the
    // post-merge use of v0 reads a conflicting location and fails closed.
    //
    //  B0: def v0; def v1; cbranch -> B1, B2
    //  B1: copy v0loc <- v1   (CLOBBER: overwrites v0's home with v1 on this edge)
    //      branch -> B3
    //  B2: branch -> B3       (v0 survives untouched on this edge)
    //  B3: use v0             (reachable via a clobbered edge -> reject)
    //
    // Allocation: v0->X0, v1->X1. The B1 clobber `X0 <- X1` is a copy with
    // dst=v0, src=v1 (so it writes v0's location X0 with v1's value).
    // -----------------------------------------------------------------------
    #[test]
    fn merge_clobber_of_live_value_rejected() {
        let v0 = vreg(0);
        let v1 = vreg(1);

        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(10)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::Imm(20)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v0),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i3 = InstId(insts.len() as u32); // B1 terminator
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i4 = InstId(insts.len() as u32); // B2 terminator
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i5 = InstId(insts.len() as u32); // B3: use v0
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "merge_clobber".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i1, i2],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i3],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i4],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i5],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // POST: inject the B1-edge clobber `v0 <- v1` (writes v1's value into
        // v0's home X0 on the B1 edge only). B2 leaves X0 untouched.
        let mut post = pre.clone();
        let clobber = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[1].insts.insert(0, clobber);

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v1, PReg::new(1));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "a live value clobbered on one merge edge must be rejected (meet must \
             still detect the cross-edge conflict)"
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::ValueFlowMismatch { vreg, .. } if *vreg == v0
            )),
            "expected a value-flow mismatch on v0 at the post-merge use, got: {:?}",
            report.errors
        );
    }

    // =======================================================================
    // x86 PHI-FREE PATH regression suite (#63 / #64 fail-open holes, now CLOSED).
    //
    // The x86-64 ISel lowers phis to copies BEFORE register allocation, so the
    // PRE-alloc function the validator receives is PHI-FREE. The OLD
    // `value_flow_report_only` (a WHOLE-FUNCTION flag set whenever a phi-free
    // function had ANY back-edge) turned property (a) entirely OFF for such
    // functions, so #63/#64 wrong-source / merge-clobber miscompiles were
    // ACCEPTED. The combined fix computes the SPEC's own value-flow over the
    // phi-free PRE program and requires POST to reproduce exactly the id the spec
    // delivers at each use — fail-closed, per-use, EXCEPT the narrow R3
    // DEFINITE-vs-DEFINITE cross-block copy-alias carve-out (box_i32). The three
    // tests below pin both directions: the two proven holes now REJECT (one side a
    // CONFLICT, so R3 does not fire), and a valid counted loop still ACCEPTS.
    // =======================================================================

    // Build a PHI-FREE counted self-loop (the x86 post-phi-lowering shape).
    // The loop-carried induction variable is ONE vreg `v_iv` (no phi): it is
    // initialized in the preheader (`v_iv <- v0`) and re-defined on the latch by
    // a copy `v_iv <- v_next`. Returns (pre, v0, v_iv, v_next).
    //
    //  B0 (preheader): def v0 = 0; copy v_iv <- v0; branch -> B1
    //  B1 (header/body):
    //                  use v_iv                ; ORIGINAL use of the iv
    //                  def v_next = step(v_iv) ; compute next iv
    //                  <LATCH COPY here>       ; v_iv <- v_next (supplied by test)
    //                  cbranch v_next -> B1 (back), B2 (exit)
    //  B2 (exit):      ret
    //
    // There are NO phi instructions anywhere — exactly what x86 hands the
    // allocator.
    fn phi_free_loop_pre() -> (MachFunction, VReg, VReg, VReg) {
        let v0 = vreg(0); // init constant
        let v_iv = vreg(1); // loop-carried induction variable (single vreg)
        let v_next = vreg(2); // next induction value

        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_init = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_iv)],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_br = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i_use = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v_iv)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_step = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 3,
            defs: vec![MachOperand::VReg(v_next)],
            uses: vec![MachOperand::VReg(v_iv), MachOperand::Imm(1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_cbr = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v_next),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i_ret = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBC,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_TERMINATOR,
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "phi_free_loop".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i_init, i_br],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i_use, i_step, i_cbr],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![i_ret],
                    preds: vec![BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        (pre, v0, v_iv, v_next)
    }

    // -----------------------------------------------------------------------
    // HOLE 1 (PROVEN FAIL-OPEN, now CLOSED): a PHI-FREE loop whose latch copy
    // threads the WRONG source (`v_iv <- v0` — the iv never advances) instead of
    // `v_iv <- v_next` must be REJECTED.
    //
    // The OLD validator set `value_flow_report_only = true` (phi-free + back-edge)
    // and gave ZERO value-flow protection — it ACCEPTED this with errors=[]. The
    // spec-value-flow check rejects it: the SPEC threads `v_next` on the back
    // edge, so the spec's loop-header value for v_iv is CONFLICT (preheader id vs
    // v_next id). The WRONG POST latch threads `v0` on BOTH edges, so POST holds a
    // DEFINITE id (v0) where the spec is CONFLICT -> mismatch (one side CONFLICT,
    // so R3 does NOT fire) -> the in-loop `use v_iv` fails closed.
    // -----------------------------------------------------------------------
    #[test]
    fn phi_free_loop_wrong_latch_copy_rejected() {
        let (pre, v0, v_iv, v_next) = phi_free_loop_pre();

        // SPEC (pre) carries the CORRECT latch copy `v_iv <- v_next` so the spec
        // value-flow at the in-loop use is the legitimate loop recurrence.
        let mut pre = pre;
        let spec_latch = InstId(pre.insts.len() as u32);
        pre.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_iv)],
            uses: vec![MachOperand::VReg(v_next)], // correct in the spec
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let cbr_idx = pre.blocks[1].insts.len() - 1;
        pre.blocks[1].insts.insert(cbr_idx, spec_latch);

        // POST mirrors the spec but the latch copy threads the WRONG source `v0`.
        let mut post = pre.clone();
        // Replace the spec latch copy with a wrong one (same InstId slot via a new
        // inserted inst; the spec's copy stays in `pre` only).
        post.insts[spec_latch.0 as usize] = MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_iv)],
            uses: vec![MachOperand::VReg(v0)], // WRONG: re-threads the init; iv never advances.
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v_iv, PReg::new(1));
        allocation.insert(v_next, PReg::new(2));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "x86 phi-free loop with a WRONG latch copy (v_iv<-v0) must be REJECTED \
             (#63/#64 fail-open hole), got errors={:?}",
            report.errors
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::ValueFlowMismatch { vreg, .. } if *vreg == v_iv
            )),
            "expected a value-flow mismatch on the in-loop use of v_iv, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // POSITIVE (NO FALSE POSITIVE): a CORRECT phi-free counted loop whose latch
    // copy threads the RIGHT source (`v_iv <- v_next`) must still VALIDATE.
    //
    // The false-positive guard for the spec-value-flow fix: POST reproduces the
    // spec's value-flow exactly (the loop-header CONFLICT on both sides), so the
    // in-cycle use's CONFLICT matches the spec's CONFLICT and the valid loop
    // validates. Property (a) is now fail-closed on x86 loops, so this MUST NOT
    // regress to a false reject.
    // -----------------------------------------------------------------------
    #[test]
    fn phi_free_loop_correct_latch_copy_validates() {
        let (pre, v0, v_iv, v_next) = phi_free_loop_pre();

        // Both spec and post carry the CORRECT latch copy `v_iv <- v_next`.
        let mut pre = pre;
        let latch = InstId(pre.insts.len() as u32);
        pre.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_iv)],
            uses: vec![MachOperand::VReg(v_next)], // CORRECT: thread the updated iv.
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let cbr_idx = pre.blocks[1].insts.len() - 1;
        pre.blocks[1].insts.insert(cbr_idx, latch);

        let post = pre.clone();

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v_iv, PReg::new(1));
        allocation.insert(v_next, PReg::new(2));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            report.is_valid(),
            "a CORRECT phi-free counted loop (v_iv<-v_next) must validate with NO \
             false positive, got errors={:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // HOLE 2 (PROVEN FAIL-OPEN, now CLOSED): an ACYCLIC forward-merge clobber
    // (#53) plus an UNRELATED self-loop must be REJECTED.
    //
    // The OLD code computed `value_flow_report_only` ONCE PER FUNCTION, so a
    // single unrelated loop disabled property (a) for the ACYCLIC merge too — the
    // ubiquitous "loop + if/else" shape silently lost #53 protection. The fix
    // makes property (a) PER-USE (keyed on the use's exact spec value), so an
    // acyclic merge in a loop-containing function stays fail-closed: the
    // acyclic-merge use of v0 is NOT in the B4 cycle, the spec delivers a DEFINITE
    // v0.id there, and the injected B1-edge clobber makes POST CONFLICT -> reject
    // (spec DEFINITE vs POST CONFLICT, so R3 does NOT fire).
    //
    //  B0 (entry): def v0; def v1; cbranch -> B1, B2
    //  B1: copy v0 <- v1  (CLOBBER, injected in POST); branch -> B3
    //  B2: branch -> B3                                (v0 survives here)
    //  B3 (merge): use v0; branch -> B4                (#53 clobbered use)
    //  B4 (loop hdr): def vL; cbranch vL -> B4 (back), B5   (UNRELATED self-loop)
    //  B5 (exit): ret
    // -----------------------------------------------------------------------
    #[test]
    fn acyclic_merge_clobber_with_unrelated_loop_rejected() {
        let v0 = vreg(0);
        let v1 = vreg(1);
        let v_l = vreg(2); // unrelated self-loop variable

        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(10)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v1)],
            uses: vec![MachOperand::Imm(20)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v0),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i3 = InstId(insts.len() as u32); // B1 terminator
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i4 = InstId(insts.len() as u32); // B2 terminator
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(3))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i5 = InstId(insts.len() as u32); // B3: use v0
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i6 = InstId(insts.len() as u32); // B3 -> B4
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(4))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i7 = InstId(insts.len() as u32); // B4: def vL
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v_l)],
            uses: vec![MachOperand::Imm(0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i8 = InstId(insts.len() as u32); // B4: cbranch vL -> B4, B5
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v_l),
                MachOperand::Block(BlockId(4)),
                MachOperand::Block(BlockId(5)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i9 = InstId(insts.len() as u32); // B5: ret
        insts.push(MachInst {
            opcode: 0xBC,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_TERMINATOR,
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "acyclic_merge_plus_loop".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i1, i2],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i3],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i4],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i5, i6],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: vec![BlockId(4)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i7, i8],
                    preds: vec![BlockId(3), BlockId(4)],
                    succs: vec![BlockId(4), BlockId(5)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![i9],
                    preds: vec![BlockId(4)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![
                BlockId(0),
                BlockId(1),
                BlockId(2),
                BlockId(3),
                BlockId(4),
                BlockId(5),
            ],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // POST: inject the B1-edge clobber `v0 <- v1`. Unrelated B4 loop unchanged.
        let mut post = pre.clone();
        let clobber = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::VReg(v1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[1].insts.insert(0, clobber);

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v1, PReg::new(1));
        allocation.insert(v_l, PReg::new(2));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "an acyclic forward-merge clobber of v0 must be REJECTED even when the \
             function ALSO contains an unrelated loop (#53 must stay fail-closed \
             per-use), got errors={:?}",
            report.errors
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::ValueFlowMismatch { vreg, .. } if *vreg == v0
            )),
            "expected a value-flow mismatch on v0 at the acyclic merge use, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // R3 CARVE-OUT (NO FALSE POSITIVE): a PHI-FREE ACYCLIC cross-block
    // copy-alias (the box_i32 shape) where POST's home for the used value holds
    // a DEFINITE-but-different id must be ACCEPTED (report-only, NOT rejected).
    //
    // This is the case the combined design relaxes and cc65069 alone would have
    // FALSE-REJECTED. The SPEC defines `v2` directly in B0, so the spec
    // value-flow at the use in B2 is DEFINITE `Some(v2.id)`. POST interposes a
    // cross-block copy `v2 <- v0` in B1 (a coalesced representative / two-address
    // fixup the block-local numbering cannot tie back to v2), so v2's home (X2)
    // exits B1 holding DEFINITE `Some(v0.id)`. At the B2 use: found = Some(v0),
    // expected = Some(v2), w != v — BOTH DEFINITE -> R3 fires -> report-only.
    //
    // There is NO merge (straight B0->B1->B2 chain), so the home is never a
    // CONFLICT: this is exactly the DEFINITE-vs-DEFINITE quadrant R3 covers, and
    // distinct from the wrong-latch (spec CONFLICT, POST DEFINITE) and merge-
    // clobber (spec DEFINITE, POST CONFLICT) cases that STILL fail closed.
    //
    //  B0: def v0; def v2; branch -> B1
    //  B1: copy v2 <- v0  (POST only — cross-block alias); branch -> B2
    //  B2: use v2; ret
    // -----------------------------------------------------------------------
    #[test]
    fn phi_free_cross_block_copy_alias_accepted() {
        let v0 = vreg(0);
        let v2 = vreg(2);

        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32); // B0: def v0
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(7)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32); // B0: def v2 (same constant value)
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::Imm(7)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i2 = InstId(insts.len() as u32); // B0 -> B1
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i3 = InstId(insts.len() as u32); // B1 -> B2
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(2))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i4 = InstId(insts.len() as u32); // B2: use v2
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v2)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i5 = InstId(insts.len() as u32); // B2: ret
        insts.push(MachInst {
            opcode: 0xBC,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_TERMINATOR,
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "cross_block_alias".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i1, i2],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i3],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i4, i5],
                    preds: vec![BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // POST: interpose a cross-block copy `v2 <- v0` in B1 (the alias the
        // block-local value-numbering cannot resolve). v2's home now holds v0's id
        // at the B2 use — a DEFINITE-but-different value.
        let mut post = pre.clone();
        let alias = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v2)],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[1].insts.insert(0, alias);

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v2, PReg::new(2));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            report.is_valid(),
            "a phi-free acyclic cross-block copy-alias (DEFINITE-vs-DEFINITE, the \
             box_i32 shape) must be ACCEPTED report-only, not falsely rejected, \
             got errors={:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // RESIDUAL (a) ELIMINATED: a PHI-FREE loop whose latch threads a WRONG
    // SECOND source — keeping POST at a CONFLICT but over a DIFFERENT source set
    // than the spec — must be REJECTED by value-flow ALONE (not the interference
    // backstop).
    //
    // Shape (phi-free x86 post-phi-lowering): an induction variable `v_iv` with a
    // genuine recurrence. The body computes BOTH the correct next value `v_next`
    // and an UNRELATED `v_alt`. The spec's latch threads `v_next`, so the spec's
    // loop-header value for `v_iv` is `Conflict({v0, v_next})`. The buggy POST
    // latch threads `v_alt` instead, so POST's `v_iv` home holds
    // `Conflict({v0, v_alt})` — STILL a conflict (so the OLD single-`None` lattice
    // compared it EQUAL to the spec conflict and ACCEPTED the miscompile), but over
    // a DIFFERENT set. The set-valued lattice makes `{v0, v_next} != {v0, v_alt}`,
    // so the in-loop `use v_iv` is rejected.
    //
    // Critically, `v_iv` (X1) and `v_alt` (X3) live in DISTINCT registers and do
    // not interfere, so the interference backstop (b) is SILENT here: this is
    // exactly the residual-(a) class that previously relied on the differential
    // oracle, now pinned by property (a) directly.
    //
    //  B0 (preheader): def v0=0; copy v_iv <- v0; br B1
    //  B1 (body):      use v_iv; def v_next=step(v_iv); def v_alt=alt(v_iv);
    //                  <LATCH>; cbranch v_next -> B1 (back), B2 (exit)
    //  B2 (exit):      ret
    // -----------------------------------------------------------------------
    #[test]
    fn phi_free_loop_wrong_second_source_latch_rejected() {
        let v0 = vreg(0); // init constant
        let v_iv = vreg(1); // induction variable
        let v_next = vreg(2); // correct next value (spec latch source)
        let v_alt = vreg(3); // unrelated value (wrong latch source in POST)

        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32); // B0: def v0 = 0
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_init = InstId(insts.len() as u32); // B0: copy v_iv <- v0
        insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_iv)],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_br = InstId(insts.len() as u32); // B0 -> B1
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i_use = InstId(insts.len() as u32); // B1: use v_iv (ORIGINAL use)
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v_iv)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_step = InstId(insts.len() as u32); // B1: def v_next = step(v_iv)
        insts.push(MachInst {
            opcode: 3,
            defs: vec![MachOperand::VReg(v_next)],
            uses: vec![MachOperand::VReg(v_iv), MachOperand::Imm(1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_alt = InstId(insts.len() as u32); // B1: def v_alt = alt(v_iv)
        insts.push(MachInst {
            opcode: 4,
            defs: vec![MachOperand::VReg(v_alt)],
            uses: vec![MachOperand::VReg(v_iv), MachOperand::Imm(2)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        // LATCH copy slot (filled per spec/post below), then the cbranch.
        let i_latch = InstId(insts.len() as u32); // B1: v_iv <- v_next (spec)
        insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_iv)],
            uses: vec![MachOperand::VReg(v_next)], // spec: thread the correct next iv
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_cbr = InstId(insts.len() as u32); // B1: cbranch v_next -> B1, B2
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v_next),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i_ret = InstId(insts.len() as u32); // B2: ret
        insts.push(MachInst {
            opcode: 0xBC,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_TERMINATOR,
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "phi_free_wrong_second_source".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i_init, i_br],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i_use, i_step, i_alt, i_latch, i_cbr],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![i_ret],
                    preds: vec![BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 4,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // POST mirrors the spec but the latch threads the WRONG SECOND source
        // `v_alt` instead of `v_next`. POST's v_iv home is still a CONFLICT (the
        // preheader threads v0, the latch threads v_alt), but over `{v0, v_alt}`,
        // a DIFFERENT set than the spec's `{v0, v_next}`.
        let mut post = pre.clone();
        post.insts[i_latch.0 as usize] = MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_iv)],
            uses: vec![MachOperand::VReg(v_alt)], // WRONG second source
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };

        // Distinct registers: v_iv and v_alt do NOT interfere, so interference (b)
        // is silent — value-flow (a) must do the rejecting.
        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v_iv, PReg::new(1));
        allocation.insert(v_next, PReg::new(2));
        allocation.insert(v_alt, PReg::new(3));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "a phi-free loop whose latch threads a WRONG SECOND source (POST \
             conflict over a DIFFERENT set than the spec) must be REJECTED by \
             value-flow alone (residual (a) eliminated), got errors={:?}",
            report.errors
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::ValueFlowMismatch { vreg, .. } if *vreg == v_iv
            )),
            "expected a value-flow mismatch on the in-loop use of v_iv (different \
             conflict sets), got: {:?}",
            report.errors
        );
        // The interference backstop must NOT be what catches this (prove value-flow
        // did the work): v_iv and v_alt are in distinct registers.
        assert!(
            !report
                .errors
                .iter()
                .any(|e| matches!(e, ValidationError::InterferenceViolation { .. })),
            "residual (a) must be caught by VALUE-FLOW, not interference; got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // RESIDUAL (a) FALSE-POSITIVE GUARD: a CORRECT phi-free loop whose body also
    // computes an unrelated value must STILL VALIDATE. The set-valued lattice must
    // not over-reject: the spec and POST conflict sets are IDENTICAL `{v0, v_next}`
    // for the correctly-threaded iv, so the in-loop use validates.
    // -----------------------------------------------------------------------
    #[test]
    fn phi_free_loop_correct_with_extra_value_validates() {
        let v0 = vreg(0);
        let v_iv = vreg(1);
        let v_next = vreg(2);
        let v_alt = vreg(3);

        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_init = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_iv)],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_br = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i_use = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v_iv)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_step = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 3,
            defs: vec![MachOperand::VReg(v_next)],
            uses: vec![MachOperand::VReg(v_iv), MachOperand::Imm(1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_alt = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 4,
            defs: vec![MachOperand::VReg(v_alt)],
            uses: vec![MachOperand::VReg(v_iv), MachOperand::Imm(2)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_latch = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_iv)],
            uses: vec![MachOperand::VReg(v_next)], // CORRECT
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_cbr = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v_next),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i_ret = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBC,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_TERMINATOR,
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "phi_free_correct_extra".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i_init, i_br],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i_use, i_step, i_alt, i_latch, i_cbr],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![i_ret],
                    preds: vec![BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 4,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let post = pre.clone();

        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v_iv, PReg::new(1));
        allocation.insert(v_next, PReg::new(2));
        allocation.insert(v_alt, PReg::new(3));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            report.is_valid(),
            "a CORRECT phi-free loop with an extra body value must validate (no \
             residual-(a) false positive — identical conflict sets), got errors={:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // (R5) COPY-INTERMEDIATE ROOT-CLOSURE RECONCILIATION — the decision boundary.
    //
    // R5 accepts a `found` vs `expected` value-flow mismatch iff the two symbols
    // have the SAME architectural value-source set (`CopyEquiv::root_closure`).
    // This unit test pins BOTH directions on a controlled copy graph:
    //   v10 = const, v11 = const        (distinct non-copy ROOTS)
    //   v20 = const                     (an UNRELATED distinct root)
    //   v30 <- v10 ; v30 <- v11         (a 0/1-style phi-free MERGE: reach {10,11})
    //   v31 <- v30                      (a COPY-INTERMEDIATE of the merge: reach {10,11})
    //
    // ACCEPT (copy-intermediate only): the POST-resolved `Conflict({10,11})` and the
    // spec's `Conflict({10,11,31})` (sparse walk reintroduced the intermediate `31`)
    // have EQUAL root closures — the exact `LineProgramHeader::parse` gimli shape.
    // REJECT (a real distinct root): adding `20` (a genuine non-copy root the merge
    // can never hold — a forward-merge clobber / wrong source) makes the closures
    // UNEQUAL, so R5 stays fail-closed. A copy provably cannot change a value, so
    // equal closures ⇔ same value; a real clobber always perturbs the root set.
    // -----------------------------------------------------------------------
    #[test]
    fn r5_root_closure_reconciles_copy_intermediate_not_alien() {
        let mk_def = |v: VReg, imm: i64| MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v)],
            uses: vec![MachOperand::Imm(imm)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let mk_copy = |dst: VReg, src: VReg| MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(dst)],
            uses: vec![MachOperand::VReg(src)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let (v10, v11, v20, v30, v31) = (vreg(10), vreg(11), vreg(20), vreg(30), vreg(31));
        let insts = vec![
            mk_def(v10, 0),
            mk_def(v11, 1),
            mk_def(v20, 2),
            mk_copy(v30, v10), // v30 <- v10   (first merge def)
            mk_copy(v30, v11), // v30 <- v11   (second merge def -> reach {10,11})
            mk_copy(v31, v30), // v31 <- v30   (copy-intermediate of the merge)
            MachInst {
                opcode: 0xBC,
                defs: vec![],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_TERMINATOR,
                tied_operands: vec![],
            },
        ];
        let n = insts.len() as u32;
        let pre = MachFunction {
            name: "r5_root_closure".into(),
            insts,
            blocks: vec![MachBlock {
                insts: (0..n).map(InstId).collect(),
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 32,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let ce = CopyEquiv::build(&pre);
        // The merge and its copy-intermediate reach the same two roots.
        assert_eq!(ce.reach.get(&30), Some(&[10u32, 11].into_iter().collect()));
        assert_eq!(ce.reach.get(&31), Some(&[10u32, 11].into_iter().collect()));

        let merge = Sym::Conflict([10u32, 11].into_iter().collect());
        let with_intermediate = Sym::Conflict([10u32, 11, 31].into_iter().collect());
        let with_alien = Sym::Conflict([10u32, 11, 20].into_iter().collect());

        // ACCEPT: a copy-intermediate difference leaves the root closure unchanged.
        assert_eq!(
            ce.root_closure(&merge),
            ce.root_closure(&with_intermediate),
            "R5 must reconcile a copy-intermediate-only conflict-set difference"
        );
        // ACCEPT (mirror): a DEFINITE copy of the merge matches the merge conflict.
        assert_eq!(
            ce.root_closure(&Sym::Defined(31)),
            ce.root_closure(&merge),
            "R5 must reconcile a definite copy of the merge against the merge"
        );
        // REJECT: an unrelated distinct root perturbs the closure -> fail-closed.
        assert_ne!(
            ce.root_closure(&merge),
            ce.root_closure(&with_alien),
            "R5 must NOT reconcile a conflict carrying a genuine distinct root \
             (a forward-merge clobber must stay fail-closed)"
        );
        // REJECT: a conflict that DROPS a required root (recurrence-stop shape).
        assert_ne!(
            ce.root_closure(&Sym::Conflict([10u32, 20].into_iter().collect())),
            ce.root_closure(&merge),
            "R5 must NOT reconcile a conflict over a different root set"
        );
    }

    // -----------------------------------------------------------------------
    // (R5) ADVERSARIAL: a phi-free acyclic MERGE whose one edge threads a genuine
    // UNRELATED constant into the merge home is a real forward-merge clobber and
    // MUST stay REJECTED — R5's root-closure carve-out must not mask it.
    //
    //   B0: def v_cond; cbranch -> B1, B2
    //   B1: def v_a = 0 ; v_m <- v_a ; br B3
    //   B2: def v_b = 1 ; def v_c = 2 ; v_m <- v_b (SPEC) / v_m <- v_c (POST) ; br B3
    //   B3: use v_m ; ret
    //
    // SPEC value-flow at the merge use is `Conflict({v_a, v_b})`; POST threads the
    // ALIEN `v_c` on the B2 edge, so POST holds `Conflict({v_a, v_c})`. `v_c` is a
    // non-copy root NOT reachable by the merge, so `roots(found) != roots(expected)`
    // and R5 does not fire -> value-flow REJECTS.
    // -----------------------------------------------------------------------
    #[test]
    fn r5_acyclic_merge_alien_root_clobber_rejected() {
        let (v_cond, v_a, v_b, v_c, v_m) = (vreg(0), vreg(1), vreg(2), vreg(3), vreg(4));
        let def = |v: VReg, imm: i64| MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v)],
            uses: vec![MachOperand::Imm(imm)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let copy = |dst: VReg, src: VReg| MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(dst)],
            uses: vec![MachOperand::VReg(src)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let insts = vec![
            def(v_cond, 0), // i0  B0
            MachInst {
                // i1  B0: cbranch v_cond -> B1, B2
                opcode: 0xBB,
                defs: vec![],
                uses: vec![
                    MachOperand::VReg(v_cond),
                    MachOperand::Block(BlockId(1)),
                    MachOperand::Block(BlockId(2)),
                ],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            def(v_a, 0),    // i2  B1
            copy(v_m, v_a), // i3  B1: v_m <- v_a
            MachInst {
                // i4  B1: br B3
                opcode: 0xBA,
                defs: vec![],
                uses: vec![MachOperand::Block(BlockId(3))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            def(v_b, 1),    // i5  B2
            def(v_c, 2),    // i6  B2
            copy(v_m, v_b), // i7  B2: v_m <- v_b (SPEC; POST overrides to v_c)
            MachInst {
                // i8  B2: br B3
                opcode: 0xBA,
                defs: vec![],
                uses: vec![MachOperand::Block(BlockId(3))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            MachInst {
                // i9  B3: use v_m (ORIGINAL use at the merge)
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(v_m)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            },
            MachInst {
                // i10 B3: ret
                opcode: 0xBC,
                defs: vec![],
                uses: vec![],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_TERMINATOR,
                tied_operands: vec![],
            },
        ];
        let pre = MachFunction {
            name: "r5_acyclic_merge_clobber".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: Vec::new(),
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2), InstId(3), InstId(4)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(5), InstId(6), InstId(7), InstId(8)],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(3)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(9), InstId(10)],
                    preds: vec![BlockId(1), BlockId(2)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)],
            entry_block: BlockId(0),
            next_vreg: 5,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        // POST threads the ALIEN v_c into the merge home on the B2 edge.
        let mut post = pre.clone();
        post.insts[7] = copy(v_m, v_c);

        let mut allocation = BTreeMap::new();
        allocation.insert(v_cond, PReg::new(0));
        allocation.insert(v_a, PReg::new(1));
        allocation.insert(v_b, PReg::new(2));
        allocation.insert(v_c, PReg::new(3));
        allocation.insert(v_m, PReg::new(4));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "a phi-free merge that threads an ALIEN constant into the merge home \
             must be REJECTED (R5 root-closure must not mask a real forward-merge \
             clobber), got errors={:?}",
            report.errors
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::ValueFlowMismatch { vreg, .. } if *vreg == v_m
            )),
            "expected a value-flow mismatch on the merge value v_m, got: {:?}",
            report.errors
        );
    }

    // -----------------------------------------------------------------------
    // CALL-RESULT LOOP-CARRIED ACCUMULATOR (m102 — the generic-call-accumulator
    // miscompile, REGALLOC SIDE). A loop-carried accumulator `s` whose in-loop
    // update is the RESULT of a `Call` (`s = s + x` via `<i32 as Add>::add`):
    // the spec latch threads the call result `v_res` into the accumulator's home,
    // so the spec value-flow at the in-loop accumulator use is the loop recurrence
    // CONFLICT (preheader init id vs call-result id). The buggy POST latch instead
    // re-threads the PRE-call accumulator value (`v_acc <- v0` — the call result
    // is DROPPED, the accumulator keeps `init`), so POST's home holds a DEFINITE id
    // (v0) where the spec is CONFLICT. One side is a CONFLICT, so R3 does NOT fire,
    // and value-flow REJECTS the in-loop accumulator use.
    //
    // This is the regalloc-validator backstop for the bug whose ROOT CAUSE is the
    // bridge's `compute_loop_header_params` (fixed there: a `Call`-terminator
    // destination local is now a scalar def-site, so a call-updated loop-carried
    // accumulator becomes a header phi and the result is threaded through a VREG
    // the value-flow can follow — making exactly this wrong back-edge detectable
    // here rather than invisible). The call CLOBBERS its result register and the
    // caller-saved set as `implicit_defs`; the result-capture (`v_res`) reads the
    // result preg via `implicit_uses`. Modeled so the wrong threading is REFUTED,
    // never silently accepted (the soundness obligation: a Call-def whose result a
    // back-edge restore clobbers must FAIL closed).
    //
    //  B0 (preheader): def v0 = init; copy v_acc <- v0; br B1
    //  B1 (body):      use v_acc; <CALL clobbers caller-saved>; def v_res = result;
    //                  <LATCH: spec `v_acc <- v_res`, POST `v_acc <- v0`>;
    //                  cbranch -> B1 (back), B2 (exit)
    //  B2 (exit):      use v_acc; ret
    // -----------------------------------------------------------------------
    #[test]
    fn phi_free_loop_call_result_accumulator_wrong_latch_rejected() {
        let v0 = vreg(0); // init constant (the accumulator's entry value)
        let v_acc = vreg(1); // loop-carried accumulator `s`
        let v_res = vreg(2); // the Call RESULT (`s + x`)

        // Caller-saved clobber set the call invalidates; the result register is
        // among them (the call writes its result there).
        let result_preg = PReg::new(10);
        let clobber_pregs = [PReg::new(11), PReg::new(12), result_preg];

        let mut insts = Vec::new();
        let i0 = InstId(insts.len() as u32); // B0: def v0 = init
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(v0)],
            uses: vec![MachOperand::Imm(5)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_init = InstId(insts.len() as u32); // B0: copy v_acc <- v0
        insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_acc)],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_br = InstId(insts.len() as u32); // B0 -> B1
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i_use = InstId(insts.len() as u32); // B1: use v_acc (call ARG = the accumulator)
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v_acc)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_call = InstId(insts.len() as u32); // B1: CALL — clobbers caller-saved
        insts.push(MachInst {
            opcode: 0x3A, // call
            defs: vec![],
            uses: vec![MachOperand::Imm(0)],
            implicit_defs: clobber_pregs.to_vec(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_CALL,
            tied_operands: vec![],
        });
        let i_res = InstId(insts.len() as u32); // B1: def v_res = result (reads result preg)
        insts.push(MachInst {
            opcode: 4,
            defs: vec![MachOperand::VReg(v_res)],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: vec![result_preg],
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_latch = InstId(insts.len() as u32); // B1: LATCH copy (spec: v_acc <- v_res)
        insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_acc)],
            uses: vec![MachOperand::VReg(v_res)], // CORRECT in the spec: thread the call result
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_cbr = InstId(insts.len() as u32); // B1: cbranch -> B1 (back), B2
        insts.push(MachInst {
            opcode: 0xBB,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(v_res),
                MachOperand::Block(BlockId(1)),
                MachOperand::Block(BlockId(2)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });
        let i_exit_use = InstId(insts.len() as u32); // B2: use v_acc (the loop result)
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(v_acc)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i_ret = InstId(insts.len() as u32); // B2: ret
        insts.push(MachInst {
            opcode: 0xBC,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_TERMINATOR,
            tied_operands: vec![],
        });

        let pre = MachFunction {
            name: "phi_free_call_acc".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i_init, i_br],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i_use, i_call, i_res, i_latch, i_cbr],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![i_exit_use, i_ret],
                    preds: vec![BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // POST: the buggy back-edge restore — the latch threads the PRE-call
        // accumulator `v0` instead of the call result `v_res`. The call result is
        // DROPPED; the accumulator keeps `init` forever (the m102 miscompile).
        let mut post = pre.clone();
        post.insts[i_latch.0 as usize] = MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(v_acc)],
            uses: vec![MachOperand::VReg(v0)], // WRONG: restores the stale pre-call accumulator
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };

        // Distinct homes so the interference backstop stays SILENT — value-flow
        // must do the work. The accumulator's home is NOT a clobbered caller-saved
        // register (a correct allocation would save it across the call), so the
        // rejection is purely the wrong loop-carried threading, not a clobber.
        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(0));
        allocation.insert(v_acc, PReg::new(1));
        allocation.insert(v_res, PReg::new(2));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "a phi-free loop whose accumulator is updated by a CALL RESULT, but whose \
             POST back-edge RESTORES the pre-call accumulator (dropping the call \
             result — the m102 generic-call-accumulator miscompile), must be \
             REJECTED, got errors={:?}",
            report.errors
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::ValueFlowMismatch { vreg, .. } if *vreg == v_acc
            )),
            "expected a value-flow mismatch on the loop-carried accumulator use \
             (spec CONFLICT vs POST DEFINITE init), got: {:?}",
            report.errors
        );
    }

    // =======================================================================
    // DECISION-IDENTITY ORACLE for the sparse walks.
    //
    // The shipped validator restricts its three super-linear computations for
    // scale (TY's ~7,300-block fused-BFS parent loop at O0):
    //
    //   1. `check_interference`: per-location sweep instead of the all-pairs
    //      interval scan;
    //   2. `compute_pre_expected`: key domain restricted to copy destinations,
    //      persisted exits to per-block live-out tracked keys;
    //   3. `compute_exit_states_fixpoint`: persisted exits restricted to
    //      live-out locations.
    //
    // Each restriction carries a written observation-equivalence proof at its
    // definition. These tests are the EMPIRICAL backstop: the historical dense
    // implementations are kept here as the reference oracle, and randomized
    // (pre, post, result) triples — valid AND broken, phi-bearing AND
    // phi-free, cyclic AND acyclic — must produce IDENTICAL ValidationReport
    // error lists (same errors, same order).
    // =======================================================================

    use super::{
        CheckValueFlowFinalInputs, CopyEquiv, LocState, PhiSpecs, PreExpected, ValidationReport,
        apply_inst, apply_inst_pre, block_entry_state, build_location_map, check_phis_eliminated,
        check_physreg_interference, check_value_flow_final, collect_function_vregs,
        collect_phi_specs, collect_remat_reload_temps, overlap_point, pre_block_entry_state,
        pre_has_phis,
    };
    use crate::linear_scan::SpillInfo;
    use crate::liveness::compute_live_intervals;
    use crate::phi_elim::IR_COPY_OPCODE;
    use crate::spill::{PSEUDO_SPILL_LOAD, PSEUDO_SPILL_STORE};

    /// Historical all-pairs interference check (the reference oracle).
    fn check_interference_reference(
        post: &MachFunction,
        locations: &BTreeMap<VReg, Location>,
        result: &AllocationResult,
        report: &mut ValidationReport,
    ) {
        let liveness = compute_live_intervals(post);
        let intervals: Vec<_> = liveness.intervals.values().collect();

        for (i, a) in intervals.iter().enumerate() {
            let Some(&loc_a) = locations.get(&a.vreg) else {
                continue;
            };
            for b in intervals.iter().skip(i + 1) {
                let Some(&loc_b) = locations.get(&b.vreg) else {
                    continue;
                };
                if loc_a != loc_b {
                    continue;
                }
                if a.vreg == b.vreg {
                    continue;
                }
                if a.overlaps(b) {
                    let point = overlap_point(a, b).unwrap_or(0);
                    report.errors.push(ValidationError::InterferenceViolation {
                        a: a.vreg,
                        b: b.vreg,
                        loc: loc_a,
                        point,
                    });
                }
            }
        }

        for spill in &result.spills {
            if let Some(&preg) = result.allocation.get(&spill.vreg) {
                report.errors.push(ValidationError::Unsupported(format!(
                    "{} is both spilled to slot{} and allocated to {} — ambiguous home",
                    spill.vreg, spill.slot.0, preg
                )));
            }
        }
    }

    /// Historical DENSE forward fixpoint over location states (no persisted-key
    /// restriction) — the reference oracle.
    fn compute_exit_states_fixpoint_reference(
        pre: &MachFunction,
        post: &MachFunction,
        locations: &BTreeMap<VReg, Location>,
        phi_specs: &PhiSpecs,
        spec_exit: Option<&BTreeMap<BlockId, super::Rc<super::PreState>>>,
    ) -> BTreeMap<BlockId, LocState> {
        let original_inst_count = pre.insts.len() as u32;
        let mut exit_states: BTreeMap<BlockId, LocState> = BTreeMap::new();
        let max_passes = post.block_order.len().saturating_mul(2).saturating_add(2);
        for _ in 0..max_passes {
            let mut changed = false;
            for &block_id in &post.block_order {
                let Some(block) = post.blocks.get(block_id.0 as usize) else {
                    continue;
                };
                let mut state = block_entry_state(
                    block,
                    &exit_states,
                    locations,
                    phi_specs,
                    block_id,
                    spec_exit,
                );
                for &inst_id in &block.insts {
                    let Some(inst) = post.insts.get(inst_id.0 as usize) else {
                        continue;
                    };
                    let spec = super::spec_inst(pre, inst_id, original_inst_count);
                    apply_inst(inst, spec, locations, &mut state);
                }
                match exit_states.get(&block_id) {
                    Some(prev) if *prev == state => {}
                    _ => {
                        exit_states.insert(block_id, state);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        exit_states
    }

    /// Historical DENSE PRE-spec value-flow (every vreg tracked, no persisted-key
    /// restriction) — the reference oracle. Tracking EVERY vreg of the function
    /// makes the sparse-capable helpers behave exactly like the historical dense
    /// code (every def is inserted, every copy propagates). Returns the per-use
    /// expected map plus the dense converged exit states (Rc-wrapped for type
    /// compatibility with the shared spec-exit consumers).
    fn compute_pre_spec_flow_reference(pre: &MachFunction) -> super::PreSpecFlow {
        let all_vregs = collect_function_vregs(pre);
        let mut exit_states: BTreeMap<BlockId, super::PreState> = BTreeMap::new();
        let max_passes = pre.block_order.len().saturating_mul(2).saturating_add(2);
        for _ in 0..max_passes {
            let mut changed = false;
            for &block_id in &pre.block_order {
                let Some(block) = pre.blocks.get(block_id.0 as usize) else {
                    continue;
                };
                let mut state =
                    pre_block_entry_state(block, &exit_states, pre, block_id, &all_vregs);
                for &inst_id in &block.insts {
                    let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                        continue;
                    };
                    apply_inst_pre(inst, &mut state, &all_vregs);
                }
                match exit_states.get(&block_id) {
                    Some(prev) if *prev == state => {}
                    _ => {
                        exit_states.insert(block_id, state);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        let mut expected: PreExpected = BTreeMap::new();
        for &block_id in &pre.block_order {
            let Some(block) = pre.blocks.get(block_id.0 as usize) else {
                continue;
            };
            let mut state = pre_block_entry_state(block, &exit_states, pre, block_id, &all_vregs);
            for &inst_id in &block.insts {
                let Some(inst) = pre.insts.get(inst_id.0 as usize) else {
                    continue;
                };
                if !inst.flags.is_phi() {
                    for op in &inst.uses {
                        if let Some(v) = op.as_vreg() {
                            let val = state.get(&v).cloned().unwrap_or(super::Sym::Defined(v.id));
                            expected.insert((inst_id, v), val);
                        }
                    }
                }
                apply_inst_pre(inst, &mut state, &all_vregs);
            }
        }
        super::PreSpecFlow {
            expected,
            exit_states: exit_states
                .into_iter()
                .map(|(k, v)| (k, super::Rc::new(v)))
                .collect(),
        }
    }

    /// Reference `validate_allocation`: identical structure and recording code,
    /// but driven by the dense reference computations above.
    fn validate_allocation_reference(
        pre: &MachFunction,
        post: &MachFunction,
        result: &AllocationResult,
    ) -> ValidationReport {
        let mut report = ValidationReport::default();
        let locations = build_location_map(result);
        check_phis_eliminated(post, &mut report);
        check_interference_reference(post, &locations, result, &mut report);
        // (b') phys-reg interference is a single deterministic pass (not one of the
        // three sparse/dense-restricted computations), so the reference runs the
        // SAME production check at the SAME position to keep decision identity.
        check_physreg_interference(post, &locations, &mut report);

        let phi_specs = collect_phi_specs(pre, post);
        let original_inst_count = pre.insts.len() as u32;
        let remat_reload_temps = collect_remat_reload_temps(post, &locations, original_inst_count);
        let pre_vregs = collect_function_vregs(pre);
        let phi_free = !pre_has_phis(pre);
        let skip_top_reads = phi_free;
        let relax_definite_alias = phi_free;
        let removed_copy_dsts = super::collect_removed_original_copy_dsts(pre, post);
        let spec_flow = if phi_free || !removed_copy_dsts.is_empty() {
            Some(compute_pre_spec_flow_reference(pre))
        } else {
            None
        };
        let empty_expected = PreExpected::new();
        let pre_expected = spec_flow
            .as_ref()
            .map(|f| &f.expected)
            .unwrap_or(&empty_expected);
        let spec_exit = if !phi_free && !removed_copy_dsts.is_empty() {
            spec_flow.as_ref().map(|f| &f.exit_states)
        } else {
            None
        };
        let exit_states =
            compute_exit_states_fixpoint_reference(pre, post, &locations, &phi_specs, spec_exit);
        let copy_equiv = if phi_free {
            Some(CopyEquiv::build(pre))
        } else {
            None
        };
        check_value_flow_final(CheckValueFlowFinalInputs {
            pre,
            post,
            locations: &locations,
            phi_specs: &phi_specs,
            exit_states: &exit_states,
            pre_expected,
            spec_exit,
            removed_copy_dsts: &removed_copy_dsts,
            original_inst_count,
            remat_reload_temps: &remat_reload_temps,
            pre_vregs: &pre_vregs,
            phi_free,
            skip_top_reads,
            relax_definite_alias,
            copy_equiv: copy_equiv.as_ref(),
            report: &mut report,
        });
        super::check_spill_discipline(post, &locations, &mut report);
        // (e) slot-init dominance — a single deterministic dataflow pass (not a
        // sparse/dense-restricted computation), so the reference runs the SAME
        // production check at the SAME position to keep decision identity with
        // the sparse validator.
        super::check_slot_init_dominance(post, &mut report);
        report
    }

    /// Tiny deterministic RNG (xorshift64), mirroring the post_ra_coalesce
    /// oracle harness.
    struct XorShift(u64);
    impl XorShift {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
        fn chance(&mut self, percent: u64) -> bool {
            self.below(100) < percent
        }
    }

    fn rand_vreg(rng: &mut XorShift, nv: u32) -> VReg {
        vreg(rng.below(nv as u64) as u32)
    }

    /// Generate a random (pre, post, result) triple: a small random CFG
    /// (possibly cyclic), random generic/copy/spill/clobber instructions,
    /// occasional phis, a post derived by random (sometimes WRONG) edits, and
    /// a random (sometimes inconsistent) allocation.
    fn random_triple(rng: &mut XorShift) -> (MachFunction, MachFunction, AllocationResult) {
        let nblocks = 1 + rng.below(5) as usize;
        let nv = 2 + rng.below(10) as u32;
        let nslots = 1 + rng.below(4) as u32;

        // CFG edges first (so phi uses can be index-aligned with preds).
        let mut succs: Vec<Vec<BlockId>> = vec![Vec::new(); nblocks];
        let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); nblocks];
        for (b, block_succs) in succs.iter_mut().enumerate() {
            let nsucc = rng.below(3) as usize; // 0..=2 successors, any target (loops!)
            for _ in 0..nsucc {
                let t = rng.below(nblocks as u64) as usize;
                block_succs.push(BlockId(t as u32));
                preds[t].push(BlockId(b as u32));
            }
        }

        let mut insts: Vec<MachInst> = Vec::new();
        let mut blocks: Vec<MachBlock> = Vec::new();
        for b in 0..nblocks {
            let mut block_insts: Vec<InstId> = Vec::new();
            // Occasionally a phi at block start, one use per pred.
            if !preds[b].is_empty() && rng.chance(25) {
                let mut flags = InstFlags::default();
                flags.insert(InstFlags::IS_PHI);
                let id = InstId(insts.len() as u32);
                insts.push(MachInst {
                    opcode: 7,
                    defs: vec![MachOperand::VReg(rand_vreg(rng, nv))],
                    uses: preds[b]
                        .iter()
                        .map(|_| MachOperand::VReg(rand_vreg(rng, nv)))
                        .collect(),
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags,
                    tied_operands: vec![],
                });
                block_insts.push(id);
            }
            let n_inst = 1 + rng.below(5);
            for _ in 0..n_inst {
                let id = InstId(insts.len() as u32);
                let inst = match rng.below(10) {
                    // Copy dst <- src (both pseudo-copy opcodes).
                    0 | 1 => MachInst {
                        opcode: if rng.chance(50) {
                            PSEUDO_COPY
                        } else {
                            IR_COPY_OPCODE
                        },
                        defs: vec![MachOperand::VReg(rand_vreg(rng, nv))],
                        uses: vec![MachOperand::VReg(rand_vreg(rng, nv))],
                        implicit_defs: Vec::new(),
                        implicit_uses: Vec::new(),
                        flags: InstFlags::default(),
                        tied_operands: vec![],
                    },
                    // Copy from an immediate (imm-source copy: generic-def arm).
                    2 => MachInst {
                        opcode: PSEUDO_COPY,
                        defs: vec![MachOperand::VReg(rand_vreg(rng, nv))],
                        uses: vec![MachOperand::Imm(rng.below(64) as i64)],
                        implicit_defs: Vec::new(),
                        implicit_uses: Vec::new(),
                        flags: InstFlags::default(),
                        tied_operands: vec![],
                    },
                    // Spill load dst <- slot.
                    3 => MachInst {
                        opcode: PSEUDO_SPILL_LOAD,
                        defs: vec![MachOperand::VReg(rand_vreg(rng, nv))],
                        uses: vec![MachOperand::StackSlot(StackSlotId(
                            rng.below(nslots as u64) as u32,
                        ))],
                        implicit_defs: Vec::new(),
                        implicit_uses: Vec::new(),
                        flags: InstFlags::default(),
                        tied_operands: vec![],
                    },
                    // Spill store slot <- src.
                    4 => MachInst {
                        opcode: PSEUDO_SPILL_STORE,
                        defs: vec![],
                        uses: vec![
                            MachOperand::VReg(rand_vreg(rng, nv)),
                            MachOperand::StackSlot(StackSlotId(rng.below(nslots as u64) as u32)),
                        ],
                        implicit_defs: Vec::new(),
                        implicit_uses: Vec::new(),
                        flags: InstFlags::default(),
                        tied_operands: vec![],
                    },
                    // Call-like clobber.
                    5 => MachInst {
                        opcode: 9,
                        defs: vec![],
                        uses: vec![MachOperand::VReg(rand_vreg(rng, nv))],
                        implicit_defs: vec![PReg::new(rng.below(4) as u16)],
                        implicit_uses: Vec::new(),
                        flags: InstFlags::default(),
                        tied_operands: vec![],
                    },
                    // Generic compute def <- uses.
                    _ => MachInst {
                        opcode: 0x20 + rng.below(4) as u16,
                        defs: vec![MachOperand::VReg(rand_vreg(rng, nv))],
                        uses: vec![
                            MachOperand::VReg(rand_vreg(rng, nv)),
                            MachOperand::VReg(rand_vreg(rng, nv)),
                        ],
                        implicit_defs: Vec::new(),
                        implicit_uses: Vec::new(),
                        flags: InstFlags::default(),
                        tied_operands: vec![],
                    },
                };
                insts.push(inst);
                block_insts.push(id);
            }
            blocks.push(MachBlock {
                insts: block_insts,
                preds: preds[b].clone(),
                succs: succs[b].clone(),
                loop_depth: 0,
            });
        }

        let pre = MachFunction {
            name: "rand".into(),
            insts,
            blocks,
            block_order: (0..nblocks as u32).map(BlockId).collect(),
            entry_block: BlockId(0),
            next_vreg: nv,
            next_stack_slot: nslots,
            stack_slots: BTreeMap::new(),
        };

        // POST: clone + random edits.
        let mut post = pre.clone();
        // Simulate phi elimination most of the time (drop phis from blocks);
        // sometimes leave them (PhiNotEliminated must fire identically).
        if rng.chance(80) {
            let phi_ids: Vec<InstId> = post
                .insts
                .iter()
                .enumerate()
                .filter(|(_, i)| i.flags.is_phi())
                .map(|(idx, _)| InstId(idx as u32))
                .collect();
            for block in &mut post.blocks {
                block.insts.retain(|iid| !phi_ids.contains(iid));
            }
        }
        // Inserted instructions (InstId >= pre.insts.len()): realizing copies
        // and spill code, possibly WRONG (random operands).
        let n_inserted = rng.below(5);
        for _ in 0..n_inserted {
            let id = InstId(post.insts.len() as u32);
            let inst = match rng.below(3) {
                0 => MachInst {
                    opcode: PSEUDO_COPY,
                    defs: vec![MachOperand::VReg(rand_vreg(rng, nv))],
                    uses: vec![MachOperand::VReg(rand_vreg(rng, nv))],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: InstFlags::default(),
                    tied_operands: vec![],
                },
                1 => MachInst {
                    opcode: PSEUDO_SPILL_LOAD,
                    defs: vec![MachOperand::VReg(rand_vreg(rng, nv))],
                    uses: vec![MachOperand::StackSlot(StackSlotId(
                        rng.below(nslots as u64) as u32,
                    ))],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: InstFlags::default(),
                    tied_operands: vec![],
                },
                _ => MachInst {
                    opcode: PSEUDO_SPILL_STORE,
                    defs: vec![],
                    uses: vec![
                        MachOperand::VReg(rand_vreg(rng, nv)),
                        MachOperand::StackSlot(StackSlotId(rng.below(nslots as u64) as u32)),
                    ],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: InstFlags::default(),
                    tied_operands: vec![],
                },
            };
            post.insts.push(inst);
            let b = rng.below(nblocks as u64) as usize;
            let len = post.blocks[b].insts.len();
            let pos = if len == 0 {
                0
            } else {
                rng.below(len as u64 + 1) as usize
            };
            post.blocks[b].insts.insert(pos, id);
        }
        // Occasionally REWRITE an existing instruction's use (a wrong rewrite
        // the validator must flag IDENTICALLY in both implementations).
        if rng.chance(40) {
            let i = rng.below(post.insts.len() as u64) as usize;
            let n_uses = post.insts[i].uses.len();
            if n_uses > 0 {
                let u = rng.below(n_uses as u64) as usize;
                if matches!(post.insts[i].uses[u], MachOperand::VReg(_)) {
                    post.insts[i].uses[u] = MachOperand::VReg(rand_vreg(rng, nv));
                }
            }
        }

        // Random allocation: mapped to a register, spilled, or unmapped —
        // INTENTIONALLY often inconsistent (overlapping homes, double homes).
        let mut allocation: BTreeMap<VReg, PReg> = BTreeMap::new();
        let mut spills: Vec<SpillInfo> = Vec::new();
        for id in 0..nv {
            let v = vreg(id);
            match rng.below(10) {
                0..=5 => {
                    allocation.insert(v, PReg::new(rng.below(4) as u16));
                }
                6 | 7 => {
                    spills.push(SpillInfo {
                        vreg: v,
                        slot: StackSlotId(rng.below(nslots as u64) as u32),
                    });
                    // Occasionally ALSO allocated (double-home guard must fire
                    // identically).
                    if rng.chance(15) {
                        allocation.insert(v, PReg::new(rng.below(4) as u16));
                    }
                }
                _ => {}
            }
        }
        let result = AllocationResult { allocation, spills };

        (pre, post, result)
    }

    /// 600 randomized triples: the shipped (sparse) validator and the dense
    /// reference oracle must produce IDENTICAL error lists — same errors, same
    /// order — across valid and broken allocations, phi-bearing and phi-free,
    /// cyclic and acyclic CFGs.
    #[test]
    fn randomized_sparse_walks_decision_identical_to_dense_reference() {
        let mut rng = XorShift(0x5eed_1dea_d00d_cafe);
        let mut cases_with_errors = 0usize;
        let mut cases_clean = 0usize;
        let mut interference_errors = 0usize;
        let mut value_flow_errors = 0usize;
        let mut phi_errors = 0usize;
        for case in 0..600 {
            let (pre, post, result) = random_triple(&mut rng);
            let fast = validate_allocation(&pre, &post, &result);
            let reference = validate_allocation_reference(&pre, &post, &result);
            assert_eq!(
                fast.errors, reference.errors,
                "case {case}: sparse validator diverged from dense reference\n\
                 pre={pre:#?}\npost={post:#?}\nresult={result:#?}"
            );
            if fast.errors.is_empty() {
                cases_clean += 1;
            } else {
                cases_with_errors += 1;
            }
            for err in &fast.errors {
                match err {
                    ValidationError::InterferenceViolation { .. } => interference_errors += 1,
                    ValidationError::ValueFlowMismatch { .. } => value_flow_errors += 1,
                    ValidationError::PhiTransferBroken { .. }
                    | ValidationError::PhiNotEliminated { .. } => phi_errors += 1,
                    _ => {}
                }
            }
        }
        // Corpus vacuity guards: the corpus must exercise both outcomes and
        // every checker the sparse restrictions touched.
        assert!(cases_clean > 0, "corpus produced no clean cases");
        assert!(cases_with_errors > 0, "corpus produced no violating cases");
        assert!(interference_errors > 0, "corpus never fired interference");
        assert!(value_flow_errors > 0, "corpus never fired value-flow");
        assert!(phi_errors > 0, "corpus never fired a phi check");
    }

    /// Directed TEETH for the CT-3 shared-state (`Rc<PreState>`) rewrite of
    /// `compute_pre_expected`: a loop-carried CONFLICT established at the header
    /// join must be carried UNCHANGED through copy-FREE flow-through blocks (the
    /// blocks that take the new O(1) share path — a JOIN block and a single-pred
    /// block). If the share/skip-retain path had degenerated the analysis (e.g.
    /// dropped the conflict, or become a no-op that reports the trivial `Defined`),
    /// the in-loop uses would read `Defined` and this test would fire. It also
    /// pins decision-identity of the shipped result against the dense reference.
    #[test]
    fn ct3_share_path_carries_loop_carried_conflict() {
        use super::{Sym, compute_pre_spec_flow};
        // v_iv = 0 (loop-carried, realized by copies -> TRACKED), v_init = 1,
        // v_next = 2. Phi-free post-phi-elim IR: preheader copies v_init in, the
        // latch copies v_next in, so the header meet is CONFLICT({1,2}).
        let mk = |opcode: u16, defs: Vec<MachOperand>, uses: Vec<MachOperand>| MachInst {
            opcode,
            defs,
            uses,
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        };
        let insts = vec![
            // block 0 (preheader)
            mk(
                0x20,
                vec![MachOperand::VReg(vreg(1))],
                vec![MachOperand::Imm(0)],
            ), // i0 def v_init
            mk(
                PSEUDO_COPY,
                vec![MachOperand::VReg(vreg(0))],
                vec![MachOperand::VReg(vreg(1))],
            ), // i1 v_iv <- v_init
            // block 1 (header, copy-FREE, JOIN of preheader + latch)
            mk(2, vec![], vec![MachOperand::VReg(vreg(0))]), // i2 use v_iv  -> CONFLICT
            // block 2 (mid, copy-FREE, single-pred share)
            mk(2, vec![], vec![MachOperand::VReg(vreg(0))]), // i3 use v_iv  -> CONFLICT
            // block 3 (latch, writes v_iv)
            mk(
                0x20,
                vec![MachOperand::VReg(vreg(2))],
                vec![MachOperand::VReg(vreg(0))],
            ), // i4 def v_next
            mk(
                PSEUDO_COPY,
                vec![MachOperand::VReg(vreg(0))],
                vec![MachOperand::VReg(vreg(2))],
            ), // i5 v_iv <- v_next
            // block 4 (exit)
            mk(2, vec![], vec![MachOperand::VReg(vreg(0))]), // i6 use v_iv
        ];
        let blocks = vec![
            MachBlock {
                insts: vec![InstId(0), InstId(1)],
                preds: vec![],
                succs: vec![BlockId(1)],
                loop_depth: 0,
            },
            MachBlock {
                insts: vec![InstId(2)],
                preds: vec![BlockId(0), BlockId(3)],
                succs: vec![BlockId(2)],
                loop_depth: 1,
            },
            MachBlock {
                insts: vec![InstId(3)],
                preds: vec![BlockId(1)],
                succs: vec![BlockId(3), BlockId(4)],
                loop_depth: 1,
            },
            MachBlock {
                insts: vec![InstId(4), InstId(5)],
                preds: vec![BlockId(2)],
                succs: vec![BlockId(1)],
                loop_depth: 1,
            },
            MachBlock {
                insts: vec![InstId(6)],
                preds: vec![BlockId(2)],
                succs: vec![],
                loop_depth: 0,
            },
        ];
        let pre = MachFunction {
            name: "ct3loop".into(),
            insts,
            blocks,
            block_order: (0..5).map(BlockId).collect(),
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        let fast = compute_pre_spec_flow(&pre).expected;
        let reference = compute_pre_spec_flow_reference(&pre).expected;
        // Decision-identity: optimized == dense reference.
        assert_eq!(
            fast, reference,
            "CT-3 shared-state compute_pre_expected diverged from the dense reference"
        );
        // Teeth: the loop-carried CONFLICT must survive through BOTH copy-free
        // share blocks (header i2 = join-materialized share, mid i3 = single-pred
        // Rc share). A degenerate/no-op analysis would report `Defined` here.
        assert!(
            matches!(fast.get(&(InstId(2), vreg(0))), Some(Sym::Conflict(_))),
            "header in-loop use must see CONFLICT, got {:?}",
            fast.get(&(InstId(2), vreg(0)))
        );
        assert!(
            matches!(fast.get(&(InstId(3), vreg(0))), Some(Sym::Conflict(_))),
            "flow-through (single-pred share) use must carry the CONFLICT, got {:?}",
            fast.get(&(InstId(3), vreg(0)))
        );
    }

    /// Tiny deterministic LCG (Knuth MMIX constants) for the many-block
    /// differential corpus below — hand-rolled, seeded, no `std::time`, no
    /// hash-order dependence anywhere (mirrors the corpus discipline of
    /// `trust-cg-opt/src/reaching_const_differential.rs`).
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 11
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
        fn chance(&mut self, percent: u64) -> bool {
            self.below(100) < percent
        }
    }

    /// One random MANY-BLOCK PRE function for the live-out-prune differential:
    /// a reducible CFG of 16..=40 blocks built from single-entry segments
    /// (each optionally a natural loop: latch -> head back edge, plus self
    /// loops), forward skip edges targeting later segment HEADS only (so every
    /// back-edge target dominates its latch and `block_order = 0..n` visits
    /// every non-back-edge predecessor first — the same seeding regime as the
    /// shipped RPO walk, keeping the dense reference's layout-order iteration
    /// convergent to the identical anchored fixpoint), phis at join heads
    /// (uses index-aligned with preds), and cross-block copies / generic ops /
    /// bare uses over a shared vreg pool.
    fn random_many_block_pre(rng: &mut Lcg, case: usize) -> MachFunction {
        let nblocks = 16 + rng.below(25) as usize; // 16..=40
        let nv = 8 + rng.below(17) as u32; // vreg pool 8..=24

        // --- CFG: segment structure first (edges before insts so phi uses can
        // be index-aligned with the final pred lists). ---
        let mut succs: Vec<Vec<BlockId>> = vec![Vec::new(); nblocks];
        let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); nblocks];
        let mut heads: Vec<usize> = Vec::new(); // segment heads, ascending
        let edge = |succs: &mut Vec<Vec<BlockId>>,
                    preds: &mut Vec<Vec<BlockId>>,
                    from: usize,
                    to: usize| {
            succs[from].push(BlockId(to as u32));
            preds[to].push(BlockId(from as u32));
        };
        let mut b = 0usize;
        while b < nblocks {
            let head = b;
            heads.push(head);
            let seg_len = 1 + rng.below(3) as usize; // 1..=3 blocks
            let seg_end = (head + seg_len - 1).min(nblocks - 1);
            // Chain the segment and fall through to the next segment head.
            for i in head..=seg_end {
                if i + 1 < nblocks {
                    edge(&mut succs, &mut preds, i, i + 1);
                }
            }
            // Natural loop: latch -> head (head dominates the whole segment:
            // its only entries from outside land on the head).
            if seg_end > head && rng.chance(45) {
                edge(&mut succs, &mut preds, seg_end, head);
            }
            // Occasional self loop on the head.
            if rng.chance(15) {
                edge(&mut succs, &mut preds, head, head);
            }
            b = seg_end + 1;
        }
        // Forward skip edges: only to LATER segment heads (keeps every segment
        // single-entry-through-its-head, i.e. the CFG reducible).
        for from in 0..nblocks {
            if rng.chance(30) {
                if let Some(&to) = heads.iter().find(|&&h| h > from) {
                    let later: Vec<usize> = heads.iter().copied().filter(|&h| h > from).collect();
                    let to = if later.len() > 1 {
                        later[rng.below(later.len() as u64) as usize]
                    } else {
                        to
                    };
                    edge(&mut succs, &mut preds, from, to);
                }
            }
        }

        // --- Instructions. ---
        let mk = |opcode: u16, defs: Vec<MachOperand>, uses: Vec<MachOperand>, phi: bool| {
            let mut flags = InstFlags::default();
            if phi {
                flags.insert(InstFlags::IS_PHI);
            }
            MachInst {
                opcode,
                defs,
                uses,
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags,
                tied_operands: vec![],
            }
        };
        let mut insts: Vec<MachInst> = Vec::new();
        let mut blocks: Vec<MachBlock> = Vec::new();
        for blk in 0..nblocks {
            let mut block_insts: Vec<InstId> = Vec::new();
            // Phis at block start on join blocks, one use per pred.
            if preds[blk].len() > 1 && rng.chance(40) {
                let id = InstId(insts.len() as u32);
                insts.push(mk(
                    7,
                    vec![MachOperand::VReg(vreg(rng.below(nv as u64) as u32))],
                    preds[blk]
                        .iter()
                        .map(|_| MachOperand::VReg(vreg(rng.below(nv as u64) as u32)))
                        .collect(),
                    true,
                ));
                block_insts.push(id);
            }
            let n_inst = 1 + rng.below(4);
            for _ in 0..n_inst {
                let id = InstId(insts.len() as u32);
                let inst = match rng.below(10) {
                    // Cross-block vreg-vreg copies (both opcodes): the tracked
                    // key domain and the loop-carried conflict fuel.
                    0..=3 => mk(
                        if rng.chance(50) {
                            PSEUDO_COPY
                        } else {
                            IR_COPY_OPCODE
                        },
                        vec![MachOperand::VReg(vreg(rng.below(nv as u64) as u32))],
                        vec![MachOperand::VReg(vreg(rng.below(nv as u64) as u32))],
                        false,
                    ),
                    // Imm-source copy (generic-def arm).
                    4 => mk(
                        PSEUDO_COPY,
                        vec![MachOperand::VReg(vreg(rng.below(nv as u64) as u32))],
                        vec![MachOperand::Imm(rng.below(64) as i64)],
                        false,
                    ),
                    // Bare use (records `.expected`, generates liveness).
                    5 | 6 => mk(
                        2,
                        vec![],
                        vec![MachOperand::VReg(vreg(rng.below(nv as u64) as u32))],
                        false,
                    ),
                    // Generic compute def <- (use, use).
                    _ => mk(
                        0x20 + rng.below(4) as u16,
                        vec![MachOperand::VReg(vreg(rng.below(nv as u64) as u32))],
                        vec![
                            MachOperand::VReg(vreg(rng.below(nv as u64) as u32)),
                            MachOperand::VReg(vreg(rng.below(nv as u64) as u32)),
                        ],
                        false,
                    ),
                };
                insts.push(inst);
                block_insts.push(id);
            }
            blocks.push(MachBlock {
                insts: block_insts,
                preds: preds[blk].clone(),
                succs: succs[blk].clone(),
                loop_depth: 0,
            });
        }
        MachFunction {
            name: format!("many_block_{case}"),
            insts,
            blocks,
            block_order: (0..nblocks as u32).map(BlockId).collect(),
            entry_block: BlockId(0),
            next_vreg: nv,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        }
    }

    /// Differential gate for the per-block LIVE-OUT persisted-exit restriction
    /// of `compute_pre_spec_flow` (the fix for the Theta(blocks^2) fixpoint on
    /// many-block functions): over a seeded family of random MANY-BLOCK CFGs
    /// with loops, phi edges and cross-block copies, the shipped sparse walk
    /// must agree with the dense reference on EVERY external observation of
    /// its result:
    ///
    ///  * `.expected` — the per-use spec map (property (a)'s obligation),
    ///    compared for full map equality;
    ///  * `phi_edge_expected(exit_states, spec_pred, src)` for every phi edge
    ///    `(pre pred i, uses[i])` — the ONLY read of `.exit_states` outside
    ///    the fixpoint (the generalized per-edge phi obligation consumed by
    ///    [`block_entry_state`] and the per-edge transfer check).
    ///
    /// 3 seeds x 40 cases, fully deterministic (hand-rolled LCG, no time, no
    /// hash order). Vacuity guards require the corpus to actually exercise
    /// loop-carried CONFLICTs, non-trivial phi-edge spec values, and pruned
    /// exit states (fast state strictly narrower than the dense reference's).
    #[test]
    fn pre_spec_flow_live_out_prune_matches_dense_reference_on_many_block_cfgs() {
        use super::{Sym, compute_pre_spec_flow, phi_edge_expected};
        let mut phi_edges = 0usize;
        let mut nontrivial_phi_edges = 0usize;
        let mut conflict_expected = 0usize;
        let mut pruned_cases = 0usize;
        for seed in [0x5eed_0001_u64, 0x5eed_0002, 0x5eed_0003] {
            let mut rng = Lcg(seed);
            for case in 0..40usize {
                let pre = random_many_block_pre(&mut rng, case);
                let fast = compute_pre_spec_flow(&pre);
                let reference = compute_pre_spec_flow_reference(&pre);
                assert_eq!(
                    fast.expected, reference.expected,
                    "seed={seed:#x} case={case}: sparse .expected diverged from \
                     the dense reference\npre={pre:#?}"
                );
                conflict_expected += fast
                    .expected
                    .values()
                    .filter(|s| matches!(s, Sym::Conflict(_)))
                    .count();
                // Every phi edge's spec obligation, read exactly the way the
                // validator reads it (pre pred i <-> uses[i], per
                // `collect_phi_specs`).
                for block in &pre.blocks {
                    for &inst_id in &block.insts {
                        let inst = &pre.insts[inst_id.0 as usize];
                        if !inst.flags.is_phi() {
                            continue;
                        }
                        for (i, &pred) in block.preds.iter().enumerate() {
                            let Some(src) = inst.uses.get(i).and_then(|op| op.as_vreg()) else {
                                continue;
                            };
                            let f = phi_edge_expected(Some(&fast.exit_states), pred, src);
                            let r = phi_edge_expected(Some(&reference.exit_states), pred, src);
                            assert_eq!(
                                f, r,
                                "seed={seed:#x} case={case}: phi edge ({pred:?}, {src:?}) \
                                 spec value diverged\npre={pre:#?}"
                            );
                            phi_edges += 1;
                            if f != Sym::Defined(src.id) {
                                nontrivial_phi_edges += 1;
                            }
                        }
                    }
                }
                // The prune must actually bite somewhere (guards against a
                // rewrite that silently keeps everything).
                let fast_width: usize = fast.exit_states.values().map(|s| s.len()).sum();
                let dense_width: usize = reference.exit_states.values().map(|s| s.len()).sum();
                if fast_width < dense_width {
                    pruned_cases += 1;
                }
            }
        }
        // Corpus vacuity guards.
        assert!(phi_edges > 100, "corpus too phi-poor: {phi_edges} edges");
        assert!(
            nontrivial_phi_edges > 0,
            "corpus never produced a non-trivial phi-edge spec value"
        );
        assert!(
            conflict_expected > 0,
            "corpus never produced a loop-carried CONFLICT in .expected"
        );
        assert!(
            pruned_cases > 100,
            "the live-out prune never narrowed an exit state ({pruned_cases} cases)"
        );
    }

    /// CT-3 opt-in measurement campaign (not run in the ordinary CI lane).
    /// Builds a large loop PRE function that maximizes live-out tracked exit-state WIDTH — the
    /// per-block `BTreeMap<VReg,Sym>` clone cost — and times `compute_pre_expected`.
    /// Default "flow" mode models the clone-dominated TY fused-BFS regime (wide
    /// value file flowing through copy-FREE blocks, where the shared-state path
    /// wins ~20x); `BENCH_MODE=heavy` models the transfer-dominated regime (every
    /// block writes the file — no share win, no regression). Run with:
    ///   TRUST_CG_RUN_MEASUREMENT_TESTS=1 cargo test -p trust-cg-regalloc \
    ///     --release bench_compute_pre_expected -- --nocapture
    #[test]
    fn bench_compute_pre_expected() {
        if !matches!(
            std::env::var("TRUST_CG_RUN_MEASUREMENT_TESTS").as_deref(),
            Ok("1")
        ) {
            eprintln!(
                "measurement campaign not requested; \
                 set TRUST_CG_RUN_MEASUREMENT_TESTS=1 to run"
            );
            return;
        }

        use super::compute_pre_spec_flow;
        // N = width of the loop-carried tracked value file (exit-state size).
        // L = number of body blocks (per-block clone count).
        const N: u32 = 300;
        const L: u32 = 200;
        // Mode "flow" (default): FEW copies, WIDE flow-through exit states — the
        //   TY-fused-BFS regime where the per-block clone dominates and copy-FREE
        //   body blocks are the norm (the CoW-sharing win). Mode "heavy": every
        //   body block copies all N vars (transfer-dominated, no CoW win).
        let heavy = std::env::var("BENCH_MODE")
            .map(|m| m == "heavy")
            .unwrap_or(false);

        let mut insts: Vec<MachInst> = Vec::new();
        let mut blocks: Vec<MachBlock> = Vec::new();

        // Block 0 (preheader): define w_i (generic) then copy v_i <- w_i, so v_i
        // [ids 0..N] are TRACKED copy-destinations that flow through the loop.
        let mut b0: Vec<InstId> = Vec::new();
        for i in 0..N {
            let dw = InstId(insts.len() as u32);
            insts.push(MachInst {
                opcode: 0x20,
                defs: vec![MachOperand::VReg(vreg(N + i))],
                uses: vec![MachOperand::Imm(i as i64)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            });
            b0.push(dw);
            let cp = InstId(insts.len() as u32);
            insts.push(MachInst {
                opcode: PSEUDO_COPY,
                defs: vec![MachOperand::VReg(vreg(i))],
                uses: vec![MachOperand::VReg(vreg(N + i))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            });
            b0.push(cp);
        }
        blocks.push(MachBlock {
            insts: b0,
            preds: Vec::new(),
            succs: vec![BlockId(1)],
            loop_depth: 0,
        });

        // Blocks 1..=L: body. "flow" mode: ONE cheap generic def to a throwaway
        // vreg (NO tracked def -> transfer is a no-op on tracked state -> copy-FREE
        // flow-through block: exit == entry, the CoW-share case). "heavy" mode:
        // copy all N vars.
        for b in 1..=L {
            let mut binsts: Vec<InstId> = Vec::new();
            if heavy {
                for i in 0..N {
                    let id = InstId(insts.len() as u32);
                    insts.push(MachInst {
                        opcode: PSEUDO_COPY,
                        defs: vec![MachOperand::VReg(vreg(i))],
                        uses: vec![MachOperand::VReg(vreg(i))],
                        implicit_defs: Vec::new(),
                        implicit_uses: Vec::new(),
                        flags: InstFlags::default(),
                        tied_operands: vec![],
                    });
                    binsts.push(id);
                }
            } else {
                let id = InstId(insts.len() as u32);
                insts.push(MachInst {
                    opcode: 0x20,
                    defs: vec![MachOperand::VReg(vreg(2 * N + b))],
                    uses: vec![MachOperand::Imm(b as i64)],
                    implicit_defs: Vec::new(),
                    implicit_uses: Vec::new(),
                    flags: InstFlags::default(),
                    tied_operands: vec![],
                });
                binsts.push(id);
            }
            let preds = if b == 1 {
                vec![BlockId(0), BlockId(L)]
            } else {
                vec![BlockId(b - 1)]
            };
            // Block L back-edges to block 1 (loop) AND falls to the exit block.
            let succs = if b == L {
                vec![BlockId(L + 1), BlockId(1)]
            } else {
                vec![BlockId(b + 1)]
            };
            blocks.push(MachBlock {
                insts: binsts,
                preds,
                succs,
                loop_depth: 1,
            });
        }

        // Exit block L+1: USE every v_i so all N tracked vars are LIVE-OUT of
        // every body block (and thus populate every body block's exit state).
        let mut bexit: Vec<InstId> = Vec::new();
        for i in 0..N {
            let id = InstId(insts.len() as u32);
            insts.push(MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(i))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            });
            bexit.push(id);
        }
        blocks.push(MachBlock {
            insts: bexit,
            preds: vec![BlockId(L)],
            succs: Vec::new(),
            loop_depth: 0,
        });

        let pre = MachFunction {
            name: "bench".into(),
            insts,
            blocks,
            block_order: (0..=L + 1).map(BlockId).collect(),
            entry_block: BlockId(0),
            next_vreg: 3 * N + L + 2,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // warmup
        let _ = compute_pre_spec_flow(&pre).expected;
        let iters = std::env::var("BENCH_ITERS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(200u32);
        let t = std::time::Instant::now();
        let mut acc = 0usize;
        for _ in 0..iters {
            let e = compute_pre_spec_flow(&pre).expected;
            acc = acc.wrapping_add(e.len());
        }
        let dt = t.elapsed();
        eprintln!(
            "bench_compute_pre_expected: {} iters, {:?} total, {:?}/iter (acc={})",
            iters,
            dt,
            dt / iters,
            acc
        );
    }

    /// Directed decision-identity on REAL allocator output: run the production
    /// pipeline on a small function and require the sparse and dense validators
    /// to agree on the result (both clean).
    #[test]
    fn sparse_walks_match_dense_reference_on_real_allocations() {
        let mut insts = Vec::new();
        for k in 0..2u32 {
            insts.push(MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(vreg(k))],
                uses: vec![MachOperand::Imm(k as i64)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            });
        }
        for k in 0..2u32 {
            insts.push(MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(vreg(k))],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            });
        }
        let inst_ids: Vec<InstId> = (0..insts.len() as u32).map(InstId).collect();
        let pre = MachFunction {
            name: "real".into(),
            insts,
            blocks: vec![MachBlock {
                insts: inst_ids,
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };
        let pre_snapshot = pre.clone();
        let mut post = pre;
        let config = AllocConfig::default_aarch64();
        let result = allocate(&mut post, &config).expect("allocation should succeed");
        let fast = validate_allocation(&pre_snapshot, &post, &result);
        let reference = validate_allocation_reference(&pre_snapshot, &post, &result);
        assert_eq!(fast.errors, reference.errors);
        assert!(fast.is_valid());
    }

    // =======================================================================
    // ADVERSARIAL refute-control tests (Phase-1 validator hardening).
    //
    // Each test hand-constructs a KNOWN-BAD allocation, demonstrates that the
    // HISTORICAL validator semantics accepted it (the control), and asserts
    // the hardened validator REJECTS it.
    // =======================================================================

    fn adv_inst(opcode: u16, defs: Vec<MachOperand>, uses: Vec<MachOperand>) -> MachInst {
        MachInst {
            opcode,
            defs,
            uses,
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }
    }

    fn adv_single_block(name: &str, insts: Vec<MachInst>, order: Vec<InstId>) -> MachFunction {
        MachFunction {
            name: name.into(),
            insts,
            blocks: vec![MachBlock {
                insts: order,
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 4,
            next_stack_slot: 1,
            stack_slots: BTreeMap::new(),
        }
    }

    /// FLAW (b), the self-certification hole: `allocate` used to REPLAY the
    /// coalescing rewrite map onto the SPEC before validating, so a WRONG merge
    /// (two INTERFERING vregs fused into one register) mutated both sides and
    /// passed trivially.
    ///
    /// Shape (the exact block-param/latch surface Phase-2 coalescing targets):
    ///
    /// ```text
    ///   b0: v0 = imm ; [phi-elim copy: d <- v0]
    ///   b1: d = phi [v0 from b0, v2 from b1]
    ///       v2 = op(d)          ; latch update
    ///       use d               ; d is READ AFTER v2's def -> d,v2 INTERFERE
    ///       br v2, b1, b2       ; [phi-elim latch copy d <- v2 would go here]
    ///   b2: use v2
    /// ```
    ///
    /// A WRONG coalesce merges the phi dest `d` with its latch source `v2`
    /// although they interfere (the latch copy is removed, all `v2` rewritten
    /// to `d`, one register). The `use d` after the update then reads v2's NEW
    /// value — a loop-carried miscompile.
    ///
    /// REFUTE CONTROL: replaying the rewrite onto the spec (the historical
    /// `rewrite_snapshot_vregs` behavior, reproduced verbatim here) and calling
    /// the validator ACCEPTS the miscompile — the flaw, demonstrated live.
    /// The hardened entry point, validating against the ORIGINAL spec with the
    /// rewrite map as namespace bookkeeping only, REJECTS it.
    #[test]
    fn adversarial_wrong_coalesce_of_interfering_vregs_rejected() {
        let d = vreg(3);
        let v0 = vreg(0);
        let v2 = vreg(2);
        let mut phi_flags = InstFlags::default();
        phi_flags.insert(InstFlags::IS_PHI);
        let insts = vec![
            // i0 (b0): v0 = imm
            adv_inst(1, vec![MachOperand::VReg(v0)], vec![MachOperand::Imm(7)]),
            // i1 (b1): d = phi [v0 from b0, v2 from b1]
            MachInst {
                opcode: 7,
                defs: vec![MachOperand::VReg(d)],
                uses: vec![MachOperand::VReg(v0), MachOperand::VReg(v2)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: phi_flags,
                tied_operands: vec![],
            },
            // i2 (b1): v2 = op(d)
            adv_inst(
                0x20,
                vec![MachOperand::VReg(v2)],
                vec![MachOperand::VReg(d)],
            ),
            // i3 (b1): use d — AFTER v2's def: d and v2 interfere.
            adv_inst(2, vec![], vec![MachOperand::VReg(d)]),
            // i4 (b1): br v2, b1, b2
            MachInst {
                opcode: 0xBB,
                defs: vec![],
                uses: vec![
                    MachOperand::VReg(v2),
                    MachOperand::Block(BlockId(1)),
                    MachOperand::Block(BlockId(2)),
                ],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            // i5 (b2): use v2
            adv_inst(2, vec![], vec![MachOperand::VReg(v2)]),
        ];
        let pre = MachFunction {
            name: "wrong_latch_merge".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0)],
                    preds: vec![],
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(1), InstId(2), InstId(3), InstId(4)],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![InstId(5)],
                    preds: vec![BlockId(1)],
                    succs: vec![],
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 4,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        };

        // Build POST: phi eliminated (b0 gets the entry copy `d <- v0`; the
        // latch copy `d <- v2` was REMOVED by the wrong coalesce), all v2
        // operands rewritten to d — the merge realized exactly as
        // apply_coalescing would.
        let rewrite_v2_to_d = |f: &mut MachFunction| {
            for inst in &mut f.insts {
                for op in inst.defs.iter_mut().chain(inst.uses.iter_mut()) {
                    if let MachOperand::VReg(v) = op
                        && *v == v2
                    {
                        *v = d;
                    }
                }
            }
        };
        let mut post = pre.clone();
        // Entry-edge realizing copy (inserted by phi elimination).
        let entry_copy = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(d)],
            uses: vec![MachOperand::VReg(v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        post.blocks[0].insts = vec![InstId(0), entry_copy];
        // Phi gone from the block list; latch copy never materialized (merged).
        post.blocks[1].insts = vec![InstId(2), InstId(3), InstId(4)];
        rewrite_v2_to_d(&mut post);

        let mut rewrites = BTreeMap::new();
        rewrites.insert(v2, d);
        let mut allocation = BTreeMap::new();
        allocation.insert(v0, PReg::new(1));
        allocation.insert(d, PReg::new(0)); // d and v2 fused onto X0
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        // ---- REFUTE CONTROL: the historical replay-onto-spec semantics ----
        // (verbatim reproduction of the removed `rewrite_snapshot_vregs` step).
        let mut replayed_spec = pre.clone();
        rewrite_v2_to_d(&mut replayed_spec);
        let old_semantics = validate_allocation(&replayed_spec, &post, &result);
        assert!(
            old_semantics.is_valid(),
            "CONTROL: the historical replay-onto-spec semantics must ACCEPT the \
             wrong merge (both sides mutated, self-certifying) — got {:?}",
            old_semantics.errors
        );

        // ---- The hardened validator: ORIGINAL spec + rewrites as bookkeeping ----
        let report = super::validate_allocation_coalesced(&pre, &post, &result, &rewrites);
        assert!(
            !report.is_valid(),
            "hardened validator must REJECT a merge of interfering vregs"
        );
        assert!(
            report
                .errors
                .iter()
                .any(|e| matches!(e, ValidationError::ValueFlowMismatch { .. })),
            "expected a value-flow mismatch (use of d reads v2's value), got {:?}",
            report.errors
        );
    }

    /// A CORRECT coalesce (copy of a dead-after-copy value) must still validate
    /// against the ORIGINAL spec — the hardening must not reject sound merges.
    /// `v0 = imm; v1 = copy v0; use v1` with the copy removed and v0 -> v1.
    #[test]
    fn correct_coalesce_validates_against_original_spec() {
        let pre = adv_single_block(
            "good_merge",
            vec![
                adv_inst(
                    1,
                    vec![MachOperand::VReg(vreg(0))],
                    vec![MachOperand::Imm(7)],
                ),
                adv_inst(
                    super::IR_COPY_OPCODE,
                    vec![MachOperand::VReg(vreg(1))],
                    vec![MachOperand::VReg(vreg(0))],
                ),
                adv_inst(2, vec![], vec![MachOperand::VReg(vreg(1))]),
            ],
            vec![InstId(0), InstId(1), InstId(2)],
        );

        let mut rewrites = BTreeMap::new();
        rewrites.insert(vreg(0), vreg(1)); // src merged into dst (coalescer orientation)
        let mut post = pre.clone();
        for inst in &mut post.insts {
            for op in inst.defs.iter_mut().chain(inst.uses.iter_mut()) {
                if let MachOperand::VReg(v) = op
                    && *v == vreg(0)
                {
                    *v = vreg(1);
                }
            }
        }
        // The copy itself is removed from the block list (apply_coalescing).
        post.blocks[0].insts = vec![InstId(0), InstId(2)];

        let mut allocation = BTreeMap::new();
        allocation.insert(vreg(1), PReg::new(0));
        let result = AllocationResult {
            allocation,
            spills: Vec::new(),
        };

        let report = super::validate_allocation_coalesced(&pre, &post, &result, &rewrites);
        assert!(
            report.is_valid(),
            "a sound coalesce must validate against the original spec, got {:?}",
            report.errors
        );
    }

    /// End-to-end: the production `allocate` pipeline (which coalesces the
    /// original copy chain away) must still validate — the always-on hardened
    /// validator introduces no false positives on real coalescing.
    #[test]
    fn allocate_with_original_copy_chain_still_validates() {
        // v0 = imm; v1 = copy v0; v2 = copy v1; use v2 (three-deep chain).
        let pre = adv_single_block(
            "copy_chain",
            vec![
                adv_inst(
                    1,
                    vec![MachOperand::VReg(vreg(0))],
                    vec![MachOperand::Imm(3)],
                ),
                adv_inst(
                    super::IR_COPY_OPCODE,
                    vec![MachOperand::VReg(vreg(1))],
                    vec![MachOperand::VReg(vreg(0))],
                ),
                adv_inst(
                    super::IR_COPY_OPCODE,
                    vec![MachOperand::VReg(vreg(2))],
                    vec![MachOperand::VReg(vreg(1))],
                ),
                adv_inst(2, vec![], vec![MachOperand::VReg(vreg(2))]),
            ],
            vec![InstId(0), InstId(1), InstId(2), InstId(3)],
        );
        let mut post = pre.clone();
        let config = AllocConfig::default_aarch64();
        // allocate() runs the hardened validator internally and fails closed.
        allocate(&mut post, &config)
            .expect("coalesced copy chain must pass the hardened validator");
    }

    /// FLAW (a), the reload-register blind spot: the value-flow walk validates
    /// a spilled use against its SLOT home, but the machine routes the value
    /// through an unnamed scratch register from the reload to the consumer. A
    /// reload separated from its consumer by another instruction leaves the
    /// scratch exposed to a clobber the validator cannot see.
    ///
    /// Shape: `v0 = imm (spilled); store v0 -> slot0; RELOAD v0; v1 = imm;
    /// use v0` — the `v1` def sits between v0's reload and its use.
    ///
    /// REFUTE CONTROL: properties (a)/(b)/(c) all ACCEPT this triple (the slot
    /// still holds v0 — exactly what the historical validator checked, so it
    /// passed). The hardened validator's spill-discipline property (d) rejects
    /// it, and ONLY (d) fires — proving the historical acceptance.
    #[test]
    fn adversarial_reload_separated_from_use_rejected() {
        let insts = vec![
            adv_inst(
                1,
                vec![MachOperand::VReg(vreg(0))],
                vec![MachOperand::Imm(7)],
            ), // i0
            adv_inst(
                1,
                vec![MachOperand::VReg(vreg(1))],
                vec![MachOperand::Imm(9)],
            ), // i1
            adv_inst(
                2,
                vec![],
                vec![MachOperand::VReg(vreg(0)), MachOperand::VReg(vreg(1))],
            ), // i2
        ];
        let pre = adv_single_block("reload_gap", insts, vec![InstId(0), InstId(1), InstId(2)]);

        // Post: spill code for v0, but the reload drifted ABOVE the v1 def.
        let mut post = pre.clone();
        let store_id = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: super::PSEUDO_SPILL_STORE,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(vreg(0)),
                MachOperand::StackSlot(StackSlotId(0)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::WRITES_MEMORY,
            tied_operands: vec![],
        });
        let load_id = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: super::PSEUDO_SPILL_LOAD,
            defs: vec![MachOperand::VReg(vreg(0))],
            uses: vec![MachOperand::StackSlot(StackSlotId(0))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::READS_MEMORY,
            tied_operands: vec![],
        });
        // Reload BEFORE the intervening v1 def: scratch crosses `v1 = imm`.
        post.blocks[0].insts = vec![InstId(0), store_id, load_id, InstId(1), InstId(2)];

        let mut allocation = BTreeMap::new();
        allocation.insert(vreg(1), PReg::new(0));
        let result = AllocationResult {
            allocation,
            spills: vec![crate::linear_scan::SpillInfo {
                vreg: vreg(0),
                slot: StackSlotId(0),
            }],
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "a reload separated from its consumer must be rejected"
        );
        // REFUTE CONTROL: only the NEW property (d) fires — (a)/(b)/(c), i.e.
        // the historical validator, accepted this exact triple.
        assert!(
            report
                .errors
                .iter()
                .all(|e| matches!(e, ValidationError::SpillDisciplineViolation { .. })),
            "only spill-discipline must fire (historical properties accepted \
             the clobber-exposed reload): {:?}",
            report.errors
        );

        // POSITIVE CONTROL: the same triple with the reload ADJACENT to its
        // consumer (the shape insert_spill_code emits) validates.
        post.blocks[0].insts = vec![InstId(0), store_id, InstId(1), load_id, InstId(2)];
        let report = validate_allocation(&pre, &post, &result);
        assert!(
            report.is_valid(),
            "adjacent reload must validate, got {:?}",
            report.errors
        );
    }

    /// Property (d), store side: a spill store separated from its def leaves the
    /// def's value in an unnamed scratch across an intervening instruction.
    #[test]
    fn adversarial_store_separated_from_def_rejected() {
        let insts = vec![
            adv_inst(
                1,
                vec![MachOperand::VReg(vreg(0))],
                vec![MachOperand::Imm(7)],
            ), // i0 (spilled)
            adv_inst(
                1,
                vec![MachOperand::VReg(vreg(1))],
                vec![MachOperand::Imm(9)],
            ), // i1
            adv_inst(2, vec![], vec![MachOperand::VReg(vreg(1))]), // i2
        ];
        let pre = adv_single_block("store_gap", insts, vec![InstId(0), InstId(1), InstId(2)]);

        let mut post = pre.clone();
        let store_id = InstId(post.insts.len() as u32);
        post.insts.push(MachInst {
            opcode: super::PSEUDO_SPILL_STORE,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(vreg(0)),
                MachOperand::StackSlot(StackSlotId(0)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::WRITES_MEMORY,
            tied_operands: vec![],
        });
        // Store drifted BELOW the v1 def: def's scratch crosses `v1 = imm`.
        post.blocks[0].insts = vec![InstId(0), InstId(1), store_id, InstId(2)];

        let mut allocation = BTreeMap::new();
        allocation.insert(vreg(1), PReg::new(0));
        let result = AllocationResult {
            allocation,
            spills: vec![crate::linear_scan::SpillInfo {
                vreg: vreg(0),
                slot: StackSlotId(0),
            }],
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "a spill store separated from its def must be rejected"
        );
        assert!(
            report
                .errors
                .iter()
                .all(|e| matches!(e, ValidationError::SpillDisciplineViolation { .. })),
            "only spill-discipline must fire: {:?}",
            report.errors
        );

        // POSITIVE CONTROL: store adjacent to its def validates.
        post.blocks[0].insts = vec![InstId(0), store_id, InstId(1), InstId(2)];
        let report = validate_allocation(&pre, &post, &result);
        assert!(
            report.is_valid(),
            "adjacent spill store must validate, got {:?}",
            report.errors
        );
    }

    // =======================================================================
    // (e) SLOT-INITIALIZATION DOMINANCE — the split-connector miscompile class.
    //
    // These drive `check_slot_init_dominance` DIRECTLY on a hand-built post
    // stream (isolated from the other gates), asserting on the presence /
    // absence of the SpillSlotUninitializedReload diagnostic.
    // =======================================================================

    fn si_store(v: u32, slot: u32) -> MachInst {
        MachInst {
            opcode: PSEUDO_SPILL_STORE,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(vreg(v)),
                MachOperand::StackSlot(StackSlotId(slot)),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::WRITES_MEMORY,
            tied_operands: vec![],
        }
    }

    fn si_load(v: u32, slot: u32) -> MachInst {
        MachInst {
            opcode: PSEUDO_SPILL_LOAD,
            defs: vec![MachOperand::VReg(vreg(v))],
            uses: vec![MachOperand::StackSlot(StackSlotId(slot))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::READS_MEMORY,
            tied_operands: vec![],
        }
    }

    /// Build a post function from `insts` and a list of `(block insts, succs)`.
    /// Predecessors are derived from succs; entry is block 0.
    fn si_func(insts: Vec<MachInst>, blocks: Vec<(Vec<InstId>, Vec<BlockId>)>) -> MachFunction {
        let n = blocks.len();
        let mut mblocks: Vec<MachBlock> = blocks
            .iter()
            .map(|(bi, succs)| MachBlock {
                insts: bi.clone(),
                preds: Vec::new(),
                succs: succs.clone(),
                loop_depth: 0,
            })
            .collect();
        for b in 0..n {
            let succs = mblocks[b].succs.clone();
            for s in succs {
                mblocks[s.0 as usize].preds.push(BlockId(b as u32));
            }
        }
        MachFunction {
            name: "slotinit".into(),
            insts,
            block_order: (0..n as u32).map(BlockId).collect(),
            blocks: mblocks,
            entry_block: BlockId(0),
            next_vreg: 32,
            next_stack_slot: 8,
            stack_slots: BTreeMap::new(),
        }
    }

    fn si_run(post: &MachFunction) -> super::ValidationReport {
        let mut report = super::ValidationReport::default();
        super::check_slot_init_dominance(post, &mut report);
        report
    }

    fn si_uninit_errors(
        report: &super::ValidationReport,
    ) -> Vec<(BlockId, StackSlotId, Option<BlockId>)> {
        report
            .errors
            .iter()
            .filter_map(|e| match e {
                ValidationError::SpillSlotUninitializedReload {
                    block,
                    slot,
                    uninit_pred,
                    ..
                } => Some((*block, *slot, *uninit_pred)),
                _ => None,
            })
            .collect()
    }

    /// A correctly-placed split: the connector store dominates the reload
    /// (store in the entry block, reload in the single successor). ACCEPTED —
    /// the gate is silent on a store that dominates every reload.
    #[test]
    fn slotinit_correct_split_accepted() {
        // b0: def v0; store v0->slot0     b1: reload v0<-slot0; use v0
        let insts = vec![
            adv_inst(
                1,
                vec![MachOperand::VReg(vreg(0))],
                vec![MachOperand::Imm(7)],
            ), // 0
            si_store(0, 0),                                        // 1
            si_load(0, 0),                                         // 2
            adv_inst(2, vec![], vec![MachOperand::VReg(vreg(0))]), // 3
        ];
        let post = si_func(
            insts,
            vec![
                (vec![InstId(0), InstId(1)], vec![BlockId(1)]),
                (vec![InstId(2), InstId(3)], vec![]),
            ],
        );
        assert!(
            si_run(&post).is_valid(),
            "a split whose store dominates its reload must validate"
        );
    }

    /// The 990628-1.c shape: a diamond whose store sits on ONLY ONE arm, with
    /// the reload at the join. The join is reached from the store-free arm on a
    /// path the store does not dominate — REJECTED, naming the slot and the
    /// offending predecessor.
    #[test]
    fn slotinit_uninit_path_split_rejected() {
        // b0: br                b1: store v0->slot0     b2: (nothing)
        // b3: reload v0<-slot0; use v0
        let insts = vec![
            adv_inst(9, vec![], vec![]), // 0  (b0 terminator)
            si_store(0, 0),              // 1  (b1)
            adv_inst(9, vec![], vec![]), // 2  (b2 filler)
            si_load(0, 0),               // 3  (b3)
            adv_inst(2, vec![], vec![MachOperand::VReg(vreg(0))]), // 4  (b3 use)
        ];
        let post = si_func(
            insts,
            vec![
                (vec![InstId(0)], vec![BlockId(1), BlockId(2)]), // b0
                (vec![InstId(1)], vec![BlockId(3)]),             // b1 (stores)
                (vec![InstId(2)], vec![BlockId(3)]),             // b2 (no store)
                (vec![InstId(3), InstId(4)], vec![]),            // b3 (reload at join)
            ],
        );
        let errs = si_uninit_errors(&si_run(&post));
        assert_eq!(
            errs,
            vec![(BlockId(3), StackSlotId(0), Some(BlockId(2)))],
            "the join reload of a slot stored on only one arm must be rejected, \
             naming slot0, block b3, and the store-free predecessor b2"
        );
    }

    /// Call-convention save/restore shape (`call_clobber`): a PSEUDO_SPILL_STORE
    /// (the save) immediately precedes the reload (the restore) in the same
    /// block, around a call. The store is RECOGNIZED as an initializer, so the
    /// reload is definite-init — ACCEPTED (no false positive on a legitimate
    /// save/restore).
    #[test]
    fn slotinit_call_convention_stores_recognized() {
        let insts = vec![
            si_store(0, 3),                // save x-reg to slot3 before call
            adv_inst(100, vec![], vec![]), // the call
            si_load(0, 3),                 // restore after call
            adv_inst(2, vec![], vec![MachOperand::VReg(vreg(0))]),
        ];
        let post = si_func(
            insts,
            vec![(vec![InstId(0), InstId(1), InstId(2), InstId(3)], vec![])],
        );
        assert!(
            si_run(&post).is_valid(),
            "a save-before-call / restore-after-call pair must validate"
        );
    }

    /// A slot stored on one arm and reloaded ONLY on that same arm (in a block
    /// reached only through the store) — the other arm neither stores nor
    /// reloads. The reload is definite-init on every path that reaches it, even
    /// though the slot is dead-and-uninitialized on the sibling arm. ACCEPTED
    /// (precision care ii: dead-on-other-paths is exactly what definite-init
    /// handles).
    #[test]
    fn slotinit_dead_path_reload_accepted() {
        //          b0: br {b1, b2}
        //   b1(idx1): store slot0 -> b1b        b2(idx2): filler -> b3
        //   b1b(idx3): reload slot0; use -> b3  b3(idx4): join
        let insts = vec![
            adv_inst(9, vec![], vec![]),                           // 0 b0
            si_store(0, 0),                                        // 1 b1
            si_load(0, 0),                                         // 2 b1b reload
            adv_inst(2, vec![], vec![MachOperand::VReg(vreg(0))]), // 3 b1b use
            adv_inst(9, vec![], vec![]),                           // 4 b2 filler
            adv_inst(9, vec![], vec![]),                           // 5 b3 join
        ];
        let post = si_func(
            insts,
            vec![
                (vec![InstId(0)], vec![BlockId(1), BlockId(2)]), // b0 idx0
                (vec![InstId(1)], vec![BlockId(3)]),             // b1 idx1: store -> b1b
                (vec![InstId(4)], vec![BlockId(4)]),             // b2 idx2: no store -> b3
                (vec![InstId(2), InstId(3)], vec![BlockId(4)]),  // b1b idx3: reload -> b3
                (vec![InstId(5)], vec![]),                       // b3 idx4: join
            ],
        );
        assert!(
            si_run(&post).is_valid(),
            "a reload only on the path where the store happened must validate"
        );
    }

    /// Loop, correct: the store is in the PREHEADER (dominates the loop). The
    /// reload in the loop body is definite-init on every iteration — the
    /// optimistic-seed fixpoint must NOT spuriously mark it uninitialized across
    /// the back edge. ACCEPTED.
    #[test]
    fn slotinit_preheader_store_loop_reload_accepted() {
        // b0 preheader: store slot0   b1 header: br   b2 body: reload; br b1/b3   b3 exit
        let insts = vec![
            si_store(0, 0),              // 0 b0
            adv_inst(9, vec![], vec![]), // 1 b1 header
            si_load(0, 0),               // 2 b2 body reload
            adv_inst(9, vec![], vec![]), // 3 b2 latch branch
            adv_inst(9, vec![], vec![]), // 4 b3 exit
        ];
        let post = si_func(
            insts,
            vec![
                (vec![InstId(0)], vec![BlockId(1)]),             // b0 preheader
                (vec![InstId(1)], vec![BlockId(2), BlockId(3)]), // b1 header
                (vec![InstId(2), InstId(3)], vec![BlockId(1)]),  // b2 body -> back to header
                (vec![InstId(4)], vec![]),                       // b3 exit
            ],
        );
        assert!(
            si_run(&post).is_valid(),
            "a preheader store that dominates the loop must validate the in-loop reload"
        );
    }

    /// Loop, buggy: the store is INSIDE the body, AFTER the reload. On the first
    /// iteration the reload runs before any store — uninitialized. REJECTED
    /// (the fixpoint must not optimistically assume the back-edge store on the
    /// first iteration).
    #[test]
    fn slotinit_loop_reload_before_store_rejected() {
        // b0: br    b1 header: br    b2 body: reload slot0; store slot0; br b1/b3    b3 exit
        let insts = vec![
            adv_inst(9, vec![], vec![]), // 0 b0
            adv_inst(9, vec![], vec![]), // 1 b1 header
            si_load(0, 0),               // 2 b2 reload (before store)
            si_store(0, 0),              // 3 b2 store
            adv_inst(9, vec![], vec![]), // 4 b3 exit
        ];
        let post = si_func(
            insts,
            vec![
                (vec![InstId(0)], vec![BlockId(1)]),             // b0
                (vec![InstId(1)], vec![BlockId(2), BlockId(3)]), // b1 header
                (vec![InstId(2), InstId(3)], vec![BlockId(1)]),  // b2 body
                (vec![InstId(4)], vec![]),                       // b3 exit
            ],
        );
        let errs = si_uninit_errors(&si_run(&post));
        assert_eq!(
            errs,
            vec![(BlockId(2), StackSlotId(0), Some(BlockId(1)))],
            "an in-loop reload before its in-loop store is uninitialized on the \
             first iteration and must be rejected"
        );
    }

    /// A slot that is NEVER stored but IS reloaded (a dropped connector store):
    /// every reload is uninitialized. REJECTED. Confirms the universe scoping
    /// (a reload-only slot never enters any init set).
    #[test]
    fn slotinit_never_stored_slot_rejected() {
        let insts = vec![
            si_load(0, 0), // 0 reload of a slot with no store anywhere
            adv_inst(2, vec![], vec![MachOperand::VReg(vreg(0))]),
        ];
        let post = si_func(insts, vec![(vec![InstId(0), InstId(1)], vec![])]);
        let errs = si_uninit_errors(&si_run(&post));
        assert_eq!(
            errs.len(),
            1,
            "a never-stored reloaded slot must be rejected"
        );
        assert_eq!(errs[0].1, StackSlotId(0));
        assert_eq!(errs[0].2, None, "uninitialized straight from entry");
    }

    /// FAITHFUL RECONSTRUCTION of the gcc-c-torture 990628-1.c `load_data`
    /// miscompile as it reaches the validator (the PSEUDO-spill form of the
    /// greedy-split disasm captured in `split_repro/s_load.s`, exit 139 / SIGSEGV
    /// as a fail-SILENT miscompile the OLD validator reported CLEAN on). One
    /// spill slot is stored on the non-loop path AND in the return-prep block,
    /// but reloaded UNINITIALIZED on the loop-exit path that the store does not
    /// dominate. The new gate REJECTS it — fail-silent -> fail-closed.
    ///
    /// CFG (block @ s_load.s address; slot = `[x29, #-0x58]`):
    /// ```text
    ///   b0 @0x52c  setup; cmp; cbnz x0 -> {b1 (not-taken), b2 (taken)}
    ///   b1 @0x5dc  STORE slot; b -> b3
    ///   b2 @0x5e8  loop preheader        -> b4
    ///   b4 @0x5fc  loop body; b.eq       -> {b5 (exit), b4 (back-edge)}
    ///   b3 @0x63c  STORE slot; RELOAD slot (dominated, OK) -> b6
    ///   b5 @0x678  RELOAD slot  <-- UNINITIALIZED on the loop path (0x684) -> b6
    ///   b6 @0x64c  epilogue; ret
    /// ```
    #[test]
    fn slotinit_repro_990628_load_data_rejected() {
        let insts = vec![
            adv_inst(9, vec![], vec![]), // 0  b0 entry (cbnz)
            si_store(0, 0),              // 1  b1 @0x5dc STORE slot0
            adv_inst(9, vec![], vec![]), // 2  b2 preheader
            si_store(0, 0),              // 3  b3 @0x640 STORE slot0
            si_load(0, 0),               // 4  b3 @0x644 RELOAD slot0 (dominated)
            adv_inst(9, vec![], vec![]), // 5  b4 loop body
            si_load(0, 0),               // 6  b5 @0x684 RELOAD slot0 (UNINIT)
            adv_inst(9, vec![], vec![]), // 7  b6 epilogue
        ];
        let post = si_func(
            insts,
            vec![
                (vec![InstId(0)], vec![BlockId(1), BlockId(2)]), // b0 idx0
                (vec![InstId(1)], vec![BlockId(3)]),             // b1 idx1 store
                (vec![InstId(2)], vec![BlockId(4)]),             // b2 idx2 preheader
                (vec![InstId(3), InstId(4)], vec![BlockId(6)]),  // b3 idx3 store+reload
                (vec![InstId(5)], vec![BlockId(5), BlockId(4)]), // b4 idx4 loop body
                (vec![InstId(6)], vec![BlockId(6)]),             // b5 idx5 loop-exit reload
                (vec![InstId(7)], vec![]),                       // b6 idx6 epilogue
            ],
        );
        let errs = si_uninit_errors(&si_run(&post));
        assert_eq!(
            errs,
            vec![(BlockId(5), StackSlotId(0), Some(BlockId(4)))],
            "the loop-exit reload of load_data's slot (stored only on the non-loop \
             path) must be rejected, naming slot0, the loop-exit block b5, and the \
             store-free loop-body predecessor b4 — the exact 990628-1.c miscompile"
        );
    }

    /// REFUTE CONTROL for the 990628 class through the FULL validator: the same
    /// split-connector shape, built as a complete (pre, post, result) triple the
    /// way the splitter + spill inserter actually emit it — the connector is a
    /// FRESH vreg (v9, outside the pre spec's namespace) defined by an inserted
    /// PSEUDO_COPY with its PSEUDO_SPILL_STORE immediately adjacent (so gate (d)
    /// adjacency HOLDS), reload immediately before its consumer, and the
    /// original use rewritten to the split temp (which property (a)'s split-temp
    /// namespace carve-out SKIPS — the documented trust boundary). Historical
    /// gates (a)-(d) all accept this triple — the class was fail-SILENT — and
    /// ONLY the new gate (e) fires, on the loop-exit reload the b1 store does
    /// not dominate. This is the fail-silent -> fail-closed conversion,
    /// demonstrated inside the shipped validator.
    #[test]
    fn slotinit_full_validator_990628_shape_only_new_gate_fires() {
        // pre (SSA spec, v1 the base value; v9 does NOT exist here):
        //   b0: i0 v1=imm; i1 br {b1,b2}
        //   b1: i2 filler          b2: i3 filler (-> loop preheader)
        //   b3: i4 filler          b4: i5 filler (loop body, latch)
        //   b5: i6 filler          b6: i7 use v1
        let pre_insts = vec![
            adv_inst(
                1,
                vec![MachOperand::VReg(vreg(1))],
                vec![MachOperand::Imm(7)],
            ), // i0
            adv_inst(9, vec![], vec![]),                           // i1
            adv_inst(9, vec![], vec![]),                           // i2
            adv_inst(9, vec![], vec![]),                           // i3
            adv_inst(9, vec![], vec![]),                           // i4
            adv_inst(9, vec![], vec![]),                           // i5
            adv_inst(9, vec![], vec![]),                           // i6
            adv_inst(2, vec![], vec![MachOperand::VReg(vreg(1))]), // i7
        ];
        let blocks = vec![
            (vec![InstId(0), InstId(1)], vec![BlockId(1), BlockId(2)]), // b0
            (vec![InstId(2)], vec![BlockId(3)]),                        // b1 (non-loop arm)
            (vec![InstId(3)], vec![BlockId(4)]),                        // b2 preheader
            (vec![InstId(4)], vec![BlockId(6)]),                        // b3
            (vec![InstId(5)], vec![BlockId(5), BlockId(4)]),            // b4 loop body
            (vec![InstId(6)], vec![BlockId(6)]),                        // b5 loop exit
            (vec![InstId(7)], vec![]),                                  // b6 join/ret
        ];
        let pre = si_func(pre_insts.clone(), blocks.clone());

        // post: the split materialization. Inserted insts (ids >= 8):
        //   b1: p8  PSEUDO_COPY v9 <- v1 ; p9  STORE v9 -> slot0   (adjacent: (d) ok)
        //   b3: p10 COPY v9 <- v1 ; p11 STORE v9 ; p12 RELOAD v9   (dominated reload)
        //   b5: p13 RELOAD v9 <- slot0 ; i6's use rewritten to v9, immediately
        //       after the reload (per-use-site materialization, so gate (d)
        //       adjacency HOLDS)   <-- reload UNINITIALIZED on the loop path
        let mut post_insts = pre_insts;
        post_insts.push(adv_inst(
            PSEUDO_COPY,
            vec![MachOperand::VReg(vreg(9))],
            vec![MachOperand::VReg(vreg(1))],
        )); // 8
        post_insts.push(si_store(9, 0)); // 9
        post_insts.push(adv_inst(
            PSEUDO_COPY,
            vec![MachOperand::VReg(vreg(9))],
            vec![MachOperand::VReg(vreg(1))],
        )); // 10
        post_insts.push(si_store(9, 0)); // 11
        post_insts.push(si_load(9, 0)); // 12
        post_insts.push(si_load(9, 0)); // 13
        // i6 (b5's original inst) consumes the reloaded split temp.
        post_insts[6] = adv_inst(2, vec![], vec![MachOperand::VReg(vreg(9))]);
        let post_blocks = vec![
            (vec![InstId(0), InstId(1)], vec![BlockId(1), BlockId(2)]),
            (vec![InstId(2), InstId(8), InstId(9)], vec![BlockId(3)]),
            (vec![InstId(3)], vec![BlockId(4)]),
            (
                vec![InstId(4), InstId(10), InstId(11), InstId(12)],
                vec![BlockId(6)],
            ),
            (vec![InstId(5)], vec![BlockId(5), BlockId(4)]),
            (vec![InstId(13), InstId(6)], vec![BlockId(6)]),
            (vec![InstId(7)], vec![]),
        ];
        let post = si_func(post_insts, post_blocks);

        let mut allocation = BTreeMap::new();
        allocation.insert(vreg(1), PReg::new(0));
        let result = AllocationResult {
            allocation,
            spills: vec![crate::linear_scan::SpillInfo {
                vreg: vreg(9),
                slot: StackSlotId(0),
            }],
        };

        let report = validate_allocation(&pre, &post, &result);
        assert!(
            !report.is_valid(),
            "the 990628 split-connector shape must be rejected by the full validator"
        );
        assert!(
            report
                .errors
                .iter()
                .all(|e| matches!(e, ValidationError::SpillSlotUninitializedReload { .. })),
            "REFUTE CONTROL: gates (a)-(d) must all accept this triple (the class \
             was fail-SILENT before gate (e)); got {:?}",
            report.errors
        );
        assert!(
            report.errors.iter().any(|e| matches!(
                e,
                ValidationError::SpillSlotUninitializedReload {
                    block: BlockId(5),
                    slot: StackSlotId(0),
                    uninit_pred: Some(BlockId(4)),
                    ..
                }
            )),
            "gate (e) must name the loop-exit block b5, slot0, and the store-free \
             loop predecessor b4: {:?}",
            report.errors
        );

        // POSITIVE CONTROL: hoisting the connector store to b0 (dominating every
        // reload) makes the SAME triple validate — the gate rejects placement,
        // not splitting itself.
        let mut fixed = post.clone();
        fixed.blocks[0].insts = vec![InstId(0), InstId(8), InstId(9), InstId(1)];
        fixed.blocks[1].insts = vec![InstId(2)];
        let report = validate_allocation(&pre, &fixed, &result);
        assert!(
            report.is_valid(),
            "a dominating connector store must validate, got {:?}",
            report.errors
        );
    }
}
