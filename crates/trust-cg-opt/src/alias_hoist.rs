// trust-cg-opt - Alias-versioned loop-invariant load hoisting
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Alias-versioned loop-invariant load hoisting (LICM tier (c)).
//!
//! A late, machine-level pass that hoists loop-invariant loads out of an inner
//! loop that ALSO writes memory — the case ordinary [`crate::licm`] refuses
//! because it cannot statically prove the loads are disjoint from the store
//! (all-runtime-heap pointers give `AddrBase::Unknown`). Instead of proving
//! disjointness at compile time, this pass emits a RUNTIME BYTE-RANGE
//! DISJOINTNESS check (the regime-C shape shipped by `neon_map`) and VERSIONS
//! the loop:
//!
//! ```text
//!   preheader ── B ──▶ check-chain ──all-disjoint──▶ fast preheader (hoisted
//!                          │                                loads) ──▶ CLONE of
//!                          │                                the loop (loads gone)
//!                          └──any-overlap──▶ original loop (untouched, slow)
//! ```
//!
//! The check compares the STORE's byte range `[store_lo, store_hi)` against
//! each hoisted-load byte range `[load_lo, load_hi)` with the exact clang
//! condition `store_hi <=u load_lo || load_hi <=u store_lo` (unsigned pointer
//! compares). When EVERY pair is disjoint the store provably never clobbers any
//! hoisted address, so the loads read the same value on every iteration and are
//! safe to hoist to the fast preheader; on ANY possible overlap control falls
//! to the original loop, which is left completely intact — so the transform is
//! sound independent of any alias claim.
//!
//! # Soundness obligations (all fail-closed)
//!
//!  * **Address invariance.** Each hoisted load is a plain `LdrRI dst, base,
//!    #imm` whose base is loop-invariant and single-def (the `licm` invariance
//!    engine, reconstructed here — including its refusal of NZCV readers, whose
//!    flag input is not in the operand list; see [`is_invariance_movable`]).
//!  * **Speculation / fault safety.** The pass fires only when the preheader
//!    UNCONDITIONALLY enters the loop (sole successor is the header) and each
//!    hoisted load's block DOMINATES the latch and every loop-exiting block —
//!    i.e. the address is already dereferenced on iteration 1, so hoisting it
//!    to the (guaranteed-reached) fast preheader introduces no new fault. This
//!    also means the loop cannot be zero-trip, so no zero-trip path can reach
//!    the speculated loads.
//!  * **Store-range boundedness.** Every memory writer in the body must be a
//!    boundable store: a fixed `Str*RI base,#imm` (single-element range) or an
//!    indexed `StrRO base, iv, <<scale` whose index is a counted induction
//!    variable starting at 0, stepping by a positive constant, and bounded
//!    above by an invariant `B` via `cmp iv+step, B; b.eq/ge/hs exit` — giving
//!    `iv ∈ [0, B)` and store range `[base, base + B*scale)`. Any call,
//!    barrier, atomic, or unrecognized writer fails the loop closed.
//!  * **Clone integrity.** The fast path is a full clone of the loop body.
//!    Values defined only inside the body are renamed to fresh vregs; the
//!    loop-carried "phi" vregs (defined both inside and outside the body) are
//!    SHARED with the original because the original preheader — which still runs
//!    on both paths — initializes them, and only one of the two loops ever runs.
//!    A body-internal value that is LIVE-OUT of the loop fails the loop closed
//!    (its renamed clone value would not reach the outside use).
//!
//! Runs at O2/O3 AFTER `scalar-unroll` + `ext-addr` (so it sees the folded
//! `ldr [base,#imm]` invariant loads the full-unroll exposes) and BEFORE the
//! scheduler. Kill switch: `TRUST_CG_DISABLE_PASSES=aliashoist`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, ProvenanceMap, RegClass,
    VReg,
};

use crate::dom::DomTree;
use crate::effects::{
    aarch64_for_each_use_position, for_each_inst_def, inst_defines_vreg, opcode_effect,
    reads_flags, single_inst_def,
};
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::MachinePass;

// AArch64 condition codes (numeric encodings, matching the encoder contract).
const CC_EQ: i64 = 0;
const CC_HS: i64 = 2;
const CC_GE: i64 = 10;
const CC_LS: i64 = 9; // unsigned lower-or-same

/// Dev trace hook (`TRUST_CG_TRACE_ALIASHOIST`).
fn trace(msg: &str) {
    if std::env::var_os("TRUST_CG_TRACE_ALIASHOIST").is_some() {
        eprintln!("[aliashoist] {msg}");
    }
}

/// Alias-versioned loop-invariant load hoisting pass.
pub struct AliasVersionedLoadHoist;

impl MachinePass for AliasVersionedLoadHoist {
    fn name(&self) -> &str {
        "alias-hoist"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        // Whole-function cheap pre-filter: the transform needs at least one
        // plain load AND one boundable store somewhere. Bail before touching the
        // dominator tree / loop analysis when either ingredient is absent (most
        // functions), so non-candidates pay only an O(insts) scan.
        let mut any_load = false;
        let mut any_store = false;
        for inst in &func.insts {
            if load_access_size(inst).is_some() {
                any_load = true;
            }
            if store_access_size(inst).is_some() {
                any_store = true;
            }
        }
        if !any_load || !any_store {
            return false;
        }
        // A single fresh dominator tree + loop analysis. `run_with_analyses` is
        // intentionally NOT implemented: this pass runs right after ext-addr,
        // which invalidates any cached analysis, so the cache is always cold in
        // this slot — the shared-analysis path would only add two clones.
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        run_impl(func, &dom, &loops)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        _provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run(func)
    }
}

/// Process loops innermost-first and version-hoist the FIRST one that matches
/// every gate. Firing mutates the CFG (adds blocks) and invalidates the loop
/// analysis, so at most one loop is transformed per invocation — the loop
/// analysis is single-shot. The transform is self-limiting under a fixpoint
/// pipeline: the slow (original) loop's new preheader is a check block with two
/// successors, so it fails the `preheader_enters_loop` gate on any re-run, and
/// the fast clone has no hoistable loads left.
fn run_impl(func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
    let mut ordered: Vec<NaturalLoop> = loops.all_loops().cloned().collect();
    ordered.sort_by_key(|lp| std::cmp::Reverse(lp.depth));
    for lp in &ordered {
        if try_version_hoist(func, dom, lp) {
            return true;
        }
    }
    false
}

// ===========================================================================
// Recognition
// ===========================================================================

/// A loop-invariant plain load selected for hoisting.
struct HoistLoad {
    inst: InstId,
    dst: VReg,
    base: VReg,
    off: i64,
    size: i64,
}

/// The union of a base register's hoisted-load addresses, as a single bounding
/// byte range `[base + min_off, base + max_end)` covering every load with that
/// base. Disjointness against the bounding range implies disjointness against
/// every member load, so one check covers a whole group.
struct LoadGroup {
    base: VReg,
    min_off: i64,
    max_end: i64,
}

/// A soundly-bounded store byte range. `lo`/`hi` are expressed as `base + k`
/// (fixed store) or `[base, base + bound*scale)` (indexed store).
enum StoreRange {
    /// `[base + off_lo, base + off_hi)` — a single fixed store address.
    Fixed {
        base: VReg,
        off_lo: i64,
        off_hi: i64,
    },
    /// `[base, base + bound*scale)` — an indexed store whose index runs `[0,
    /// bound)`.
    Indexed {
        base: VReg,
        bound: Bound,
        scale: i64,
    },
}

/// A loop bound value: an invariant register (whose def dominates the
/// preheader) or a reconstructed compile-time constant.
enum Bound {
    Reg(VReg),
    Const(i64),
}

/// Attempt to alias-version and load-hoist a single loop. Returns true on a
/// committed transform.
fn try_version_hoist(func: &mut MachFunction, dom: &DomTree, lp: &NaturalLoop) -> bool {
    let header = lp.header;

    // (G1) Natural preheader that UNCONDITIONALLY enters the loop. This gives
    // both the zero-trip fault guarantee and a single clean redirect point.
    let Some(preheader) = lp.preheader else {
        return false;
    };
    {
        let succs = &func.block(preheader).succs;
        if succs.len() != 1 || succs[0] != header {
            trace(&format!(
                "hdr {header:?}: preheader not unconditional-entry"
            ));
            return false;
        }
    }
    // The preheader's branch to the header (redirected into the check chain).
    let Some(preheader_term) = func
        .block(preheader)
        .insts
        .iter()
        .rev()
        .copied()
        .find(|&id| branch_targets(func.inst(id)).contains(&header))
    else {
        return false;
    };

    // Cheap early-out: the transform needs at least one plain load AND one
    // memory writer in the body. Skip the heavy invariance analysis otherwise.
    let mut has_plain_load = false;
    let mut has_writer = false;
    for &block_id in &lp.body {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            if load_access_size(inst).is_some() {
                has_plain_load = true;
            }
            let eff = opcode_effect(inst.opcode);
            if eff.writes_memory() || eff.is_barrier() {
                has_writer = true;
            }
        }
    }
    if !has_plain_load || !has_writer {
        return false;
    }

    let def_counts = build_def_counts(func);
    let loop_defs = build_loop_defs(func, &lp.body);
    let invariant = compute_invariants(func, lp, &loop_defs, &def_counts);

    // (G2) Guaranteed-execution exit set (dominated by candidate load blocks).
    // Collect hoistable, guaranteed-to-execute, invariant plain loads.
    let mut hoisted: Vec<HoistLoad> = Vec::new();
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            let Some(size) = load_access_size(inst) else {
                continue;
            };
            // Plain base+imm load shape: def, base (op1), const offset (op2).
            let Some(&MachOperand::VReg(dst)) = inst.operands.first() else {
                continue;
            };
            if def_counts.get(&dst).copied().unwrap_or(0) != 1 {
                continue;
            }
            if inst_touches_fixed_register(inst) {
                continue;
            }
            let Some(&MachOperand::VReg(base)) = inst.operands.get(1) else {
                continue;
            };
            let Some(off) = inst.operands.get(2).and_then(imm_of) else {
                continue;
            };
            // Address invariance: the base must be loop-invariant.
            if !is_vreg_invariant(base, &loop_defs, &invariant, &def_counts) {
                continue;
            }
            // Speculation safety: the load must be guaranteed to execute.
            if !load_guaranteed_to_execute(func, dom, lp, block_id) {
                continue;
            }
            hoisted.push(HoistLoad {
                inst: inst_id,
                dst,
                base,
                off,
                size,
            });
        }
    }
    trace(&format!(
        "hdr {header:?}: {} hoistable loads",
        hoisted.len()
    ));
    if hoisted.is_empty() {
        return false;
    }

    // (G3) Bound every memory writer in the body. Any writer we cannot bound
    // (call, barrier, atomic, unrecognized store, non-invariant base) fails the
    // loop closed.
    let mut stores: Vec<StoreRange> = Vec::new();
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            let eff = opcode_effect(inst.opcode);
            if !(eff.writes_memory() || eff.is_barrier()) {
                continue;
            }
            match bound_store(
                func,
                dom,
                lp,
                inst,
                preheader,
                &loop_defs,
                &invariant,
                &def_counts,
            ) {
                Some(range) => stores.push(range),
                None => {
                    trace(&format!(
                        "hdr {header:?}: unbounded writer {:?}",
                        inst.opcode
                    ));
                    return false; // opaque / unboundable writer
                }
            }
        }
    }
    if stores.is_empty() {
        // No writers means ordinary LICM already had license; nothing to do.
        return false;
    }

    // (G4) Clone integrity: a body-internal (renamed) value must not be
    // live-out of the loop. Loop-carried (shared) values are exempt.
    let (body_defs, outside_defs) = body_and_outside_defs(func, &lp.body);
    if body_internal_value_is_live_out(func, &lp.body, &body_defs, &outside_defs) {
        trace(&format!("hdr {header:?}: body-internal value live-out"));
        return false;
    }
    trace(&format!(
        "hdr {header:?}: FIRING ({} loads, {} stores)",
        hoisted.len(),
        stores.len()
    ));

    // Group hoisted loads by base to minimize the number of checks. A bounding
    // range per base is a sound over-approximation.
    let groups = group_loads(&hoisted);

    // Offsets must fit the constant-add emitter; else fail closed.
    for g in &groups {
        if !off_encodable(g.min_off) || !off_encodable(g.max_end) {
            return false;
        }
    }
    for s in &stores {
        if let StoreRange::Fixed { off_lo, off_hi, .. } = s
            && (!off_encodable(*off_lo) || !off_encodable(*off_hi))
        {
            return false;
        }
    }

    // (G5) The load/store BASE values (and any register bound) must be available
    // before the loop. A base can be an invariant value COMPUTED INSIDE the body
    // (e.g. ext-addr's `madd base, 0, scale, real_base` address artifact); the
    // pure invariant slice that computes it is hoisted into the preamble. If any
    // base's slice is not a pure invariant chain, fail closed.
    let mut roots: Vec<VReg> = Vec::new();
    for h in &hoisted {
        roots.push(h.base);
    }
    for s in &stores {
        match s {
            StoreRange::Fixed { base, .. } => roots.push(*base),
            StoreRange::Indexed { base, bound, .. } => {
                roots.push(*base);
                if let Bound::Reg(v) = bound {
                    roots.push(*v);
                }
            }
        }
    }
    let Some(slice) = collect_invariant_slice(func, &roots, &lp.body, &invariant) else {
        trace(&format!("hdr {header:?}: base slice not hoistable"));
        return false;
    };

    commit(
        func,
        lp,
        preheader,
        preheader_term,
        &hoisted,
        &groups,
        &stores,
        &body_defs,
        &outside_defs,
        &slice,
    );
    true
}

/// Collect the pure, loop-invariant instruction slice (deps-first) that computes
/// every `root` value inside the body. A root defined OUTSIDE the body is
/// already available and contributes nothing. Returns `None` if any root
/// resolves to an in-body value that is not a pure invariant (unhoistable).
fn collect_invariant_slice(
    func: &MachFunction,
    roots: &[VReg],
    body: &HashSet<BlockId>,
    invariant: &HashSet<VReg>,
) -> Option<Vec<InstId>> {
    let def_map = build_def_map(func);
    let mut order: Vec<InstId> = Vec::new();
    let mut done: HashSet<VReg> = HashSet::new();
    let mut on_stack: HashSet<VReg> = HashSet::new();
    for &r in roots {
        visit_slice(
            func,
            r,
            body,
            invariant,
            &def_map,
            &mut order,
            &mut done,
            &mut on_stack,
        )?;
    }
    Some(order)
}

#[allow(clippy::too_many_arguments)]
fn visit_slice(
    func: &MachFunction,
    v: VReg,
    body: &HashSet<BlockId>,
    invariant: &HashSet<VReg>,
    def_map: &HashMap<VReg, InstId>,
    order: &mut Vec<InstId>,
    done: &mut HashSet<VReg>,
    on_stack: &mut HashSet<VReg>,
) -> Option<()> {
    if done.contains(&v) {
        return Some(());
    }
    let Some(&def_id) = def_map.get(&v) else {
        // No tracked def (e.g. an ABI copy) — treat as already available.
        done.insert(v);
        return Some(());
    };
    let in_body = block_of_inst(func, def_id).is_some_and(|b| body.contains(&b));
    if !in_body {
        done.insert(v); // defined outside the loop — available as-is
        return Some(());
    }
    if !invariant.contains(&v) {
        return None; // in-body but not invariant — cannot hoist
    }
    if on_stack.contains(&v) {
        return None; // cycle among invariants — bail
    }
    let inst = func.inst(def_id);
    // Same movement contract as `compute_invariants` (see
    // [`is_invariance_movable`]): a flag reader re-materialized here would
    // execute in the preamble, where NZCV is the ORIGINAL preheader's leftover
    // state and no compare of its own has run.
    if !is_invariance_movable(inst)
        || single_inst_def(inst) != Some(v)
        || inst_touches_fixed_register(inst)
    {
        return None;
    }
    on_stack.insert(v);
    let mut uses = Vec::new();
    aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
        if let Some(MachOperand::VReg(u)) = inst.operands.get(pos) {
            uses.push(*u);
        }
    });
    for u in uses {
        visit_slice(func, u, body, invariant, def_map, order, done, on_stack)?;
    }
    on_stack.remove(&v);
    done.insert(v);
    order.push(def_id);
    Some(())
}

/// Bound a single store's byte range, or `None` if it is not a shape we can
/// soundly bound.
#[allow(clippy::too_many_arguments)]
fn bound_store(
    func: &MachFunction,
    dom: &DomTree,
    lp: &NaturalLoop,
    inst: &MachInst,
    preheader: BlockId,
    loop_defs: &HashMap<VReg, InstId>,
    invariant: &HashSet<VReg>,
    def_counts: &HashMap<VReg, usize>,
) -> Option<StoreRange> {
    match inst.opcode {
        // Fixed base+immediate store: a single element at `base + imm`.
        AArch64Opcode::StrRI | AArch64Opcode::StrbRI | AArch64Opcode::StrhRI => {
            let base = vreg_of(inst.operands.get(1)?)?;
            if !is_vreg_invariant(base, loop_defs, invariant, def_counts) {
                return None;
            }
            let off = imm_of(inst.operands.get(2)?)?;
            let elem = store_access_size(inst)?;
            Some(StoreRange::Fixed {
                base,
                off_lo: off,
                off_hi: off.checked_add(elem)?,
            })
        }
        // Indexed store: `base + extend(idx) << log2(scale)`. The index must be
        // a counted IV in `[0, bound)` and the scale must equal the transfer
        // size (S=1), so the whole written region is `[base, base+bound*scale)`.
        AArch64Opcode::StrRO => {
            let base = vreg_of(inst.operands.get(1)?)?;
            if !is_vreg_invariant(base, loop_defs, invariant, def_counts) {
                return None;
            }
            let idx = vreg_of(inst.operands.get(2)?)?;
            let packed = imm_of(inst.operands.get(3)?)?;
            // S bit must be set: index is scaled by log2(transfer size).
            if packed & 1 == 0 {
                return None;
            }
            let scale = store_access_size(inst)?;
            let bound = recognize_counted_index(func, dom, lp, idx, preheader, def_counts)?;
            // A constant bound is materialized as `Movz #(bound*scale)`, which
            // only encodes a 16-bit immediate; reject an out-of-range product
            // (a register bound is fine — it is shifted, not materialized).
            if let Bound::Const(k) = &bound
                && !k
                    .checked_mul(scale)
                    .is_some_and(|n| (0..=0xFFFF).contains(&n))
            {
                return None;
            }
            Some(StoreRange::Indexed { base, bound, scale })
        }
        _ => None,
    }
}

/// Recognize `idx` as a counted induction variable of `lp` that provably takes
/// values in `[0, bound)` at every store, and return `bound`.
///
/// Requires (fail-closed on any deviation):
///  * `idx` is initialized to the constant 0 by a def OUTSIDE the loop body
///    (the preheader/dominating init).
///  * `idx` has exactly ONE in-body def, a copy of a step value `step`.
///  * `step = AddRI(idx, #c)` with `c >= 1` (monotone increasing).
///  * a body block ends `CmpRR/CmpRI(step, bound); BCond(EQ|GE|HS) -> <exit>`
///    (the compare immediately before the branch, comparing the STEP value),
///    with the branch leaving the loop body — so the loop continues only while
///    `step` has not reached `bound`, pinning `idx < bound`.
fn recognize_counted_index(
    func: &MachFunction,
    dom: &DomTree,
    lp: &NaturalLoop,
    idx: VReg,
    preheader: BlockId,
    def_counts: &HashMap<VReg, usize>,
) -> Option<Bound> {
    let def_map = build_def_map(func);

    // The single in-body def of `idx`, and any out-of-body defs (the init).
    let mut in_body_def: Option<InstId> = None;
    let mut has_outside_def = false;
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            if !inst_defines_vreg(inst, idx) {
                continue;
            }
            if lp.body.contains(&block_id) {
                if in_body_def.is_some() {
                    return None; // more than one in-body def
                }
                in_body_def = Some(inst_id);
            } else {
                has_outside_def = true;
                // The init must be a dominating, non-negative constant 0.
                if !dom.dominates(block_id, preheader) {
                    return None;
                }
                if resolve_const(func, &def_map, idx, inst_id) != Some(0) {
                    return None;
                }
            }
        }
    }
    if !has_outside_def {
        return None;
    }
    let body_def = in_body_def?;

    // `idx <- copy(step)`  (the loop-carried write in the latch).
    let step = copy_src(func.inst(body_def))?;
    // `step = AddRI(idx, #c)`, c >= 1.
    let step_def = func.inst(*def_map.get(&step)?);
    if step_def.opcode != AArch64Opcode::AddRI {
        return None;
    }
    if vreg_of(step_def.operands.first()?)? != step {
        return None;
    }
    if vreg_of(step_def.operands.get(1)?)? != idx {
        return None;
    }
    let c = imm_of(step_def.operands.get(2)?)?;
    if c < 1 {
        return None;
    }

    // The exit test: a BCond leaving the body, preceded immediately by a
    // compare of `step` against the bound.
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        let insts = &func.block(block_id).insts;
        let Some(p) = insts.iter().position(|&id| {
            let i = func.inst(id);
            i.opcode == AArch64Opcode::BCond
                && matches!(imm_of(&i.operands[0]), Some(CC_EQ | CC_GE | CC_HS))
                && branch_targets(i).iter().any(|t| !lp.body.contains(t))
        }) else {
            continue;
        };
        if p == 0 {
            continue;
        }
        // The test must gate every loop continuation, i.e. dominate every
        // back-edge source. Otherwise an iteration could skip the test, step the
        // index past `bound`, and store out of the `[0, bound)` range — a range
        // under-approximation, which is a miscompile.
        let gates_backedges = lp
            .body
            .iter()
            .all(|&b| !func.block(b).succs.contains(&lp.header) || dom.dominates(block_id, b));
        if !gates_backedges {
            continue;
        }
        let cmp = func.inst(insts[p - 1]);
        match cmp.opcode {
            AArch64Opcode::CmpRR => {
                if vreg_of(cmp.operands.first()?)? != step {
                    continue;
                }
                let b = vreg_of(cmp.operands.get(1)?)?;
                // Bound must be invariant and dominate the preheader, or a const.
                if let Some(&bdef) = def_map.get(&b)
                    && def_counts.get(&b).copied().unwrap_or(0) == 1
                    && let Some(bblk) = block_of_inst(func, bdef)
                    && !lp.body.contains(&bblk)
                    && dom.dominates(bblk, preheader)
                {
                    return Some(Bound::Reg(b));
                }
                if let Some(k) = resolve_const_vreg(func, &def_map, b)
                    && k >= 1
                {
                    return Some(Bound::Const(k));
                }
            }
            AArch64Opcode::CmpRI => {
                if vreg_of(cmp.operands.first()?)? != step {
                    continue;
                }
                let k = imm_of(cmp.operands.get(1)?)?;
                if k >= 1 {
                    return Some(Bound::Const(k));
                }
            }
            _ => {}
        }
    }
    None
}

// ===========================================================================
// Commit (CFG construction)
// ===========================================================================

#[allow(clippy::too_many_arguments)]
fn commit(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    preheader: BlockId,
    preheader_term: InstId,
    hoisted: &[HoistLoad],
    groups: &[LoadGroup],
    stores: &[StoreRange],
    body_defs: &HashSet<VReg>,
    outside_defs: &HashSet<VReg>,
    slice: &[InstId],
) {
    let header = lp.header;

    // Fresh blocks: preamble, per (store,group) check pair, fast preheader.
    let pre = func.create_block();
    let mut checks: Vec<(BlockId, BlockId)> = Vec::new();
    for _ in 0..stores.len() * groups.len() {
        checks.push((func.create_block(), func.create_block()));
    }
    let fh = func.create_block();

    // Clone the loop body (fresh internal vregs; shared loop-carried vregs;
    // hoisted-load dsts mapped to their preheader values).
    let (block_map, header_clone, hoist_values) =
        clone_body(func, lp, hoisted, body_defs, outside_defs);

    // --- Preamble, part 1: recompute the invariant base slice with fresh vregs
    // so the check chain and the hoisted loads have their bases available before
    // the loop. `ph` maps each in-body base value to its preamble copy; a base
    // defined outside the loop is unmapped (used as-is). ---
    let ph = emit_slice(func, pre, slice);
    let ph_base = |v: VReg| -> VReg { ph.get(&v.id).copied().unwrap_or(v) };

    // --- Preamble, part 2: materialize the store and group range endpoints. ---
    // Each store's [lo, hi).
    let mut store_ep: Vec<(MachOperand, MachOperand)> = Vec::new();
    for s in stores {
        let (lo, hi) = match s {
            StoreRange::Fixed {
                base,
                off_lo,
                off_hi,
            } => {
                let base = ph_base(*base);
                (
                    add_const(func, pre, base, *off_lo),
                    add_const(func, pre, base, *off_hi),
                )
            }
            StoreRange::Indexed { base, bound, scale } => {
                let base = ph_base(*base);
                let bound = match bound {
                    Bound::Reg(v) => Bound::Reg(ph_base(*v)),
                    Bound::Const(k) => Bound::Const(*k),
                };
                let nbytes = emit_bound_bytes(func, pre, &bound, *scale);
                let hi = alloc(func, RegClass::Gpr64);
                emit(
                    func,
                    pre,
                    AArch64Opcode::AddRR,
                    vec![vreg(hi), vreg(base), vreg(nbytes)],
                );
                (vreg(base), vreg(hi))
            }
        };
        store_ep.push((lo, hi));
    }
    // Each group's [lo, hi).
    let mut group_ep: Vec<(MachOperand, MachOperand)> = Vec::new();
    for g in groups {
        let base = ph_base(g.base);
        let lo = add_const(func, pre, base, g.min_off);
        let hi = add_const(func, pre, base, g.max_end);
        group_ep.push((lo, hi));
    }
    emit(func, pre, AArch64Opcode::B, vec![block(checks[0].0)]);
    func.add_edge(pre, checks[0].0);

    // --- Check chain: for each (store, group) pair, prove disjointness. ---
    let mut pair = 0usize;
    for (si, (s_lo, s_hi)) in store_ep.iter().enumerate() {
        for (gi, (g_lo, g_hi)) in group_ep.iter().enumerate() {
            let (c1, c2) = checks[pair];
            let is_last = si == store_ep.len() - 1 && gi == group_ep.len() - 1;
            let ok = if is_last { fh } else { checks[pair + 1].0 };
            // c1: store_hi <=u group_lo  (store entirely below group) => disjoint.
            emit(
                func,
                c1,
                AArch64Opcode::CmpRR,
                vec![s_hi.clone(), g_lo.clone()],
            );
            emit(func, c1, AArch64Opcode::BCond, vec![imm(CC_LS), block(ok)]);
            emit(func, c1, AArch64Opcode::B, vec![block(c2)]);
            func.add_edge(c1, ok);
            func.add_edge(c1, c2);
            // c2: group_hi <=u store_lo  (group entirely below store) => disjoint.
            emit(
                func,
                c2,
                AArch64Opcode::CmpRR,
                vec![g_hi.clone(), s_lo.clone()],
            );
            emit(func, c2, AArch64Opcode::BCond, vec![imm(CC_LS), block(ok)]);
            emit(func, c2, AArch64Opcode::B, vec![block(header)]); // overlap => slow loop
            func.add_edge(c2, ok);
            func.add_edge(c2, header);
            pair += 1;
        }
    }

    // --- Fast preheader: the hoisted loads (reading the recomputed bases),
    // then enter the clone. ---
    for h in hoisted {
        let hv = hoist_values[&h.dst.id]; // fresh dst set up by clone_body
        emit_load_like(func, fh, h.inst, hv, ph_base(h.base), h.off);
    }
    emit(func, fh, AArch64Opcode::B, vec![block(header_clone)]);
    func.add_edge(fh, header_clone);

    // --- Redirect the original preheader into the check chain. ---
    rewrite_block_target(func.inst_mut(preheader_term), header, pre);
    remove_cfg_edge(func, preheader, header);
    func.add_edge(preheader, pre);

    // --- Layout: place fresh blocks just before the header. ---
    let mut fresh: Vec<BlockId> = vec![pre];
    for (c1, c2) in &checks {
        fresh.push(*c1);
        fresh.push(*c2);
    }
    fresh.push(fh);
    // Clone blocks in body iteration order for locality.
    for (_orig, cl) in block_map.iter_ordered() {
        fresh.push(*cl);
    }
    insert_new_blocks_before(func, header, &fresh);
}

/// Deterministic block clone map preserving insertion order.
struct BlockMap {
    map: HashMap<BlockId, BlockId>,
    order: Vec<(BlockId, BlockId)>,
}

impl BlockMap {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
            order: Vec::new(),
        }
    }
    fn insert(&mut self, orig: BlockId, clone: BlockId) {
        self.map.insert(orig, clone);
        self.order.push((orig, clone));
    }
    fn get(&self, orig: BlockId) -> Option<BlockId> {
        self.map.get(&orig).copied()
    }
    fn iter_ordered(&self) -> impl Iterator<Item = &(BlockId, BlockId)> {
        self.order.iter()
    }
}

/// Clone every body block. Returns the block map, the clone of the header, and
/// the map from each hoisted-load dst to its fresh preheader value.
///
/// Renaming rule:
///  * hoisted-load dst  -> a fresh preheader vreg (returned in `hoist_values`);
///    the load itself is NOT cloned into the body.
///  * body-internal def (in `body_defs`, not in `outside_defs`) -> fresh vreg.
///  * loop-carried / invariant vregs -> kept (shared).
fn clone_body(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    hoisted: &[HoistLoad],
    body_defs: &HashSet<VReg>,
    outside_defs: &HashSet<VReg>,
) -> (BlockMap, BlockId, HashMap<u32, VReg>) {
    // Body blocks in deterministic block_order sequence.
    let body_order: Vec<BlockId> = func
        .block_order
        .iter()
        .copied()
        .filter(|b| lp.body.contains(b))
        .collect();

    // Create clone blocks.
    let mut block_map = BlockMap::new();
    for &b in &body_order {
        let cl = func.create_block();
        block_map.insert(b, cl);
    }

    // Build the vreg rename map.
    let hoisted_insts: HashSet<InstId> = hoisted.iter().map(|h| h.inst).collect();
    let mut rename: HashMap<u32, VReg> = HashMap::new();
    let mut hoist_values: HashMap<u32, VReg> = HashMap::new();
    // Hoisted-load dsts map to fresh preheader values.
    for h in hoisted {
        let hv = alloc(func, h.dst.class);
        rename.insert(h.dst.id, hv);
        hoist_values.insert(h.dst.id, hv);
    }
    // Body-internal defs (not loop-carried) get fresh vregs. Mint them in
    // ascending vreg order: `body_defs` is a HashSet, and its per-process
    // random iteration order would otherwise decide WHICH fresh id each body
    // def receives, leaking hash-seed nondeterminism into downstream
    // allocation order and breaking reproducible builds (same .ll input must
    // yield byte-identical objects).
    let mut internal_defs: Vec<VReg> = body_defs
        .iter()
        .copied()
        .filter(|v| !outside_defs.contains(v))
        .collect();
    internal_defs.sort_unstable();
    for v in internal_defs {
        rename.entry(v.id).or_insert_with(|| alloc(func, v.class));
    }

    // Clone instructions block by block.
    for &b in &body_order {
        let cl = block_map.get(b).unwrap();
        let inst_ids: Vec<InstId> = func.block(b).insts.clone();
        for id in inst_ids {
            if hoisted_insts.contains(&id) {
                continue; // hoisted out — not present in the fast body
            }
            let src = func.inst(id);
            let opcode = src.opcode;
            let source_loc = src.source_loc;
            let new_operands: Vec<MachOperand> = src
                .operands
                .iter()
                .map(|op| match op {
                    MachOperand::VReg(v) => MachOperand::VReg(*rename.get(&v.id).unwrap_or(v)),
                    MachOperand::Block(t) => MachOperand::Block(block_map.get(*t).unwrap_or(*t)),
                    other => other.clone(),
                })
                .collect();
            let mut new_inst = MachInst::new(opcode, new_operands);
            new_inst.source_loc = source_loc;
            let new_id = func.push_inst(new_inst);
            func.append_inst(cl, new_id);
        }
    }

    // Wire clone CFG: intra-body succ -> clone; exit succ -> same (adds a pred).
    for &b in &body_order {
        let cl = block_map.get(b).unwrap();
        let succs: Vec<BlockId> = func.block(b).succs.clone();
        for s in succs {
            let target = block_map.get(s).unwrap_or(s);
            func.add_edge(cl, target);
        }
    }

    let header_clone = block_map.get(lp.header).unwrap();
    (block_map, header_clone, hoist_values)
}

// ===========================================================================
// Invariance / liveness helpers (reconstructing the LICM engine locally)
// ===========================================================================

/// Machine-MOVEMENT purity, the admission predicate for the invariance engine.
///
/// [`opcode_effect`] classifies MEMORY effects only. `Csel`, `CSet`, `Csinc`,
/// `Csinv`, `Csneg`, `FcselRR`, `Adc` and `Sbc` are all `MemoryEffect::Pure`
/// yet consume NZCV — an input that is NOT in their explicit operand list — so
/// the operand-only test in [`compute_invariants`] would certify one as
/// "loop-invariant" while its value changes with every flag write in the body.
/// Two things then break at once:
///
///  * a hoisted load whose BASE is such a value is not address-invariant at
///    all, so the fast clone reads iteration 1's address on every iteration
///    (and a store base likewise makes the disjointness check prove the wrong
///    range); and
///  * [`emit_slice`] re-materializes the flag reader in the PREAMBLE, which is
///    reached from the original preheader — there is no compare there at all,
///    so it selects on whatever NZCV the caller happened to leave.
///
/// `licm.rs` does not have this hole because it admits on
/// [`crate::interfaces::OpInterfaces::is_pure`], the machine movement contract,
/// which rejects flag readers and writers; this pass reconstructed the engine
/// locally on the weaker memory predicate. Flag WRITERS need no gate here: the
/// slice is only ever COPIED into the preamble (the original stays in the
/// body, so the loop's own flag sequence is untouched), and nothing the
/// preamble or the check chain executes reads NZCV before writing it — every
/// check block opens with its own `CmpRR`. Flag READERS are the whole gap, and
/// this fails them closed.
fn is_invariance_movable(inst: &MachInst) -> bool {
    opcode_effect(inst.opcode).is_pure() && !reads_flags(inst.opcode)
}

fn compute_invariants(
    func: &MachFunction,
    lp: &NaturalLoop,
    loop_defs: &HashMap<VReg, InstId>,
    def_counts: &HashMap<VReg, usize>,
) -> HashSet<VReg> {
    let mut invariant: HashSet<VReg> = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for &block_id in &func.block_order {
            if !lp.body.contains(&block_id) {
                continue;
            }
            for &inst_id in &func.block(block_id).insts {
                let inst = func.inst(inst_id);
                if !is_invariance_movable(inst) {
                    continue;
                }
                if inst.is_branch() || inst.is_terminator() || inst.opcode.is_phi() {
                    continue;
                }
                let Some(def) = single_inst_def(inst) else {
                    continue;
                };
                if def_counts.get(&def).copied().unwrap_or(0) != 1 || invariant.contains(&def) {
                    continue;
                }
                if inst_touches_fixed_register(inst) {
                    continue;
                }
                let mut all_inv = true;
                aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                    if !inst.operands.get(pos).is_some_and(|op| {
                        is_operand_invariant(op, loop_defs, &invariant, def_counts)
                    }) {
                        all_inv = false;
                    }
                });
                if all_inv {
                    invariant.insert(def);
                    changed = true;
                }
            }
        }
    }
    invariant
}

fn is_operand_invariant(
    op: &MachOperand,
    loop_defs: &HashMap<VReg, InstId>,
    invariant: &HashSet<VReg>,
    def_counts: &HashMap<VReg, usize>,
) -> bool {
    match op {
        MachOperand::VReg(v) => is_vreg_invariant(*v, loop_defs, invariant, def_counts),
        MachOperand::Imm(_) | MachOperand::FImm(_) | MachOperand::Symbol(_) => true,
        _ => false,
    }
}

fn is_vreg_invariant(
    v: VReg,
    loop_defs: &HashMap<VReg, InstId>,
    invariant: &HashSet<VReg>,
    def_counts: &HashMap<VReg, usize>,
) -> bool {
    if def_counts.get(&v).copied().unwrap_or(0) != 1 {
        return false;
    }
    if loop_defs.contains_key(&v) {
        invariant.contains(&v)
    } else {
        true // defined outside the loop
    }
}

/// LICM must-execute test: the load block dominates EVERY back-edge source (all
/// latches, not just `lp.latch` — a merged multi-latch body can have several)
/// AND every loop-exiting block. Together with the caller's unconditional-entry
/// gate this guarantees the load ran on iteration 1 in the original, so
/// hoisting it into the fast preheader introduces no new fault.
fn load_guaranteed_to_execute(
    func: &MachFunction,
    dom: &DomTree,
    lp: &NaturalLoop,
    load_block: BlockId,
) -> bool {
    for &b in &lp.body {
        let succs = &func.block(b).succs;
        let is_latch = succs.contains(&lp.header);
        let is_exiting = succs.iter().any(|s| !lp.body.contains(s));
        if (is_latch || is_exiting) && !dom.dominates(load_block, b) {
            return false;
        }
    }
    true
}

/// (body_defs, outside_defs) over value-producing definitions.
fn body_and_outside_defs(
    func: &MachFunction,
    body: &HashSet<BlockId>,
) -> (HashSet<VReg>, HashSet<VReg>) {
    let mut body_defs = HashSet::new();
    let mut outside_defs = HashSet::new();
    for &block_id in &func.block_order {
        let in_body = body.contains(&block_id);
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            for_each_inst_def(inst, |d| {
                if in_body {
                    body_defs.insert(d);
                } else {
                    outside_defs.insert(d);
                }
            });
        }
    }
    (body_defs, outside_defs)
}

/// True if some body-internal (non-loop-carried) value is used outside the
/// loop body — the clone's renamed value would not reach that use.
fn body_internal_value_is_live_out(
    func: &MachFunction,
    body: &HashSet<BlockId>,
    body_defs: &HashSet<VReg>,
    outside_defs: &HashSet<VReg>,
) -> bool {
    for &block_id in &func.block_order {
        if body.contains(&block_id) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            let mut live_out = false;
            aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(pos)
                    && body_defs.contains(v)
                    && !outside_defs.contains(v)
                {
                    live_out = true;
                }
            });
            if live_out {
                return true;
            }
        }
    }
    false
}

fn group_loads(hoisted: &[HoistLoad]) -> Vec<LoadGroup> {
    let mut groups: Vec<LoadGroup> = Vec::new();
    for h in hoisted {
        if let Some(g) = groups.iter_mut().find(|g| g.base == h.base) {
            g.min_off = g.min_off.min(h.off);
            g.max_end = g.max_end.max(h.off + h.size);
        } else {
            groups.push(LoadGroup {
                base: h.base,
                min_off: h.off,
                max_end: h.off + h.size,
            });
        }
    }
    groups
}

// ===========================================================================
// Low-level IR helpers
// ===========================================================================

fn vreg(v: VReg) -> MachOperand {
    MachOperand::VReg(v)
}
fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn block(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}
fn vreg_of(op: &MachOperand) -> Option<VReg> {
    match op {
        MachOperand::VReg(v) => Some(*v),
        _ => None,
    }
}
fn imm_of(op: &MachOperand) -> Option<i64> {
    match op {
        MachOperand::Imm(v) => Some(*v),
        _ => None,
    }
}

fn emit(
    func: &mut MachFunction,
    b: BlockId,
    op: AArch64Opcode,
    operands: Vec<MachOperand>,
) -> InstId {
    let id = func.push_inst(MachInst::new(op, operands));
    func.append_inst(b, id);
    id
}

/// Allocate a vreg id strictly greater than every id currently in use (matching
/// the NEON passes' collision-free allocator).
fn alloc(func: &mut MachFunction, class: RegClass) -> VReg {
    let max_existing = func
        .insts
        .iter()
        .flat_map(|inst| inst.operands.iter())
        .filter_map(vreg_of)
        .map(|v| v.id)
        .max()
        .unwrap_or(0);
    let mut id = func.alloc_vreg();
    while id <= max_existing {
        id = func.alloc_vreg();
    }
    VReg::new(id, class)
}

/// Emit the invariant base slice `slice` (deps-first order) into `b`, renaming
/// each defined value to a fresh vreg. Operands defined outside the slice keep
/// their original vreg. Returns the rename map (orig vreg id -> fresh vreg).
fn emit_slice(func: &mut MachFunction, b: BlockId, slice: &[InstId]) -> HashMap<u32, VReg> {
    let mut rename: HashMap<u32, VReg> = HashMap::new();
    for &id in slice {
        let src = func.inst(id);
        let opcode = src.opcode;
        let source_loc = src.source_loc;
        let Some(&MachOperand::VReg(old_dst)) = src.operands.first() else {
            continue;
        };
        let operands: Vec<MachOperand> = src.operands.clone();
        let fresh = alloc(func, old_dst.class);
        let new_ops: Vec<MachOperand> = operands
            .iter()
            .enumerate()
            .map(|(i, op)| {
                if i == 0 {
                    return vreg(fresh);
                }
                match op {
                    MachOperand::VReg(u) => vreg(*rename.get(&u.id).unwrap_or(u)),
                    other => other.clone(),
                }
            })
            .collect();
        let mut inst = MachInst::new(opcode, new_ops);
        inst.source_loc = source_loc;
        let new_id = func.push_inst(inst);
        func.append_inst(b, new_id);
        rename.insert(old_dst.id, fresh);
    }
    rename
}

/// Emit a copy of a hoisted load (`h.inst`'s opcode) into `b` writing `dst`,
/// reading `base + off`.
fn emit_load_like(
    func: &mut MachFunction,
    b: BlockId,
    src: InstId,
    dst: VReg,
    base: VReg,
    off: i64,
) {
    let opcode = func.inst(src).opcode;
    emit(func, b, opcode, vec![vreg(dst), vreg(base), imm(off)]);
}

/// `base + off` as an operand: `base` itself when `off == 0`, else a fresh
/// Gpr64 holding the sum. `off` is assumed encodable (checked by the caller).
fn add_const(func: &mut MachFunction, b: BlockId, base: VReg, off: i64) -> MachOperand {
    if off == 0 {
        return vreg(base);
    }
    let dst = alloc(func, RegClass::Gpr64);
    if (1..=4095).contains(&off) {
        emit(
            func,
            b,
            AArch64Opcode::AddRI,
            vec![vreg(dst), vreg(base), imm(off)],
        );
    } else {
        let c = alloc(func, RegClass::Gpr64);
        emit(func, b, AArch64Opcode::Movz, vec![vreg(c), imm(off)]);
        emit(
            func,
            b,
            AArch64Opcode::AddRR,
            vec![vreg(dst), vreg(base), vreg(c)],
        );
    }
    vreg(dst)
}

/// `bound * scale` bytes as a fresh Gpr64. `scale` is a power of two.
fn emit_bound_bytes(func: &mut MachFunction, b: BlockId, bound: &Bound, scale: i64) -> VReg {
    let sh = scale.trailing_zeros() as i64;
    match bound {
        Bound::Reg(v) => {
            if sh == 0 {
                // scale == 1: bytes == bound; copy into a Gpr64.
                let dst = alloc(func, RegClass::Gpr64);
                emit(func, b, AArch64Opcode::MovR, vec![vreg(dst), vreg(*v)]);
                dst
            } else {
                let dst = alloc(func, RegClass::Gpr64);
                emit(
                    func,
                    b,
                    AArch64Opcode::LslRI,
                    vec![vreg(dst), vreg(*v), imm(sh)],
                );
                dst
            }
        }
        Bound::Const(k) => {
            let dst = alloc(func, RegClass::Gpr64);
            emit(
                func,
                b,
                AArch64Opcode::Movz,
                vec![vreg(dst), imm(k * scale)],
            );
            dst
        }
    }
}

fn off_encodable(off: i64) -> bool {
    (0..=0xFFFF).contains(&off)
}

/// `MovR(d,s)` / `Copy(d,s)` / `AddRI(d,s,0)` copy source.
fn copy_src(inst: &MachInst) -> Option<VReg> {
    match inst.opcode {
        AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => {
            vreg_of(&inst.operands[1])
        }
        AArch64Opcode::AddRI
            if inst.operands.len() == 3 && imm_of(&inst.operands[2]) == Some(0) =>
        {
            vreg_of(&inst.operands[1])
        }
        _ => None,
    }
}

/// Resolve the constant value defined by `inst_id` for vreg `v`, following copy
/// idioms and `Movz`.
fn resolve_const(
    func: &MachFunction,
    def_map: &HashMap<VReg, InstId>,
    v: VReg,
    inst_id: InstId,
) -> Option<i64> {
    let inst = func.inst(inst_id);
    if let Some((dst, value)) = crate::reaching_const::movz_value(inst)
        && dst == v
        && let Ok(value) = i64::try_from(value)
    {
        return Some(value);
    }
    if let Some(src) = copy_src(inst) {
        let src_def = *def_map.get(&src)?;
        return resolve_const(func, def_map, src, src_def);
    }
    None
}

fn resolve_const_vreg(
    func: &MachFunction,
    def_map: &HashMap<VReg, InstId>,
    v: VReg,
) -> Option<i64> {
    let def = *def_map.get(&v)?;
    resolve_const(func, def_map, v, def)
}

fn branch_targets(inst: &MachInst) -> Vec<BlockId> {
    inst.operands
        .iter()
        .filter_map(|op| match op {
            MachOperand::Block(b) => Some(*b),
            _ => None,
        })
        .collect()
}

fn rewrite_block_target(inst: &mut MachInst, old: BlockId, new: BlockId) {
    for op in &mut inst.operands {
        if matches!(op, MachOperand::Block(b) if *b == old) {
            *op = MachOperand::Block(new);
        }
    }
}

fn remove_cfg_edge(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.block_mut(from).succs.retain(|&s| s != to);
    func.block_mut(to).preds.retain(|&p| p != from);
}

fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    for (idx, block) in func.blocks.iter().enumerate() {
        if block.insts.contains(&target) {
            return Some(BlockId(idx as u32));
        }
    }
    None
}

fn insert_new_blocks_before(func: &mut MachFunction, before: BlockId, new_blocks: &[BlockId]) {
    let mut reordered = Vec::with_capacity(func.block_order.len() + new_blocks.len());
    for &b in &func.block_order {
        if b == before {
            reordered.extend(new_blocks.iter().copied());
        }
        if !new_blocks.contains(&b) {
            reordered.push(b);
        }
    }
    func.block_order = reordered;
}

fn build_def_counts(func: &MachFunction) -> HashMap<VReg, usize> {
    let mut counts: HashMap<VReg, usize> = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            for_each_inst_def(inst, |def| {
                *counts.entry(def).or_insert(0) += 1;
            });
        }
    }
    counts
}

fn build_def_map(func: &MachFunction) -> HashMap<VReg, InstId> {
    crate::effects::build_reaching_def_map_by_vreg(func)
}

fn build_loop_defs(func: &MachFunction, body: &HashSet<BlockId>) -> HashMap<VReg, InstId> {
    let mut defs: HashMap<VReg, InstId> = HashMap::new();
    for &block_id in &func.block_order {
        if !body.contains(&block_id) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            for_each_inst_def(inst, |def| {
                defs.insert(def, inst_id);
            });
        }
    }
    defs
}

fn operand_touches_fixed_register(operand: &MachOperand) -> bool {
    matches!(
        operand,
        MachOperand::PReg(_) | MachOperand::MemOp { .. } | MachOperand::Special(_)
    )
}

fn inst_touches_fixed_register(inst: &MachInst) -> bool {
    !inst.implicit_defs.is_empty()
        || !inst.implicit_uses.is_empty()
        || inst.operands.iter().any(operand_touches_fixed_register)
}

/// Transfer size of a plain base+immediate load, or `None` for any other load
/// form (writeback, pair, register-offset, GOT/TLS/literal, atomic).
fn load_access_size(inst: &MachInst) -> Option<i64> {
    match inst.opcode {
        AArch64Opcode::LdrRI => Some(class_bytes(load_dst_class(inst)?)),
        AArch64Opcode::LdrbRI | AArch64Opcode::LdrsbRI => Some(1),
        AArch64Opcode::LdrhRI | AArch64Opcode::LdrshRI => Some(2),
        _ => None,
    }
}

fn load_dst_class(inst: &MachInst) -> Option<RegClass> {
    match inst.operands.first()? {
        MachOperand::VReg(v) => Some(v.class),
        _ => None,
    }
}

/// Transfer size of a store we can bound.
fn store_access_size(inst: &MachInst) -> Option<i64> {
    match inst.opcode {
        AArch64Opcode::StrRI | AArch64Opcode::StrRO => match inst.operands.first()? {
            MachOperand::VReg(v) => Some(class_bytes(v.class)),
            _ => None,
        },
        AArch64Opcode::StrbRI => Some(1),
        AArch64Opcode::StrhRI => Some(2),
        _ => None,
    }
}

/// An UPPER BOUND on the transfer width, in bytes, of a register class.
///
/// This feeds the byte range a store is assumed to clobber and the range a
/// hoisted load is assumed to read, and the runtime check then proves those
/// ranges disjoint. Only ONE direction of error is unsound: a range that is too
/// SMALL lets the pass prove a disjointness that does not hold and hoist a load
/// across its own clobber. A range that is too LARGE can only make the check
/// fail and send execution down the untouched slow loop.
///
/// The old `_ => 8` catch-all was therefore safe for every class NARROWER than
/// 8 bytes — and unsound for the one class that is WIDER: `Fpr128`, a 16-byte
/// `STR Q` / `LDR Q`, which the addressing-mode fold and the NEON vectorizers
/// both produce. That single under-estimate is corrected here.
///
/// The narrow classes deliberately keep the conservative 8: tightening them to
/// their exact widths is a separate, purely-permissive change that moves
/// shipping `-O1` code (measured: Linpack's disjointness check goes from
/// `lsl #3` to `lsl #2`), and it belongs in a round that can measure it rather
/// than riding along with a soundness fix. The match is exhaustive, so a new
/// `RegClass` variant is a compile error rather than a silent default.
fn class_bytes(class: RegClass) -> i64 {
    match class {
        RegClass::Fpr128 => 16,
        RegClass::Gpr64
        | RegClass::Fpr64
        | RegClass::System
        | RegClass::Gpr32
        | RegClass::Fpr32
        | RegClass::Fpr16
        | RegClass::Fpr8 => 8,
    }
}

#[cfg(test)]
mod tests;
