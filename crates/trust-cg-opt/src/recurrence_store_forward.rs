// trust-cg-opt - SOUND aarch64 loop-carried store-to-load forwarding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # Loop-carried store-to-load forwarding (`recurrence-store-forward`)
//!
//! Register-carries the memory recurrence of an innermost, counted, in-place
//! array recurrence of the shape
//!
//! ```text
//! let mut i = i0;                       // compile-time constant, i0 <u N
//! while i <u N { a[i + 1] = f(a[i], i); i += 1; }
//! ```
//!
//! The scalar bridge lowering re-LOADS `a[i]` each iteration even though the
//! previous iteration just STORED that exact address (`a[(i-1)+1]`), which puts
//! the store-to-load-forwarding latency (~4-5 cycles on Apple M4, and
//! address/predictor-sensitive run-to-run variance) on the loop-carried
//! critical path. LLVM register-carries this recurrence; this pass matches it:
//!
//! * PREHEADER (appended before its unconditional `B header` terminator):
//!   `tP = Madd(iv, scale, base); vS = LdrRI [tP]` — load `a[i0]` ONCE;
//! * DELETE every in-loop load of `a[iv]` (and its private address `Madd`), and
//!   rewrite their result uses to read `vS` — the register the loop's single
//!   store `StrRI vS -> [Madd(iv+1, scale, base)]` already carries. The
//!   recurrence `f` then runs register-to-register (`AddRR(vS, vS, ...)`), with
//!   ZERO copies added to the carried chain.
//!
//! ## Why this is SOUND (an in-place rewrite, argued in full)
//!
//! Let `w` be the access width (4 for `Gpr32`, 8 for `Gpr64`), `scale == w`,
//! and let "cycle" mean the recognized simple-cycle body: every body block has
//! exactly ONE in-loop successor, so one traversal `header -> ... -> latch`
//! executes every body instruction exactly once, in a fixed order `pos(.)`
//! (side exits abandon the traversal — and then the forwarded loads do not
//! execute either). Recognition REQUIRES `pos(load_j) <= pos(def vS) <
//! pos(store)` and that every read of a deleted load's result sits in
//! `(pos(load_j), pos(def vS)]`, and that `iv`'s copies feeding every address
//! are read strictly before the single in-loop `iv` redefinition.
//!
//! 1. VALUE EQUALITY (bit-exact). The load address at traversal `k` is
//!    `base + (i0+k)*w`; the single store at traversal `k-1` wrote
//!    `base + ((i0+k-1)+1)*w` — the SAME address, same width. Between that
//!    store and traversal `k`'s load position the cycle executes no other
//!    store, no call, and no atomic (closed-world opcode whitelist), so
//!    nothing can write the location in between: the loaded value IS the
//!    stored value. The stored value is `vS` read at `pos(store) > pos(def
//!    vS)`, and `vS` is not redefined in `(pos(def vS), pos(store))` (single
//!    in-loop def) nor in `(pos(store), next pos(load))` — so at traversal
//!    `k`'s load positions `vS` still holds exactly the traversal-`k-1` stored
//!    value. For `k == 0` the preheader load reads `base + i0*w` — the
//!    IDENTICAL address the deleted traversal-0 loads read — after every
//!    preceding preheader store and with no store on the path
//!    preheader-end -> header -> ... -> first load position (the cycle's store
//!    is positioned after the loads). Replacing each deleted load's result
//!    with `vS` at positions `<= pos(def vS)` therefore substitutes a
//!    bit-identical value. Reads of the result at positions AFTER `pos(def
//!    vS)` (which would observe the NEW `vS`) are rejected by recognition.
//! 2. NO NEW FAULTS. The only added memory access is the preheader load of
//!    `base + i0*w`. It executes exactly when control reaches the preheader's
//!    unconditional `B header` (REQUIRED terminator shape — a conditional
//!    preheader exit would let the load run on a path that never enters the
//!    loop), and the compile-time guard relation `i0 <u N` (`i0 <s N` for an
//!    `LT` guard; both consts are checked in range) proves the FIRST traversal
//!    always runs, so the original program dereferences the identical address
//!    itself: same access, same width, no new fault. Deleting loads cannot
//!    fault.
//! 3. TRAPS/STORES/EXITS UNTOUCHED. The store, every compare/branch, and any
//!    `TrapBoundsCheck*` guard carrier stay byte-for-byte in place and in
//!    order, and the stored VALUE register is untouched — post-transform
//!    memory and abort behavior are identical under ANY outside aliasing
//!    (only the loop's own single store can write between the forwarded pair).
//! 4. GATE FOOTPRINT. Deleting loads only shrinks the emitted-opcode set; the
//!    added `Madd`/`LdrRI` are opcodes this pass's target loop already emits
//!    (and both are long-credited backend-wide). No new proof surface.
//!
//! Every unproven precondition BAILS (fail-closed, closed-world): exactly one
//! store of the exact `StrRI [vS, Madd(iv+1, #w, base), #0]` shape; EVERY
//! in-loop load is `LdrRI [Madd(iv, #w, base), #0]` with width class == `vS`
//! class; `iv: Gpr64` with exactly one in-loop redefinition
//! `MovR(iv, AddRI(iv, 1))` and one dominating init def with a compile-time
//! constant value; loop-invariant `base` and single-def `Movz #w` scale, the
//! SAME vregs at every access (`scale == w` keeps consecutive cells disjoint);
//! `vS` single-def func-wide, defined in the cycle, never read outside it; no
//! call/atomic/other store/unknown opcode anywhere in the body.
//!
//! Runs right AFTER `aarch64-bounds-check-elim` (the clean bounds-elided body
//! is the recognized shape) and BEFORE the unrollers/vectorizers. Default-ON
//! at O2/Os/O3 (never O0/O1). Compile-time kill switch:
//! `TCG_NO_RECURRENCE_STORE_FWD` (run() becomes a no-op). Per-pass bisect:
//! `TRUST_CG_DISABLE_PASSES=recurrence_store_fwd`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

#[cfg(test)]
mod tests;

/// AArch64 condition code for unsigned lower (`LO`).
const CC_LO: i64 = 3;
/// AArch64 condition code for signed less-than (`LT`).
const CC_LT: i64 = 11;

/// Compile-time kill switch: set `TCG_NO_RECURRENCE_STORE_FWD` (any value) to
/// disable the pass (run() is a no-op). Default ON at O2/Os/O3.
fn rsf_enabled() -> bool {
    std::env::var_os("TCG_NO_RECURRENCE_STORE_FWD").is_none()
}

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `recurrence-store-forward` machine pass.
#[derive(Default)]
pub struct RecurrenceStoreForward {
    fired: usize,
}

impl RecurrenceStoreForward {
    pub fn new() -> Self {
        Self { fired: 0 }
    }
    /// Loops forwarded in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for RecurrenceStoreForward {
    fn name(&self) -> &str {
        "recurrence-store-forward"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if !rsf_enabled() {
            return false;
        }
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        if !rsf_enabled() {
            return false;
        }
        let loops = analyses.loop_analysis(func).clone();
        let changed = {
            let dom = analyses.domtree(func);
            self.run_core(func, dom, &loops)
        };
        if changed {
            analyses.invalidate();
        }
        changed
    }
}

impl RecurrenceStoreForward {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;
        // Recognize first (read-only). Applying a plan appends fresh
        // instructions and unlinks instructions of ITS OWN cycle/preheader
        // only; `InstId`s are never renumbered, and distinct innermost loops
        // have disjoint bodies, so recognized data for other loops stays valid
        // UNLESS two loops share a preheader block — the unconditional
        // `B header` terminator requirement makes that impossible (a block has
        // one terminator target).
        let mut plans = Vec::new();
        for lp in loops.all_loops() {
            let is_innermost = loops
                .all_loops()
                .all(|other| other.header == lp.header || !lp.body.contains(&other.header));
            if !is_innermost {
                continue;
            }
            if let Some(rec) = Recognized::recognize(func, dom, lp.header, lp.latch, &lp.body) {
                plans.push(rec);
            }
        }
        let mut changed = false;
        for rec in plans {
            apply(func, &rec);
            self.fired += 1;
            changed = true;
        }
        if changed && std::env::var("TRUST_CG_DUMP_RSF").is_ok() {
            eprintln!(
                "[recurrence-store-forward] fn={} forwarded={}",
                func.name, self.fired
            );
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// A cycle-relative instruction position: (block rank on the forced traversal
/// `header -> ... -> latch`, instruction index within the block).
type CyclePos = (usize, usize);

struct Recognized {
    /// The preheader block; its terminator is the REQUIRED unconditional
    /// `B header` (single successor), so appended code runs iff the loop is
    /// entered.
    preheader: BlockId,
    /// The `Gpr64` induction with exactly one in-loop redefinition
    /// `MovR(iv, AddRI(iv, 1))` and one dominating init def.
    iv: VReg,
    /// The loop-invariant base pointer (same vreg at every access).
    base: VReg,
    /// The single-def `Movz #scale` register (same vreg at every access);
    /// `scale` equals the access byte width.
    scale_reg: VReg,
    /// The forwarded register: the single store's value, single-def func-wide.
    vs: VReg,
    /// Every in-loop load: (load `InstId`, its result vreg, its address `Madd`
    /// `InstId`, the address dst vreg, block of the load, block of the Madd).
    loads: Vec<LoadSite>,
}

struct LoadSite {
    load_id: InstId,
    load_block: BlockId,
    dst: VReg,
    madd_id: InstId,
    madd_block: BlockId,
    madd_dst: VReg,
}

impl Recognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        let dump = std::env::var("TRUST_CG_DUMP_RSF").is_ok();
        macro_rules! bail {
            ($($t:tt)*) => {{
                if dump {
                    eprintln!(
                        "[recurrence-store-forward] bail@{}: {}",
                        func.name,
                        format!($($t)*)
                    );
                }
                return None;
            }};
        }

        // (0) SIMPLE CYCLE: every body block has exactly ONE in-loop successor;
        // walking it from the header visits every body block exactly once and
        // returns to the header from the latch. This forces one fixed
        // execution order per traversal — the spine of the value argument.
        let Some(order) = cycle_order(func, header, latch, body) else {
            bail!("body is not a simple cycle");
        };
        let pos_of = build_pos_map(func, &order);
        let pos = |id: InstId| -> Option<CyclePos> { pos_of.get(&id).copied() };

        // (1) PREHEADER: unique non-latch header pred, terminated by an
        // UNCONDITIONAL `B header` (single successor). Anything appended
        // before that terminator executes iff the loop is entered (2. NO NEW
        // FAULTS depends on this).
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            bail!("header preds != {{latch, preheader}}: {:?}", hpreds);
        }
        let preheader = *hpreds.iter().find(|&&b| b != latch)?;
        if body.contains(&preheader) {
            bail!("preheader inside the body");
        }
        let ph_insts = &func.block(preheader).insts;
        let Some(&ph_term) = ph_insts.last() else {
            bail!("empty preheader");
        };
        let term = func.inst(ph_term);
        if term.opcode != AArch64Opcode::B
            || branch_targets(term) != vec![header]
            || func.block(preheader).succs.len() != 1
        {
            bail!("preheader terminator is not an unconditional `B header`");
        }
        // (2) CLOSED-WORLD opcode whitelist over the whole body; collect the
        // single store and every load.
        let mut store_ids: Vec<InstId> = Vec::new();
        let mut load_ids: Vec<(InstId, BlockId)> = Vec::new();
        for &b in &order {
            for &id in &func.block(b).insts {
                let op = func.inst(id).opcode;
                if !allowed_loop_op(op) {
                    bail!("disallowed body op {:?}", op);
                }
                if op == AArch64Opcode::StrRI {
                    store_ids.push(id);
                }
                if op == AArch64Opcode::LdrRI {
                    load_ids.push((id, b));
                }
            }
        }
        if store_ids.len() != 1 {
            bail!("expected exactly one store, found {}", store_ids.len());
        }
        if load_ids.is_empty() {
            bail!("no loads to forward");
        }
        let store_id = store_ids[0];
        let all_defs = build_all_defs(func);
        let single_def = |v: VReg| -> Option<InstId> {
            match all_defs.get(&v) {
                Some(ids) if ids.len() == 1 => Some(ids[0]),
                _ => None,
            }
        };

        // (3) INDUCTION: exactly one in-loop redefinition
        // `MovR(iv, AddRI(iv, 1))` of a Gpr64 `iv` (the AddRI's source may be
        // a single-def in-cycle copy of `iv` read before the redefinition).
        let cycle_insts: HashSet<InstId> = pos_of.keys().copied().collect();
        let Some((iv, redef_id)) = find_unit_induction(func, &all_defs, &cycle_insts, &order)
        else {
            bail!("no `iv = MovR(AddRI(iv, 1))` writeback");
        };
        let redef_pos = pos(redef_id)?;
        let defs_of_iv = all_defs.get(&iv)?;
        if defs_of_iv.len() != 2 {
            bail!("iv def count != 2 ({} defs)", defs_of_iv.len());
        }
        let &init_id = defs_of_iv.iter().find(|&&d| d != redef_id)?;
        if cycle_insts.contains(&init_id) {
            bail!("second iv def is inside the cycle");
        }
        let init_block = block_of_inst(func, init_id)?;
        if !dom.dominates(init_block, preheader) {
            bail!("iv init def does not dominate the preheader");
        }
        // `iv`'s init value must be a compile-time constant.
        let Some(iv0) = init_const_value(func, &single_def, init_id) else {
            bail!("iv init value is not a compile-time constant");
        };
        // `iv == iv0` WHENEVER control reaches the preheader. The appended
        // preheader load reads `base + iv*scale`; both its "no new fault"
        // justification (the first in-loop load dereferences this address,
        // proven live by trip >= 1 with `iv == iv0`) and the trip proof
        // (`iv0 < N`) need `iv == iv0` there. `init` DOMINATES the preheader
        // (checked above) so every path to the preheader passes through `init`
        // — but domination alone does NOT stop the in-cycle redef from reaching
        // the preheader AGAIN through an enclosing loop that never re-runs
        // `init` (e.g. `let mut iv = 0; for _ in 0..M { while iv < N { a[iv+1]
        // = f(a[iv], iv); iv += 1 } }` — on outer iterations 2..M `iv == N` at
        // the preheader, and with an outer-varying `base` the appended load
        // could fault out of bounds). Precise fail-closed test: no path from
        // the redef reaches the preheader WITHOUT re-passing `init`. When none
        // does, the last def of `iv` before every preheader visit is `init`
        // (= `iv0`) with no later redef, so `iv == iv0`. This ADMITS the
        // properly-reset nested case (d02's inner loop sits in the `reps`
        // loop, and `iv = 0` re-runs each outer iteration between the outer
        // back-edge and the preheader, so every redef -> preheader path passes
        // through it) and REJECTS the un-reset one.
        let redef_block = block_of_inst(func, redef_id)?;
        if reaches_avoiding(func, redef_block, preheader, init_block) {
            bail!("redef reaches the preheader without re-passing init (iv may not be iv0)");
        }

        // (4) GUARD / TRIP >= 1: the header holds `Cmp(iv-copy, N)` with a
        // constant `N` and a forward `BCond LO/LT` into the body, plus a
        // non-body exit successor; the constant relation `iv0 < N` (in the
        // guard's own signedness) proves the first traversal executes.
        let Some((n, guard_cc)) = recognize_const_bound(
            func,
            &single_def,
            &cycle_insts,
            &pos_of,
            body,
            header,
            iv,
            redef_pos,
        ) else {
            bail!("no native constant-bound `iv < N` continue test in header");
        };
        if !(0..=i64::from(u32::MAX)).contains(&iv0) || !(1..=i64::from(u32::MAX)).contains(&n) {
            bail!("iv0 {} / N {} out of range", iv0, n);
        }
        // Both consts are in [0, u32::MAX], where signed and unsigned i64
        // comparison agree.
        let trip_ge_1 = match guard_cc {
            CC_LO | CC_LT => iv0 < n,
            _ => false,
        };
        if !trip_ge_1 {
            bail!("cannot prove trip >= 1 (iv0={} N={})", iv0, n);
        }

        // (5) STORE: `StrRI [vS, addr, #0]` with
        // `addr := Madd(ivp1, scaleReg, base)`, `ivp1 := AddRI(iv-copy, 1)`,
        // all single-def, in-cycle, and read strictly before the iv
        // redefinition (so the address is `base + (iv+1)*scale` of THIS
        // traversal).
        let store = func.inst(store_id);
        let store_pos = pos(store_id)?;
        if store.operands.len() != 3 || imm_of(&store.operands[2]) != Some(0) {
            bail!("store shape not `StrRI [v, addr, #0]`");
        }
        let vs = vreg_of(&store.operands[0])?;
        let width: i64 = match vs.class {
            RegClass::Gpr32 => 4,
            RegClass::Gpr64 => 8,
            _ => bail!("store value class {:?} unsupported", vs.class),
        };
        let store_addr = vreg_of(&store.operands[1])?;
        let Some(store_madd) = single_def(store_addr).filter(|id| cycle_insts.contains(id)) else {
            bail!("store address is not a single-def in-cycle Madd");
        };
        let (sm_idx, sm_scale, sm_base) = madd_parts(func.inst(store_madd))?;
        let store_madd_pos = pos(store_madd)?;
        if store_madd_pos >= store_pos {
            bail!("store address Madd not before the store");
        }
        // scale register: single-def `Movz #width`, def outside the cycle,
        // dominating the preheader.
        let scale_reg = sm_scale;
        let Some(scale_def) = single_def(scale_reg) else {
            bail!("scale register is not single-def");
        };
        if cycle_insts.contains(&scale_def) {
            bail!("scale register defined in the cycle");
        }
        if movz_const(func.inst(scale_def)) != Some(width) {
            bail!("scale is not `Movz #{}` (access width)", width);
        }
        let Some(scale_block) = block_of_inst(func, scale_def) else {
            bail!("scale def not in a block");
        };
        if !dom.dominates(scale_block, preheader) {
            bail!("scale def does not dominate the preheader");
        }
        // base: loop-invariant (no def in the cycle, SOME def dominating the
        // preheader — the all-defs scan, as in strided-store-unroll).
        let base = sm_base;
        if !is_loop_invariant(func, &all_defs, dom, &cycle_insts, preheader, base) {
            bail!("base not loop-invariant");
        }
        if base == iv || base == scale_reg || base == vs {
            bail!("base aliases iv/scale/vS");
        }
        // store index: `AddRI(iv-copy, 1)` read before the redefinition.
        let Some(ivp1_def) = single_def(sm_idx).filter(|id| cycle_insts.contains(id)) else {
            bail!("store index is not a single-def in-cycle AddRI");
        };
        let ivp1 = func.inst(ivp1_def);
        if ivp1.opcode != AArch64Opcode::AddRI
            || ivp1.operands.len() != 3
            || imm_of(&ivp1.operands[2]) != Some(1)
        {
            bail!("store index def is not `AddRI(_, 1)`");
        }
        let ivp1_pos = pos(ivp1_def)?;
        if ivp1_pos >= store_madd_pos || ivp1_pos >= redef_pos {
            bail!("store index computed too late");
        }
        let ivp1_src = vreg_of(&ivp1.operands[1])?;
        if !is_iv_copy_before(
            func,
            &single_def,
            &pos_of,
            &cycle_insts,
            iv,
            ivp1_src,
            ivp1_pos,
            redef_pos,
        ) {
            bail!("store index source is not `iv` read before its redefinition");
        }

        // (6) vS: single def func-wide, in the cycle, positioned AFTER every
        // load and BEFORE the store (`pos(load) <= pos(def vS) < pos(store)`),
        // never read outside the cycle, and distinct from the loop plumbing.
        let Some(vs_def) = single_def(vs).filter(|id| cycle_insts.contains(id)) else {
            bail!("store value is not a single-def in-cycle register");
        };
        let vs_def_pos = pos(vs_def)?;
        if vs_def_pos >= store_pos {
            bail!("vS defined after the store");
        }
        if vs == iv || vs == base || vs == scale_reg {
            bail!("vS aliases loop plumbing");
        }
        for (idx, inst) in func.insts.iter().enumerate() {
            let id = InstId(idx as u32);
            if cycle_insts.contains(&id) {
                continue;
            }
            if reads_vreg(inst, vs) && is_linked(func, id) {
                bail!("vS is read outside the cycle");
            }
        }

        // (7) LOADS: EVERY in-loop load is
        // `LdrRI [dst, Madd(iv-copy, scaleReg, base), #0]` with `dst` class ==
        // `vS` class, `dst` single-def (the load), every read of `dst` inside
        // the cycle in `(pos(load), pos(def vS)]`, and the whole address chain
        // read before the iv redefinition.
        let mut loads = Vec::new();
        for (load_id, load_block) in load_ids {
            let load = func.inst(load_id);
            let load_pos = pos(load_id)?;
            if load.operands.len() != 3 || imm_of(&load.operands[2]) != Some(0) {
                bail!("load shape not `LdrRI [dst, addr, #0]`");
            }
            let dst = vreg_of(&load.operands[0])?;
            if dst.class != vs.class {
                bail!(
                    "load width class {:?} != vS class {:?}",
                    dst.class,
                    vs.class
                );
            }
            if single_def(dst) != Some(load_id) {
                bail!("load dst is not single-def");
            }
            if dst == vs || dst == iv || dst == base || dst == scale_reg {
                bail!("load dst aliases loop plumbing");
            }
            let addr = vreg_of(&load.operands[1])?;
            let Some(madd_id) = single_def(addr).filter(|id| cycle_insts.contains(id)) else {
                bail!("load address is not a single-def in-cycle Madd");
            };
            let (lm_idx, lm_scale, lm_base) = madd_parts(func.inst(madd_id))?;
            if lm_scale != scale_reg || lm_base != base {
                bail!("load Madd scale/base differ from the store's");
            }
            let madd_pos = pos(madd_id)?;
            if madd_pos >= load_pos {
                bail!("load address Madd not before the load");
            }
            if !is_iv_copy_before(
                func,
                &single_def,
                &pos_of,
                &cycle_insts,
                iv,
                lm_idx,
                madd_pos,
                redef_pos,
            ) {
                bail!("load index is not `iv` read before its redefinition");
            }
            if load_pos > vs_def_pos {
                bail!("load positioned after the vS def");
            }
            // Every read of `dst` sits inside the cycle in
            // `(pos(load), pos(def vS)]`: earlier reads would observe the
            // PREVIOUS traversal's value, later reads the NEW `vS`.
            for (idx, inst) in func.insts.iter().enumerate() {
                let id = InstId(idx as u32);
                if !reads_vreg(inst, dst) || !is_linked(func, id) || id == load_id {
                    continue;
                }
                let Some(use_pos) = pos(id) else {
                    bail!("load dst read outside the cycle");
                };
                if use_pos <= load_pos || use_pos > vs_def_pos {
                    bail!("load dst read outside (pos(load), pos(def vS)]");
                }
            }
            let madd_dst = vreg_of(&func.inst(madd_id).operands[0])?;
            let madd_block = block_of_inst(func, madd_id)?;
            loads.push(LoadSite {
                load_id,
                load_block,
                dst,
                madd_id,
                madd_block,
                madd_dst,
            });
        }

        if dump {
            eprintln!(
                "[recurrence-store-forward] RECOGNIZED@{} iv={:?} base={:?} vS={:?} \
                 loads={} iv0={} N={}",
                func.name,
                iv,
                base,
                vs,
                loads.len(),
                iv0,
                n
            );
        }
        Some(Recognized {
            preheader,
            iv,
            base,
            scale_reg,
            vs,
            loads,
        })
    }
}

/// Walk the body from `header` following each block's unique in-loop
/// successor; succeed iff every body block is visited exactly once and the
/// walk returns to the header from `latch`.
fn cycle_order(
    func: &MachFunction,
    header: BlockId,
    latch: BlockId,
    body: &HashSet<BlockId>,
) -> Option<Vec<BlockId>> {
    let mut order = Vec::with_capacity(body.len());
    let mut cur = header;
    loop {
        order.push(cur);
        let in_loop: Vec<BlockId> = func
            .block(cur)
            .succs
            .iter()
            .copied()
            .filter(|s| body.contains(s))
            .collect();
        if in_loop.len() != 1 {
            return None;
        }
        let next = in_loop[0];
        if next == header {
            // Closed the cycle: must be from the latch, having seen all blocks.
            if cur == latch && order.len() == body.len() {
                return Some(order);
            }
            return None;
        }
        if order.contains(&next) || order.len() > body.len() {
            return None;
        }
        cur = next;
    }
}

/// Map every body instruction to its cycle-relative position.
fn build_pos_map(func: &MachFunction, order: &[BlockId]) -> HashMap<InstId, CyclePos> {
    let mut map = HashMap::new();
    for (rank, &b) in order.iter().enumerate() {
        for (idx, &id) in func.block(b).insts.iter().enumerate() {
            map.insert(id, (rank, idx));
        }
    }
    map
}

/// Find the unit-strided induction: a cycle instruction
/// `MovR/Copy(d: Gpr64, s)` with `s := AddRI(x, 1)` (single-def, in-cycle) and
/// `x` resolving to `d` (directly, or through one single-def in-cycle copy).
/// Returns `(iv, redef_id)`; `None` unless exactly one such redefinition
/// exists.
fn find_unit_induction(
    func: &MachFunction,
    all_defs: &HashMap<VReg, Vec<InstId>>,
    cycle_insts: &HashSet<InstId>,
    order: &[BlockId],
) -> Option<(VReg, InstId)> {
    let single_def = |v: VReg| -> Option<InstId> {
        match all_defs.get(&v) {
            Some(ids) if ids.len() == 1 => Some(ids[0]),
            _ => None,
        }
    };
    let mut found: Option<(VReg, InstId)> = None;
    for &b in order {
        for &id in &func.block(b).insts {
            let Some((d, s)) = copy_like(func.inst(id)) else {
                continue;
            };
            if d.class != RegClass::Gpr64 {
                continue;
            }
            let Some(sdef) = single_def(s).filter(|i| cycle_insts.contains(i)) else {
                continue;
            };
            let si = func.inst(sdef);
            if si.opcode != AArch64Opcode::AddRI
                || si.operands.len() != 3
                || imm_of(&si.operands[2]) != Some(1)
            {
                continue;
            }
            let Some(x) = vreg_of(&si.operands[1]) else {
                continue;
            };
            // x == d directly, or x := MovR/Copy(d) single-def in-cycle.
            let is_iv = x == d
                || single_def(x)
                    .filter(|i| cycle_insts.contains(i))
                    .and_then(|i| copy_like(func.inst(i)))
                    .is_some_and(|(cd, cs)| cd == x && cs == d);
            if !is_iv {
                continue;
            }
            if found.is_some() {
                // More than one candidate induction: ambiguous, bail.
                return None;
            }
            found = Some((d, id));
        }
    }
    found
}

/// The header's `Cmp(iv-copy, N)` + forward `BCond LO/LT` into the body with a
/// non-body exit successor. Returns `(N, cc)`.
#[allow(clippy::too_many_arguments)]
fn recognize_const_bound(
    func: &MachFunction,
    single_def: &impl Fn(VReg) -> Option<InstId>,
    cycle_insts: &HashSet<InstId>,
    pos_of: &HashMap<InstId, CyclePos>,
    body: &HashSet<BlockId>,
    header: BlockId,
    iv: VReg,
    redef_pos: CyclePos,
) -> Option<(i64, i64)> {
    let insts = &func.block(header).insts;
    // Exactly ONE `BCond` in the header; it must be a forward `LO/LT` into the
    // body.
    let bconds: Vec<usize> = insts
        .iter()
        .enumerate()
        .filter(|&(_, &id)| func.inst(id).opcode == AArch64Opcode::BCond)
        .map(|(idx, _)| idx)
        .collect();
    let [bcond_idx] = bconds[..] else {
        return None;
    };
    let bcond = func.inst(insts[bcond_idx]);
    if bcond.operands.len() != 2 {
        return None;
    }
    let cc = imm_of(&bcond.operands[0])?;
    if cc != CC_LO && cc != CC_LT {
        return None;
    }
    let tgt = *branch_targets(bcond).first()?;
    if !body.contains(&tgt) {
        return None;
    }
    // The flags the BCond reads: the LAST compare before it, with nothing that
    // could disturb flags in between (the whitelisted ALU/move ops write no
    // flags; `Trap*` carriers may lower to compare+branch, so they must not
    // sit between the compare and the BCond).
    let cmp_idx = insts[..bcond_idx].iter().rposition(|&id| {
        matches!(
            func.inst(id).opcode,
            AArch64Opcode::CmpRR | AArch64Opcode::CmpRI
        )
    })?;
    if insts[cmp_idx + 1..bcond_idx].iter().any(|&id| {
        matches!(
            func.inst(id).opcode,
            AArch64Opcode::TrapBoundsCheckExact | AArch64Opcode::TrapBoundsCheck
        )
    }) {
        return None;
    }
    let cmp_id = insts[cmp_idx];
    let cmp = func.inst(cmp_id);
    if cmp.operands.len() != 2 {
        return None;
    }
    let lhs = vreg_of(&cmp.operands[0])?;
    let cmp_pos = *pos_of.get(&cmp_id)?;
    if !is_iv_copy_before(
        func,
        single_def,
        pos_of,
        cycle_insts,
        iv,
        lhs,
        cmp_pos,
        redef_pos,
    ) {
        return None;
    }
    let n = match cmp.opcode {
        AArch64Opcode::CmpRI => imm_of(&cmp.operands[1])?,
        AArch64Opcode::CmpRR => {
            let rhs = vreg_of(&cmp.operands[1])?;
            let rhs_def = single_def(rhs)?;
            if cycle_insts.contains(&rhs_def) {
                return None;
            }
            movz_const(func.inst(rhs_def))?
        }
        _ => return None,
    };
    // A non-body successor: the true exit of a pre-tested loop.
    func.block(header)
        .succs
        .iter()
        .find(|s| !body.contains(s))?;
    Some((n, cc))
}

/// `v` holds the CURRENT traversal's `iv` value at `use_pos`: it is `iv`
/// itself (read at `use_pos < redef_pos`), or a single-def in-cycle
/// `MovR/Copy` chain (<= 4 hops) rooted at `iv` whose every hop is positioned
/// before its consumer and strictly before the redefinition.
#[allow(clippy::too_many_arguments)]
fn is_iv_copy_before(
    func: &MachFunction,
    single_def: &impl Fn(VReg) -> Option<InstId>,
    pos_of: &HashMap<InstId, CyclePos>,
    cycle_insts: &HashSet<InstId>,
    iv: VReg,
    v: VReg,
    use_pos: CyclePos,
    redef_pos: CyclePos,
) -> bool {
    if use_pos >= redef_pos {
        return false;
    }
    let mut cur = v;
    let mut cur_use = use_pos;
    for _ in 0..4 {
        if cur == iv {
            return true;
        }
        let Some(def_id) = single_def(cur).filter(|i| cycle_insts.contains(i)) else {
            return false;
        };
        let Some(&def_pos) = pos_of.get(&def_id) else {
            return false;
        };
        if def_pos >= cur_use || def_pos >= redef_pos {
            return false;
        }
        let Some((d, s)) = copy_like(func.inst(def_id)) else {
            return false;
        };
        if d != cur || d.class != RegClass::Gpr64 || s.class != RegClass::Gpr64 {
            return false;
        }
        cur = s;
        cur_use = def_pos;
    }
    cur == iv
}

/// `Madd [dst, index, scale, base]` -> `(index, scale, base)`.
fn madd_parts(inst: &MachInst) -> Option<(VReg, VReg, VReg)> {
    if inst.opcode != AArch64Opcode::Madd || inst.operands.len() != 4 {
        return None;
    }
    Some((
        vreg_of(&inst.operands[1])?,
        vreg_of(&inst.operands[2])?,
        vreg_of(&inst.operands[3])?,
    ))
}

/// `Movz [dst, #imm]` (no shift, or explicit `#0` shift) -> `imm`.
fn movz_const(inst: &MachInst) -> Option<i64> {
    let (_, value) = crate::reaching_const::movz_value(inst)?;
    i64::try_from(value).ok()
}

/// The compile-time constant an `iv` init def assigns: the def is `Movz #c`
/// directly, or a `MovR/Copy` whose source resolves through single-def
/// `MovR/Copy` hops (<= 4) to a `Movz #c`.
fn init_const_value(
    func: &MachFunction,
    single_def: &impl Fn(VReg) -> Option<InstId>,
    init_id: InstId,
) -> Option<i64> {
    let init = func.inst(init_id);
    if let Some(c) = movz_const(init) {
        return Some(c);
    }
    let (_, mut src) = copy_like(init)?;
    for _ in 0..4 {
        let def_id = single_def(src)?;
        let def = func.inst(def_id);
        if let Some(c) = movz_const(def) {
            return Some(c);
        }
        let (d, s) = copy_like(def)?;
        if d != src {
            return None;
        }
        src = s;
    }
    None
}

/// Loop-invariance for `v` (mirrors `strided_store_unroll::is_loop_invariant`):
/// no def anywhere in the cycle, and SOME def dominates the preheader (or no
/// def at all: a pre-colored ABI parameter).
fn is_loop_invariant(
    func: &MachFunction,
    all_defs: &HashMap<VReg, Vec<InstId>>,
    dom: &DomTree,
    cycle_insts: &HashSet<InstId>,
    preheader: BlockId,
    v: VReg,
) -> bool {
    let Some(defs) = all_defs.get(&v) else {
        return true; // never defined: ABI parameter register
    };
    if defs.iter().any(|d| cycle_insts.contains(d)) {
        return false;
    }
    defs.iter()
        .any(|&d| block_of_inst(func, d).is_some_and(|db| dom.dominates(db, preheader)))
}

/// Opcodes permitted in the body. Calls, atomics, unknown stores/loads, and
/// anything unmodeled are absent -> BAIL (closed-world). `Trap*` guard
/// carriers are pure register checks that abort — they cannot write memory, so
/// they do not threaten the forwarding argument, and they are left untouched.
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        MovR | Copy
            | Movz
            | Movk
            | Movn
            | MovI
            | AddRR
            | AddRI
            | SubRR
            | SubRI
            | EorRR
            | EorRRShift
            | EorRRLsl
            | EorRRLsr
            | OrrRR
            | AndRI
            | AndRR
            | LslRI
            | LsrRI
            | AsrRI
            | RorRI
            | Uxtw
            | Madd
            | CmpRR
            | CmpRI
            | CSet
            | BCond
            | B
            | Cbz
            | Cbnz
            | LdrRI
            | StrRI
            | TrapBoundsCheckExact
            | TrapBoundsCheck
    )
}

// ---------------------------------------------------------------------------
// Transformation (delete the in-loop loads, forward the stored register)
// ---------------------------------------------------------------------------

fn apply(func: &mut MachFunction, rec: &Recognized) {
    // Preheader, before the (unconditional-`B header`) terminator:
    //   tP = Madd(iv, scaleReg, base)   — the traversal-0 load address
    //   vS = LdrRI [tP, #0]             — a[i0], loaded once
    let tp = alloc(func, RegClass::Gpr64);
    let madd_id = func.push_inst(MachInst::new(
        AArch64Opcode::Madd,
        vec![vreg(tp), vreg(rec.iv), vreg(rec.scale_reg), vreg(rec.base)],
    ));
    let ldr_id = func.push_inst(MachInst::new(
        AArch64Opcode::LdrRI,
        vec![vreg(rec.vs), vreg(tp), MachOperand::Imm(0)],
    ));
    let insts = &mut func.block_mut(rec.preheader).insts;
    let term_pos = insts.len() - 1;
    insts.insert(term_pos, madd_id);
    insts.insert(term_pos + 1, ldr_id);

    for site in &rec.loads {
        // Unlink the load.
        func.block_mut(site.load_block)
            .insts
            .retain(|&id| id != site.load_id);
        // Unlink its private address Madd when the load was the only reader.
        let madd_dead = !func.block_order.iter().any(|&b| {
            func.block(b)
                .insts
                .iter()
                .any(|&id| reads_vreg(func.inst(id), site.madd_dst))
        });
        if madd_dead {
            func.block_mut(site.madd_block)
                .insts
                .retain(|&id| id != site.madd_id);
        }
    }
    // Rewrite every read of a deleted load's result to the forwarded `vS`
    // (recognition proved every read sits in `(pos(load), pos(def vS)]`).
    let dsts: Vec<VReg> = rec.loads.iter().map(|s| s.dst).collect();
    for block_id in func.block_order.clone() {
        for inst_id in func.block(block_id).insts.clone() {
            let inst = func.inst_mut(inst_id);
            let skip_def = inst.opcode.produces_value();
            for (idx, op) in inst.operands.iter_mut().enumerate() {
                if skip_def && idx == 0 {
                    continue;
                }
                if let MachOperand::VReg(v) = op
                    && dsts.contains(v)
                {
                    *op = MachOperand::VReg(rec.vs);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Small local IR helpers (independent copies, as in the sibling passes)
// ---------------------------------------------------------------------------

fn vreg(v: VReg) -> MachOperand {
    MachOperand::VReg(v)
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

/// `MovR(d, s)` / `Copy(d, s)` -> `(d, s)`.
fn copy_like(inst: &MachInst) -> Option<(VReg, VReg)> {
    match inst.opcode {
        AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => {
            Some((vreg_of(&inst.operands[0])?, vreg_of(&inst.operands[1])?))
        }
        _ => None,
    }
}

/// Does `inst` READ `v` (its def position — operand 0 of a value-producing
/// opcode — is not a read)?
fn reads_vreg(inst: &MachInst, v: VReg) -> bool {
    let skip_def = inst.opcode.produces_value();
    inst.operands
        .iter()
        .enumerate()
        .any(|(idx, op)| !(skip_def && idx == 0) && vreg_of(op) == Some(v))
}

/// Is the instruction linked into some block?
fn is_linked(func: &MachFunction, target: InstId) -> bool {
    func.block_order
        .iter()
        .any(|&b| func.block(b).insts.contains(&target))
}

/// ALL defs of every vreg across block-linked instructions.
fn build_all_defs(func: &MachFunction) -> HashMap<VReg, Vec<InstId>> {
    let mut map: HashMap<VReg, Vec<InstId>> = HashMap::new();
    for &b in &func.block_order {
        for &id in &func.block(b).insts {
            let inst = func.inst(id);
            if inst.opcode.produces_value()
                && let Some(MachOperand::VReg(v)) = inst.operands.first()
            {
                map.entry(*v).or_default().push(id);
            }
        }
    }
    map
}

fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    func.block_order
        .iter()
        .find(|&&b| func.block(b).insts.contains(&target))
        .copied()
}

/// Can `target` be reached from a point just AFTER `from` executes, over the
/// CFG successor edges, WITHOUT ever passing through `barrier`? Forward
/// worklist BFS seeded with `from`'s successors, treating `barrier` as a
/// non-traversable sink. Used fail-closed: with `from = redef_block`,
/// `barrier = init_block`, a `true` result means the redefined `iv` can reach
/// the preheader without re-running the initializer, so `iv == iv0` there is
/// unproven (see the `iv == iv0` argument in `recognize`). When `barrier` is
/// itself `target` (the init lives in the preheader and re-runs on every
/// entry), no path can reach `target` without hitting the barrier, so this is
/// `false` — correctly sound.
fn reaches_avoiding(func: &MachFunction, from: BlockId, target: BlockId, barrier: BlockId) -> bool {
    let mut seen: HashSet<BlockId> = HashSet::new();
    let mut work: Vec<BlockId> = Vec::new();
    let push = |b: BlockId, work: &mut Vec<BlockId>, seen: &mut HashSet<BlockId>| -> bool {
        if b == barrier {
            return false;
        }
        if b == target {
            return true;
        }
        if seen.insert(b) {
            work.push(b);
        }
        false
    };
    for &s in &func.block(from).succs {
        if push(s, &mut work, &mut seen) {
            return true;
        }
    }
    while let Some(b) = work.pop() {
        for &s in &func.block(b).succs {
            if push(s, &mut work, &mut seen) {
                return true;
            }
        }
    }
    false
}

fn branch_targets(inst: &MachInst) -> Vec<BlockId> {
    inst.operands
        .iter()
        .filter_map(|o| match o {
            MachOperand::Block(b) => Some(*b),
            _ => None,
        })
        .collect()
}

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
