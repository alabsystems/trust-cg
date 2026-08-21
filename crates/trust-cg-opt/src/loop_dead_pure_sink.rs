// trust-cg-opt - Loop-dead pure-computation deferral (store sinking)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Defer a loop's pure store-producing computation past the loop when the
//! stored locations are provably never read inside it.
//!
//! # The shape (almabench)
//!
//! ```text
//! for i { for n { for p in 0..8 {          // C = the p-loop, L = the i-loop
//!     planetpv(jd, p, pv);                 // opaque call, writes pv
//!     position[p] = f(pv[0..3]);           // f = sqrt/atan2/asin slice (PURE)
//! }}}
//! ... read position[0..8] ...              // only read AFTER the loops
//! ```
//!
//! `position[p]` is overwritten every (i, n) iteration and only read after the
//! loop nest, so every intermediate `f(...)` evaluation is unobservable: only
//! the values from the FINAL sweep survive. clang -O3 exploits this by sinking
//! the whole pure slice past the loops (asin runs 8x instead of 5,844,000x).
//!
//! # The transform
//!
//! For an inner counted loop `C` (constant 0..B do-while) whose header stores
//! `slot[base + iv*K + off] = f(inputs)` where
//!   * every `f` instruction is PURE (effects model) or an importer-licensed
//!     libm-pure call (`InstFlags::LIBM_PURE_CALL`),
//!   * the slice inputs are in-loop loads from loop-invariant addresses or
//!     loop-invariant vregs,
//!   * the target stack slot's address NEVER escapes and is never accessed
//!     inside the enclosing loop `L` except by these stores,
//!
//! rewrite:
//!   * in `C`'s header, replace `f` + stores with plain stores of the captured
//!     input values into a fresh scratch stack slot (same `iv` indexing);
//!   * on `L`'s single exit edge, emit a deferred 0..B loop that reads the
//!     scratch slot and performs the original `f` + stores.
//!
//! This is DEFERRAL, not speculation: the exit slice consumes exactly the
//! final captured inputs; the intermediate results were unobservable; and the
//! deferred calls are `speculatable willreturn memory(none)` libm math whose
//! only effect is their return value, so executing them fewer times (and
//! later) is unobservable too. The replayed store sequence at the exit is
//! operand-for-operand the sequence the final in-loop sweep performed.
//!
//! # Fail-closed guards (each bails the candidate)
//!
//! * `C` must be the exact two-block rotated do-while ISel emits (header with
//!   `AddRI iv' = iv+1; CmpRI iv',B; CSet EQ; CmpRI,0; BCond NE exit; B latch`
//!   and a `MovR iv, iv'; B header` latch), with constant 0-init and bound.
//! * store addresses must resolve to `AddPCRel SP, slot` + `iv*K` + const.
//! * `L` must have exactly ONE exit edge, dominated by the store block, so the
//!   deferred code runs iff at least one full final sweep completed.
//! * the slot address must not escape: every transitive use of every
//!   `AddPCRel` of the slot is address arithmetic, a load OUTSIDE `L`, or one
//!   of the group stores (the SROA partial-escape provenance argument — a
//!   non-escaping slot cannot be named by any call or unrelated pointer).
//! * every slice instruction must pass the purity/flag checks; NZCV pairs
//!   (Fcmp/Fcsel) stay adjacent with no intervening flag writer or call.
//! * removed defs must have no uses outside the removed set; NZCV must not be
//!   live into the exit target.
//!
//! Kill switch: `TCG_NO_LOOP_DEAD_SINK` (pass stays registered, run is a
//! no-op, bytes identical to a build without the pass).

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand, RegClass,
    StackSlot, StackSlotId, VReg,
};

use crate::dom::DomTree;
use crate::effects::{
    MemoryEffect, aarch64_use_operand_positions, for_each_inst_def, opcode_effect, reads_flags,
    writes_flags,
};
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::MachinePass;

/// Upper bound on the recognized constant trip count (sanity cap; also caps
/// the deferred loop's runtime).
const MAX_TRIP: i64 = 100_000;
/// Upper bound on the scratch capture slot, in bytes.
const MAX_SCRATCH_BYTES: u64 = 16 * 1024;
/// Upper bound on slice size (instructions cloned to the exit).
const MAX_SLICE_INSTS: usize = 200;
/// Upper bound on captured inputs per candidate group.
const MAX_INPUTS: usize = 8;

pub struct LoopDeadPureSink;

impl MachinePass for LoopDeadPureSink {
    fn name(&self) -> &str {
        "loop-dead-pure-sink"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if crate::env_lock::var_os("TCG_NO_LOOP_DEAD_SINK").is_some() {
            return false;
        }
        run_pass(func)
    }
}

fn trace() -> bool {
    std::env::var_os("TCG_LOOP_DEAD_SINK_TRACE").is_some()
}

fn run_pass(func: &mut MachFunction) -> bool {
    // Cheap gate: the transform requires at least one importer-licensed
    // libm-pure call. Skip the whole analysis when none exists (which is the
    // overwhelmingly common case).
    let has_pure_call = func.insts.iter().any(|inst| {
        inst.opcode == AArch64Opcode::Bl && inst.flags.contains(InstFlags::LIBM_PURE_CALL)
    });
    if !has_pure_call {
        return false;
    }

    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    if loops.is_empty() {
        return false;
    }

    // Deterministic candidate order: loops by header id (BTreeMap order).
    let all: Vec<NaturalLoop> = loops.all_loops().cloned().collect();
    for c in &all {
        if let Some(plan) = plan_for_inner_loop(func, &dom, &loops, c) {
            if trace() {
                eprintln!(
                    "[loop-dead-pure-sink] {}: firing on inner loop {:?} (outer {:?}), \
                     {} stores, {} inputs, {} slice insts, trip {}",
                    func.name,
                    plan.c_header,
                    plan.l_header,
                    plan.stores.len(),
                    plan.inputs.len(),
                    plan.slice.len(),
                    plan.bound
                );
            }
            apply_plan(func, &plan);
            // One firing per run: the rewrite invalidates the analyses. The
            // almabench-class shape has a single qualifying nest.
            return true;
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// One admitted store: `StrRI [value(Fpr64), addr, imm]` with
/// `addr+imm == slot_base + iv*K + total_off`.
#[derive(Debug, Clone)]
struct StoreInfo {
    inst_id: InstId,
    value: VReg,
    /// Total constant byte offset from `slot_base + iv*K`.
    total_off: i64,
}

#[derive(Debug)]
struct Plan {
    /// Inner counted loop C: header block (contains the stores + IV logic).
    c_header: BlockId,
    /// Outer loop L that the computation is deferred past.
    l_header: BlockId,
    /// L's single exit edge.
    exit_src: BlockId,
    exit_tgt: BlockId,
    /// C's IV state.
    iv: VReg,
    bound: i64,
    /// Store group (all to `slot` with the same stride K and base vreg).
    stores: Vec<StoreInfo>,
    stride_k: i64,
    /// The `AddPCRel SP, slot` vreg the store chains resolve to.
    target_base: VReg,
    /// Captured input loads, in header order: (vreg, load inst id).
    inputs: Vec<(VReg, InstId)>,
    /// Slice instruction ids in header order (excludes the input loads;
    /// includes the group stores).
    slice: Vec<InstId>,
    /// Position just after the last input load (capture insertion point).
    capture_pos: usize,
}

/// Map from vreg to (def inst ids, def blocks). Multi-def vregs keep all defs.
struct DefMap {
    defs: HashMap<VReg, Vec<(InstId, BlockId)>>,
}

impl DefMap {
    fn build(func: &MachFunction) -> Self {
        let mut defs: HashMap<VReg, Vec<(InstId, BlockId)>> = HashMap::new();
        for &block_id in &func.block_order {
            for &inst_id in &func.block(block_id).insts {
                let inst = func.inst(inst_id);
                for (pos, op) in inst.operands.iter().enumerate() {
                    if let MachOperand::VReg(v) = op
                        && operand_is_def(inst, pos)
                    {
                        defs.entry(*v).or_default().push((inst_id, block_id));
                    }
                }
            }
        }
        Self { defs }
    }

    fn defs_of(&self, v: VReg) -> &[(InstId, BlockId)] {
        self.defs.get(&v).map(Vec::as_slice).unwrap_or(&[])
    }

    /// The unique def of `v`, or None if 0 or >1 defs.
    fn single_def(&self, v: VReg) -> Option<(InstId, BlockId)> {
        match self.defs_of(v) {
            [one] => Some(*one),
            _ => None,
        }
    }
}

/// Does operand `pos` of `inst` WRITE the register (Def or DefUse)?
fn operand_is_def(inst: &MachInst, pos: usize) -> bool {
    let roles = crate::effects::aarch64_operand_roles(inst.opcode, inst.operands.len());
    roles.get(pos).is_some_and(|r| {
        matches!(
            r,
            crate::effects::OperandRole::Def | crate::effects::OperandRole::DefUse
        )
    })
}

/// Try to build a full deferral plan with `c` as the inner store loop.
fn plan_for_inner_loop(
    func: &MachFunction,
    dom: &DomTree,
    loops: &LoopAnalysis,
    c: &NaturalLoop,
) -> Option<Plan> {
    // C must be nested (there must be an outer loop to defer past).
    c.parent?;

    // --- C shape: exact two-block rotated do-while --------------------------
    if c.body.len() != 2 || c.header == c.latch || !c.body.contains(&c.latch) {
        return None;
    }
    let header = func.block(c.header);
    let latch = func.block(c.latch);
    // Latch: exactly `MovR iv, iv_next; B header`.
    if latch.insts.len() != 2 {
        return None;
    }
    let latch_mov = func.inst(latch.insts[0]);
    let latch_b = func.inst(latch.insts[1]);
    if latch_mov.opcode != AArch64Opcode::MovR || latch_b.opcode != AArch64Opcode::B {
        return None;
    }
    if latch_b.operands.first() != Some(&MachOperand::Block(c.header)) {
        return None;
    }
    let (iv, iv_next) = match (latch_mov.operands.first(), latch_mov.operands.get(1)) {
        (Some(MachOperand::VReg(d)), Some(MachOperand::VReg(s))) => (*d, *s),
        _ => return None,
    };
    if iv.class != RegClass::Gpr64 || iv_next.class != RegClass::Gpr64 {
        return None;
    }
    // Latch must have no other successors and exactly the header successor.
    if latch.succs.as_slice() != [c.header] {
        return None;
    }

    // Header terminators: `... BCond(NE, exit); B(latch)` with the preceding
    // `CmpRI iv_next, bound; CSet EQ; CmpRI t, 0` triple.
    let n = header.insts.len();
    if n < 7 {
        return None;
    }
    let b_inst = func.inst(header.insts[n - 1]);
    let bcond_inst = func.inst(header.insts[n - 2]);
    if b_inst.opcode != AArch64Opcode::B || bcond_inst.opcode != AArch64Opcode::BCond {
        return None;
    }
    if b_inst.operands.first() != Some(&MachOperand::Block(c.latch)) {
        return None;
    }
    let c_exit_tgt = match (bcond_inst.operands.first(), bcond_inst.operands.get(1)) {
        (Some(MachOperand::Imm(1)), Some(MachOperand::Block(t))) if !c.body.contains(t) => *t,
        _ => return None,
    };
    let _ = c_exit_tgt;
    // CmpRI t, 0
    let cmp_t = func.inst(header.insts[n - 3]);
    let (t_vreg,) = match (cmp_t.opcode, cmp_t.operands.first(), cmp_t.operands.get(1)) {
        (AArch64Opcode::CmpRI, Some(MachOperand::VReg(t)), Some(MachOperand::Imm(0))) => (*t,),
        _ => return None,
    };
    // CSet t, EQ(0)
    let cset = func.inst(header.insts[n - 4]);
    match (cset.opcode, cset.operands.first(), cset.operands.get(1)) {
        (AArch64Opcode::CSet, Some(MachOperand::VReg(t)), Some(MachOperand::Imm(0)))
            if *t == t_vreg => {}
        _ => return None,
    }
    // CmpRI iv_next, bound
    let cmp_bound = func.inst(header.insts[n - 5]);
    let bound = match (
        cmp_bound.opcode,
        cmp_bound.operands.first(),
        cmp_bound.operands.get(1),
    ) {
        (AArch64Opcode::CmpRI, Some(MachOperand::VReg(v)), Some(MachOperand::Imm(b)))
            if *v == iv_next =>
        {
            *b
        }
        _ => return None,
    };
    if !(1..=MAX_TRIP).contains(&bound) {
        return None;
    }

    let defs = DefMap::build(func);

    // iv_next: unique def `AddRI iv_next, iv, 1` inside the header.
    let (ivn_def_id, ivn_def_block) = defs.single_def(iv_next)?;
    if ivn_def_block != c.header {
        return None;
    }
    let ivn_def = func.inst(ivn_def_id);
    match (
        ivn_def.opcode,
        ivn_def.operands.first(),
        ivn_def.operands.get(1),
        ivn_def.operands.get(2),
    ) {
        (
            AArch64Opcode::AddRI,
            Some(MachOperand::VReg(d)),
            Some(MachOperand::VReg(s)),
            Some(MachOperand::Imm(1)),
        ) if *d == iv_next && *s == iv => {}
        _ => return None,
    }

    // iv: exactly two defs — the latch MovR and one 0-init outside C.
    let iv_defs = defs.defs_of(iv);
    if iv_defs.len() != 2 {
        return None;
    }
    let init_def = iv_defs
        .iter()
        .find(|(id, _)| *id != latch.insts[0])
        .copied()?;
    if c.body.contains(&init_def.1) {
        return None;
    }
    if !iv_init_is_zero(func, &defs, init_def.0) {
        return None;
    }

    // --- Candidate stores in the header -------------------------------------
    let mut candidates: Vec<(StoreInfo, StackSlotId, i64, VReg)> = Vec::new();
    for &inst_id in header.insts.iter() {
        let inst = func.inst(inst_id);
        if inst.opcode != AArch64Opcode::StrRI {
            continue;
        }
        let (value, addr, imm) = match (
            inst.operands.first(),
            inst.operands.get(1),
            inst.operands.get(2),
        ) {
            (Some(MachOperand::VReg(v)), Some(MachOperand::VReg(a)), Some(MachOperand::Imm(i))) => {
                (*v, *a, *i)
            }
            _ => continue,
        };
        if value.class != RegClass::Fpr64 {
            continue;
        }
        let Some((slot, k, base_vreg, total_off)) =
            resolve_iv_scaled_slot_addr(func, &defs, c, iv, addr, imm)
        else {
            continue;
        };
        // STR imm-offset legality for the deferred re-expression.
        if !(0..=4096).contains(&total_off) || total_off % 8 != 0 {
            continue;
        }
        candidates.push((
            StoreInfo {
                inst_id,
                value,
                total_off,
            },
            slot,
            k,
            base_vreg,
        ));
    }
    if candidates.is_empty() {
        return None;
    }
    // All candidates must agree on (slot, K, base vreg): mixed groups bail.
    let (slot, stride_k, target_base) = (candidates[0].1, candidates[0].2, candidates[0].3);
    if candidates
        .iter()
        .any(|(_, s, k, b)| *s != slot || *k != stride_k || *b != target_base)
    {
        return None;
    }
    let stores: Vec<StoreInfo> = candidates.into_iter().map(|(s, ..)| s).collect();

    // Bounds sanity: the recognized footprint stays inside the declared slot
    // (an out-of-bounds original would be UB — never transform it).
    let slot_size = func.stack_slots.get(slot.0 as usize)?.size;
    let max_off = stores.iter().map(|s| s.total_off).max().unwrap_or(0);
    if (bound - 1)
        .checked_mul(stride_k)
        .and_then(|x| x.checked_add(max_off + 8))
        .is_none_or(|end| end as u64 > u64::from(slot_size))
    {
        return None;
    }

    // --- Choose the outermost qualifying L ----------------------------------
    let mut l_candidate: Option<(NaturalLoop, (BlockId, BlockId))> = None;
    let mut cursor = c.parent;
    while let Some(l_header) = cursor {
        let l = loops.get_loop(l_header)?.clone();
        match qualifies_as_outer(func, dom, c, &l, slot, &stores, target_base) {
            Some(exit_edge) => {
                l_candidate = Some((l.clone(), exit_edge));
                cursor = l.parent;
            }
            None => break,
        }
    }
    let (l, (exit_src, exit_tgt)) = l_candidate?;

    // The slot base and the IV init must be defined OUTSIDE the chosen L and
    // dominate C's header (so they are valid in the header AND at L's exit).
    let (_, base_def_block) = defs.single_def(target_base)?;
    if l.body.contains(&base_def_block) || !dom.dominates(base_def_block, c.header) {
        return None;
    }
    if !dom.dominates(init_def.1, c.header) {
        return None;
    }

    // --- Slice computation ---------------------------------------------------
    let slice = compute_slice(
        func,
        dom,
        &defs,
        c,
        &l,
        &stores,
        InductionVRegs {
            current: iv,
            next: iv_next,
        },
    )?;

    // Scratch capacity: bound * 8 * n_inputs bytes, hard-capped.
    let scratch_bytes = (bound as u64).checked_mul(8 * slice.inputs.len() as u64)?;
    if scratch_bytes == 0 || scratch_bytes > MAX_SCRATCH_BYTES {
        return None;
    }

    Some(Plan {
        c_header: c.header,
        l_header: l.header,
        exit_src,
        exit_tgt,
        iv,
        bound,
        stores,
        stride_k,
        target_base,
        inputs: slice.inputs,
        slice: slice.insts,
        capture_pos: slice.capture_pos,
    })
}

/// Chase `iv`'s init def to a constant zero: `Movz iv, 0` directly or
/// `MovR iv, z` where `z`'s unique def is `Movz z, 0`.
fn iv_init_is_zero(func: &MachFunction, defs: &DefMap, init_id: InstId) -> bool {
    let inst = func.inst(init_id);
    match inst.opcode {
        AArch64Opcode::Movz => inst.operands.get(1) == Some(&MachOperand::Imm(0)),
        AArch64Opcode::MovR => {
            let Some(MachOperand::VReg(src)) = inst.operands.get(1) else {
                return false;
            };
            let Some((src_def, _)) = defs.single_def(*src) else {
                return false;
            };
            let src_inst = func.inst(src_def);
            src_inst.opcode == AArch64Opcode::Movz
                && src_inst.operands.get(1) == Some(&MachOperand::Imm(0))
        }
        _ => false,
    }
}

/// Resolve a store address `addr + imm` to `slot_base + iv*K + total_off`.
///
/// Accepted chain (walking up single-def vregs):
///   `AddRI x, y, c`                (accumulate c)
///   `Madd x, iv, k_vreg, base`     (k_vreg: unique `Movz k, K`; exactly once)
///   `AddPCRel base, SP, slot`      (terminates; the slot base)
fn resolve_iv_scaled_slot_addr(
    func: &MachFunction,
    defs: &DefMap,
    c: &NaturalLoop,
    iv: VReg,
    addr: VReg,
    imm: i64,
) -> Option<(StackSlotId, i64, VReg, i64)> {
    let mut off = imm;
    let mut cur = addr;
    let mut k: Option<i64> = None;
    let mut base: Option<(StackSlotId, VReg)> = None;
    for _ in 0..8 {
        let (def_id, def_block) = defs.single_def(cur)?;
        let inst = func.inst(def_id);
        match inst.opcode {
            AArch64Opcode::AddRI => {
                // Constant-offset nodes must live in the store's own header:
                // the only shape ISel emits for these chains, and it rules out
                // any stale cross-block address vreg by construction.
                if def_block != c.header {
                    return None;
                }
                let (MachOperand::VReg(_d), MachOperand::VReg(s), MachOperand::Imm(c_imm)) = (
                    inst.operands.first()?,
                    inst.operands.get(1)?,
                    inst.operands.get(2)?,
                ) else {
                    return None;
                };
                off = off.checked_add(*c_imm)?;
                cur = *s;
            }
            AArch64Opcode::Madd => {
                // Madd d, a, b, addend  ==  d = a*b + addend
                if k.is_some() || def_block != c.header {
                    return None;
                }
                let (
                    MachOperand::VReg(_d),
                    MachOperand::VReg(a),
                    MachOperand::VReg(b),
                    MachOperand::VReg(addend),
                ) = (
                    inst.operands.first()?,
                    inst.operands.get(1)?,
                    inst.operands.get(2)?,
                    inst.operands.get(3)?,
                )
                else {
                    return None;
                };
                if *a != iv {
                    return None;
                }
                let (k_def, _) = defs.single_def(*b)?;
                let k_inst = func.inst(k_def);
                if k_inst.opcode != AArch64Opcode::Movz {
                    return None;
                }
                let MachOperand::Imm(k_imm) = k_inst.operands.get(1)? else {
                    return None;
                };
                // Movz with a shift operand would encode k_imm << shift; only
                // the plain 2-operand form is accepted.
                if k_inst.operands.len() != 2 || !(1..=4096).contains(k_imm) {
                    return None;
                }
                k = Some(*k_imm);
                cur = *addend;
            }
            AArch64Opcode::AddPCRel => {
                let (MachOperand::VReg(d), MachOperand::PReg(sp), MachOperand::StackSlot(sid)) = (
                    inst.operands.first()?,
                    inst.operands.get(1)?,
                    inst.operands.get(2)?,
                ) else {
                    return None;
                };
                if sp.encoding() != 31 {
                    return None;
                }
                base = Some((*sid, *d));
                break;
            }
            _ => return None,
        }
    }
    let (slot, base_vreg) = base?;
    Some((slot, k?, base_vreg, off))
}

/// Verify `l` (an ancestor loop of `c`) admits the deferral, returning its
/// single exit edge.
fn qualifies_as_outer(
    func: &MachFunction,
    dom: &DomTree,
    c: &NaturalLoop,
    l: &NaturalLoop,
    slot: StackSlotId,
    stores: &[StoreInfo],
    target_base: VReg,
) -> Option<(BlockId, BlockId)> {
    if !c.body.is_subset(&l.body) || l.header == c.header {
        return None;
    }
    // Store block dominates L's latch: the stores execute on every complete
    // L-iteration.
    if !dom.dominates(c.header, l.latch) {
        return None;
    }
    // Exactly one exit edge, whose source the store block dominates: the
    // deferred code runs only after at least one full final sweep.
    let mut exits: Vec<(BlockId, BlockId)> = Vec::new();
    let mut body_sorted: Vec<BlockId> = l.body.iter().copied().collect();
    body_sorted.sort_by_key(|b| b.0);
    for &b in &body_sorted {
        for &s in &func.block(b).succs {
            if !l.body.contains(&s) {
                exits.push((b, s));
            }
        }
    }
    if exits.len() != 1 {
        return None;
    }
    let (exit_src, exit_tgt) = exits[0];
    if !dom.dominates(c.header, exit_src) {
        return None;
    }
    // The exit source must reach the target through exactly one terminator
    // operand (no degenerate double edge).
    let src_block = func.block(exit_src);
    if src_block.succs.iter().filter(|s| **s == exit_tgt).count() != 1 {
        return None;
    }
    // NZCV must not be live into the exit target: the deferred loop sets
    // flags. Fail closed if the target reads flags before writing them.
    let tgt_block = func.block(exit_tgt);
    for &inst_id in &tgt_block.insts {
        let inst = func.inst(inst_id);
        if reads_flags(inst.opcode) {
            return None;
        }
        if writes_flags(inst.opcode) || inst.is_call() {
            break;
        }
    }
    // Slot non-escape + no in-L reads (whole-function provenance walk).
    if !slot_accesses_admissible(func, l, slot, stores, target_base) {
        return None;
    }
    Some((exit_src, exit_tgt))
}

/// Whole-function provenance walk for the target slot.
///
/// Collects every vreg derived from ANY `AddPCRel SP, slot` and verifies each
/// use is one of:
///   * pure address arithmetic (derivation continues),
///   * a load with the derived vreg as BASE, OUTSIDE `l` (the legitimate
///     after/before-loop consumers),
///   * one of the group stores (base position),
///   * a store with derived BASE outside `l` (overwritten state; final memory
///     unchanged by the deferral).
///
/// Anything else — a call argument, a stored VALUE (address escape), a load
/// inside `l`, an unrecognized opcode — fails the walk. Because the slot can
/// then never be named by any pointer the program constructs elsewhere, the
/// opaque calls inside `l` provably cannot read or write it.
fn slot_accesses_admissible(
    func: &MachFunction,
    l: &NaturalLoop,
    slot: StackSlotId,
    stores: &[StoreInfo],
    target_base: VReg,
) -> bool {
    let store_ids: HashSet<InstId> = stores.iter().map(|s| s.inst_id).collect();

    // Roots: every AddPCRel of this slot anywhere in the function.
    let mut derived: HashSet<VReg> = HashSet::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::AddPCRel
                && inst.operands.get(2) == Some(&MachOperand::StackSlot(slot))
            {
                let Some(MachOperand::VReg(d)) = inst.operands.first() else {
                    return false;
                };
                derived.insert(*d);
            }
        }
    }
    if !derived.contains(&target_base) {
        return false;
    }

    // Transitive closure with a fixpoint over use sites.
    loop {
        let mut grew = false;
        for &block_id in &func.block_order {
            let in_l = l.body.contains(&block_id);
            for &inst_id in &func.block(block_id).insts {
                let inst = func.inst(inst_id);
                let use_positions = aarch64_use_operand_positions(inst.opcode, inst.operands.len());
                let uses_derived = use_positions.iter().any(|&p| {
                    matches!(inst.operands.get(p), Some(MachOperand::VReg(v)) if derived.contains(v))
                });
                if !uses_derived {
                    continue;
                }
                match opcode_effect(inst.opcode) {
                    MemoryEffect::Pure => {
                        // Address arithmetic: the def joins the derived set.
                        // (Flag-setting compares on addresses would be exotic;
                        // they produce no pointer, so they are safe to ignore
                        // as derivations but we still require a plain def.)
                        for_each_inst_def(inst, |d| {
                            if !derived.contains(&d) {
                                derived.insert(d);
                                grew = true;
                            }
                        });
                    }
                    MemoryEffect::Load => {
                        // Only the exact scalar `LdrRI [dst, base(derived),
                        // imm]` shape is admitted, and only OUTSIDE `l` (the
                        // legitimate after/before-loop consumers). Any other
                        // load opcode touching a derived vreg (pair loads,
                        // register-offset forms whose INDEX could launder the
                        // address into another object) fails closed.
                        if in_l || inst.opcode != AArch64Opcode::LdrRI {
                            return false;
                        }
                        let base_is_derived = matches!(
                            inst.operands.get(1),
                            Some(MachOperand::VReg(b)) if derived.contains(b)
                        );
                        if !base_is_derived {
                            // Derived vreg in a non-base position of a load.
                            return false;
                        }
                        if let Some(MachOperand::VReg(d)) = inst.operands.first()
                            && d.class == RegClass::Gpr64
                            && !derived.contains(d)
                        {
                            // Fail-closed over-approximation for pointer-sized
                            // loads: treat the loaded value as derived too.
                            derived.insert(*d);
                            grew = true;
                        }
                    }
                    MemoryEffect::Store => {
                        // Only the exact `StrRI [value, base(derived), imm]`
                        // shape is admitted: the derived vreg must be the BASE,
                        // never the stored VALUE (address escape), and in-l
                        // stores must be exactly the group stores. Any other
                        // store opcode touching a derived vreg fails closed.
                        if inst.opcode != AArch64Opcode::StrRI {
                            return false;
                        }
                        let value_is_derived = matches!(
                            inst.operands.first(),
                            Some(MachOperand::VReg(v)) if derived.contains(v)
                        );
                        if value_is_derived {
                            return false;
                        }
                        if in_l && !store_ids.contains(&inst_id) {
                            return false;
                        }
                    }
                    MemoryEffect::Call => return false,
                }
            }
        }
        if !grew {
            break;
        }
    }
    true
}

struct SliceResult {
    /// Slice inst ids in header order (includes the group stores).
    insts: Vec<InstId>,
    /// Captured inputs in header order: (vreg, load inst id).
    inputs: Vec<(VReg, InstId)>,
    capture_pos: usize,
}

#[derive(Clone, Copy)]
struct InductionVRegs {
    current: VReg,
    next: VReg,
}

/// Compute the combined backward slice of the group stores within the header.
fn compute_slice(
    func: &MachFunction,
    dom: &DomTree,
    defs: &DefMap,
    c: &NaturalLoop,
    l: &NaturalLoop,
    stores: &[StoreInfo],
    induction: InductionVRegs,
) -> Option<SliceResult> {
    let InductionVRegs {
        current: iv,
        next: iv_next,
    } = induction;
    let header = func.block(c.header);
    let pos_of: HashMap<InstId, usize> = header
        .insts
        .iter()
        .enumerate()
        .map(|(i, id)| (*id, i))
        .collect();

    let mut slice: HashSet<InstId> = HashSet::new();
    let mut inputs: Vec<(VReg, InstId)> = Vec::new();
    let mut input_set: HashSet<VReg> = HashSet::new();
    let mut invariants: HashSet<VReg> = HashSet::new();
    let mut worklist: Vec<VReg> = Vec::new();

    for s in stores {
        slice.insert(s.inst_id);
        worklist.push(s.value);
    }

    let mut visited: HashSet<VReg> = HashSet::new();
    while let Some(v) = worklist.pop() {
        if !visited.insert(v) {
            continue;
        }
        if v == iv || v == iv_next {
            // The stored values must not depend on the IV (v1 narrowness).
            return None;
        }
        if input_set.contains(&v) || invariants.contains(&v) {
            continue;
        }
        let v_defs = defs.defs_of(v);
        match v_defs {
            [] => return None,
            [(def_id, def_block)] => {
                let def_id = *def_id;
                let def_block = *def_block;
                if def_block == c.header {
                    if !admit_header_def(
                        func,
                        header,
                        &pos_of,
                        defs,
                        def_id,
                        v,
                        &mut slice,
                        &mut inputs,
                        &mut input_set,
                        &mut worklist,
                        l,
                        dom,
                        c,
                    ) {
                        return None;
                    }
                } else if !l.body.contains(&def_block) && dom.dominates(def_block, c.header) {
                    // Loop-invariant: usable directly at the exit (its def
                    // dominates every block of `l`, hence the new blocks).
                    invariants.insert(v);
                } else {
                    // Defined inside `l` but outside the header (not
                    // iteration-repeating in general) — bail.
                    return None;
                }
            }
            _multi => {
                // Multi-def vreg: admit ONLY the Movz+Movk immediate-chain
                // idiom, entirely inside the header.
                if !admit_movk_chain(func, &pos_of, v_defs, &mut slice) {
                    return None;
                }
            }
        }
    }

    if inputs.is_empty() || inputs.len() > MAX_INPUTS {
        return None;
    }
    if slice.len() > MAX_SLICE_INSTS {
        return None;
    }
    // The deferral must actually remove at least one libm call from the loop:
    // that is the entire prize, and requiring it also makes the pass
    // idempotent — the capture stores it emits (an identity slice with no
    // call) can never re-qualify on a later run of an iterating schedule.
    if !slice
        .iter()
        .any(|id| func.inst(*id).opcode == AArch64Opcode::Bl)
    {
        return None;
    }

    // Materialize the ordered slice.
    let mut ordered: Vec<(usize, InstId)> = slice
        .iter()
        .map(|id| (*pos_of.get(id).expect("slice inst in header"), *id))
        .collect();
    ordered.sort_unstable();
    let insts: Vec<InstId> = ordered.iter().map(|(_, id)| *id).collect();

    // Order inputs by load position (deterministic capture layout).
    inputs.sort_by_key(|(_, id)| pos_of[id]);
    let capture_pos = inputs.iter().map(|(_, id)| pos_of[id]).max()? + 1;

    // Flag-pair discipline: every flag-READING slice inst must have its
    // nearest preceding flag WRITER in the slice, with no other flag writer or
    // call strictly between them; and every flag-WRITING slice inst must not
    // feed a non-slice reader.
    if !flag_discipline_ok(func, header, &slice) {
        return None;
    }

    // External-use check: every def of a slice inst must have all its uses
    // inside the slice. (Slice = the removed set; the input loads stay.)
    if !removed_defs_have_no_external_uses(func, &slice) {
        return None;
    }

    Some(SliceResult {
        insts,
        inputs,
        capture_pos,
    })
}

/// Admit one header-defined vreg def into the slice. Returns false to bail.
#[allow(clippy::too_many_arguments)]
fn admit_header_def(
    func: &MachFunction,
    header: &trust_cg_ir::MachBlock,
    pos_of: &HashMap<InstId, usize>,
    defs: &DefMap,
    def_id: InstId,
    _v: VReg,
    slice: &mut HashSet<InstId>,
    inputs: &mut Vec<(VReg, InstId)>,
    input_set: &mut HashSet<VReg>,
    worklist: &mut Vec<VReg>,
    l: &NaturalLoop,
    dom: &DomTree,
    c: &NaturalLoop,
) -> bool {
    let inst = func.inst(def_id);
    let op = inst.opcode;

    // Call result read: `Copy [VReg, PReg(d0)]` immediately after a
    // libm-pure `Bl` with its contiguous arg-setup copies before it.
    if op == AArch64Opcode::Copy
        && let (Some(MachOperand::VReg(dst)), Some(MachOperand::PReg(src))) =
            (inst.operands.first(), inst.operands.get(1))
    {
        if dst.class != RegClass::Fpr64 {
            return false;
        }
        let Some(&copy_pos) = pos_of.get(&def_id) else {
            return false;
        };
        // d0 is the scalar FP return register.
        if src.encoding() != 96 {
            return false;
        }
        return admit_pure_call_cluster(func, header, copy_pos, slice, worklist);
    }

    // Input load: LdrRI from an invariant base.
    if op == AArch64Opcode::LdrRI {
        let (
            Some(MachOperand::VReg(dst)),
            Some(MachOperand::VReg(base)),
            Some(MachOperand::Imm(_)),
        ) = (
            inst.operands.first(),
            inst.operands.get(1),
            inst.operands.get(2),
        )
        else {
            return false;
        };
        if dst.class != RegClass::Fpr64 {
            return false;
        }
        let Some((_, base_block)) = defs.single_def(*base) else {
            return false;
        };
        if l.body.contains(&base_block) || !dom.dominates(base_block, c.header) {
            return false;
        }
        if input_set.insert(*dst) {
            inputs.push((*dst, def_id));
        }
        return true;
    }

    // Plain pure computation (no memory, no calls, no branches).
    let effect = opcode_effect(op);
    if effect != MemoryEffect::Pure || inst.is_call() || inst.is_branch() || inst.is_terminator() {
        return false;
    }
    // Flag writers are admitted only via the reader (paired below); admitting
    // one directly is fine too — discipline is checked globally afterwards.
    slice.insert(def_id);
    if reads_flags(op) {
        // Pull the nearest preceding flag writer into the slice.
        let Some(&pos) = pos_of.get(&def_id) else {
            return false;
        };
        let mut writer: Option<InstId> = None;
        for &cand in header.insts[..pos].iter().rev() {
            let cand_inst = func.inst(cand);
            if writes_flags(cand_inst.opcode) {
                writer = Some(cand);
                break;
            }
            if cand_inst.is_call() {
                return false;
            }
        }
        let Some(writer_id) = writer else {
            return false;
        };
        let writer_inst = func.inst(writer_id);
        // Only the pure compare family; its operands feed the slice.
        if !matches!(
            writer_inst.opcode,
            AArch64Opcode::Fcmp | AArch64Opcode::CmpRR | AArch64Opcode::CmpRI
        ) {
            return false;
        }
        slice.insert(writer_id);
        for p in aarch64_use_operand_positions(writer_inst.opcode, writer_inst.operands.len()) {
            if let Some(MachOperand::VReg(u)) = writer_inst.operands.get(p) {
                worklist.push(*u);
            }
        }
    }
    // Recurse into vreg uses. Movk-style DefUse op0 recurses into the SAME
    // vreg, which the multi-def path resolves.
    for p in aarch64_use_operand_positions(op, inst.operands.len()) {
        if let Some(MachOperand::VReg(u)) = inst.operands.get(p) {
            worklist.push(*u);
        }
    }
    true
}

/// Admit the `Copy [PReg dN, VReg]* ; Bl(pure) ; Copy [VReg, d0]` cluster whose
/// result-read copy sits at `copy_pos`. Arg source vregs join the worklist.
fn admit_pure_call_cluster(
    func: &MachFunction,
    header: &trust_cg_ir::MachBlock,
    copy_pos: usize,
    slice: &mut HashSet<InstId>,
    worklist: &mut Vec<VReg>,
) -> bool {
    if copy_pos == 0 {
        return false;
    }
    let bl_pos = copy_pos - 1;
    let bl_id = header.insts[bl_pos];
    let bl = func.inst(bl_id);
    if bl.opcode != AArch64Opcode::Bl || !bl.flags.contains(InstFlags::LIBM_PURE_CALL) {
        return false;
    }
    // The next inst after the result read must not be another result read of
    // the same call (a two-result call would be silently truncated).
    if let Some(&next_id) = header.insts.get(copy_pos + 1) {
        let next = func.inst(next_id);
        if next.opcode == AArch64Opcode::Copy
            && matches!(
                (next.operands.first(), next.operands.get(1)),
                (Some(MachOperand::VReg(_)), Some(MachOperand::PReg(_)))
            )
        {
            return false;
        }
    }
    // Contiguous FP arg setups immediately before the Bl: Copy [PReg, VReg].
    let mut arg_positions: Vec<usize> = Vec::new();
    let mut i = bl_pos;
    while i > 0 {
        let cand_id = header.insts[i - 1];
        let cand = func.inst(cand_id);
        if cand.opcode == AArch64Opcode::Copy
            && let (Some(MachOperand::PReg(_)), Some(MachOperand::VReg(_))) =
                (cand.operands.first(), cand.operands.get(1))
        {
            arg_positions.push(i - 1);
            i -= 1;
            continue;
        }
        break;
    }
    if arg_positions.is_empty() || arg_positions.len() > 8 {
        return false;
    }
    slice.insert(bl_id);
    slice.insert(header.insts[copy_pos]);
    for &p in &arg_positions {
        let id = header.insts[p];
        slice.insert(id);
        if let Some(MachOperand::VReg(src)) = func.inst(id).operands.get(1) {
            worklist.push(*src);
        }
    }
    true
}

/// Admit a multi-def vreg only for the Movz+Movk immediate chain, all defs in
/// the header. All defs join the slice.
fn admit_movk_chain(
    func: &MachFunction,
    pos_of: &HashMap<InstId, usize>,
    v_defs: &[(InstId, BlockId)],
    slice: &mut HashSet<InstId>,
) -> bool {
    let mut sorted: Vec<(usize, InstId)> = Vec::new();
    for (id, _block) in v_defs {
        let Some(&pos) = pos_of.get(id) else {
            // A def outside the header — not the local immediate idiom.
            return false;
        };
        sorted.push((pos, *id));
    }
    sorted.sort_unstable();
    let first = func.inst(sorted[0].1);
    if first.opcode != AArch64Opcode::Movz {
        return false;
    }
    for &(_, id) in &sorted[1..] {
        if func.inst(id).opcode != AArch64Opcode::Movk {
            return false;
        }
    }
    for &(_, id) in &sorted {
        slice.insert(id);
    }
    true
}

/// Every flag-reading slice member must pair with an in-slice nearest
/// preceding writer (no other writer or call strictly between), and no
/// non-slice reader may consume a removed writer's flags.
fn flag_discipline_ok(
    func: &MachFunction,
    header: &trust_cg_ir::MachBlock,
    slice: &HashSet<InstId>,
) -> bool {
    let ids = &header.insts;
    for (pos, &id) in ids.iter().enumerate() {
        let inst = func.inst(id);
        if reads_flags(inst.opcode) {
            // Find nearest preceding writer.
            let mut writer: Option<(usize, InstId)> = None;
            for p in (0..pos).rev() {
                let cand = func.inst(ids[p]);
                if writes_flags(cand.opcode) {
                    writer = Some((p, ids[p]));
                    break;
                }
                if cand.is_call() && !slice.contains(&ids[p]) {
                    // A remaining call between reader and writer clobbers
                    // NZCV for the REMAINING sequence too; it was already
                    // broken/irrelevant — keep scanning (calls do not define
                    // flags in the model). Removed calls vanish, which only
                    // shortens the distance.
                }
            }
            match writer {
                None => {
                    // Reader with no in-block writer: flags flow across the
                    // block boundary — never touch such a block.
                    return false;
                }
                Some((wpos, wid)) => {
                    let reader_in = slice.contains(&id);
                    let writer_in = slice.contains(&wid);
                    if reader_in != writer_in {
                        return false;
                    }
                    if reader_in {
                        // No intervening call (removed or kept) or writer
                        // between the pair in the ORIGINAL order; the clone
                        // preserves subsequence order, so this stays valid.
                        for &mid_id in ids.iter().take(pos).skip(wpos + 1) {
                            let mid = func.inst(mid_id);
                            if mid.is_call() || writes_flags(mid.opcode) {
                                return false;
                            }
                        }
                    }
                }
            }
        }
    }
    true
}

/// True when every def produced by a slice (removed) instruction is used only
/// by other slice instructions.
fn removed_defs_have_no_external_uses(func: &MachFunction, slice: &HashSet<InstId>) -> bool {
    let mut removed_defs: HashSet<VReg> = HashSet::new();
    for &id in slice {
        let inst = func.inst(id);
        for (pos, op) in inst.operands.iter().enumerate() {
            if let MachOperand::VReg(v) = op
                && operand_is_def(inst, pos)
            {
                removed_defs.insert(*v);
            }
        }
    }
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            if slice.contains(&inst_id) {
                continue;
            }
            let inst = func.inst(inst_id);
            for p in aarch64_use_operand_positions(inst.opcode, inst.operands.len()) {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(p)
                    && removed_defs.contains(v)
                {
                    return false;
                }
            }
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Rewrite
// ---------------------------------------------------------------------------

fn apply_plan(func: &mut MachFunction, plan: &Plan) {
    let n_inputs = plan.inputs.len() as i64;
    let stride = 8 * n_inputs;
    let scratch_bytes = (plan.bound * stride) as u64;
    assert!(
        scratch_bytes > 0 && scratch_bytes <= MAX_SCRATCH_BYTES,
        "loop-dead-pure-sink: planned scratch {scratch_bytes}B out of range (plan bug)"
    );
    let scratch_slot = func.alloc_stack_slot(StackSlot::new(scratch_bytes as u32, 8));

    // --- 1. Scratch base in the entry block (dominates everything). --------
    let sb = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let sp = trust_cg_ir::regs::SP;
    let addr_inst = func.push_inst(MachInst::new(
        AArch64Opcode::AddPCRel,
        vec![
            MachOperand::VReg(sb),
            MachOperand::PReg(sp),
            MachOperand::StackSlot(scratch_slot),
        ],
    ));
    let entry = func.entry;
    let entry_len = func.block(entry).insts.len();
    debug_assert!(entry_len >= 1, "entry must have a terminator");
    func.block_mut(entry).insts.insert(entry_len - 1, addr_inst);

    // --- 2. Header rewrite: drop the slice, insert captures. ----------------
    let slice_set: HashSet<InstId> = plan.slice.iter().copied().collect();
    let v_stride = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let v_cap = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let cap_stride_inst = func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v_stride), MachOperand::Imm(stride)],
    ));
    let cap_madd_inst = func.push_inst(MachInst::new(
        AArch64Opcode::Madd,
        vec![
            MachOperand::VReg(v_cap),
            MachOperand::VReg(plan.iv),
            MachOperand::VReg(v_stride),
            MachOperand::VReg(sb),
        ],
    ));
    let mut capture_insts: Vec<InstId> = vec![cap_stride_inst, cap_madd_inst];
    for (k, (input, _)) in plan.inputs.iter().enumerate() {
        capture_insts.push(func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(*input),
                MachOperand::VReg(v_cap),
                MachOperand::Imm(8 * k as i64),
            ],
        )));
    }
    let old_header = std::mem::take(&mut func.block_mut(plan.c_header).insts);
    let mut new_header: Vec<InstId> = Vec::with_capacity(old_header.len());
    for (pos, id) in old_header.into_iter().enumerate() {
        if pos == plan.capture_pos {
            new_header.extend_from_slice(&capture_insts);
        }
        if slice_set.contains(&id) {
            continue;
        }
        new_header.push(id);
    }
    func.block_mut(plan.c_header).insts = new_header;

    // --- 3. Deferred loop blocks on the exit edge. ---------------------------
    let dl_pre = func.create_block();
    let dl_body = func.create_block();
    let dl_latch = func.create_block();

    let v_q = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let v_q1 = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let v_t = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let v_k = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let v_pb = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let v_stride2 = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let v_sb2 = VReg::new(func.alloc_vreg(), RegClass::Gpr64);

    // DL_pre: q = 0.
    let pre_insts = [
        MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(v_q), MachOperand::Imm(0)],
        ),
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(dl_body)]),
    ];
    for inst in pre_insts {
        let id = func.push_inst(inst);
        func.append_inst(dl_pre, id);
    }

    // DL_body: addresses, captured loads, cloned slice, IV, branches.
    let mut body: Vec<MachInst> = vec![
        MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(v_k), MachOperand::Imm(plan.stride_k)],
        ),
        MachInst::new(
            AArch64Opcode::Madd,
            vec![
                MachOperand::VReg(v_pb),
                MachOperand::VReg(v_q),
                MachOperand::VReg(v_k),
                MachOperand::VReg(plan.target_base),
            ],
        ),
        MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(v_stride2), MachOperand::Imm(stride)],
        ),
        MachInst::new(
            AArch64Opcode::Madd,
            vec![
                MachOperand::VReg(v_sb2),
                MachOperand::VReg(v_q),
                MachOperand::VReg(v_stride2),
                MachOperand::VReg(sb),
            ],
        ),
    ];

    // Captured input loads; map original input vregs to the reloads.
    let mut vmap: HashMap<VReg, VReg> = HashMap::new();
    for (k, (input, _)) in plan.inputs.iter().enumerate() {
        let c_k = VReg::new(func.alloc_vreg(), RegClass::Fpr64);
        vmap.insert(*input, c_k);
        body.push(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(c_k),
                MachOperand::VReg(v_sb2),
                MachOperand::Imm(8 * k as i64),
            ],
        ));
    }

    // Clone the slice in original order.
    //
    // Remap discipline:
    //   * a vreg DEFINED by a slice inst (the removed set) gets ONE fresh
    //     name, shared by all its defs and uses in the clone (correct for the
    //     DefUse Movz/Movk chains, whose defs span several insts);
    //   * an input vreg maps to its scratch reload;
    //   * any other vreg (loop-invariant) passes through UNCHANGED — its def
    //     dominates the new blocks (checked during slice admission).
    let mut slice_defs: HashSet<VReg> = HashSet::new();
    for &orig_id in &plan.slice {
        let inst = func.inst(orig_id);
        for (pos, op) in inst.operands.iter().enumerate() {
            if let MachOperand::VReg(v) = op
                && operand_is_def(inst, pos)
            {
                slice_defs.insert(*v);
            }
        }
    }
    let store_off: HashMap<InstId, i64> = plan
        .stores
        .iter()
        .map(|s| (s.inst_id, s.total_off))
        .collect();
    for &orig_id in &plan.slice {
        let orig = func.inst(orig_id).clone();
        if let Some(&off) = store_off.get(&orig_id) {
            // Group store: re-expressed against the deferred position base.
            let MachOperand::VReg(orig_val) = orig.operands[0] else {
                unreachable!("recognized store has a vreg value");
            };
            let val = *vmap.get(&orig_val).unwrap_or(&orig_val);
            body.push(MachInst::new(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::VReg(val),
                    MachOperand::VReg(v_pb),
                    MachOperand::Imm(off),
                ],
            ));
            continue;
        }
        let mut cloned = orig;
        for op in cloned.operands.iter_mut() {
            let MachOperand::VReg(v) = op else { continue };
            let mapped = if let Some(m) = vmap.get(v) {
                *m
            } else if slice_defs.contains(v) {
                let fresh = VReg::new(func.alloc_vreg(), v.class);
                vmap.insert(*v, fresh);
                fresh
            } else {
                // Loop-invariant use: keep the original vreg.
                continue;
            };
            *op = MachOperand::VReg(mapped);
        }
        body.push(cloned);
    }

    // IV maintenance + exit test (mirrors the recognized C shape).
    body.push(MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::VReg(v_q1),
            MachOperand::VReg(v_q),
            MachOperand::Imm(1),
        ],
    ));
    body.push(MachInst::new(
        AArch64Opcode::CmpRI,
        vec![MachOperand::VReg(v_q1), MachOperand::Imm(plan.bound)],
    ));
    body.push(MachInst::new(
        AArch64Opcode::CSet,
        vec![MachOperand::VReg(v_t), MachOperand::Imm(0)],
    ));
    body.push(MachInst::new(
        AArch64Opcode::CmpRI,
        vec![MachOperand::VReg(v_t), MachOperand::Imm(0)],
    ));
    body.push(MachInst::new(
        AArch64Opcode::BCond,
        vec![MachOperand::Imm(1), MachOperand::Block(plan.exit_tgt)],
    ));
    body.push(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(dl_latch)],
    ));
    for inst in body {
        let id = func.push_inst(inst);
        func.append_inst(dl_body, id);
    }

    // DL_latch: q = q1; back edge.
    let latch_insts = [
        MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(v_q), MachOperand::VReg(v_q1)],
        ),
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(dl_body)]),
    ];
    for inst in latch_insts {
        let id = func.push_inst(inst);
        func.append_inst(dl_latch, id);
    }

    // --- 4. CFG surgery on the exit edge. ------------------------------------
    // Retarget src's terminator operands tgt -> DL_pre.
    let src_insts: Vec<InstId> = func.block(plan.exit_src).insts.clone();
    for id in src_insts {
        let inst = func.inst_mut(id);
        if !inst.is_branch() && !inst.is_terminator() {
            continue;
        }
        for op in inst.operands.iter_mut() {
            if let MachOperand::Block(t) = op
                && *t == plan.exit_tgt
            {
                *t = dl_pre;
            }
        }
    }
    for s in func.block_mut(plan.exit_src).succs.iter_mut() {
        if *s == plan.exit_tgt {
            *s = dl_pre;
        }
    }
    for p in func.block_mut(plan.exit_tgt).preds.iter_mut() {
        if *p == plan.exit_src {
            *p = dl_body;
        }
    }
    func.block_mut(dl_pre).preds = vec![plan.exit_src];
    func.block_mut(dl_pre).succs = vec![dl_body];
    func.block_mut(dl_body).preds = vec![dl_pre, dl_latch];
    func.block_mut(dl_body).succs = vec![plan.exit_tgt, dl_latch];
    func.block_mut(dl_latch).preds = vec![dl_body];
    func.block_mut(dl_latch).succs = vec![dl_body];

    // Loop depth metadata (regalloc spill weights; analyses recompute CFG).
    let tgt_depth = func.block(plan.exit_tgt).loop_depth;
    func.block_mut(dl_pre).loop_depth = tgt_depth;
    func.block_mut(dl_body).loop_depth = tgt_depth + 1;
    func.block_mut(dl_latch).loop_depth = tgt_depth + 1;

    // Layout: place the new blocks immediately before the exit target.
    func.block_order
        .retain(|b| *b != dl_pre && *b != dl_body && *b != dl_latch);
    let tgt_pos = func
        .block_order
        .iter()
        .position(|b| *b == plan.exit_tgt)
        .expect("exit target in layout");
    func.block_order.insert(tgt_pos, dl_latch);
    func.block_order.insert(tgt_pos, dl_body);
    func.block_order.insert(tgt_pos, dl_pre);
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::regs::{D0, SP, V0, V1};
    use trust_cg_ir::{PReg, Signature, Type};

    const CALL_DEFS: &[PReg] = &[V0, V1];
    const CALL_USES: &[PReg] = &[D0];

    fn g64(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }
    fn f64v(id: u32) -> VReg {
        VReg::new(id, RegClass::Fpr64)
    }

    /// Build the minimal almabench-shaped nest:
    ///
    /// ```text
    /// bb0: target/input slot bases, outer counter init      -> bb1
    /// bb1 (L header): iv init                               -> bb2
    /// bb2 (C header): Madd addr; input load; pure asin call;
    ///                 store; iv++; exit test                -> bb4 | bb3
    /// bb3 (C latch): MovR iv, iv'                           -> bb2
    /// bb4 (L latch): outer++; exit test                     -> bb5 | bb6
    /// bb6: MovR outer                                       -> bb1
    /// bb5 (exit): load target; Ret
    /// ```
    fn make_nest(mark_pure: bool) -> MachFunction {
        let mut f = MachFunction::new("nest".to_string(), Signature::new(vec![], vec![Type::I64]));
        let target_slot = f.alloc_stack_slot(StackSlot::new(64, 8));
        let input_slot = f.alloc_stack_slot(StackSlot::new(8, 8));

        let bb0 = f.entry;
        let bb1 = f.create_block();
        let bb2 = f.create_block();
        let bb3 = f.create_block();
        let bb4 = f.create_block();
        let bb5 = f.create_block();
        let bb6 = f.create_block();

        let v_tbase = g64(0);
        let v_ibase = g64(1);
        let v_outer = g64(2);
        let v_outer_z = g64(3);
        let push = |f: &mut MachFunction, bb, inst: MachInst| {
            let id = f.push_inst(inst);
            f.append_inst(bb, id);
        };

        // bb0
        push(
            &mut f,
            bb0,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    MachOperand::VReg(v_tbase),
                    MachOperand::PReg(SP),
                    MachOperand::StackSlot(target_slot),
                ],
            ),
        );
        push(
            &mut f,
            bb0,
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    MachOperand::VReg(v_ibase),
                    MachOperand::PReg(SP),
                    MachOperand::StackSlot(input_slot),
                ],
            ),
        );
        push(
            &mut f,
            bb0,
            MachInst::new(
                AArch64Opcode::Movz,
                vec![MachOperand::VReg(v_outer_z), MachOperand::Imm(0)],
            ),
        );
        push(
            &mut f,
            bb0,
            MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::VReg(v_outer), MachOperand::VReg(v_outer_z)],
            ),
        );
        push(
            &mut f,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        );

        // bb1 (L header): iv init
        let v_iv_z = g64(4);
        let v_iv = g64(5);
        push(
            &mut f,
            bb1,
            MachInst::new(
                AArch64Opcode::Movz,
                vec![MachOperand::VReg(v_iv_z), MachOperand::Imm(0)],
            ),
        );
        push(
            &mut f,
            bb1,
            MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::VReg(v_iv), MachOperand::VReg(v_iv_z)],
            ),
        );
        push(
            &mut f,
            bb1,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
        );

        // bb2 (C header)
        let v_k = g64(6);
        let v_addr = g64(7);
        let v_in = f64v(8);
        let v_res = f64v(9);
        let v_ivn = g64(10);
        let v_t = g64(11);
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::Movz,
                vec![MachOperand::VReg(v_k), MachOperand::Imm(8)],
            ),
        );
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::Madd,
                vec![
                    MachOperand::VReg(v_addr),
                    MachOperand::VReg(v_iv),
                    MachOperand::VReg(v_k),
                    MachOperand::VReg(v_tbase),
                ],
            ),
        );
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::VReg(v_in),
                    MachOperand::VReg(v_ibase),
                    MachOperand::Imm(0),
                ],
            ),
        );
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::Copy,
                vec![MachOperand::PReg(D0), MachOperand::VReg(v_in)],
            ),
        );
        let mut bl = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("asin".to_string())],
        )
        .with_implicit_uses(CALL_USES)
        .with_implicit_defs(CALL_DEFS);
        if mark_pure {
            bl.flags.insert(InstFlags::LIBM_PURE_CALL);
        }
        push(&mut f, bb2, bl);
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::Copy,
                vec![MachOperand::VReg(v_res), MachOperand::PReg(D0)],
            ),
        );
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::VReg(v_res),
                    MachOperand::VReg(v_addr),
                    MachOperand::Imm(0),
                ],
            ),
        );
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::VReg(v_ivn),
                    MachOperand::VReg(v_iv),
                    MachOperand::Imm(1),
                ],
            ),
        );
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::CmpRI,
                vec![MachOperand::VReg(v_ivn), MachOperand::Imm(4)],
            ),
        );
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::CSet,
                vec![MachOperand::VReg(v_t), MachOperand::Imm(0)],
            ),
        );
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::CmpRI,
                vec![MachOperand::VReg(v_t), MachOperand::Imm(0)],
            ),
        );
        push(
            &mut f,
            bb2,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![MachOperand::Imm(1), MachOperand::Block(bb4)],
            ),
        );
        push(
            &mut f,
            bb2,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );

        // bb3 (C latch)
        push(
            &mut f,
            bb3,
            MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::VReg(v_iv), MachOperand::VReg(v_ivn)],
            ),
        );
        push(
            &mut f,
            bb3,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
        );

        // bb4 (L latch)
        let v_outer_n = g64(12);
        let v_t2 = g64(13);
        push(
            &mut f,
            bb4,
            MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::VReg(v_outer_n),
                    MachOperand::VReg(v_outer),
                    MachOperand::Imm(1),
                ],
            ),
        );
        push(
            &mut f,
            bb4,
            MachInst::new(
                AArch64Opcode::CmpRI,
                vec![MachOperand::VReg(v_outer_n), MachOperand::Imm(2)],
            ),
        );
        push(
            &mut f,
            bb4,
            MachInst::new(
                AArch64Opcode::CSet,
                vec![MachOperand::VReg(v_t2), MachOperand::Imm(0)],
            ),
        );
        push(
            &mut f,
            bb4,
            MachInst::new(
                AArch64Opcode::CmpRI,
                vec![MachOperand::VReg(v_t2), MachOperand::Imm(0)],
            ),
        );
        push(
            &mut f,
            bb4,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![MachOperand::Imm(1), MachOperand::Block(bb5)],
            ),
        );
        push(
            &mut f,
            bb4,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb6)]),
        );

        // bb6 (L latch tail)
        push(
            &mut f,
            bb6,
            MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::VReg(v_outer), MachOperand::VReg(v_outer_n)],
            ),
        );
        push(
            &mut f,
            bb6,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        );

        // bb5 (exit): read the target slot after the loops.
        let v_out = f64v(14);
        push(
            &mut f,
            bb5,
            MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::VReg(v_out),
                    MachOperand::VReg(v_tbase),
                    MachOperand::Imm(0),
                ],
            ),
        );
        push(&mut f, bb5, MachInst::new(AArch64Opcode::Ret, vec![]));

        // CFG edges.
        f.add_edge(bb0, bb1);
        f.add_edge(bb1, bb2);
        f.add_edge(bb2, bb4);
        f.add_edge(bb2, bb3);
        f.add_edge(bb3, bb2);
        f.add_edge(bb4, bb5);
        f.add_edge(bb4, bb6);
        f.add_edge(bb6, bb1);

        // next_vreg above the manual ids.
        f.next_vreg = 100;
        f
    }

    fn count_bls(f: &MachFunction, block: BlockId) -> usize {
        f.block(block)
            .insts
            .iter()
            .filter(|id| f.inst(**id).opcode == AArch64Opcode::Bl)
            .count()
    }

    #[test]
    fn fires_on_almabench_shape() {
        let mut f = make_nest(true);
        let slots_before = f.stack_slots.len();
        let blocks_before = f.blocks.len();
        assert!(run_pass(&mut f));

        // A scratch slot was allocated.
        assert_eq!(f.stack_slots.len(), slots_before + 1);
        // Three deferred blocks were created.
        assert_eq!(f.blocks.len(), blocks_before + 3);
        // The call left the inner loop header (bb2)...
        assert_eq!(count_bls(&f, BlockId(2)), 0);
        // ...and exactly one clone lives in the deferred body.
        let deferred_bls: usize = (blocks_before..f.blocks.len())
            .map(|i| count_bls(&f, BlockId(i as u32)))
            .sum();
        assert_eq!(deferred_bls, 1);
        // The inner header now captures the input into the scratch slot: a
        // store whose value is the INPUT vreg (8).
        let header_has_capture = f.block(BlockId(2)).insts.iter().any(|id| {
            let inst = f.inst(*id);
            inst.opcode == AArch64Opcode::StrRI
                && inst.operands.first() == Some(&MachOperand::VReg(f64v(8)))
        });
        assert!(header_has_capture, "capture store missing");
        // The exit edge bb4 -> bb5 was retargeted to the deferred blocks.
        let bb4_succs = &f.block(BlockId(4)).succs;
        assert!(
            !bb4_succs.contains(&BlockId(5)),
            "exit edge must be split: {bb4_succs:?}"
        );
    }

    #[test]
    fn unmarked_call_blocks_firing() {
        let mut f = make_nest(false);
        assert!(!run_pass(&mut f), "unlicensed call must fail closed");
    }

    #[test]
    fn kill_switch_is_inert() {
        crate::env_lock::with_env_overrides(&[("TCG_NO_LOOP_DEAD_SINK", "1")], || {
            let mut f = make_nest(true);
            let mut pass = LoopDeadPureSink;
            assert!(!pass.run(&mut f));
            assert_eq!(count_bls(&f, BlockId(2)), 1, "loop untouched");
        });
    }

    #[test]
    fn in_loop_read_of_target_blocks_firing() {
        let mut f = make_nest(true);
        // Add a load of the target slot inside the OUTER loop latch (bb4):
        // the deferral would change the value it observes.
        let v_bad = f64v(90);
        let id = f.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::VReg(v_bad),
                MachOperand::VReg(g64(0)),
                MachOperand::Imm(0),
            ],
        ));
        f.block_mut(BlockId(4)).insts.insert(0, id);
        assert!(!run_pass(&mut f), "in-loop read must fail closed");
    }

    #[test]
    fn escaping_target_address_blocks_firing() {
        let mut f = make_nest(true);
        // Store the target base pointer to memory (address escape) in bb0.
        let id = f.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(g64(0)),
                MachOperand::VReg(g64(1)),
                MachOperand::Imm(0),
            ],
        ));
        let pos = f.block(BlockId(0)).insts.len() - 1;
        f.block_mut(BlockId(0)).insts.insert(pos, id);
        assert!(!run_pass(&mut f), "escaped address must fail closed");
    }
}
