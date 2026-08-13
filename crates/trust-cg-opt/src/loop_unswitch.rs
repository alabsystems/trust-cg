// trust-cg-opt - Invariant loop unswitching (machine level, pre-RA).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! INVARIANT LOOP UNSWITCHING: hoist a loop-invariant conditional branch out
//! of a loop by duplicating the loop body into two versions and deciding the
//! branch ONCE in the preheader.
//!
//! Stanford Queens' `Try` is the motivating shape: `if (i < 8) { Try(i+1,...) }
//! else *q = true;` sits INSIDE the j=1..8 trial loop, but `i < 8` is
//! loop-invariant (one `CSet` before the loop). Keeping the test in the body
//! means the bounded-early-exit full unroll replicates it 8x per call, and
//! post-RA the boolean is spilled, so every unrolled clone pays a serialized
//! `ldur + cbnz`. Unswitching moves the decision to the preheader (a single
//! well-predicted `cbnz` per loop entry) and each version's unrolled clones
//! carry NO invariant test at all.
//!
//! # The transform
//!
//! ```text
//!   preheader:  ...; b header           preheader:  ...; cbnz V, header_A; b header_B
//!   loop L (V single-def OUTSIDE L):
//!     C: ...; cmp V, #0; b.ne T1; b T2   version A (original blocks):
//!                                          C: ...; b T1
//!                                        version B (renamed clone):
//!                                          C': ...; b T2'
//! ```
//!
//! Version A is only entered when the branch would have been TAKEN on every
//! iteration; version B only when it would have FALLEN THROUGH. Because `V`
//! has a single definition outside the loop that dominates the preheader, its
//! value is frozen for the whole loop execution, so each version's constant
//! branch direction reproduces the original control flow exactly.
//!
//! # Soundness of vreg naming in the clone
//!
//! The two versions are MUTUALLY EXCLUSIVE within one activation: the
//! preheader test picks exactly one. Body-defined vregs whose uses are all
//! dominated by an in-body def are renamed to fresh ids in the clone
//! (restoring the single-def discipline the downstream unroller/fusion passes
//! key on — same policy as the bounded-early-exit unroll's per-clone rename).
//! Loop-carried vregs (defined in both the preheader and a latch, e.g. the
//! `j` phi-copy) are deliberately NOT renamed: the clone's latch redefines the
//! same vreg, which is semantically identical because only one version ever
//! executes — every use still sees the defs of its own version's path.
//!
//! # Fail-closed gates (decline on ANY departure)
//!
//! * innermost natural loops only, with a preheader whose terminator is an
//!   unconditional `B -> header` (single successor);
//! * loop body <= `MAX_BODY_BLOCKS` blocks and <= `MAX_BODY_INSTS`
//!   instructions (code growth is a straight 2x of the body);
//! * exactly ONE exit edge (body -> non-body), mirroring the unroller's
//!   discipline; the exit block gains the clone's exit edge;
//! * NO `Phi` in any body block or in the exit block, and NO body-defined
//!   vreg used outside the body (no live-outs): with those two facts the exit
//!   needs no phi surgery at all — the honest subset of the classic
//!   transform. Queens' `Try` loop has no register live-outs (all state flows
//!   through memory);
//! * exactly ONE invariant conditional branch in the loop, of the exact ISel
//!   shapes `Cbnz/Cbz V, T1; B T2` or `CmpRI V, #0; BCond EQ/NE, T1; B T2`
//!   (adjacent), with BOTH targets inside the loop and `V` single-def outside
//!   the loop, its def block dominating the preheader;
//! * for the `CmpRI` form the compare is DELETED in both versions, so the
//!   NZCV it wrote must be provably dead: every path from the branch block's
//!   successors must reach a flag WRITER (or a call, which clobbers NZCV)
//!   before any flag READER — else decline;
//! * one unswitch per function per pass run.
//!
//! Dead in-version paths (the not-taken target's subgraph, when it becomes
//! unreachable) are left in place; `cfg-simplify`'s unreachable-block removal
//! cleans them downstream. Kill switch: `TCG_NO_LOOP_UNSWITCH`; bisect key
//! `unswitch` (`TRUST_CG_DISABLE_PASSES=unswitch`).

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, CondCode, InstFlags, InstId, MachFunction, MachInst, MachOperand, VReg,
};

use crate::dom::DomTree;
use crate::effects::{
    aarch64_for_each_def_position, aarch64_for_each_use_position, reads_flags, writes_flags,
};
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Maximum number of blocks in an unswitchable loop body. Queens' `Try` trial
/// loop is 9 machine blocks (header + 3 guard tests + place + call + restore +
/// leaf-store + exit-test + latch); 12 keeps the "small trial loop" intent
/// with a little headroom.
const MAX_BODY_BLOCKS: usize = 12;

/// Maximum total instructions across the body (the clone doubles this).
const MAX_BODY_INSTS: usize = 96;

/// Compile-time kill switch: set `TCG_NO_LOOP_UNSWITCH` (any value) to
/// disable the pass entirely (byte-identical output to a build without it).
fn unswitch_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_LOOP_UNSWITCH").is_none()
}

/// Invariant loop unswitching pass (aarch64, pre-RA, runs right before
/// loop-unroll).
#[derive(Debug, Clone, Default)]
pub struct LoopUnswitch;

impl MachinePass for LoopUnswitch {
    fn name(&self) -> &str {
        "loop-unswitch"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if !unswitch_enabled() {
            return false;
        }
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        run_unswitch(func, &loop_analysis, &dom)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        if !unswitch_enabled() {
            return false;
        }
        let loop_analysis = analyses.loop_analysis(func).clone();
        // Use the cache's dominator tree instead of recomputing. Identical
        // content: `DomTree::compute` is deterministic over (entry, preds,
        // succs), the cached tree was computed over the same CFG, and the cache
        // is invalidated on any CFG-fingerprint change — an in-place rewrite
        // that survives the fingerprint cannot alter preds/succs. Recomputing
        // here paid one O(blocks) walk per pass invocation for nothing.
        let changed = {
            let dom = analyses.domtree(func);
            run_unswitch(func, &loop_analysis, dom)
        };
        changed
    }
}

/// A fully-validated unswitch site. All ids are captured read-only;
/// [`apply_unswitch`] performs the mutation.
struct UnswitchPlan {
    /// Loop header (version A keeps it).
    header: BlockId,
    /// The loop preheader (its `B -> header` terminator becomes the test).
    preheader: BlockId,
    /// Loop body blocks in `block_order` (deterministic clone order).
    body_blocks: Vec<BlockId>,
    /// The block containing the invariant conditional branch.
    branch_block: BlockId,
    /// The invariant `CmpRI V, #0` to delete in both versions (`None` for the
    /// raw `Cbnz`/`Cbz` form, which reads a register, not NZCV).
    cmp_id: Option<InstId>,
    /// The conditional branch instruction (`BCond` or `Cbnz`/`Cbz`).
    cond_br: InstId,
    /// `branch_block`'s trailing unconditional `B` (to `fallthrough`).
    b_term: InstId,
    /// Taken target of the invariant branch (version A branches here).
    taken: BlockId,
    /// Fallthrough target (the clone branches to its copy of this).
    fallthrough: BlockId,
    /// The invariant condition vreg.
    cond_vreg: VReg,
    /// Preheader test polarity: `true` -> `Cbnz V, header_A` (enter version A
    /// when `V != 0`), `false` -> `Cbz V, header_A`.
    test_is_cbnz: bool,
}

fn run_unswitch(func: &mut MachFunction, loop_analysis: &LoopAnalysis, dom: &DomTree) -> bool {
    if loop_analysis.is_empty() {
        return false;
    }

    // Innermost loops only (same filter as the unroller). `all_loops()`
    // iterates in header order (BTreeMap) — deterministic.
    let all_loops: Vec<NaturalLoop> = loop_analysis.all_loops().cloned().collect();

    for lp in &all_loops {
        let is_innermost = !all_loops.iter().any(|o| o.parent == Some(lp.header));
        if !is_innermost {
            continue;
        }
        if let Some(plan) = find_unswitch(func, lp, dom) {
            apply_unswitch(func, &plan);
            // Cap: one unswitch per function per run. The versions produced
            // here contain no invariant conditional branch (it was replaced
            // by unconditional `B`s), so a later run cannot re-fire on them.
            return true;
        }
    }
    false
}

fn as_vreg(op: &MachOperand) -> Option<VReg> {
    match op {
        MachOperand::VReg(v) => Some(*v),
        _ => None,
    }
}

fn as_block(op: &MachOperand) -> Option<BlockId> {
    match op {
        MachOperand::Block(b) => Some(*b),
        _ => None,
    }
}

fn as_imm(op: &MachOperand) -> Option<i64> {
    match op {
        MachOperand::Imm(i) => Some(*i),
        _ => None,
    }
}

/// Decode a `BCond` condition-code immediate. Only `EQ`/`NE` are accepted:
/// the preheader test is re-materialized as `Cbz`/`Cbnz` (no NZCV writer is
/// inserted into the preheader), which is exact only for compare-against-zero
/// equality senses.
fn decode_eq_ne(enc: i64) -> Option<CondCode> {
    match enc as u8 {
        0 => Some(CondCode::EQ),
        1 => Some(CondCode::NE),
        _ => None,
    }
}

/// Def sites of every vreg: `(inst, block)` pairs, over `block_order`.
fn build_def_sites(func: &MachFunction) -> HashMap<VReg, Vec<(InstId, BlockId)>> {
    let mut map: HashMap<VReg, Vec<(InstId, BlockId)>> = HashMap::new();
    for &b in &func.block_order {
        for &iid in &func.block(b).insts {
            let inst = func.inst(iid);
            aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |dp| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(dp) {
                    map.entry(*v).or_default().push((iid, b));
                }
            });
        }
    }
    map
}

/// True if any vreg defined inside `body` is used by an instruction outside
/// `body` (a register live-out — declined; see the module gates).
fn body_has_live_out(func: &MachFunction, body: &HashSet<BlockId>) -> bool {
    let mut body_defined: HashSet<VReg> = HashSet::new();
    for &b in body {
        for &iid in &func.block(b).insts {
            let inst = func.inst(iid);
            aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |dp| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(dp) {
                    body_defined.insert(*v);
                }
            });
        }
    }
    for &b in &func.block_order {
        if body.contains(&b) {
            continue;
        }
        for &iid in &func.block(b).insts {
            let inst = func.inst(iid);
            let mut found = false;
            aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |up| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(up)
                    && body_defined.contains(v)
                {
                    found = true;
                }
            });
            if found {
                return true;
            }
        }
    }
    false
}

/// True if the NZCV state at entry to each of `starts` is DEAD: every path
/// first reaches a flag writer (or a call, which architecturally clobbers
/// NZCV) before any flag reader. Fail-closed: any instruction whose flag
/// behavior is not positively known (codegen-expanded trap carriers, unknown
/// pseudos) counts as a reader.
fn nzcv_dead_from(func: &MachFunction, starts: &[BlockId]) -> bool {
    use AArch64Opcode::*;
    let mut seen: HashSet<BlockId> = HashSet::new();
    let mut work: Vec<BlockId> = starts.to_vec();
    while let Some(b) = work.pop() {
        if !seen.insert(b) {
            continue;
        }
        let mut killed = false;
        for &iid in &func.block(b).insts {
            let inst = func.inst(iid);
            let op = inst.opcode;
            // Readers first: a BCond or any CSel-family/carry consumer that
            // observes the deleted compare's flags makes the deletion unsound.
            if op == BCond || reads_flags(op) {
                return false;
            }
            // Trap carriers expand at codegen time into cmp/branch/brk
            // sequences — treat as unknown (fail closed).
            if matches!(
                op,
                Brk | TrapOverflow
                    | TrapBoundsCheck
                    | TrapBoundsCheckExact
                    | TrapNull
                    | TrapNullIfZero
                    | TrapDivZero
                    | TrapDivZeroIfZero
                    | TrapShiftRange
                    | TrapShiftRangeIfOOB
                    | TrapOverflowExact
            ) {
                return false;
            }
            if writes_flags(op) {
                killed = true;
                break;
            }
            let flags = inst.flags.union(op.default_flags());
            if flags.contains(InstFlags::IS_CALL) {
                // NZCV is caller-saved: the call clobbers it, so the deleted
                // compare's value cannot be observed past this point.
                killed = true;
                break;
            }
            if flags.contains(InstFlags::IS_PSEUDO) && !matches!(op, Copy | Nop | Phi | StackAlloc)
            {
                return false; // unknown expansion — fail closed
            }
        }
        if !killed {
            for &s in &func.block(b).succs {
                work.push(s);
            }
        }
    }
    true
}

/// Recognize an unswitchable invariant conditional branch in `lp`, applying
/// every gate from the module doc. Returns the validated plan or `None`.
fn find_unswitch(func: &MachFunction, lp: &NaturalLoop, dom: &DomTree) -> Option<UnswitchPlan> {
    let preheader = lp.preheader?;
    let header = lp.header;

    // Preheader must end in an unconditional `B -> header` and have the
    // header as its ONLY successor (we replace that terminator with the
    // version test).
    let ph_succs = &func.block(preheader).succs;
    if ph_succs.len() != 1 || ph_succs[0] != header {
        return None;
    }
    let &ph_term = func.block(preheader).insts.last()?;
    let ph_term_inst = func.inst(ph_term);
    if ph_term_inst.opcode != AArch64Opcode::B
        || ph_term_inst.operands.first() != Some(&MachOperand::Block(header))
    {
        return None;
    }

    // Size gates.
    if lp.body.len() > MAX_BODY_BLOCKS {
        return None;
    }
    let body_blocks: Vec<BlockId> = func
        .block_order
        .iter()
        .copied()
        .filter(|b| lp.body.contains(b))
        .collect();
    // Every body block must be in block_order (the clone iterates it).
    if body_blocks.len() != lp.body.len() {
        return None;
    }
    let body_insts: usize = body_blocks.iter().map(|b| func.block(*b).insts.len()).sum();
    if body_insts > MAX_BODY_INSTS {
        return None;
    }

    // Exactly one exit edge (body -> non-body).
    let mut exit_edge: Option<(BlockId, BlockId)> = None;
    for &b in &body_blocks {
        for &s in &func.block(b).succs {
            if !lp.body.contains(&s) {
                if exit_edge.is_some() {
                    return None;
                }
                exit_edge = Some((b, s));
            }
        }
    }
    let (_, exit_block) = exit_edge?;

    // No Phi anywhere the transform would have to patch: the body (cloned)
    // and the exit block (gains a predecessor).
    for &b in body_blocks.iter().chain(std::iter::once(&exit_block)) {
        for &iid in &func.block(b).insts {
            if func.inst(iid).opcode == AArch64Opcode::Phi {
                return None;
            }
        }
    }

    // No register live-outs from the body.
    if body_has_live_out(func, &lp.body) {
        return None;
    }

    let def_sites = build_def_sites(func);

    // Scan for invariant conditional branches; require EXACTLY one.
    let mut found: Option<UnswitchPlan> = None;
    for &c in &body_blocks {
        let insts = &func.block(c).insts;
        let n = insts.len();
        if n < 2 {
            continue;
        }
        let b_term = insts[n - 1];
        let b_inst = func.inst(b_term);
        if b_inst.opcode != AArch64Opcode::B {
            continue;
        }
        let Some(fallthrough) = b_inst.operands.first().and_then(as_block) else {
            continue;
        };

        let cond_br = insts[n - 2];
        let cbr = func.inst(cond_br);
        let (cond_vreg, taken, cmp_id, test_is_cbnz) = match cbr.opcode {
            AArch64Opcode::Cbnz | AArch64Opcode::Cbz => {
                let Some(v) = cbr.operands.first().and_then(as_vreg) else {
                    continue;
                };
                let Some(t1) = cbr.operands.get(1).and_then(as_block) else {
                    continue;
                };
                (v, t1, None, cbr.opcode == AArch64Opcode::Cbnz)
            }
            AArch64Opcode::BCond => {
                let Some(cc) = cbr.operands.first().and_then(as_imm).and_then(decode_eq_ne) else {
                    continue;
                };
                let Some(t1) = cbr.operands.get(1).and_then(as_block) else {
                    continue;
                };
                if n < 3 {
                    continue;
                }
                // The flag setter must be the ADJACENT `CmpRI V, #0`.
                let cmp = insts[n - 3];
                let cmp_inst = func.inst(cmp);
                if cmp_inst.opcode != AArch64Opcode::CmpRI {
                    continue;
                }
                let Some(v) = cmp_inst.operands.first().and_then(as_vreg) else {
                    continue;
                };
                if cmp_inst.operands.get(1).and_then(as_imm) != Some(0) {
                    continue;
                }
                (v, t1, Some(cmp), cc == CondCode::NE)
            }
            _ => continue,
        };

        // Both targets inside the loop, distinct, and exactly C's successors.
        if taken == fallthrough || !lp.body.contains(&taken) || !lp.body.contains(&fallthrough) {
            continue;
        }
        let succs = &func.block(c).succs;
        if succs.len() != 2 || !succs.contains(&taken) || !succs.contains(&fallthrough) {
            continue;
        }

        // `cond_vreg` must be single-def, defined OUTSIDE the loop, and its
        // def block must dominate the preheader (the hoisted test reads a
        // value that is always available and frozen for the whole loop).
        let Some(defs) = def_sites.get(&cond_vreg) else {
            continue;
        };
        if defs.len() != 1 {
            continue;
        }
        let def_block = defs[0].1;
        if lp.body.contains(&def_block) || !dom.dominates(def_block, preheader) {
            continue;
        }

        // For the CmpRI form the compare is deleted in both versions: its
        // NZCV result must be dead along every outgoing path.
        if cmp_id.is_some() && !nzcv_dead_from(func, &[taken, fallthrough]) {
            continue;
        }

        if found.is_some() {
            return None; // more than one invariant branch — decline (gate)
        }
        found = Some(UnswitchPlan {
            header,
            preheader,
            body_blocks: body_blocks.clone(),
            branch_block: c,
            cmp_id,
            cond_br,
            b_term,
            taken,
            fallthrough,
            cond_vreg,
            test_is_cbnz,
        });
    }
    found
}

/// Body-defined vregs SAFE to rename to fresh ids in the clone: every use
/// (function-wide) is inside a body block AND dominated by an in-body def.
/// This is the bounded-early-exit unroller's rename policy (minus its IV
/// exclusion, which does not apply here): renaming such a vreg per version is
/// semantically identical while preserving single-def form for downstream
/// passes. Loop-carried copies (preheader+latch defs) fail the dominance test
/// and keep their original id in the clone — correct because the two versions
/// are mutually exclusive. Returns a deterministically sorted list.
fn renamable_clone_vregs(func: &MachFunction, body: &[BlockId], dom: &DomTree) -> Vec<VReg> {
    let body_set: HashSet<BlockId> = body.iter().copied().collect();

    // Def sites of each vreg inside the body: (block, position-within-block).
    let mut defs: HashMap<VReg, Vec<(BlockId, usize)>> = HashMap::new();
    for &b in body {
        for (pos, &iid) in func.block(b).insts.iter().enumerate() {
            let inst = func.inst(iid);
            aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |dp| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(dp) {
                    defs.entry(*v).or_default().push((b, pos));
                }
            });
        }
    }

    // A use at (ub, upos) is covered iff some in-body def of `v` dominates it.
    let use_covered = |v: VReg, ub: BlockId, upos: usize| -> bool {
        let Some(sites) = defs.get(&v) else {
            return false;
        };
        sites.iter().any(|&(db, dpos)| {
            if db == ub {
                dpos < upos
            } else {
                dom.dominates(db, ub)
            }
        })
    };

    let mut unsafe_vregs: HashSet<VReg> = HashSet::new();
    for &b in &func.block_order {
        let in_body = body_set.contains(&b);
        for (pos, &iid) in func.block(b).insts.iter().enumerate() {
            let inst = func.inst(iid);
            aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |up| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(up)
                    && defs.contains_key(v)
                    && (!in_body || !use_covered(*v, b, pos))
                {
                    unsafe_vregs.insert(*v);
                }
            });
        }
    }

    let mut out: Vec<VReg> = defs
        .keys()
        .copied()
        .filter(|v| !unsafe_vregs.contains(v))
        .collect();
    out.sort();
    out
}

/// Clone `iid` verbatim (flags / source_loc preserved) with block operands
/// remapped via `map` and renamed vregs remapped via `vmap` (defs AND uses —
/// `vmap` only contains vregs proven safe to rename).
fn clone_remap(
    func: &MachFunction,
    iid: InstId,
    map: &HashMap<BlockId, BlockId>,
    vmap: &HashMap<VReg, VReg>,
) -> MachInst {
    let mut inst = func.inst(iid).clone();
    for op in &mut inst.operands {
        match op {
            MachOperand::Block(b) => {
                if let Some(&nb) = map.get(b) {
                    *b = nb;
                }
            }
            MachOperand::VReg(v) => {
                if let Some(&nv) = vmap.get(v) {
                    *v = nv;
                }
            }
            _ => {}
        }
    }
    inst
}

/// Add out-edges of a freshly-populated clone `block` from its branch
/// operands (same policy as the unroller).
fn wire_out_edges(func: &mut MachFunction, block: BlockId) {
    let mut targets: Vec<BlockId> = Vec::new();
    for &iid in &func.block(block).insts.clone() {
        for op in &func.inst(iid).operands {
            if let MachOperand::Block(b) = op
                && !targets.contains(b)
            {
                targets.push(*b);
            }
        }
    }
    for tgt in targets {
        func.add_edge(block, tgt);
    }
}

fn apply_unswitch(func: &mut MachFunction, plan: &UnswitchPlan) {
    // 1. Per-clone rename map for safe body vregs (deterministic order).
    let dom = DomTree::compute(func);
    let renamable = renamable_clone_vregs(func, &plan.body_blocks, &dom);
    let vmap: HashMap<VReg, VReg> = renamable
        .iter()
        .map(|&v| (v, VReg::new(func.alloc_vreg(), v.class)))
        .collect();

    // 2. Create the clone blocks (version B), preserving loop depth.
    let mut map: HashMap<BlockId, BlockId> = HashMap::new();
    for &bo in &plan.body_blocks {
        let nb = func.create_block();
        func.block_mut(nb).loop_depth = func.block(bo).loop_depth;
        map.insert(bo, nb);
    }

    // 3. Populate the clones. In the branch block the invariant test
    //    (`CmpRI` if present, plus the conditional branch) is SKIPPED, so the
    //    clone's terminator is the remapped trailing `B -> fallthrough'`.
    for &bo in &plan.body_blocks {
        let nb = map[&bo];
        for iid in func.block(bo).insts.clone() {
            if bo == plan.branch_block && (Some(iid) == plan.cmp_id || iid == plan.cond_br) {
                continue;
            }
            let ni = clone_remap(func, iid, &map, &vmap);
            let nid = func.push_inst(ni);
            func.append_inst(nb, nid);
        }
        wire_out_edges(func, nb);
    }

    // 4. Version A (original blocks): replace the invariant test with an
    //    unconditional `B -> taken`. The dropped `CmpRI`'s flags are proven
    //    dead (plan gate) and the original branch instructions are orphaned
    //    in the arena (standard practice; nothing references them).
    {
        let drop: [Option<InstId>; 3] = [plan.cmp_id, Some(plan.cond_br), Some(plan.b_term)];
        func.block_mut(plan.branch_block)
            .insts
            .retain(|id| !drop.contains(&Some(*id)));
        let nb = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(plan.taken)],
        ));
        func.append_inst(plan.branch_block, nb);
        // CFG: C -> {taken} only; the fallthrough edge belongs to the clone.
        func.block_mut(plan.branch_block).succs = vec![plan.taken];
        func.block_mut(plan.fallthrough)
            .preds
            .retain(|p| *p != plan.branch_block);
    }

    // 5. Preheader: replace `B -> header` with the version test. Polarity
    //    replicates the original branch exactly: version A is the TAKEN
    //    version, so `Cbnz` (for `!= 0` / NE senses) or `Cbz` (EQ) targets
    //    the ORIGINAL header; the fallthrough `B` enters the clone.
    {
        let ph = plan.preheader;
        // Validated in `find_unswitch`: the last inst is `B -> header`.
        func.block_mut(ph).insts.pop();
        let test_opcode = if plan.test_is_cbnz {
            AArch64Opcode::Cbnz
        } else {
            AArch64Opcode::Cbz
        };
        let test = func.push_inst(MachInst::new(
            test_opcode,
            vec![
                MachOperand::VReg(plan.cond_vreg),
                MachOperand::Block(plan.header),
            ],
        ));
        func.append_inst(ph, test);
        let clone_header = map[&plan.header];
        let b = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(clone_header)],
        ));
        func.append_inst(ph, b);
        // succs: [header] (existing edge, now the Cbnz/Cbz target) + the new
        // fallthrough edge into the clone (conditional-target-first order,
        // matching ISel's convention).
        func.add_edge(ph, clone_header);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{RegClass, Signature};

    fn vreg(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }

    fn op_v(id: u32) -> MachOperand {
        MachOperand::VReg(vreg(id))
    }

    fn op_b(b: BlockId) -> MachOperand {
        MachOperand::Block(b)
    }

    fn op_i(i: i64) -> MachOperand {
        MachOperand::Imm(i)
    }

    /// Build the Queens-`Try`-shaped loop:
    ///
    /// ```text
    ///  bb0 (preheader): v0=Movz #1 (invariant cond); v1=Movz #0; v2=MovR v1 (iv init); B bb1
    ///  bb1 (header):    v3=AddRI v2,#1 ; CmpRI v3,#0 ; BCond NE, bb2 ; B bb5
    ///  bb2 (C):         CmpRI v0,#0 ; BCond NE, bb3 ; B bb4      <- invariant branch
    ///  bb3 (taken):     v4=AddRI v3,#7 ; B bb5
    ///  bb4 (fallthru):  v5=AddRI v3,#9 ; B bb5
    ///  bb5 (exit test): CmpRI v3,#8 ; BCond NE, bb6 ; B bb7
    ///  bb6 (latch):     v2=MovR v3 ; B bb1
    ///  bb7 (exit):      Ret
    /// ```
    fn make_unswitchable_loop() -> MachFunction {
        let mut f = MachFunction::new("try_shape".to_string(), Signature::new(vec![], vec![]));
        let bb0 = f.entry;
        let bb1 = f.create_block();
        let bb2 = f.create_block();
        let bb3 = f.create_block();
        let bb4 = f.create_block();
        let bb5 = f.create_block();
        let bb6 = f.create_block();
        let bb7 = f.create_block();
        for _ in 0..6 {
            f.alloc_vreg();
        }

        // bb0
        for inst in [
            MachInst::new(AArch64Opcode::Movz, vec![op_v(0), op_i(1)]),
            MachInst::new(AArch64Opcode::Movz, vec![op_v(1), op_i(0)]),
            MachInst::new(AArch64Opcode::MovR, vec![op_v(2), op_v(1)]),
            MachInst::new(AArch64Opcode::B, vec![op_b(bb1)]),
        ] {
            let id = f.push_inst(inst);
            f.append_inst(bb0, id);
        }
        // bb1 (header): work + a NON-invariant conditional branch.
        for inst in [
            MachInst::new(AArch64Opcode::AddRI, vec![op_v(3), op_v(2), op_i(1)]),
            MachInst::new(AArch64Opcode::CmpRI, vec![op_v(3), op_i(0)]),
            MachInst::new(
                AArch64Opcode::BCond,
                vec![op_i(CondCode::NE.encoding() as i64), op_b(bb2)],
            ),
            MachInst::new(AArch64Opcode::B, vec![op_b(bb5)]),
        ] {
            let id = f.push_inst(inst);
            f.append_inst(bb1, id);
        }
        // bb2 (C): the INVARIANT branch.
        for inst in [
            MachInst::new(AArch64Opcode::CmpRI, vec![op_v(0), op_i(0)]),
            MachInst::new(
                AArch64Opcode::BCond,
                vec![op_i(CondCode::NE.encoding() as i64), op_b(bb3)],
            ),
            MachInst::new(AArch64Opcode::B, vec![op_b(bb4)]),
        ] {
            let id = f.push_inst(inst);
            f.append_inst(bb2, id);
        }
        // bb3 / bb4: version-divergent work, both to bb5.
        for inst in [
            MachInst::new(AArch64Opcode::AddRI, vec![op_v(4), op_v(3), op_i(7)]),
            MachInst::new(AArch64Opcode::B, vec![op_b(bb5)]),
        ] {
            let id = f.push_inst(inst);
            f.append_inst(bb3, id);
        }
        for inst in [
            MachInst::new(AArch64Opcode::AddRI, vec![op_v(5), op_v(3), op_i(9)]),
            MachInst::new(AArch64Opcode::B, vec![op_b(bb5)]),
        ] {
            let id = f.push_inst(inst);
            f.append_inst(bb4, id);
        }
        // bb5 (exit test)
        for inst in [
            MachInst::new(AArch64Opcode::CmpRI, vec![op_v(3), op_i(8)]),
            MachInst::new(
                AArch64Opcode::BCond,
                vec![op_i(CondCode::NE.encoding() as i64), op_b(bb6)],
            ),
            MachInst::new(AArch64Opcode::B, vec![op_b(bb7)]),
        ] {
            let id = f.push_inst(inst);
            f.append_inst(bb5, id);
        }
        // bb6 (latch)
        for inst in [
            MachInst::new(AArch64Opcode::MovR, vec![op_v(2), op_v(3)]),
            MachInst::new(AArch64Opcode::B, vec![op_b(bb1)]),
        ] {
            let id = f.push_inst(inst);
            f.append_inst(bb6, id);
        }
        // bb7 (exit)
        let ret = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        f.append_inst(bb7, ret);

        f.add_edge(bb0, bb1);
        f.add_edge(bb1, bb2);
        f.add_edge(bb1, bb5);
        f.add_edge(bb2, bb3);
        f.add_edge(bb2, bb4);
        f.add_edge(bb3, bb5);
        f.add_edge(bb4, bb5);
        f.add_edge(bb5, bb6);
        f.add_edge(bb5, bb7);
        f.add_edge(bb6, bb1);

        f
    }

    fn run_pass(f: &mut MachFunction) -> bool {
        LoopUnswitch.run(f)
    }

    #[test]
    fn fires_on_invariant_cmpri_bcond_shape() {
        let mut f = make_unswitchable_loop();
        let blocks_before = f.num_blocks();
        assert!(run_pass(&mut f), "pass must fire on the Try shape");
        // 7 body blocks cloned (bb1..bb6 = 6 body blocks: header, C, taken,
        // fallthrough, exit-test, latch).
        assert_eq!(f.num_blocks(), blocks_before + 6);

        // Preheader now ends: Cbnz v0 -> bb1 ; B -> clone header.
        let ph = f.block(BlockId(0));
        let n = ph.insts.len();
        let test = f.inst(ph.insts[n - 2]);
        assert_eq!(test.opcode, AArch64Opcode::Cbnz);
        assert_eq!(test.operands[0], op_v(0));
        assert_eq!(test.operands[1], op_b(BlockId(1)));
        let fall = f.inst(ph.insts[n - 1]);
        assert_eq!(fall.opcode, AArch64Opcode::B);
        assert_eq!(ph.succs.len(), 2);

        // Version A's branch block ends with a single unconditional B -> bb3,
        // and the invariant CmpRI is gone.
        let c = f.block(BlockId(2));
        let last = f.inst(*c.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::B);
        assert_eq!(last.operands[0], op_b(BlockId(3)));
        assert!(
            c.insts
                .iter()
                .all(|&id| f.inst(id).opcode != AArch64Opcode::CmpRI),
            "invariant CmpRI must be deleted in version A"
        );
        assert_eq!(c.succs, vec![BlockId(3)]);
        // bb4 lost its version-A predecessor.
        assert!(!f.block(BlockId(4)).preds.contains(&BlockId(2)));

        // The exit block gained the clone's exit edge.
        assert_eq!(f.block(BlockId(7)).preds.len(), 2);
    }

    #[test]
    fn clone_branch_block_falls_through_and_body_vregs_renamed() {
        let mut f = make_unswitchable_loop();
        assert!(run_pass(&mut f));
        // Clone blocks are appended in body block_order: bb8=hdr', bb9=C',
        // bb10=taken', bb11=fallthrough', bb12=exit-test', bb13=latch'.
        let c_clone = f.block(BlockId(9));
        let last = f.inst(*c_clone.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::B);
        assert_eq!(
            last.operands[0],
            op_b(BlockId(11)),
            "clone takes fallthrough"
        );
        assert!(
            c_clone
                .insts
                .iter()
                .all(|&id| f.inst(id).opcode != AArch64Opcode::BCond),
            "invariant branch must not survive in the clone"
        );

        // v3 (body-defined, dominated uses) is renamed in the clone header;
        // v2 (loop-carried preheader+latch copy) is NOT.
        let hdr_clone = f.block(BlockId(8));
        let add = f.inst(hdr_clone.insts[0]);
        assert_eq!(add.opcode, AArch64Opcode::AddRI);
        assert_ne!(add.operands[0], op_v(3), "v3 def must be renamed");
        assert_eq!(add.operands[1], op_v(2), "loop-carried v2 keeps its id");
        // Latch clone still writes v2.
        let latch_clone = f.block(BlockId(13));
        let mov = f.inst(latch_clone.insts[0]);
        assert_eq!(mov.opcode, AArch64Opcode::MovR);
        assert_eq!(mov.operands[0], op_v(2));
        assert_eq!(
            mov.operands[1], add.operands[0],
            "latch threads renamed iv-next"
        );
    }

    #[test]
    fn kill_switch_disables_pass() {
        crate::env_lock::with_env_overrides(&[("TCG_NO_LOOP_UNSWITCH", "1")], || {
            let mut f = make_unswitchable_loop();
            let blocks_before = f.num_blocks();
            assert!(!run_pass(&mut f));
            assert_eq!(f.num_blocks(), blocks_before);
        });
    }

    #[test]
    fn declines_branch_on_loop_defined_vreg() {
        let mut f = make_unswitchable_loop();
        // Make bb2's test read v3 (defined in the header) instead of v0.
        let cmp_id = f.block(BlockId(2)).insts[0];
        f.inst_mut(cmp_id).operands[0] = op_v(3);
        assert!(!run_pass(&mut f), "non-invariant condition must decline");
    }

    #[test]
    fn declines_multi_def_condition() {
        let mut f = make_unswitchable_loop();
        // Second def of v0 (still outside the loop).
        let extra = f.push_inst(MachInst::new(AArch64Opcode::Movz, vec![op_v(0), op_i(3)]));
        f.block_mut(BlockId(0)).insts.insert(0, extra);
        assert!(!run_pass(&mut f), "multi-def condition must decline");
    }

    #[test]
    fn declines_live_out_body_vreg() {
        let mut f = make_unswitchable_loop();
        // Use v3 (body-defined) in the exit block.
        let use_inst = f.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![op_v(5), op_v(3), op_i(1)],
        ));
        f.block_mut(BlockId(7)).insts.insert(0, use_inst);
        assert!(!run_pass(&mut f), "register live-out must decline");
    }

    #[test]
    fn declines_two_invariant_branches() {
        let mut f = make_unswitchable_loop();
        // Rewrite bb3 to end with a SECOND invariant conditional branch
        // (cbnz v0 -> bb5 ; b bb4). Both targets in-loop.
        let bb3 = BlockId(3);
        let cb = f.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![op_v(0), op_b(BlockId(5))],
        ));
        let b = f.push_inst(MachInst::new(AArch64Opcode::B, vec![op_b(BlockId(4))]));
        let keep = f.block(bb3).insts[0];
        f.block_mut(bb3).insts = vec![keep, cb, b];
        f.block_mut(bb3).succs = vec![BlockId(5), BlockId(4)];
        f.block_mut(BlockId(4)).preds.push(bb3);
        assert!(!run_pass(&mut f), "two invariant branches must decline");
    }

    #[test]
    fn declines_when_deleted_cmp_flags_are_read() {
        let mut f = make_unswitchable_loop();
        // Make the taken block CONSUME flags before setting them: a CSet at
        // its head would observe the deleted CmpRI's NZCV.
        let cset = f.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![op_v(4), op_i(CondCode::NE.encoding() as i64)],
        ));
        let bb3 = BlockId(3);
        let mut insts = f.block(bb3).insts.clone();
        insts.insert(0, cset);
        f.block_mut(bb3).insts = insts;
        assert!(
            !run_pass(&mut f),
            "flags reader after deleted cmp must decline"
        );
    }

    #[test]
    fn fires_on_raw_cbz_form_with_inverted_versions() {
        let mut f = make_unswitchable_loop();
        // Replace bb2's CmpRI+BCond with a single `Cbz v0 -> bb3`.
        let bb2 = BlockId(2);
        let cbz = f.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![op_v(0), op_b(BlockId(3))],
        ));
        let b = f.block(bb2).insts[2];
        f.block_mut(bb2).insts = vec![cbz, b];
        assert!(run_pass(&mut f));
        // Preheader test must be Cbz (taken -> original header).
        let ph = f.block(BlockId(0));
        let test = f.inst(ph.insts[ph.insts.len() - 2]);
        assert_eq!(test.opcode, AArch64Opcode::Cbz);
        assert_eq!(test.operands[1], op_b(BlockId(1)));
    }

    #[test]
    fn declines_loop_without_preheader_terminator_shape() {
        let mut f = make_unswitchable_loop();
        // Give the preheader a second successor (conditional entry) so its
        // terminator is no longer a lone `B -> header`.
        let bb0 = BlockId(0);
        let term = *f.block(bb0).insts.last().unwrap();
        *f.inst_mut(term) = MachInst::new(
            AArch64Opcode::BCond,
            vec![op_i(CondCode::NE.encoding() as i64), op_b(BlockId(1))],
        );
        let b7 = f.push_inst(MachInst::new(AArch64Opcode::B, vec![op_b(BlockId(7))]));
        f.append_inst(bb0, b7);
        f.add_edge(bb0, BlockId(7));
        assert!(
            !run_pass(&mut f),
            "conditional preheader terminator must decline"
        );
    }

    #[test]
    fn second_run_is_inert_after_unswitch() {
        let mut f = make_unswitchable_loop();
        assert!(run_pass(&mut f));
        assert!(
            !run_pass(&mut f),
            "versions contain no invariant conditional branch; must not re-fire"
        );
    }
}
