// trust-cg-opt — DIFFERENTIAL harness for the reaching-definitions analysis
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # Per-query differential validation of `reaching_defs_at`
//!
//! This module exists so the analysis core can be REWRITTEN — the planned
//! all-ids bitvector formulation, or any future fast path — and validated by
//! **exhaustive per-query agreement** instead of by byte-comparing 18 corpus
//! binaries. Byte-identity is a weaker instrument: a changed verdict that does
//! not change the folded constant, or changes code no corpus program contains,
//! is invisible to it.
//!
//! Three instruments, asserted together:
//!
//! 1. **An independent ORACLE** (`reaching_oracle`): the same documented
//!    semantics — Uninit seeded at entry only, GEN = last def in block,
//!    pred-joins restricted to succ-reachable blocks — implemented by a
//!    DIFFERENT algorithmic route (deterministic seeded worklist over
//!    `BTreeMap`s, no hash-order dependence). It shares only the audited
//!    operand-role table, deliberately: the def MODEL is common ground, the
//!    ALGORITHM is what must be independent.
//! 2. **A pointed CFG corpus** (`cfg_corpus`): every counterexample shape from
//!    the 2026-08-12 adversarial review (latch-def/header-use, def-after-use,
//!    entry-block uses, unreachable defs, double linkage, preds/succs
//!    asymmetry in BOTH directions, irreducible regions), plus a seeded random
//!    family. 32 ABSOLUTE expected verdicts guard against a rewrite that
//!    changes both compared paths identically — cross-path agreement alone
//!    cannot catch that.
//! 3. **The production paths x solution states**: one-shot (ctx=None), fresh
//!    `ReachingCtx`, and a WARM ctx whose all-ids product solution has already
//!    served earlier queries.
//!
//! ## Fail-closed malformed CFGs
//!
//! Both asymmetric cases are retained as tripwires, but the production contract
//! now declines every cross-block query when the reachable `preds` and `succs`
//! edge sets disagree. The oracle mirrors that boundary before running its
//! independent product semantics; in-block answers remain exact and available.

// ===========================================================================
// ORACLE HALF of the reaching-definitions differential harness.
//
// An INDEPENDENT reference implementation of `reaching_defs_at` /
// `unique_reaching_def`. It shares the audited DEF MODEL
// (`crate::effects::aarch64_def_operand_positions`) — deliberately, that table
// is the spec — but shares NO algorithm with the module under test:
//
//   production : one joint worklist over the whole set lattice, IN pulled from
//                `preds`, re-queued along `succs`, HashSet/HashMap throughout.
//   oracle     : per-site *graph reachability*. Each definition site is an
//                independent single-source problem over the transposed JOIN
//                graph (the `preds` relation reversed), blocked by any block
//                that has its own GEN. BTreeSet/BTreeMap + VecDeque, sorted
//                seeds, no hash iteration anywhere.
//
// Why the routes are equivalent (and why this one is the *spec*): the framework
// is `OUT[b] = GEN[b].is_some() ? {Inst(GEN[b])} : IN[b]`, i.e. every transfer
// function is either a constant or the identity, and the join is union. Such a
// framework is fully distributive AND decomposes elementwise: for a fixed site
// `s`, `s in OUT[b]` iff `b` is a source of `s`, or `GEN[b]` is None and some
// reachable predecessor carries `s`. That recurrence is *literally* single
// source reachability through the gen-free blocks, so the least fixpoint of the
// set-valued system equals the union over sites of these per-site reachability
// sets. BFS is complete, so the oracle always lands on the LEAST FIXPOINT —
// which is what makes it able to catch a production worklist that stops early.
// ===========================================================================

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use trust_cg_ir::{BlockId, InstId, MachBlock, MachFunction, MachOperand};

use crate::effects::aarch64_def_operand_positions;

/// A definition site reaching a program point — the oracle's own mirror of the
/// module-private `DefSite`. Ordering is derived and total (`Uninit` sorts
/// first), which is what makes the returned `BTreeSet` printable and
/// diff-stable in assertion failures.
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) enum OracleSite {
    /// Entry reached with no definition of the id on some pred-walk.
    Uninit,
    /// The instruction that (last) writes the id on some pred-walk.
    Inst(InstId),
}

// ---------------------------------------------------------------------------
// Primitives
// ---------------------------------------------------------------------------

/// Bounds-tolerant block lookup.
///
/// Production indexes `func.blocks[id.0]` and PANICS on a dangling BlockId; the
/// oracle skips it instead so a harness that fuzzes edges gets a comparison
/// failure rather than an unwind it cannot attribute. Use
/// [`oracle_cfg_sanity`] to assert no dangling ids exist before trusting an
/// agreement result.
fn oracle_block(func: &MachFunction, b: BlockId) -> Option<&MachBlock> {
    func.blocks.get(b.0 as usize)
}

/// True iff `inst` writes SOME vreg whose id is `id`.
///
/// Class-blind by construction (only `VReg::id` is compared, never
/// `VReg::class`), and driven by the same audited operand-role table the
/// analysis uses — sharing the def model is correct; sharing the algorithm is
/// not.
#[allow(dead_code)]
pub(crate) fn oracle_defines_id(func: &MachFunction, inst: InstId, id: u32) -> bool {
    let mi = match func.insts.get(inst.0 as usize) {
        Some(mi) => mi,
        None => return false,
    };
    aarch64_def_operand_positions(mi.opcode, mi.operands.len())
        .into_iter()
        .any(|pos| matches!(mi.operands.get(pos), Some(MachOperand::VReg(v)) if v.id == id))
}

/// The blocks reachable from `func.entry` along SUCC edges.
///
/// NOTE the deliberate asymmetry with the join below: reachability is a
/// `succs` question, the join is a `preds` question. Production makes exactly
/// the same split, and every divergence the adversarial review could construct
/// lived in the gap between the two.
#[allow(dead_code)]
pub(crate) fn oracle_reachable_blocks(func: &MachFunction) -> BTreeSet<BlockId> {
    let mut seen: BTreeSet<BlockId> = BTreeSet::new();
    let mut work: Vec<BlockId> = vec![func.entry];
    while let Some(b) = work.pop() {
        if !seen.insert(b) {
            continue;
        }
        if let Some(block) = oracle_block(func, b) {
            for &s in &block.succs {
                if !seen.contains(&s) {
                    work.push(s);
                }
            }
        }
    }
    seen
}

/// `(containing block, index in that block)` of `inst`, or `None` when it is
/// linked into no block at all.
///
/// FIRST linkage wins, in ascending `BlockId` order — matching BOTH production
/// paths: the one-shot `block_of` scans `func.blocks` in index order, and
/// `ReachingCtx::new` builds `loc` with `entry(..).or_insert(..)` over the same
/// order. `block_order` is NOT consulted by either, so the oracle must not
/// consult it either (a test that permutes `block_order` must not move a
/// verdict).
#[allow(dead_code)]
pub(crate) fn oracle_locate(func: &MachFunction, inst: InstId) -> Option<(BlockId, usize)> {
    for (idx, block) in func.blocks.iter().enumerate() {
        if let Some(pos) = block.insts.iter().position(|&i| i == inst) {
            return Some((BlockId(idx as u32), pos));
        }
    }
    None
}

/// Ascending in-block positions at which `id` is defined in `b`.
///
/// One entry per *instruction*, never per def operand: an instruction naming
/// the id at two def positions (LDP-style double defs, pre/post-index
/// writebacks) is one definition. Built by a forward scan; production reaches
/// the same fact by a backward `find` (one-shot) or a `partition_point` over a
/// prebuilt index (ctx).
fn oracle_def_positions(func: &MachFunction, b: BlockId, id: u32) -> Vec<usize> {
    let mut positions = Vec::new();
    if let Some(block) = oracle_block(func, b) {
        for (pos, &inst) in block.insts.iter().enumerate() {
            if oracle_defines_id(func, inst, id) {
                positions.push(pos);
            }
        }
    }
    positions
}

/// `GEN[b]` for every REACHABLE block: the LAST instruction in the block that
/// defines `id`. Later defs kill earlier ones inside a block, so one survivor
/// per block is exact.
fn oracle_gens(
    func: &MachFunction,
    reachable: &BTreeSet<BlockId>,
    id: u32,
) -> BTreeMap<BlockId, InstId> {
    let mut gens: BTreeMap<BlockId, InstId> = BTreeMap::new();
    for &b in reachable {
        if let (Some(&last), Some(block)) = (
            oracle_def_positions(func, b, id).last(),
            oracle_block(func, b),
        ) {
            gens.insert(b, block.insts[last]);
        }
    }
    gens
}

/// The TRANSPOSED JOIN GRAPH: `p -> { b : p is listed in b.preds }`, restricted
/// to reachable blocks on both ends.
///
/// This is the edge set the dataflow actually joins over. It is NOT the `succs`
/// graph: `succs` decides reachability, `preds` decides the join, and on an
/// asymmetric CFG they differ. Transposing `preds` (rather than reusing
/// `succs`) is what makes the oracle's propagation complete where the
/// production worklist — which re-queues along `succs` after changing an OUT —
/// can stop early.
fn oracle_join_edges(
    func: &MachFunction,
    reachable: &BTreeSet<BlockId>,
) -> BTreeMap<BlockId, BTreeSet<BlockId>> {
    let mut edges: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
    for &b in reachable {
        if let Some(block) = oracle_block(func, b) {
            for &p in &block.preds {
                if reachable.contains(&p) {
                    edges.entry(p).or_default().insert(b);
                }
            }
        }
    }
    edges
}

/// Blocks whose OUT carries a site seeded at `seeds`.
///
/// Deterministic BFS: `seeds` arrives sorted (a `BTreeSet`), the frontier is a
/// `VecDeque`, and every adjacency is a `BTreeSet`. A block that has its own
/// GEN is BLOCKED — `OUT[b] = {Inst(GEN[b])}` kills whatever flowed in — unless
/// it is itself a seed, in which case it already carries the site and needs no
/// re-entry. The reachability set of a set of sources is the union of the
/// per-source sets (the blocking predicate does not depend on the path), so
/// seeding one source at a time is equivalent and keeps each query readable.
fn oracle_carriers(
    join: &BTreeMap<BlockId, BTreeSet<BlockId>>,
    gens: &BTreeMap<BlockId, InstId>,
    seeds: &BTreeSet<BlockId>,
) -> BTreeSet<BlockId> {
    let mut carriers: BTreeSet<BlockId> = seeds.clone();
    let mut frontier: VecDeque<BlockId> = seeds.iter().copied().collect();
    while let Some(p) = frontier.pop_front() {
        let Some(targets) = join.get(&p) else {
            continue;
        };
        for &b in targets {
            if gens.contains_key(&b) {
                continue; // b redefines the id: its own GEN kills the site
            }
            if carriers.insert(b) {
                frontier.push_back(b);
            }
        }
    }
    carriers
}

// ---------------------------------------------------------------------------
// The oracle
// ---------------------------------------------------------------------------

/// The set of definitions of vreg-id `id` reaching `use_inst` (immediately
/// BEFORE it executes).
///
/// `None` mirrors `reaching_defs_at`'s `None` exactly and means one of:
/// * `use_inst` is linked into no block; or
/// * `use_inst`'s block is not reachable from `func.entry` via SUCC edges.
///
/// `Some(set)` may legitimately be EMPTY: a reachable non-entry block whose
/// every predecessor is unreachable (or which lists no preds at all) has
/// `IN = {}`. Production returns the same empty set — it is not `None`, and
/// `unique_reaching_def` turns it into `None` only because `len() != 1`.
#[allow(dead_code)]
pub(crate) fn oracle_reaching(
    func: &MachFunction,
    use_inst: InstId,
    id: u32,
) -> Option<BTreeSet<OracleSite>> {
    let (use_block, use_pos) = oracle_locate(func, use_inst)?;
    let reachable = oracle_reachable_blocks(func);
    if !reachable.contains(&use_block) {
        return None;
    }

    // (1) IN-BLOCK SHORTCUT. The last def STRICTLY before the use, inside the
    // use's own block, kills everything upstream — including the entry `Uninit`
    // marker. Straight-line, so it is exact and terminal.
    let positions = oracle_def_positions(func, use_block, id);
    if let Some(&pos) = positions.iter().rev().find(|&&p| p < use_pos) {
        let d = oracle_block(func, use_block)?.insts[pos];
        return Some(BTreeSet::from([OracleSite::Inst(d)]));
    }

    // (2) CFG COHERENCE. A cross-block fact cannot choose between redundant,
    // disagreeing edge views without risking a missed bypass or definition.
    // Production deliberately fails closed at this boundary; the oracle must
    // model that semantic precondition before exercising its independent
    // product-lattice algorithm.
    if !oracle_reachable_cfg_is_symmetric(func, &reachable) {
        return None;
    }

    // (3) CROSS-BLOCK. `IN[use_block]`, assembled exactly like the analysis'
    // `assemble_in`: the entry seed, plus the OUT of every REACHABLE listed
    // predecessor. Unreachable preds name edges that can never be traversed.
    let mut answer: BTreeSet<OracleSite> = BTreeSet::new();
    if use_block == func.entry {
        // The use is in the entry block with no def before it: control arrives
        // at the function with the id unwritten on that path. Seeded whether or
        // not the entry block has any preds (a loop back edge into entry ADDS
        // sites, it never removes this one).
        answer.insert(OracleSite::Uninit);
    }
    let contributors: BTreeSet<BlockId> = match oracle_block(func, use_block) {
        Some(block) => block
            .preds
            .iter()
            .copied()
            .filter(|p| reachable.contains(p))
            .collect(),
        None => BTreeSet::new(),
    };
    if contributors.is_empty() {
        return Some(answer);
    }

    let gens = oracle_gens(func, &reachable, id);
    let join = oracle_join_edges(func, &reachable);

    // The `Uninit` source. It lives in `IN[entry]`, so it escapes into
    // `OUT[entry]` only when the entry block has no def of the id at all.
    if !gens.contains_key(&func.entry) {
        let seeds = BTreeSet::from([func.entry]);
        if !oracle_carriers(&join, &gens, &seeds).is_disjoint(&contributors) {
            answer.insert(OracleSite::Uninit);
        }
    }

    // Every real def site. A block with a GEN emits it unconditionally — it
    // does NOT need to be pred-walk reachable from entry, only SUCC-reachable
    // (that is what put it in `reachable`).
    for (&gen_block, &def) in &gens {
        let seeds = BTreeSet::from([gen_block]);
        if !oracle_carriers(&join, &gens, &seeds).is_disjoint(&contributors) {
            answer.insert(OracleSite::Inst(def));
        }
    }

    Some(answer)
}

/// True iff the redundant edge views agree over successor-reachable blocks.
/// Edges wholly outside this executable region cannot affect a query.
fn oracle_reachable_cfg_is_symmetric(func: &MachFunction, reachable: &BTreeSet<BlockId>) -> bool {
    let mut from_succs = BTreeSet::new();
    let mut from_preds = BTreeSet::new();
    for &b in reachable {
        let Some(block) = oracle_block(func, b) else {
            return false;
        };
        from_succs.extend(
            block
                .succs
                .iter()
                .filter(|s| reachable.contains(s))
                .map(|&s| (b, s)),
        );
        from_preds.extend(
            block
                .preds
                .iter()
                .filter(|p| reachable.contains(p))
                .map(|&p| (p, b)),
        );
    }
    from_succs == from_preds
}

/// The single definition of `id` reaching `use_inst`, mirroring
/// `unique_reaching_def`: `Some(d)` iff the reaching set is EXACTLY one real
/// instruction. An empty set, two sites, or any `Uninit` member ⇒ `None`.
#[allow(dead_code)]
pub(crate) fn oracle_unique(func: &MachFunction, use_inst: InstId, id: u32) -> Option<InstId> {
    let sites = oracle_reaching(func, use_inst, id)?;
    if sites.len() != 1 {
        return None;
    }
    match sites.into_iter().next()? {
        OracleSite::Inst(d) => Some(d),
        OracleSite::Uninit => None,
    }
}

// ---------------------------------------------------------------------------
// CFG well-formedness — lets the harness classify a divergence
// ---------------------------------------------------------------------------

/// Structural defects that make `preds` and `succs` disagree.
///
/// Every constructible production/oracle divergence found so far needs one of
/// these; a clean report means the CFG is in the regime where the two
/// implementations MUST agree, and any difference is a genuine bug.
#[allow(dead_code)]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct OracleCfgSanity {
    /// `(a, b)` where `b` is in `a.succs` but `a` is not in `b.preds`.
    pub succ_without_pred_mirror: Vec<(BlockId, BlockId)>,
    /// `(p, b)` where `p` is in `b.preds` but `b` is not in `p.succs`.
    pub pred_without_succ_mirror: Vec<(BlockId, BlockId)>,
    /// Edges naming a BlockId outside `func.blocks` — production PANICS on
    /// these, so a harness must never generate one.
    pub dangling: Vec<(BlockId, BlockId)>,
}

#[allow(dead_code)]
impl OracleCfgSanity {
    /// True iff `preds` and `succs` are exact mirrors and no id dangles.
    pub fn is_clean(&self) -> bool {
        self.succ_without_pred_mirror.is_empty()
            && self.pred_without_succ_mirror.is_empty()
            && self.dangling.is_empty()
    }
}

/// Audit `preds`/`succs` mirroring across the whole function.
///
/// Edges are compared as SETS: `add_edge` twice makes a duplicate, and neither
/// union-join nor reachability can observe multiplicity, so a duplicate is not
/// a defect.
#[allow(dead_code)]
pub(crate) fn oracle_cfg_sanity(func: &MachFunction) -> OracleCfgSanity {
    let mut report = OracleCfgSanity::default();
    let n = func.blocks.len();
    let in_range = |b: BlockId| (b.0 as usize) < n;

    for (idx, block) in func.blocks.iter().enumerate() {
        let a = BlockId(idx as u32);
        for &s in &block.succs {
            if !in_range(s) {
                report.dangling.push((a, s));
                continue;
            }
            if !func.blocks[s.0 as usize].preds.contains(&a) {
                report.succ_without_pred_mirror.push((a, s));
            }
        }
        for &p in &block.preds {
            if !in_range(p) {
                report.dangling.push((p, a));
                continue;
            }
            if !func.blocks[p.0 as usize].succs.contains(&a) {
                report.pred_without_succ_mirror.push((p, a));
            }
        }
    }
    report.dangling.sort_unstable();
    report.dangling.dedup();
    report
}

// ---------------------------------------------------------------------------
// Third opinion: strict dominance
// ---------------------------------------------------------------------------

/// Iterative dominators over the REACHABLE subgraph, joined along `preds`
/// (the same edge set the dataflow joins over).
///
/// `dom[entry] = {entry}`; every other block starts at "all reachable blocks"
/// and shrinks. Blocks with no reachable predecessor keep the full set — the
/// vacuous answer, which is only meaningful on a mirror-consistent CFG.
fn oracle_dominators(
    func: &MachFunction,
    reachable: &BTreeSet<BlockId>,
) -> BTreeMap<BlockId, BTreeSet<BlockId>> {
    let all: BTreeSet<BlockId> = reachable.clone();
    let mut dom: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
    for &b in reachable {
        if b == func.entry {
            dom.insert(b, BTreeSet::from([b]));
        } else {
            dom.insert(b, all.clone());
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for &b in reachable {
            if b == func.entry {
                continue;
            }
            let mut acc: Option<BTreeSet<BlockId>> = None;
            if let Some(block) = oracle_block(func, b) {
                for &p in &block.preds {
                    if !reachable.contains(&p) {
                        continue;
                    }
                    let pd = match dom.get(&p) {
                        Some(pd) => pd.clone(),
                        None => continue,
                    };
                    acc = Some(match acc {
                        None => pd,
                        Some(a) => a.intersection(&pd).copied().collect(),
                    });
                }
            }
            let mut next = acc.unwrap_or_else(|| all.clone());
            next.insert(b);
            if dom.get(&b) != Some(&next) {
                dom.insert(b, next);
                changed = true;
            }
        }
    }
    dom
}

/// Does `def_inst` STRICTLY dominate `use_inst`? `None` = not applicable
/// (either instruction unlinked or in an unreachable block).
///
/// This is the THIRD opinion the harness triangulates with. On a CFG for which
/// [`oracle_cfg_sanity`] is clean, and for a vreg id with exactly one def site
/// linked into a reachable block, the adversarial review's theorem is:
///
/// ```text
/// oracle_unique(f, u, id) == Some(d)   <=>   oracle_strictly_dominates(f, d, u) == Some(true)
/// ```
///
/// Assert that only under a clean sanity report — on an asymmetric CFG a block
/// can be SUCC-reachable while pred-walk-unreachable, which makes the vacuous
/// "dominated by everything" answer disagree with an empty `IN`.
#[allow(dead_code)]
pub(crate) fn oracle_strictly_dominates(
    func: &MachFunction,
    def_inst: InstId,
    use_inst: InstId,
) -> Option<bool> {
    let (def_block, def_pos) = oracle_locate(func, def_inst)?;
    let (use_block, use_pos) = oracle_locate(func, use_inst)?;
    let reachable = oracle_reachable_blocks(func);
    if !reachable.contains(&def_block) || !reachable.contains(&use_block) {
        return None;
    }
    if def_block == use_block {
        return Some(def_pos < use_pos);
    }
    let dom = oracle_dominators(func, &reachable);
    Some(dom.get(&use_block).is_some_and(|d| d.contains(&def_block)))
}

// ---------------------------------------------------------------------------
// The oracle's own sanity tests (independent of the production analysis).
// ---------------------------------------------------------------------------

#[cfg(test)]
mod oracle_self_tests {
    use super::*;
    use trust_cg_ir::{AArch64Opcode, MachInst, RegClass, Signature, VReg};

    fn orc_func() -> MachFunction {
        MachFunction::new("orc".into(), Signature::new(vec![], vec![]))
    }
    fn orc_v(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }
    fn orc_im(x: i64) -> MachOperand {
        MachOperand::Imm(x)
    }
    fn orc_emit(
        f: &mut MachFunction,
        b: BlockId,
        op: AArch64Opcode,
        ops: Vec<MachOperand>,
    ) -> InstId {
        let id = f.push_inst(MachInst::new(op, ops));
        f.append_inst(b, id);
        id
    }

    /// Entry-block use with a def before it: the def kills the `Uninit` seed.
    #[test]
    fn oracle_inblock_def_kills_uninit() {
        let mut f = orc_func();
        let e = f.entry;
        let d = orc_emit(&mut f, e, AArch64Opcode::Movz, vec![orc_v(0), orc_im(41)]);
        let u = orc_emit(
            &mut f,
            e,
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(0), orc_v(0)],
        );
        assert_eq!(
            oracle_reaching(&f, u, 0),
            Some(BTreeSet::from([OracleSite::Inst(d)]))
        );
        assert_eq!(oracle_unique(&f, u, 0), Some(d));
        assert_eq!(oracle_strictly_dominates(&f, d, u), Some(true));
    }

    /// Entry-block use with no def: only the `Uninit` marker.
    #[test]
    fn oracle_entry_use_is_uninit_only() {
        let mut f = orc_func();
        let e = f.entry;
        let u = orc_emit(
            &mut f,
            e,
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(0), orc_v(0)],
        );
        assert_eq!(
            oracle_reaching(&f, u, 0),
            Some(BTreeSet::from([OracleSite::Uninit]))
        );
        assert_eq!(oracle_unique(&f, u, 0), None);
    }

    /// A later def in the same block does not reach a use before it.
    #[test]
    fn oracle_later_def_in_block_ignored() {
        let mut f = orc_func();
        let e = f.entry;
        let d = orc_emit(&mut f, e, AArch64Opcode::Movz, vec![orc_v(0), orc_im(5)]);
        let u = orc_emit(
            &mut f,
            e,
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(0), orc_v(0)],
        );
        orc_emit(&mut f, e, AArch64Opcode::Movz, vec![orc_v(0), orc_im(99)]);
        assert_eq!(oracle_unique(&f, u, 0), Some(d));
    }

    /// Diamond: both arm defs reach the join.
    #[test]
    fn oracle_diamond_joins_two_defs() {
        let mut f = orc_func();
        let e = f.entry;
        let (b1, b2, b3) = (f.create_block(), f.create_block(), f.create_block());
        f.add_edge(e, b1);
        f.add_edge(e, b2);
        f.add_edge(b1, b3);
        f.add_edge(b2, b3);
        let d1 = orc_emit(&mut f, b1, AArch64Opcode::Movz, vec![orc_v(0), orc_im(1)]);
        let d2 = orc_emit(&mut f, b2, AArch64Opcode::Movz, vec![orc_v(0), orc_im(2)]);
        let u = orc_emit(
            &mut f,
            b3,
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(0), orc_v(0)],
        );
        assert_eq!(
            oracle_reaching(&f, u, 0),
            Some(BTreeSet::from([OracleSite::Inst(d1), OracleSite::Inst(d2)]))
        );
        assert_eq!(oracle_unique(&f, u, 0), None);
        assert!(oracle_cfg_sanity(&f).is_clean());
        assert_eq!(oracle_strictly_dominates(&f, d1, u), Some(false));
    }

    /// Loop: the preheader def AND the latch redefinition both reach the header
    /// use, and the entry `Uninit` does NOT (the preheader def kills it).
    #[test]
    fn oracle_loop_back_edge_adds_latch_def() {
        let mut f = orc_func();
        let e = f.entry;
        let (h, l, x) = (f.create_block(), f.create_block(), f.create_block());
        f.add_edge(e, h);
        f.add_edge(h, l);
        f.add_edge(h, x);
        f.add_edge(l, h);
        let d0 = orc_emit(&mut f, e, AArch64Opcode::Movz, vec![orc_v(0), orc_im(1)]);
        let u = orc_emit(
            &mut f,
            h,
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(1), orc_v(0)],
        );
        let d1 = orc_emit(&mut f, l, AArch64Opcode::Movz, vec![orc_v(0), orc_im(1)]);
        orc_emit(&mut f, x, AArch64Opcode::Ret, vec![]);
        assert_eq!(
            oracle_reaching(&f, u, 0),
            Some(BTreeSet::from([OracleSite::Inst(d0), OracleSite::Inst(d1)]))
        );
        assert_eq!(oracle_unique(&f, u, 0), None);
        // The theorem: d0 does not STRICTLY dominate... it does dominate the
        // header, but uniqueness fails because a second def exists. The
        // dominance triangulation is only claimed for SINGLE-def ids.
        assert_eq!(oracle_strictly_dominates(&f, d0, u), Some(true));
    }

    /// A use in a block unreachable from entry ⇒ `None`, and an instruction
    /// linked into no block at all ⇒ `None`.
    #[test]
    fn oracle_unreachable_and_unlinked_are_none() {
        let mut f = orc_func();
        let e = f.entry;
        let orphan = f.create_block();
        orc_emit(&mut f, e, AArch64Opcode::Movz, vec![orc_v(0), orc_im(1)]);
        let u = orc_emit(
            &mut f,
            orphan,
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(0), orc_v(0)],
        );
        assert_eq!(oracle_reaching(&f, u, 0), None);
        let floating = f.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(0), orc_v(0)],
        ));
        assert_eq!(oracle_reaching(&f, floating, 0), None);
    }

    /// A def parked in an unreachable block contributes nothing.
    #[test]
    fn oracle_unreachable_def_does_not_contribute() {
        let mut f = orc_func();
        let e = f.entry;
        let dead = f.create_block();
        let live = f.create_block();
        f.add_edge(e, live);
        f.add_edge(dead, live);
        let d = orc_emit(&mut f, e, AArch64Opcode::Movz, vec![orc_v(0), orc_im(7)]);
        orc_emit(&mut f, dead, AArch64Opcode::Movz, vec![orc_v(0), orc_im(9)]);
        let u = orc_emit(
            &mut f,
            live,
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(0), orc_v(0)],
        );
        assert_eq!(oracle_unique(&f, u, 0), Some(d));
    }

    /// A reachable block with no mirrored predecessor is malformed, so its
    /// cross-block query fails closed before an empty `IN` can be mistaken for
    /// evidence.
    #[test]
    fn oracle_asymmetric_empty_in_fails_closed() {
        let mut f = orc_func();
        let e = f.entry;
        let b = f.create_block();
        f.add_edge(e, b);
        f.block_mut(b).preds.clear(); // asymmetric on purpose
        orc_emit(&mut f, e, AArch64Opcode::Movz, vec![orc_v(0), orc_im(7)]);
        let u = orc_emit(
            &mut f,
            b,
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(0), orc_v(0)],
        );
        assert_eq!(oracle_reaching(&f, u, 0), None);
        assert_eq!(oracle_unique(&f, u, 0), None);
        let sanity = oracle_cfg_sanity(&f);
        assert!(!sanity.is_clean());
        assert_eq!(sanity.succ_without_pred_mirror, vec![(e, b)]);
    }

    /// A store's operand 0 is a USE, and a post-index writeback base IS a def —
    /// the shared audited role table, exercised through the oracle's own path.
    #[test]
    fn oracle_uses_the_audited_role_table() {
        let mut f = orc_func();
        let e = f.entry;
        let p = MachOperand::VReg(VReg::new(0, RegClass::Gpr64));
        let q0 = MachOperand::VReg(VReg::new(2, RegClass::Fpr128));
        let q1 = MachOperand::VReg(VReg::new(3, RegClass::Fpr128));
        let d = orc_emit(&mut f, e, AArch64Opcode::Movz, vec![p.clone(), orc_im(64)]);
        let store = orc_emit(
            &mut f,
            e,
            AArch64Opcode::StrRI,
            vec![p.clone(), p.clone(), orc_im(0)],
        );
        assert!(!oracle_defines_id(&f, store, 0));
        let u0 = orc_emit(
            &mut f,
            e,
            AArch64Opcode::AddRR,
            vec![orc_v(1), p.clone(), p.clone()],
        );
        assert_eq!(oracle_unique(&f, u0, 0), Some(d));
        let wb = orc_emit(
            &mut f,
            e,
            AArch64Opcode::NeonLdpQPost,
            vec![q0, q1, p.clone(), orc_im(32)],
        );
        assert!(oracle_defines_id(&f, wb, 0));
        let u1 = orc_emit(
            &mut f,
            e,
            AArch64Opcode::AddRR,
            vec![orc_v(1), p.clone(), p],
        );
        assert_eq!(oracle_unique(&f, u1, 0), Some(wb));
    }

    /// Class-blind: a Gpr32 write kills a Gpr64 def of the same id.
    #[test]
    fn oracle_is_class_blind() {
        let mut f = orc_func();
        let e = f.entry;
        let x64 = MachOperand::VReg(VReg::new(0, RegClass::Gpr64));
        orc_emit(&mut f, e, AArch64Opcode::Movz, vec![x64.clone(), orc_im(1)]);
        let w = orc_emit(&mut f, e, AArch64Opcode::Movz, vec![orc_v(0), orc_im(2)]);
        let u = orc_emit(
            &mut f,
            e,
            AArch64Opcode::AddRR,
            vec![orc_v(1), x64.clone(), x64],
        );
        assert_eq!(oracle_unique(&f, u, 0), Some(w));
    }

    /// `block_order` is not part of the analysis: permuting it moves nothing.
    #[test]
    fn oracle_ignores_block_order() {
        let mut f = orc_func();
        let e = f.entry;
        let b = f.create_block();
        f.add_edge(e, b);
        let d = orc_emit(&mut f, e, AArch64Opcode::Movz, vec![orc_v(0), orc_im(3)]);
        let u = orc_emit(
            &mut f,
            b,
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(0), orc_v(0)],
        );
        let before = oracle_reaching(&f, u, 0);
        f.block_order = vec![b, e];
        assert_eq!(oracle_reaching(&f, u, 0), before);
        assert_eq!(oracle_unique(&f, u, 0), Some(d));
    }

    /// Determinism: repeated calls on the same function agree exactly.
    #[test]
    fn oracle_is_deterministic() {
        let mut f = orc_func();
        let e = f.entry;
        let (b1, b2, b3) = (f.create_block(), f.create_block(), f.create_block());
        f.add_edge(e, b1);
        f.add_edge(e, b2);
        f.add_edge(b1, b3);
        f.add_edge(b2, b3);
        f.add_edge(b3, b1);
        orc_emit(&mut f, b1, AArch64Opcode::Movz, vec![orc_v(0), orc_im(1)]);
        orc_emit(&mut f, b2, AArch64Opcode::Movz, vec![orc_v(0), orc_im(2)]);
        let u = orc_emit(
            &mut f,
            b3,
            AArch64Opcode::AddRR,
            vec![orc_v(1), orc_v(0), orc_v(0)],
        );
        let first = oracle_reaching(&f, u, 0);
        for _ in 0..64 {
            assert_eq!(oracle_reaching(&f, u, 0), first);
        }
    }
}
// CFG CORPUS — the fixture half of the reaching-definitions differential
// harness (see reaching_const.rs).
//
// Self-contained: depends only on `trust_cg_ir`, so it may be pasted at file
// scope under `#[cfg(test)]` or nested inside an existing `mod tests`.
#[cfg(test)]
#[allow(dead_code)]
pub(crate) mod cfg_corpus {
    use trust_cg_ir::{
        AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, Signature,
        VReg,
    };

    // ---------------------------------------------------------------------
    // Case
    // ---------------------------------------------------------------------

    /// One corpus entry.
    ///
    /// `well_formed` is the ONLY structural promise this half makes to the
    /// runner half:
    ///
    /// * `true`  — every `succs` edge has its `preds` mirror and vice versa
    ///   (built with `add_edge` alone). On these the fixpoint is confluent, so
    ///   the one-shot path, a fresh `ReachingCtx`, and a reused/warm
    ///   `ReachingCtx` MUST return identical verdicts for every
    ///   `(use_inst, vreg)` pair, on every run.
    /// * `false` — preds/succs are deliberately out of step. Cross-block
    ///   queries must fail closed before either dataflow engine runs; in-block
    ///   answers remain exact.
    pub(crate) struct Case {
        pub(crate) name: &'static str,
        pub(crate) func: MachFunction,
        pub(crate) well_formed: bool,
    }

    /// A vreg id that no corpus function mentions. Included in every
    /// [`query_vregs`] list so the "zero definition sites anywhere" path is
    /// exercised on every case, not only on `zero_defs_for_id`.
    pub(crate) const GHOST_ID: u32 = 4242;

    // ---------------------------------------------------------------------
    // Builders (same style as reaching_const.rs's own `mod tests`)
    // ---------------------------------------------------------------------

    fn new_func(name: &str) -> MachFunction {
        MachFunction::new(name.to_string(), Signature::new(vec![], vec![]))
    }

    fn w(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr32)
    }
    fn x(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }
    fn vr(v: VReg) -> MachOperand {
        MachOperand::VReg(v)
    }
    fn im(v: i64) -> MachOperand {
        MachOperand::Imm(v)
    }
    fn bl(b: BlockId) -> MachOperand {
        MachOperand::Block(b)
    }

    fn emit(f: &mut MachFunction, b: BlockId, op: AArch64Opcode, ops: Vec<MachOperand>) -> InstId {
        let id = f.push_inst(MachInst::new(op, ops));
        f.append_inst(b, id);
        id
    }

    /// `Movz v, #imm` — every def site in this corpus carries a DISTINCT
    /// immediate so a verdict of `Some(k)` names exactly one def site.
    fn movz(f: &mut MachFunction, b: BlockId, v: VReg, imm: i64) -> InstId {
        emit(f, b, AArch64Opcode::Movz, vec![vr(v), im(imm)])
    }

    /// `AddRR dst, src, src` — the queryable USE. `dst` is a scratch id that is
    /// never the id under test, so a use never doubles as a def of it.
    fn use_add(f: &mut MachFunction, b: BlockId, dst: VReg, src: VReg) -> InstId {
        emit(f, b, AArch64Opcode::AddRR, vec![vr(dst), vr(src), vr(src)])
    }

    fn br(f: &mut MachFunction, b: BlockId, target: BlockId) -> InstId {
        emit(f, b, AArch64Opcode::B, vec![bl(target)])
    }

    /// `CMP scratch, #0` + `B.cond taken` + `B fallthrough` — a two-successor
    /// terminator. Defines nothing (CmpRI/BCond/B produce no value).
    fn cond_br(f: &mut MachFunction, b: BlockId, taken: BlockId, fallthrough: BlockId) {
        emit(f, b, AArch64Opcode::CmpRI, vec![vr(w(99)), im(0)]);
        emit(f, b, AArch64Opcode::BCond, vec![im(0), bl(taken)]);
        br(f, b, fallthrough);
    }

    fn ret(f: &mut MachFunction, b: BlockId) -> InstId {
        emit(f, b, AArch64Opcode::Ret, vec![])
    }

    // ---------------------------------------------------------------------
    // Expected verdicts (absolute anchors)
    // ---------------------------------------------------------------------
    //
    // Cross-path agreement alone cannot catch a rewrite that changes BOTH
    // paths the same way. These pin the reviewed semantics themselves.

    /// Where a query is anchored. Block/pos for linked instructions; arena
    /// index for instructions deliberately left out of every block.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(crate) enum Site {
        /// `func.block(BlockId(b)).insts[pos]`
        At { block: usize, pos: usize },
        /// `InstId(i)` — an instruction in the arena, possibly unlinked.
        Arena { inst: usize },
    }

    /// One machine-checkable expectation: `unique_reaching_const(func, site,
    /// vreg) == verdict`, for the named case.
    pub(crate) struct Expect {
        pub(crate) case: &'static str,
        pub(crate) site: Site,
        pub(crate) vreg: VReg,
        pub(crate) verdict: Option<i64>,
        pub(crate) why: &'static str,
    }

    /// Resolve a [`Site`] against a case's function.
    pub(crate) fn site_inst(func: &MachFunction, site: Site) -> InstId {
        match site {
            Site::At { block, pos } => func.block(BlockId(block as u32)).insts[pos],
            Site::Arena { inst } => InstId(inst as u32),
        }
    }

    fn at(block: usize, pos: usize) -> Site {
        Site::At { block, pos }
    }

    fn expect(
        case: &'static str,
        site: Site,
        vreg: VReg,
        verdict: Option<i64>,
        why: &'static str,
    ) -> Expect {
        Expect {
            case,
            site,
            vreg,
            verdict,
            why,
        }
    }

    /// Absolute expected verdicts for the handcrafted corpus.
    ///
    /// Both malformed-CFG cases have a single fail-closed answer for every
    /// cross-block query.
    pub(crate) fn expectations() -> Vec<Expect> {
        vec![
            expect(
                "straight_line_def_then_use",
                at(2, 0),
                w(0),
                Some(7),
                "sole site in D, D on every entry->U path and strictly before U",
            ),
            expect(
                "def_in_latch_use_in_header",
                at(1, 0),
                w(0),
                None,
                "IN[H] = OUT[E] u OUT[L] = {Uninit, Movz#3}: iteration 1 arrives undefined",
            ),
            expect(
                "def_in_preheader_self_loop_header",
                at(2, 0),
                w(0),
                Some(9),
                "P GENs, killing Uninit; OUT[H]=IN[H] feeds back a set it already contains",
            ),
            expect(
                "sole_def_after_use_in_entry",
                at(0, 0),
                w(0),
                None,
                "assemble_in seeds Uninit at entry unconditionally; the def is BELOW the use",
            ),
            expect(
                "use_in_entry_def_elsewhere",
                at(0, 0),
                w(0),
                None,
                "IN[entry] = {Uninit}; a downstream def cannot reach backwards",
            ),
            expect(
                "def_only_in_unreachable_block",
                at(1, 0),
                w(0),
                None,
                "Z has no succ path from entry, so its Movz is not a def site; IN[U]={Uninit}",
            ),
            expect(
                "def_only_in_unreachable_block",
                at(2, 1),
                w(0),
                None,
                "the use itself sits in an unreachable block: the guard fires BEFORE the in-block def at pos 0",
            ),
            expect(
                "double_linked_def",
                at(3, 0),
                w(0),
                Some(7),
                "GEN[A] and GEN[B] are the SAME InstId, so the union is one DefSite",
            ),
            expect(
                "double_linked_use",
                at(3, 0),
                w(0),
                Some(7),
                "a doubly-linked use resolves in its FIRST block by BlockId (M), which block_of and ctx.loc both pick",
            ),
            expect(
                "double_linked_use",
                at(4, 0),
                w(0),
                Some(7),
                "same InstId asked through N: the answer must NOT depend on the asking block",
            ),
            expect(
                "zero_defs_for_id",
                at(1, 0),
                w(0),
                None,
                "no def site anywhere: Uninit flows entry->U untouched",
            ),
            expect(
                "diamond_two_defs",
                at(3, 0),
                w(0),
                None,
                "IN[M] = {Movz#1, Movz#2} — two sites on merging paths",
            ),
            expect(
                "two_defs_same_block",
                at(1, 1),
                w(0),
                Some(1),
                "in-block: LAST def strictly before the use wins; the later Movz#2 is invisible",
            ),
            expect(
                "two_defs_same_block",
                at(2, 0),
                w(0),
                Some(2),
                "GEN[D] is the LAST def in D; Movz#1 is killed inside the block",
            ),
            expect(
                "loop_carried_accumulator",
                at(3, 0),
                w(0),
                None,
                "IN[X]=OUT[H]=OUT[E] u OUT[body] = {Movz#1, Movz#2}: the .or_else accumulator shape",
            ),
            expect(
                "asym_succ_without_pred_mirror",
                at(2, 0),
                w(0),
                None,
                "reachable preds/succs disagree, so cross-block analysis declines before consulting GEN",
            ),
            expect(
                "irreducible_two_entry_loop",
                at(1, 0),
                w(0),
                Some(4),
                "id 0's sole site is the entry preheader; the fixpoint converges through the two-entry region",
            ),
            expect(
                "irreducible_two_entry_loop",
                at(2, 0),
                w(2),
                None,
                "id 2 is defined only in A, and E->B reaches B without passing A: {Uninit, Movz#6}",
            ),
            expect(
                "irreducible_two_entry_loop",
                at(2, 1),
                w(0),
                Some(4),
                "id 0 again, asked from the other loop entry",
            ),
            expect(
                "self_loop_def_and_use",
                at(1, 1),
                w(0),
                Some(3),
                "in-block def at pos 0 kills everything arriving on the back edge",
            ),
            expect(
                "unreachable_pred_carrying_def",
                at(1, 0),
                w(0),
                Some(1),
                "Z is a pred of U but is not succ-reachable: compute_out AND assemble_in must skip it, else {Movz#1, Movz#2}",
            ),
            expect(
                "duplicate_edge_to_same_target",
                at(1, 0),
                w(0),
                Some(7),
                "E appears twice in D.preds; the union is idempotent",
            ),
            expect(
                "class_blind_w_def_x_use",
                at(1, 0),
                x(0),
                Some(7),
                "defs match by vreg ID ONLY: a Gpr32 write is found by a Gpr64 query",
            ),
            expect(
                "class_blind_w_def_x_use",
                at(1, 0),
                w(0),
                Some(7),
                "same reaching set for the W view; class only affects the final truncation",
            ),
            expect(
                "unlinked_def_and_use",
                at(1, 0),
                w(0),
                None,
                "the Movz is in the arena but linked into no block, so it is not a def site",
            ),
            expect(
                "unlinked_def_and_use",
                Site::Arena { inst: 4 },
                w(0),
                None,
                "an unlinked USE cannot be located: block_of / ctx.loc both miss and the query fails closed",
            ),
            expect(
                "sole_def_after_use_in_loop_header",
                at(1, 0),
                w(0),
                None,
                "loop variant of the same shape: {Uninit, Movz#5} — iteration 1 reads an undefined value",
            ),
            expect(
                "entry_use_with_back_edge_def",
                at(0, 0),
                w(0),
                None,
                "Uninit is seeded at entry unconditionally, even though Movz#7 genuinely reaches around the back edge",
            ),
            expect(
                "movk_chain_across_blocks",
                at(2, 0),
                x(0),
                Some(500_001),
                "cross-block Movz+Movk: the Movk's tied input is resolved by a NESTED reaching-defs query at the Movk itself",
            ),
            expect(
                "tied_def_two_positions",
                at(1, 0),
                x(0),
                None,
                "the Ldp names id 0 at two DEF operand positions but is ONE def site, and it is the last one in E — a non-move-wide def, so the fold fails closed (Some(7) would mean the Ldp was dropped)",
            ),
            expect(
                "nested_loops_two_ids",
                at(2, 0),
                w(0),
                Some(11),
                "id 0's sole site is the outer preheader and it dominates the inner header",
            ),
            expect(
                "nested_loops_two_ids",
                at(2, 1),
                w(3),
                None,
                "id 3 is defined only in the inner body: {Uninit, Movz#12} at the inner header",
            ),
        ]
    }

    // ---------------------------------------------------------------------
    // The handcrafted corpus
    // ---------------------------------------------------------------------

    /// Every handcrafted case. Small (<= 6 blocks each) and structurally
    /// pointed; the numbered comments are the adversarial review's
    /// counterexample list.
    pub(crate) fn corpus() -> Vec<Case> {
        vec![
            case_straight_line(),
            case_def_in_latch_use_in_header(),
            case_def_in_preheader_self_loop_header(),
            case_sole_def_after_use_in_entry(),
            case_use_in_entry_def_elsewhere(),
            case_def_only_in_unreachable_block(),
            case_double_linked_def(),
            case_double_linked_use(),
            case_zero_defs_for_id(),
            case_diamond_two_defs(),
            case_two_defs_same_block(),
            case_loop_carried_accumulator(),
            case_asym_succ_without_pred_mirror(),
            case_asym_pred_without_succ_mirror(),
            case_irreducible_two_entry_loop(),
            case_self_loop_def_and_use(),
            // --- beyond the required list ---
            case_unreachable_pred_carrying_def(),
            case_duplicate_edge_to_same_target(),
            case_class_blind_w_def_x_use(),
            case_unlinked_def_and_use(),
            case_sole_def_after_use_in_loop_header(),
            case_entry_use_with_back_edge_def(),
            case_movk_chain_across_blocks(),
            case_tied_def_two_positions(),
            case_nested_loops_two_ids(),
        ]
    }

    /// 1. Straight line entry -> D -> U with one def in D.
    ///
    /// EXPECT `Some(7)` at U pos 0 for id 0. The single site is on every path
    /// from entry to the use and strictly precedes it, so `IN[U] = OUT[D] =
    /// {Movz#7}` and Uninit was killed by D's GEN.
    fn case_straight_line() -> Case {
        let mut f = new_func("straight_line");
        let (e, d, u) = (f.entry, f.create_block(), f.create_block());
        f.add_edge(e, d);
        f.add_edge(d, u);
        br(&mut f, e, d);
        movz(&mut f, d, w(0), 7);
        br(&mut f, d, u);
        use_add(&mut f, u, w(1), w(0));
        ret(&mut f, u);
        Case {
            name: "straight_line_def_then_use",
            func: f,
            well_formed: true,
        }
    }

    /// 2. Def in the loop LATCH, use in the HEADER (the shipped
    ///    `loop_redefinition_bails` shape, reduced to a SINGLE def site).
    ///
    /// EXPECT `None` at H pos 0 for id 0. One site, but two paths reach the
    /// header: `IN[H] = OUT[E] u OUT[L] = {Uninit, Movz#3}`. On iteration 1 the
    /// value is undefined, so the answer must be non-unique even though the
    /// function contains exactly one definition of the id.
    fn case_def_in_latch_use_in_header() -> Case {
        let mut f = new_func("latch_def");
        let (e, h, l, exit) = (
            f.entry,
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        f.add_edge(e, h);
        f.add_edge(h, l);
        f.add_edge(h, exit);
        f.add_edge(l, h);
        br(&mut f, e, h);
        use_add(&mut f, h, w(1), w(0)); // <- the use, pos 0
        cond_br(&mut f, h, exit, l);
        movz(&mut f, l, w(0), 3);
        br(&mut f, l, h);
        ret(&mut f, exit);
        Case {
            name: "def_in_latch_use_in_header",
            func: f,
            well_formed: true,
        }
    }

    /// 3. Def in a rotated PREHEADER, use in a self-looping header.
    ///
    /// EXPECT `Some(9)` at H pos 0 for id 0. `OUT[P] = {Movz#9}` (P's GEN kills
    /// the Uninit it received from entry) and `OUT[H] = IN[H]`, so the back edge
    /// feeds H a set it already contains — the fixpoint is `{Movz#9}`.
    fn case_def_in_preheader_self_loop_header() -> Case {
        let mut f = new_func("preheader_def");
        let (e, p, h, exit) = (
            f.entry,
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        f.add_edge(e, p);
        f.add_edge(p, h);
        f.add_edge(h, h);
        f.add_edge(h, exit);
        br(&mut f, e, p);
        movz(&mut f, p, w(0), 9);
        br(&mut f, p, h);
        use_add(&mut f, h, w(1), w(0)); // <- the use, pos 0
        cond_br(&mut f, h, h, exit);
        ret(&mut f, exit);
        Case {
            name: "def_in_preheader_self_loop_header",
            func: f,
            well_formed: true,
        }
    }

    /// 4. The single def sits in the use's OWN block, AFTER the use (CE-D).
    ///
    /// EXPECT `None` at entry pos 0 for id 0: the in-block scan partitions
    /// strictly below `use_pos` and finds nothing, and `assemble_in` seeds
    /// Uninit unconditionally for the entry block. This is the case that makes
    /// STRICT dominance mandatory — non-strict dominance answers `Some(5)` and
    /// folds an incoming value as a constant.
    fn case_sole_def_after_use_in_entry() -> Case {
        let mut f = new_func("def_after_use");
        let e = f.entry;
        use_add(&mut f, e, w(1), w(0)); // <- the use, pos 0
        movz(&mut f, e, w(0), 5); // the ONLY def site, pos 1
        ret(&mut f, e);
        Case {
            name: "sole_def_after_use_in_entry",
            func: f,
            well_formed: true,
        }
    }

    /// 5. Use in the ENTRY block, def elsewhere — Uninit must poison.
    ///
    /// EXPECT `None` at entry pos 0 for id 0. Entry has no predecessors, so
    /// `IN[entry] = {Uninit}` exactly; the set has ONE member, and it is the
    /// synthetic one, so this exercises the `DefSite::Uninit => None` arm rather
    /// than the cardinality check.
    fn case_use_in_entry_def_elsewhere() -> Case {
        let mut f = new_func("entry_use");
        let (e, d) = (f.entry, f.create_block());
        f.add_edge(e, d);
        use_add(&mut f, e, w(1), w(0)); // <- the use, pos 0
        br(&mut f, e, d);
        movz(&mut f, d, w(0), 7);
        ret(&mut f, d);
        Case {
            name: "use_in_entry_def_elsewhere",
            func: f,
            well_formed: true,
        }
    }

    /// 6. The only def sits in an UNREACHABLE block (no succ path from entry).
    ///
    /// EXPECT `None` at U pos 0 for id 0 — Z is not in `reachable_blocks`, so
    /// its Movz is not a def site at all and `IN[U] = OUT[E] = {Uninit}`.
    /// EXPECT `None` at Z pos 1 for id 0 as well — the use in Z is itself
    /// unreachable, and the reachability guard fires BEFORE the in-block fast
    /// path would have found the Movz at Z pos 0.
    fn case_def_only_in_unreachable_block() -> Case {
        let mut f = new_func("unreachable_def");
        let (e, u, z) = (f.entry, f.create_block(), f.create_block());
        f.add_edge(e, u); // z is deliberately left with no edges at all
        br(&mut f, e, u);
        use_add(&mut f, u, w(1), w(0)); // <- reachable use, pos 0
        ret(&mut f, u);
        movz(&mut f, z, w(0), 7); // pos 0
        use_add(&mut f, z, w(2), w(0)); // <- unreachable use, pos 1
        ret(&mut f, z);
        Case {
            name: "def_only_in_unreachable_block",
            func: f,
            well_formed: true,
        }
    }

    /// 7a. The same DEF INSTRUCTION linked into TWO blocks.
    ///
    /// EXPECT `Some(7)` at M pos 0 for id 0. `GEN[A]` and `GEN[B]` are the same
    /// `InstId`, so the merge at M is a ONE-element `HashSet<DefSite>` — double
    /// linkage collapses, it does not produce a spurious second site.
    fn case_double_linked_def() -> Case {
        let mut f = new_func("double_def");
        let (e, a, b, m) = (
            f.entry,
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        f.add_edge(e, a);
        f.add_edge(e, b);
        f.add_edge(a, m);
        f.add_edge(b, m);
        cond_br(&mut f, e, a, b);
        let shared = f.push_inst(MachInst::new(AArch64Opcode::Movz, vec![vr(w(0)), im(7)]));
        f.append_inst(a, shared); // linked into A ...
        br(&mut f, a, m);
        f.append_inst(b, shared); // ... and into B
        br(&mut f, b, m);
        use_add(&mut f, m, w(1), w(0)); // <- the use, pos 0
        ret(&mut f, m);
        Case {
            name: "double_linked_def",
            func: f,
            well_formed: true,
        }
    }

    /// 7b. The same USE INSTRUCTION linked into TWO blocks with DIFFERENT
    ///     incoming defs.
    ///
    /// EXPECT `Some(7)` for id 0 whether the site is named as M pos 0 or N pos 0
    /// — it is one `InstId`, and both `block_of` (first block by ascending
    /// `BlockId`) and `ReachingCtx::loc` (`or_insert`, blocks visited in
    /// ascending `BlockId`) resolve it to M. B's `Movz #8` must stay invisible.
    /// If a rewrite ever re-points a duplicated instruction at its LAST block
    /// this flips to `Some(8)`.
    fn case_double_linked_use() -> Case {
        let mut f = new_func("double_use");
        let (e, a, b, m, n) = (
            f.entry,
            f.create_block(),
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        f.add_edge(e, a);
        f.add_edge(e, b);
        f.add_edge(a, m);
        f.add_edge(b, n);
        cond_br(&mut f, e, a, b);
        movz(&mut f, a, w(0), 7);
        br(&mut f, a, m);
        movz(&mut f, b, w(0), 8);
        br(&mut f, b, n);
        let shared_use = f.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vr(w(1)), vr(w(0)), vr(w(0))],
        ));
        f.append_inst(m, shared_use);
        ret(&mut f, m);
        f.append_inst(n, shared_use);
        ret(&mut f, n);
        Case {
            name: "double_linked_use",
            func: f,
            well_formed: true,
        }
    }

    /// 8. An id with ZERO defs anywhere in the function.
    ///
    /// EXPECT `None` at U pos 0 for id 0: `gens` is empty, so every block simply
    /// forwards its input and the entry's Uninit reaches the use. The same holds
    /// for [`GHOST_ID`], which no case mentions at all.
    fn case_zero_defs_for_id() -> Case {
        let mut f = new_func("zero_defs");
        let (e, u) = (f.entry, f.create_block());
        f.add_edge(e, u);
        br(&mut f, e, u);
        use_add(&mut f, u, w(1), w(0)); // <- the use, pos 0
        ret(&mut f, u);
        Case {
            name: "zero_defs_for_id",
            func: f,
            well_formed: true,
        }
    }

    /// 9. Two def sites in DIFFERENT blocks on merging paths (diamond).
    ///
    /// EXPECT `None` at M pos 0 for id 0 — `IN[M] = {Movz#1, Movz#2}`.
    fn case_diamond_two_defs() -> Case {
        let mut f = new_func("diamond");
        let (e, t, fa, m) = (
            f.entry,
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        f.add_edge(e, t);
        f.add_edge(e, fa);
        f.add_edge(t, m);
        f.add_edge(fa, m);
        cond_br(&mut f, e, t, fa);
        movz(&mut f, t, w(0), 1);
        br(&mut f, t, m);
        movz(&mut f, fa, w(0), 2);
        br(&mut f, fa, m);
        use_add(&mut f, m, w(1), w(0)); // <- the use, pos 0
        ret(&mut f, m);
        Case {
            name: "diamond_two_defs",
            func: f,
            well_formed: true,
        }
    }

    /// 10. Two def sites in the SAME block — the last kills the first.
    ///
    /// EXPECT `Some(1)` at D pos 1 (the in-block use between the two defs):
    /// the last def STRICTLY before the use wins.
    /// EXPECT `Some(2)` at U pos 0: `GEN[D]` is the LAST def in D, so the first
    /// Movz never escapes the block.
    fn case_two_defs_same_block() -> Case {
        let mut f = new_func("two_defs_one_block");
        let (e, d, u) = (f.entry, f.create_block(), f.create_block());
        f.add_edge(e, d);
        f.add_edge(d, u);
        br(&mut f, e, d);
        movz(&mut f, d, w(0), 1); // pos 0
        use_add(&mut f, d, w(1), w(0)); // <- in-block use, pos 1
        movz(&mut f, d, w(0), 2); // pos 2
        br(&mut f, d, u); // pos 3
        use_add(&mut f, u, w(2), w(0)); // <- cross-block use, pos 0
        ret(&mut f, u);
        Case {
            name: "two_defs_same_block",
            func: f,
            well_formed: true,
        }
    }

    /// 11. Loop-carried accumulator: def BEFORE the loop and again IN the loop
    ///     body, use AFTER the loop (the `mul-shift-reduce` `.or_else` shape).
    ///
    /// EXPECT `None` at X pos 0 for id 0. `IN[X] = OUT[H] = OUT[E] u OUT[body] =
    /// {Movz#1, Movz#2}`: the pre-loop initializer and the in-loop update both
    /// reach the exit, so no constant is provable there.
    fn case_loop_carried_accumulator() -> Case {
        let mut f = new_func("acc_loop");
        let (e, h, body, exit) = (
            f.entry,
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        f.add_edge(e, h);
        f.add_edge(h, body);
        f.add_edge(h, exit);
        f.add_edge(body, h);
        movz(&mut f, e, w(0), 1);
        br(&mut f, e, h);
        cond_br(&mut f, h, exit, body);
        movz(&mut f, body, w(0), 2);
        br(&mut f, body, h);
        use_add(&mut f, exit, w(1), w(0)); // <- the use, pos 0
        ret(&mut f, exit);
        Case {
            name: "loop_carried_accumulator",
            func: f,
            well_formed: true,
        }
    }

    /// 12. ASYMMETRIC (CE-A): a succ-reachable block whose `preds` list is
    ///     missing the entry edge — the `if_convert.rs` `header.succs.clear()`
    ///     drift, built well-formed and then half-unbuilt.
    ///
    /// EXPECT `None` at U pos 0 for id 0: although D holds a GEN, the missing
    /// mirror means the executable edge views disagree. Cross-block analysis
    /// fails closed before choosing either view.
    fn case_asym_succ_without_pred_mirror() -> Case {
        let mut f = new_func("asym_succ");
        let (e, d, u) = (f.entry, f.create_block(), f.create_block());
        f.add_edge(e, d);
        f.add_edge(d, u);
        br(&mut f, e, d);
        movz(&mut f, d, w(0), 7);
        br(&mut f, d, u);
        use_add(&mut f, u, w(1), w(0)); // <- the use, pos 0
        ret(&mut f, u);
        // The drift: drop ONLY the pred half of E->D. E.succs still names D.
        f.block_mut(d).preds.retain(|&b| b != e);
        Case {
            name: "asym_succ_without_pred_mirror",
            func: f,
            well_formed: false,
        }
    }

    /// 13. ASYMMETRIC (CE-B): a block whose `preds` names a block that does not
    ///     list it in `succs`.
    ///
    /// EXPECT all cross-block queries to decline before the asymmetric
    /// predecessor graph reaches the product solver. This used to expose
    /// worklist-order nondeterminism and remains a regression tripwire.
    fn case_asym_pred_without_succ_mirror() -> Case {
        let mut f = new_func("asym_pred");
        let (e, d, u, z) = (
            f.entry,
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        f.add_edge(e, d);
        f.add_edge(d, u);
        f.add_edge(u, z);
        br(&mut f, e, d);
        movz(&mut f, d, x(0), 7);
        br(&mut f, d, u);
        use_add(&mut f, u, x(1), x(0)); // <- the use, pos 0
        br(&mut f, u, z);
        ret(&mut f, z);
        // The drift a branch retarget leaves when only `succs` is updated:
        // Z now claims E as a predecessor although E.succs = [D], and U claims
        // Z although Z.succs = [].
        f.block_mut(z).preds = vec![e];
        f.block_mut(u).preds.push(z);
        Case {
            name: "asym_pred_without_succ_mirror",
            func: f,
            well_formed: false,
        }
    }

    /// 14. Irreducible: a two-entry loop region (E branches into BOTH A and B,
    ///     which loop around each other) — no single loop header.
    ///
    /// EXPECT `Some(4)` at A pos 0 and at B pos 1 for id 0: its sole site is in
    /// the entry block, which dominates the whole region, and the fixpoint
    /// converges around the irreducible cycle without inventing a second site.
    /// EXPECT `None` at B pos 0 for id 2: id 2 is defined only in A, and the
    /// E->B entry reaches B without passing A, so `IN[B] = {Uninit, Movz#6}`.
    fn case_irreducible_two_entry_loop() -> Case {
        let mut f = new_func("irreducible");
        let (e, a, b, exit) = (
            f.entry,
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        f.add_edge(e, a);
        f.add_edge(e, b);
        f.add_edge(a, b);
        f.add_edge(b, a);
        f.add_edge(a, exit);
        movz(&mut f, e, w(0), 4);
        cond_br(&mut f, e, a, b);
        use_add(&mut f, a, w(1), w(0)); // <- use of id 0, pos 0
        movz(&mut f, a, w(2), 6); // sole site of id 2, pos 1
        cond_br(&mut f, a, b, exit);
        use_add(&mut f, b, w(3), w(2)); // <- use of id 2, pos 0
        use_add(&mut f, b, w(4), w(0)); // <- use of id 0, pos 1
        br(&mut f, b, a);
        ret(&mut f, exit);
        Case {
            name: "irreducible_two_entry_loop",
            func: f,
            well_formed: true,
        }
    }

    /// 15. A self-loop block containing BOTH the def and the use.
    ///
    /// EXPECT `Some(3)` at H pos 1 for id 0: the in-block fast path finds the
    /// def at pos 0 and returns before any cross-block reasoning, so the back
    /// edge (which carries the same site anyway) is irrelevant.
    fn case_self_loop_def_and_use() -> Case {
        let mut f = new_func("self_loop");
        let (e, h, exit) = (f.entry, f.create_block(), f.create_block());
        f.add_edge(e, h);
        f.add_edge(h, h);
        f.add_edge(h, exit);
        br(&mut f, e, h);
        movz(&mut f, h, w(0), 3); // pos 0
        use_add(&mut f, h, w(1), w(0)); // <- the use, pos 1
        cond_br(&mut f, h, h, exit);
        ret(&mut f, exit);
        Case {
            name: "self_loop_def_and_use",
            func: f,
            well_formed: true,
        }
    }

    /// EXTRA. A pred that is not succ-reachable, carrying a COMPETING def.
    ///
    /// EXPECT `Some(1)` at U pos 0 for id 0. Z is a genuine `preds` entry of U
    /// (added symmetrically), but nothing reaches Z from entry, so both
    /// `compute_out` and `assemble_in` must skip it. Dropping either
    /// reachability filter yields `{Movz#1, Movz#2}` and `None` — this case
    /// distinguishes them, unlike a lone unreachable def.
    fn case_unreachable_pred_carrying_def() -> Case {
        let mut f = new_func("unreachable_pred");
        let (e, u, z) = (f.entry, f.create_block(), f.create_block());
        f.add_edge(e, u);
        f.add_edge(z, u); // symmetric, but z has no path from entry
        movz(&mut f, e, w(0), 1);
        br(&mut f, e, u);
        use_add(&mut f, u, w(1), w(0)); // <- the use, pos 0
        ret(&mut f, u);
        movz(&mut f, z, w(0), 2);
        br(&mut f, z, u);
        Case {
            name: "unreachable_pred_carrying_def",
            func: f,
            well_formed: true,
        }
    }

    /// EXTRA. The same edge added twice (a conditional branch and its
    /// fallthrough both targeting D).
    ///
    /// EXPECT `Some(7)` at D pos 0 for id 0: `D.preds = [E, E]`, and the
    /// `assemble_in` union is idempotent. Also pins that `well_formed` is
    /// judged by edge CONTAINMENT, not by multiset equality.
    fn case_duplicate_edge_to_same_target() -> Case {
        let mut f = new_func("dup_edge");
        let (e, d) = (f.entry, f.create_block());
        f.add_edge(e, d);
        f.add_edge(e, d);
        movz(&mut f, e, w(0), 7);
        cond_br(&mut f, e, d, d);
        use_add(&mut f, d, w(1), w(0)); // <- the use, pos 0
        ret(&mut f, d);
        Case {
            name: "duplicate_edge_to_same_target",
            func: f,
            well_formed: true,
        }
    }

    /// EXTRA. Class-blind def matching: a `Gpr32` write, a `Gpr64` read.
    ///
    /// EXPECT `Some(7)` at U pos 0 for BOTH `x0` and `w0`: definitions are
    /// matched by vreg ID only, so the W write is the reaching def of the X
    /// view. (Class-blindness only ever ADDS reaching defs, which is
    /// fail-closed for uniqueness.)
    fn case_class_blind_w_def_x_use() -> Case {
        let mut f = new_func("class_blind");
        let (e, u) = (f.entry, f.create_block());
        f.add_edge(e, u);
        movz(&mut f, e, w(0), 7); // 32-bit write
        br(&mut f, e, u);
        use_add(&mut f, u, x(1), x(0)); // <- 64-bit read of the same id, pos 0
        ret(&mut f, u);
        Case {
            name: "class_blind_w_def_x_use",
            func: f,
            well_formed: true,
        }
    }

    /// EXTRA. Instructions present in the arena but linked into NO block.
    ///
    /// EXPECT `None` at U pos 0 for id 0: the unlinked Movz is not a def site
    /// (only block-linked instructions can execute), so Uninit reaches the use.
    /// EXPECT `None` for the unlinked AddRR used as the query site (arena index
    /// 4): neither `block_of` nor `ctx.loc` can locate it, and the query fails
    /// closed rather than panicking.
    fn case_unlinked_def_and_use() -> Case {
        let mut f = new_func("unlinked");
        let (e, u) = (f.entry, f.create_block());
        f.add_edge(e, u);
        br(&mut f, e, u);
        use_add(&mut f, u, w(1), w(0)); // arena 1 -- the linked use, U pos 0
        ret(&mut f, u);
        // Arena 3 and arena 4 are pushed but NEVER appended to a block: a def
        // that must not count, and a use that must not resolve.
        f.push_inst(MachInst::new(AArch64Opcode::Movz, vec![vr(w(0)), im(7)]));
        f.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vr(w(2)), vr(w(0)), vr(w(0))],
        ));
        Case {
            name: "unlinked_def_and_use",
            func: f,
            well_formed: true,
        }
    }

    /// EXTRA (CE-D, loop variant). The sole def sits after the use inside a
    /// SELF-LOOPING header — proof that case 4 is not an entry-block artifact.
    ///
    /// EXPECT `None` at H pos 0 for id 0: `IN[H] = OUT[E] u OUT[H] = {Uninit,
    /// Movz#5}`. Iteration 1 reads an undefined value; only iterations >= 2 see
    /// the Movz. Non-strict dominance answers `Some(5)` and miscompiles.
    fn case_sole_def_after_use_in_loop_header() -> Case {
        let mut f = new_func("def_after_use_loop");
        let (e, h, exit) = (f.entry, f.create_block(), f.create_block());
        f.add_edge(e, h);
        f.add_edge(h, h);
        f.add_edge(h, exit);
        br(&mut f, e, h);
        use_add(&mut f, h, w(1), w(0)); // <- the use, pos 0
        movz(&mut f, h, w(0), 5); // the ONLY def site, pos 1
        cond_br(&mut f, h, h, exit);
        ret(&mut f, exit);
        Case {
            name: "sole_def_after_use_in_loop_header",
            func: f,
            well_formed: true,
        }
    }

    /// EXTRA. Use in the entry block with a def that genuinely reaches it
    /// around a BACK EDGE into entry.
    ///
    /// EXPECT `None` at entry pos 0 for id 0: `IN[entry] = {Uninit} u OUT[D] =
    /// {Uninit, Movz#7}`. The Uninit seed at entry is unconditional — it is not
    /// suppressed by entry having predecessors.
    fn case_entry_use_with_back_edge_def() -> Case {
        let mut f = new_func("entry_back_edge");
        let (e, d, exit) = (f.entry, f.create_block(), f.create_block());
        f.add_edge(e, d);
        f.add_edge(d, e);
        f.add_edge(d, exit);
        use_add(&mut f, e, w(1), w(0)); // <- the use, entry pos 0
        br(&mut f, e, d);
        movz(&mut f, d, w(0), 7);
        cond_br(&mut f, d, e, exit);
        ret(&mut f, exit);
        Case {
            name: "entry_use_with_back_edge_def",
            func: f,
            well_formed: true,
        }
    }

    /// EXTRA. A `Movz` + `Movk` materialization chain SPLIT ACROSS BLOCKS.
    ///
    /// EXPECT `Some(500_001)` at U pos 0 for id 0 (`41249 | 7 << 16`). The Movk
    /// is a tied def-use, so it is the reaching def at U; resolving it issues a
    /// NESTED reaching-defs query at the Movk itself for the same id, which must
    /// find the Movz in the previous block. This also exercises repeated
    /// projection from the same warm all-ids solution.
    fn case_movk_chain_across_blocks() -> Case {
        let mut f = new_func("movk_chain");
        let (e, d, u) = (f.entry, f.create_block(), f.create_block());
        f.add_edge(e, d);
        f.add_edge(d, u);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x(0)), im(41_249)]);
        br(&mut f, e, d);
        emit(
            &mut f,
            d,
            AArch64Opcode::Movk,
            vec![vr(x(0)), im(7), im(16)],
        );
        br(&mut f, d, u);
        use_add(&mut f, u, x(1), x(0)); // <- the use, pos 0
        ret(&mut f, u);
        Case {
            name: "movk_chain_across_blocks",
            func: f,
            well_formed: true,
        }
    }

    /// EXTRA. ONE instruction that names the queried id at TWO def operand
    /// positions (`LDP x0, x1, [x0], #16` — data reg 0 and the writeback base
    /// are the same vreg).
    ///
    /// EXPECT `None` at U pos 0 for id 0. The Ldp is the LAST def of id 0 in E,
    /// and it is not a move-wide, so the fold fails closed. `Some(7)` would mean
    /// the Ldp had been dropped as a def site — the exact hazard in
    /// `ReachingCtx`'s `positions.last() != Some(&pos)` dedup, which must record
    /// ONE block position for an instruction that yields the id twice while the
    /// one-shot backward scan (a predicate over instructions) counts it once by
    /// construction.
    fn case_tied_def_two_positions() -> Case {
        let mut f = new_func("tied_two_positions");
        let (e, u) = (f.entry, f.create_block());
        f.add_edge(e, u);
        movz(&mut f, e, x(0), 7); // pos 0
        emit(
            &mut f,
            e,
            AArch64Opcode::LdpPostIndex,
            vec![vr(x(0)), vr(x(1)), vr(x(0)), im(16)],
        ); // pos 1: defines id 0 at operand 0 AND operand 2
        br(&mut f, e, u);
        use_add(&mut f, u, x(2), x(0)); // <- the use, pos 0
        ret(&mut f, u);
        Case {
            name: "tied_def_two_positions",
            func: f,
            well_formed: true,
        }
    }

    /// EXTRA. Nested loops, two ids — a deeper fixpoint with one id that
    /// survives it and one that does not.
    ///
    /// EXPECT `Some(11)` at H2 pos 0 for id 0: its sole site is the outer
    /// preheader (entry), which dominates the inner header.
    /// EXPECT `None` at H2 pos 1 for id 3: its sole site is the inner body, so
    /// the inner header sees `{Uninit, Movz#12}` on the first inner iteration.
    fn case_nested_loops_two_ids() -> Case {
        let mut f = new_func("nested_loops");
        let (e, h1, h2, body, latch1, exit) = (
            f.entry,
            f.create_block(),
            f.create_block(),
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        f.add_edge(e, h1);
        f.add_edge(h1, h2);
        f.add_edge(h1, exit);
        f.add_edge(h2, body);
        f.add_edge(h2, latch1);
        f.add_edge(body, h2);
        f.add_edge(latch1, h1);
        movz(&mut f, e, w(0), 11);
        br(&mut f, e, h1);
        cond_br(&mut f, h1, exit, h2);
        use_add(&mut f, h2, w(1), w(0)); // <- use of id 0, pos 0
        use_add(&mut f, h2, w(2), w(3)); // <- use of id 3, pos 1
        cond_br(&mut f, h2, body, latch1);
        movz(&mut f, body, w(3), 12);
        br(&mut f, body, h2);
        br(&mut f, latch1, h1);
        ret(&mut f, exit);
        Case {
            name: "nested_loops_two_ids",
            func: f,
            well_formed: true,
        }
    }

    // ---------------------------------------------------------------------
    // Query enumeration
    // ---------------------------------------------------------------------

    /// Every vreg worth querying on `func`, in a DETERMINISTIC order: each
    /// distinct `(id, class)` pair in arena order, plus the [`GHOST_ID`] vreg
    /// that no function defines.
    pub(crate) fn query_vregs(func: &MachFunction) -> Vec<VReg> {
        let mut out: Vec<VReg> = Vec::new();
        for inst in &func.insts {
            for op in &inst.operands {
                if let MachOperand::VReg(v) = op {
                    if !out.contains(v) {
                        out.push(*v);
                    }
                }
            }
        }
        out.push(VReg::new(GHOST_ID, RegClass::Gpr64));
        out
    }

    /// The exhaustive `(use_inst, vreg)` grid for one function, in a
    /// deterministic order.
    ///
    /// Covers EVERY instruction in the arena, including terminators (a query at
    /// a branch is legal and must answer), instructions in unreachable blocks,
    /// instructions linked into two blocks, and instructions linked into none —
    /// each of which is a distinct early-return in `reaching_defs_at`.
    pub(crate) fn query_points(func: &MachFunction) -> Vec<(InstId, VReg)> {
        let vregs = query_vregs(func);
        let mut out = Vec::with_capacity(func.insts.len() * vregs.len());
        for i in 0..func.insts.len() {
            for &v in &vregs {
                out.push((InstId(i as u32), v));
            }
        }
        out
    }

    // ---------------------------------------------------------------------
    // Seeded random family
    // ---------------------------------------------------------------------

    /// Hand-rolled 64-bit LCG + a splitmix output mix (the raw LCG's low bits
    /// are not usable modulo small n). No external crates, no clock: the same
    /// seed always yields byte-identical corpora.
    pub(crate) struct Lcg(u64);

    impl Lcg {
        pub(crate) fn new(seed: u64) -> Self {
            Lcg(seed ^ 0x9E37_79B9_7F4A_7C15)
        }

        fn next_u64(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let mut z = self.0;
            z ^= z >> 30;
            z = z.wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z ^= z >> 27;
            z = z.wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        /// Uniform-ish in `0..n` (`0` when `n == 0`).
        fn below(&mut self, n: usize) -> usize {
            if n == 0 {
                0
            } else {
                (self.next_u64() % n as u64) as usize
            }
        }

        /// True with probability `p/100`.
        fn pct(&mut self, p: u64) -> bool {
            self.next_u64() % 100 < p
        }
    }

    /// Reachability from block 0 over a raw edge list, for the generator's own
    /// repair step (the emitted function does not exist yet at that point).
    fn reachable_over(edges: &[(usize, usize)], n: usize) -> Vec<bool> {
        let mut seen = vec![false; n];
        let mut work = vec![0usize];
        while let Some(b) = work.pop() {
            if seen[b] {
                continue;
            }
            seen[b] = true;
            for &(s, t) in edges {
                if s == b && !seen[t] {
                    work.push(t);
                }
            }
        }
        seen
    }

    /// What a random block body slot holds.
    enum Slot {
        /// `Movz <id>, #imm` — every def carries a distinct immediate.
        Def { id: u32, class: RegClass, imm: i64 },
        /// `AddRR <scratch>, <lhs>, <rhs>` — the queryable use.
        Use {
            scratch: u32,
            lhs: u32,
            rhs: u32,
            class: RegClass,
        },
    }

    /// `n` deterministic random cases. Same `(seed, n)` => identical corpus,
    /// case for case and instruction for instruction.
    ///
    /// All edges go through `add_edge`, so every case is `well_formed: true`
    /// and every query MUST agree across the one-shot path, a fresh
    /// `ReachingCtx`, and a reused (warm) one.
    pub(crate) fn random_cases(seed: u64, n: usize) -> Vec<Case> {
        let mut rng = Lcg::new(seed);
        (0..n).map(|i| random_case(&mut rng, seed, i)).collect()
    }

    fn random_case(rng: &mut Lcg, seed: u64, index: usize) -> Case {
        let nblocks = 2 + rng.below(5); // 2..=6 blocks, entry included
        let nids = 1 + rng.below(3); // 1..=3 ids under test: 0..nids

        // --- shape: a mostly-connected digraph, built with add_edge only ---
        let mut edges: Vec<(usize, usize)> = Vec::new();
        for t in 1..nblocks {
            // A forward edge from a lower-numbered block keeps most blocks
            // reachable; skipping it deliberately strands some.
            if rng.pct(80) {
                let s = rng.below(t);
                edges.push((s, t));
            }
        }
        let extra = rng.below(nblocks + 1);
        for _ in 0..extra {
            // Unrestricted: self loops, back edges and cross edges all appear,
            // so loops and irreducible regions arise on their own.
            let s = rng.below(nblocks);
            let t = rng.below(nblocks);
            if !edges.contains(&(s, t)) {
                edges.push((s, t));
            }
        }
        // Cap out-degree at 2 so the terminator emitter below stays honest.
        let mut degree = vec![0usize; nblocks];
        let mut kept: Vec<(usize, usize)> = Vec::new();
        for (s, t) in edges {
            if degree[s] < 2 {
                degree[s] += 1;
                kept.push((s, t));
            }
        }
        // Reattach MOST stranded blocks: an all-unreachable tail would spend
        // the case on the reachability guard and never reach the fixpoint. The
        // rest stay stranded on purpose (unreachable defs must not count).
        for t in 1..nblocks {
            let reach = reachable_over(&kept, nblocks);
            if reach[t] || !rng.pct(70) {
                continue;
            }
            let start = rng.below(nblocks);
            for k in 0..nblocks {
                let s = (start + k) % nblocks;
                if reach[s] && degree[s] < 2 && !kept.contains(&(s, t)) {
                    degree[s] += 1;
                    kept.push((s, t));
                    break;
                }
            }
        }

        // --- bodies: planned first so the "at least one use" repair lands
        // --- before a block's terminator rather than after it.
        let mut next_imm: i64 = 1;
        let mut next_scratch: u32 = 200;
        let mut plan: Vec<Vec<Slot>> = Vec::with_capacity(nblocks);
        let mut any_use = false;
        for _ in 0..nblocks {
            let mut body = Vec::new();
            for _ in 0..rng.below(4) {
                let class = if rng.pct(50) {
                    RegClass::Gpr32
                } else {
                    RegClass::Gpr64
                };
                if rng.pct(50) {
                    body.push(Slot::Def {
                        id: rng.below(nids) as u32,
                        class,
                        imm: next_imm,
                    });
                    next_imm += 1;
                } else {
                    body.push(Slot::Use {
                        scratch: next_scratch,
                        lhs: rng.below(nids) as u32,
                        rhs: rng.below(nids) as u32,
                        class,
                    });
                    next_scratch += 1;
                    any_use = true;
                }
            }
            plan.push(body);
        }
        if !any_use {
            plan[0].push(Slot::Use {
                scratch: next_scratch,
                lhs: 0,
                rhs: 0,
                class: RegClass::Gpr32,
            });
        }

        // --- emit ---
        let mut f = new_func("rand");
        let mut blocks = vec![f.entry];
        for _ in 1..nblocks {
            blocks.push(f.create_block());
        }
        for &(s, t) in &kept {
            f.add_edge(blocks[s], blocks[t]);
        }
        for (bi, body) in plan.into_iter().enumerate() {
            let b = blocks[bi];
            for slot in body {
                match slot {
                    Slot::Def { id, class, imm } => {
                        movz(&mut f, b, VReg::new(id, class), imm);
                    }
                    Slot::Use {
                        scratch,
                        lhs,
                        rhs,
                        class,
                    } => {
                        emit(
                            &mut f,
                            b,
                            AArch64Opcode::AddRR,
                            vec![
                                vr(VReg::new(scratch, class)),
                                vr(VReg::new(lhs, class)),
                                vr(VReg::new(rhs, class)),
                            ],
                        );
                    }
                }
            }
            let succs = f.block(b).succs.clone();
            match succs.len() {
                0 => {
                    ret(&mut f, b);
                }
                1 => {
                    br(&mut f, b, succs[0]);
                }
                _ => cond_br(&mut f, b, succs[0], succs[1]),
            }
        }

        Case {
            name: Box::leak(format!("random_s{seed}_n{index}_b{nblocks}").into_boxed_str()),
            func: f,
            well_formed: true,
        }
    }
}

// ===========================================================================
// The differential runner
// ===========================================================================

#[cfg(test)]
mod differential_runner {
    use super::super::{DefSite, ReachingCtx, reaching_defs_at, unique_reaching_const};
    use super::cfg_corpus::{self, Case};
    use super::{OracleSite, oracle_reaching};
    use std::collections::BTreeSet;
    use std::collections::HashSet;

    fn to_oracle(s: &HashSet<DefSite>) -> BTreeSet<OracleSite> {
        s.iter()
            .map(|d| match d {
                DefSite::Uninit => OracleSite::Uninit,
                DefSite::Inst(i) => OracleSite::Inst(*i),
            })
            .collect()
    }

    /// The full corpus: every handcrafted shape plus three seeded random
    /// families. Determinism of the family is itself asserted elsewhere in the
    /// corpus module's self-tests.
    fn all_cases() -> Vec<Case> {
        let mut cases = cfg_corpus::corpus();
        for seed in [1u64, 2, 3] {
            cases.extend(cfg_corpus::random_cases(seed, 40));
        }
        cases
    }

    /// Absolute verdicts first: cross-path agreement cannot catch a rewrite
    /// that changes every compared path identically (e.g. swapping strict for
    /// non-strict dominance), so 32 expected outcomes are pinned against the
    /// reviewed semantics. Two of them (`sole_def_after_use_*`) are exactly the
    /// shapes non-strict dominance miscompiles.
    #[test]
    fn expectations_hold() {
        let cases = cfg_corpus::corpus();
        for e in cfg_corpus::expectations() {
            let case = cases
                .iter()
                .find(|c| c.name == e.case)
                .unwrap_or_else(|| panic!("expectation names unknown case {}", e.case));
            let use_inst = cfg_corpus::site_inst(&case.func, e.site);
            let got = unique_reaching_const(&case.func, use_inst, e.vreg);
            assert_eq!(
                got, e.verdict,
                "case `{}` site {:?} vreg {:?}: expected {:?}, got {:?} — {}",
                e.case, e.site, e.vreg, e.verdict, got, e.why
            );
        }
    }

    /// The differential proper: for every (case, use_inst, vreg-id) tuple,
    /// the independent oracle, the one-shot path, a fresh-context path and a
    /// WARM-context path must return the same reaching set.
    ///
    /// The warm context is the same `ReachingCtx` reused across the whole grid,
    /// so after the first cross-block query its all-ids product solution serves
    /// every later projection.
    #[test]
    fn oracle_and_both_production_paths_agree_everywhere() {
        let mut some_verdicts = 0usize;
        let mut none_verdicts = 0usize;
        let mut queries = 0usize;

        for case in all_cases() {
            let ctx_warm = ReachingCtx::new(&case.func);
            for (use_inst, vreg) in cfg_corpus::query_points(&case.func) {
                queries += 1;
                let oracle = oracle_reaching(&case.func, use_inst, vreg.id);
                let one_shot =
                    reaching_defs_at(&case.func, None, use_inst, vreg.id).map(|s| to_oracle(&s));
                let fresh = {
                    let ctx = ReachingCtx::new(&case.func);
                    reaching_defs_at(&case.func, Some(&ctx), use_inst, vreg.id)
                        .map(|s| to_oracle(&s))
                };
                let warm = reaching_defs_at(&case.func, Some(&ctx_warm), use_inst, vreg.id)
                    .map(|s| to_oracle(&s));

                let ctx_label = ["one-shot", "fresh-ctx", "warm-ctx"];
                for (i, got) in [&one_shot, &fresh, &warm].into_iter().enumerate() {
                    assert_eq!(
                        &oracle, got,
                        "case `{}` (well_formed={}) use {:?} id {}: oracle {:?} != {} {:?}",
                        case.name, case.well_formed, use_inst, vreg.id, oracle, ctx_label[i], got
                    );
                }

                match &oracle {
                    Some(set) if set.len() == 1 && !set.contains(&OracleSite::Uninit) => {
                        some_verdicts += 1;
                    }
                    _ => none_verdicts += 1,
                }
            }
        }

        eprintln!(
            "differential grid: {queries} queries, {some_verdicts} unique-def, {none_verdicts} other"
        );
        // VACUITY GATE. A harness where every query resolves to "nothing
        // reaches" compares nothing. The corpus is built so a substantial
        // fraction of queries have a real unique reaching def; if a refactor
        // of the corpus or the query grid ever drives this below the floor,
        // the harness must fail rather than pass emptily.
        // Floor set from measurement: the shipped corpus produces 31%
        // (4241/13603) unique-def verdicts. 25% leaves headroom for corpus
        // growth while still failing loudly if the battery ever goes hollow.
        assert!(
            some_verdicts * 4 >= queries,
            "vacuous battery: only {some_verdicts} unique-def verdicts across \
             {queries} queries ({none_verdicts} non-unique)"
        );
    }

    /// The random family must be a pure function of its seed: same seed, same
    /// corpus, byte for byte. The draft that produced it verified this
    /// externally; this pins it so a future edit (e.g. someone reaching for
    /// `HashMap` inside the generator) fails here instead of silently making
    /// every differential run test a different corpus.
    #[test]
    fn random_family_is_deterministic() {
        for seed in [1u64, 2, 3, 0xC0FFEE] {
            let a = cfg_corpus::random_cases(seed, 12);
            let b = cfg_corpus::random_cases(seed, 12);
            assert_eq!(a.len(), b.len());
            for (x, y) in a.iter().zip(&b) {
                assert_eq!(x.name, y.name, "seed {seed}");
                assert_eq!(
                    format!("{:?}{:?}", x.func.insts, x.func.blocks),
                    format!("{:?}{:?}", y.func.insts, y.func.blocks),
                    "seed {seed}: case {} not reproducible",
                    x.name
                );
            }
        }
        let a = cfg_corpus::random_cases(7, 8);
        let b = cfg_corpus::random_cases(8, 8);
        assert!(
            format!(
                "{:?}",
                a.iter().map(|c| c.func.insts.len()).collect::<Vec<_>>()
            ) != format!(
                "{:?}",
                b.iter().map(|c| c.func.insts.len()).collect::<Vec<_>>()
            ) || format!("{:?}", a[0].func.blocks) != format!("{:?}", b[0].func.blocks),
            "different seeds should produce different corpora"
        );
    }

    /// Repeated queries against ONE context must be stable: the lazy all-ids
    /// product solution must never return a different answer on later
    /// projections than on the query that initialized it.
    #[test]
    fn warm_solution_is_stable_across_repeats() {
        for case in all_cases() {
            let ctx = ReachingCtx::new(&case.func);
            for (use_inst, vreg) in cfg_corpus::query_points(&case.func) {
                let first = reaching_defs_at(&case.func, Some(&ctx), use_inst, vreg.id)
                    .map(|s| to_oracle(&s));
                for _ in 0..2 {
                    let again = reaching_defs_at(&case.func, Some(&ctx), use_inst, vreg.id)
                        .map(|s| to_oracle(&s));
                    assert_eq!(
                        first, again,
                        "warm-solution instability: case `{}` use {:?} id {}",
                        case.name, use_inst, vreg.id
                    );
                }
            }
        }
    }
}
