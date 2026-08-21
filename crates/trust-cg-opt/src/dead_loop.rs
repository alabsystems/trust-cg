// trust-cg-opt - Dead counted-loop elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Dead counted-loop elimination (`deadloop`).
//!
//! DELETE a natural loop whose body has **no observable effect** and which
//! **provably terminates**, replacing it with a direct edge from the preheader
//! to the loop's unique exit. When the induction variable is live after the
//! loop, its closed-form final value is materialized in the preheader.
//!
//! This is a SOUND, aggressively fail-closed transform: it fires only on loops
//! it can prove are safe to delete and BAILS on everything else. The soundness
//! argument is:
//!
//!  * A finite (terminating) loop whose body performs no store / call / atomic /
//!    memory write and whose defined values are all dead after the loop computes
//!    nothing observable. Deleting it preserves the program's observable
//!    behavior (only its running time changes, which the C abstract machine does
//!    not observe). This is *stronger* than C11's forward-progress license: we
//!    require an actual COUNTED structure (a monotone unit-stride induction
//!    variable tested against a loop-invariant bound), so we never delete a
//!    possibly-infinite loop.
//!
//! # Exact conditions (all required, else BAIL)
//!
//! 1. A natural loop with a **preheader** ([`NaturalLoop::preheader`] is `Some`)
//!    and a **single latch** (one back-edge source). The only entry into the
//!    body is `preheader -> header`.
//! 2. It provably **terminates**: a unit-stride (`+1`) induction variable `iv`
//!    whose sole in-body write is the latch write-back, tested against a
//!    loop-invariant bound by the exit branch. Two shapes are accepted (the same
//!    ones the NEON vectorizers recognize):
//!    * exit-taken `cmp T, bound ; b.<EQ|GE|HS> exit`  (rotated / top-tested),
//!    * continue-taken `cmp T, bound ; b.<LT|LO> header` (bottom-tested),
//!      where `T` is `iv` or `iv+1`. Unit stride + these condition codes give a
//!      finite trip count (`b.EQ`/`b.LT` on a `+1` counter visits `bound` within
//!      `2^bits` iterations; the monotone `>=` / `<` cases cross any fixed bound).
//!
//!    Those trip-count arguments all assume the compare RUNS ONCE PER TRIP and
//!    that a trip is finite, so two structural conditions are also required:
//!    * the exiting block **dominates the latch** — otherwise the exit test sits
//!      on a conditional path, can be skipped forever, and the loop diverges;
//!    * the body is **acyclic once the `latch -> header` back-edge is removed** —
//!      otherwise a nested (or irreducible) cycle can spin without ever reaching
//!      the latch, and the counted IV never advances.
//!
//!    For the same reason the step `iv_next = iv + 1` must be defined INSIDE the
//!    body and dominate the latch. A step computed in the preheader also
//!    dominates the latch, but then `iv = iv_next` writes the same value every
//!    trip and the loop is infinite.
//! 3. **No observable side effect** in ANY body block: every instruction must be
//!    in a conservative pure whitelist AND independently pass the effect-flag /
//!    memory-effect model (no store, no load, no call, no atomic, no barrier, no
//!    implicit defs/uses, no `HAS_SIDE_EFFECTS`).
//! 4. **No value defined in the loop is live-out**, except the induction
//!    variable. A live-out non-IV value (e.g. a reduction result) => BAIL. A
//!    live-out IV is replaced by its CLOSED-FORM final value materialized in the
//!    preheader (only the exactly-computable constant-bounds top-tested shape is
//!    supported; anything else BAILS).
//! 5. **Single exit**: exactly one edge leaves the body. Rewire `preheader ->
//!    exit`, drop the body blocks. Multiple exits => BAIL.
//!
//! The pass iterates to a local fixpoint, so nested dead loops are peeled
//! (deleting the outer loop directly also removes an all-pure nested inner
//! loop). Every uncertainty is resolved by BAILING.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::effects::{
    MemoryEffect, aarch64_for_each_use_position, for_each_inst_def, inst_defines_vreg,
    opcode_effect,
};
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::{AnalysisCache, MachinePass};

// AArch64 condition codes (subset used here).
const CC_EQ: i64 = 0;
const CC_HS: i64 = 2;
const CC_LO: i64 = 3;
const CC_GE: i64 = 10;
const CC_LT: i64 = 11;

/// Safety cap on the internal deletion fixpoint (each deletion strictly shrinks
/// the CFG, so this is only a runaway guard).
const MAX_DELETIONS: usize = 512;

/// The `deadloop` machine pass.
#[derive(Default)]
pub struct DeadCountedLoopElimination {
    /// Number of loops deleted in the last `run` (diagnostics/tests).
    fired: usize,
}

impl DeadCountedLoopElimination {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops deleted in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }

    fn run_impl(
        &mut self,
        func: &mut MachFunction,
        mut cached: Option<&mut AnalysisCache>,
    ) -> bool {
        self.fired = 0;
        let dump = std::env::var("TRUST_CG_DUMP_DEADLOOP").is_ok();
        let mut changed = false;

        // Delete one loop per iteration, recomputing dominance + loop analysis
        // after the CFG surgery (which invalidates them). Deleting the SMALLEST
        // body first peels nested loops cleanly.
        for _ in 0..MAX_DELETIONS {
            // The FIRST scan may reuse the pass manager's shared, CFG-derived
            // analyses (the common case is one scan that finds no dead loop and
            // bails — no CFG surgery). `take()` ensures only the first iteration
            // uses the cache; every later iteration recomputes against the CFG we
            // just mutated. Sound + byte-identical: DomTree/LoopAnalysis depend
            // only on the CFG, which the cache invalidates on any change.
            let (dom, la) = if let Some(cache) = cached.take() {
                (
                    cache.domtree(func).clone(),
                    cache.loop_analysis(func).clone(),
                )
            } else {
                let dom = DomTree::compute(func);
                let la = LoopAnalysis::compute(func, &dom);
                (dom, la)
            };
            if la.is_empty() {
                break;
            }

            let mut loops: Vec<NaturalLoop> = la.all_loops().cloned().collect();
            loops.sort_by_key(|lp| (lp.body.len(), lp.header.0));

            // Whole-function index, built ONCE per scan instead of once per
            // candidate. `recognize` is called for every natural loop until one
            // fires, and it rebuilt this map on each call, so a function with
            // many loops paid O(loops x function) — the dominant term in this
            // pass on block-dense code (many_fns: deadloop 32.1ms -> 127.2ms
            // for a 2x block count, 3.96x).
            //
            // Sound for the whole scan because the scan does not mutate: the
            // FIRST loop that fires applies its plan and immediately `break`s,
            // and the enclosing `loop` then recomputes dom/loop analysis from
            // scratch. Every `recognize` call in one scan therefore sees the
            // same unmutated function this index was built from.
            let maps = Maps::build(func);

            let mut deleted = false;
            for lp in &loops {
                if let Some(plan) = recognize(func, &dom, &maps, lp) {
                    if dump {
                        eprintln!(
                            "[deadloop] FIRE fn={} header={:?} exit={:?} body={} liveout_iv={}",
                            func.name,
                            plan.header,
                            plan.exit,
                            plan.body.len(),
                            plan.liveout.is_some()
                        );
                    }
                    apply(func, &plan);
                    self.fired += 1;
                    changed = true;
                    deleted = true;
                    break;
                }
            }
            if !deleted {
                break;
            }
        }

        if changed && std::env::var("TRUST_CG_DUMP_DEADLOOP").is_ok() {
            eprintln!("[deadloop] fn={} deleted={}", func.name, self.fired);
        }
        changed
    }
}

impl MachinePass for DeadCountedLoopElimination {
    fn name(&self) -> &str {
        "deadloop"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        self.run_impl(func, None)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        // Reuse the shared analyses for the first candidate scan; after any
        // deletion the CFG changes and we recompute internally, as before.
        let changed = self.run_impl(func, Some(&mut *analyses));
        // On a FIRE we deleted loop blocks; drop the shared analyses so no
        // downstream pass reads a stale loop tree. Zero cost in the no-fire path.
        if changed {
            analyses.invalidate();
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognized plan
// ---------------------------------------------------------------------------

/// A live-out induction variable and its exactly-computed closed-form final
/// value, to be materialized in the preheader.
struct LiveOutIv {
    /// The loop-carried IV vreg used after the loop.
    iv: VReg,
    /// The exact constant value the IV holds when the loop finishes.
    final_value: u64,
    /// Register class of the IV.
    rc: RegClass,
}

/// A verified-legal dead loop ready to be deleted. Every field is established by
/// construction in [`recognize`].
struct DeadLoopPlan {
    /// All loop body blocks (to be removed).
    body: Vec<BlockId>,
    /// The preheader (its `-> header` edge is redirected to `exit`).
    preheader: BlockId,
    /// The loop header.
    header: BlockId,
    /// The unique exit block.
    exit: BlockId,
    /// The unique exiting body block (`exiting -> exit`).
    exiting: BlockId,
    /// Present iff the IV is live-out (closed-form final value to materialize).
    liveout: Option<LiveOutIv>,
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// Precomputed def / block lookup tables, built once per [`recognize`] call.
struct Maps {
    /// First (lowest-`InstId`) def per vreg id.
    def_first: HashMap<VReg, InstId>,
    /// Number of defs per vreg id (to detect multi-def, e.g. `Movz;Movk`).
    def_count: HashMap<VReg, u32>,
    /// Block containing each instruction (over `block_order`).
    inst_block: HashMap<InstId, BlockId>,
}

impl Maps {
    fn build(func: &MachFunction) -> Self {
        let mut def_first: HashMap<VReg, InstId> = HashMap::new();
        let mut def_count: HashMap<VReg, u32> = HashMap::new();
        let mut inst_block: HashMap<InstId, BlockId> = HashMap::new();
        for &bid in &func.block_order {
            for &iid in &func.block(bid).insts {
                inst_block.insert(iid, bid);
                let inst = func.inst(iid);
                for_each_inst_def(inst, |v| {
                    def_first.entry(v).or_insert(iid);
                    *def_count.entry(v).or_insert(0) += 1;
                });
            }
        }
        Self {
            def_first,
            def_count,
            inst_block,
        }
    }

    fn def_block(&self, v: VReg) -> Option<BlockId> {
        self.inst_block.get(self.def_first.get(&v)?).copied()
    }
}

fn recognize(
    func: &MachFunction,
    dom: &DomTree,
    maps: &Maps,
    lp: &NaturalLoop,
) -> Option<DeadLoopPlan> {
    let preheader = lp.preheader?;
    let header = lp.header;
    let body = &lp.body;

    if body.is_empty() || body.contains(&preheader) {
        return None;
    }

    // (1) Single latch: exactly one body block branches back to the header.
    let latches: Vec<BlockId> = body
        .iter()
        .copied()
        .filter(|&b| func.block(b).succs.contains(&header))
        .collect();
    if latches.len() != 1 {
        return None;
    }
    let latch = latches[0];

    // (1) The only entry into the body is preheader -> header: the header's
    // non-body predecessors are exactly {preheader}. (Guarantees redirecting the
    // preheader edge removes every path into the loop.)
    {
        let ext_preds: Vec<BlockId> = func
            .block(header)
            .preds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if ext_preds != vec![preheader] {
            return None;
        }
    }
    // The preheader must actually branch to the header (the edge we redirect).
    if !func.block(preheader).succs.contains(&header) {
        return None;
    }

    // (5) Single exit edge: exactly one (body -> non-body) edge in the whole loop.
    let mut exit_edges: Vec<(BlockId, BlockId)> = Vec::new();
    for &b in body {
        for &s in &func.block(b).succs {
            if !body.contains(&s) {
                exit_edges.push((b, s));
            }
        }
    }
    if exit_edges.len() != 1 {
        return None;
    }
    let (exiting, exit) = exit_edges[0];
    if body.contains(&exit) {
        return None;
    }
    // If the exit target IS the preheader (the loop is the inner body of an outer
    // loop whose latch is our preheader), redirecting `preheader -> exit` would
    // splice a bogus self-edge on the preheader. Bail (fail-closed).
    if exit == preheader {
        return None;
    }

    // (2a) The exit test must be evaluated on EVERY trip. `terminating_cc`
    // argues termination from "unit stride + condition code", and every one of
    // those arguments silently assumes the compare runs once per iteration. If
    // the exiting block sits on a CONDITIONAL path inside the body, the test can
    // be skipped forever and the loop never terminates.
    //
    // Requiring `exiting` to dominate `latch` is exactly that guarantee: the
    // body is entry-closed (checked above — the header's only external
    // predecessor is the preheader, and `compute_loop_body` grows backwards from
    // the latch stopping at the header, so no other body block has an outside
    // predecessor). So if some body path `header -> latch` avoided `exiting`,
    // `entry -> preheader -> header -> ... -> latch` would too, contradicting
    // dominance. Hence every `header -> latch` path runs the exit test.
    if !dom.dominates(exiting, latch) {
        return None;
    }

    // (2b) A single trip must be FINITE. The counted-IV argument only bounds the
    // number of times the latch executes; it says nothing about a nested (or
    // irreducible) cycle strictly inside the body, which could spin forever
    // without ever reaching the latch. Require the body to be acyclic once the
    // `latch -> header` back-edge is removed, so every trip is a finite path
    // from the header to the latch or to the exit.
    if !body_acyclic_without_backedge(func, body, latch, header) {
        return None;
    }

    // (3) Every body instruction must be pure and effect-free.
    for &b in body {
        for &iid in &func.block(b).insts {
            if !is_pure_effect_free(func.inst(iid)) {
                return None;
            }
        }
    }

    // `maps` is supplied by the caller, built ONCE per candidate scan.

    // (2) Exit test + induction variable.
    let exit_test = find_exit_test(func, exiting, exit)?;

    // Identify the unit-stride IV from the latch write-backs, tied to the exit
    // test value.
    let iv_info = find_counted_iv(func, dom, &maps, latch, body, &exit_test)?;

    // (2) Bound must be loop-invariant.
    if !is_loop_invariant(func, body, &exit_test.bound) {
        return None;
    }

    // (2) Termination: the condition code must, together with the unit stride,
    // give a finite trip count.
    if !terminating_cc(exit_test.exit_taken, exit_test.cc) {
        return None;
    }

    // (4) Live-out analysis.
    let body_defs = collect_body_defs(func, body);
    let liveouts = collect_liveouts(func, body, &body_defs);

    let liveout = if liveouts.is_empty() {
        None
    } else if liveouts.len() == 1 && liveouts.contains(&iv_info.iv) {
        // The IV is the only live-out value: materialize its closed-form final
        // value. Only the exactly-computable constant-bounds top-tested shape is
        // supported; anything else BAILS (fail-closed).
        Some(materialize_liveout_iv(
            func, &maps, preheader, &iv_info, &exit_test,
        )?)
    } else {
        // A non-IV loop value is live-out (e.g. a reduction result): BAIL.
        return None;
    };

    Some(DeadLoopPlan {
        body: body.iter().copied().collect(),
        preheader,
        header,
        exit,
        exiting,
        liveout,
    })
}

/// The recognized exit test.
struct ExitTest {
    /// Condition code on the exit branch.
    cc: i64,
    /// True when taking the branch LEAVES the loop (`b.cc exit`); false when
    /// taking the branch CONTINUES (`b.cc header`, exit via fall-through).
    exit_taken: bool,
    /// Compared test value (`cmp operand 0`) — must be `iv` or `iv+1`.
    test: VReg,
    /// The loop-invariant bound (`cmp operand 1`).
    bound: BoundOperand,
    /// The `CmpRR`/`CmpRI` instruction id feeding the branch.
    #[allow(dead_code)]
    cmp: InstId,
}

/// The bound operand of the exit compare.
#[derive(Clone)]
enum BoundOperand {
    Reg(VReg),
    Imm(i64),
}

/// Recognize the exit test in `exiting`: `[.., Cmp(T, bound), BCond(cc, t), B(o)]`
/// where `{t, o}` are the block's two successors and one of them is `exit`.
fn find_exit_test(func: &MachFunction, exiting: BlockId, exit: BlockId) -> Option<ExitTest> {
    let insts = &func.block(exiting).insts;
    if insts.len() < 3 {
        return None;
    }
    let last = func.inst(insts[insts.len() - 1]);
    let bcond = func.inst(insts[insts.len() - 2]);
    let cmp_id = insts[insts.len() - 3];
    let cmp = func.inst(cmp_id);

    // Terminator must be exactly `BCond(cc, Block(t)) ; B(Block(o))`.
    if last.opcode != AArch64Opcode::B || bcond.opcode != AArch64Opcode::BCond {
        return None;
    }
    let branch_target = block_operand(last)?; // fall-through target `o`
    let cc = imm_of(&bcond.operands[0])?;
    let cond_target = bcond.operands.iter().find_map(|op| {
        if let MachOperand::Block(b) = op {
            Some(*b)
        } else {
            None
        }
    })?; // `t`

    // Exactly one of {cond_target, branch_target} is the exit.
    let exit_taken = if cond_target == exit && branch_target != exit {
        true
    } else if branch_target == exit && cond_target != exit {
        false
    } else {
        return None;
    };

    // Flag producer must be the immediately-preceding CmpRR/CmpRI.
    let (test, bound) = match cmp.opcode {
        AArch64Opcode::CmpRR => (
            vreg_of(&cmp.operands[0])?,
            BoundOperand::Reg(vreg_of(&cmp.operands[1])?),
        ),
        AArch64Opcode::CmpRI => (
            vreg_of(&cmp.operands[0])?,
            BoundOperand::Imm(imm_of(&cmp.operands[1])?),
        ),
        _ => return None,
    };

    Some(ExitTest {
        cc,
        exit_taken,
        test,
        bound,
        cmp: cmp_id,
    })
}

/// The recognized induction variable.
struct IvInfo {
    /// The loop-carried IV (written in the preheader init and the latch write-back).
    iv: VReg,
    /// True when the exit test compares `iv+1` (rotated); false when it compares
    /// `iv` directly (top-/bottom-tested on the carried value).
    #[allow(dead_code)]
    test_is_next: bool,
}

/// Find a unit-stride IV among the latch write-backs whose value the exit test
/// compares. Requires: a copy `iv <- iv_next` in the latch (the IV's sole in-body
/// definition), `iv_next = iv + 1`, `iv_next`'s def dominates the latch, and the
/// exit test compares `iv` or `iv_next`.
fn find_counted_iv(
    func: &MachFunction,
    dom: &DomTree,
    maps: &Maps,
    latch: BlockId,
    body: &HashSet<BlockId>,
    exit_test: &ExitTest,
) -> Option<IvInfo> {
    for &iid in &func.block(latch).insts {
        let Some((dst, src)) = copy_like(func.inst(iid)) else {
            continue;
        };
        let iv = dst;
        let iv_next = src;
        if iv == iv_next {
            continue;
        }
        // `iv_next = iv + 1`.
        if !is_step_one(func, maps, iv_next, iv) {
            continue;
        }
        // `iv`'s ONLY in-body definition is this latch write-back (so it is
        // incremented exactly once per iteration).
        if count_body_defs(func, body, iv) != 1 {
            continue;
        }
        // `iv_next` must be single-def (SSA), and its def dominates the latch, so
        // the write-back always sees exactly `iv + 1`.
        if maps.def_count.get(&iv_next).copied() != Some(1) {
            continue;
        }
        let Some(next_block) = maps.def_block(iv_next) else {
            continue;
        };
        // The step must be RECOMPUTED every trip: its def must live INSIDE the
        // loop body and dominate the latch. Dominance alone is not enough — a
        // preheader `iv_next = iv + 1` also dominates the latch, but then the
        // latch write-back `iv = iv_next` stores the same value on every trip,
        // so `iv` is constant from iteration 1 on and the loop never terminates.
        if !body.contains(&next_block) {
            continue;
        }
        if !dom.dominates(next_block, latch) {
            continue;
        }
        // The exit test must compare this IV (directly or as iv+1).
        let test_is_next = if exit_test.test == iv {
            false
        } else if exit_test.test == iv_next {
            true
        } else {
            continue;
        };
        return Some(IvInfo { iv, test_is_next });
    }
    None
}

/// True iff the loop body contains NO cycle other than the `latch -> header`
/// back-edge, i.e. one trip of the loop is a finite path.
///
/// Detects cycles by dominator-free colouring (white/grey/black DFS) rather than
/// by looking for back-edges in the dominator tree, so an IRREDUCIBLE cycle
/// inside the body — which has no dominator back-edge and which `LoopAnalysis`
/// therefore never reports as a loop — is caught too. Fail-closed.
fn body_acyclic_without_backedge(
    func: &MachFunction,
    body: &HashSet<BlockId>,
    latch: BlockId,
    header: BlockId,
) -> bool {
    #[derive(Clone, Copy, PartialEq)]
    enum Color {
        White,
        Grey,
        Black,
    }
    let mut color: HashMap<BlockId, Color> = body.iter().map(|&b| (b, Color::White)).collect();
    // Iterative DFS: the stack holds (block, index of next successor to visit).
    let mut stack: Vec<(BlockId, usize)> = Vec::new();
    for &start in body {
        if color.get(&start) != Some(&Color::White) {
            continue;
        }
        color.insert(start, Color::Grey);
        stack.push((start, 0));
        while let Some((b, idx)) = stack.pop() {
            let succs = &func.block(b).succs;
            if idx >= succs.len() {
                color.insert(b, Color::Black);
                continue;
            }
            let s = succs[idx];
            stack.push((b, idx + 1));
            // Leave the body / take the loop's own back-edge: not a body cycle.
            if !body.contains(&s) || (b == latch && s == header) {
                continue;
            }
            match color.get(&s) {
                Some(Color::Grey) => return false, // cycle strictly inside the body
                Some(Color::White) => {
                    color.insert(s, Color::Grey);
                    stack.push((s, 0));
                }
                _ => {}
            }
        }
    }
    true
}

/// Unit-stride + condition-code combinations that give a finite trip count.
fn terminating_cc(exit_taken: bool, cc: i64) -> bool {
    if exit_taken {
        // exit when `T <cc> bound`. `+1` stride:
        //   EQ:  visits `bound` within 2^bits iterations.
        //   GE/HS: monotone increase crosses any fixed bound.
        cc == CC_EQ || cc == CC_GE || cc == CC_HS
    } else {
        // continue when `T <cc> bound` (exit otherwise). `+1` stride:
        //   LT/LO: exit when `T >= bound`, reached by the monotone increase.
        cc == CC_LT || cc == CC_LO
    }
}

/// Materialize the closed-form final value of a live-out IV. Supported ONLY for
/// the exactly-computable shape: an exit-taken top test (`b.<GE|HS> exit`) on the
/// carried `iv` (not `iv+1`) with compile-time-constant start and bound. Then the
/// final value is `(start <cc bound) ? bound : start`, exact for the top-tested
/// loop (0 trips => `start`, else the first `iv >= bound` which `+1` reaches
/// exactly = `bound`). Anything else BAILS.
fn materialize_liveout_iv(
    func: &MachFunction,
    maps: &Maps,
    preheader: BlockId,
    iv_info: &IvInfo,
    exit_test: &ExitTest,
) -> Option<LiveOutIv> {
    // Only the top-tested, exit-taken shape whose compare reads the carried IV
    // directly (not `iv+1`).
    if !exit_test.exit_taken || exit_test.test != iv_info.iv {
        return None;
    }
    if !(exit_test.cc == CC_GE || exit_test.cc == CC_HS) {
        return None;
    }
    let unsigned = exit_test.cc == CC_HS;

    // Start: the IV's initializer in the preheader, as a constant.
    let start = const_iv_init(func, maps, preheader, iv_info.iv)? as u64;
    // Bound: a compile-time constant.
    let bound = match &exit_test.bound {
        BoundOperand::Imm(v) => *v as u64,
        BoundOperand::Reg(v) => resolve_const(func, maps, *v)? as u64,
    };

    let takes = if unsigned {
        start < bound
    } else {
        (start as i64) < (bound as i64)
    };
    let final_value = if takes { bound } else { start };

    Some(LiveOutIv {
        iv: iv_info.iv,
        final_value,
        rc: iv_info.iv.class,
    })
}

// ---------------------------------------------------------------------------
// Transformation
// ---------------------------------------------------------------------------

fn apply(func: &mut MachFunction, plan: &DeadLoopPlan) {
    // 1. Materialize a live-out IV's final value in the preheader and rewire its
    //    post-loop uses BEFORE any CFG surgery.
    if let Some(lo) = &plan.liveout {
        let final_reg = materialize_const(func, plan.preheader, lo.final_value, lo.rc);
        rewrite_external_uses(func, &plan.body, lo.iv, final_reg);
    }

    let body: HashSet<BlockId> = plan.body.iter().copied().collect();

    // 2. Redirect the preheader's `-> header` branch edge to `-> exit`. The only
    //    block-referencing instructions in a preheader are its terminating
    //    branches, so retargeting every `Block(header)` operand redirects exactly
    //    the entry edge.
    let ph_insts = func.block(plan.preheader).insts.clone();
    for iid in ph_insts {
        for op in func.inst_mut(iid).operands.iter_mut() {
            if let MachOperand::Block(b) = op
                && *b == plan.header
            {
                *b = plan.exit;
            }
        }
    }

    // 3. CFG edge surgery.
    //    preheader.succs: header -> exit (dedup).
    replace_succ(func, plan.preheader, plan.header, plan.exit);
    //    exit.preds: drop the exiting body block, add the preheader.
    func.block_mut(plan.exit)
        .preds
        .retain(|&p| p != plan.exiting);
    if !func.block(plan.exit).preds.contains(&plan.preheader) {
        func.block_mut(plan.exit).preds.push(plan.preheader);
    }

    // 4. Remove every body block: clear its contents and drop it from the layout.
    for &b in &plan.body {
        let blk = func.block_mut(b);
        blk.insts.clear();
        blk.preds.clear();
        blk.succs.clear();
    }
    func.block_order.retain(|b| !body.contains(b));

    // 5. Defensively scrub any dangling references to deleted blocks.
    for &b in &func.block_order.clone() {
        func.block_mut(b).preds.retain(|p| !body.contains(p));
        func.block_mut(b).succs.retain(|s| !body.contains(s));
    }
}

/// Replace `old` with `new` in `block`'s successor list (dedup: if `new` already
/// present, just remove `old`).
fn replace_succ(func: &mut MachFunction, block: BlockId, old: BlockId, new: BlockId) {
    let succs = &mut func.block_mut(block).succs;
    let has_new = succs.contains(&new);
    if has_new {
        succs.retain(|&s| s != old);
    } else {
        for s in succs.iter_mut() {
            if *s == old {
                *s = new;
            }
        }
    }
}

/// Rewrite every USE of `old` outside the loop body to `new`.
fn rewrite_external_uses(func: &mut MachFunction, body: &[BlockId], old: VReg, new: VReg) {
    let body_set: HashSet<BlockId> = body.iter().copied().collect();
    let blocks: Vec<BlockId> = func.block_order.clone();
    for bid in blocks {
        if body_set.contains(&bid) {
            continue;
        }
        let inst_ids: Vec<InstId> = func.block(bid).insts.clone();
        for iid in inst_ids {
            let inst = func.inst_mut(iid);
            let opcode = inst.opcode;
            let operand_count = inst.operands.len();
            aarch64_for_each_use_position(opcode, operand_count, |pos| {
                if inst.operands.get(pos).and_then(MachOperand::as_vreg) == Some(old) {
                    inst.operands[pos] = MachOperand::VReg(new);
                }
            });
        }
    }
}

/// Materialize a 64/32-bit constant into the preheader (before its terminator)
/// with a `Movz` (+ `Movk` chain for wider values). Returns the destination vreg.
fn materialize_const(
    func: &mut MachFunction,
    preheader: BlockId,
    value: u64,
    rc: RegClass,
) -> VReg {
    let dst = VReg::new(func.alloc_vreg(), rc);
    let lo = (value & 0xFFFF) as i64;
    let movz = func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(dst), MachOperand::Imm(lo)],
    ));
    insert_before_terminator(func, preheader, movz);
    for shift in [16u32, 32, 48] {
        let chunk = ((value >> shift) & 0xFFFF) as i64;
        if chunk != 0 {
            let movk = func.push_inst(MachInst::new(
                AArch64Opcode::Movk,
                vec![
                    MachOperand::VReg(dst),
                    MachOperand::Imm(chunk),
                    MachOperand::Imm(shift as i64),
                ],
            ));
            insert_before_terminator(func, preheader, movk);
        }
    }
    dst
}

fn insert_before_terminator(func: &mut MachFunction, block: BlockId, inst_id: InstId) {
    let block_insts = &func.block(block).insts;
    if block_insts.is_empty() {
        func.block_mut(block).insts.push(inst_id);
        return;
    }
    let last = block_insts[block_insts.len() - 1];
    let flags = func.inst(last).flags;
    let is_term = flags.is_terminator() || flags.is_branch();
    let block_data = func.block_mut(block);
    if is_term {
        let pos = block_data.insts.len() - 1;
        block_data.insts.insert(pos, inst_id);
    } else {
        block_data.insts.push(inst_id);
    }
}

// ---------------------------------------------------------------------------
// Purity model
// ---------------------------------------------------------------------------

/// A conservative whitelist of opcodes permitted in a deletable loop body. ANY
/// opcode outside this set BAILS (rules out stores, loads, calls, atomics,
/// barriers, division, and every unmodeled effect). Every entry is additionally
/// re-checked against the effect-flag / memory-effect model in
/// [`is_pure_effect_free`], so a whitelist mistake cannot admit an effectful op.
fn allowed_body_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        // arithmetic
        AddRR | AddRI | SubRR | SubRI | MulRR | Madd | Msub | Neg | Umulh | Smulh
        // bitwise
        | AndRR | AndRI | OrrRR | OrrRI | EorRR | EorRI | BicRR | OrnRR
        // shifts / bitfield
        | LslRR | LsrRR | AsrRR | LslRI | LsrRI | AsrRI | RorRI | Rbit | Ubfm | Sbfm | Bfm
        // moves / constants
        | MovR | Copy | Movz | Movn | Movk | Nop
        // extends
        | Sxtw | Uxtw | Sxtb | Sxth | Uxtb | Uxth
        // compare / select
        | CmpRR | CmpRI | Tst | CSet | Csel | Csinc | Csinv | Csneg
        // branches (control flow inside the body)
        | B | BCond | Cbz | Cbnz | Tbz | Tbnz
    )
}

/// A body instruction is safe to delete iff it is in the whitelist AND the
/// memory-effect model agrees it is pure (no store/load/call/atomic/barrier) AND
/// it touches no memory and calls nothing AND it clobbers no implicit registers.
///
/// Note: `has_side_effects()` is deliberately NOT consulted. Flag-writing
/// compares (`CmpRR`/`CmpRI`/`Tst`) and the flag-setting arithmetic
/// (`AddsRR`/`SubsRR`/...) carry `HAS_SIDE_EFFECTS` only because they write NZCV
/// — a register-like effect consumed locally by the loop's own branch, dead once
/// the loop is deleted and never observable. The whitelist keeps genuinely
/// effectful `HAS_SIDE_EFFECTS` opcodes (traps, `Brk`, barriers, `StackAlloc`)
/// OUT (they are absent from the whitelist and/or are non-`Pure` in the memory
/// model), so admitting the pure flag-writers here is sound.
fn is_pure_effect_free(inst: &MachInst) -> bool {
    allowed_body_op(inst.opcode)
        && opcode_effect(inst.opcode) == MemoryEffect::Pure
        && !inst.writes_memory()
        && !inst.reads_memory()
        && !inst.is_call()
        && inst.implicit_defs.is_empty()
        && inst.implicit_uses.is_empty()
}

// ---------------------------------------------------------------------------
// Small helpers (mirrors of the NEON recognizers' utilities)
// ---------------------------------------------------------------------------

fn vreg_of(op: &MachOperand) -> Option<VReg> {
    op.as_vreg()
}

fn imm_of(op: &MachOperand) -> Option<i64> {
    op.as_imm()
}

fn block_operand(inst: &MachInst) -> Option<BlockId> {
    inst.operands.iter().find_map(|op| match op {
        MachOperand::Block(b) => Some(*b),
        _ => None,
    })
}

/// `MovR(d, s)` / `Copy(d, s)` / `AddRI(d, s, 0)` copy idioms => `(d, s)`.
fn copy_like(inst: &MachInst) -> Option<(VReg, VReg)> {
    match inst.opcode {
        AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => {
            Some((vreg_of(&inst.operands[0])?, vreg_of(&inst.operands[1])?))
        }
        AArch64Opcode::AddRI
            if inst.operands.len() == 3 && imm_of(&inst.operands[2]) == Some(0) =>
        {
            Some((vreg_of(&inst.operands[0])?, vreg_of(&inst.operands[1])?))
        }
        _ => None,
    }
}

/// `iv_next == iv + 1` (via `AddRI(iv, 1)` or `AddRR(iv, const-1)`).
fn is_step_one(func: &MachFunction, maps: &Maps, iv_next: VReg, iv: VReg) -> bool {
    let Some(&id) = maps.def_first.get(&iv_next) else {
        return false;
    };
    let inst = func.inst(id);
    match inst.opcode {
        AArch64Opcode::AddRI => {
            inst.operands.len() == 3
                && vreg_of(&inst.operands[1]) == Some(iv)
                && imm_of(&inst.operands[2]) == Some(1)
        }
        AArch64Opcode::AddRR => {
            if inst.operands.len() != 3 {
                return false;
            }
            let a = vreg_of(&inst.operands[1]);
            let b = vreg_of(&inst.operands[2]);
            (a == Some(iv) && b.and_then(|v| resolve_const(func, maps, v)) == Some(1))
                || (b == Some(iv) && a.and_then(|v| resolve_const(func, maps, v)) == Some(1))
        }
        _ => false,
    }
}

/// Resolve a vreg to a compile-time constant by following a SINGLE-DEF
/// `Movz` / `MovR` / `Copy` / `AddRI(_, 0)` chain. Multi-def vregs (e.g. a
/// `Movz;Movk` pair, whose exact value is not recoverable from a single-slot def
/// map) return `None` — fail-closed. Used where the *exact value* matters.
fn resolve_const(func: &MachFunction, maps: &Maps, v: VReg) -> Option<i64> {
    let mut cur = v;
    for _ in 0..16 {
        if maps.def_count.get(&cur).copied() != Some(1) {
            return None;
        }
        let inst = func.inst(*maps.def_first.get(&cur)?);
        match inst.opcode {
            AArch64Opcode::Movz => {
                let (dst, value) = crate::reaching_const::movz_value(inst)?;
                if dst != cur {
                    return None;
                }
                return i64::try_from(value).ok();
            }
            AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => {
                cur = vreg_of(&inst.operands[1])?;
            }
            AArch64Opcode::AddRI
                if inst.operands.len() == 3 && imm_of(&inst.operands[2]) == Some(0) =>
            {
                cur = vreg_of(&inst.operands[1])?;
            }
            _ => return None,
        }
    }
    None
}

/// The IV's constant initializer, taken from its definition IN the preheader.
fn const_iv_init(func: &MachFunction, maps: &Maps, preheader: BlockId, iv: VReg) -> Option<i64> {
    // Find iv's (last) definition within the preheader block, then resolve it.
    for &iid in func.block(preheader).insts.iter().rev() {
        let inst = func.inst(iid);
        if inst_defines_vreg(inst, iv) {
            return match inst.opcode {
                AArch64Opcode::Movz => {
                    let (dst, value) = crate::reaching_const::movz_value(inst)?;
                    if dst != iv {
                        return None;
                    }
                    i64::try_from(value).ok()
                }
                AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => {
                    resolve_const(func, maps, vreg_of(&inst.operands[1])?)
                }
                _ => None,
            };
        }
    }
    None
}

/// A bound operand is loop-invariant iff it is an immediate, a value defined
/// entirely outside the loop body, or a materialized compile-time constant
/// (`Movz`/`Movk`/`Movn` chain — invariant even if recomputed inside the body).
fn is_loop_invariant(func: &MachFunction, body: &HashSet<BlockId>, bound: &BoundOperand) -> bool {
    match bound {
        BoundOperand::Imm(_) => true,
        BoundOperand::Reg(v) => {
            // Defined entirely outside the loop body?
            let mut any = false;
            let mut all_outside = true;
            for &bid in &func.block_order {
                let in_body = body.contains(&bid);
                for &iid in &func.block(bid).insts {
                    let inst = func.inst(iid);
                    if inst_defines_vreg(inst, *v) {
                        any = true;
                        if in_body {
                            all_outside = false;
                        }
                    }
                }
            }
            if any && all_outside {
                return true;
            }
            // Otherwise it must be a materialized constant.
            is_materialized_constant(func, *v)
        }
    }
}

/// True iff EVERY definition of `v` is a `Movz`/`Movk`/`Movn` with immediate
/// operands (so `v` holds a compile-time constant, hence is loop-invariant).
fn is_materialized_constant(func: &MachFunction, v: VReg) -> bool {
    let mut any = false;
    let mut any_base = false;
    for &bid in &func.block_order {
        for &iid in &func.block(bid).insts {
            let inst = func.inst(iid);
            if !inst_defines_vreg(inst, v) {
                continue;
            }
            any = true;
            let ok = match inst.opcode {
                AArch64Opcode::Movz => {
                    let valid =
                        crate::reaching_const::movz_value(inst).is_some_and(|(dst, _)| dst == v);
                    any_base |= valid;
                    valid
                }
                AArch64Opcode::Movn => {
                    let valid =
                        crate::reaching_const::movn_value(inst).is_some_and(|(dst, _)| dst == v);
                    any_base |= valid;
                    valid
                }
                AArch64Opcode::Movk => crate::reaching_const::parse_move_wide_inst(inst)
                    .is_some_and(|(dst, _, _)| dst == v),
                _ => false,
            };
            if !ok {
                return false;
            }
        }
    }
    any && any_base
}

/// Count `v`'s definitions inside the loop body.
fn count_body_defs(func: &MachFunction, body: &HashSet<BlockId>, v: VReg) -> usize {
    let mut n = 0;
    for &b in body {
        for &iid in &func.block(b).insts {
            let inst = func.inst(iid);
            if inst_defines_vreg(inst, v) {
                n += 1;
            }
        }
    }
    n
}

/// All vregs defined inside the loop body.
fn collect_body_defs(func: &MachFunction, body: &HashSet<BlockId>) -> HashSet<VReg> {
    let mut defs = HashSet::new();
    for &b in body {
        for &iid in &func.block(b).insts {
            let inst = func.inst(iid);
            for_each_inst_def(inst, |v| {
                defs.insert(v);
            });
        }
    }
    defs
}

/// Body-defined vregs that are USED outside the loop body (live-out).
fn collect_liveouts(
    func: &MachFunction,
    body: &HashSet<BlockId>,
    body_defs: &HashSet<VReg>,
) -> HashSet<VReg> {
    let mut liveouts = HashSet::new();
    for &b in &func.block_order {
        if body.contains(&b) {
            continue;
        }
        for &iid in &func.block(b).insts {
            let inst = func.inst(iid);
            aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                if let Some(v) = inst.operands.get(pos).and_then(MachOperand::as_vreg)
                    && body_defs.contains(&v)
                {
                    liveouts.insert(v);
                }
            });
        }
    }
    liveouts
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{MachInst, Signature};

    fn g64(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }
    fn vr(v: VReg) -> MachOperand {
        MachOperand::VReg(v)
    }
    fn imm(v: i64) -> MachOperand {
        MachOperand::Imm(v)
    }
    fn blk(b: BlockId) -> MachOperand {
        MachOperand::Block(b)
    }

    fn new_func() -> MachFunction {
        MachFunction::new("dead_loop_test".to_string(), Signature::new(vec![], vec![]))
    }

    fn push(func: &mut MachFunction, block: BlockId, op: AArch64Opcode, ops: Vec<MachOperand>) {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(block, id);
    }

    /// A ROTATED empty counted loop `for (iv=0; iv+1!=bound; )` with a dead IV.
    ///
    /// ```text
    ///   bb0 (preheader): iv0=0 ; iv=iv0 ; bound=10 ; B bb1
    ///   bb1 (header):    iv1=iv+1 ; cmp iv1,bound ; b.eq bb3 ; B bb2
    ///   bb2 (latch):     iv=iv1 ; B bb1
    ///   bb3 (exit):      ret
    /// ```
    fn make_rotated_empty_loop() -> (MachFunction, BlockId, BlockId, BlockId, BlockId) {
        use AArch64Opcode::*;
        let mut func = new_func();
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let (iv0, iv, bound, one, iv1) = (g64(0), g64(1), g64(2), g64(3), g64(4));

        push(&mut func, bb0, Movz, vec![vr(iv0), imm(0)]);
        push(&mut func, bb0, MovR, vec![vr(iv), vr(iv0)]);
        push(&mut func, bb0, Movz, vec![vr(bound), imm(10)]);
        push(&mut func, bb0, Movz, vec![vr(one), imm(1)]);
        push(&mut func, bb0, B, vec![blk(bb1)]);

        push(&mut func, bb1, AddRR, vec![vr(iv1), vr(iv), vr(one)]);
        push(&mut func, bb1, CmpRR, vec![vr(iv1), vr(bound)]);
        push(&mut func, bb1, BCond, vec![imm(CC_EQ), blk(bb3)]);
        push(&mut func, bb1, B, vec![blk(bb2)]);

        push(&mut func, bb2, MovR, vec![vr(iv), vr(iv1)]);
        push(&mut func, bb2, B, vec![blk(bb1)]);

        push(&mut func, bb3, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb3);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb1);

        (func, bb0, bb1, bb2, bb3)
    }

    #[test]
    fn deletes_empty_counted_loop() {
        let (mut func, bb0, bb1, bb2, bb3) = make_rotated_empty_loop();
        let mut pass = DeadCountedLoopElimination::new();
        let changed = pass.run(&mut func);

        assert!(changed, "the empty counted loop must be deleted");
        assert_eq!(pass.fired(), 1);
        // Body blocks are gone from the layout ...
        assert!(!func.block_order.contains(&bb1));
        assert!(!func.block_order.contains(&bb2));
        // ... preheader now branches straight to the exit ...
        assert_eq!(func.block(bb0).succs, vec![bb3]);
        assert!(func.block(bb3).preds.contains(&bb0));
        // ... and the preheader terminator targets the exit.
        let term = *func.block(bb0).insts.last().unwrap();
        assert!(
            func.inst(term)
                .operands
                .iter()
                .any(|o| matches!(o, MachOperand::Block(b) if *b == bb3))
        );
    }

    #[test]
    fn does_not_delete_loop_with_store() {
        use AArch64Opcode::*;
        let (mut func, _bb0, bb1, _bb2, _bb3) = make_rotated_empty_loop();
        // Inject a store into the latch: now the body has an observable effect.
        let store = func.push_inst(MachInst::new(StrRI, vec![vr(g64(1)), vr(g64(1)), imm(0)]));
        // Insert before the latch terminator (bb2's `B bb1`).
        let bb2 = _bb2;
        let pos = func.block(bb2).insts.len() - 1;
        func.block_mut(bb2).insts.insert(pos, store);

        let mut pass = DeadCountedLoopElimination::new();
        let changed = pass.run(&mut func);

        assert!(!changed, "a loop with a store must NOT be deleted");
        assert_eq!(pass.fired(), 0);
        assert!(func.block_order.contains(&bb1));
    }

    #[test]
    fn does_not_delete_loop_with_non_iv_liveout() {
        use AArch64Opcode::*;
        let (mut func, _bb0, bb1, bb2, bb3) = make_rotated_empty_loop();
        // Add an accumulator `sum` written in the latch and READ after the loop
        // (a reduction result live-out) — must block deletion.
        let sum = g64(9);
        let sum_next = g64(10);
        // Insert `sum_next = sum + iv1` before the latch terminator.
        let acc = func.push_inst(MachInst::new(
            AddRR,
            vec![vr(sum_next), vr(sum), vr(g64(4))],
        ));
        let wb = func.push_inst(MachInst::new(MovR, vec![vr(sum), vr(sum_next)]));
        let pos = func.block(bb2).insts.len() - 1;
        func.block_mut(bb2).insts.insert(pos, acc);
        func.block_mut(bb2).insts.insert(pos + 1, wb);
        // Read `sum` in the exit block.
        push(&mut func, bb3, MovR, vec![vr(g64(11)), vr(sum)]);

        let mut pass = DeadCountedLoopElimination::new();
        let changed = pass.run(&mut func);

        assert!(!changed, "a non-IV live-out value must block deletion");
        assert!(func.block_order.contains(&bb1));
    }

    #[test]
    fn does_not_delete_unbounded_loop() {
        use AArch64Opcode::*;
        // `while (1) {}` — an infinite self-loop with NO exit edge.
        let mut func = new_func();
        let bb0 = func.entry;
        let bb1 = func.create_block();
        push(&mut func, bb0, Movz, vec![vr(g64(0)), imm(0)]);
        push(&mut func, bb0, B, vec![blk(bb1)]);
        push(
            &mut func,
            bb1,
            AddRR,
            vec![vr(g64(1)), vr(g64(0)), vr(g64(0))],
        );
        push(&mut func, bb1, B, vec![blk(bb1)]);
        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb1);

        let mut pass = DeadCountedLoopElimination::new();
        let changed = pass.run(&mut func);

        assert!(!changed, "an unbounded (no-exit) loop must NOT be deleted");
        assert!(func.block_order.contains(&bb1));
    }

    #[test]
    fn does_not_delete_non_unit_stride_loop() {
        use AArch64Opcode::*;
        // Same rotated shape but stride +2 (`iv1 = iv + 2`): not provably a unit
        // counted loop under our rule -> BAIL (fail-closed).
        let (mut func, _bb0, bb1, _bb2, _bb3) = make_rotated_empty_loop();
        // Rewrite the increment constant `one` (Movz g64(3), #1) to #2.
        for &bid in &func.block_order.clone() {
            for &iid in &func.block(bid).insts.clone() {
                let inst = func.inst(iid);
                if inst.opcode == Movz
                    && matches!(inst.operands.first(), Some(MachOperand::VReg(v)) if *v == g64(3))
                {
                    func.inst_mut(iid).operands[1] = imm(2);
                }
            }
        }
        let mut pass = DeadCountedLoopElimination::new();
        let changed = pass.run(&mut func);
        assert!(!changed, "a non-unit-stride loop must NOT be deleted");
        assert!(func.block_order.contains(&bb1));
    }

    /// AUDIT REPRO: the single exiting block sits on a CONDITIONAL path, so the
    /// exit test is NOT evaluated on every trip. With `cond != 0` the loop never
    /// reaches bb3 and runs forever — it must NOT be deleted.
    ///
    /// ```text
    ///   bb0 (preheader): iv=0 ; bound=10 ; one=1 ; cond=1 ; B bb1
    ///   bb1 (header):    cbnz cond, bb2 ; B bb3
    ///   bb2:             B bb4
    ///   bb3:             cmp iv,bound ; b.ge bb5 ; B bb4
    ///   bb4 (latch):     iv1=iv+one ; iv=iv1 ; B bb1
    ///   bb5 (exit):      ret
    /// ```
    #[test]
    fn audit_guarded_exit_test_loop() {
        use AArch64Opcode::*;
        let mut func = new_func();
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();
        let bb5 = func.create_block();
        let (iv0, iv, bound, one, iv1, cond) = (g64(0), g64(1), g64(2), g64(3), g64(4), g64(5));

        push(&mut func, bb0, Movz, vec![vr(iv0), imm(0)]);
        push(&mut func, bb0, MovR, vec![vr(iv), vr(iv0)]);
        push(&mut func, bb0, Movz, vec![vr(bound), imm(10)]);
        push(&mut func, bb0, Movz, vec![vr(one), imm(1)]);
        push(&mut func, bb0, Movz, vec![vr(cond), imm(1)]);
        push(&mut func, bb0, B, vec![blk(bb1)]);

        push(&mut func, bb1, Cbnz, vec![vr(cond), blk(bb2)]);
        push(&mut func, bb1, B, vec![blk(bb3)]);

        push(&mut func, bb2, B, vec![blk(bb4)]);

        push(&mut func, bb3, CmpRR, vec![vr(iv), vr(bound)]);
        push(&mut func, bb3, BCond, vec![imm(CC_GE), blk(bb5)]);
        push(&mut func, bb3, B, vec![blk(bb4)]);

        push(&mut func, bb4, AddRR, vec![vr(iv1), vr(iv), vr(one)]);
        push(&mut func, bb4, MovR, vec![vr(iv), vr(iv1)]);
        push(&mut func, bb4, B, vec![blk(bb1)]);

        push(&mut func, bb5, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb4);
        func.add_edge(bb3, bb5);
        func.add_edge(bb3, bb4);
        func.add_edge(bb4, bb1);

        let mut pass = DeadCountedLoopElimination::new();
        let changed = pass.run(&mut func);
        eprintln!(
            "AUDIT deadloop guarded-exit: changed={} fired={}",
            changed,
            pass.fired()
        );
        assert!(
            !changed,
            "a loop whose exit test is not evaluated every iteration may be \
             infinite and must NOT be deleted"
        );
        assert!(func.block_order.contains(&bb1));
    }

    /// AUDIT REPRO (variant 2): `iv_next = iv + 1` is computed ONCE in the
    /// PREHEADER; the latch write-back `iv = iv_next` therefore makes `iv`
    /// constant from iteration 1 on. `find_counted_iv` only requires
    /// `iv_next`'s def to DOMINATE the latch, so this passes as "unit stride"
    /// while the loop is in fact infinite.
    ///
    /// ```text
    ///   bb0 (preheader): iv=0 ; bound=10 ; one=1 ; iv1=iv+one ; B bb1
    ///   bb1 (header):    cmp iv,bound ; b.ge bb3 ; B bb2
    ///   bb2 (latch):     iv=iv1 ; B bb1
    ///   bb3 (exit):      ret
    /// ```
    #[test]
    fn audit_loop_invariant_iv_step() {
        use AArch64Opcode::*;
        let mut func = new_func();
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let (iv0, iv, bound, one, iv1) = (g64(0), g64(1), g64(2), g64(3), g64(4));

        push(&mut func, bb0, Movz, vec![vr(iv0), imm(0)]);
        push(&mut func, bb0, MovR, vec![vr(iv), vr(iv0)]);
        push(&mut func, bb0, Movz, vec![vr(bound), imm(10)]);
        push(&mut func, bb0, Movz, vec![vr(one), imm(1)]);
        push(&mut func, bb0, AddRR, vec![vr(iv1), vr(iv), vr(one)]);
        push(&mut func, bb0, B, vec![blk(bb1)]);

        push(&mut func, bb1, CmpRR, vec![vr(iv), vr(bound)]);
        push(&mut func, bb1, BCond, vec![imm(CC_GE), blk(bb3)]);
        push(&mut func, bb1, B, vec![blk(bb2)]);

        push(&mut func, bb2, MovR, vec![vr(iv), vr(iv1)]);
        push(&mut func, bb2, B, vec![blk(bb1)]);

        push(&mut func, bb3, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb3);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb1);

        let mut pass = DeadCountedLoopElimination::new();
        let changed = pass.run(&mut func);
        eprintln!(
            "AUDIT deadloop invariant-step: changed={} fired={}",
            changed,
            pass.fired()
        );
        assert!(
            !changed,
            "an IV whose step is computed OUTSIDE the loop is not a unit-stride \
             counted IV; the loop is infinite and must NOT be deleted"
        );
        assert!(func.block_order.contains(&bb1));
    }

    /// AUDIT REPRO (variant 3): the exit test IS on every path to the latch, but
    /// a nested pure cycle sits between the header and the latch. One trip can
    /// spin forever inside it, so the counted-IV argument proves nothing.
    ///
    /// ```text
    ///   bb0 (preheader): iv=0 ; bound=10 ; one=1 ; cond=1 ; B bb1
    ///   bb1 (header):    cmp iv,bound ; b.ge bb4(exit) ; B bb2
    ///   bb2:             cbnz cond, bb2 ; B bb3      <-- inner infinite cycle
    ///   bb3 (latch):     iv1=iv+one ; iv=iv1 ; B bb1
    ///   bb4 (exit):      ret
    /// ```
    #[test]
    fn audit_nested_cycle_in_body() {
        use AArch64Opcode::*;
        let mut func = new_func();
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();
        let (iv0, iv, bound, one, iv1, cond) = (g64(0), g64(1), g64(2), g64(3), g64(4), g64(5));

        push(&mut func, bb0, Movz, vec![vr(iv0), imm(0)]);
        push(&mut func, bb0, MovR, vec![vr(iv), vr(iv0)]);
        push(&mut func, bb0, Movz, vec![vr(bound), imm(10)]);
        push(&mut func, bb0, Movz, vec![vr(one), imm(1)]);
        push(&mut func, bb0, Movz, vec![vr(cond), imm(1)]);
        push(&mut func, bb0, B, vec![blk(bb1)]);

        push(&mut func, bb1, CmpRR, vec![vr(iv), vr(bound)]);
        push(&mut func, bb1, BCond, vec![imm(CC_GE), blk(bb4)]);
        push(&mut func, bb1, B, vec![blk(bb2)]);

        push(&mut func, bb2, Cbnz, vec![vr(cond), blk(bb2)]);
        push(&mut func, bb2, B, vec![blk(bb3)]);

        push(&mut func, bb3, AddRR, vec![vr(iv1), vr(iv), vr(one)]);
        push(&mut func, bb3, MovR, vec![vr(iv), vr(iv1)]);
        push(&mut func, bb3, B, vec![blk(bb1)]);

        push(&mut func, bb4, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb4);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb2);
        func.add_edge(bb2, bb3);
        func.add_edge(bb3, bb1);

        let mut pass = DeadCountedLoopElimination::new();
        let changed = pass.run(&mut func);
        eprintln!(
            "AUDIT deadloop nested-cycle: changed={} fired={}",
            changed,
            pass.fired()
        );
        assert!(
            !changed,
            "a loop whose body contains a nested cycle may spin forever within \
             one trip and must NOT be deleted"
        );
        assert!(func.block_order.contains(&bb1));
    }

    #[test]
    fn materializes_liveout_iv_final_value() {
        use AArch64Opcode::*;
        // NATIVE top-tested `for (iv=0; iv<10; iv++) {}` with `iv` LIVE-OUT.
        //
        //   bb0 (preheader): iv0=0 ; iv=iv0 ; bound=10 ; one=1 ; B bb1
        //   bb1 (header):    cmp iv,bound ; b.ge bb3 ; B bb2
        //   bb2 (latch):     iv1=iv+1 ; iv=iv1 ; B bb1
        //   bb3 (exit):      result = iv ; ret     (reads the live-out IV = 10)
        let mut func = new_func();
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let (iv0, iv, bound, one, iv1, result) = (g64(0), g64(1), g64(2), g64(3), g64(4), g64(5));

        push(&mut func, bb0, Movz, vec![vr(iv0), imm(0)]);
        push(&mut func, bb0, MovR, vec![vr(iv), vr(iv0)]);
        push(&mut func, bb0, Movz, vec![vr(bound), imm(10)]);
        push(&mut func, bb0, Movz, vec![vr(one), imm(1)]);
        push(&mut func, bb0, B, vec![blk(bb1)]);

        push(&mut func, bb1, CmpRR, vec![vr(iv), vr(bound)]);
        push(&mut func, bb1, BCond, vec![imm(CC_GE), blk(bb3)]);
        push(&mut func, bb1, B, vec![blk(bb2)]);

        push(&mut func, bb2, AddRR, vec![vr(iv1), vr(iv), vr(one)]);
        push(&mut func, bb2, MovR, vec![vr(iv), vr(iv1)]);
        push(&mut func, bb2, B, vec![blk(bb1)]);

        push(&mut func, bb3, MovR, vec![vr(result), vr(iv)]);
        push(&mut func, bb3, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb3);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb1);

        let mut pass = DeadCountedLoopElimination::new();
        let changed = pass.run(&mut func);

        assert!(changed, "the live-out counted loop must be deleted");
        assert!(!func.block_order.contains(&bb1));
        assert!(!func.block_order.contains(&bb2));

        // The exit's read of the IV must now use a fresh reg materialized in the
        // preheader with the exact final value (bound = 10).
        let exit_read = func.block(bb3).insts[0];
        let new_src = func.inst(exit_read).operands[1]
            .as_vreg()
            .expect("iv use rewritten");
        assert_ne!(new_src, iv, "exit use must be rewired off the deleted IV");

        // Find `new_src`'s definition in the preheader: a Movz #10.
        let mut found = false;
        for &iid in &func.block(bb0).insts {
            let inst = func.inst(iid);
            if inst.opcode == Movz
                && inst.operands[0].as_vreg() == Some(new_src)
                && inst.operands[1].as_imm() == Some(10)
            {
                found = true;
            }
        }
        assert!(
            found,
            "IV final value (10) must be materialized in the preheader"
        );
    }
}
