// trust-cg-opt - Reduction splitting (accumulator widening)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Reduction-splitting (accumulator-widening) loop optimization.
//!
//! Transforms a throughput-bound integer reduction
//!
//! ```text
//!   acc = acc_init;
//!   for i in start..limit { acc = acc <op> f(i); }   // op ∈ {+, *, |, ^}
//! ```
//!
//! whose loop-carried dependency chain (`acc` feeds the next `acc`) serialises
//! the CPU, into one that uses `N` independent accumulators:
//!
//! ```text
//!   acc0 = acc_init; acc1 = id; ... accN-1 = id;   // id = op identity
//!   for i in (start..limit step N) {
//!       acc0 = acc0 <op> f(i);
//!       acc1 = acc1 <op> f(i+1);
//!       ...
//!       accN-1 = accN-1 <op> f(i+N-1);
//!   }
//!   acc = ((acc0 <op> acc1) <op> (acc2 <op> acc3));   // balanced-tree combine
//! ```
//!
//! Breaking the single reduction chain into `N` parallel chains lets the CPU
//! exploit instruction-level parallelism (multiple in-flight adds), closing a
//! measured throughput gap versus clang -O2 on kernels like
//! `for i { acc += (i*i) ^ (i*3) }`.
//!
//! # Why this is sound (legality by construction)
//!
//! The scalar loop computes `acc_init <op> f(start) <op> ... <op> f(limit-1)`.
//! Two's-complement integer **add and multiply are associative AND commutative**
//! over `Z/2^w`, as are bitwise **or** and **xor**. Therefore ANY
//! regrouping/reordering of the `f(i)` terms yields a bit-for-bit identical
//! result. Distributing the terms across `N` accumulators by residue class
//! (`accj` gets `f(j), f(j+N), f(j+2N), ...`) and combining
//! `acc0 <op> ... <op> accN-1` is exactly such a regrouping. Because the op is
//! integer add/mul/or/xor (NOT float add/mul, which are non-associative — those
//! are rejected), the transform needs no per-instance proof; the regrouping
//! identity is proven once for all inputs (see
//! `trust-cg-verify/src/reduction_split_proofs.rs`).
//!
//! # IR shape (copy-based, post-DCE/CFG-simplify)
//!
//! This pass runs late (after DCE and CFG-simplify) where the loop is a clean
//! two-block copy-form loop with NO `Phi` pseudos — loop-carried variables are
//! plain vregs written both in the preheader (init) and at the tail of the latch
//! (`MovR v, v_next` writebacks):
//!
//! ```text
//!   preheader:  Movz v0,#limit; Movz v1,#0; ...; MovR iv,#0; MovR acc,#0; B header
//!   header:     CmpRR iv, limit; BCond GE, exit; B latch
//!   latch:      <term = f(iv)>; acc_next = op(acc, term); iv_next = iv + 1;
//!               MovR iv, iv_next; MovR acc, acc_next; B header
//! ```
//!
//! # Fail-closed doctrine
//!
//! This pass runs on ALL code, so a wrong transform is a miscompile affecting
//! everything. The recognizer bails (leaves the loop untouched) unless the loop
//! EXACTLY matches the recognized safe shape:
//!
//! * innermost loop, a preheader, body is exactly `{header, latch}`, the latch's
//!   only successor is the header, the header is exactly
//!   `[compare(iv,limit), BCond >= exit, B latch]`, and the exit's only
//!   predecessor is the header;
//! * exactly two loop-carried vars — an induction variable (`iv = iv + 1`) and
//!   the accumulator (`acc = acc <op> term`), each with a preheader init and a
//!   single latch writeback;
//! * the trip count is either a **constant** divisible by `N`, OR a **runtime**
//!   limit — a loop-invariant vreg the header compares `iv` against (see the
//!   RUNTIME section below);
//! * `op` ∈ {`AddRR`, `MulRR`, `OrrRR`, `EorRR`} (AND is bailed; float ops are
//!   non-associative);
//! * the whole body is pure (no load/store/call — a register reduction);
//! * `acc` is read nowhere in the body except the reduction op;
//! * the term `f(iv)` reads only the IV, loop-invariants, and earlier term defs
//!   (a closed-world, cloneable computation).
//!
//! Anything else: BAIL.
//!
//! # RUNTIME trip counts (split-with-tail)
//!
//! When the limit is a runtime value (not a compile-time constant), the exact
//! number of iterations is unknown, so a bare N-wide loop would over- or
//! under-run. Instead we emit a **guarded 4-wide main loop** followed by a
//! **peeled sequential remainder tail**:
//!
//! ```text
//!   preheader: acc0=init; acc1..3=identity; main_bound = limit - (N-1);
//!              if main_bound >= limit { goto combine }   // GUARD (see below)
//!   main:      for (; iv < main_bound; iv += N) {        // iv<main_bound == iv+N<=limit
//!                  acc0 op= term(iv); acc1 op= term(iv+1);
//!                  acc2 op= term(iv+2); acc3 op= term(iv+3);
//!              }
//!   combine:   acc_final = ((acc0 op acc1) op (acc2 op acc3));
//!   tail:      for k in 0..N-1 { if iv < limit { acc_final op= term(iv); iv += 1; } }
//!   exit:      liveouts use acc_final.
//! ```
//!
//! **Bound safety (the one subtle correctness point).** The main loop processes
//! `N` UNGUARDED elements per iteration, so it must run *only* while `iv+N <=
//! limit`. We test `iv < main_bound` with `main_bound = limit-(N-1)`; over the
//! integers `iv < limit-(N-1) ⟺ iv+N <= limit`. The danger is that computing
//! `limit-(N-1)` can WRAP when `limit` is within `N-1` of the type's minimum
//! (signed) or of zero (unsigned) — a wrapped `main_bound` could make the main
//! loop run and over-run past `limit`. The preheader **guard** `main_bound >=
//! limit ⇒ skip main` fail-closes exactly those cases: if the subtraction wrapped
//! (or fewer than `N` iterations exist) the main loop is skipped entirely and the
//! peeled tail runs the whole `[start,limit)` range sequentially — identical to
//! the original loop. So the main loop NEVER executes with an unsafe bound.
//! Because in every entered case `iv < main_bound` implies `iv..iv+N-1` are all
//! `< limit`, the four unrolled indices are always in range.
//!
//! **Remainder ≤ N-1.** When the main loop runs, it exits at the first `iv >=
//! main_bound = limit-(N-1)`, and (stepping by `N` from a value `< main_bound`)
//! `iv <= limit`, so `limit - iv ∈ [0, N-1]`. When it is skipped by the guard,
//! at most `N-1` iterations existed to begin with. Either way ≤ `N-1` elements
//! remain, so the `N-1` peeled, individually-`iv<limit`-guarded tail steps
//! suffice AND cannot over-process (each guards its own element).
//!
//! **Idempotence.** The main loop's IV now steps by `N` (not 1), so the
//! recognizer bails on it; the tail is straight-line (no back-edge), so it is not
//! a loop and can never be re-recognized. The transform is a fixpoint.
//!
//! Soundness of the regrouping (main lanes by residue + balanced combine) and of
//! the sequential tail is proven in
//! `trust-cg-verify/src/reduction_split_proofs.rs`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    RegClass, SourceLoc, VReg,
};

use crate::dom::DomTree;
use crate::effects::{MemoryEffect, inst_produces_value, opcode_effect};
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Number of independent accumulators (split factor / partial-unroll count).
const SPLIT_FACTOR: usize = 4;

/// AArch64 condition-code encodings for "exit when `iv >= limit`".
const CC_HS: i64 = 2; // unsigned >=
const CC_GE: i64 = 10; // signed >=

/// Reduction-splitting (accumulator-widening) pass.
pub struct ReductionSplit;

impl MachinePass for ReductionSplit {
    fn name(&self) -> &str {
        "reduction-split"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        Self::run_with_loop_analysis(func, &loop_analysis, None)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        Self::run_with_loop_analysis(func, &loop_analysis, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        Self::run_with_loop_analysis(func, &loop_analysis, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        Self::run_with_loop_analysis(func, &loop_analysis, Some(provenance))
    }
}

impl ReductionSplit {
    fn run_with_loop_analysis(
        func: &mut MachFunction,
        loop_analysis: &LoopAnalysis,
        mut provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        if loop_analysis.is_empty() {
            return false;
        }

        // Only innermost loops.
        let all_loops: Vec<NaturalLoop> = loop_analysis.all_loops().cloned().collect();
        let innermost: Vec<NaturalLoop> = all_loops
            .iter()
            .filter(|lp| !all_loops.iter().any(|o| o.parent == Some(lp.header)))
            .cloned()
            .collect();

        let dump = std::env::var("TRUST_CG_DUMP_REDSPLIT").is_ok();

        let mut changed = false;
        for lp in &innermost {
            match recognize(func, lp) {
                Some(plan) => {
                    if dump {
                        let mode = match plan.mode {
                            SplitMode::Constant => "constant".to_string(),
                            SplitMode::Runtime { limit, cc } => {
                                format!("runtime(limit={limit:?},cc={cc})")
                            }
                        };
                        eprintln!(
                            "[redsplit] FIRE fn={} header={:?} op={:?} mode={} acc={:?} iv={:?}",
                            func.name, lp.header, plan.combine_op, mode, plan.acc, plan.iv
                        );
                    }
                    apply(func, &plan, provenance.as_deref_mut());
                    if dump {
                        eprintln!("[redsplit] POST-TRANSFORM fn={}", func.name);
                        dump_all(func);
                    }
                    changed = true;
                }
                None => {
                    if dump {
                        eprintln!("[redsplit] BAIL fn={} header={:?}", func.name, lp.header);
                        dump_loop(func, lp);
                    }
                }
            }
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Closed-form (Faulhaber) reduction — the loop-DELETING sibling of the split
// ---------------------------------------------------------------------------
//
// When a reduction loop's ENTIRE term is a pure polynomial in the induction
// variable of degree ≤ 2 — `acc += a2·i² + a1·i + a0`, with NO opaque ops
// (no xor/or/and/shift/data-dependent work) — the whole loop collapses to a
// straight-line closed form (scalar-evolution loop deletion, like clang):
//
//   Σ_{i<n} i   = n(n-1)/2                    (S1; exact ÷2 via 128-bit halving)
//   Σ_{i<n} i²  = n(n-1)(2n-1)/6              (S2; exact ÷3 via modular inverse)
//   result      = acc_init + a2·S2 + a1·S1 + a0·n   (all u64 wrapping, mod 2^64)
//
// This runs BEFORE `ReductionSplit` (as its own pass) and fires ONLY on the
// exact pure-polynomial add-reduction shape; everything else it leaves for the
// split pass. It is FAIL-CLOSED: any premise it cannot establish ⇒ BAIL.
pub struct ClosedFormReduction;

impl MachinePass for ClosedFormReduction {
    fn name(&self) -> &str {
        "closed-form-reduction"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        Self::run_with_loop_analysis(func, &loop_analysis, None)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        Self::run_with_loop_analysis(func, &loop_analysis, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        Self::run_with_loop_analysis(func, &loop_analysis, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        Self::run_with_loop_analysis(func, &loop_analysis, Some(provenance))
    }
}

impl ClosedFormReduction {
    fn run_with_loop_analysis(
        func: &mut MachFunction,
        loop_analysis: &LoopAnalysis,
        mut provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        if loop_analysis.is_empty() {
            return false;
        }
        let all_loops: Vec<NaturalLoop> = loop_analysis.all_loops().cloned().collect();
        let innermost: Vec<NaturalLoop> = all_loops
            .iter()
            .filter(|lp| !all_loops.iter().any(|o| o.parent == Some(lp.header)))
            .cloned()
            .collect();
        let dump = std::env::var("TRUST_CG_DUMP_CLOSEDFORM").is_ok();

        let mut changed = false;
        // Only the FIRST recognized loop per function is closed-form-rewritten
        // per pass invocation: the CFG surgery removes blocks, which invalidates
        // the (cloned) loop analysis for any later loop. The pass is re-run to
        // fixpoint by the O3 pass manager, and O2's single run handles the
        // common single-loop kernels; a second independent loop is picked up on
        // the next iteration (O3) or by ReductionSplit (O2).
        for lp in &innermost {
            match recognize_closed_form(func, lp) {
                Some(cf) => {
                    if dump {
                        eprintln!(
                            "[closedform] FIRE fn={} header={:?} poly=(a2={},a1={},a0={}) start={} cc={}",
                            func.name,
                            lp.header,
                            cf.poly.a2,
                            cf.poly.a1,
                            cf.poly.a0,
                            cf.start,
                            cf.cc
                        );
                    }
                    apply_closed_form(func, &cf, provenance.as_deref_mut());
                    if dump {
                        eprintln!("[closedform] POST-TRANSFORM fn={}", func.name);
                        dump_all(func);
                    }
                    changed = true;
                    break;
                }
                None => {
                    if dump {
                        eprintln!("[closedform] BAIL fn={} header={:?}", func.name, lp.header);
                    }
                }
            }
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Associative-integer op family
// ---------------------------------------------------------------------------

/// The associative + commutative integer ops this pass can split, with their
/// identity element. `AndRR` is intentionally excluded (its all-ones identity
/// materialization is out of scope), and all float ops are excluded (float
/// add/mul are NOT associative). Returns `None` for any other opcode.
fn assoc_int_identity(op: AArch64Opcode) -> Option<i64> {
    match op {
        AArch64Opcode::AddRR => Some(0),
        AArch64Opcode::MulRR => Some(1),
        AArch64Opcode::OrrRR => Some(0),
        AArch64Opcode::EorRR => Some(0),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Recognized plan
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum RedKind {
    /// `acc_next = op(acc, term)` for an associative-int op.
    Assoc(AArch64Opcode),
    /// `acc_next = Madd(a, b, acc)` == `a*b + acc` — a fused sum-of-products add
    /// (the shape mul+add reductions like `acc += a[i]*b[i]` fold into). Treated
    /// as an integer add reduction with term `a*b`.
    Madd,
}

/// How the loop's trip count is known — which drives which rewrite is emitted.
#[derive(Clone, Copy)]
enum SplitMode {
    /// A compile-time-constant trip count divisible by `SPLIT_FACTOR`. Rewrites
    /// in place: N accumulators, IV steps by N, balanced combine on the exit
    /// edge (no guard, no tail — the count is exact).
    Constant,
    /// A runtime (loop-invariant) limit vreg the header compares `iv` against,
    /// with the given exit condition-code (`CC_GE` / `CC_HS`). Rewrites to a
    /// guarded N-wide main loop + peeled sequential remainder tail.
    Runtime { limit: VReg, cc: i64 },
}

/// Limit discovered in the header compare.
enum LimitKind {
    /// `iv` is compared against a compile-time constant.
    Const(i64),
    /// `iv` is compared against a runtime (non-constant) vreg.
    Runtime(VReg),
}

/// A verified-legal split-reduction ready to be rewritten. Every field is
/// established by construction in `recognize`.
struct SplitPlan {
    header: BlockId,
    latch: BlockId,
    preheader: BlockId,
    exit: BlockId,
    /// Reduction form.
    red_kind: RedKind,
    /// Opcode for the balanced-tree combine (the Assoc op, or `AddRR` for Madd).
    combine_op: AArch64Opcode,
    /// Op identity materialised into the extra accumulators.
    identity: i64,
    /// Reduction input operands (remapped per copy): `[term]` for Assoc,
    /// `[a, b]` for Madd.
    red_inputs: Vec<VReg>,
    /// Register class of the accumulator side.
    rc: RegClass,
    /// Induction variable (the loop-carried counter vreg).
    iv: VReg,
    iv_class: RegClass,
    /// Accumulator (loop-carried) vreg — this is `acc0`.
    acc: VReg,
    /// The IV-increment instruction (`iv_next = iv + 1`) in the latch.
    iv_inc_inst: InstId,
    /// vreg holding `iv_next` (the IV increment result).
    iv_next: VReg,
    /// The reduction instruction (`acc_next = op(acc, term)`) in the latch.
    reduction_inst: InstId,
    /// The latch writeback `MovR iv, iv_next`.
    iv_writeback: InstId,
    /// Latch instructions computing the term (ordered).
    term_insts: Vec<InstId>,
    /// How the trip count is known (constant-exact vs runtime split-with-tail).
    mode: SplitMode,
    /// The (constant) loop start value — `iv`'s init. The recognizer already
    /// requires this to resolve to a constant; it is retained so the
    /// strength-reduction can materialise the constant per-lane recurrence seeds
    /// `f(start+k)` in the preheader.
    start: i64,
    /// Optional polynomial strength-reduction plan. `Some` when the term
    /// contains multiplies that are polynomials in the IV (`i*i`, `i*c`, …),
    /// which the N-wide main loop can compute with running additions (a per-lane
    /// difference engine) instead of multiplies. `None` ⇒ emit the term verbatim
    /// (clone-with-`iv→i+k`) exactly as the original transform did. See
    /// `analyze_poly_term`.
    poly: Option<PolyTermPlan>,
}

// ---------------------------------------------------------------------------
// Recognizer
// ---------------------------------------------------------------------------

fn recognize(func: &MachFunction, lp: &NaturalLoop) -> Option<SplitPlan> {
    let preheader = lp.preheader?;
    let header = lp.header;
    let latch = lp.latch;

    // -- CFG shape: body is exactly {header, latch}, header != latch. --
    if header == latch
        || lp.body.len() != 2
        || !lp.body.contains(&header)
        || !lp.body.contains(&latch)
    {
        return None;
    }
    // Latch's only successor is the header (the back-edge).
    if func.block(latch).succs != vec![header] {
        return None;
    }
    // Header has exactly two successors: the latch and a single exit block.
    let hsuccs = func.block(header).succs.clone();
    if hsuccs.len() != 2 {
        return None;
    }
    let exits: Vec<BlockId> = hsuccs
        .iter()
        .copied()
        .filter(|s| !lp.body.contains(s))
        .collect();
    if exits.len() != 1 {
        return None;
    }
    let exit = exits[0];
    if !hsuccs.contains(&latch) {
        return None;
    }
    // The exit's only predecessor is the header (single-entry exit).
    if func.block(exit).preds != vec![header] {
        return None;
    }

    // -- Whole body must be pure (register reduction: no load/store/call). --
    for &bid in &[header, latch] {
        for &iid in &func.block(bid).insts {
            if opcode_effect(func.inst(iid).opcode) != MemoryEffect::Pure {
                return None;
            }
        }
    }

    // -- Loop-carried variables via latch writebacks. --
    let preheader_defs = block_value_defs(func, preheader);
    // (dst, src, writeback-inst)
    let mut carried: Vec<(VReg, VReg, InstId)> = Vec::new();
    for &iid in &func.block(latch).insts {
        let inst = func.inst(iid);
        if !matches!(inst.opcode, AArch64Opcode::MovR | AArch64Opcode::Copy) {
            continue;
        }
        let (Some(dst), Some(src)) = (
            inst.operands.first().and_then(|o| o.as_vreg()),
            inst.operands.get(1).and_then(|o| o.as_vreg()),
        ) else {
            continue;
        };
        if dst == src || !preheader_defs.contains(&dst) {
            continue;
        }
        // The carried var must be written exactly once in the latch (here).
        if count_defs_in_block(func, latch, dst) != 1 {
            return None;
        }
        carried.push((dst, src, iid));
    }
    if carried.len() != 2 {
        return None;
    }

    // Classify the two carried vars as IV and accumulator.
    let mut iv_info: Option<(VReg, VReg, InstId, InstId)> = None; // (iv, iv_next, inc_inst, writeback)
    let mut acc_info: Option<(VReg, InstId, RedKind, Vec<VReg>)> = None; // (acc, red_inst, kind, inputs)

    for &(dst, src, wb) in &carried {
        let def = latch_unique_def(func, latch, src)?;
        let def_inst = func.inst(def);
        // IV: src = AddRR(dst, c=1) or AddRI(dst, #1).
        if let Some(step) = increment_step(func, lp, def_inst, dst) {
            if step != 1 {
                return None; // only +1 IV supported (idempotence + f(i+k) indexing)
            }
            if iv_info.is_some() {
                return None;
            }
            iv_info = Some((dst, src, def, wb));
            continue;
        }
        // ACC (associative op): src = op(dst, term).
        if assoc_int_identity(def_inst.opcode).is_some() && def_inst.operands.len() >= 3 {
            let a = def_inst.operands[1].as_vreg();
            let b = def_inst.operands[2].as_vreg();
            let term = if a == Some(dst) {
                b
            } else if b == Some(dst) {
                a
            } else {
                None
            };
            if let Some(term) = term {
                if acc_info.is_some() {
                    return None;
                }
                acc_info = Some((dst, def, RedKind::Assoc(def_inst.opcode), vec![term]));
                continue;
            }
        }
        // ACC (fused multiply-add): src = Madd(a, b, dst) == a*b + acc.
        if def_inst.opcode == AArch64Opcode::Madd && def_inst.operands.len() >= 4 {
            let a = def_inst.operands[1].as_vreg();
            let b = def_inst.operands[2].as_vreg();
            let c = def_inst.operands[3].as_vreg();
            if let (Some(a), Some(b), Some(c)) = (a, b, c)
                && c == dst
                && a != dst
                && b != dst
            {
                if acc_info.is_some() {
                    return None;
                }
                acc_info = Some((dst, def, RedKind::Madd, vec![a, b]));
                continue;
            }
        }
        return None; // a carried var that is neither IV nor recognizable accumulator.
    }

    let (iv, iv_next, iv_inc_inst, iv_writeback) = iv_info?;
    let (acc, reduction_inst, red_kind, red_inputs) = acc_info?;
    let (combine_op, identity) = match red_kind {
        RedKind::Assoc(op) => (op, assoc_int_identity(op)?),
        RedKind::Madd => (AArch64Opcode::AddRR, 0),
    };

    // -- Class/width uniformity on the accumulator side. --
    let rc = acc.class;
    if iv.class != rc {
        return None;
    }
    for &v in &red_inputs {
        if v.class != rc {
            return None;
        }
    }

    // -- Header shape + limit (constant or runtime) + exit condition-code. --
    // `start` must resolve to a constant (the common `for i in 0..n` has
    // start = 0); this keeps parity with the constant path and is a harmless
    // conservative gate for the runtime path (correctness does not depend on the
    // concrete start value — see the RUNTIME section of the module docs).
    let start = resolve_const(func, lp, iv_init_source(func, preheader, iv)?)?;
    let (limit_kind, cc) = validate_header(func, header, iv, latch, exit, lp)?;

    // -- `acc` read nowhere in the body except the reduction. --
    for &bid in &[header, latch] {
        for &iid in &func.block(bid).insts {
            if iid == reduction_inst {
                continue; // the reduction is the one allowed reader of `acc`.
            }
            let inst = func.inst(iid);
            let produces = inst_produces_value(inst);
            for (idx, operand) in inst.operands.iter().enumerate() {
                if produces && idx == 0 {
                    continue; // def slot is not a read.
                }
                if operand.as_vreg() == Some(acc) {
                    return None;
                }
            }
        }
    }

    // -- Term computation: latch minus control/writeback/reduction/inc. --
    let branch_id = *func.block(latch).insts.last()?;
    let acc_writeback = carried
        .iter()
        .find(|(d, _, _)| *d == acc)
        .map(|(_, _, wb)| *wb)?;
    let control: [InstId; 5] = [
        iv_inc_inst,
        reduction_inst,
        iv_writeback,
        acc_writeback,
        branch_id,
    ];
    let mut term_insts: Vec<InstId> = Vec::new();
    for &iid in &func.block(latch).insts {
        if control.contains(&iid) {
            continue;
        }
        term_insts.push(iid);
    }

    // Closed-world check: each term inst is a value producer reading only
    // {iv, loop-invariants, earlier term defs}.
    let body_defs = collect_body_defs(func, lp);
    let mut term_defs: HashSet<VReg> = HashSet::new();
    for &iid in &term_insts {
        let inst = func.inst(iid);
        if !inst_produces_value(inst) {
            return None;
        }
        let def = inst.operands.first().and_then(|o| o.as_vreg())?;
        for operand in inst.operands.iter().skip(1) {
            if let Some(v) = operand.as_vreg() {
                let ok = v == iv || term_defs.contains(&v) || !body_defs.contains(&v);
                if !ok {
                    return None;
                }
            }
        }
        term_defs.insert(def);
    }

    // Every reduction input must be the IV, a term-inst def, or a loop-invariant
    // (so the per-copy reduction can be reconstructed by remapping `iv -> i+k`).
    for &v in &red_inputs {
        let ok = v == iv || term_defs.contains(&v) || !body_defs.contains(&v);
        if !ok {
            return None;
        }
    }

    // -- Decide the trip-count mode. --
    // CONSTANT: keep the exact v1 contract — fire only when the trip count is a
    //   compile-time constant divisible by (and >=) SPLIT_FACTOR; otherwise BAIL
    //   (a non-divisible constant trip is intentionally NOT rerouted through the
    //   runtime path, preserving the existing `test_bail_non_divisible` contract).
    // RUNTIME: the limit is a non-constant vreg — require it be loop-invariant
    //   (not written in the body) and share the IV's class (they are compared),
    //   then take the guarded main + peeled-tail path.
    let mode = match limit_kind {
        LimitKind::Const(limit) => {
            if limit <= start {
                return None;
            }
            let trips = limit.checked_sub(start)? as u64;
            if trips == 0
                || !trips.is_multiple_of(SPLIT_FACTOR as u64)
                || trips < SPLIT_FACTOR as u64
            {
                return None;
            }
            SplitMode::Constant
        }
        LimitKind::Runtime(limit) => {
            if limit.class != iv.class || body_defs.contains(&limit) {
                return None;
            }
            SplitMode::Runtime { limit, cc }
        }
    };

    // -- Polynomial strength-reduction analysis (Assoc reductions only). --
    // If the term contains multiplies that are degree-≤2 polynomials in the IV
    // (`i*i`, `i*c`, `(i+1)*(i+2)`, …), the N-wide main loop can compute those
    // sub-terms with a per-lane difference engine (running additions) instead of
    // multiplies. `None` ⇒ no reducible multiply; emit the term verbatim.
    let poly = match red_kind {
        RedKind::Assoc(_) => {
            analyze_poly_term(func, lp, &term_insts, &red_inputs, iv, &body_defs, start)
        }
        RedKind::Madd => None,
    };

    Some(SplitPlan {
        header,
        latch,
        preheader,
        exit,
        red_kind,
        combine_op,
        identity,
        red_inputs,
        rc,
        iv,
        iv_class: iv.class,
        acc,
        iv_inc_inst,
        iv_next,
        reduction_inst,
        iv_writeback,
        term_insts,
        mode,
        start,
        poly,
    })
}

/// If `def_inst` computes `dst + const` (via `AddRR(dst, c)` with `c` a
/// loop-invariant constant, or `AddRI(dst, #imm)`), return the step.
fn increment_step(
    func: &MachFunction,
    lp: &NaturalLoop,
    def_inst: &MachInst,
    dst: VReg,
) -> Option<i64> {
    match def_inst.opcode {
        AArch64Opcode::AddRI => {
            if def_inst.operands.len() >= 3
                && def_inst.operands[1].as_vreg() == Some(dst)
                && let Some(imm) = def_inst.operands[2].as_imm()
            {
                return Some(imm);
            }
            None
        }
        AArch64Opcode::AddRR => {
            if def_inst.operands.len() >= 3 {
                let a = def_inst.operands[1].as_vreg();
                let b = def_inst.operands[2].as_vreg();
                if a == Some(dst)
                    && let Some(r) = b
                {
                    return resolve_const(func, lp, r);
                }
                if b == Some(dst)
                    && let Some(r) = a
                {
                    return resolve_const(func, lp, r);
                }
            }
            None
        }
        _ => None,
    }
}

/// Source vreg of the preheader init writeback `MovR iv, src`.
fn iv_init_source(func: &MachFunction, preheader: BlockId, iv: VReg) -> Option<VReg> {
    for &iid in &func.block(preheader).insts {
        let inst = func.inst(iid);
        if matches!(inst.opcode, AArch64Opcode::MovR | AArch64Opcode::Copy)
            && inst.operands.first().and_then(|o| o.as_vreg()) == Some(iv)
        {
            return inst.operands.get(1).and_then(|o| o.as_vreg());
        }
        // Direct materialization `Movz iv, #imm` / `MovI iv, #imm`.
        if matches!(
            inst.opcode,
            AArch64Opcode::Movz | AArch64Opcode::MovI | AArch64Opcode::Movk
        ) && inst.operands.first().and_then(|o| o.as_vreg()) == Some(iv)
        {
            return Some(iv);
        }
    }
    None
}

/// Validate the header is exactly `[compare(iv, limit), BCond >= exit, B latch]`
/// and return the limit (constant or runtime vreg) plus the exit condition-code.
fn validate_header(
    func: &MachFunction,
    header: BlockId,
    iv: VReg,
    latch: BlockId,
    exit: BlockId,
    lp: &NaturalLoop,
) -> Option<(LimitKind, i64)> {
    let insts = &func.block(header).insts;
    if insts.len() != 3 {
        return None;
    }
    let cmp = func.inst(insts[0]);
    let bcond = func.inst(insts[1]);
    let b = func.inst(insts[2]);

    // Compare: iv (operand 0) vs a limit — a constant (`CmpRI`, or `CmpRR`
    // against a resolvable constant) or a runtime vreg (`CmpRR`, unresolvable).
    let limit_kind = match cmp.opcode {
        AArch64Opcode::CmpRI => {
            if cmp.operands.first().and_then(|o| o.as_vreg()) != Some(iv) {
                return None;
            }
            LimitKind::Const(cmp.operands.get(1)?.as_imm()?)
        }
        AArch64Opcode::CmpRR => {
            if cmp.operands.first().and_then(|o| o.as_vreg()) != Some(iv) {
                return None;
            }
            let r = cmp.operands.get(1)?.as_vreg()?;
            match resolve_const(func, lp, r) {
                Some(c) => LimitKind::Const(c),
                None => LimitKind::Runtime(r),
            }
        }
        _ => return None,
    };

    // BCond: exit when iv >= limit (cc ∈ {GE, HS}), branching to the exit block.
    if bcond.opcode != AArch64Opcode::BCond {
        return None;
    }
    let cc = bcond.operands.first()?.as_imm()?;
    if cc != CC_GE && cc != CC_HS {
        return None;
    }
    if !matches!(bcond.operands.get(1), Some(MachOperand::Block(t)) if *t == exit) {
        return None;
    }
    // Fallthrough unconditional branch to the latch.
    if b.opcode != AArch64Opcode::B
        || !matches!(b.operands.first(), Some(MachOperand::Block(t)) if *t == latch)
    {
        return None;
    }
    Some((limit_kind, cc))
}

/// Resolve a vreg to a constant by folding the `Movz` / `Movk` / `MovI`
/// sequence that defines it in blocks OUTSIDE the loop body.
fn resolve_const(func: &MachFunction, lp: &NaturalLoop, v: VReg) -> Option<i64> {
    let mut val: Option<u64> = None;
    let mut saw_def = false;
    for &bid in &func.block_order {
        if lp.body.contains(&bid) {
            continue;
        }
        for &iid in &func.block(bid).insts {
            let inst = func.inst(iid);
            if inst.operands.first().and_then(|o| o.as_vreg()) != Some(v) {
                continue;
            }
            match inst.opcode {
                AArch64Opcode::MovI if inst.operands.len() == 2 => {
                    val = Some(inst.operands.get(1)?.as_imm()? as u64);
                    saw_def = true;
                }
                AArch64Opcode::Movz => {
                    let (dst, value) = crate::reaching_const::movz_value(inst)?;
                    if dst != v {
                        return None;
                    }
                    val = Some(value);
                    saw_def = true;
                }
                AArch64Opcode::Movk => {
                    let (dst, imm, shift) = crate::reaching_const::parse_move_wide_inst(inst)?;
                    if dst != v {
                        return None;
                    }
                    let cur = val?;
                    val = Some((cur & !(0xFFFFu64 << shift)) | (imm << shift));
                    saw_def = true;
                }
                _ if inst_produces_value(inst) => {
                    // Some other definition of `v` — cannot resolve to a constant.
                    return None;
                }
                _ => {}
            }
        }
    }
    if saw_def { Some(val? as i64) } else { None }
}

/// The unique value-producing instruction in `block` that defines `v`, if
/// exactly one exists.
fn latch_unique_def(func: &MachFunction, block: BlockId, v: VReg) -> Option<InstId> {
    let mut found: Option<InstId> = None;
    for &iid in &func.block(block).insts {
        let inst = func.inst(iid);
        if inst_produces_value(inst) && inst.operands.first().and_then(|o| o.as_vreg()) == Some(v) {
            if found.is_some() {
                return None;
            }
            found = Some(iid);
        }
    }
    found
}

fn count_defs_in_block(func: &MachFunction, block: BlockId, v: VReg) -> usize {
    let mut n = 0;
    for &iid in &func.block(block).insts {
        let inst = func.inst(iid);
        if inst_produces_value(inst) && inst.operands.first().and_then(|o| o.as_vreg()) == Some(v) {
            n += 1;
        }
    }
    n
}

/// The set of vregs defined (operand 0 of a value producer) in `block`.
fn block_value_defs(func: &MachFunction, block: BlockId) -> HashSet<VReg> {
    let mut defs = HashSet::new();
    for &iid in &func.block(block).insts {
        let inst = func.inst(iid);
        if inst_produces_value(inst)
            && let Some(v) = inst.operands.first().and_then(|o| o.as_vreg())
        {
            defs.insert(v);
        }
    }
    defs
}

/// All vregs defined inside the loop body.
fn collect_body_defs(func: &MachFunction, lp: &NaturalLoop) -> HashSet<VReg> {
    let mut defs = HashSet::new();
    for &bid in &func.block_order {
        if !lp.body.contains(&bid) {
            continue;
        }
        for &iid in &func.block(bid).insts {
            let inst = func.inst(iid);
            if inst_produces_value(inst)
                && let Some(v) = inst.operands.first().and_then(|o| o.as_vreg())
            {
                defs.insert(v);
            }
        }
    }
    defs
}

// ---------------------------------------------------------------------------
// Polynomial (linear) strength reduction of the term
// ---------------------------------------------------------------------------
//
// The N-wide main loop must, for each lane `k ∈ [0,N)`, evaluate the term at
// index `idx_k = start + k + N·m` on iteration `m`. The original transform
// recomputes the term from scratch per lane (cloning `iv → i+k`), so a term like
// `(i*i) ^ (i*3)` costs a multiply per lane for EACH multiplicative sub-term.
//
// We strength-reduce the AFFINE (degree-1) multiplicative sub-terms — a sub-term
// `L(i) = c·i` (e.g. `i*3`, `i*7`) — into a running addition, exactly as clang
// does. A single loop-carried value `v = L(i)` is maintained; per lane its value
// is `v + c·k` (a small immediate offset) and it advances `v += c·N` per
// iteration. The seeds `L(start)`, `c·k`, `c·N` are compile-time constants (the
// recognizer already requires `start` constant), so the preheader materialises
// constants and each linear sub-term becomes adds in the hot loop.
//
// QUADRATICS ARE LEFT AS MULTIPLIES. A sub-term like `i*i` is NOT reduced — it
// is emitted as a real `mul(i+k, i+k)` per lane. This matches clang, which keeps
// the `i*i` multiplies and only running-adds the linear terms: reducing `i*i` to
// a finite-difference engine is sound but *slower* (it trades ~4 cheap
// multiplies for a dozen adds). The analysis (`inst_poly`) therefore caps the
// polynomial degree at 1 and treats any degree-2 value as opaque.
//
// SOUNDNESS: a reduced sub-term's per-lane value equals `L(idx_k)`, which is
// *exactly* the value the original clone-with-`iv→i+k` transform computes for
// lane `k`. The linear recurrence-preservation identities (per-lane offset and
// per-iteration step) are proven for all inputs at 8/64-bit in
// `trust-cg-verify/src/reduction_split_proofs.rs`. The lane-regrouping / combine
// / tail are unchanged and already proven. If ANY sub-term is not an analyzable
// affine polynomial the analysis returns `None` and the verbatim (proven)
// multiply path runs — a fail-closed superset.

/// A degree-≤2 polynomial `a2·i² + a1·i + a0` in the IV, with exact `i128`
/// coefficients. Only affine (`a2 == 0`) values are strength-reduced; `a2` is
/// retained so `inst_poly` can DETECT and reject quadratics. Coefficient
/// *combination* uses `checked_*`: a genuinely huge product bails the analysis
/// (verbatim multiplies) rather than mis-classifying.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Poly {
    a0: i128,
    a1: i128,
    a2: i128,
}

impl Poly {
    fn constant(c: i128) -> Poly {
        Poly {
            a0: c,
            a1: 0,
            a2: 0,
        }
    }
    fn iv() -> Poly {
        Poly {
            a0: 0,
            a1: 1,
            a2: 0,
        }
    }
    fn add(self, o: Poly) -> Option<Poly> {
        Some(Poly {
            a0: self.a0.checked_add(o.a0)?,
            a1: self.a1.checked_add(o.a1)?,
            a2: self.a2.checked_add(o.a2)?,
        })
    }
    fn sub(self, o: Poly) -> Option<Poly> {
        Some(Poly {
            a0: self.a0.checked_sub(o.a0)?,
            a1: self.a1.checked_sub(o.a1)?,
            a2: self.a2.checked_sub(o.a2)?,
        })
    }
    /// Polynomial product — `None` if the exact product would exceed degree 2
    /// (or overflows `i128`, treated conservatively as non-reducible).
    fn mul(self, o: Poly) -> Option<Poly> {
        // Degree-raising cross terms (i³, i⁴) must vanish.
        let hi3 = self
            .a1
            .checked_mul(o.a2)?
            .checked_add(self.a2.checked_mul(o.a1)?)?;
        let hi4 = self.a2.checked_mul(o.a2)?;
        if hi3 != 0 || hi4 != 0 {
            return None;
        }
        let a0 = self.a0.checked_mul(o.a0)?;
        let a1 = self
            .a0
            .checked_mul(o.a1)?
            .checked_add(self.a1.checked_mul(o.a0)?)?;
        let a2 = self
            .a0
            .checked_mul(o.a2)?
            .checked_add(self.a1.checked_mul(o.a1)?)?
            .checked_add(self.a2.checked_mul(o.a0)?)?;
        Some(Poly { a0, a1, a2 })
    }
}

/// Static analysis result: which term-defs are polynomials in the IV, and which
/// polynomial values feed the *opaque* part of the term (the per-lane
/// "boundaries" that get a difference-engine recurrence).
struct PolyTermPlan {
    /// Coefficients of every term-def (and the IV) that is a polynomial in `i`.
    /// A term-def NOT in this map is *opaque* and is emitted verbatim per lane.
    coeffs: HashMap<VReg, Poly>,
    /// Distinct polynomial values (source vregs, possibly the IV) consumed by an
    /// opaque term-inst or used directly as a reduction input. Ordered.
    boundaries: Vec<VReg>,
}

/// One affine boundary sub-term `L(i) = a1·i + a0`'s running recurrence. A
/// SINGLE loop-carried base value `v = L(i)` is kept; lane `k`'s value is
/// `v + a1·k` (a small immediate offset) and it advances `v += a1·N` per
/// iteration. Low register pressure (one carried vreg per reduced sub-term).
struct BoundaryEngine {
    /// The affine coefficients (drive the constant per-lane offsets and step).
    p: Poly,
    /// Carried base value vreg (`L(i)` for the base index `i`).
    v: VReg,
}

/// Evaluate `P(x)` mod 2^128 (residue reduced to the loop width at
/// materialisation). Uses wrapping arithmetic — the *values* are deliberately
/// modular; only degree analysis (`Poly::mul`) is exact.
fn poly_eval(p: Poly, x: i128) -> i128 {
    p.a2.wrapping_mul(x)
        .wrapping_mul(x)
        .wrapping_add(p.a1.wrapping_mul(x))
        .wrapping_add(p.a0)
}

/// Reduce an `i128` value to the low `w` bits (two's-complement residue mod 2^w).
fn mask_to_width(v: i128, w: u32) -> u64 {
    let u = v as u64; // low 64 bits
    if w >= 64 { u } else { u & ((1u64 << w) - 1) }
}

/// Classify one term-inst as a polynomial in the IV of degree ≤ 2, or `None` if
/// the instruction is opaque (not an analyzable arithmetic op, or a genuine
/// degree-3+ / overflowing product). This is the shared core of the polynomial
/// analysis; it does NOT apply the affine (degree-1) cap — see `inst_poly` for
/// the strength-reduction caller and `closed_form_term_poly` for the closed-form
/// caller, which needs the full degree-2 result (`i*i`).
fn inst_poly_core(
    func: &MachFunction,
    lp: &NaturalLoop,
    inst: &MachInst,
    iv: VReg,
    coeffs: &HashMap<VReg, Poly>,
    body_defs: &HashSet<VReg>,
) -> Option<Poly> {
    let operand_poly = |idx: usize| -> Option<Poly> {
        let v = inst.operands.get(idx)?.as_vreg()?;
        if let Some(p) = coeffs.get(&v) {
            return Some(*p);
        }
        if v == iv {
            return Some(Poly::iv());
        }
        // A loop-invariant that resolves to a constant is a degree-0 polynomial.
        if !body_defs.contains(&v)
            && let Some(c) = resolve_const(func, lp, v)
        {
            return Some(Poly::constant(c as i128));
        }
        None
    };
    let imm = |idx: usize| -> Option<i128> { inst.operands.get(idx)?.as_imm().map(i128::from) };
    match inst.opcode {
        AArch64Opcode::MulRR => operand_poly(1)?.mul(operand_poly(2)?),
        AArch64Opcode::AddRR => operand_poly(1)?.add(operand_poly(2)?),
        AArch64Opcode::SubRR => operand_poly(1)?.sub(operand_poly(2)?),
        AArch64Opcode::AddRI => operand_poly(1)?.add(Poly::constant(imm(2)?)),
        AArch64Opcode::SubRI => operand_poly(1)?.sub(Poly::constant(imm(2)?)),
        _ => None,
    }
}

/// Classify one term-inst as an AFFINE (degree ≤ 1) polynomial in the IV, or
/// `None` if opaque OR quadratic. Used by the affine strength-reduction path,
/// which deliberately leaves `i*i` as a real multiply (see below).
fn inst_poly(
    func: &MachFunction,
    lp: &NaturalLoop,
    inst: &MachInst,
    iv: VReg,
    coeffs: &HashMap<VReg, Poly>,
    body_defs: &HashSet<VReg>,
) -> Option<Poly> {
    let result = inst_poly_core(func, lp, inst, iv, coeffs, body_defs)?;
    // DEGREE CAP: only affine (degree ≤ 1) polynomials are strength-reduced.
    // A quadratic like `i*i` is left OPAQUE — emitted as a real multiply of the
    // per-lane index `i+k`, exactly as clang does (clang keeps the `i*i`
    // multiplies and only running-adds the linear terms). Reducing `i*i` to a
    // difference engine is sound but *slower* (it trades ~4 cheap multiplies for
    // a dozen adds), so we deliberately bail on it. `a2` is retained purely to
    // DETECT and reject quadratics here.
    if result.a2 != 0 {
        return None;
    }
    Some(result)
}

/// Analyze the term for degree-≤2 polynomial multiplies in the IV. Returns
/// `Some` only when at least one `MulRR` becomes a recurrence.
fn analyze_poly_term(
    func: &MachFunction,
    lp: &NaturalLoop,
    term_insts: &[InstId],
    red_inputs: &[VReg],
    iv: VReg,
    body_defs: &HashSet<VReg>,
    _start: i64,
) -> Option<PolyTermPlan> {
    let mut coeffs: HashMap<VReg, Poly> = HashMap::new();
    coeffs.insert(iv, Poly::iv());

    let mut muls_eliminated = 0usize;
    for &tid in term_insts {
        let inst = func.inst(tid);
        let def = inst.operands.first().and_then(|o| o.as_vreg())?;
        if let Some(p) = inst_poly(func, lp, inst, iv, &coeffs, body_defs) {
            coeffs.insert(def, p);
            if inst.opcode == AArch64Opcode::MulRR {
                muls_eliminated += 1;
            }
        }
    }
    if muls_eliminated == 0 {
        return None;
    }

    // Boundaries: polynomial values consumed by an opaque term-inst, or used as
    // a reduction input.
    let mut boundaries: Vec<VReg> = Vec::new();
    let mut seen: HashSet<VReg> = HashSet::new();
    for &tid in term_insts {
        let inst = func.inst(tid);
        let def = inst.operands.first().and_then(|o| o.as_vreg())?;
        if coeffs.contains_key(&def) {
            continue; // polynomial def — not opaque, not emitted.
        }
        for o in inst.operands.iter().skip(1) {
            if let Some(v) = o.as_vreg()
                && coeffs.contains_key(&v)
                && seen.insert(v)
            {
                boundaries.push(v);
            }
        }
    }
    for &r in red_inputs {
        if coeffs.contains_key(&r) && seen.insert(r) {
            boundaries.push(r);
        }
    }

    Some(PolyTermPlan { coeffs, boundaries })
}

/// Materialise `value` into a fresh vreg using a `Movz`(+`Movk`) chain in the
/// `[dst, imm16(, shift)]` convention isel emits. Returns the dst and the
/// created instruction ids (in order).
fn emit_const(
    func: &mut MachFunction,
    src_loc: Option<SourceLoc>,
    value: u64,
    rc: RegClass,
) -> (VReg, Vec<InstId>) {
    let dst = VReg::new(func.alloc_vreg(), rc);
    let w = rc.size_bits();
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let value = value & mask;
    let chunks = (w / 16) as usize;
    let mut ids: Vec<InstId> = Vec::new();
    for c in 0..chunks {
        let imm = ((value >> (c * 16)) & 0xFFFF) as i64;
        if imm == 0 {
            continue; // zero halfwords are implied by the initial Movz
        }
        let shift = (c * 16) as i64;
        let opcode = if ids.is_empty() {
            AArch64Opcode::Movz
        } else {
            AArch64Opcode::Movk
        };
        let ops = if shift == 0 {
            vec![MachOperand::VReg(dst), MachOperand::Imm(imm)]
        } else {
            vec![
                MachOperand::VReg(dst),
                MachOperand::Imm(imm),
                MachOperand::Imm(shift),
            ]
        };
        ids.push(push_with_loc(func, src_loc, opcode, ops));
    }
    if ids.is_empty() {
        // value == 0
        ids.push(push_with_loc(
            func,
            src_loc,
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(dst), MachOperand::Imm(0)],
        ));
    }
    (dst, ids)
}

fn insert_all_before_terminator(func: &mut MachFunction, block: BlockId, ids: &[InstId]) {
    for &id in ids {
        insert_before_terminator(func, block, id);
    }
}

/// Emit lane `k`'s term computation using the per-lane difference-engine values.
/// Polynomial sub-terms resolve to their carried recurrence vreg; opaque
/// instructions are cloned verbatim with operands remapped to this lane's
/// values. Returns the new instructions (in order) and the remapped reduction
/// input vregs.
fn emit_sr_lane_term(
    func: &mut MachFunction,
    plan: &SplitPlan,
    pp: &PolyTermPlan,
    lane_map: &HashMap<VReg, VReg>,
    src_loc: Option<SourceLoc>,
) -> (Vec<InstId>, Vec<VReg>) {
    let lane_val = |v: VReg| -> Option<VReg> { lane_map.get(&v).copied() };
    let mut body: Vec<InstId> = Vec::new();
    // term-def -> this lane's value vreg (opaque defs get fresh vregs; boundary
    // polynomials map to their per-lane recurrence value).
    let mut map: HashMap<VReg, VReg> = HashMap::new();

    for &tid in &plan.term_insts {
        let (opcode, operands, def) = {
            let inst = func.inst(tid);
            let def = inst
                .operands
                .first()
                .and_then(|o| o.as_vreg())
                .expect("term produces value");
            (inst.opcode, inst.operands.clone(), def)
        };
        if pp.coeffs.contains_key(&def) {
            // Polynomial def: value is carried (if a boundary); record the
            // mapping so opaque consumers resolve it. Non-boundary polys are
            // subsumed by their consumers and emit nothing.
            if let Some(lv) = lane_val(def) {
                map.insert(def, lv);
            }
            continue;
        }
        // Opaque def: clone verbatim, remapping operands to this lane's values.
        let new_def = VReg::new(func.alloc_vreg(), def.class);
        let new_ops: Vec<MachOperand> = operands
            .iter()
            .enumerate()
            .map(|(idx, o)| {
                if idx == 0 {
                    return MachOperand::VReg(new_def);
                }
                if let Some(v) = o.as_vreg() {
                    if let Some(lv) = lane_val(v) {
                        return MachOperand::VReg(lv);
                    }
                    if let Some(&mv) = map.get(&v) {
                        return MachOperand::VReg(mv);
                    }
                }
                o.clone()
            })
            .collect();
        let cid = push_with_loc(func, src_loc, opcode, new_ops);
        body.push(cid);
        map.insert(def, new_def);
    }

    let inputs: Vec<VReg> = plan
        .red_inputs
        .iter()
        .map(|&r| {
            if let Some(lv) = lane_val(r) {
                lv
            } else if let Some(&mv) = map.get(&r) {
                mv
            } else {
                r
            }
        })
        .collect();
    (body, inputs)
}

/// Materialise a loop-invariant constant into the preheader once, caching by
/// (value, class). Used for offsets/steps that exceed the 12-bit `AddRI`
/// immediate range (rare — only for large coefficients).
fn const_reg(
    func: &mut MachFunction,
    src_loc: Option<SourceLoc>,
    preheader: BlockId,
    cache: &mut HashMap<(u64, RegClass), VReg>,
    value: u64,
    rc: RegClass,
    synthesized: &mut Vec<InstId>,
) -> VReg {
    if let Some(&v) = cache.get(&(value, rc)) {
        return v;
    }
    let (v, ids) = emit_const(func, src_loc, value, rc);
    insert_all_before_terminator(func, preheader, &ids);
    synthesized.extend(&ids);
    cache.insert((value, rc), v);
    v
}

/// Emit `dst = base + value` (mod 2^w) into `body`. A zero offset returns `base`
/// unchanged (no instruction). A `value` in `[1,4095]` uses `AddRI`; anything
/// larger materialises the constant into a preheader register (via `const_reg`)
/// and uses `AddRR`. `value` must already be masked to the register width.
#[allow(clippy::too_many_arguments)]
fn emit_add_const(
    func: &mut MachFunction,
    src_loc: Option<SourceLoc>,
    preheader: BlockId,
    cache: &mut HashMap<(u64, RegClass), VReg>,
    base: VReg,
    value: u64,
    rc: RegClass,
    body: &mut Vec<InstId>,
    synthesized: &mut Vec<InstId>,
) -> VReg {
    if value == 0 {
        return base;
    }
    let dst = VReg::new(func.alloc_vreg(), rc);
    let id = if value <= 0xFFF {
        push_with_loc(
            func,
            src_loc,
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(base),
                MachOperand::Imm(value as i64),
            ],
        )
    } else {
        let creg = const_reg(func, src_loc, preheader, cache, value, rc, synthesized);
        push_with_loc(
            func,
            src_loc,
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(base),
                MachOperand::VReg(creg),
            ],
        )
    };
    body.push(id);
    synthesized.push(id);
    dst
}

/// Build the strength-reduced N-wide main-loop latch in place. Each reduced
/// affine boundary sub-term `L(i) = a1·i + a0` carries a SINGLE base value
/// `v = L(i)`; lane `k`'s value is `v + a1·k` (small immediate) and the engine
/// advances `v += a1·N`. The induction variable itself, where used opaquely
/// (e.g. inside a kept `i*i` multiply), is materialised per lane as `i+k` from
/// the real IV — NOT a separate recurrence — so quadratics become
/// `mul(i+k, i+k)` exactly like clang. Register pressure stays low (one carried
/// vreg per reduced sub-term). The original term/reduction stay live in the
/// arena for the runtime tail. Combine/rewire is done by the caller.
fn build_sr_main_latch(
    func: &mut MachFunction,
    plan: &SplitPlan,
    pp: &PolyTermPlan,
    acc_vregs: &[VReg],
    synthesized: &mut Vec<InstId>,
) {
    let n = SPLIT_FACTOR;
    let rc = plan.rc;
    let iv = plan.iv;
    let src_loc = func.inst(plan.reduction_inst).source_loc;
    let start = plan.start as i128;
    let preheader = plan.preheader;
    // Loop-invariant constant cache (only used for offsets/steps > 4095).
    let mut cache: HashMap<(u64, RegClass), VReg> = HashMap::new();

    // --- Phase A: seed each (non-IV) affine boundary's base value `v = L(start)`.
    let mut engines: HashMap<VReg, BoundaryEngine> = HashMap::new();
    for &b in &pp.boundaries {
        if b == iv {
            continue; // the IV is handled as `i+k`, not a recurrence.
        }
        let p = pp.coeffs[&b];
        debug_assert!(
            p.a2 == 0,
            "boundary must be affine (degree cap in inst_poly)"
        );
        let bc = b.class;
        let vinit = mask_to_width(poly_eval(p, start), bc.size_bits());
        let (vreg, vids) = emit_const(func, src_loc, vinit, bc);
        insert_all_before_terminator(func, preheader, &vids);
        synthesized.extend(vids);
        engines.insert(b, BoundaryEngine { p, v: vreg });
    }

    // --- Phase B: rebuild the latch body. ---
    let latch = plan.latch;
    let branch_id = *func
        .block(latch)
        .insts
        .last()
        .expect("latch has a terminator");

    // IV now steps by N (reuse the original increment instruction).
    {
        let inst = func.inst_mut(plan.iv_inc_inst);
        inst.opcode = AArch64Opcode::AddRI;
        inst.operands = vec![
            MachOperand::VReg(plan.iv_next),
            MachOperand::VReg(plan.iv),
            MachOperand::Imm(n as i64),
        ];
    }

    let mut body: Vec<InstId> = Vec::new();
    // (carried dst, next-value src) writeback pairs, emitted after all reads.
    let mut writebacks: Vec<(VReg, VReg)> = Vec::new();

    // Per-boundary per-lane value vregs. For the IV boundary: `i+k` (lane 0 = the
    // IV itself). For an affine engine: `v + a1·k`.
    let mut lane_values: HashMap<VReg, Vec<VReg>> = HashMap::new();
    for &b in &pp.boundaries {
        let mut vals: Vec<VReg> = Vec::with_capacity(n);
        if b == iv {
            for k in 0..n {
                if k == 0 {
                    vals.push(iv);
                } else {
                    let dst = VReg::new(func.alloc_vreg(), iv.class);
                    let id = push_with_loc(
                        func,
                        src_loc,
                        AArch64Opcode::AddRI,
                        vec![
                            MachOperand::VReg(dst),
                            MachOperand::VReg(iv),
                            MachOperand::Imm(k as i64),
                        ],
                    );
                    body.push(id);
                    synthesized.push(id);
                    vals.push(dst);
                }
            }
        } else {
            let (p, v) = {
                let e = &engines[&b];
                (e.p, e.v)
            };
            let bc = b.class;
            let w = bc.size_bits();
            for k in 0..n {
                let off = mask_to_width((k as i128).wrapping_mul(p.a1), w);
                let val = emit_add_const(
                    func,
                    src_loc,
                    preheader,
                    &mut cache,
                    v,
                    off,
                    bc,
                    &mut body,
                    synthesized,
                );
                vals.push(val);
            }
        }
        lane_values.insert(b, vals);
    }

    // Lane bodies: opaque term + reduction, reading the per-lane values.
    for k in 0..n {
        let mut lane_map: HashMap<VReg, VReg> = HashMap::new();
        for &b in &pp.boundaries {
            lane_map.insert(b, lane_values[&b][k]);
        }
        let (lane_body, red_inputs_k) = emit_sr_lane_term(func, plan, pp, &lane_map, src_loc);
        for &id in &lane_body {
            body.push(id);
        }
        synthesized.extend(lane_body);
        let acck = acc_vregs[k];
        let acck_next = VReg::new(func.alloc_vreg(), rc);
        let red = emit_reduction(func, plan, acck_next, acck, &red_inputs_k, src_loc);
        body.push(red);
        synthesized.push(red);
        writebacks.push((acck, acck_next));
    }

    // Advance each affine engine: `v += a1·N`. (The IV advances via iv_inc.)
    for &b in &pp.boundaries {
        if b == iv {
            continue;
        }
        let (p, v) = {
            let e = &engines[&b];
            (e.p, e.v)
        };
        let bc = b.class;
        let step = mask_to_width(p.a1.wrapping_mul(n as i128), bc.size_bits());
        let vnext = emit_add_const(
            func,
            src_loc,
            preheader,
            &mut cache,
            v,
            step,
            bc,
            &mut body,
            synthesized,
        );
        writebacks.push((v, vnext));
    }

    // IV increment (reused) computes iv_next.
    body.push(plan.iv_inc_inst);

    // Writebacks: carried acc/recurrence copies, then the reused IV writeback.
    for &(dst, src) in &writebacks {
        let mv = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(dst), MachOperand::VReg(src)],
        );
        body.push(mv);
        synthesized.push(mv);
    }
    body.push(plan.iv_writeback);
    body.push(branch_id);

    func.block_mut(latch).insts = body;
}

// ---------------------------------------------------------------------------
// Transform
// ---------------------------------------------------------------------------

fn reduction_split_pass_id() -> PassId {
    PassId::new("reduction-split")
}

/// Dispatch to the constant-exact or runtime split-with-tail rewrite.
fn apply(func: &mut MachFunction, plan: &SplitPlan, provenance: Option<&mut ProvenanceMap>) {
    match plan.mode {
        SplitMode::Constant => apply_constant(func, plan, provenance),
        SplitMode::Runtime { limit, cc } => apply_runtime(func, plan, limit, cc, provenance),
    }
}

/// Best-effort provenance: mark the rewritten IV/reduction as in-place transforms
/// and attribute every synthesized instruction to the reduction's origin.
fn record_provenance(
    provenance: &mut Option<&mut ProvenanceMap>,
    plan: &SplitPlan,
    synthesized: &[InstId],
) {
    if let Some(prov) = provenance.as_deref_mut() {
        let pass = reduction_split_pass_id();
        prov.record_in_place_transform(plan.iv_inc_inst, pass.clone());
        prov.record_in_place_transform(plan.reduction_inst, pass.clone());
        for &sid in synthesized {
            prov.record_clone(plan.reduction_inst, sid, pass.clone());
        }
    }
}

/// Constant-trip rewrite (v1): N accumulators, IV steps by N, balanced combine on
/// the exit edge. The trip count is an exact multiple of N, so no guard or tail is
/// needed — every iteration processes exactly N valid indices.
fn apply_constant(
    func: &mut MachFunction,
    plan: &SplitPlan,
    mut provenance: Option<&mut ProvenanceMap>,
) {
    let n = SPLIT_FACTOR;
    let rc = plan.rc;
    let src_loc = func.inst(plan.reduction_inst).source_loc;
    let identity = plan.identity;

    let mut synthesized: Vec<InstId> = Vec::new();

    // 1. New accumulators acc1..accN-1: materialize identity in the preheader
    //    (a fresh loop-carried var initialised to the op identity).
    let mut acc_vregs: Vec<VReg> = vec![plan.acc]; // acc0
    for _ in 1..n {
        let accj = VReg::new(func.alloc_vreg(), rc);
        let init = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(accj), MachOperand::Imm(identity)],
        );
        insert_before_terminator(func, plan.preheader, init);
        synthesized.push(init);
        acc_vregs.push(accj);
    }

    // 2+3. Latch. If the term reduces to polynomial recurrences, emit the
    //    strength-reduced multiply-free main loop (per-lane difference engines,
    //    IV stepped by N). Otherwise clone the term verbatim per lane (the
    //    original transform), splicing lanes 1..N-1 before the IV writeback and
    //    stepping the IV by N.
    if let Some(pp) = &plan.poly {
        build_sr_main_latch(func, plan, pp, &acc_vregs, &mut synthesized);
        // 4. Combine block on the header->exit edge; rewire liveouts.
        build_combine_and_rewire(func, plan, &acc_vregs, &mut synthesized, src_loc);
        record_provenance(&mut provenance, plan, &synthesized);
        return;
    }

    let mut new_latch_insts: Vec<InstId> = Vec::new();
    for (k, &acc_k) in acc_vregs.iter().enumerate().take(n).skip(1) {
        // i + k
        let i_pk = VReg::new(func.alloc_vreg(), plan.iv_class);
        let inc = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(i_pk),
                MachOperand::VReg(plan.iv),
                MachOperand::Imm(k as i64),
            ],
        );
        new_latch_insts.push(inc);
        synthesized.push(inc);

        // Clone the term computation with rename {iv -> i_pk, def -> fresh}.
        let mut rename: HashMap<VReg, VReg> = HashMap::new();
        rename.insert(plan.iv, i_pk);
        for &tid in &plan.term_insts {
            let (opcode, operands, def) = {
                let inst = func.inst(tid);
                let def = inst.operands[0].as_vreg().expect("term produces value");
                (inst.opcode, inst.operands.clone(), def)
            };
            let new_def = VReg::new(func.alloc_vreg(), def.class);
            rename.insert(def, new_def);
            let new_ops: Vec<MachOperand> = operands
                .iter()
                .enumerate()
                .map(|(idx, o)| {
                    if idx == 0 {
                        return MachOperand::VReg(new_def);
                    }
                    if let MachOperand::VReg(v) = o
                        && let Some(&r) = rename.get(v)
                    {
                        return MachOperand::VReg(r);
                    }
                    o.clone()
                })
                .collect();
            let cid = push_with_loc(func, src_loc, opcode, new_ops);
            new_latch_insts.push(cid);
            synthesized.push(cid);
        }

        // Remap the reduction inputs for this copy (iv -> i+k, term defs ->
        // their clones, invariants unchanged).
        let inputs_k: Vec<VReg> = plan
            .red_inputs
            .iter()
            .map(|&v| rename.get(&v).copied().unwrap_or(v))
            .collect();

        // acck_next = <reduction>(acck, inputs_k...); MovR acck, acck_next.
        let acck_next = VReg::new(func.alloc_vreg(), rc);
        let red = match plan.red_kind {
            RedKind::Assoc(op) => push_with_loc(
                func,
                src_loc,
                op,
                vec![
                    MachOperand::VReg(acck_next),
                    MachOperand::VReg(acc_k),
                    MachOperand::VReg(inputs_k[0]),
                ],
            ),
            RedKind::Madd => push_with_loc(
                func,
                src_loc,
                AArch64Opcode::Madd,
                vec![
                    MachOperand::VReg(acck_next),
                    MachOperand::VReg(inputs_k[0]),
                    MachOperand::VReg(inputs_k[1]),
                    MachOperand::VReg(acc_k),
                ],
            ),
        };
        new_latch_insts.push(red);
        synthesized.push(red);
        let wb = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(acc_k), MachOperand::VReg(acck_next)],
        );
        new_latch_insts.push(wb);
        synthesized.push(wb);
    }

    // Splice the new latch instructions in just before the IV writeback.
    let iv_wb_pos = func
        .block(plan.latch)
        .insts
        .iter()
        .position(|&id| id == plan.iv_writeback)
        .expect("iv writeback in latch");
    func.block_mut(plan.latch)
        .insts
        .splice(iv_wb_pos..iv_wb_pos, new_latch_insts);

    // 3. IV steps by N now: rewrite the increment to `AddRI iv_next, iv, #N`.
    {
        let inst = func.inst_mut(plan.iv_inc_inst);
        inst.opcode = AArch64Opcode::AddRI;
        inst.operands = vec![
            MachOperand::VReg(plan.iv_next),
            MachOperand::VReg(plan.iv),
            MachOperand::Imm(n as i64),
        ];
    }

    // 4. Combine block on the header->exit edge; rewire liveouts.
    build_combine_and_rewire(func, plan, &acc_vregs, &mut synthesized, src_loc);

    // 5. Provenance (best effort).
    if let Some(prov) = provenance {
        let pass = reduction_split_pass_id();
        prov.record_in_place_transform(plan.iv_inc_inst, pass.clone());
        prov.record_in_place_transform(plan.reduction_inst, pass.clone());
        for &sid in &synthesized {
            prov.record_clone(plan.reduction_inst, sid, pass.clone());
        }
    }
}

/// Runtime-trip rewrite: a guarded N-wide main loop feeding a balanced combine,
/// then a peeled sequential remainder tail. See the RUNTIME section of the module
/// docs for the bound-safety argument. Every branch here is fail-closed: the
/// preheader guard skips the main loop whenever the bound could be unsafe, and the
/// tail guards each remainder element with its own `iv < limit` test.
#[allow(clippy::too_many_lines)]
fn apply_runtime(
    func: &mut MachFunction,
    plan: &SplitPlan,
    limit: VReg,
    cc: i64,
    provenance: Option<&mut ProvenanceMap>,
) {
    let n = SPLIT_FACTOR;
    let rc = plan.rc;
    let src_loc = func.inst(plan.reduction_inst).source_loc;
    let identity = plan.identity;
    let mut synthesized: Vec<InstId> = Vec::new();

    // 1. Extra accumulators acc1..accN-1 seeded to the op identity, in preheader.
    let mut acc_vregs: Vec<VReg> = vec![plan.acc];
    for _ in 1..n {
        let accj = VReg::new(func.alloc_vreg(), rc);
        let init = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(accj), MachOperand::Imm(identity)],
        );
        insert_before_terminator(func, plan.preheader, init);
        synthesized.push(init);
        acc_vregs.push(accj);
    }

    // 2. main_bound = limit - (N-1), in the preheader. The main loop runs while
    //    `iv < main_bound`, i.e. while at least N iterations remain. (Bound safety
    //    is enforced by the guard in step 8 — see module docs.)
    let main_bound = VReg::new(func.alloc_vreg(), plan.iv_class);
    let sub = push_with_loc(
        func,
        src_loc,
        AArch64Opcode::SubRI,
        vec![
            MachOperand::VReg(main_bound),
            MachOperand::VReg(limit),
            MachOperand::Imm((n - 1) as i64),
        ],
    );
    insert_before_terminator(func, plan.preheader, sub);
    synthesized.push(sub);

    // 3+4. Main-loop latch. When the term reduces to polynomial recurrences,
    //    emit the strength-reduced multiply-free main loop (per-lane difference
    //    engines, IV stepped by N); the ORIGINAL term instructions stay live in
    //    the arena so the mul-based remainder tail (step 6) can still clone them
    //    verbatim. Otherwise clone the term per lane exactly as before.
    if let Some(pp) = &plan.poly {
        build_sr_main_latch(func, plan, pp, &acc_vregs, &mut synthesized);
    } else {
        let mut new_latch_insts: Vec<InstId> = Vec::new();
        for (k, &acc_k) in acc_vregs.iter().enumerate().take(n).skip(1) {
            let i_pk = VReg::new(func.alloc_vreg(), plan.iv_class);
            let inc = push_with_loc(
                func,
                src_loc,
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::VReg(i_pk),
                    MachOperand::VReg(plan.iv),
                    MachOperand::Imm(k as i64),
                ],
            );
            new_latch_insts.push(inc);
            synthesized.push(inc);

            let mut rename: HashMap<VReg, VReg> = HashMap::new();
            rename.insert(plan.iv, i_pk);
            let cloned = clone_term(func, &plan.term_insts, &mut rename, src_loc);
            for &cid in &cloned {
                new_latch_insts.push(cid);
                synthesized.push(cid);
            }
            let inputs_k: Vec<VReg> = plan
                .red_inputs
                .iter()
                .map(|&v| rename.get(&v).copied().unwrap_or(v))
                .collect();

            let acck_next = VReg::new(func.alloc_vreg(), rc);
            let red = emit_reduction(func, plan, acck_next, acc_k, &inputs_k, src_loc);
            new_latch_insts.push(red);
            synthesized.push(red);
            let wb = push_with_loc(
                func,
                src_loc,
                AArch64Opcode::MovR,
                vec![MachOperand::VReg(acc_k), MachOperand::VReg(acck_next)],
            );
            new_latch_insts.push(wb);
            synthesized.push(wb);
        }
        let iv_wb_pos = func
            .block(plan.latch)
            .insts
            .iter()
            .position(|&id| id == plan.iv_writeback)
            .expect("iv writeback in latch");
        func.block_mut(plan.latch)
            .insts
            .splice(iv_wb_pos..iv_wb_pos, new_latch_insts);

        // IV steps by N now.
        let inst = func.inst_mut(plan.iv_inc_inst);
        inst.opcode = AArch64Opcode::AddRI;
        inst.operands = vec![
            MachOperand::VReg(plan.iv_next),
            MachOperand::VReg(plan.iv),
            MachOperand::Imm(n as i64),
        ];
    }

    // 5. Combine block: balanced tree over acc0..accN-1 -> acc_final.
    let combine = func.create_block();
    let acc_final =
        build_balanced_combine(func, plan, &acc_vregs, combine, &mut synthesized, src_loc);

    // 6. Peeled remainder tail: for each of the N-1 possible leftover elements a
    //    (check, body) pair — `check` guards `iv < limit`, `body` does one
    //    reduction step and increments the IV. All branch targets are distinct
    //    blocks (no critical duplicate-succ), and there is NO back-edge, so the
    //    tail is not a loop and can never be re-recognized (idempotence).
    let mut checks: Vec<BlockId> = Vec::new();
    let mut bodies: Vec<BlockId> = Vec::new();
    for _ in 0..(n - 1) {
        checks.push(func.create_block());
        bodies.push(func.create_block());
    }
    let first_check = checks[0];
    let br_combine = push_with_loc(
        func,
        src_loc,
        AArch64Opcode::B,
        vec![MachOperand::Block(first_check)],
    );
    func.append_inst(combine, br_combine);
    synthesized.push(br_combine);

    for k in 0..(n - 1) {
        let check = checks[k];
        let body = bodies[k];
        let next = if k + 1 < n - 1 {
            checks[k + 1]
        } else {
            plan.exit
        };

        // check: cmp iv, limit ; BCond CC exit ; B body
        let cmp = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::CmpRR,
            vec![MachOperand::VReg(plan.iv), MachOperand::VReg(limit)],
        );
        func.append_inst(check, cmp);
        synthesized.push(cmp);
        let bc = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(cc), MachOperand::Block(plan.exit)],
        );
        func.append_inst(check, bc);
        synthesized.push(bc);
        let bbody = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::B,
            vec![MachOperand::Block(body)],
        );
        func.append_inst(check, bbody);
        synthesized.push(bbody);

        // body: <term(iv)> ; acc_final = op(acc_final, term) ; iv += 1 ; B next
        let mut rename: HashMap<VReg, VReg> = HashMap::new(); // iv maps to itself
        let cloned = clone_term(func, &plan.term_insts, &mut rename, src_loc);
        for &cid in &cloned {
            func.append_inst(body, cid);
            synthesized.push(cid);
        }
        let inputs: Vec<VReg> = plan
            .red_inputs
            .iter()
            .map(|&v| rename.get(&v).copied().unwrap_or(v))
            .collect();
        let acc_next = VReg::new(func.alloc_vreg(), rc);
        let red = emit_reduction(func, plan, acc_next, acc_final, &inputs, src_loc);
        func.append_inst(body, red);
        synthesized.push(red);
        let wb = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(acc_final), MachOperand::VReg(acc_next)],
        );
        func.append_inst(body, wb);
        synthesized.push(wb);
        let iv_n = VReg::new(func.alloc_vreg(), plan.iv_class);
        let ivinc = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(iv_n),
                MachOperand::VReg(plan.iv),
                MachOperand::Imm(1),
            ],
        );
        func.append_inst(body, ivinc);
        synthesized.push(ivinc);
        let ivwb = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(plan.iv), MachOperand::VReg(iv_n)],
        );
        func.append_inst(body, ivwb);
        synthesized.push(ivwb);
        let bnext = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::B,
            vec![MachOperand::Block(next)],
        );
        func.append_inst(body, bnext);
        synthesized.push(bnext);
    }

    // 7. Rewrite the header: compare `iv` against `main_bound` (not `limit`), and
    //    redirect the exit edge to the combine block.
    {
        let header_insts = func.block(plan.header).insts.clone();
        let cmp_id = header_insts[0];
        func.inst_mut(cmp_id).operands[1] = MachOperand::VReg(main_bound);
        let bc_id = header_insts[1];
        for op in func.inst_mut(bc_id).operands.iter_mut() {
            if let MachOperand::Block(b) = op
                && *b == plan.exit
            {
                *b = combine;
            }
        }
    }

    // 8. Preheader guard: `cmp main_bound, limit ; BCond CC combine` inserted just
    //    before the preheader's terminating `B header`. Branches to `combine`
    //    (skipping the N-wide main loop) whenever `main_bound >= limit` — i.e. the
    //    `limit-(N-1)` subtraction wrapped, or fewer than N iterations exist. On
    //    that path acc1..N-1 hold the op identity, so combine yields acc0 unchanged
    //    and the tail runs the entire [start,limit) range sequentially.
    {
        let gcmp = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::CmpRR,
            vec![MachOperand::VReg(main_bound), MachOperand::VReg(limit)],
        );
        insert_before_terminator(func, plan.preheader, gcmp);
        synthesized.push(gcmp);
        let gbc = push_with_loc(
            func,
            src_loc,
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(cc), MachOperand::Block(combine)],
        );
        insert_before_terminator(func, plan.preheader, gbc);
        synthesized.push(gbc);
    }

    // 9. CFG edges & block order.
    //    preheader -> combine (guard); preheader -> header already exists.
    func.block_mut(plan.preheader).succs.insert(0, combine);
    func.block_mut(combine).preds.push(plan.preheader);
    //    header -> combine replaces header -> exit.
    for s in func.block_mut(plan.header).succs.iter_mut() {
        if *s == plan.exit {
            *s = combine;
        }
    }
    func.block_mut(combine).preds.push(plan.header);
    //    exit no longer has the header as a predecessor.
    func.block_mut(plan.exit)
        .preds
        .retain(|&p| p != plan.header);
    //    combine -> first check ; check_k -> {exit, body_k} ; body_k -> next.
    func.add_edge(combine, first_check);
    for k in 0..(n - 1) {
        func.add_edge(checks[k], plan.exit);
        func.add_edge(checks[k], bodies[k]);
        let next = if k + 1 < n - 1 {
            checks[k + 1]
        } else {
            plan.exit
        };
        func.add_edge(bodies[k], next);
    }
    //    Place combine + the tail blocks right before exit in block_order.
    let new_blocks: Vec<BlockId> = std::iter::once(combine)
        .chain((0..(n - 1)).flat_map(|k| [checks[k], bodies[k]]))
        .collect();
    for &b in &new_blocks {
        func.block_order.retain(|&x| x != b);
    }
    let pos = func
        .block_order
        .iter()
        .position(|&b| b == plan.exit)
        .unwrap_or(func.block_order.len());
    for (i, &b) in new_blocks.iter().enumerate() {
        func.block_order.insert(pos + i, b);
    }

    // 10. Rewire out-of-loop reads of acc0 -> acc_final. The loop body, the
    //     combine (reads acc0..N-1), and the tail blocks (use acc_final by
    //     construction) are excluded; every other read of acc0 is a liveout and
    //     becomes acc_final, which after the tail holds the fully-reduced value.
    let mut exclude: HashSet<BlockId> = HashSet::new();
    exclude.insert(plan.header);
    exclude.insert(plan.latch);
    exclude.insert(combine);
    for k in 0..(n - 1) {
        exclude.insert(checks[k]);
        exclude.insert(bodies[k]);
    }
    let blocks: Vec<BlockId> = func.block_order.clone();
    for bid in blocks {
        if exclude.contains(&bid) {
            continue;
        }
        let inst_ids: Vec<InstId> = func.block(bid).insts.clone();
        for iid in inst_ids {
            let produces = inst_produces_value(func.inst(iid));
            for (idx, op) in func.inst_mut(iid).operands.iter_mut().enumerate() {
                if produces && idx == 0 {
                    continue;
                }
                if op.as_vreg() == Some(plan.acc) {
                    *op = MachOperand::VReg(acc_final);
                }
            }
        }
    }

    // 11. Provenance (best effort).
    if let Some(prov) = provenance {
        let pass = reduction_split_pass_id();
        prov.record_in_place_transform(plan.iv_inc_inst, pass.clone());
        prov.record_in_place_transform(plan.reduction_inst, pass.clone());
        for &sid in &synthesized {
            prov.record_clone(plan.reduction_inst, sid, pass.clone());
        }
    }
}

/// Clone the ordered term-computation instructions, renaming `def -> fresh` for
/// every internal def (so results are independent) and applying any renames
/// already present in `rename` (e.g. `iv -> i+k` for a lane copy). Loop-invariant
/// operands and (for the tail) the IV itself pass through unchanged. Returns the
/// new instruction ids in order; `rename` is updated with each def's clone.
fn clone_term(
    func: &mut MachFunction,
    term_insts: &[InstId],
    rename: &mut HashMap<VReg, VReg>,
    src_loc: Option<SourceLoc>,
) -> Vec<InstId> {
    let mut out = Vec::with_capacity(term_insts.len());
    for &tid in term_insts {
        let (opcode, operands, def) = {
            let inst = func.inst(tid);
            let def = inst.operands[0].as_vreg().expect("term produces value");
            (inst.opcode, inst.operands.clone(), def)
        };
        let new_def = VReg::new(func.alloc_vreg(), def.class);
        rename.insert(def, new_def);
        let new_ops: Vec<MachOperand> = operands
            .iter()
            .enumerate()
            .map(|(idx, o)| {
                if idx == 0 {
                    return MachOperand::VReg(new_def);
                }
                if let MachOperand::VReg(v) = o
                    && let Some(&r) = rename.get(v)
                {
                    return MachOperand::VReg(r);
                }
                o.clone()
            })
            .collect();
        let cid = push_with_loc(func, src_loc, opcode, new_ops);
        out.push(cid);
    }
    out
}

/// Emit one reduction step `dst = acc_in <op> term` (Assoc) or
/// `dst = Madd(a, b, acc_in)` (fused sum-of-products). `inputs` is the remapped
/// reduction input list (`[term]` for Assoc, `[a, b]` for Madd).
fn emit_reduction(
    func: &mut MachFunction,
    plan: &SplitPlan,
    dst: VReg,
    acc_in: VReg,
    inputs: &[VReg],
    src_loc: Option<SourceLoc>,
) -> InstId {
    match plan.red_kind {
        RedKind::Assoc(op) => push_with_loc(
            func,
            src_loc,
            op,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(acc_in),
                MachOperand::VReg(inputs[0]),
            ],
        ),
        RedKind::Madd => push_with_loc(
            func,
            src_loc,
            AArch64Opcode::Madd,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(inputs[0]),
                MachOperand::VReg(inputs[1]),
                MachOperand::VReg(acc_in),
            ],
        ),
    }
}

/// Emit the balanced-tree combine over `acc_vregs` into `block` (no terminator),
/// returning the final combined vreg. Matches the tree shape in
/// `build_combine_and_rewire` and the proof's `split_combine`.
fn build_balanced_combine(
    func: &mut MachFunction,
    plan: &SplitPlan,
    acc_vregs: &[VReg],
    block: BlockId,
    synthesized: &mut Vec<InstId>,
    src_loc: Option<SourceLoc>,
) -> VReg {
    let rc = plan.rc;
    let mut level: Vec<VReg> = acc_vregs.to_vec();
    while level.len() > 1 {
        let mut next: Vec<VReg> = Vec::new();
        let mut i = 0;
        while i + 1 < level.len() {
            let d = VReg::new(func.alloc_vreg(), rc);
            let id = push_with_loc(
                func,
                src_loc,
                plan.combine_op,
                vec![
                    MachOperand::VReg(d),
                    MachOperand::VReg(level[i]),
                    MachOperand::VReg(level[i + 1]),
                ],
            );
            func.append_inst(block, id);
            synthesized.push(id);
            next.push(d);
            i += 2;
        }
        if i < level.len() {
            next.push(level[i]);
        }
        level = next;
    }
    level[0]
}

/// Insert the balanced-tree combine into a fresh block spliced on the
/// header->exit edge, then rewire every out-of-loop use of `acc0` to the
/// combined result. Returns the `acc_final` vreg.
fn build_combine_and_rewire(
    func: &mut MachFunction,
    plan: &SplitPlan,
    acc_vregs: &[VReg],
    synthesized: &mut Vec<InstId>,
    src_loc: Option<SourceLoc>,
) -> VReg {
    let rc = plan.rc;
    let combine = func.create_block();

    // Balanced-tree combine over acc0..accN-1.
    let mut level: Vec<VReg> = acc_vregs.to_vec();
    while level.len() > 1 {
        let mut next: Vec<VReg> = Vec::new();
        let mut i = 0;
        while i + 1 < level.len() {
            let d = VReg::new(func.alloc_vreg(), rc);
            let id = push_with_loc(
                func,
                src_loc,
                plan.combine_op,
                vec![
                    MachOperand::VReg(d),
                    MachOperand::VReg(level[i]),
                    MachOperand::VReg(level[i + 1]),
                ],
            );
            func.append_inst(combine, id);
            synthesized.push(id);
            next.push(d);
            i += 2;
        }
        if i < level.len() {
            next.push(level[i]);
        }
        level = next;
    }
    let acc_final = level[0];

    let br = push_with_loc(
        func,
        src_loc,
        AArch64Opcode::B,
        vec![MachOperand::Block(plan.exit)],
    );
    func.append_inst(combine, br);
    synthesized.push(br);

    // Splice combine on the header->exit edge.
    let header_insts = func.block(plan.header).insts.clone();
    for iid in header_insts {
        for op in &mut func.inst_mut(iid).operands {
            if let MachOperand::Block(b) = op
                && *b == plan.exit
            {
                *b = combine;
            }
        }
    }
    for s in func.block_mut(plan.header).succs.iter_mut() {
        if *s == plan.exit {
            *s = combine;
        }
    }
    for p in func.block_mut(plan.exit).preds.iter_mut() {
        if *p == plan.header {
            *p = combine;
        }
    }
    func.block_mut(combine).preds.push(plan.header);
    func.block_mut(combine).succs.push(plan.exit);

    // Place combine right before exit in block_order.
    let pos = func
        .block_order
        .iter()
        .position(|&b| b == plan.exit)
        .unwrap_or(func.block_order.len());
    func.block_order.retain(|&b| b != combine);
    func.block_order.insert(pos, combine);

    // Rewrite every out-of-loop use of acc0 -> acc_final (skip the loop body and
    // the combine block, whose combine ops legitimately read acc0..accN-1).
    let blocks: Vec<BlockId> = func.block_order.clone();
    for bid in blocks {
        if plan.header == bid || plan.latch == bid || bid == combine {
            continue;
        }
        let inst_ids: Vec<InstId> = func.block(bid).insts.clone();
        for iid in inst_ids {
            // Rewrite only READS of acc0. Operand 0 of a value producer is the
            // DEF slot (e.g. acc0's own preheader init `MovR acc, #0`) and must
            // never be rewritten — doing so would leave acc0 uninitialised.
            let produces = inst_produces_value(func.inst(iid));
            for (idx, op) in func.inst_mut(iid).operands.iter_mut().enumerate() {
                if produces && idx == 0 {
                    continue;
                }
                if op.as_vreg() == Some(plan.acc) {
                    *op = MachOperand::VReg(acc_final);
                }
            }
        }
    }

    acc_final
}

fn push_with_loc(
    func: &mut MachFunction,
    src_loc: Option<SourceLoc>,
    opcode: AArch64Opcode,
    operands: Vec<MachOperand>,
) -> InstId {
    let mut inst = MachInst::new(opcode, operands);
    inst.source_loc = src_loc;
    func.push_inst(inst)
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
// Debug dump
// ---------------------------------------------------------------------------

fn dump_all(func: &MachFunction) {
    for &bid in &func.block_order {
        eprintln!(
            "  block {:?} preds={:?} succs={:?}",
            bid,
            func.block(bid).preds,
            func.block(bid).succs
        );
        for &iid in &func.block(bid).insts {
            eprintln!("    {:?}", func.inst(iid));
        }
    }
}

fn dump_loop(func: &MachFunction, lp: &NaturalLoop) {
    eprintln!(
        "  loop header={:?} latch={:?} preheader={:?} body={:?}",
        lp.header, lp.latch, lp.preheader, lp.body
    );
    let mut blocks: Vec<BlockId> = lp.body.iter().copied().collect();
    if let Some(ph) = lp.preheader {
        blocks.push(ph);
    }
    blocks.sort_by_key(|b| b.0);
    for bid in blocks {
        eprintln!(
            "  block {:?} preds={:?} succs={:?}",
            bid,
            func.block(bid).preds,
            func.block(bid).succs
        );
        for &iid in &func.block(bid).insts {
            eprintln!("    {:?}", func.inst(iid));
        }
    }
}

// ---------------------------------------------------------------------------
// Closed-form (Faulhaber) recognizer + rewrite
// ---------------------------------------------------------------------------

/// Modular inverse of 3 mod 2^64: `3 · INV3 ≡ 1 (mod 2^64)`.
const INV3_U64: u64 = 0xAAAA_AAAA_AAAA_AAAB;

/// AArch64 condition codes for the header branch polarity analysis.
const CC_LO: i64 = 3; // unsigned <
const CC_LT: i64 = 11; // signed <

/// A recognized closed-form-eligible reduction: a pure-polynomial ADD/Madd
/// reduction with a RUNTIME limit and a constant, non-negative start. All fields
/// are established by construction in `recognize_closed_form`.
struct ClosedForm {
    header: BlockId,
    latch: BlockId,
    preheader: BlockId,
    exit: BlockId,
    /// Accumulator (loop-carried) vreg — holds `acc_init` in the preheader.
    acc: VReg,
    /// Register class (64-bit — the S1/S2 identities are mod 2^64).
    rc: RegClass,
    /// Constant, non-negative loop start (`iv`'s init).
    start: i64,
    /// The runtime loop limit `n` (the header compares `iv` against it).
    limit: VReg,
    /// EXIT condition-code (`CC_GE`/`CC_HS`): the loop runs 0 times iff
    /// `start ≥ limit` under `cc`. Reproduces the loop's own entry test.
    cc: i64,
    /// The term as a degree-≤2 polynomial `P(i) = a2·i² + a1·i + a0` (exact
    /// i128 coefficients).
    poly: Poly,
    /// The reduction instruction (`acc_next = op(acc, term)`) — the provenance
    /// anchor for the synthesized closed-form code.
    reduction_inst: InstId,
    /// Source location carried onto the synthesized closed-form code.
    src_loc: Option<SourceLoc>,
}

/// Recognize a loop the closed-form rewrite can DELETE. This is a SELF-CONTAINED
/// recognizer (it does NOT reuse `ReductionSplit::recognize`, whose header shape
/// assumes an "exit-if-≥" branch and whose `apply` depends on that shape): it
/// accepts the loop in the exact form the pipeline produces right before
/// `LoopLatchLayoutCombine` — a clean, non-rotated, copy-form register loop whose
/// header test is a "continue-if-<" branch. It imposes the closed-form gates:
///  * ADD or fused-`Madd` reduction whose term is a pure polynomial in the IV;
///  * a RUNTIME limit (constant trips stay with `ReductionSplit`'s exact split);
///  * 64-bit accumulator/IV/limit (the S1/S2 identities are mod 2^64);
///  * a constant start `≥ 0` (`F(k) = Σ_{i<k} P` is only defined for `k ≥ 0`);
///  * the term resolves to a degree-≤2 polynomial in the IV — every instruction
///    feeding it is analyzable arithmetic, no opaque ops (xor/or/and/shift/…);
///  * a clean single-`B header` preheader whose retarget deletes the loop.
///
/// Anything else ⇒ BAIL (leave the loop for `ReductionSplit`).
fn recognize_closed_form(func: &MachFunction, lp: &NaturalLoop) -> Option<ClosedForm> {
    let preheader = lp.preheader?;
    let header = lp.header;
    let latch = lp.latch;

    // -- CFG shape: body is exactly {header, latch}, header != latch. --
    if header == latch
        || lp.body.len() != 2
        || !lp.body.contains(&header)
        || !lp.body.contains(&latch)
    {
        return None;
    }
    // Latch's only successor is the header (the back-edge).
    if func.block(latch).succs != vec![header] {
        return None;
    }
    // Header has exactly two successors: the latch and a single exit block.
    let hsuccs = func.block(header).succs.clone();
    if hsuccs.len() != 2 {
        return None;
    }
    let exits: Vec<BlockId> = hsuccs
        .iter()
        .copied()
        .filter(|s| !lp.body.contains(s))
        .collect();
    if exits.len() != 1 {
        return None;
    }
    let exit = exits[0];
    if !hsuccs.contains(&latch) {
        return None;
    }
    // The exit's only predecessor is the header (single-entry exit).
    if func.block(exit).preds != vec![header] {
        return None;
    }
    // The loop is entered ONLY through the preheader: the header's preds are
    // exactly {preheader, latch}. Then retargeting preheader→exit removes every
    // path into the loop, so header/latch DCE cleanly.
    {
        let mut hp = func.block(header).preds.clone();
        hp.sort_by_key(|b| b.0);
        let mut ex = vec![preheader, latch];
        ex.sort_by_key(|b| b.0);
        if hp != ex {
            return None;
        }
    }
    // Clean preheader: single successor (header), ending in `B header`, which we
    // retarget to the exit to delete the loop.
    if func.block(preheader).succs != vec![header] {
        return None;
    }
    let ph_term = *func.block(preheader).insts.last()?;
    {
        let ti = func.inst(ph_term);
        if ti.opcode != AArch64Opcode::B
            || !matches!(ti.operands.first(), Some(MachOperand::Block(t)) if *t == header)
        {
            return None;
        }
    }

    // -- Whole body must be pure (register reduction: no load/store/call). --
    for &bid in &[header, latch] {
        for &iid in &func.block(bid).insts {
            if opcode_effect(func.inst(iid).opcode) != MemoryEffect::Pure {
                return None;
            }
        }
    }

    // -- Loop-carried variables via latch writebacks. --
    let preheader_defs = block_value_defs(func, preheader);
    let mut carried: Vec<(VReg, VReg, InstId)> = Vec::new();
    for &iid in &func.block(latch).insts {
        let inst = func.inst(iid);
        if !matches!(inst.opcode, AArch64Opcode::MovR | AArch64Opcode::Copy) {
            continue;
        }
        let (Some(dst), Some(src)) = (
            inst.operands.first().and_then(|o| o.as_vreg()),
            inst.operands.get(1).and_then(|o| o.as_vreg()),
        ) else {
            continue;
        };
        if dst == src || !preheader_defs.contains(&dst) {
            continue;
        }
        if count_defs_in_block(func, latch, dst) != 1 {
            return None;
        }
        carried.push((dst, src, iid));
    }
    if carried.len() != 2 {
        return None;
    }

    // -- Classify the two carried vars as IV and accumulator. The IV is
    //    DEFINITIVELY the one the header compares against the limit — using the
    //    header disambiguates a constant-add reduction `acc = acc + 7` (which
    //    otherwise looks exactly like an IV with step 7) from the real IV. --
    let hdr = &func.block(header).insts;
    if hdr.len() != 3 {
        return None;
    }
    let cmp = func.inst(hdr[0]);
    if cmp.opcode != AArch64Opcode::CmpRR {
        return None;
    }
    let iv_vreg = cmp.operands.first().and_then(|o| o.as_vreg())?;
    let &(iv, iv_next, iv_writeback) = carried.iter().find(|(d, _, _)| *d == iv_vreg)?;
    let &(acc, acc_next, _) = carried.iter().find(|(d, _, _)| *d != iv_vreg)?;
    if iv == acc {
        return None;
    }

    // IV: its writeback source is `iv + 1`.
    let iv_inc_inst = latch_unique_def(func, latch, iv_next)?;
    if increment_step(func, lp, func.inst(iv_inc_inst), iv) != Some(1) {
        return None;
    }

    // ACC: its writeback source is `AddRR(acc, term)` (Assoc add) or a fused
    // `Madd(a, b, acc)` (== a·b + acc).
    let reduction_inst = latch_unique_def(func, latch, acc_next)?;
    let acc_def = func.inst(reduction_inst);
    let (red_kind, red_inputs) =
        if acc_def.opcode == AArch64Opcode::AddRR && acc_def.operands.len() >= 3 {
            let a = acc_def.operands[1].as_vreg();
            let b = acc_def.operands[2].as_vreg();
            let term = if a == Some(acc) {
                b
            } else if b == Some(acc) {
                a
            } else {
                None
            }?;
            (RedKind::Assoc(AArch64Opcode::AddRR), vec![term])
        } else if acc_def.opcode == AArch64Opcode::Madd && acc_def.operands.len() >= 4 {
            let a = acc_def.operands[1].as_vreg();
            let b = acc_def.operands[2].as_vreg();
            let c = acc_def.operands[3].as_vreg();
            if c != Some(acc) || a.is_none() || b.is_none() || a == Some(acc) || b == Some(acc) {
                return None;
            }
            (RedKind::Madd, vec![a.unwrap(), b.unwrap()])
        } else {
            return None;
        };

    // -- 64-bit uniform accumulator/IV/inputs. --
    let rc = acc.class;
    if rc.size_bits() != 64 || iv.class != rc {
        return None;
    }
    for &v in &red_inputs {
        if v.class != rc {
            return None;
        }
    }

    // -- `acc` read nowhere in the body except the reduction. --
    for &bid in &[header, latch] {
        for &iid in &func.block(bid).insts {
            if iid == reduction_inst {
                continue;
            }
            let inst = func.inst(iid);
            let produces = inst_produces_value(inst);
            for (idx, operand) in inst.operands.iter().enumerate() {
                if produces && idx == 0 {
                    continue;
                }
                if operand.as_vreg() == Some(acc) {
                    return None;
                }
            }
        }
    }

    // -- Constant, non-negative start. --
    let start = resolve_const(func, lp, iv_init_source(func, preheader, iv)?)?;
    if start < 0 {
        return None;
    }

    // -- Header shape + RUNTIME limit + exit condition-code (both polarities). --
    let (limit, cc) = validate_header_closed_form(func, header, iv, latch, exit)?;
    let body_defs = collect_body_defs(func, lp);
    if limit.class != iv.class || body_defs.contains(&limit) {
        return None;
    }
    // RUNTIME limit only; a constant trip count stays with ReductionSplit / the
    // scalar loop (fail-closed — the closed form here targets runtime `n`).
    if resolve_const(func, lp, limit).is_some() {
        return None;
    }

    // -- Term computation: latch minus control/writeback/reduction/inc. --
    let branch_id = *func.block(latch).insts.last()?;
    let acc_writeback = carried
        .iter()
        .find(|(d, _, _)| *d == acc)
        .map(|(_, _, wb)| *wb)?;
    let control: [InstId; 5] = [
        iv_inc_inst,
        reduction_inst,
        iv_writeback,
        acc_writeback,
        branch_id,
    ];
    let mut term_insts: Vec<InstId> = Vec::new();
    for &iid in &func.block(latch).insts {
        if control.contains(&iid) {
            continue;
        }
        term_insts.push(iid);
    }
    // Closed-world check: each term inst reads only {iv, invariants, earlier defs}.
    let mut term_defs: HashSet<VReg> = HashSet::new();
    for &iid in &term_insts {
        let inst = func.inst(iid);
        if !inst_produces_value(inst) {
            return None;
        }
        let def = inst.operands.first().and_then(|o| o.as_vreg())?;
        for operand in inst.operands.iter().skip(1) {
            if let Some(v) = operand.as_vreg()
                && !(v == iv || term_defs.contains(&v) || !body_defs.contains(&v))
            {
                return None;
            }
        }
        term_defs.insert(def);
    }

    // -- The term must be a pure degree-≤2 polynomial in the IV. --
    let poly = closed_form_term_poly(
        func,
        lp,
        &term_insts,
        &red_kind,
        &red_inputs,
        iv,
        &body_defs,
    )?;

    let src_loc = func.inst(reduction_inst).source_loc;
    Some(ClosedForm {
        header,
        latch,
        preheader,
        exit,
        acc,
        rc,
        start,
        limit,
        cc,
        poly,
        reduction_inst,
        src_loc,
    })
}

/// Validate the header is `[cmp iv, limit ; BCond … ; B …]` with a RUNTIME
/// (register) limit, and return `(limit, exit_cc)` where `exit_cc ∈ {GE, HS}` is
/// the condition under which the loop exits (`iv ≥ limit`). Accepts BOTH branch
/// polarities the backend may emit:
///  * "exit-if-≥":   `BCond cc∈{GE,HS} → exit ; B latch`  ⇒ exit_cc = cc;
///  * "continue-if-<": `BCond cc∈{LT,LO} → latch ; B exit` ⇒ exit_cc = ¬cc
///    (LO⇒HS, LT⇒GE), the pipeline's natural pre-rotation form.
///    `iv` must be the first compare operand (BAIL on a swapped compare).
fn validate_header_closed_form(
    func: &MachFunction,
    header: BlockId,
    iv: VReg,
    latch: BlockId,
    exit: BlockId,
) -> Option<(VReg, i64)> {
    let insts = &func.block(header).insts;
    if insts.len() != 3 {
        return None;
    }
    let cmp = func.inst(insts[0]);
    let bcond = func.inst(insts[1]);
    let b = func.inst(insts[2]);

    if cmp.opcode != AArch64Opcode::CmpRR
        || cmp.operands.first().and_then(|o| o.as_vreg()) != Some(iv)
    {
        return None;
    }
    let limit = cmp.operands.get(1)?.as_vreg()?;

    if bcond.opcode != AArch64Opcode::BCond || b.opcode != AArch64Opcode::B {
        return None;
    }
    let cc_branch = bcond.operands.first()?.as_imm()?;
    let bcond_target = match bcond.operands.get(1)? {
        MachOperand::Block(t) => *t,
        _ => return None,
    };
    let b_target = match b.operands.first()? {
        MachOperand::Block(t) => *t,
        _ => return None,
    };

    let cc_exit = if bcond_target == exit && b_target == latch {
        // exit-if-≥ (the ReductionSplit-recognized polarity).
        if cc_branch != CC_HS && cc_branch != CC_GE {
            return None;
        }
        cc_branch
    } else if bcond_target == latch && b_target == exit {
        // continue-if-< (the backend's natural pre-rotation polarity).
        match cc_branch {
            CC_LO => CC_HS, // continue iff iv <u limit ⇒ exit iff iv ≥u limit
            CC_LT => CC_GE, // continue iff iv <s limit ⇒ exit iff iv ≥s limit
            _ => return None,
        }
    } else {
        return None;
    };
    Some((limit, cc_exit))
}

/// Resolve one operand of a term instruction to a polynomial in the IV, using
/// the running `coeffs` map (earlier term-defs), the IV itself, or a
/// loop-invariant constant. The closed-form analog of `inst_poly_core`'s inner
/// `operand_poly` — kept standalone so the fused-`Madd` case below can reuse it
/// WITHOUT modifying the shared `inst_poly_core` (which the strength-reduction
/// path depends on).
fn cf_operand_poly(
    func: &MachFunction,
    lp: &NaturalLoop,
    inst: &MachInst,
    idx: usize,
    iv: VReg,
    coeffs: &HashMap<VReg, Poly>,
    body_defs: &HashSet<VReg>,
) -> Option<Poly> {
    let v = inst.operands.get(idx)?.as_vreg()?;
    if let Some(p) = coeffs.get(&v) {
        return Some(*p);
    }
    if v == iv {
        return Some(Poly::iv());
    }
    if !body_defs.contains(&v) {
        return Some(Poly::constant(resolve_const(func, lp, v)? as i128));
    }
    None
}

/// Classify one term-inst as a polynomial in the IV for the closed-form path.
/// Extends `inst_poly_core` with the fused multiply-add `Madd(a,b,c) = a·b + c`
/// (into which a term like `3·i + 5` is commonly fused by isel). Kept separate
/// from `inst_poly_core` so the affine strength-reduction path is untouched.
fn cf_inst_poly(
    func: &MachFunction,
    lp: &NaturalLoop,
    inst: &MachInst,
    iv: VReg,
    coeffs: &HashMap<VReg, Poly>,
    body_defs: &HashSet<VReg>,
) -> Option<Poly> {
    if inst.opcode == AArch64Opcode::Madd {
        let a = cf_operand_poly(func, lp, inst, 1, iv, coeffs, body_defs)?;
        let b = cf_operand_poly(func, lp, inst, 2, iv, coeffs, body_defs)?;
        let c = cf_operand_poly(func, lp, inst, 3, iv, coeffs, body_defs)?;
        return a.mul(b)?.add(c);
    }
    inst_poly_core(func, lp, inst, iv, coeffs, body_defs)
}

/// Compute the reduction's term as a degree-≤2 polynomial in the IV, or `None`
/// if any operation feeding it is opaque (xor/or/and/shift/…), the degree would
/// exceed 2, or a coefficient overflows i128. For an `AddRR` reduction the term
/// is `red_inputs[0]`; for a fused `Madd(a,b,acc)` reduction the term is `a·b`
/// (the product of the two multiplicand polynomials). Because `cf_inst_poly`
/// only records a def in `coeffs` when its ENTIRE input chain is polynomial, a
/// resolvable term guarantees a pure polynomial in `i`.
fn closed_form_term_poly(
    func: &MachFunction,
    lp: &NaturalLoop,
    term_insts: &[InstId],
    red_kind: &RedKind,
    red_inputs: &[VReg],
    iv: VReg,
    body_defs: &HashSet<VReg>,
) -> Option<Poly> {
    let mut coeffs: HashMap<VReg, Poly> = HashMap::new();
    coeffs.insert(iv, Poly::iv());
    for &tid in term_insts {
        let inst = func.inst(tid);
        let def = inst.operands.first().and_then(|o| o.as_vreg())?;
        if let Some(p) = cf_inst_poly(func, lp, inst, iv, &coeffs, body_defs) {
            coeffs.insert(def, p);
        }
    }
    let resolve = |v: VReg| -> Option<Poly> {
        if v == iv {
            Some(Poly::iv())
        } else if let Some(p) = coeffs.get(&v) {
            Some(*p)
        } else if !body_defs.contains(&v) {
            Some(Poly::constant(resolve_const(func, lp, v)? as i128))
        } else {
            None
        }
    };
    match red_kind {
        RedKind::Assoc(_) => resolve(*red_inputs.first()?),
        // Madd term = a·b — the product of the two multiplicand polynomials
        // (`Poly::mul` returns None if the exact product exceeds degree 2).
        RedKind::Madd => resolve(*red_inputs.first()?)?.mul(resolve(*red_inputs.get(1)?)?),
    }
}

/// `Σ_{i<m} (a2·i² + a1·i + a0)` mod 2^64, computed with the EXACT modular
/// formula the rewrite emits — the compile-time oracle for the constant
/// `F(start)` correction. `a*` are the (mod-2^64) coefficients.
fn g_of_const(a2: u64, a1: u64, a0: u64, m: u64) -> u64 {
    if m == 0 {
        return 0;
    }
    // S1 = m(m-1)/2 mod 2^64 — exact ÷2 via a 128-bit product (m(m-1) is even).
    let s1 = (((m as u128) * (m.wrapping_sub(1) as u128)) >> 1) as u64;
    // twoM1 = 2m-1 (wrapping); S2 = S1·(2m-1)·inv3 = Σi² mod 2^64.
    let two_m1 = 2u64.wrapping_mul(m).wrapping_sub(1);
    let s2 = s1.wrapping_mul(two_m1).wrapping_mul(INV3_U64);
    a2.wrapping_mul(s2)
        .wrapping_add(a1.wrapping_mul(s1))
        .wrapping_add(a0.wrapping_mul(m))
}

/// Emit `dst = op(srcs…)` into the preheader (before its terminator), alloc a
/// fresh dst of class `rc`, record it as synthesized, and return it.
fn emit_ph(
    func: &mut MachFunction,
    src_loc: Option<SourceLoc>,
    ph: BlockId,
    synth: &mut Vec<InstId>,
    rc: RegClass,
    opcode: AArch64Opcode,
    srcs: &[MachOperand],
) -> VReg {
    let dst = VReg::new(func.alloc_vreg(), rc);
    let mut ops = Vec::with_capacity(srcs.len() + 1);
    ops.push(MachOperand::VReg(dst));
    ops.extend_from_slice(srcs);
    let id = push_with_loc(func, src_loc, opcode, ops);
    insert_before_terminator(func, ph, id);
    synth.push(id);
    dst
}

/// Materialize the constant `value` into a fresh preheader register.
fn mat_ph(
    func: &mut MachFunction,
    src_loc: Option<SourceLoc>,
    ph: BlockId,
    synth: &mut Vec<InstId>,
    value: u64,
    rc: RegClass,
) -> VReg {
    let (dst, ids) = emit_const(func, src_loc, value, rc);
    insert_all_before_terminator(func, ph, &ids);
    synth.extend(ids);
    dst
}

/// Rewrite the recognized loop into its straight-line closed form:
///   * emit the Faulhaber arithmetic in the preheader → `full`;
///   * guard with the loop's own zero-trip test (`start ≥ limit ? acc : full`);
///   * retarget preheader → exit (deleting the loop);
///   * wire the guarded result into every out-of-loop use of `acc`;
///   * prune the now-unreachable header/latch.
#[allow(clippy::too_many_lines)]
fn apply_closed_form(
    func: &mut MachFunction,
    cf: &ClosedForm,
    provenance: Option<&mut ProvenanceMap>,
) {
    let rc = cf.rc; // 64-bit (checked in the recognizer)
    let ph = cf.preheader;
    let limit = cf.limit;
    let src_loc = cf.src_loc;
    let mut synth: Vec<InstId> = Vec::new();

    let a2 = cf.poly.a2 as u64;
    let a1 = cf.poly.a1 as u64;
    let a0 = cf.poly.a0 as u64;

    use AArch64Opcode as Op;
    let vr = MachOperand::VReg;
    let imm = MachOperand::Imm;

    // --- S1 = (limit·(limit-1)) >> 1  (mod 2^64; exact via 128-bit halving) ---
    let lm1 = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::SubRI,
        &[vr(limit), imm(1)],
    );
    let lo = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::MulRR,
        &[vr(limit), vr(lm1)],
    );
    let hi = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::Umulh,
        &[vr(limit), vr(lm1)],
    );
    let lo_sh = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::LsrRI,
        &[vr(lo), imm(1)],
    );
    let hi_sh = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::LslRI,
        &[vr(hi), imm(63)],
    );
    let s1 = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::OrrRR,
        &[vr(lo_sh), vr(hi_sh)],
    );

    // --- twoM1 = 2·limit - 1  (wrapping) ---
    let l2 = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::LslRI,
        &[vr(limit), imm(1)],
    );
    let two_m1 = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::SubRI,
        &[vr(l2), imm(1)],
    );

    // --- S2 = S1 · twoM1 · inv3  (= Σi² mod 2^64) ---
    let s1t = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::MulRR,
        &[vr(s1), vr(two_m1)],
    );
    let inv3 = mat_ph(func, src_loc, ph, &mut synth, INV3_U64, rc);
    let s2 = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::MulRR,
        &[vr(s1t), vr(inv3)],
    );

    // --- Glimit = a2·S2 + a1·S1 + a0·limit  (skip zero coefficients) ---
    let mut terms: Vec<VReg> = Vec::new();
    if a2 != 0 {
        let c2 = mat_ph(func, src_loc, ph, &mut synth, a2, rc);
        terms.push(emit_ph(
            func,
            src_loc,
            ph,
            &mut synth,
            rc,
            Op::MulRR,
            &[vr(s2), vr(c2)],
        ));
    }
    if a1 != 0 {
        let c1 = mat_ph(func, src_loc, ph, &mut synth, a1, rc);
        terms.push(emit_ph(
            func,
            src_loc,
            ph,
            &mut synth,
            rc,
            Op::MulRR,
            &[vr(s1), vr(c1)],
        ));
    }
    if a0 != 0 {
        let c0 = mat_ph(func, src_loc, ph, &mut synth, a0, rc);
        terms.push(emit_ph(
            func,
            src_loc,
            ph,
            &mut synth,
            rc,
            Op::MulRR,
            &[vr(limit), vr(c0)],
        ));
    }
    let glimit = if let Some((&first, rest)) = terms.split_first() {
        let mut acc = first;
        for &t in rest {
            acc = emit_ph(
                func,
                src_loc,
                ph,
                &mut synth,
                rc,
                Op::AddRR,
                &[vr(acc), vr(t)],
            );
        }
        acc
    } else {
        mat_ph(func, src_loc, ph, &mut synth, 0, rc)
    };

    // --- full = acc_init + Glimit - F(start).  `cf.acc` still holds acc_init
    //     here (its preheader init precedes our inserts). ---
    let sum = emit_ph(
        func,
        src_loc,
        ph,
        &mut synth,
        rc,
        Op::AddRR,
        &[vr(glimit), vr(cf.acc)],
    );
    let g_start = g_of_const(a2, a1, a0, cf.start as u64);
    let full = if g_start == 0 {
        sum
    } else {
        let gs = mat_ph(func, src_loc, ph, &mut synth, g_start, rc);
        emit_ph(
            func,
            src_loc,
            ph,
            &mut synth,
            rc,
            Op::SubRR,
            &[vr(sum), vr(gs)],
        )
    };

    // --- Zero-trip guard: result = (start ≥ limit under cc) ? acc_init : full.
    //     This reproduces the loop's own entry test (iv=start, `BCond cc exit`)
    //     exactly, so a 0-iteration loop yields acc_init unchanged and a running
    //     loop yields the closed form. The CmpRR immediately precedes the Csel so
    //     the NZCV dependency is intact. ---
    let start_reg = mat_ph(func, src_loc, ph, &mut synth, cf.start as u64, rc);
    let cmp = push_with_loc(func, src_loc, Op::CmpRR, vec![vr(start_reg), vr(limit)]);
    insert_before_terminator(func, ph, cmp);
    synth.push(cmp);
    let result = VReg::new(func.alloc_vreg(), rc);
    let csel = push_with_loc(
        func,
        src_loc,
        Op::Csel,
        vec![vr(result), vr(cf.acc), vr(full), imm(cf.cc)],
    );
    insert_before_terminator(func, ph, csel);
    synth.push(csel);

    // --- CFG surgery: preheader → exit (delete the loop). ---
    let ph_term = *func
        .block(ph)
        .insts
        .last()
        .expect("preheader has a terminator");
    for op in func.inst_mut(ph_term).operands.iter_mut() {
        if let MachOperand::Block(b) = op
            && *b == cf.header
        {
            *b = cf.exit;
        }
    }
    for s in func.block_mut(ph).succs.iter_mut() {
        if *s == cf.header {
            *s = cf.exit;
        }
    }
    func.block_mut(cf.exit).preds.push(ph);

    // Wire the guarded result into every out-of-loop read of `acc` (the
    // liveouts). Exclude the preheader (our arithmetic legitimately reads
    // acc_init) and the loop blocks (about to be pruned).
    let blocks: Vec<BlockId> = func.block_order.clone();
    for bid in blocks {
        if bid == ph || bid == cf.header || bid == cf.latch {
            continue;
        }
        let inst_ids: Vec<InstId> = func.block(bid).insts.clone();
        for iid in inst_ids {
            let produces = inst_produces_value(func.inst(iid));
            for (idx, op) in func.inst_mut(iid).operands.iter_mut().enumerate() {
                if produces && idx == 0 {
                    continue;
                }
                if op.as_vreg() == Some(cf.acc) {
                    *op = vr(result);
                }
            }
        }
    }

    // Prune the now-unreachable header/latch (no cleanup pass runs after us).
    prune_to_reachable(func);

    // Provenance (best effort): attribute synthesized insts to the reduction.
    if let Some(prov) = provenance {
        let pass = PassId::new("closed-form-reduction");
        prov.record_in_place_transform(cf.reduction_inst, pass.clone());
        for &sid in &synth {
            prov.record_clone(cf.reduction_inst, sid, pass.clone());
        }
    }
}

/// Remove every block not reachable from `func.entry`: drop it from
/// `block_order` AND clear its instructions and edges. Clearing is essential —
/// the MachFunction→LIR lowering iterates the block ARENA (`0..blocks.len()`),
/// not `block_order`, so an orphaned-but-non-empty block would still be lowered;
/// its vregs (defined only within the removed loop) are invisible to the
/// block_order-scoped register allocator and would surface as "unresolved vreg"
/// at encode. Emptying the removed blocks makes them inert dead code. Runs with
/// no cleanup pass after the closed-form rewrite in the O2 pipeline.
fn prune_to_reachable(func: &mut MachFunction) {
    let mut reachable: HashSet<BlockId> = HashSet::new();
    let mut stack = vec![func.entry];
    while let Some(b) = stack.pop() {
        if !reachable.insert(b) {
            continue;
        }
        for &s in &func.block(b).succs.clone() {
            if !reachable.contains(&s) {
                stack.push(s);
            }
        }
    }
    let removed: Vec<BlockId> = func
        .block_order
        .iter()
        .copied()
        .filter(|b| !reachable.contains(b))
        .collect();
    for &b in &removed {
        let blk = func.block_mut(b);
        blk.insts.clear();
        blk.preds.clear();
        blk.succs.clear();
    }
    func.block_order.retain(|b| reachable.contains(b));
    let survivors: Vec<BlockId> = func.block_order.clone();
    for b in survivors {
        func.block_mut(b).preds.retain(|p| reachable.contains(p));
        func.block_mut(b).succs.retain(|s| reachable.contains(s));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::MachinePass;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, RegClass, Signature,
        SourceLoc, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }
    fn imm(v: i64) -> MachOperand {
        MachOperand::Imm(v)
    }
    fn blk(b: BlockId) -> MachOperand {
        MachOperand::Block(b)
    }

    /// Build a copy-form integer reduction loop that mirrors the real
    /// post-DCE/CFG-simplify AArch64 shape:
    ///
    /// ```text
    ///   bb0: MovI v0,#limit; MovI v1,#0; MovI v2,#1;
    ///        MovR v3,v1 (iv=0); MovR v4,v1 (acc=0); B bb1
    ///   bb1: CmpRR v3,v0; BCond GE,bb2; B bb3
    ///   bb3: <op-defined term/reduction>; AddRR v11,v3,v2 (iv+1);
    ///        MovR v3,v11; MovR v4,v10; B bb1
    ///   bb2: MovR v20,v4 (liveout); Ret
    /// ```
    ///
    /// `reduction` inserts the term + reduction that produce `v10 = acc_next`
    /// from `v3` (iv) and `v4` (acc).
    fn make_reduction_loop(
        limit: i64,
        reduction: impl FnOnce(&mut MachFunction, BlockId),
    ) -> MachFunction {
        let mut func = MachFunction::new("red".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        // Preheader.
        for i in func_preheader_insts(limit) {
            let id = func.push_inst(i);
            func.append_inst(bb0, id);
        }
        let b0 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![blk(bb1)]));
        func.append_inst(bb0, b0);

        // Header: CmpRR v3,v0; BCond GE,bb2; B bb3.
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(3), vreg(0)]));
        func.append_inst(bb1, cmp);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CC_GE), blk(bb2)],
        ));
        func.append_inst(bb1, bcond);
        let bh = func.push_inst(MachInst::new(AArch64Opcode::B, vec![blk(bb3)]));
        func.append_inst(bb1, bh);

        // Latch: caller inserts term + reduction (produces v10), then IV inc +
        // writebacks + branch.
        reduction(&mut func, bb3);
        let ivinc = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(11), vreg(3), vreg(2)],
        ));
        func.append_inst(bb3, ivinc);
        let wb_iv = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(3), vreg(11)]));
        func.append_inst(bb3, wb_iv);
        let wb_acc = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(4), vreg(10)]));
        func.append_inst(bb3, wb_acc);
        let bl = func.push_inst(MachInst::new(AArch64Opcode::B, vec![blk(bb1)]));
        func.append_inst(bb3, bl);

        // Exit: liveout use of acc (v4) then Ret.
        let lo = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(20), vreg(4)]));
        func.append_inst(bb2, lo);
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);
        func.next_vreg = 40;
        func
    }

    fn func_preheader_insts(limit: i64) -> Vec<MachInst> {
        vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(limit)]),
            MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(0)]),
            MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(1)]),
            MachInst::new(AArch64Opcode::MovR, vec![vreg(3), vreg(1)]),
            MachInst::new(AArch64Opcode::MovR, vec![vreg(4), vreg(1)]),
        ]
    }

    /// `acc += i*i`: term v9 = i*i (MulRR), reduction v10 = acc + v9 (AddRR).
    fn sumsq_body(func: &mut MachFunction, latch: BlockId) {
        let mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg(9), vreg(3), vreg(3)],
        ));
        func.append_inst(latch, mul);
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(10), vreg(4), vreg(9)],
        ));
        func.append_inst(latch, add);
    }

    fn count_op(func: &MachFunction, op: AArch64Opcode) -> usize {
        func.block_order
            .iter()
            .flat_map(|&b| func.block(b).insts.iter().copied())
            .filter(|&i| func.inst(i).opcode == op)
            .count()
    }

    #[test]
    fn test_fires_and_widens_accumulators() {
        let mut func = make_reduction_loop(100, sumsq_body);
        let blocks_before = func.block_order.len();
        let mut pass = ReductionSplit;
        assert!(pass.run(&mut func), "sum-of-squares reduction should split");

        // Three identity-init accumulators materialised in the preheader.
        let movz0 = func
            .block(BlockId(0))
            .insts
            .iter()
            .filter(|&&i| {
                func.inst(i).opcode == AArch64Opcode::Movz
                    && func.inst(i).operands.get(1).and_then(|o| o.as_imm()) == Some(0)
            })
            .count();
        assert_eq!(
            movz0, 3,
            "expected 3 extra accumulators seeded to identity 0"
        );

        // IV now steps by N (AddRI #4) instead of +1.
        let ivinc = func
            .block(BlockId(3))
            .insts
            .iter()
            .find(|&&i| {
                let inst = func.inst(i);
                inst.opcode == AArch64Opcode::AddRI
                    && inst.operands.first().and_then(|o| o.as_vreg())
                        == Some(VReg::new(11, RegClass::Gpr64))
            })
            .copied()
            .expect("iv increment rewritten to AddRI");
        assert_eq!(
            func.inst(ivinc).operands.get(2).and_then(|o| o.as_imm()),
            Some(SPLIT_FACTOR as i64),
            "IV must step by the split factor"
        );

        // A combine block was spliced on the exit edge.
        assert_eq!(
            func.block_order.len(),
            blocks_before + 1,
            "a combine block should be added"
        );

        // Four independent accumulate reductions (acc0..acc3) in the latch.
        let latch_adds = func
            .block(BlockId(3))
            .insts
            .iter()
            .filter(|&&i| func.inst(i).opcode == AArch64Opcode::AddRR)
            .count();
        assert_eq!(
            latch_adds, SPLIT_FACTOR,
            "one reduction add per accumulator"
        );

        // The liveout use of acc0 (v4) in the exit is rewired away from v4.
        let acc0 = VReg::new(4, RegClass::Gpr64);
        let exit_uses_v4 = func.block(BlockId(2)).insts.iter().any(|&i| {
            let inst = func.inst(i);
            inst.operands.iter().enumerate().any(|(idx, o)| {
                !(inst_produces_value(inst) && idx == 0) && o.as_vreg() == Some(acc0)
            })
        });
        assert!(!exit_uses_v4, "exit liveout must be rewired to acc_final");
    }

    #[test]
    fn test_idempotent() {
        let mut func = make_reduction_loop(100, sumsq_body);
        let mut pass = ReductionSplit;
        assert!(pass.run(&mut func), "first run splits");
        // Second run must not re-split: the IV now steps by N (not +1), so the
        // recognizer bails.
        assert!(!pass.run(&mut func), "second run must be idempotent");
    }

    #[test]
    fn test_source_loc_preserved_on_synthesized() {
        let loc = SourceLoc {
            file: 0,
            line: 42,
            col: 7,
        };
        let mut func = make_reduction_loop(100, |func, latch| {
            let mul = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(9), vreg(3), vreg(3)],
            ));
            func.append_inst(latch, mul);
            let mut add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(10), vreg(4), vreg(9)]);
            add.source_loc = Some(loc);
            let add = func.push_inst(add);
            func.append_inst(latch, add);
        });
        let mut pass = ReductionSplit;
        assert!(pass.run(&mut func));

        // The combine block (last non-exit block) reductions must carry the
        // reduction's source_loc.
        let combine = func
            .block_order
            .iter()
            .copied()
            .find(|&b| b.0 > 3)
            .expect("combine block exists");
        let combine_add = func
            .block(combine)
            .insts
            .iter()
            .find(|&&i| func.inst(i).opcode == AArch64Opcode::AddRR)
            .copied()
            .expect("combine has an add");
        assert_eq!(
            func.inst(combine_add).source_loc,
            Some(loc),
            "synthesized combine ops must preserve source_loc"
        );
    }

    #[test]
    fn test_bail_non_associative_sub_reduction() {
        // `acc -= i`: SubRR is not associative/commutative — must NOT split.
        let mut func = make_reduction_loop(100, |func, latch| {
            let sub = func.push_inst(MachInst::new(
                AArch64Opcode::SubRR,
                vec![vreg(10), vreg(4), vreg(3)],
            ));
            func.append_inst(latch, sub);
        });
        let mut pass = ReductionSplit;
        assert!(!pass.run(&mut func), "subtraction reduction must not split");
    }

    #[test]
    fn test_bail_non_divisible_trip_count() {
        // trip count 101 is not divisible by the split factor — must BAIL
        // (no remainder loop in v1).
        let mut func = make_reduction_loop(101, sumsq_body);
        let mut pass = ReductionSplit;
        assert!(!pass.run(&mut func), "non-divisible trip count must bail");
    }

    #[test]
    fn test_bail_acc_read_by_other_instruction() {
        // A live second use of acc inside the loop (a side accumulator that
        // observes the running partial sum) must block the split.
        let mut func = make_reduction_loop(100, |func, latch| {
            let mul = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(9), vreg(3), vreg(3)],
            ));
            func.append_inst(latch, mul);
            let add = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(10), vreg(4), vreg(9)],
            ));
            func.append_inst(latch, add);
            // Extra LIVE read of acc (v4): v30 = acc * 2 — a live use whose
            // result escapes via the mul below would observe reordered partials.
            let leak = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(30), vreg(4), vreg(2)],
            ));
            func.append_inst(latch, leak);
            // Keep v30 live by feeding it into the term (so it is not dead).
            let use30 = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(10), vreg(10), vreg(30)],
            ));
            func.append_inst(latch, use30);
        });
        let mut pass = ReductionSplit;
        assert!(
            !pass.run(&mut func),
            "a non-reduction read of acc must block the split"
        );
    }

    #[test]
    fn test_madd_fused_reduction_splits() {
        // `acc += i*i` fused into a single Madd(i, i, acc).
        let mut func = make_reduction_loop(100, |func, latch| {
            let madd = func.push_inst(MachInst::new(
                AArch64Opcode::Madd,
                vec![vreg(10), vreg(3), vreg(3), vreg(4)],
            ));
            func.append_inst(latch, madd);
        });
        let mut pass = ReductionSplit;
        assert!(pass.run(&mut func), "fused Madd reduction should split");
        // Four Madd accumulate ops (acc0..acc3) remain in the latch.
        assert_eq!(
            count_op(&func, AArch64Opcode::Madd),
            SPLIT_FACTOR,
            "one Madd per accumulator"
        );
    }

    #[test]
    fn test_linear_term_strength_reduced() {
        // `acc += i*3`: the linear multiply must become a running addition — NO
        // MulRR survives (each lane's `i*3` is a per-lane offset of a carried
        // recurrence). This is the affine strength reduction.
        let mut func = make_reduction_loop(100, |func, latch| {
            // v9 = i(v3) * v5, where v5 = const 3 (injected into the preheader).
            let mul = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(9), vreg(3), vreg(5)],
            ));
            func.append_inst(latch, mul);
            let add = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(10), vreg(4), vreg(9)],
            ));
            func.append_inst(latch, add);
        });
        // Materialise v5 = 3 in the preheader so `resolve_const(v5)` folds it.
        let c3 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(5), imm(3)]));
        func.block_mut(BlockId(0)).insts.insert(0, c3);

        assert_eq!(
            count_op(&func, AArch64Opcode::MulRR),
            1,
            "one linear multiply before"
        );
        let mut pass = ReductionSplit;
        assert!(pass.run(&mut func), "linear-term reduction should split");
        assert_eq!(
            count_op(&func, AArch64Opcode::MulRR),
            0,
            "the linear i*3 multiply must be strength-reduced away"
        );
        // Idempotent under the O3 fixpoint.
        assert!(!pass.run(&mut func), "second run must be idempotent");
    }

    #[test]
    fn test_mix_keeps_quadratic_reduces_linear() {
        // `acc += (i*i) ^ (i*3)`: the quadratic `i*i` stays as a multiply (one
        // per lane = SPLIT_FACTOR), while the linear `i*3` is reduced away —
        // exactly clang's strategy.
        let mut func = make_reduction_loop(100, |func, latch| {
            let sq = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(9), vreg(3), vreg(3)],
            ));
            func.append_inst(latch, sq);
            let lin = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(12), vreg(3), vreg(5)],
            ));
            func.append_inst(latch, lin);
            let xor = func.push_inst(MachInst::new(
                AArch64Opcode::EorRR,
                vec![vreg(13), vreg(9), vreg(12)],
            ));
            func.append_inst(latch, xor);
            let add = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(10), vreg(4), vreg(13)],
            ));
            func.append_inst(latch, add);
        });
        let c3 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(5), imm(3)]));
        func.block_mut(BlockId(0)).insts.insert(0, c3);

        assert_eq!(
            count_op(&func, AArch64Opcode::MulRR),
            2,
            "two multiplies before (i*i, i*3)"
        );
        let mut pass = ReductionSplit;
        assert!(pass.run(&mut func), "mixed reduction should split");
        // Only the quadratic survives: SPLIT_FACTOR muls (one per lane); the
        // linear i*3 is gone.
        assert_eq!(
            count_op(&func, AArch64Opcode::MulRR),
            SPLIT_FACTOR,
            "quadratic i*i kept as one multiply per lane; linear i*3 reduced away"
        );
        assert!(!pass.run(&mut func), "second run must be idempotent");
    }

    /// Build a reduction loop whose limit (`v0`) is a RUNTIME value — defined by
    /// a `Copy` (not a `Mov*`) so `resolve_const` fails and the recognizer takes
    /// the runtime split-with-tail path.
    fn make_runtime_reduction_loop(
        reduction: impl FnOnce(&mut MachFunction, BlockId),
    ) -> MachFunction {
        let mut func = make_reduction_loop(1000, reduction);
        let v0 = VReg::new(0, RegClass::Gpr64);
        let entry = func.entry;
        for iid in func.block(entry).insts.clone() {
            let inst = func.inst(iid);
            if inst.opcode == AArch64Opcode::MovI
                && inst.operands.first().and_then(|o| o.as_vreg()) == Some(v0)
            {
                let m = func.inst_mut(iid);
                m.opcode = AArch64Opcode::Copy;
                m.operands = vec![vreg(0), vreg(50)]; // v0 = copy of a param-like vreg
            }
        }
        func
    }

    #[test]
    fn test_runtime_fires_with_guard_and_tail() {
        let mut func = make_runtime_reduction_loop(sumsq_body);
        let blocks_before = func.block_order.len();
        let mut pass = ReductionSplit;
        assert!(pass.run(&mut func), "runtime-limit reduction should split");

        // combine + (N-1) check + (N-1) body blocks = 1 + 2*(N-1) new blocks.
        assert_eq!(
            func.block_order.len(),
            blocks_before + 1 + 2 * (SPLIT_FACTOR - 1),
            "runtime split adds combine + peeled (check,body) tail blocks"
        );

        // The main IV steps by N (AddRI #N), just like the constant path.
        let steps_by_n = func.block_order.iter().any(|&b| {
            func.block(b).insts.iter().any(|&i| {
                let inst = func.inst(i);
                inst.opcode == AArch64Opcode::AddRI
                    && inst.operands.first().and_then(|o| o.as_vreg())
                        == Some(VReg::new(11, RegClass::Gpr64))
                    && inst.operands.get(2).and_then(|o| o.as_imm()) == Some(SPLIT_FACTOR as i64)
            })
        });
        assert!(steps_by_n, "main-loop IV must step by the split factor");

        // A `SubRI _, v0, #(N-1)` (main_bound = limit - (N-1)) was materialised.
        let has_main_bound = func.block_order.iter().any(|&b| {
            func.block(b).insts.iter().any(|&i| {
                let inst = func.inst(i);
                inst.opcode == AArch64Opcode::SubRI
                    && inst.operands.get(1).and_then(|o| o.as_vreg())
                        == Some(VReg::new(0, RegClass::Gpr64))
                    && inst.operands.get(2).and_then(|o| o.as_imm())
                        == Some((SPLIT_FACTOR - 1) as i64)
            })
        });
        assert!(
            has_main_bound,
            "main_bound = limit - (N-1) must be computed"
        );

        // The header no longer compares iv against the raw limit v0 (it now uses
        // main_bound) — a guard against the exact over-run failure mode.
        let header = BlockId(1);
        let cmp = func.block(header).insts[0];
        assert_ne!(
            func.inst(cmp).operands.get(1).and_then(|o| o.as_vreg()),
            Some(VReg::new(0, RegClass::Gpr64)),
            "header compare RHS must be main_bound, not the raw runtime limit"
        );
    }

    #[test]
    fn test_runtime_idempotent() {
        // The runtime rewrite must be a fixpoint (O3 iterates the pass): the main
        // loop now steps by N (recognizer bails), and the tail is straight-line
        // (not a loop), so a second run changes nothing.
        let mut func = make_runtime_reduction_loop(sumsq_body);
        let mut pass = ReductionSplit;
        assert!(pass.run(&mut func), "first run splits the runtime loop");
        assert!(!pass.run(&mut func), "second run must be idempotent");
    }

    // -- Closed-form (Faulhaber) reduction --------------------------------

    fn arith_count(func: &MachFunction, op: AArch64Opcode) -> usize {
        func.block_order
            .iter()
            .flat_map(|&b| func.block(b).insts.iter().copied())
            .filter(|&i| func.inst(i).opcode == op)
            .count()
    }

    #[test]
    fn test_closed_form_fires_and_deletes_loop() {
        // `acc += i*i` for a RUNTIME trip count collapses to straight-line code.
        let mut func = make_runtime_reduction_loop(sumsq_body);
        let mut pass = ClosedFormReduction;
        assert!(
            pass.run(&mut func),
            "pure-poly runtime reduction closes to a form"
        );

        // The loop is gone: only the preheader and the exit remain in layout.
        assert_eq!(
            func.block_order.len(),
            2,
            "closed form deletes the loop blocks"
        );
        assert!(!func.block_order.contains(&BlockId(1)), "header removed");
        assert!(!func.block_order.contains(&BlockId(3)), "latch removed");

        // Faulhaber arithmetic is present: the 128-bit halving (Umulh), the
        // modular inverse mul chain, and the zero-trip guard (Csel).
        assert!(
            arith_count(&func, AArch64Opcode::Umulh) >= 1,
            "128-bit halving emitted"
        );
        assert!(
            arith_count(&func, AArch64Opcode::Csel) == 1,
            "zero-trip guard emitted"
        );
        assert!(
            arith_count(&func, AArch64Opcode::MulRR) >= 3,
            "S1·(2n-1)·inv3·a2 muls emitted"
        );

        // No back-edge remains anywhere (the surviving blocks form a DAG).
        for &b in &func.block_order {
            assert!(
                !func.block(b).succs.contains(&BlockId(1))
                    && !func.block(b).succs.contains(&BlockId(3)),
                "no edge into a deleted loop block"
            );
        }
    }

    #[test]
    fn test_closed_form_idempotent() {
        // After the loop is deleted there is nothing left to recognize.
        let mut func = make_runtime_reduction_loop(sumsq_body);
        let mut pass = ClosedFormReduction;
        assert!(pass.run(&mut func), "first run closes the form");
        assert!(!pass.run(&mut func), "second run is a fixpoint");
    }

    #[test]
    fn test_closed_form_bails_on_constant_trip() {
        // A constant trip count stays with ReductionSplit (fail-closed here).
        let mut func = make_reduction_loop(100, sumsq_body);
        let mut pass = ClosedFormReduction;
        assert!(
            !pass.run(&mut func),
            "constant-trip loop must not be closed-formed"
        );
    }

    #[test]
    fn test_closed_form_bails_on_opaque_xor_term() {
        // `acc += (i*i) ^ i` — the xor makes the term non-polynomial: BAIL.
        let mut func = make_runtime_reduction_loop(|func, latch| {
            let mul = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(9), vreg(3), vreg(3)],
            ));
            func.append_inst(latch, mul);
            let xor = func.push_inst(MachInst::new(
                AArch64Opcode::EorRR,
                vec![vreg(31), vreg(9), vreg(3)],
            ));
            func.append_inst(latch, xor);
            let add = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(10), vreg(4), vreg(31)],
            ));
            func.append_inst(latch, add);
        });
        let mut pass = ClosedFormReduction;
        assert!(
            !pass.run(&mut func),
            "opaque (xor) term must BAIL to ReductionSplit"
        );
    }

    #[test]
    fn test_closed_form_bails_when_acc_read_in_body() {
        // The acc-read-only-by-reduction guard applies: an extra live read of acc
        // means the loop is not a clean reduction -> BAIL.
        let mut func = make_runtime_reduction_loop(|func, latch| {
            let mul = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(9), vreg(3), vreg(3)],
            ));
            func.append_inst(latch, mul);
            let add = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(10), vreg(4), vreg(9)],
            ));
            func.append_inst(latch, add);
            let leak = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(30), vreg(4), vreg(2)],
            ));
            func.append_inst(latch, leak);
            let use30 = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(10), vreg(10), vreg(30)],
            ));
            func.append_inst(latch, use30);
        });
        let mut pass = ClosedFormReduction;
        assert!(
            !pass.run(&mut func),
            "acc read outside the reduction must BAIL"
        );
    }

    #[test]
    fn test_runtime_bails_when_acc_read_in_body() {
        // The acc-read-only-by-reduction guard still applies on the runtime path.
        let mut func = make_runtime_reduction_loop(|func, latch| {
            let mul = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(9), vreg(3), vreg(3)],
            ));
            func.append_inst(latch, mul);
            let add = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(10), vreg(4), vreg(9)],
            ));
            func.append_inst(latch, add);
            // Extra LIVE read of acc (v4) folded back into the term.
            let leak = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(30), vreg(4), vreg(2)],
            ));
            func.append_inst(latch, leak);
            let use30 = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(10), vreg(10), vreg(30)],
            ));
            func.append_inst(latch, use30);
        });
        let mut pass = ReductionSplit;
        assert!(
            !pass.run(&mut func),
            "runtime path must still bail when acc is read outside the reduction"
        );
    }
}
