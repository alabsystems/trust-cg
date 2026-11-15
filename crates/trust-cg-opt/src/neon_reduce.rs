// trust-cg-opt - NEON integer-reduction vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON integer-reduction vectorizer (`neon-reduce`)
//!
//! Vectorizes counted integer reduction loops of the shape
//!
//! ```text
//! acc = seed;  for i in 0..n (signed i < n):  acc += TERM(i)
//! ```
//!
//! where `TERM(i)` is computed with **lane-wise** integer operations of the
//! induction variable `i` and loop-invariant constants: `+  -  *  &  |  ^  <<
//! >>` (and the fused `madd = a*b + c`). It processes `UNROLL * VF = 16` scalar
//! iterations per NEON iteration across `UNROLL = 4` INDEPENDENT `4 x i32`
//! vector accumulators (for ILP), carrying each accumulator's per-lane index as
//! a vector that is advanced by a constant vector each iteration (vector
//! strength reduction — the index is never re-derived from the scalar `iv`).
//! At loop exit it combines the accumulators, horizontally reduces, and lets the
//! ORIGINAL scalar loop handle the remaining `< 16` tail iterations.
//!
//! It runs before [`crate::reduction_split`] in the O2/Os/O3 pipeline, admitting
//! the recognized lane-wise shapes and leaving other loops untouched, so
//! `reduction_split`'s scalar accumulator-split still handles non-vectorizable
//! reductions. Disable with `TRUST_CG_DISABLE_PASSES=neonreduce`.
//!
//! A second path recognizes forward memory chains with i32/i64 integer add or
//! bitwise reductions. Both paths construct a private candidate using checked
//! IDs, setup anchors and entry-edge splicing. Failure discards every candidate
//! edit, including preheader instructions; recognition itself is read-only.
//!
//! ## Equivalence argument and evidence limits
//!
//! The transform is *purely additive*: it inserts a vector main loop in front
//! of the scalar loop and never edits the scalar loop's instructions. The
//! scalar tail still needs the correct entry state, so the vector main loop,
//! drain and edge redirection must preserve the original reduction semantics.
//! The argument below is not a current solver/checker receipt for the complete
//! transform or the emitted binary.
//!
//! Let `w = 32` (i32 lanes). For a block of `VF` consecutive iterations
//! starting at `i`, the NEON index vector is `vi = [i, i+1, i+2, i+3]`, and the
//! lowered `TERM` computes, lane `k`, exactly `TERM(i + k) (mod 2^w)`:
//!
//! * scalar-to-vector operation models are described in
//!   `trust-cg-verify/src/vectorization_proofs.rs` (`ADD/SUB/MUL/AND/ORR/EOR`
//!   on `.4S`, `SHL/USHR/SSHR` immediate); `madd(a,b,c)` is lowered to
//!   `mul` then `add`;
//! * `i + k` per lane is materialized exactly by `DUP` + `INS`;
//! * constants are identical in every lane.
//!
//! Each accumulator does `vacc_k += vterm_k` every vector iteration over its own
//! disjoint set of lane indices, so after processing iterations `[iv0, V)` with
//! `V = iv0 + width * floor((n - iv0) / width)` (`width = 16`), every partial
//! `vacc_k` lane holds a sum of a disjoint subset of `{TERM(j)}`. Two's-complement
//! addition mod `2^w` is associative and commutative (modeled in
//! `trust-cg-verify/src/reduction_split_proofs.rs`), so combining the four
//! accumulators with vector adds and then summing the four lanes reproduces
//! `sum_{j in [iv0,V)} TERM(j) (mod 2^w)` regardless of grouping — this is the
//! reduction-split argument lifted into the vector domain. The horizontal
//! reduction uses `UMOV` lane extraction and scalar addition. Its partial sum
//! is added to the original accumulator seed, and the scalar tail adds
//! `TERM(j)` for `j in [V, n)`. The intended total is therefore
//! `seed + sum_{j in [iv0,n)} TERM(j) (mod 2^w)`; instruction coverage alone
//! does not establish this whole-transform relation.
//!
//! ## Fail-closed guards (BAIL preconditions)
//!
//! Every one of these must hold or the loop is left entirely to the scalar
//! path (see `Recognized::recognize`): a single innermost `{header, latch}`
//! loop; a `+1` induction; the exact `signed <` (cc=LT) exit test; a single
//! accumulator read ONLY by the reduction; an `acc += TERM` (or fused
//! `acc = madd(a,b,acc)`) reduction; a `TERM` slice built only from allowed
//! lane-wise ops with leaves that are the induction or 16-bit constants; and
//! NO memory / call / unrecognized op anywhere in the loop body.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use crate::loop_contract::{
    ExitPlan, GuardBound, Handoff, InductionGuards, LoopLocality, exit_of_test,
};
use crate::mach_util::{
    block_of_inst, branch_targets, const_value, copies_reg, copy_like, strip_copies,
};

use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, MachOperand, RegClass, VReg};

use crate::candidate::{alloc, emit, emit_before, insert_new_blocks_before};
use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Lanes per NEON iteration (`4 x i32`).
const VF: i64 = 4;
/// Lanes per NEON iteration for the i64 (`.2D`) bitwise-chain path (`2 x i64`).
const VF_I64: i64 = 2;
/// NEON element-size operand code for `S` (32-bit) lanes.
const ELEM_S: i64 = 4;
/// NEON element-size operand code for `D` (64-bit) lanes (`.2D` bitwise chain).
const ELEM_D: i64 = 8;
/// NEON arrangement operand code for `.4S`.
const ARR_S4: i64 = 5;
/// AArch64 condition code for signed less-than (`LT`).
const CC_LT: i64 = 11;
/// AArch64 condition code for unsigned less-than (`LO`/`CC`) — the forward
/// bitwise-chain loop-continue / bounds-guard test.
const CC_LO: i64 = 3;
/// Byte size of an `i32` array element (bitwise chain addressing).
const ELEM_BYTES: i64 = 4;
/// Byte size of an `i64` array element (`.2D` bitwise chain addressing).
const ELEM_BYTES_I64: i64 = 8;

/// The `neon-reduce` machine pass.
#[derive(Default)]
pub struct NeonReducePass {
    /// Number of loops vectorized in the last run (diagnostics/tests).
    fired: usize,
}

impl NeonReducePass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonReducePass {
    fn name(&self) -> &str {
        "neon-reduce"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    // Share the AnalysisCache's CFG-derived DomTree + LoopAnalysis instead of
    // recomputing per pass (see NeonArrayPass). Sound + byte-identical: both
    // analyses depend only on the CFG, which the cache invalidates on any CFG
    // change, so a shared instance equals a fresh recompute here.
    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loops = analyses.loop_analysis(func).clone();
        let changed = {
            let dom = analyses.domtree(func);
            self.run_core(func, dom, &loops)
        };
        // Invalidate the shared analyses on a FIRE (CFG mutated) so no downstream
        // pass reads a stale loop tree; zero cost in the no-fire hot path. See
        // NeonArrayPass::run_with_analyses.
        if changed {
            analyses.invalidate();
        }
        changed
    }
}

impl NeonReducePass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;

        // Recognize all candidate loops read-only first; applying a plan only
        // *adds* blocks (never renumbers existing block/inst ids or edits other
        // loops' blocks), so recognized data for other loops stays valid.
        //
        // Dispatch: the STRICT 2-block induction-term ADD reduction ([`Recognized`],
        // byte-identical to the shipped path) is tried FIRST; only if it bails is
        // the FORWARD-CHAIN K-way BITWISE reduction recognizer
        // ([`BitChainRecognized`]) tried — the `while i<N` chain the bridge emits
        // for `acc OP= a[i]` (OP in {&, |, ^}) over a LOCAL fixed-size array, whose
        // per-access bounds checks become a chain of diamonds/pass-throughs
        // (`body.len() >= 3`). The two shapes are disjoint (2-block ADD term vs
        // >=3-block memory-load bitwise), so a loop is never processed by both.
        let mut plans: Vec<Plan> = Vec::new();
        for lp in loops.all_loops() {
            if let Some(rec) = Recognized::recognize(func, dom, lp.header, lp.latch, &lp.body) {
                plans.push(Plan::Strict(rec));
            } else if let Some(chain) =
                BitChainRecognized::recognize(func, dom, lp.header, lp.latch, &lp.body)
            {
                plans.push(Plan::Chain(chain));
            }
        }

        let mut changed = false;
        for plan in plans {
            let ok = match &plan {
                Plan::Strict(rec) => apply(func, rec),
                Plan::Chain(chain) => apply_chain(func, chain),
            };
            if ok {
                self.fired += 1;
                changed = true;
            }
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// The `TERM` value to lower per lane.
#[derive(Clone, Copy)]
enum Term {
    /// A single SSA value defining the whole term.
    Value(VReg),
    /// A fused `a * b` (from a reduction expressed as `madd(a, b, acc)`).
    MulPair(VReg, VReg),
}

/// A fully validated, lane-wise-vectorizable reduction loop.
struct Recognized {
    /// Preheader-guard block reached once before the loop.
    guard: BlockId,
    /// Block that branches into `guard`.
    preheader: BlockId,
    /// The `preheader` terminator instruction targeting `guard`.
    preheader_term: InstId,
    /// Loop-carried induction register (`+1` each iteration).
    iv: VReg,
    /// Loop-carried accumulator register.
    acc: VReg,
    /// Loop bound register (`iv < bound`).
    bound: VReg,
    /// The per-iteration term to lower.
    term: Term,
    /// Global def map (`vreg id -> defining InstId`).
    def: HashMap<u32, InstId>,
    /// Instruction ids that live inside the loop body.
    loop_insts: HashSet<InstId>,
    /// The loop-state contract (`crate::loop_contract`) passed for
    /// `[iv, acc]`. The plan cannot be built without it.
    _locality: LoopLocality,
}

/// Opcodes permitted anywhere in the loop body. Anything else ⇒ BAIL (rules out
/// loads/stores/calls/atomics/division and any unmodeled effect).
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR
            | AddRI
            | SubRR
            | SubRI
            | MulRR
            | Madd
            | AndRR
            | AndRI
            | OrrRR
            | OrrRI
            | EorRR
            | EorRI
            | LslRI
            | LsrRI
            | AsrRI
            | Movz
            | Movn
            | MovR
            | Copy
            | CmpRR
            | CmpRI
            | BCond
            | B
            | Sxtw
    )
}

impl Recognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // (R1) exactly a 2-block innermost loop {header, latch}.
        if header == latch || body.len() != 2 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // Whitelist every opcode in the loop body — no memory/call/div/etc.
        let mut loop_insts = HashSet::default();
        for &b in [header, latch].iter() {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

        let def = crate::effects::build_reaching_def_map(func);

        // (R6) header preds are exactly {latch, guard}; guard has one pred.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            return None;
        }
        let guard = *hpreds.iter().find(|&&b| b != latch)?;
        let gpreds = &func.block(guard).preds;
        if gpreds.len() != 1 {
            return None;
        }
        let preheader = gpreds[0];
        // The preheader terminator must branch to guard.
        let preheader_term = *func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&guard))?;

        // (R2) latch: find the exit branch `BCond(cc) -> header` and its compare.
        let latch_insts = &func.block(latch).insts;
        let bcond = latch_insts
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::BCond && branch_targets(i).contains(&header))?;
        if bcond.operands[0].as_imm() != Some(CC_LT) {
            return None; // only signed `<` counted loops
        }
        // The compare feeding it: `CmpRR(iv, bound)`.
        let cmp = latch_insts
            .iter()
            .map(|&id| func.inst(id))
            .rev()
            .find(|i| i.opcode == AArch64Opcode::CmpRR)?;
        let iv = cmp.operands[0].as_vreg()?;
        let bound = cmp.operands[1].as_vreg()?;

        // Loop-carried writebacks in the latch: exactly two (iv, acc).
        let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
        for &id in latch_insts {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                writebacks.push((d, s));
            }
        }
        if writebacks.len() != 2 {
            return None;
        }
        // iv writeback source.
        let iv_src = writebacks.iter().find(|(d, _)| *d == iv).map(|(_, s)| *s)?;
        // acc is the other writeback target.
        let (acc, acc_src) = {
            let other = writebacks.iter().find(|(d, _)| *d != iv)?;
            (other.0, other.1)
        };
        if acc == iv {
            return None;
        }

        // (R3) step: iv_src = AddRR(iv, +1)  (or AddRI(iv, 1)).
        if !is_increment_by_one(func, &def, iv_src, iv) {
            return None;
        }

        // (R4) reduction: acc_src defined by `AddRR(acc, term)` (commutative)
        // or fused `Madd(a, b, acc)` (term = a*b).
        let acc_def = func.inst(*def.get(&acc_src.id)?);
        let term = match acc_def.opcode {
            AArch64Opcode::AddRR => {
                let x = acc_def.operands[1].as_vreg()?;
                let y = acc_def.operands[2].as_vreg()?;
                if x == acc {
                    Term::Value(y)
                } else if y == acc {
                    Term::Value(x)
                } else {
                    return None;
                }
            }
            AArch64Opcode::Madd if acc_def.operands.len() == 4 => {
                let a = acc_def.operands[1].as_vreg()?;
                let b = acc_def.operands[2].as_vreg()?;
                let c = acc_def.operands[3].as_vreg()?;
                if c != acc || a == acc || b == acc {
                    return None;
                }
                Term::MulPair(a, b)
            }
            _ => return None,
        };

        // (R4b) acc must be read ONLY by the reduction inst inside the loop.
        let acc_reducer = *def.get(&acc_src.id)?;
        for &id in loop_insts.iter() {
            if id == acc_reducer {
                continue;
            }
            let inst = func.inst(id);
            // skip the operand-0 (def) position; count uses only.
            for op in inst.operands.iter().skip(1) {
                if op.as_vreg() == Some(acc) {
                    return None;
                }
            }
            // Copy/MovR/AddRI writeback of acc reads its *source*, not acc, so
            // operand-0 (the def) being acc is fine and already skipped.
        }

        // Registers must be 32-bit (i32 lanes).
        if iv.class != RegClass::Gpr32 || acc.class != RegClass::Gpr32 {
            return None;
        }

        // The bound must be a 32-bit, loop-invariant value whose definition is
        // available in the preheader (so the preheader can `Sxtw` it). Requiring
        // its def block to dominate the preheader guarantees both: it is not
        // written in the loop and it reaches the preheader.
        if bound.class != RegClass::Gpr32 {
            return None;
        }
        let bound_def = *def.get(&bound.id)?;
        let bound_block = block_of_inst(func, bound_def)?;
        if !dom.dominates(bound_block, preheader) {
            return None;
        }

        // LOOP STATE (`crate::loop_contract`): the vector loop runs only
        // iterations the latch's `iv < bound` test continues, and reproduces only
        // `iv` and `acc`; the loop may leave by no other exit, and no other
        // register the loop carries or leaves live may be skipped.
        let exit = exit_of_test(func, body.iter().copied(), latch)?;
        let locality = match LoopLocality::check(
            func,
            body.iter().copied(),
            header,
            &ExitPlan::loop_test(latch, exit),
            Handoff::HeaderOrExit,
            &[iv, acc],
        ) {
            Ok(locality) => locality,
            Err(_escape) => return None,
        };
        let rec = Recognized {
            _locality: locality,
            guard,
            preheader,
            preheader_term,
            iv,
            acc,
            bound,
            term,
            def,
            loop_insts,
        };

        // (R5) term must be lowerable per-lane. Dry-run the lowering feasibility.
        if !rec.term_is_lowerable(func) {
            return None;
        }
        Some(rec)
    }

    /// Read-only feasibility check mirroring [`lower`]: every reachable node is
    /// the induction, a 16-bit constant, or an allowed lane-wise op over such.
    fn term_is_lowerable(&self, func: &MachFunction) -> bool {
        let mut seen = HashSet::default();
        match self.term {
            Term::Value(v) => self.node_ok(func, v, &mut seen),
            Term::MulPair(a, b) => {
                self.node_ok(func, a, &mut seen) && self.node_ok(func, b, &mut seen)
            }
        }
    }

    fn node_ok(&self, func: &MachFunction, val: VReg, seen: &mut HashSet<u32>) -> bool {
        if val == self.iv {
            return true;
        }
        if val == self.acc {
            return false; // recurrence — not lane-wise
        }
        if const_value(func, &self.def, val).is_some() {
            return true;
        }
        if !seen.insert(val.id) {
            return true; // already validated
        }
        let Some(&def_id) = self.def.get(&val.id) else {
            return false; // non-const value defined outside the loop
        };
        if !self.loop_insts.contains(&def_id) {
            return false;
        }
        let inst = func.inst(def_id);
        use AArch64Opcode::*;
        match inst.opcode {
            MulRR | AddRR | SubRR | AndRR | OrrRR | EorRR => {
                let a = match inst.operands[1].as_vreg() {
                    Some(v) => v,
                    None => return false,
                };
                let b = match inst.operands[2].as_vreg() {
                    Some(v) => v,
                    None => return false,
                };
                self.node_ok(func, a, seen) && self.node_ok(func, b, seen)
            }
            AddRI | SubRI | AndRI | OrrRI | EorRI => {
                // reg <op> immediate: immediate must fit a 16-bit vec constant.
                let a = match inst.operands[1].as_vreg() {
                    Some(v) => v,
                    None => return false,
                };
                let ok_imm =
                    matches!(inst.operands[2].as_imm(), Some(v) if (0..=0xFFFF).contains(&v));
                ok_imm && self.node_ok(func, a, seen)
            }
            LslRI | LsrRI | AsrRI => {
                let a = match inst.operands[1].as_vreg() {
                    Some(v) => v,
                    None => return false,
                };
                let ok_sh = matches!(inst.operands[2].as_imm(), Some(v) if (0..=31).contains(&v));
                ok_sh && self.node_ok(func, a, seen)
            }
            Madd if inst.operands.len() == 4 => {
                let a = inst.operands[1].as_vreg();
                let b = inst.operands[2].as_vreg();
                let c = inst.operands[3].as_vreg();
                match (a, b, c) {
                    (Some(a), Some(b), Some(c)) => {
                        self.node_ok(func, a, seen)
                            && self.node_ok(func, b, seen)
                            && self.node_ok(func, c, seen)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }
}

fn is_increment_by_one(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    iv_src: VReg,
    iv: VReg,
) -> bool {
    let Some(&id) = def.get(&iv_src.id) else {
        return false;
    };
    let inst = func.inst(id);
    match inst.opcode {
        AArch64Opcode::AddRI => {
            inst.operands[1].as_vreg() == Some(iv) && inst.operands[2].as_imm() == Some(1)
        }
        AArch64Opcode::AddRR => {
            let a = inst.operands[1].as_vreg();
            let b = inst.operands[2].as_vreg();
            (a == Some(iv) && const_value(func, def, b.unwrap_or(iv)) == Some(1))
                || (b == Some(iv) && const_value(func, def, a.unwrap_or(iv)) == Some(1))
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Transformation
// ---------------------------------------------------------------------------

/// Per-lowering context: fresh blocks + caches.
struct LowerCtx {
    iv: VReg,
    acc: VReg,
    /// The single loop-carried base index vector `[iv, iv+1, iv+2, iv+3]`.
    vidx0: VReg,
    /// Broadcast lane offsets: `voff[k] = broadcast(k*VF)` (`voff[0]` unused).
    voff: Vec<VReg>,
    /// Accumulator index in `0..UNROLL` — its lanes are `vidx0 + k*VF`.
    accum: usize,
    /// Lazily rematerialized per-accumulator index `vidx0 + voff[accum]`, built
    /// only if the term references the index directly (not via a shared product).
    vi_cache: HashMap<usize, VReg>,
    vbody: BlockId,
    preheader_term: InstId,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    const_cache: HashMap<i64, VReg>,
    memo: HashMap<u32, VReg>,
    /// Cross-accumulator strength reduction: base product `vidx0 * c` for an
    /// `iv * const` node (keyed by that node's scalar result id). Accumulator
    /// `k > 0` reuses it as `base + broadcast(k*VF*c)` instead of re-multiplying.
    /// Persists across accumulators (unlike `memo`).
    base_products: HashMap<u32, VReg>,
}

impl LowerCtx {
    /// The per-lane index vector for the accumulator currently being lowered,
    /// materialized on demand: accumulator 0 uses the carried `vidx0`; others
    /// rematerialize `vidx0 + voff[accum]` in the body (once per accumulator).
    fn current_vi(&mut self, func: &mut MachFunction) -> Option<VReg> {
        if self.accum == 0 {
            return Some(self.vidx0);
        }
        if let Some(&v) = self.vi_cache.get(&self.accum) {
            return Some(v);
        }
        let d = alloc(func, RegClass::Fpr128)?;
        emit(
            func,
            self.vbody,
            AArch64Opcode::NeonAddV,
            vec![
                vreg(d),
                vreg(self.vidx0),
                vreg(*self.voff.get(self.accum)?),
                imm(ARR_S4),
            ],
        )?;
        self.vi_cache.insert(self.accum, d);
        Some(d)
    }
}

/// Number of independent vector accumulators (ILP). `UNROLL * VF` i32 lanes are
/// processed per vector iteration (16 with VF=4).
const UNROLL: usize = 4;

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    // IDEMPOTENCE: never vectorize the remainder loop of a loop this pass
    // already vectorized (see `crate::vector_remainder`).
    if crate::vector_remainder::preheader_folds_neon_lane_into(func, rec.preheader, rec.acc) {
        return false;
    }
    crate::candidate::commit(func, |candidate| apply_candidate(candidate, rec))
}

fn apply_candidate(func: &mut MachFunction, rec: &Recognized) -> Option<()> {
    let width = UNROLL as i64 * VF; // lanes per vector iteration (16)
    let vh = func.try_create_block()?;
    let vb = func.try_create_block()?;
    let vl = func.try_create_block()?;
    let vx = func.try_create_block()?;
    insert_new_blocks_before(func, rec.guard, &[vh, vb, vl, vx])?;

    // These edges and all setup instructions remain private until the entire
    // candidate, including the final entry-edge splice, succeeds.
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: UNROLL independent zeroed vector accumulators.
    let wz = alloc(func, RegClass::Gpr32)?;
    emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(wz), imm(0)])?;
    let vacc: Vec<VReg> = (0..UNROLL)
        .map(|_| {
            let a = alloc(func, RegClass::Fpr128)?;
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonDupGen,
                vec![vreg(a), vreg(wz), imm(ELEM_S)],
            )?;
            Some(a)
        })
        .collect::<Option<Vec<_>>>()?;

    // --- Preheader: sign-extend the loop bound once.
    let nb64 = alloc(func, RegClass::Gpr64)?;
    emit_before(
        func,
        pre,
        AArch64Opcode::Sxtw,
        vec![vreg(nb64), vreg(rec.bound)],
    )?;

    // --- Preheader: materialize the single carried base index vector
    // vidx0 = [iv, iv+1, iv+2, iv+3] and the broadcast lane offsets voff[k] =
    // broadcast(k*VF). Only vidx0 is loop-carried (advanced by `vstep =
    // broadcast(width)` each iteration — vector strength reduction). Accumulator
    // `k`'s index is derived on demand as `vidx0 + voff[k]`, so an accumulator
    // whose term uses the index only through shared `iv*const` products never
    // materializes its index at all.
    let vidx0 = alloc(func, RegClass::Fpr128)?;
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonDupGen,
        vec![vreg(vidx0), vreg(rec.iv), imm(ELEM_S)],
    )?;
    for lane in 1..VF {
        let sc = alloc(func, RegClass::Gpr32)?;
        emit_before(
            func,
            pre,
            AArch64Opcode::AddRI,
            vec![vreg(sc), vreg(rec.iv), imm(lane)],
        )?;
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonInsGen,
            vec![vreg(vidx0), vreg(sc), imm(lane), imm(ELEM_S)],
        )?;
    }
    let vstep = dup_const_pre(func, pre, width)?;
    let voff: Vec<VReg> = (0..UNROLL)
        .map(|k| {
            if k == 0 {
                Some(vidx0) // accumulator zero uses the base directly
            } else {
                dup_const_pre(func, pre, k as i64 * VF)
            }
        })
        .collect::<Option<Vec<_>>>()?;

    // --- Vector header: guard `sxtw(iv) + (width-1) < sxtw(bound)` (i64, no
    // overflow) — enough for a full `width`-lane block.
    let gi = alloc(func, RegClass::Gpr64)?;
    let gilast = alloc(func, RegClass::Gpr64)?;
    emit(func, vh, AArch64Opcode::Sxtw, vec![vreg(gi), vreg(rec.iv)])?;
    emit(
        func,
        vh,
        AArch64Opcode::AddRI,
        vec![vreg(gilast), vreg(gi), imm(width - 1)],
    )?;
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(gilast), vreg(nb64)],
    )?;
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LT), block(vb)])?;
    emit(func, vh, AArch64Opcode::B, vec![block(vx)])?;

    // --- Vector body: for each accumulator, lower TERM over its index and
    // accumulate. Constants and `iv*const` base products are shared across
    // accumulators (the per-lane `memo` is reset per accumulator; `const_cache`
    // and `base_products` persist). After all accumulators, advance the single
    // carried base index once.
    let mut ctx = LowerCtx {
        iv: rec.iv,
        acc: rec.acc,
        vidx0,
        voff,
        accum: 0,
        vi_cache: HashMap::default(),
        vbody: vb,
        preheader_term: pre,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        const_cache: HashMap::default(),
        memo: HashMap::default(),
        base_products: HashMap::default(),
    };
    for (k, &acc) in vacc.iter().enumerate().take(UNROLL) {
        ctx.accum = k;
        ctx.memo.clear();
        let vterm = lower_term(func, &mut ctx, rec.term)?;
        emit(
            func,
            vb,
            AArch64Opcode::NeonAddV,
            vec![vreg(acc), vreg(acc), vreg(vterm), imm(ARR_S4)],
        )?;
    }
    // Advance the carried base index once (all per-accumulator indices are
    // derived from it, so a single advance suffices).
    emit(
        func,
        vb,
        AArch64Opcode::NeonAddV,
        vec![vreg(vidx0), vreg(vidx0), vreg(vstep), imm(ARR_S4)],
    )?;
    emit(func, vb, AArch64Opcode::B, vec![block(vl)])?;

    // --- Vector latch: advance the scalar induction by `width`.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    )?;
    emit(func, vl, AArch64Opcode::B, vec![block(vh)])?;

    // --- Vector exit: combine the accumulators (balanced vector adds), then
    // horizontally reduce (UMOV each lane + scalar add) and seed the scalar acc.
    let mut level = vacc.clone();
    while level.len() > 1 {
        let mut next = Vec::new();
        let mut i = 0;
        while i + 1 < level.len() {
            let d = alloc(func, RegClass::Fpr128)?;
            emit(
                func,
                vx,
                AArch64Opcode::NeonAddV,
                vec![vreg(d), vreg(level[i]), vreg(level[i + 1]), imm(ARR_S4)],
            )?;
            next.push(d);
            i += 2;
        }
        if i < level.len() {
            next.push(level[i]);
        }
        level = next;
    }
    let vsum = level[0];
    let lane_regs: Vec<VReg> = (0..VF)
        .map(|lane| {
            let w = alloc(func, RegClass::Gpr32)?;
            emit(
                func,
                vx,
                AArch64Opcode::NeonUmovGen,
                vec![vreg(w), vreg(vsum), imm(lane), imm(ELEM_S)],
            )?;
            Some(w)
        })
        .collect::<Option<Vec<_>>>()?;
    let s01 = alloc(func, RegClass::Gpr32)?;
    let s23 = alloc(func, RegClass::Gpr32)?;
    let ssum = alloc(func, RegClass::Gpr32)?;
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(s01), vreg(lane_regs[0]), vreg(lane_regs[1])],
    )?;
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(s23), vreg(lane_regs[2]), vreg(lane_regs[3])],
    )?;
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(ssum), vreg(s01), vreg(s23)],
    )?;
    // FOLD the vector partial sum INTO the scalar accumulator — never
    // overwrite it.
    //
    // WRONG-CODE FIX (2026-08-18): this was `MovR acc, ssum`, which silently
    // DROPPED the accumulator's pre-loop value M0. `vx` sits on the only edge
    // out of the vector loop, so it runs on every path (including a zero-trip
    // vector loop), and recognition never required `acc == 0` on the preheader
    // edge — it only constrains how `acc` is carried and read. A source
    // reduction seeded with a non-zero value (`let mut acc = seed;`) therefore
    // computed `sum(TERM)` instead of `seed + sum(TERM)`, wrong by exactly the
    // seed for every trip count. This invariant is independent of which
    // frontend produced the recognized loop.
    //
    // At `vx` the accumulator still holds M0 because the vector loop
    // accumulates only into the NEON lane registers and never writes `acc`.
    // Every sibling drain already folds: `apply_chain` below ("Fold the
    // extracted lanes into `acc` (= M0)"), and neon_array's ("never overwrite:
    // preserves a non-zero initial acc"). The STRICT recognizer admits only
    // `AddRR`/`Madd` reductions, so ADD is the correct fold operator.
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(rec.acc), vreg(rec.acc), vreg(ssum)],
    )?;
    emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)])?;

    // Admit the original entry edge before redirecting the private candidate.
    // A missing/mismatched anchor discards the candidate, including its setup.
    crate::candidate::splice_edge(func, rec.preheader, rec.preheader_term, rec.guard, vh)?;
    func.add_edge(vx, rec.guard);

    Some(())
}

/// Materialize a broadcast `4 x i32` constant vector in the preheader (not
/// cached — used for the small index offset/step constants).
fn dup_const_pre(func: &mut MachFunction, pre: InstId, value: i64) -> Option<VReg> {
    let w = alloc(func, RegClass::Gpr32)?;
    let v = alloc(func, RegClass::Fpr128)?;
    emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(w), imm(value)])?;
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonDupGen,
        vec![vreg(v), vreg(w), imm(ELEM_S)],
    )?;
    Some(v)
}

/// Lower `term` to a `4 x i32` NEON value (in the vector body). Returns `None`
/// on a missing recognized shape or failed candidate construction.
fn lower_term(func: &mut MachFunction, ctx: &mut LowerCtx, term: Term) -> Option<VReg> {
    match term {
        Term::Value(v) => lower(func, ctx, v),
        Term::MulPair(a, b) => {
            let va = lower(func, ctx, a)?;
            let vb = lower(func, ctx, b)?;
            Some(bin(func, ctx, AArch64Opcode::NeonMulV, va, vb, true)?)
        }
    }
}

fn lower(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> Option<VReg> {
    if val == ctx.iv {
        return ctx.current_vi(func);
    }
    if val == ctx.acc {
        return None;
    }
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
    }
    if let Some(imm_v) = const_value(func, &ctx.def, val) {
        let v = const_vec(func, ctx, imm_v)?;
        ctx.memo.insert(val.id, v);
        return Some(v);
    }
    let &def_id = ctx.def.get(&val.id)?;
    if !ctx.loop_insts.contains(&def_id) {
        return None;
    }
    let inst = func.inst(def_id);
    let opcode = inst.opcode;
    let ops = inst.operands.clone();
    use AArch64Opcode::*;
    let result = match opcode {
        MulRR => {
            // Cross-accumulator strength reduction for `iv * const`: distribute
            // the multiply over the per-accumulator index offset so it is
            // computed once (accumulator 0) and reused as `base + k*VF*c`.
            if let Some(multiplier) = shared_iv_multiplier(func, ctx, &ops) {
                lower_shared_iv_mul(func, ctx, val.id, multiplier)?
            } else {
                let (a, b) = lower_two(func, ctx, &ops)?;
                bin(func, ctx, NeonMulV, a, b, true)?
            }
        }
        AddRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonAddV, a, b, true)?
        }
        SubRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonSubV, a, b, true)?
        }
        AndRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonAndV, a, b, false)?
        }
        OrrRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonOrrV, a, b, false)?
        }
        EorRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonEorV, a, b, false)?
        }
        AddRI | SubRI | AndRI | OrrRI | EorRI => {
            let a = lower(func, ctx, ops[1].as_vreg()?)?;
            let cvec = const_vec(func, ctx, ops[2].as_imm()?)?;
            let (nop, arr) = match opcode {
                AddRI => (NeonAddV, true),
                SubRI => (NeonSubV, true),
                AndRI => (NeonAndV, false),
                OrrRI => (NeonOrrV, false),
                _ => (NeonEorV, false),
            };
            bin(func, ctx, nop, a, cvec, arr)?
        }
        LslRI | LsrRI | AsrRI => {
            let a = lower(func, ctx, ops[1].as_vreg()?)?;
            let sh = ops[2].as_imm()?;
            let nop = match opcode {
                LslRI => NeonShlVImm,
                LsrRI => NeonUshrVImm,
                _ => NeonSshrVImm,
            };
            let d = alloc(func, RegClass::Fpr128)?;
            emit(
                func,
                ctx.vbody,
                nop,
                vec![vreg(d), vreg(a), imm(sh), imm(ARR_S4)],
            )?;
            d
        }
        Madd => {
            let a = lower(func, ctx, ops[1].as_vreg()?)?;
            let b = lower(func, ctx, ops[2].as_vreg()?)?;
            let c = lower(func, ctx, ops[3].as_vreg()?)?;
            let m = bin(func, ctx, NeonMulV, a, b, true)?;
            bin(func, ctx, NeonAddV, m, c, true)?
        }
        _ => return None,
    };
    ctx.memo.insert(val.id, result);
    Some(result)
}

/// Cross-accumulator strength reduction for a scalar `iv * const` multiply.
///
/// Because accumulator `k`'s index vector is `vidx[0] + broadcast(k*VF)`,
/// distributivity over `Z/2^32` gives `idx_k * c = idx_0 * c + broadcast(k*VF*c)`.
/// So the multiply is computed ONCE (accumulator 0, cached in `base_products`)
/// and every other accumulator adds a loop-invariant constant vector instead of
/// re-multiplying. Returns `None` (fall back to a plain vector
/// multiply) unless one operand is exactly the induction variable, the other a
/// 16-bit constant `c`, and the largest offset `(UNROLL-1)*VF*c` fits a 16-bit
/// broadcast constant. Sound: it never changes the per-lane value.
fn shared_iv_multiplier(func: &MachFunction, ctx: &LowerCtx, ops: &[MachOperand]) -> Option<i64> {
    let a = ops.get(1)?.as_vreg()?;
    let b = ops.get(2)?.as_vreg()?;
    let c = if a == ctx.iv {
        const_value(func, &ctx.def, b)?
    } else if b == ctx.iv {
        const_value(func, &ctx.def, a)?
    } else {
        return None;
    };
    let max_off = (VF * (UNROLL as i64 - 1)).checked_mul(c)?;
    if !(0..=0xFFFF).contains(&max_off) {
        return None;
    }
    Some(c)
}

/// Construction failure is not "no shared pattern": it must abort the private
/// candidate, never fall back after partially emitting a shared product.
fn lower_shared_iv_mul(
    func: &mut MachFunction,
    ctx: &mut LowerCtx,
    val_id: u32,
    c: i64,
) -> Option<VReg> {
    if ctx.accum == 0 {
        let cvec = const_vec(func, ctx, c)?;
        let vi0 = ctx.current_vi(func)?;
        let p0 = bin(func, ctx, AArch64Opcode::NeonMulV, vi0, cvec, true)?;
        ctx.base_products.insert(val_id, p0);
        Some(p0)
    } else {
        let p0 = *ctx.base_products.get(&val_id)?;
        let off = VF * ctx.accum as i64 * c;
        let offvec = const_vec(func, ctx, off)?;
        Some(bin(func, ctx, AArch64Opcode::NeonAddV, p0, offvec, true)?)
    }
}

fn lower_two(
    func: &mut MachFunction,
    ctx: &mut LowerCtx,
    ops: &[MachOperand],
) -> Option<(VReg, VReg)> {
    let a = lower(func, ctx, ops.get(1)?.as_vreg()?)?;
    let b = lower(func, ctx, ops.get(2)?.as_vreg()?)?;
    Some((a, b))
}

/// Emit a same-shape binary NEON op `d = op(a, b)` in the vector body.
/// `arr` selects whether the op carries an arrangement immediate (arithmetic:
/// `.4S`) or none (bitwise logic: `.16B`, Q inferred from the FPR128 class).
fn bin(
    func: &mut MachFunction,
    ctx: &LowerCtx,
    op: AArch64Opcode,
    a: VReg,
    b: VReg,
    arr: bool,
) -> Option<VReg> {
    let d = alloc(func, RegClass::Fpr128)?;
    let mut operands = vec![vreg(d), vreg(a), vreg(b)];
    if arr {
        operands.push(imm(ARR_S4));
    }
    emit(func, ctx.vbody, op, operands)?;
    Some(d)
}

/// Materialize (once) a broadcast `4 x i32` constant vector in the preheader.
fn const_vec(func: &mut MachFunction, ctx: &mut LowerCtx, value: i64) -> Option<VReg> {
    if let Some(&v) = ctx.const_cache.get(&value) {
        return Some(v);
    }
    let w = alloc(func, RegClass::Gpr32)?;
    let v = alloc(func, RegClass::Fpr128)?;
    emit_before(
        func,
        ctx.preheader_term,
        AArch64Opcode::Movz,
        vec![vreg(w), imm(value)],
    )?;
    emit_before(
        func,
        ctx.preheader_term,
        AArch64Opcode::NeonDupGen,
        vec![vreg(v), vreg(w), imm(ELEM_S)],
    )?;
    ctx.const_cache.insert(value, v);
    Some(v)
}

// ---------------------------------------------------------------------------
// Small local IR helpers (kept independent of vectorize.rs)
// ---------------------------------------------------------------------------

fn vreg(v: VReg) -> MachOperand {
    MachOperand::VReg(v)
}
fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn block(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}

// ===========================================================================
// FORWARD-CHAIN K-way BITWISE reduction (`acc OP= a[i]`, OP in {&, |, ^})
//
// The strict 2-block path above vectorizes an ADD reduction whose term is a
// lane-wise function of the INDUCTION variable (no memory). This second path
// vectorizes the complementary shape the bridge emits for
//
//   let mut sa = !0; let mut so = 0; let mut i = 0;
//   while i < N { sa &= a[i]; so |= a[i]; i += 1; }   // K reductions, one loop
//
// over a LOCAL fixed-size array: each `a[i]` access carries its own `i <u N`
// bounds-check, so the straight-line body is spread across a FORWARD CHAIN of
// blocks (`header(i<N?) -> g/passthrough -> ... -> latch -> header`), and there
// are K >= 1 UNCONDITIONAL bitwise reductions (`iv + K` latch writebacks). This
// is the SAME systemic forward-chain gap already closed for neon_map /
// neon_array / neon_minmax / neon_predsum; the recognizer mirrors
// `neon_map::recognize_forward_chain` (SINGLE-N agreement over the loop-continue
// + every bounds-guard limit) and the K-reduction collection mirrors
// `neon_predsum`'s `result_wbs`, but the reduction operator is a BITWISE
// AND/OR/XOR (associative + commutative) instead of ADD.
//
// ## Equivalence argument
//
// The transform is purely ADDITIVE (like the whole neon family): `apply_chain`
// splices a vector main loop in FRONT of the scalar loop header and NEVER edits
// the scalar chain. Its tail `[V, N)` still requires the correct entry state.
// The intended bounds and reduction arguments follow; they are not a complete
// transform proof or current solver/checker discharge:
//
//   * IN-BOUNDS (additive subset): every guard in the chain is the array bounds
//     check `iv <u a.len()` (panic otherwise), and we fire ONLY when the
//     loop-continue limit AND every bounds-guard limit are the SAME constant `N`
//     compared against a copy of the SAME induction — so `N == a.len()` for
//     every array the body touches. The vector header admits a block only while
//     `iv <u N-(width-1)`, i.e. `iv+width-1 < N`, so every vector element index
//     lies in `[0, N) = [0, a.len())` — a SUBSET of what the scalar loop reads.
//   * FAITHFUL: each reduction is `acc = acc OP a[iv]` with OP an associative +
//     commutative bitwise monoid. `apply_chain` seeds `UNROLL` vector
//     accumulators PER reduction with the per-lane IDENTITY (all-ones `0xFF` for
//     AND, `0` for OR/XOR), accumulates `vacc = OP(vacc, load)` over disjoint
//     lane subsets of `[0, V)`, then combines the accumulators and horizontally
//     folds them with the SAME OP — reproducing `OP_{j in [0,V)} a[j]` regardless
//     of grouping (assoc + comm). The pre-loop scalar accumulator value `M0` is
//     folded in once (`acc = OP(M0, lanes...)`); when NO vector iteration runs
//     the accumulators are still the identity, so the fold is `OP(M0, identity…)
//     = M0` and the untouched scalar loop does everything. The two reductions
//     read the SAME `a[iv]` — the load is issued ONCE per base and fed to both.
//
// Fail-closed on ANY deviation. The load is read-only (the whitelist forbids
// StrRI), so aliasing is irrelevant; the reduction target is a register.
// ===========================================================================

/// A recognized `neon-reduce` plan: the strict 2-block induction-term ADD
/// reduction, or a forward-chain K-way bitwise reduction.
enum Plan {
    Strict(Recognized),
    Chain(BitChainRecognized),
}

/// An associative + commutative reduction operator.
///
/// # Lane width is NOT optional for every member
///
/// The three BITWISE members (`And`/`Or`/`Xor`) are lane-width AGNOSTIC: AND/OR/
/// XOR give the same answer whether a 128-bit register is read as 16 x i8 or
/// 2 x i64, so they use the whole-register `.16B` forms which carry no
/// arrangement.
///
/// `Add` is NOT. Carries do not cross lane boundaries, so a `NeonAddV` issued
/// with the wrong arrangement computes e.g. sixteen byte-wise sums where the
/// source semantics is a 64-bit `wrapping_add` — a SILENT WRONG-VALUE
/// miscompile, not a crash. Worse, `neon_arrangement` in the encoder reads the
/// LAST operand and falls back to `S4` for anything unrecognized, so simply
/// forgetting the arrangement operand yields 4 x 32-bit adds rather than an
/// error.
///
/// That is why the vector-op API here is [`ReduceOp::vec_op_operands`], which
/// returns the COMPLETE operand list, rather than a bare opcode: it makes
/// omitting the arrangement structurally impossible at the call site.
///
/// Reassociating integer addition is EXACT (it is associative and commutative
/// with identity 0), so unlike float reduction there is no reordering concern.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ReduceOp {
    And,
    Or,
    Xor,
    Add,
}

impl ReduceOp {
    fn from_opcode(op: AArch64Opcode) -> Option<ReduceOp> {
        match op {
            AArch64Opcode::AndRR => Some(ReduceOp::And),
            AArch64Opcode::OrrRR => Some(ReduceOp::Or),
            AArch64Opcode::EorRR => Some(ReduceOp::Xor),
            AArch64Opcode::AddRR => Some(ReduceOp::Add),
            _ => None,
        }
    }

    /// The COMPLETE operand list for one vector reduction step
    /// `dst = OP(a, b)`.
    ///
    /// Bitwise ops emit the arrangement-free `.16B` form. `Add` appends the
    /// arrangement immediate matching the element width — `D2` (2 x i64) or
    /// `S4` (4 x i32) — which is the whole reason this returns operands instead
    /// of an opcode. See the type docs.
    fn vec_op_operands(
        self,
        dst: VReg,
        a: VReg,
        b: VReg,
        is_i64: bool,
    ) -> (AArch64Opcode, Vec<MachOperand>) {
        let base = vec![vreg(dst), vreg(a), vreg(b)];
        match self {
            ReduceOp::And => (AArch64Opcode::NeonAndV, base),
            ReduceOp::Or => (AArch64Opcode::NeonOrrV, base),
            ReduceOp::Xor => (AArch64Opcode::NeonEorV, base),
            ReduceOp::Add => {
                let arrangement = if is_i64 {
                    ARRANGEMENT_D2
                } else {
                    ARRANGEMENT_S4
                };
                let mut ops = base;
                ops.push(imm(arrangement));
                (AArch64Opcode::NeonAddV, ops)
            }
        }
    }

    /// The scalar GPR opcode for the horizontal fold.
    ///
    /// Width-correct for every member INCLUDING `Add`: the fold extracts lanes
    /// into GPRs of `const_class` (Gpr64 for i64, Gpr32 for i32) and combines
    /// them there, so the addition happens at the element width rather than
    /// across packed lanes.
    fn scalar_op(self) -> AArch64Opcode {
        match self {
            ReduceOp::And => AArch64Opcode::AndRR,
            ReduceOp::Or => AArch64Opcode::OrrRR,
            ReduceOp::Xor => AArch64Opcode::EorRR,
            ReduceOp::Add => AArch64Opcode::AddRR,
        }
    }

    /// `MOVI Vd.16B, #imm` immediate for the per-lane reduction identity:
    /// all-ones (`0xFF` byte-replicate => every lane all-ones, any width) for
    /// AND, all-zeros for OR/XOR/ADD.
    ///
    /// Zero is the correct identity for ADD at EVERY lane width, so the
    /// byte-replicated MOVI remains valid here — this is the one place `Add`
    /// does not need width threading, which is precisely what makes the
    /// omission in `vec_op_operands` easy to miss.
    fn identity_movi(self) -> i64 {
        match self {
            ReduceOp::And => 0xFF,
            ReduceOp::Or | ReduceOp::Xor | ReduceOp::Add => 0,
        }
    }
}

/// `neon_arrangement` operand codes (encoder: `2S`=4, `4S`=5, `2D`=6).
const ARRANGEMENT_S4: i64 = 5;
const ARRANGEMENT_D2: i64 = 6;

/// The loop-continue / bounds-guard limit of a forward `while iv <u N` chain: a
/// constant `CmpRI(iv, Imm(N))` (the folded form for a local fixed-size array)
/// or a register `CmpRR(iv, N_reg)`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ChainBound {
    Const(i64),
    Reg(VReg),
}

/// One recognized bitwise reduction inside a forward chain: `acc = acc OP a[iv]`.
struct BitChainReduction {
    op: ReduceOp,
    /// The loop-carried accumulator (its latch-writeback destination).
    acc: VReg,
    /// Loop-invariant base pointer of the `a[iv]` load (its lane-wise loaded
    /// value IS the per-iteration term).
    base: VReg,
}

/// A fully validated forward-chain, K-way, UNCONDITIONAL bitwise reduction loop.
/// `Gpr64` induction; the element/accumulator width is uniform (`Gpr32` `.4S` or
/// `Gpr64` `.2D`).
struct BitChainRecognized {
    /// The loop header (== the vectorizer's splice point / `guard`).
    guard: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    iv: VReg,
    /// Compile-time loop bound `N` (constant, `[1, i32::MAX]`).
    bound: i64,
    /// True when the elements/accumulators are `i64` (`.2D` path); false = `i32`
    /// (`.4S`). Bitwise vector ops are width-agnostic; only the load element
    /// size, lane count, and scalar fold width differ.
    is_i64: bool,
    reductions: Vec<BitChainReduction>,
    /// Distinct candidate base pointers (first-seen order) — one running pointer
    /// + one paired load stream each in `apply_chain`.
    bases: Vec<VReg>,
    /// The loop-state contract (`crate::loop_contract`) passed for
    /// `iv` and every reduction accumulator. The plan cannot be built without it.
    _locality: LoopLocality,
    /// The scalar loop's exit, when the vector loop provably leaves the scalar
    /// tail no iteration (see [`dead_tail_exit`]): the drain then branches
    /// straight to it and the scalar loop becomes unreachable.
    dead_tail_exit: Option<BlockId>,
}

/// Opcodes permitted anywhere in the bitwise-chain loop body. Anything else ⇒
/// BAIL. Note the ABSENCE of `StrRI` (a store makes `a[iv]` non-loop-stable and
/// introduces aliasing) and of `Csel`/`CSet` (a predicated reduction belongs to
/// neon-predsum/neon-minmax) — both fail closed.
fn allowed_chain_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR
            | AddRI
            | SubRR
            | SubRI
            | MulRR
            | Madd
            | AndRR
            | AndRI
            | OrrRR
            | OrrRI
            | EorRR
            | EorRI
            | LslRI
            | LsrRI
            | AsrRI
            | Movz
            | Movn
            | Movk
            | MovR
            | Copy
            | CmpRR
            | CmpRI
            | BCond
            | B
            | Sxtw
            | Uxtw
            | LdrRI
    )
}

/// Build a def map (`vreg id -> defining InstId`) over ONLY the LIVE
/// instructions (reachable through `block_order`), EXCLUDING `StrRI` /
/// `TrapBoundsCheckExact` from `produces_def` (their operand 0 is a stored VALUE
/// / an index READ, never a def, so admitting them would shadow a real def).
/// The flat [`build_def_map`] instead iterates raw storage and treats every
/// operand-0 as a def, which a detached carrier or a store elsewhere can use to
/// shadow the real in-block def. Mirrors `neon_predsum::build_live_def_map` (the
/// "key fix"). When a vreg has multiple LIVE defs (loop-carried phis: `iv`, each
/// `acc`) the last in block/program order wins, tolerated because the walkers
/// check `== iv` / `== acc` before following a def.
fn build_live_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    crate::effects::build_reaching_def_map(func)
}

/// Count the definitions of `v` inside `loop_insts`.
fn count_loop_defs(func: &MachFunction, loop_insts: &HashSet<InstId>, v: VReg) -> usize {
    loop_insts
        .iter()
        .filter(|&&id| crate::effects::inst_defines_vreg(func.inst(id), v))
        .count()
}

/// Recognize the terminating guard diamond `cmp x, N; b.lo t_lo; b t_b` (last
/// three instructions) with the unsigned-`LO` taken edge `t_lo` IN the loop and
/// the fall-through `t_b` OUT of it. `N` is a constant immediate (`CmpRI`) or a
/// register (`CmpRR`). Mirrors `neon_predsum::recognize_chain_guard`.
/// Fail-closed on any other shape.
fn recognize_chain_guard(
    func: &MachFunction,
    blk: BlockId,
    body: &HashSet<BlockId>,
) -> Option<(VReg, ChainBound, BlockId)> {
    let insts = &func.block(blk).insts;
    let n = insts.len();
    if n < 3 {
        return None;
    }
    let cmp = func.inst(insts[n - 3]);
    let bcond = func.inst(insts[n - 2]);
    let br = func.inst(insts[n - 1]);
    if bcond.opcode != AArch64Opcode::BCond
        || br.opcode != AArch64Opcode::B
        || bcond.operands[0].as_imm()? != CC_LO
    {
        return None;
    }
    let (x, bound) = match cmp.opcode {
        AArch64Opcode::CmpRR => (
            cmp.operands[0].as_vreg()?,
            ChainBound::Reg(cmp.operands[1].as_vreg()?),
        ),
        AArch64Opcode::CmpRI => (
            cmp.operands[0].as_vreg()?,
            ChainBound::Const(cmp.operands[1].as_imm()?),
        ),
        _ => return None,
    };
    let t_lo = *branch_targets(bcond).first()?;
    let t_b = *branch_targets(br).first()?;
    if !body.contains(&t_lo) || body.contains(&t_b) {
        return None;
    }
    Some((x, bound, t_lo))
}

/// Two chain bounds agree iff same constant / same register (after copy strip) /
/// register-resolves-to-the-constant on every path ([`const_value`]).
/// Mirrors `neon_predsum::chain_bound_agrees`.
fn chain_bound_agrees(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    a: ChainBound,
    b: ChainBound,
) -> bool {
    match (a, b) {
        (ChainBound::Const(x), ChainBound::Const(y)) => x == y,
        (ChainBound::Reg(x), ChainBound::Reg(y)) => {
            strip_copies(func, def, x) == strip_copies(func, def, y)
                || matches!(
                    (const_value(func, def, x), const_value(func, def, y)),
                    (Some(p), Some(q)) if p == q
                )
        }
        (ChainBound::Const(x), ChainBound::Reg(r)) | (ChainBound::Reg(r), ChainBound::Const(x)) => {
            const_value(func, def, r) == Some(x)
        }
    }
}

/// Recognize an `a[iv]` load (offset 0): `dst = *(base + idx*elem)` with `dst`
/// the element width (`Gpr32` i32 / `Gpr64` i64), `idx` a copy of `iv` (mixed
/// `Gpr64` induction used directly) OR `Sxtw(iv)`/`Uxtw(iv)`, the element size
/// the constant `elem`, and `base` loop-invariant (its def dominates the
/// preheader). Returns `base`. Mirrors `neon_predsum::load_base` /
/// `neon_minmax::chain_load_base`. Fail-closed otherwise.
fn chain_load_base(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    dst: VReg,
    iv: VReg,
    preheader: BlockId,
    is_i64: bool,
) -> Option<VReg> {
    let (want_class, elem_bytes) = if is_i64 {
        (RegClass::Gpr64, ELEM_BYTES_I64)
    } else {
        (RegClass::Gpr32, ELEM_BYTES)
    };
    if dst.class != want_class {
        return None;
    }
    let load = func.inst(*def.get(&dst.id)?);

    // FORM 2: scaled register-offset load, `LDR Xt, [Xbase, Xiv, LSL #k]`.
    //
    // This is the shape isel produces for a bounds-checked slice/Vec index such
    // as h1_vec_push_sum's `v[k]`, and it was previously unrecognized — the
    // Chain plan only ever accepted FORM 1 below (`LdrRI` off a `Madd`-computed
    // address), so a whole class of reducible loops silently kept the scalar
    // loop.
    //
    // Operands: [Rt, Rn(base), Rm(index), Imm(packed)] where
    // `packed = (option << 1) | S`, option 0b011 = LSL. S=1 means "scale by
    // log2(access size)", which is exactly elem_bytes, so S=1 is REQUIRED: with
    // S=0 the index is a byte offset and the same vector plan would stride the
    // wrong distance.
    if load.opcode == AArch64Opcode::LdrRO {
        if load.operands.len() != 4 {
            return None;
        }
        let base = load.operands[1].as_vreg()?;
        let index = load.operands[2].as_vreg()?;
        let packed = load.operands[3].as_imm()?;
        // option must be LSL (0b011) and S must be 1 (element-scaled).
        if (packed >> 1) & 0b111 != 0b011 || packed & 1 != 1 {
            return None;
        }
        if !copies_reg(func, def, index, iv) {
            return None;
        }
        let base_def = *def.get(&base.id)?;
        let base_block = block_of_inst(func, base_def)?;
        if !dom.dominates(base_block, preheader) {
            return None;
        }
        return Some(base);
    }

    // FORM 1: `LdrRI` at offset 0 off an address computed by `Madd`.
    if load.opcode != AArch64Opcode::LdrRI
        || load.operands.len() != 3
        || load.operands[2].as_imm() != Some(0)
    {
        return None;
    }
    let addr = load.operands[1].as_vreg()?;
    let madd = func.inst(*def.get(&addr.id)?);
    if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
        return None;
    }
    let f1 = madd.operands[1].as_vreg()?;
    let f2 = madd.operands[2].as_vreg()?;
    let base = madd.operands[3].as_vreg()?;
    let is_ext_iv = |factor: VReg| -> bool {
        let Some(&id) = def.get(&factor.id) else {
            return false;
        };
        let inst = func.inst(id);
        matches!(inst.opcode, AArch64Opcode::Sxtw | AArch64Opcode::Uxtw)
            && inst.operands.len() == 2
            && inst.operands[1]
                .as_vreg()
                .is_some_and(|s| copies_reg(func, def, s, iv))
    };
    let idx_ok = |factor: VReg| copies_reg(func, def, factor, iv) || is_ext_iv(factor);
    let es_ok = |factor: VReg| const_value(func, def, factor) == Some(elem_bytes);
    if !((idx_ok(f1) && es_ok(f2)) || (idx_ok(f2) && es_ok(f1))) {
        return None;
    }
    let base_def = *def.get(&base.id)?;
    let base_block = block_of_inst(func, base_def)?;
    if !dom.dominates(base_block, preheader) {
        return None;
    }
    Some(base)
}

/// Materialize a non-negative i32-range constant into a fresh preheader vreg via
/// the isel `Movz`(+`Movk`) convention. Used for the compile-time vector guard
/// limit (the loop bound is a folded immediate inside the loop). Mirrors
/// `neon_predsum::materialize_const`.
fn materialize_const(
    func: &mut MachFunction,
    pre: InstId,
    k: i64,
    class: RegClass,
) -> Option<VReg> {
    let b = alloc(func, class)?;
    let lo = k & 0xFFFF;
    let hi = (k >> 16) & 0xFFFF;
    emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(b), imm(lo)])?;
    if hi != 0 {
        emit_before(
            func,
            pre,
            AArch64Opcode::Movk,
            vec![vreg(b), imm(hi), imm(16)],
        )?;
    }
    Some(b)
}

impl BitChainRecognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // A strict 2-block loop is handled by [`Recognized`]; the chain has
        // header + latch + at least one middle block.
        if header == latch || body.len() < 3 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // Whitelist every opcode across EVERY body block (no store/call/div/
        // select/etc). No `StrRI` makes every `a[iv]` load LOOP-STABLE.
        let mut loop_insts = HashSet::default();
        for &b in body {
            for &id in &func.block(b).insts {
                if !allowed_chain_op(func.inst(id).opcode) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

        // REQUIRED: the block-order-restricted def map (see build_live_def_map).
        let def = build_live_def_map(func);

        // Header preds = {latch, preheader}; the preheader edge branches into it.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            return None;
        }
        let preheader = *hpreds.iter().find(|&&b| b != latch)?;
        let preheader_term = *func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))?;

        // The latch's ONLY successor is the header, ending in that back-edge `B`
        // (test-first while — the exit test lives in the header guard chain).
        let lsuccs = &func.block(latch).succs;
        if lsuccs.len() != 1 || lsuccs[0] != header {
            return None;
        }
        let latch_term = *func.block(latch).insts.last()?;
        if func.inst(latch_term).opcode != AArch64Opcode::B
            || !branch_targets(func.inst(latch_term)).contains(&header)
        {
            return None;
        }

        // Latch loop-carried writebacks: the `iv = iv+1` induction plus K >= 1
        // reduction writebacks (`acc = MovR(result)`).
        let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
        for &id in &func.block(latch).insts {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                writebacks.push((d, s));
            }
        }
        let iv = writebacks
            .iter()
            .find(|(d, s)| is_increment_by_one(func, &def, *s, *d))
            .map(|(d, _)| *d)?;
        if writebacks.iter().filter(|(d, _)| *d == iv).count() != 1 {
            return None;
        }
        // The induction is the `Gpr64` `usize` counter of a `for i in 0..N` loop
        // (the mixed i64-index / element-width shape the bridge emits for a local
        // fixed-size array). A `Gpr32` induction is not vectorized here.
        if iv.class != RegClass::Gpr64 {
            return None;
        }
        let result_wbs: Vec<(VReg, VReg)> = writebacks
            .iter()
            .copied()
            .filter(|(d, _)| *d != iv)
            .collect();
        if result_wbs.is_empty() {
            return None;
        }

        // Every accumulator is a distinct register with EXACTLY ONE in-loop def
        // (its latch writeback) and a UNIFORM element width (all `Gpr32` or all
        // `Gpr64`).
        let mut accs: HashSet<u32> = HashSet::default();
        let mut is_i64: Option<bool> = None;
        for (acc, _) in &result_wbs {
            if *acc == iv || !accs.insert(acc.id) {
                return None;
            }
            let w = match acc.class {
                RegClass::Gpr32 => false,
                RegClass::Gpr64 => true,
                _ => return None,
            };
            match is_i64 {
                Some(p) if p != w => return None,
                None => is_i64 = Some(w),
                _ => {}
            }
            if count_loop_defs(func, &loop_insts, *acc) != 1 {
                return None;
            }
        }
        let is_i64 = is_i64?;

        // Decode each UNCONDITIONAL bitwise reduction: `result` (the latch
        // writeback source) must be `AndRR/OrrRR/EorRR(acc, a[iv])` (commutative),
        // and `acc` must be read ONLY by that reducer inside the loop.
        let mut reductions: Vec<BitChainReduction> = Vec::new();
        let mut bases: Vec<VReg> = Vec::new();
        for (acc, result) in &result_wbs {
            let red_src = strip_copies(func, &def, *result);
            let red_def_id = *def.get(&red_src.id)?;
            if !loop_insts.contains(&red_def_id) {
                return None;
            }
            let red_def = func.inst(red_def_id);
            let op = ReduceOp::from_opcode(red_def.opcode)?;
            if red_def.operands.len() != 3 {
                return None;
            }
            let x = red_def.operands[1].as_vreg()?;
            let y = red_def.operands[2].as_vreg()?;
            // EXACTLY one operand is the accumulator (or a copy of it); the other
            // is the per-iteration term. `copies_reg(_, acc)` never follows acc's
            // own loop-carried writeback, so it cannot be fooled by the term.
            let x_is_acc = copies_reg(func, &def, x, *acc);
            let y_is_acc = copies_reg(func, &def, y, *acc);
            let term = if x_is_acc && !y_is_acc {
                y
            } else if y_is_acc && !x_is_acc {
                x
            } else {
                return None;
            };
            if term == *acc || term == iv {
                return None;
            }
            // The term must be a bare `a[iv]` load (records the loop-invariant
            // base). A lane-wise function of the load keeps the scalar loop.
            let base = chain_load_base(func, &def, dom, term, iv, preheader, is_i64)?;
            // (R4b) `acc` read ONLY by its reducer inside the loop — any other
            // in-loop use of the mid-loop accumulator value would be dropped.
            for &id in loop_insts.iter() {
                if id == red_def_id {
                    continue;
                }
                let inst = func.inst(id);
                for opd in inst.operands.iter().skip(1) {
                    if opd.as_vreg() == Some(*acc) {
                        return None;
                    }
                }
            }
            if !bases.iter().any(|b| b.id == base.id) {
                bases.push(base);
            }
            reductions.push(BitChainReduction {
                op,
                acc: *acc,
                base,
            });
        }

        // Walk the chain header -> ... -> latch: every non-latch block is the
        // loop-continue / a surviving bounds-guard diamond (SINGLE-N agreement) or
        // a pass-through, covering EVERY body block exactly once.
        let bound = Self::walk_chain(func, &def, body, header, latch, iv)?;
        let ChainBound::Const(n) = bound else {
            return None; // only compile-time constant bounds (the folded form)
        };
        if !(1..=i32::MAX as i64).contains(&n) {
            return None;
        }

        // LOOP STATE (`crate::loop_contract`): the vector loop runs only
        // iterations the header's `iv <u N` guard continues, and reproduces `iv`
        // and the K accumulators. The chain's surviving bounds guards (on `iv`,
        // against the same `N`) are exits the contract admits by its own rule;
        // any other exit, and any other register the loop carries or leaves
        // live, refuses the loop.
        let carried: Vec<VReg> = std::iter::once(iv)
            .chain(reductions.iter().map(|reduction| reduction.acc))
            .collect();
        let chain_bound = |guard: GuardBound| match guard {
            GuardBound::Imm(n) => ChainBound::Const(n),
            GuardBound::Reg(r) => ChainBound::Reg(r),
        };
        let is_iv = |v: VReg| copies_reg(func, &def, v, iv);
        let is_bound =
            |guard: GuardBound| chain_bound_agrees(func, &def, bound, chain_bound(guard));
        let exits =
            ExitPlan::unsigned_loop_test(func, body.iter().copied(), header, &is_iv, &is_bound)?
                .and_induction_guards(
                    func,
                    body.iter().copied(),
                    header,
                    &InductionGuards {
                        iv,
                        at_most_iv: &is_iv,
                        covers_loop_bound: &is_bound,
                    },
                );
        let locality = LoopLocality::check(
            func,
            body.iter().copied(),
            header,
            &exits,
            Handoff::HeaderOrExit,
            &carried,
        )
        .ok()?;
        let width = UNROLL as i64 * if is_i64 { VF_I64 } else { VF };
        let dead_tail_exit = dead_tail_exit(func, &def, dom, header, preheader, body, iv, n, width);

        Some(BitChainRecognized {
            _locality: locality,
            guard: header,
            preheader,
            preheader_term,
            iv,
            bound: n,
            is_i64,
            reductions,
            bases,
            dead_tail_exit,
        })
    }

    /// Classify the chain and return its single loop bound. Fail-closed on any
    /// block off the header->latch structure or a limit disagreement. Mirrors
    /// `neon_map::recognize_forward_chain`'s walk (guard-diamond | pass-through);
    /// the UNCONDITIONAL reductions live inside pass-through/latch blocks and need
    /// no diamond classification (unlike neon_predsum/neon_minmax).
    fn walk_chain(
        func: &MachFunction,
        def: &HashMap<u32, InstId>,
        body: &HashSet<BlockId>,
        header: BlockId,
        latch: BlockId,
        iv: VReg,
    ) -> Option<ChainBound> {
        let mut bound: Option<ChainBound> = None;
        let mut visited: HashSet<BlockId> = HashSet::default();
        let mut cur = header;
        loop {
            if !body.contains(&cur) || !visited.insert(cur) {
                return None;
            }
            if cur == latch {
                break;
            }
            let succs = &func.block(cur).succs;
            let next = if succs.len() == 2 {
                // Loop-continue / surviving bounds-guard diamond: validate the
                // index is the induction and the limit agrees with the single N.
                let (x, b, t_lo) = recognize_chain_guard(func, cur, body)?;
                if !copies_reg(func, def, x, iv) {
                    return None;
                }
                match bound {
                    Some(bb) if !chain_bound_agrees(func, def, bb, b) => return None,
                    None => bound = Some(b),
                    _ => {}
                }
                t_lo
            } else if succs.len() == 1 {
                // Pass-through (its bounds guard was elided; the header is never a
                // pass-through, so `bound` is already set by the time we hit one).
                if bound.is_none() || !body.contains(&succs[0]) {
                    return None;
                }
                succs[0]
            } else {
                return None;
            };
            cur = next;
        }
        if visited.len() != body.len() {
            return None; // some body block is off the header->latch chain
        }
        bound
    }
}

/// Vectorize a [`BitChainRecognized`] forward-chain K-way bitwise reduction.
/// Purely ADDITIVE: splices a vector main loop between the preheader and the
/// header and never edits the scalar chain, so the scalar loop finishes the
/// `< width` tail unchanged.
fn apply_chain(func: &mut MachFunction, rec: &BitChainRecognized) -> bool {
    // IDEMPOTENCE: never vectorize the remainder loop of a loop this pass
    // already vectorized (see `crate::vector_remainder`).
    if rec.reductions.iter().any(|r| {
        crate::vector_remainder::preheader_folds_neon_lane_into(func, rec.preheader, r.acc)
    }) {
        return false;
    }
    crate::candidate::commit(func, |candidate| apply_chain_candidate(candidate, rec))
}

fn apply_chain_candidate(func: &mut MachFunction, rec: &BitChainRecognized) -> Option<()> {
    let (vf, elem_bytes, elem_code, const_class) = if rec.is_i64 {
        (VF_I64, ELEM_BYTES_I64, ELEM_D, RegClass::Gpr64)
    } else {
        (VF, ELEM_BYTES, ELEM_S, RegClass::Gpr32)
    };
    let width = UNROLL as i64 * vf; // 16 (i32) or 8 (i64)

    let vh = func.try_create_block()?;
    let vb = func.try_create_block()?;
    let vl = func.try_create_block()?;
    let vx = func.try_create_block()?;
    insert_new_blocks_before(func, rec.guard, &[vh, vb, vl, vx])?;
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: per-reduction UNROLL accumulators seeded with the per-lane
    // reduction IDENTITY (all-ones for AND, zero for OR/XOR) via `MOVI .16B`.
    let vacc: Vec<Vec<VReg>> = rec
        .reductions
        .iter()
        .map(|red| {
            (0..UNROLL)
                .map(|_| {
                    let a = alloc(func, RegClass::Fpr128)?;
                    emit_before(
                        func,
                        pre,
                        AArch64Opcode::NeonMovi,
                        vec![vreg(a), imm(red.op.identity_movi())],
                    )?;
                    Some(a)
                })
                .collect::<Option<Vec<_>>>()
        })
        .collect::<Option<Vec<_>>>()?;

    // --- Guard bound. The scalar loop-continue is `iv <u N` (UNSIGNED `LO`), so
    // the vector guard is UNSIGNED too. `N` is a compile-time constant in
    // `[1, i32::MAX]`, so the guard limit `main = N - (width-1)` (the largest
    // `iv` whose full `width`-block fits in `[0, N)`) is computed at COMPILE time;
    // when `N < width` no full block fits and we use `0` so `iv <u 0` never
    // passes (the scalar loop does everything). `iv` is `Gpr64`, matching the
    // scalar's 64-bit `CmpRI(iv, N)` bit-for-bit.
    let main_bound_k = if rec.bound >= width {
        rec.bound - (width - 1)
    } else {
        0
    };
    let main_bound = materialize_const(func, pre, main_bound_k, RegClass::Gpr64)?;

    // --- Preheader: element-size const + one running pointer per candidate base
    // (`p = base + iv0*elem`, the `Gpr64` induction used directly — the exact
    // mixed i64-index / element-width addressing the scalar loop performs).
    let c_es = alloc(func, RegClass::Gpr64)?;
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(elem_bytes)],
    )?;
    let ptrs: Vec<VReg> = rec
        .bases
        .iter()
        .map(|base| {
            let p = alloc(func, RegClass::Gpr64)?;
            emit_before(
                func,
                pre,
                AArch64Opcode::Madd,
                vec![vreg(p), vreg(rec.iv), vreg(c_es), vreg(*base)],
            )?;
            Some(p)
        })
        .collect::<Option<Vec<_>>>()?;

    // --- Vector header: UNSIGNED guard `iv <u main_bound` (== `iv+width-1 <u N`),
    // matching the scalar's `iv <u N` loop-continue in the same 64-bit width.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    )?;
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)])?;
    emit(func, vh, AArch64Opcode::B, vec![block(vx)])?;

    // --- Vector body: paired post-index LDP per base (32 bytes = 2 Q-regs each),
    // then per accumulator per reduction `vacc = OP(vacc, loaded)`. The load is
    // issued ONCE per base and fed to every reduction over that base.
    let mut loaded: HashMap<(u32, usize), VReg> = HashMap::default();
    for (base, p) in rec.bases.iter().zip(&ptrs) {
        for pair in 0..UNROLL / 2 {
            let q0 = alloc(func, RegClass::Fpr128)?;
            let q1 = alloc(func, RegClass::Fpr128)?;
            emit(
                func,
                vb,
                AArch64Opcode::NeonLdpQPost,
                vec![vreg(q0), vreg(q1), vreg(*p), imm(32)],
            )?;
            loaded.insert((base.id, 2 * pair), q0);
            loaded.insert((base.id, 2 * pair + 1), q1);
        }
    }
    for k in 0..UNROLL {
        for (ri, red) in rec.reductions.iter().enumerate() {
            let &vterm = loaded.get(&(red.base.id, k))?;
            let acc = *vacc.get(ri)?.get(k)?;
            let (vop, vops) = red.op.vec_op_operands(acc, acc, vterm, rec.is_i64);
            emit(func, vb, vop, vops)?;
        }
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)])?;

    // --- Vector latch: advance iv by width.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    )?;
    emit(func, vl, AArch64Opcode::B, vec![block(vh)])?;

    // --- Vector exit: for each reduction combine its accumulators (balanced tree,
    // same OP), horizontally reduce (UMOV each lane + scalar OP), and fold into
    // the scalar accumulator (still holding its pre-loop value M0 — the vector
    // loop never wrote it; the scalar tail continues from here).
    for (ri, red) in rec.reductions.iter().enumerate() {
        let mut level = vacc[ri].clone();
        while level.len() > 1 {
            let mut next = Vec::new();
            let mut i = 0;
            while i + 1 < level.len() {
                let d = alloc(func, RegClass::Fpr128)?;
                let (vop, vops) = red
                    .op
                    .vec_op_operands(d, level[i], level[i + 1], rec.is_i64);
                emit(func, vx, vop, vops)?;
                next.push(d);
                i += 2;
            }
            if i < level.len() {
                next.push(level[i]);
            }
            level = next;
        }
        let vsum = level[0];
        let lane_regs: Vec<VReg> = (0..vf)
            .map(|lane| {
                let w = alloc(func, const_class)?;
                emit(
                    func,
                    vx,
                    AArch64Opcode::NeonUmovGen,
                    vec![vreg(w), vreg(vsum), imm(lane), imm(elem_code)],
                )?;
                Some(w)
            })
            .collect::<Option<Vec<_>>>()?;
        // Fold the extracted lanes into `acc` (= M0), overwriting it with
        // `OP(M0, lane0, lane1, ...)` — a left fold with the scalar bitwise op.
        let mut running = red.acc;
        for (i, &w) in lane_regs.iter().enumerate() {
            let last = i + 1 == lane_regs.len();
            let dst = if last {
                red.acc
            } else {
                alloc(func, const_class)?
            };
            emit(
                func,
                vx,
                red.op.scalar_op(),
                vec![vreg(dst), vreg(running), vreg(w)],
            )?;
            running = dst;
        }
    }
    // The drain continues into the scalar tail, or straight to the loop exit
    // when the tail provably runs no iteration.
    let after_drain = rec.dead_tail_exit.unwrap_or(rec.guard);
    emit(func, vx, AArch64Opcode::B, vec![block(after_drain)])?;

    // Splice the private candidate; publication happens only after success.
    crate::candidate::splice_edge(func, rec.preheader, rec.preheader_term, rec.guard, vh)?;
    func.add_edge(vx, after_drain);
    Some(())
}

/// The exit of a chain loop whose scalar tail the vector loop leaves with no
/// iteration, or `None`.
///
/// The vector loop runs while `iv + width <= N` from the induction's entry
/// value `iv0`, stepping by `width`. When `iv0` is one known constant on every
/// path into the loop, with `0 <= iv0 <= N` and `N - iv0` a multiple of
/// `width`, it exits with `iv == N` exactly, so the scalar header's continue
/// test `iv <u N` fails on its first evaluation and the loop exits. The drain
/// may then branch to that exit directly, provided taking the header's exit
/// edge does nothing else: the header is exactly `cmp; b.lo body; b exit`,
/// possibly reading the induction through copies no other block reads (the
/// compare only writes flags), and NZCV is dead on entry to the exit. The
/// scalar loop, now entered from nowhere, is unreachable, and no later pass
/// vectorizes it again (measured on `b1_mispredict`: a 16-element `u64` sum
/// kept a second vector loop and a scalar remainder, 45 instructions that
/// never execute).
#[allow(clippy::too_many_arguments)]
fn dead_tail_exit(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    header: BlockId,
    preheader: BlockId,
    body: &HashSet<BlockId>,
    iv: VReg,
    bound: i64,
    width: i64,
) -> Option<BlockId> {
    // The header: exactly the continue test, optionally reading the induction
    // through header-private copies of it (`t = iv; cmp t, N`) that nothing
    // outside the header reads.
    let header_insts = &func.block(header).insts;
    let [copies @ .., cmp, bcond, br] = header_insts.as_slice() else {
        return None;
    };
    let mut iv_views = vec![iv];
    for &id in copies {
        let (dst, src) = copy_like(func.inst(id))?;
        if !iv_views.contains(&src) || dst == iv {
            return None;
        }
        let read_outside = func.block_order.iter().any(|block_id| {
            *block_id != header
                && func.block(*block_id).insts.iter().any(|&other| {
                    func.inst(other)
                        .operands
                        .iter()
                        .any(|op| op.as_vreg() == Some(dst))
                })
        });
        if read_outside {
            return None;
        }
        iv_views.push(dst);
    }
    let (cmp, bcond, br) = (func.inst(*cmp), func.inst(*bcond), func.inst(*br));
    if !matches!(cmp.opcode, AArch64Opcode::CmpRI | AArch64Opcode::CmpRR)
        || !cmp
            .operands
            .first()
            .and_then(MachOperand::as_vreg)
            .is_some_and(|v| iv_views.contains(&v))
        || bcond.opcode != AArch64Opcode::BCond
        || bcond.operands.first().and_then(MachOperand::as_imm) != Some(CC_LO)
        || br.opcode != AArch64Opcode::B
    {
        return None;
    }
    let exit = *branch_targets(br).first()?;
    if body.contains(&exit) {
        return None;
    }
    // No path from the exit reads a flag the skipped compare would have set
    // (conditional branches included, and through the exit's successors: a
    // later block may reuse a predecessor's live-out NZCV).
    if !crate::effects::nzcv_dead_at_block_entry(func, exit) {
        return None;
    }
    // The induction's entry value: its only definition outside the loop, a
    // constant, in a block that dominates the preheader.
    let mut outside = Vec::new();
    for block_id in &func.block_order {
        if body.contains(block_id) {
            continue;
        }
        for &id in &func.block(*block_id).insts {
            let mut defines = false;
            crate::effects::for_each_inst_def(func.inst(id), |v| defines |= v == iv);
            if defines {
                outside.push((*block_id, id));
            }
        }
    }
    let [(def_block, def_id)] = outside.as_slice() else {
        return None;
    };
    if !dom.dominates(*def_block, preheader) {
        return None;
    }
    let init = func.inst(*def_id);
    let iv0 = match init.opcode {
        AArch64Opcode::Movz if init.operands.len() == 2 => init.operands[1].as_imm()?,
        _ => {
            let (_, src) = copy_like(init)?;
            // `strip_copies` stops at a register with several live defs, which
            // has no single entry value; `const_value` refuses it.
            const_value(func, def, strip_copies(func, def, src))?
        }
    };
    ((0..=bound).contains(&iv0) && iv0 % width == 0 && (bound - iv0) % width == 0).then_some(exit)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::MachInst;
    use trust_cg_ir::Signature;

    fn candidate_plan(func: &MachFunction) -> Plan {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        loops
            .all_loops()
            .find_map(|lp| {
                Recognized::recognize(func, &dom, lp.header, lp.latch, &lp.body)
                    .map(Plan::Strict)
                    .or_else(|| {
                        BitChainRecognized::recognize(func, &dom, lp.header, lp.latch, &lp.body)
                            .map(Plan::Chain)
                    })
            })
            .expect("unmodified fixture must be recognized")
    }

    fn apply_candidate_plan(func: &mut MachFunction, plan: &Plan) -> bool {
        match plan {
            Plan::Strict(rec) => apply(func, rec),
            Plan::Chain(rec) => apply_chain(func, rec),
        }
    }

    fn candidate_fixture(chain: bool) -> MachFunction {
        if chain {
            build_chain_loop(false)
        } else {
            build_loop(1)
        }
    }

    fn assert_candidate_refusal(chain: bool, corruption: usize) {
        let mut func = candidate_fixture(chain);
        let plan = candidate_plan(&func);
        let (pre, guard) = match &plan {
            Plan::Strict(rec) => (rec.preheader_term, rec.guard),
            Plan::Chain(rec) => (rec.preheader_term, rec.guard),
        };
        // Private-plan corruption after recognition exercises publication
        // atomicity; it is not a claim that a frontend emits these stale plans.
        match corruption {
            0 => func.next_vreg = u32::MAX,
            1 => func.next_vreg = u32::MAX - 4,
            2 => func.noalias_params.push(u32::MAX),
            3 => func.inst_mut(pre).operands.clear(),
            4 => {
                for block in &mut func.blocks {
                    block.insts.retain(|id| *id != pre);
                }
            }
            5 => func.block_order.retain(|id| *id != guard),
            _ => unreachable!(),
        }
        let before = format!("{func:?}");
        assert!(
            !apply_candidate_plan(&mut func, &plan),
            "corruption={corruption}"
        );
        assert_eq!(
            format!("{func:?}"),
            before,
            "refusal must preserve the entire function"
        );
    }

    macro_rules! candidate_refusal_test {
        ($name:ident, $chain:expr, $corruption:expr) => {
            #[test]
            fn $name() {
                assert_candidate_refusal($chain, $corruption);
            }
        };
    }
    candidate_refusal_test!(candidate_strict_early_exhaustion, false, 0);
    candidate_refusal_test!(candidate_strict_late_exhaustion, false, 1);
    candidate_refusal_test!(candidate_strict_metadata_exhaustion, false, 2);
    candidate_refusal_test!(candidate_strict_splice_refusal, false, 3);
    candidate_refusal_test!(candidate_strict_missing_setup, false, 4);
    candidate_refusal_test!(candidate_strict_missing_layout, false, 5);
    candidate_refusal_test!(candidate_chain_early_exhaustion, true, 0);
    candidate_refusal_test!(candidate_chain_late_exhaustion, true, 1);
    candidate_refusal_test!(candidate_chain_metadata_exhaustion, true, 2);
    candidate_refusal_test!(candidate_chain_splice_refusal, true, 3);
    candidate_refusal_test!(candidate_chain_missing_setup, true, 4);
    candidate_refusal_test!(candidate_chain_missing_layout, true, 5);

    fn candidate_variants() -> Vec<(&'static str, MachFunction)> {
        let mut shared = build_loop(1);
        for inst in &mut shared.insts {
            if inst.opcode == AArch64Opcode::MulRR {
                inst.operands[2] = v(10);
            }
        }
        let mut wide = build_chain_loop(false);
        for inst in &mut wide.insts {
            if inst.opcode == AArch64Opcode::Movz && inst.operands[0] == v64(1) {
                inst.operands[1] = i(8);
            }
            for op in &mut inst.operands {
                if let MachOperand::VReg(v) = op {
                    v.class = RegClass::Gpr64;
                }
            }
        }
        vec![
            ("strict", build_loop(1)),
            ("shared-multiply", shared),
            ("chain-i32", build_chain_loop(false)),
            ("chain-i64", wide),
        ]
    }

    #[test]
    fn candidate_success_snapshots() {
        for (label, mut func) in candidate_variants() {
            let plan = candidate_plan(&func);
            assert!(apply_candidate_plan(&mut func, &plan), "{label}");
            println!("REDUCTION_CANDIDATE_SNAPSHOT {label}: {func:?}");
        }
    }

    #[test]
    fn candidate_public_routes_refuse_without_mutation() {
        for (label, fixture) in candidate_variants() {
            for analyses_route in [false, true] {
                let mut positive = fixture.clone();
                let mut pass = NeonReducePass::new();
                assert!(
                    if analyses_route {
                        pass.run_with_analyses(&mut positive, &mut AnalysisCache::new())
                    } else {
                        pass.run(&mut positive)
                    },
                    "positive {label}"
                );
                assert_eq!(pass.fired(), 1);
                for noalias in [false, true] {
                    let mut func = fixture.clone();
                    if noalias {
                        func.noalias_params.push(u32::MAX);
                    } else {
                        func.next_vreg = u32::MAX;
                    }
                    let before = format!("{func:?}");
                    assert!(
                        !if analyses_route {
                            pass.run_with_analyses(&mut func, &mut AnalysisCache::new())
                        } else {
                            pass.run(&mut func)
                        },
                        "{label}"
                    );
                    assert_eq!(pass.fired(), 0);
                    assert_eq!(format!("{func:?}"), before, "{label}");
                }
            }
        }
    }

    #[test]
    fn candidate_sparse_detached_and_metadata_ids_remain_fresh() {
        for (label, mut func) in candidate_variants() {
            func.push_inst(MachInst::new(
                AArch64Opcode::Movz,
                vec![
                    MachOperand::VReg(VReg::new(1_000_000_000, RegClass::Gpr64)),
                    imm(0),
                ],
            ));
            func.noalias_params.push(1_000_000_007);
            func.next_vreg = 0;
            let first_new = func.insts.len();
            assert!(NeonReducePass::new().run(&mut func), "{label}");
            assert!(func.next_vreg > 1_000_000_007);
            for inst in &func.insts[first_new..] {
                for v in inst.operands.iter().filter_map(MachOperand::as_vreg) {
                    assert!(v.id < 64 || v.id > 1_000_000_007, "{label}: {v:?}");
                }
            }
        }
    }

    #[test]
    fn candidate_every_register_reservation_refuses_atomically() {
        for (label, fixture) in candidate_variants() {
            let mut ordinary = fixture.clone();
            assert!(NeonReducePass::new().run(&mut ordinary), "positive {label}");
            let count = ordinary.next_vreg - fixture.next_vreg;
            assert!(count > 4, "fixture must exercise late allocation");
            for available in 0..count {
                let mut func = fixture.clone();
                func.next_vreg = u32::MAX - available;
                let before = format!("{func:?}");
                let mut pass = NeonReducePass::new();
                assert!(!pass.run(&mut func), "{label}: available={available}");
                assert_eq!(pass.fired(), 0);
                assert_eq!(
                    format!("{func:?}"),
                    before,
                    "{label}: available={available}"
                );
            }
        }
    }

    #[test]
    fn candidate_final_representable_range_preserves_normalized_output() {
        for (label, fixture) in candidate_variants() {
            let mut ordinary = fixture.clone();
            assert!(NeonReducePass::new().run(&mut ordinary));
            let count = ordinary.next_vreg - fixture.next_vreg;
            let first = u32::MAX - count;
            let mut boundary = fixture.clone();
            boundary.next_vreg = first;
            assert!(NeonReducePass::new().run(&mut boundary), "{label}");
            assert_eq!(boundary.next_vreg, u32::MAX);
            for inst in &mut boundary.insts {
                for operand in &mut inst.operands {
                    if let MachOperand::VReg(v) = operand
                        && v.id >= first
                    {
                        v.id = fixture.next_vreg + (v.id - first);
                    }
                }
            }
            boundary.next_vreg = ordinary.next_vreg;
            assert_eq!(format!("{boundary:?}"), format!("{ordinary:?}"), "{label}");
        }
    }

    #[test]
    fn candidate_lowering_refusal_preserves_live_function() {
        for chain in [false, true] {
            let mut func = candidate_fixture(chain);
            let mut plan = candidate_plan(&func);
            match &mut plan {
                Plan::Strict(rec) => rec.term = Term::Value(VReg::new(123456, RegClass::Gpr32)),
                Plan::Chain(rec) => rec.reductions[0].base = VReg::new(123456, RegClass::Gpr64),
            }
            let before = format!("{func:?}");
            assert!(!apply_candidate_plan(&mut func, &plan));
            assert_eq!(format!("{func:?}"), before);
        }
    }

    #[test]
    fn candidate_duplicate_setup_ownership_is_refused() {
        for chain in [false, true] {
            let mut func = candidate_fixture(chain);
            let plan = candidate_plan(&func);
            let pre = match &plan {
                Plan::Strict(rec) => rec.preheader_term,
                Plan::Chain(rec) => rec.preheader_term,
            };
            func.block_mut(func.entry).insts.push(pre);
            let before = format!("{func:?}");
            assert!(!apply_candidate_plan(&mut func, &plan));
            assert_eq!(format!("{func:?}"), before);
        }
    }

    /// LANE-WIDTH GUARD. `Add` MUST carry an arrangement immediate; the bitwise
    /// ops must NOT.
    ///
    /// This is the whole hazard of admitting ADD into a plan that was built
    /// lane-width agnostic. `neon_arrangement` in the encoder reads the LAST
    /// operand and falls back to `S4` for anything it does not recognize, so an
    /// `Add` emitted with only three operands does not fail — it silently
    /// becomes four 32-bit adds. For a 64-bit `wrapping_add` reduction that is a
    /// wrong VALUE, and the corpus checksums would still look plausible.
    #[test]
    fn add_carries_an_arrangement_and_bitwise_does_not() {
        let d = VReg::new(1, RegClass::Fpr128);
        let a = VReg::new(2, RegClass::Fpr128);
        let b = VReg::new(3, RegClass::Fpr128);

        for (is_i64, want) in [(true, ARRANGEMENT_D2), (false, ARRANGEMENT_S4)] {
            let (op, ops) = ReduceOp::Add.vec_op_operands(d, a, b, is_i64);
            assert_eq!(op, AArch64Opcode::NeonAddV);
            assert_eq!(
                ops.len(),
                4,
                "Add must append an arrangement; 3 operands silently decodes as S4"
            );
            assert_eq!(
                ops[3],
                MachOperand::Imm(want),
                "is_i64={is_i64}: wrong arrangement is a silent wrong-value miscompile"
            );
        }

        // The bitwise members stay on the arrangement-free .16B forms.
        for op in [ReduceOp::And, ReduceOp::Or, ReduceOp::Xor] {
            for is_i64 in [true, false] {
                let (_, ops) = op.vec_op_operands(d, a, b, is_i64);
                assert_eq!(ops.len(), 3, "bitwise ops are lane-width agnostic");
            }
        }
    }

    /// Zero is the identity for ADD at every lane width, and the byte-replicated
    /// MOVI stays valid. Pinned because this is the one place `Add` needs no
    /// width threading — which is exactly what makes the omission in
    /// `vec_op_operands` easy to miss.
    #[test]
    fn add_identity_is_zero_and_scalar_fold_is_add() {
        assert_eq!(ReduceOp::Add.identity_movi(), 0);
        assert_eq!(ReduceOp::Add.scalar_op(), AArch64Opcode::AddRR);
        assert_eq!(
            ReduceOp::from_opcode(AArch64Opcode::AddRR),
            Some(ReduceOp::Add)
        );
    }

    fn v(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }
    fn i(x: i64) -> MachOperand {
        MachOperand::Imm(x)
    }
    fn b(x: BlockId) -> MachOperand {
        MachOperand::Block(x)
    }
    fn count(func: &MachFunction, op: AArch64Opcode) -> usize {
        func.blocks
            .iter()
            .flat_map(|blk| blk.insts.iter().copied())
            .filter(|&id| func.inst(id).opcode == op)
            .count()
    }

    /// Build the recognized rotated reduction loop:
    ///   for iv in 0..bound: acc += TERM(iv)
    /// header holds TERM + reduction + step; latch holds the writebacks +
    /// `CmpRR(iv,bound)` + `BCond(LT)->header`. `step_imm` controls the induction
    /// stride (2 makes it un-recognizable) and `mul_term` toggles `iv*iv` vs a
    /// bare `iv` term.
    fn build_loop(step_reg_val: i64) -> MachFunction {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block(); // guard
        let bb2 = func.create_block(); // header
        let bb3 = func.create_block(); // latch
        let bb4 = func.create_block(); // exit

        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        // Preheader.
        push(&mut func, bb0, Movz, vec![v(0), i(100)]); // bound
        push(&mut func, bb0, Movz, vec![v(1), i(0)]); // zero
        push(&mut func, bb0, Movz, vec![v(10), i(step_reg_val)]); // step const
        push(&mut func, bb0, MovR, vec![v(3), v(1)]); // iv = 0
        push(&mut func, bb0, MovR, vec![v(4), v(1)]); // acc = 0
        push(&mut func, bb0, B, vec![b(bb1)]);
        // Guard.
        push(&mut func, bb1, CmpRR, vec![v(3), v(0)]);
        push(&mut func, bb1, BCond, vec![i(CC_LT), b(bb2)]);
        push(&mut func, bb1, B, vec![b(bb4)]);
        // Header: term = iv*iv; acc' = acc + term; iv' = iv + step.
        push(&mut func, bb2, MulRR, vec![v(5), v(3), v(3)]);
        push(&mut func, bb2, AddRR, vec![v(6), v(4), v(5)]);
        push(&mut func, bb2, AddRR, vec![v(7), v(3), v(10)]);
        push(&mut func, bb2, B, vec![b(bb3)]);
        // Latch: writebacks + compare + branch.
        push(&mut func, bb3, AddRI, vec![v(4), v(6), i(0)]);
        push(&mut func, bb3, AddRI, vec![v(3), v(7), i(0)]);
        push(&mut func, bb3, CmpRR, vec![v(3), v(0)]);
        push(&mut func, bb3, BCond, vec![i(CC_LT), b(bb2)]);
        // Exit.
        push(&mut func, bb4, MovR, vec![v(20), v(4)]);
        push(&mut func, bb4, Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb4);
        func.add_edge(bb2, bb3);
        func.add_edge(bb3, bb2);
        func.add_edge(bb3, bb4);
        func.next_vreg = 64;
        func
    }

    /// WRONG-CODE REGRESSION (2026-08-18): the STRICT drain must FOLD the
    /// vector partial sum into the scalar accumulator, never overwrite it.
    ///
    /// It used to emit `MovR acc, ssum`, dropping the accumulator's pre-loop
    /// value — so a reduction seeded with a non-zero value computed
    /// `sum(TERM)` instead of `seed + sum(TERM)`, wrong by exactly the seed at
    /// every trip count (including zero, since the drain block is on the only
    /// edge out of the vector loop). Recognition never required `acc == 0`.
    ///
    /// Pin it structurally: after the pass fires, the accumulator must be READ
    /// by the drain, not merely written. A `MovR acc, ssum` reads `acc` zero
    /// times; the correct `AddRR acc, acc, ssum` reads it once.
    #[test]
    fn strict_drain_folds_into_accumulator_never_overwrites() {
        let mut func = build_loop(1);
        let mut pass = NeonReducePass::new();
        assert!(
            pass.run(&mut func),
            "pass should fire on the recognized shape"
        );

        // Scope the check to the DRAIN block — the one holding the four
        // NeonUmovGen lane extracts. Checking function-wide would be vacuous:
        // the untouched scalar loop's own `AddRR acc, acc, term` would satisfy
        // any "some fold exists" assertion even with the bug present.
        let drain = func
            .blocks
            .iter()
            .find(|b| {
                b.insts
                    .iter()
                    .filter(|&&id| func.inst(id).opcode == AArch64Opcode::NeonUmovGen)
                    .count()
                    == 4
            })
            .expect("drain block with 4 lane extracts");

        // The last writer of the accumulator in the drain must READ it (fold).
        // `MovR acc, ssum` reads it zero times — that is the bug.
        let mut last_acc_writer: Option<(AArch64Opcode, bool)> = None;
        let mut acc_id: Option<u32> = None;
        for &id in &drain.insts {
            let inst = func.inst(id);
            let Some(MachOperand::VReg(dst)) = inst.operands.first() else {
                continue;
            };
            if !matches!(inst.opcode, AArch64Opcode::MovR | AArch64Opcode::AddRR) {
                continue;
            }
            let reads_own_dst = inst
                .operands
                .iter()
                .skip(1)
                .any(|o| matches!(o, MachOperand::VReg(v) if v.id == dst.id));
            // The accumulator is the only vreg the drain writes that is ALSO
            // live into the scalar loop, i.e. written elsewhere in the function.
            let written_elsewhere = func.blocks.iter().any(|b| {
                !std::ptr::eq(b.insts.as_slice(), drain.insts.as_slice())
                    && b.insts.iter().any(|&oid| {
                        matches!(func.inst(oid).operands.first(),
                                 Some(MachOperand::VReg(v)) if v.id == dst.id)
                    })
            });
            if written_elsewhere {
                acc_id = Some(dst.id);
                last_acc_writer = Some((inst.opcode, reads_own_dst));
            }
        }

        let (opcode, reads_own_dst) =
            last_acc_writer.expect("drain must write the loop-carried accumulator");
        assert!(
            reads_own_dst,
            "drain writes accumulator v{} with {opcode:?} WITHOUT reading it — that \
             overwrites the pre-loop value M0, so a seeded reduction loses its seed",
            acc_id.unwrap_or(0)
        );
        assert_eq!(
            opcode,
            AArch64Opcode::AddRR,
            "the STRICT recognizer admits only AddRR/Madd reductions, so the drain \
             fold must be an ADD"
        );
    }

    #[test]
    fn vectorizes_isq_reduction() {
        let mut func = build_loop(1); // +1 induction
        let mut pass = NeonReducePass::new();
        let changed = pass.run(&mut func);
        assert!(changed, "pass should fire on the recognized shape");
        assert_eq!(pass.fired(), 1);
        // NEON body: index build (DUP + 3 INS), i*i (MUL.4S), vacc += (ADD.4S),
        // horizontal reduce (4 UMOV).
        assert!(
            count(&func, AArch64Opcode::NeonMulV) >= 1,
            "expected MUL.4S"
        );
        assert!(
            count(&func, AArch64Opcode::NeonAddV) >= 1,
            "expected ADD.4S"
        );
        assert!(
            count(&func, AArch64Opcode::NeonDupGen) >= 2,
            "vi + vacc dup"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonInsGen), 3, "lanes 1..4");
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmovGen),
            4,
            "reduce 4 lanes"
        );
    }

    #[test]
    fn bails_on_non_unit_stride() {
        let mut func = build_loop(2); // +2 induction => not recognized
        let mut pass = NeonReducePass::new();
        let changed = pass.run(&mut func);
        assert!(!changed, "pass must BAIL on a non-+1 induction");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonMulV), 0, "no NEON emitted");
    }

    fn v64(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    /// Build the e03 forward-chain DUAL bitwise reduction shape:
    ///   bb0 (preheader: base/accs/iv init) -> bb1 (header: iv <u 2048 diamond)
    ///   -> bb2 (pass-through: sa &= a[iv]) -> bb3 (latch: so |= a[iv];
    ///   iv+1 writeback + K writebacks; B -> bb1) ; bb4 = exit.
    /// `store_in_loop` plants a StrRI in bb2 (must BAIL fail-closed).
    fn build_chain_loop(store_in_loop: bool) -> MachFunction {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry; // preheader
        let bb1 = func.create_block(); // header (guard diamond)
        let bb2 = func.create_block(); // pass-through (AND)
        let bb3 = func.create_block(); // latch (OR + writebacks)
        let bb4 = func.create_block(); // exit

        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        // Preheader: base ptr (v0), elem size (v1=4), iv (v2=0), sa (v3=!0),
        // so (v4=0).
        push(&mut func, bb0, AddPCRel, vec![v64(0), i(0)]);
        push(&mut func, bb0, Movz, vec![v64(1), i(4)]);
        push(&mut func, bb0, Movz, vec![v64(2), i(0)]);
        push(&mut func, bb0, Movn, vec![v(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v(4), i(0)]);
        push(&mut func, bb0, B, vec![b(bb1)]);
        // Header: guard diamond `iv <u 2048`.
        push(&mut func, bb1, CmpRI, vec![v64(2), i(2048)]);
        push(&mut func, bb1, BCond, vec![i(CC_LO), b(bb2)]);
        push(&mut func, bb1, B, vec![b(bb4)]);
        // Pass-through: sa' = sa & a[iv].
        push(&mut func, bb2, Madd, vec![v64(10), v64(2), v64(1), v64(0)]);
        push(&mut func, bb2, LdrRI, vec![v(11), v64(10), i(0)]);
        push(&mut func, bb2, AndRR, vec![v(12), v(3), v(11)]);
        if store_in_loop {
            push(&mut func, bb2, StrRI, vec![v(12), v64(10), i(0)]);
        }
        push(&mut func, bb2, B, vec![b(bb3)]);
        // Latch: so' = so | a[iv]; iv/sa/so writebacks; back-edge.
        push(&mut func, bb3, Madd, vec![v64(13), v64(2), v64(1), v64(0)]);
        push(&mut func, bb3, LdrRI, vec![v(14), v64(13), i(0)]);
        push(&mut func, bb3, OrrRR, vec![v(15), v(4), v(14)]);
        push(&mut func, bb3, AddRI, vec![v64(16), v64(2), i(1)]);
        push(&mut func, bb3, MovR, vec![v(3), v(12)]);
        push(&mut func, bb3, MovR, vec![v64(2), v64(16)]);
        push(&mut func, bb3, MovR, vec![v(4), v(15)]);
        push(&mut func, bb3, B, vec![b(bb1)]);
        // Exit.
        push(&mut func, bb4, Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb4);
        func.add_edge(bb2, bb3);
        func.add_edge(bb3, bb1);
        func.next_vreg = 64;
        func
    }

    #[test]
    fn vectorizes_dual_bitwise_chain() {
        let mut func = build_chain_loop(false);
        let mut pass = NeonReducePass::new();
        let changed = pass.run(&mut func);
        assert!(changed, "chain path should fire on the dual AND+OR shape");
        assert_eq!(pass.fired(), 1);
        // 2 reductions x 4 accumulators seeded with MOVI identities, one shared
        // LDP stream (UNROLL/2 = 2 pair loads), per-lane AND/ORR accumulate +
        // combine trees, and 4-lane UMOV horizontal folds per reduction.
        assert_eq!(
            count(&func, AArch64Opcode::NeonMovi),
            8,
            "2x4 identity seeds"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            2,
            "one shared stream"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonAndV),
            4 + 3,
            "4 accumulates + 3 combines (AND)"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonOrrV),
            4 + 3,
            "4 accumulates + 3 combines (OR)"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonUmovGen), 8, "2x4 lanes");
        // Scalar horizontal folds: 4 AndRR + 4 OrrRR beyond the loop's own 1+1.
        assert_eq!(count(&func, AArch64Opcode::AndRR), 1 + 4);
        assert_eq!(count(&func, AArch64Opcode::OrrRR), 1 + 4);
    }

    /// The block the vector drain (the horizontal UMOV fold) ends in, and the
    /// block its final branch continues to.
    fn drain_successor(func: &MachFunction) -> BlockId {
        let drain = func
            .block_order
            .iter()
            .copied()
            .find(|&b| {
                func.block(b)
                    .insts
                    .iter()
                    .any(|&id| func.inst(id).opcode == AArch64Opcode::NeonUmovGen)
            })
            .expect("drain block");
        let last = *func.block(drain).insts.last().unwrap();
        assert_eq!(func.inst(last).opcode, AArch64Opcode::B);
        branch_targets(func.inst(last))[0]
    }

    /// `for iv in 0..2048` over `i32` lanes (width 16): the vector loop exits
    /// with `iv == 2048`, so the scalar tail can never run. The drain goes to
    /// the loop exit, and the scalar loop is entered from nowhere.
    #[test]
    fn chain_drain_skips_a_provably_empty_scalar_tail() {
        let mut func = build_chain_loop(false);
        let (header, exit) = (BlockId(1), BlockId(4));
        assert!(NeonReducePass::new().run(&mut func));
        assert_eq!(drain_successor(&func), exit);
        let entry_preds: Vec<_> = func
            .block(header)
            .preds
            .iter()
            .copied()
            .filter(|p| *p != BlockId(3))
            .collect();
        assert!(
            entry_preds.is_empty(),
            "the scalar header is still entered from {entry_preds:?}"
        );

        // A nonzero entry value that is a multiple of the width still fits.
        let mut func = build_chain_loop(false);
        let init = func.block(func.entry).insts[2];
        func.inst_mut(init).operands[1] = MachOperand::Imm(32);
        assert!(NeonReducePass::new().run(&mut func));
        assert_eq!(drain_successor(&func), exit);

        // The entry value copied from a register whose only def is a constant.
        let mut func = build_chain_loop(false);
        let init = func.block(func.entry).insts[2];
        *func.inst_mut(init) = MachInst::new(AArch64Opcode::MovR, vec![v64(2), v64(50)]);
        let k = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![v64(50), i(32)]));
        func.block_mut(func.entry).insts.insert(0, k);
        assert!(NeonReducePass::new().run(&mut func));
        assert_eq!(drain_successor(&func), exit);
    }

    /// A register bound agrees with the loop's constant bound only when it
    /// holds that constant on every path: its one live def is the `Movz`.
    #[test]
    fn chain_bound_agrees_needs_one_def_of_a_register_bound() {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let early = func.create_block();
        let late = func.create_block();
        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        let (r, s) = (
            VReg::new(50, RegClass::Gpr64),
            VReg::new(51, RegClass::Gpr64),
        );
        push(&mut func, entry, Movz, vec![v64(51), i(2048)]);
        push(&mut func, entry, BCond, vec![i(CC_LO), b(early)]);
        push(&mut func, entry, B, vec![b(late)]);
        push(&mut func, early, Ret, vec![]);
        push(&mut func, late, Movz, vec![v64(50), i(2048)]);
        push(&mut func, late, Ret, vec![]);
        func.add_edge(entry, early);
        func.add_edge(entry, late);
        let agrees =
            |func: &MachFunction, a, b| chain_bound_agrees(func, &build_live_def_map(func), a, b);
        assert!(agrees(&func, ChainBound::Const(2048), ChainBound::Reg(r)));
        assert!(agrees(&func, ChainBound::Reg(s), ChainBound::Reg(r)));
        // `r` also written on the other path, before the layout-last `#2048`.
        let other = func.push_inst(MachInst::new(Movz, vec![v64(50), i(3)]));
        func.block_mut(early).insts.insert(0, other);
        assert!(!agrees(&func, ChainBound::Const(2048), ChainBound::Reg(r)));
        assert!(!agrees(&func, ChainBound::Reg(r), ChainBound::Const(2048)));
        assert!(!agrees(&func, ChainBound::Reg(s), ChainBound::Reg(r)));
    }

    /// Negative controls: the drain keeps continuing into the scalar tail, or
    /// the loop-state contract refuses the loop before a drain is planned (a
    /// header copy or NZCV live into the exit), so no tail is ever skipped.
    #[test]
    fn chain_drain_keeps_the_scalar_tail_unless_it_is_provably_empty() {
        let header = BlockId(1);
        // A bound that leaves a remainder.
        let mut func = build_chain_loop(false);
        let cmp = func.block(header).insts[0];
        func.inst_mut(cmp).operands[1] = MachOperand::Imm(2047);
        assert!(NeonReducePass::new().run(&mut func));
        assert_eq!(drain_successor(&func), header);
        // An entry value that is not a multiple of the width.
        let mut func = build_chain_loop(false);
        let init = func.block(func.entry).insts[2];
        func.inst_mut(init).operands[1] = MachOperand::Imm(3);
        assert!(NeonReducePass::new().run(&mut func));
        assert_eq!(drain_successor(&func), header);
        // An entry value copied from a register with two constant defs: the
        // copy reads `#3` (the preheader's def), while the last-wins def map
        // names the layout-later `#32` in the exit, which would fit the width.
        // A multi-def register has no single entry value, so the tail is kept.
        let mut func = build_chain_loop(false);
        let init = func.block(func.entry).insts[2];
        *func.inst_mut(init) = MachInst::new(AArch64Opcode::MovR, vec![v64(2), v64(50)]);
        let k = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![v64(50), i(3)]));
        func.block_mut(func.entry).insts.insert(0, k);
        let later = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![v64(50), i(32)]));
        func.block_mut(BlockId(4)).insts.insert(0, later);
        assert!(NeonReducePass::new().run(&mut func));
        assert_eq!(drain_successor(&func), header);
        // A header copy of the induction that the exit block still reads. The
        // loop-state contract refuses the whole loop before the drain is
        // planned: `v40` is written in the loop, live into the exit, and not
        // reproduced by the vector code.
        let mut func = build_chain_loop(false);
        let copy = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![v64(40), v64(2)]));
        func.block_mut(header).insts.insert(0, copy);
        let cmp = func.block(header).insts[1];
        func.inst_mut(cmp).operands[0] = v64(40);
        let read = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![v64(41), v64(40), i(1)],
        ));
        func.block_mut(BlockId(4)).insts.insert(0, read);
        assert!(!NeonReducePass::new().run(&mut func));
        // A header copy of the induction that a body block reads: the contract
        // admits the loop (the copy is redefined before every read and is not
        // live into an exit), and the drain still keeps the scalar tail.
        let mut func = build_chain_loop(false);
        let copy = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![v64(40), v64(2)]));
        func.block_mut(header).insts.insert(0, copy);
        let cmp = func.block(header).insts[1];
        func.inst_mut(cmp).operands[0] = v64(40);
        let read = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![v64(41), v64(40), i(1)],
        ));
        func.block_mut(BlockId(2)).insts.insert(0, read);
        assert!(NeonReducePass::new().run(&mut func));
        assert_eq!(drain_successor(&func), header);
        // The exit reads the header compare's flags (`cset`). NZCV is a
        // register to the loop-state contract: written in the loop, live into
        // the exit and not reproduced, so the contract refuses the loop.
        let mut func = build_chain_loop(false);
        let cset = func.push_inst(MachInst::new(AArch64Opcode::CSet, vec![v(42), i(CC_LO)]));
        func.block_mut(BlockId(4)).insts.insert(0, cset);
        assert!(!NeonReducePass::new().run(&mut func));
        // A successor of the exit reuses those flags (`b.lo`): NZCV is live
        // into the exit although the exit itself neither reads nor writes it,
        // and the contract refuses the loop for the same reason.
        let mut func = build_chain_loop(false);
        let exit = BlockId(4);
        let (next, far) = (func.create_block(), func.create_block());
        let ret = func.block_mut(exit).insts.pop().unwrap();
        let to_next = func.push_inst(MachInst::new(AArch64Opcode::B, vec![b(next)]));
        func.append_inst(exit, to_next);
        func.add_edge(exit, next);
        let bcond = func.push_inst(MachInst::new(AArch64Opcode::BCond, vec![i(CC_LO), b(far)]));
        func.append_inst(next, bcond);
        func.append_inst(next, ret);
        func.add_edge(next, far);
        let far_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(far, far_ret);
        assert!(!NeonReducePass::new().run(&mut func));
    }

    #[test]
    fn chain_bails_on_store_in_loop() {
        let mut func = build_chain_loop(true);
        let mut pass = NeonReducePass::new();
        let changed = pass.run(&mut func);
        assert!(!changed, "a store in the loop body must BAIL fail-closed");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonMovi), 0, "no NEON emitted");
    }

    /// IDEMPOTENCE (the neon-bytesum / neon-fill bug class of 2026-08-27: a
    /// vectorizer that keeps the scalar loop as the remainder and then
    /// recognizes that remainder again on the next fixpoint iteration). After
    /// the first firing, further runs must change nothing.
    #[test]
    fn second_run_is_a_no_op() {
        let mut func = build_loop(1);
        assert!(NeonReducePass::new().run(&mut func), "first run must fire");
        let (insts, blocks) = (func.insts.len(), func.blocks.len());
        for again in 2..=4 {
            assert!(
                !NeonReducePass::new().run(&mut func),
                "run {again}: re-fired on its own output"
            );
            assert_eq!(func.insts.len(), insts, "run {again} added instructions");
            assert_eq!(func.blocks.len(), blocks, "run {again} added blocks");
        }
    }

    /// IDEMPOTENCE over every firing shape the builders offer (the primary
    /// `second_run_is_a_no_op` covers one; today's bug class hid in shapes
    /// the primary test did not exercise).
    #[test]
    fn second_run_is_a_no_op_for_every_firing_variant() {
        type Build = Box<dyn Fn() -> MachFunction>;
        let cases: Vec<(&str, Build)> = vec![
            ("isq", Box::new(|| build_loop(1))),
            ("dual-bitwise-chain", Box::new(|| build_chain_loop(false))),
        ];
        for (label, build) in cases {
            let mut func = build();
            assert!(
                NeonReducePass::new().run(&mut func),
                "{label}: first run must fire"
            );
            let (insts, blocks) = (func.insts.len(), func.blocks.len());
            for again in 2..=4 {
                assert!(
                    !NeonReducePass::new().run(&mut func),
                    "{label}: run {again} re-fired on its own output"
                );
                assert_eq!(
                    func.insts.len(),
                    insts,
                    "{label}: run {again} added instructions"
                );
                assert_eq!(
                    func.blocks.len(),
                    blocks,
                    "{label}: run {again} added blocks"
                );
            }
        }
    }

    /// Loop-state contract (`crate::loop_contract`): both recognizers' vector
    /// loops reproduce only the induction and the accumulators, so a second
    /// carried register and a live-out-only register must each refuse, while
    /// the plain fixtures still fire.
    #[test]
    fn refuses_skipped_register_state() {
        type Build = fn() -> MachFunction;
        let shapes: [(&str, Build, VReg); 2] = [
            (
                "strict add",
                || build_loop(1),
                VReg::new(3, RegClass::Gpr32),
            ),
            (
                "bitwise chain",
                || build_chain_loop(false),
                VReg::new(2, RegClass::Gpr64),
            ),
        ];
        let mut wrong = Vec::new();
        for (name, build, iv) in shapes {
            assert!(
                NeonReducePass::new().run(&mut build()),
                "{name}: plain fires"
            );
            let mut carried = build();
            crate::loop_contract::test_support::add_second_accumulator(&mut carried, iv);
            if NeonReducePass::new().run(&mut carried) {
                wrong.push(format!("{name}: fired with a second accumulator"));
            }
            let mut live_out = build();
            crate::loop_contract::test_support::add_live_out(&mut live_out, iv);
            if NeonReducePass::new().run(&mut live_out) {
                wrong.push(format!("{name}: fired with a live-out-only register"));
            }
        }
        assert!(
            wrong.is_empty(),
            "skipped register state:\n  {}",
            wrong.join("\n  ")
        );
    }
}
