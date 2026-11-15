// trust-cg-opt - SOUND hoisted-range-guard crosswise-swap loop fast path (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # Hoisted-range-guard swap loop (`swap-range-guard`)
//!
//! Recognizes the innermost bounds-checked crosswise SWAP loop
//!
//! ```text
//! while x <u C {                      // C const
//!     i1 = y*S + x;  check i1 <u K;   // expanded bounds check -> abort
//!     t1 = base[i1];
//!     i2 = x*S + y;  check i2 <u K;
//!     t2 = base[i2];
//!     i1' = y*S + x; check i1' <u K;  // literal recomputations survive GVN
//!     base[i1'] = t2;
//!     i2' = x*S + y; check i2' <u K;
//!     base[i2'] = t1;
//!     x += 1;
//! }
//! ```
//!
//! (the matrix-transpose inner loop: `a[y*N+x] <-> a[x*N+y]` with per-access
//! `cmp idx,#K; b.lo; b -> abort` diamonds, 4 checks and 6 taken branches per
//! swap) and splices a GUARDED FAST PATH in front of the UNTOUCHED scalar
//! loop:
//!
//! * PREHEADER GUARDS (once per loop entry): `y <u K`, `m1 = y*S + (C-1) <u
//!   K`, `m2 = y + (C-1)*S <u K`, `x <u C`. Any failure -> the scalar loop,
//!   unchanged, with every original check.
//! * MAIN LOOP (single-block, bottom-tested): running pointers `p1 = base +
//!   (y*S+x)*es`, `p2 = base + (x*S+y)*es`;
//!   `w1=[p1]; w2=[p2]; [p1]=w2; [p2]=w1; p1+=es; p2+=S*es; x+=1;
//!   x <u C -> repeat` — no checks, no index recomputation, one taken branch.
//!   On exit `x == C`, so the scalar header runs ZERO iterations.
//!
//! ## Why this is SOUND
//!
//! TRACE EQUIVALENCE, aliasing-agnostic. On guard-pass the fast path issues
//! the IDENTICAL load/store sequence at the IDENTICAL addresses in the
//! IDENTICAL order with the IDENTICAL (crosswise) values as the scalar loop:
//! by induction `p1 == base + (y*S+x)*es` and `p2 == base + (x*S+y)*es` at
//! every iteration (the `+es` / `+S*es` bumps are exactly d(i1)/dx·es and
//! d(i2)/dx·es), and each iteration performs load(i1), load(i2), store(i1,
//! t2), store(i2, t1) — the scalar's exact per-iteration memory trace, so the
//! result is byte-identical under ANY aliasing (including i1 == i2).
//!
//! ELIDED CHECKS: both indices are STRICTLY MONOTONE INCREASING in `x`
//! (`i1(x) = y*S+x`, `i2(x) = x*S+y`, `S >= 1`), so over `x in [x0, C)` their
//! maxima are `m1 = y*S+(C-1)` and `m2 = (C-1)*S+y`. The guards prove `y <u
//! K` (so `y < 2^31` and, with the recognition caps `K <= i32::MAX`, `S*C <=
//! 2^31`, every index expression is wrap-free in 64-bit) and `m1,m2 <u K` —
//! therefore EVERY elided per-access check would have PASSED, and the scalar
//! loop would not have trapped on those iterations either. Guard-fail runs
//! the untouched scalar loop, traps preserved. No reordering of any memory
//! op => zero aliasing obligations.
//!
//! IV HANDOFF: entry requires `x <u C`; the bottom test re-checks `x <u C`,
//! so the fast path runs exactly `C - x0` iterations and exits with `x == C`
//! — precisely the scalar loop's own exit value.
//!
//! REGISTER STATE: the crate's one loop-state contract
//! ([`crate::loop_contract`]) admits the loop only when no register it writes
//! other than `x` is live into the header or an exit, so skipping the scalar
//! iterations cannot leave an observable stale register. Recognition also
//! requires every body vreg other than `x` to be single-def (for the
//! matchers).
//!
//! Every opcode emitted (`Movz`, `Movk`, `Madd`, `AddRR`, `AddRI`, `LdrRI`,
//! `StrRI`, `CmpRR`, `CmpRI`, `BCond`, `B`, `MovR`) is already
//! coverage-credited — no new emittable opcode, no new proof obligation.
//! (The design's post-index store form is deliberately NOT used: the scalar
//! writeback encoder is 64-bit only; explicit `AddRI` pointer bumps keep the
//! 32-bit `StrRI` transfer exact.)
//!
//! Default-ON at O2/Os/O3 (never O0/O1). Disable with
//! `TRUST_CG_DISABLE_PASSES=swap_range_guard`.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use crate::loop_contract::{ExitPlan, Handoff, LoopExit, LoopLocality, exit_of_test};
use crate::mach_util::{branch_targets, copied_const, copy_like, strip_copies};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// i32 element size in bytes (32-bit `LdrRI`/`StrRI` transfers only).
const ELEM_SIZE: i64 = 4;

/// AArch64 condition code for unsigned lower (`LO`).
const CC_LO: i64 = 3;
/// AArch64 condition code for signed less-than (`LT`).
const CC_LT: i64 = 11;
/// AArch64 condition code for unsigned higher-or-same (`HS`).
const CC_HS: i64 = 2;

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `swap-range-guard` machine pass.
#[derive(Default)]
pub struct SwapRangeGuardPass {
    fired: usize,
}

impl SwapRangeGuardPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }
    /// Loops rewritten in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for SwapRangeGuardPass {
    fn name(&self) -> &str {
        "swap-range-guard"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
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

impl SwapRangeGuardPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;
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
            if apply(func, &rec) {
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

/// One recognized index expression: `A`: `y*S + x` or `B`: `x*S + y`.
#[derive(Clone, Copy, Debug, PartialEq)]
enum IdxKind {
    A,
    B,
}

struct Recognized {
    header: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    /// The `Gpr64` induction `x` (`x += 1`).
    iv: VReg,
    /// The const trip bound `C` in `x <u C`.
    c_const: i64,
    /// The loop-invariant row register `y`.
    y: VReg,
    /// The const stride `S` (`i1 = y*S + x`, `i2 = x*S + y`).
    s_const: i64,
    /// Loop-invariant array base pointer.
    base: VReg,
    /// The shared bounds-check limit `K` (array length).
    k_const: i64,
    /// The loop-state contract (`crate::loop_contract`) passed for
    /// `[x]` (the induction). The plan cannot be built without it.
    _locality: LoopLocality,
}

impl Recognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        macro_rules! bail {
            ($($t:tt)*) => {{
                return None;
            }};
        }
        // The exact 6-block chain: header + 4 check/access blocks + latch.
        if body.len() != 6 || header == latch {
            bail!("body is not the 6-block swap chain (len={})", body.len());
        }
        let def = crate::effects::build_reaching_def_map(func);

        // Closed-world whitelist over the body.
        for &b in body {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    bail!("disallowed body op {:?}", func.inst(id).opcode);
                }
            }
        }
        let loop_insts: HashSet<InstId> = body
            .iter()
            .flat_map(|&b| func.block(b).insts.iter().copied())
            .collect();

        // Preheader: the single non-latch predecessor of the header.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            bail!("header preds != {{latch, preheader}}: {:?}", hpreds);
        }
        let preheader = *hpreds.iter().find(|&&b| b != latch)?;
        let Some(&preheader_term) = func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))
        else {
            bail!("no preheader->header branch");
        };

        // The `+1` Gpr64 induction, from the latch.
        let Some(iv) = find_induction(func, &def, latch) else {
            bail!("no +1 iv writeback in latch");
        };
        if iv.class != RegClass::Gpr64 {
            bail!("iv class not Gpr64");
        }

        // Def discipline (block-resident instructions only; see neon_iota_fill
        // for the ghost-instruction rationale): one definition per loop
        // register, for the matchers below. Whether a loop register is
        // observable after the fast path is the loop-state contract's
        // question, asked last.
        let live_ids: Vec<InstId> = func
            .block_order
            .iter()
            .flat_map(|&bid| func.block(bid).insts.iter().copied())
            .collect();
        let mut def_counts: HashMap<u32, usize> = HashMap::default();
        for &id in &live_ids {
            let inst = func.inst(id);
            crate::effects::for_each_inst_def(inst, |v| {
                *def_counts.entry(v.id).or_insert(0) += 1;
            });
        }
        let mut body_defs: HashSet<u32> = HashSet::default();
        for &id in &loop_insts {
            let inst = func.inst(id);
            crate::effects::for_each_inst_def(inst, |v| {
                body_defs.insert(v.id);
            });
        }
        for &vid in &body_defs {
            let n = def_counts.get(&vid).copied().unwrap_or(0);
            if vid == iv.id {
                let in_loop = live_ids
                    .iter()
                    .filter(|&&id| {
                        crate::effects::inst_defines_vreg(func.inst(id), iv)
                            && loop_insts.contains(&id)
                    })
                    .count();
                if n != 2 || in_loop != 1 {
                    bail!("iv def discipline violated");
                }
            } else if n != 1 {
                bail!("multi-def loop vreg v{}", vid);
            }
        }

        // --- Header: `x <u C` with a forward LT/LO branch into the chain and
        // one non-body exit successor.
        let (c_const, chain_head) =
            recognize_header(func, &def, header, body, iv).or_else(|| bail!("bad header test"))?;
        if !(2..=4095).contains(&c_const) {
            bail!("C {} out of range", c_const);
        }

        // --- Walk the 4-block check/access chain + latch, verifying the exact
        // grammar. Every non-latch chain block ends `CmpRI idx,#K; BCond LO ->
        // next; B -> abt` with ONE shared abort target.
        let mut blocks_seq = Vec::new();
        let mut cur = chain_head;
        for _ in 0..4 {
            blocks_seq.push(cur);
            let Some((next, _abt)) = chain_block_targets(func, cur, body) else {
                bail!("chain block {:?} lacks the check/abort terminator", cur);
            };
            cur = next;
        }
        if cur != latch {
            bail!("chain does not end at the latch");
        }
        blocks_seq.push(latch);
        // Latch terminator: unconditional back-edge only.
        {
            let succs = &func.block(latch).succs;
            if succs.len() != 1 || succs[0] != header {
                bail!("latch succs != [header]");
            }
        }
        // Abort targets: identical for all four checks, outside the body.
        let mut abt_seen: Option<BlockId> = None;
        for &b in &blocks_seq[..4] {
            let (_, abt) = chain_block_targets(func, b, body)?;
            if body.contains(&abt) {
                bail!("abort target inside the loop");
            }
            match abt_seen {
                None => abt_seen = Some(abt),
                Some(prev) if prev == abt => {}
                _ => bail!("differing abort targets"),
            }
        }

        // --- Flatten the chain (skipping pure copies) and match the exact
        // instruction grammar.
        let mut ops: Vec<InstId> = Vec::new();
        for &b in &blocks_seq {
            for &id in &func.block(b).insts {
                let inst = func.inst(id);
                match inst.opcode {
                    AArch64Opcode::MovR | AArch64Opcode::Copy => continue, // handled by reaches_reg
                    AArch64Opcode::B | AArch64Opcode::BCond => continue, // terminators checked above
                    _ => ops.push(id),
                }
            }
        }
        // Expected flat op sequence (16 non-copy ops):
        //  0: Madd i1      1: CmpRI i1,K
        //  2: Madd a1      3: Ldr w1        4: Madd i2     5: CmpRI i2,K
        //  6: Madd a2      7: Ldr w2        8: Madd i1'    9: CmpRI i1',K
        // 10: Madd a3     11: Str w2       12: Madd i2'   13: CmpRI i2',K
        // 14: Madd a4     15: Str w1       (+ latch AddRI, counted separately)
        // The latch's `AddRI x,1` (and its phi copy) are also in `ops`; strip
        // them from the tail.
        let mut tail = ops.clone();
        // Remove the induction AddRI (x+1) — it is the last non-copy op.
        let Some(&last) = tail.last() else {
            bail!("empty chain");
        };
        if !is_iv_add1(func, last, iv) {
            bail!("chain tail is not the iv writeback");
        }
        tail.pop();
        if tail.len() != 16 {
            bail!("chain op count {} != 16", tail.len());
        }

        // Index/check/access matching.
        let idx1 = match_idx_madd(func, &def, tail[0], iv)?;
        let k1 = match_check(func, tail[1], def_reg(func, tail[0])?)?;
        let a1 = match_addr_madd(func, &def, tail[2], def_reg(func, tail[0])?)?;
        let w1 = match_load(func, tail[3], def_reg(func, tail[2])?)?;
        let idx2 = match_idx_madd(func, &def, tail[4], iv)?;
        let k2 = match_check(func, tail[5], def_reg(func, tail[4])?)?;
        let a2 = match_addr_madd(func, &def, tail[6], def_reg(func, tail[4])?)?;
        let w2 = match_load(func, tail[7], def_reg(func, tail[6])?)?;
        let idx3 = match_idx_madd(func, &def, tail[8], iv)?;
        let k3 = match_check(func, tail[9], def_reg(func, tail[8])?)?;
        let a3 = match_addr_madd(func, &def, tail[10], def_reg(func, tail[8])?)?;
        let s1 = match_store(func, tail[11], def_reg(func, tail[10])?)?;
        let idx4 = match_idx_madd(func, &def, tail[12], iv)?;
        let k4 = match_check(func, tail[13], def_reg(func, tail[12])?)?;
        let a4 = match_addr_madd(func, &def, tail[14], def_reg(func, tail[12])?)?;
        let s2 = match_store(func, tail[15], def_reg(func, tail[14])?)?;

        // Shapes: i1/i1' are kind A (y*S+x), i2/i2' kind B (x*S+y); the two
        // recomputations must agree with the originals on (y, S).
        if idx1.kind != IdxKind::A
            || idx2.kind != IdxKind::B
            || idx3.kind != IdxKind::A
            || idx4.kind != IdxKind::B
        {
            bail!(
                "index kinds not (A,B,A,B): {:?}",
                (idx1.kind, idx2.kind, idx3.kind, idx4.kind)
            );
        }
        let y = idx1.y;
        let s_const = idx1.s;
        for other in [&idx2, &idx3, &idx4] {
            if strip_copies(func, &def, other.y) != strip_copies(func, &def, y)
                || other.s != s_const
            {
                bail!("index expressions disagree on (y, S)");
            }
        }
        // One shared K.
        let k_const = k1;
        if [k2, k3, k4].iter().any(|&k| k != k_const) {
            bail!("bounds-check limits disagree");
        }
        // One shared base; es == 4 on every access.
        let base = a1.base;
        for other in [&a2, &a3, &a4] {
            if strip_copies(func, &def, other.base) != strip_copies(func, &def, base)
                || other.es != ELEM_SIZE
            {
                bail!("access bases / element sizes disagree");
            }
        }
        if a1.es != ELEM_SIZE {
            bail!("element size != 4");
        }
        // CROSSWISE swap: first store writes the SECOND load's value, second
        // store the FIRST's. Transfers are Gpr32.
        if s1 != w2 || s2 != w1 {
            bail!("stores are not the crosswise swap of the loads");
        }
        if w1.class != RegClass::Gpr32 || w2.class != RegClass::Gpr32 {
            bail!("transfer registers not Gpr32");
        }

        // Invariance + range caps. `y`/`base` feed 64-bit guard/pointer
        // arithmetic in the fast path — pin their classes (fail-closed).
        let y = strip_copies(func, &def, y);
        if y.class != RegClass::Gpr64 {
            bail!("y class not Gpr64");
        }
        if !is_loop_invariant(func, &def, dom, &loop_insts, preheader, y) {
            bail!("y not loop-invariant");
        }
        let base = strip_copies(func, &def, base);
        if base.class != RegClass::Gpr64 {
            bail!("base class not Gpr64");
        }
        if !is_loop_invariant(func, &def, dom, &loop_insts, preheader, base) {
            bail!("base not loop-invariant");
        }
        if base == iv || y == iv {
            bail!("base/y aliases iv");
        }
        if !(1..=1 << 20).contains(&s_const) {
            bail!("S {} out of range", s_const);
        }
        if !(1..=i64::from(i32::MAX)).contains(&k_const) {
            bail!("K {} out of range", k_const);
        }
        if s_const * ELEM_SIZE > 4095 {
            bail!("S*es {} exceeds the AddRI bump range", s_const * ELEM_SIZE);
        }
        // Wrap-freedom cap for the hoisted maxima: (C-1)*S + K stays far below
        // 2^63 given the individual caps (C<=4095, S<=2^20, K<=2^31): maximum
        // ~2^32 + 2^31. Nothing further to check.

        // LOOP STATE (`crate::loop_contract`): the fast path runs only
        // iterations the header's `x <u C` test continues, and reproduces only
        // the induction `x`. The four chain checks' abort edges are the only
        // other exits, and the preheader guards prove every one of them passes
        // over `x in [x0, C)` (a pre-guard, so this pass claims them; see
        // "ELIDED CHECKS"). Any other exit refuses the loop.
        let Some(exit) = exit_of_test(func, body.iter().copied(), header) else {
            bail!("the header test has no single exit");
        };
        let mut exits = ExitPlan::loop_test(header, exit);
        for &b in &blocks_seq[..4] {
            let (_, abort) = chain_block_targets(func, b, body)?;
            exits = exits.and_proved_not_taken(LoopExit::Edge { from: b, to: abort });
        }
        let locality = match LoopLocality::check(
            func,
            body.iter().copied(),
            header,
            &exits,
            Handoff::HeaderOrExit,
            &[iv],
        ) {
            Ok(locality) => locality,
            Err(_escape) => bail!("loop state escapes: {:?}", _escape),
        };
        Some(Recognized {
            _locality: locality,
            header,
            preheader,
            preheader_term,
            iv,
            c_const,
            y,
            s_const,
            base,
            k_const,
        })
    }
}

/// The header must be: `[copies] CmpRI/CmpRR(iv, C) ; BCond LT/LO -> chain ;
/// B -> exit` with exactly one body successor and one non-body successor.
/// Returns `(C, chain_head)`.
fn recognize_header(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    header: BlockId,
    body: &HashSet<BlockId>,
    iv: VReg,
) -> Option<(i64, BlockId)> {
    let succs = &func.block(header).succs;
    if succs.len() != 2 {
        return None;
    }
    let inside = succs.iter().filter(|s| body.contains(s)).count();
    if inside != 1 {
        return None;
    }
    // Walk in order tracking the LAST flag-setter; the qualifying
    // `BCond LT/LO -> body` must consume the flags of the iv-vs-C compare
    // (a stray non-iv compare in between -> fail closed). The only
    // whitelisted flag-setters are CmpRR/CmpRI, so this tracking is complete.
    let mut last_cmp: Option<(VReg, Option<i64>)> = None;
    let mut c_const: Option<i64> = None;
    let mut taken: Option<BlockId> = None;
    for &id in &func.block(header).insts {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::MovR | AArch64Opcode::Copy => continue,
            AArch64Opcode::CmpRI if inst.operands.len() == 2 => {
                last_cmp = Some((inst.operands[0].as_vreg()?, inst.operands[1].as_imm()));
            }
            AArch64Opcode::CmpRR if inst.operands.len() == 2 => {
                last_cmp = Some((
                    inst.operands[0].as_vreg()?,
                    copied_const(func, def, inst.operands[1].as_vreg()?),
                ));
            }
            AArch64Opcode::BCond if inst.operands.len() == 2 => {
                let cc = inst.operands[0].as_imm()?;
                let tgt = *branch_targets(inst).first()?;
                if (cc == CC_LT || cc == CC_LO) && body.contains(&tgt) {
                    let (lhs, c) = last_cmp?;
                    if !reaches_reg(func, def, lhs, iv) {
                        return None;
                    }
                    c_const = c;
                    taken = Some(tgt);
                }
            }
            AArch64Opcode::B => {}
            _ => return None,
        }
    }
    Some((c_const?, taken?))
}

/// A chain block's terminator: `BCond LO -> next(in body) ; B -> abt(out)`.
fn chain_block_targets(
    func: &MachFunction,
    b: BlockId,
    body: &HashSet<BlockId>,
) -> Option<(BlockId, BlockId)> {
    let mut next: Option<BlockId> = None;
    let mut abt: Option<BlockId> = None;
    for &id in &func.block(b).insts {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::BCond if inst.operands.len() == 2 => {
                if inst.operands[0].as_imm()? != CC_LO {
                    return None;
                }
                let tgt = *branch_targets(inst).first()?;
                if !body.contains(&tgt) {
                    return None;
                }
                if next.is_some() {
                    return None;
                }
                next = Some(tgt);
            }
            AArch64Opcode::B => {
                let tgt = *branch_targets(inst).first()?;
                if abt.is_some() {
                    return None;
                }
                abt = Some(tgt);
            }
            _ => {}
        }
    }
    let succs = &func.block(b).succs;
    if succs.len() != 2 {
        return None;
    }
    Some((next?, abt?))
}

struct IdxMatch {
    kind: IdxKind,
    y: VReg,
    s: i64,
}

/// Match `Madd d, f1, f2, f3` as `A`: `y*S + x` or `B`: `x*S + y`.
fn match_idx_madd(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    id: InstId,
    iv: VReg,
) -> Option<IdxMatch> {
    let inst = func.inst(id);
    if inst.opcode != AArch64Opcode::Madd || inst.operands.len() != 4 {
        return None;
    }
    let f1 = inst.operands[1].as_vreg()?;
    let f2 = inst.operands[2].as_vreg()?;
    let f3 = inst.operands[3].as_vreg()?;
    let s_of = |v: VReg| copied_const(func, def, v);
    // A: (y * S) + x  — f3 reaches iv; one factor const S, the other is y.
    let a = if reaches_reg(func, def, f3, iv) {
        if let Some(s) = s_of(f2) {
            if !reaches_reg(func, def, f1, iv) {
                Some(IdxMatch {
                    kind: IdxKind::A,
                    y: f1,
                    s,
                })
            } else {
                None
            }
        } else if let Some(s) = s_of(f1) {
            if !reaches_reg(func, def, f2, iv) {
                Some(IdxMatch {
                    kind: IdxKind::A,
                    y: f2,
                    s,
                })
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };
    // B: (x * S) + y — one factor reaches iv, the other const S; f3 is y.
    let b = if !reaches_reg(func, def, f3, iv) {
        if reaches_reg(func, def, f1, iv) {
            s_of(f2).map(|s| IdxMatch {
                kind: IdxKind::B,
                y: f3,
                s,
            })
        } else if reaches_reg(func, def, f2, iv) {
            s_of(f1).map(|s| IdxMatch {
                kind: IdxKind::B,
                y: f3,
                s,
            })
        } else {
            None
        }
    } else {
        None
    };
    match (a, b) {
        (Some(m), None) | (None, Some(m)) => Some(m),
        _ => None, // ambiguous or neither: fail closed
    }
}

/// Match `CmpRI d,#K` where `d` is EXACTLY `want` (the just-computed index).
fn match_check(func: &MachFunction, id: InstId, want: VReg) -> Option<i64> {
    let inst = func.inst(id);
    if inst.opcode != AArch64Opcode::CmpRI || inst.operands.len() != 2 {
        return None;
    }
    if inst.operands[0].as_vreg()? != want {
        return None;
    }
    inst.operands[1].as_imm()
}

struct AddrMatch {
    base: VReg,
    es: i64,
}

/// Match `Madd d, idx, es, base` (either factor order) for EXACTLY `idx`.
fn match_addr_madd(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    id: InstId,
    idx: VReg,
) -> Option<AddrMatch> {
    let inst = func.inst(id);
    if inst.opcode != AArch64Opcode::Madd || inst.operands.len() != 4 {
        return None;
    }
    let f1 = inst.operands[1].as_vreg()?;
    let f2 = inst.operands[2].as_vreg()?;
    let base = inst.operands[3].as_vreg()?;
    if f1 == idx {
        Some(AddrMatch {
            base,
            es: copied_const(func, def, f2)?,
        })
    } else if f2 == idx {
        Some(AddrMatch {
            base,
            es: copied_const(func, def, f1)?,
        })
    } else {
        None
    }
}

/// Match `LdrRI w,[addr,#0]` for EXACTLY `addr`; returns the transfer reg.
fn match_load(func: &MachFunction, id: InstId, addr: VReg) -> Option<VReg> {
    let inst = func.inst(id);
    if inst.opcode != AArch64Opcode::LdrRI || inst.operands.len() != 3 {
        return None;
    }
    if inst.operands[1].as_vreg()? != addr || inst.operands[2].as_imm() != Some(0) {
        return None;
    }
    inst.operands[0].as_vreg()
}

/// Match `StrRI w,[addr,#0]` for EXACTLY `addr`; returns the stored reg.
fn match_store(func: &MachFunction, id: InstId, addr: VReg) -> Option<VReg> {
    let inst = func.inst(id);
    if inst.opcode != AArch64Opcode::StrRI || inst.operands.len() != 3 {
        return None;
    }
    if inst.operands[1].as_vreg()? != addr || inst.operands[2].as_imm() != Some(0) {
        return None;
    }
    inst.operands[0].as_vreg()
}

/// The def register of instruction `id` (operand 0).
fn def_reg(func: &MachFunction, id: InstId) -> Option<VReg> {
    func.inst(id).operands.first()?.as_vreg()
}

/// `AddRI d, iv, #1` (the induction step, either in-place or the phi source).
fn is_iv_add1(func: &MachFunction, id: InstId, iv: VReg) -> bool {
    let inst = func.inst(id);
    inst.opcode == AArch64Opcode::AddRI
        && inst.operands.len() == 3
        && inst.operands[1].as_vreg() == Some(iv)
        && inst.operands[2].as_imm() == Some(1)
}

/// Find the `+1` Gpr64 induction writeback in the latch.
fn find_induction(func: &MachFunction, def: &HashMap<u32, InstId>, latch: BlockId) -> Option<VReg> {
    for &id in &func.block(latch).insts {
        let inst = func.inst(id);
        if inst.opcode == AArch64Opcode::AddRI
            && inst.operands.len() == 3
            && inst.operands[2].as_imm() == Some(1)
        {
            let d = inst.operands[0].as_vreg()?;
            let s = inst.operands[1].as_vreg()?;
            if d == s && d.class == RegClass::Gpr64 {
                return Some(d);
            }
        }
    }
    for &id in &func.block(latch).insts {
        let Some((d, s)) = copy_like(func.inst(id)) else {
            continue;
        };
        if d.class != RegClass::Gpr64 {
            continue;
        }
        let Some(&sdef) = def.get(&s.id) else {
            continue;
        };
        let si = func.inst(sdef);
        if si.opcode == AArch64Opcode::AddRI
            && si.operands.len() == 3
            && si.operands[1].as_vreg() == Some(d)
            && si.operands[2].as_imm() == Some(1)
        {
            return Some(d);
        }
    }
    None
}

/// STRICT FULL-WIDTH copy walk (see neon_iota_fill): `v` reaches EXACTLY
/// `target` through `MovR`/`Copy`/`AddRI #0` copies with EVERY register in
/// the chain `Gpr64`. Everything this pass matches against the iv is 64-bit
/// index arithmetic — a truncating `w` hop would change the value for
/// `iv >= 2^32` (fail-closed).
fn reaches_reg(func: &MachFunction, def: &HashMap<u32, InstId>, mut v: VReg, target: VReg) -> bool {
    if target.class != RegClass::Gpr64 {
        return false;
    }
    for _ in 0..16 {
        if v.class != RegClass::Gpr64 {
            return false;
        }
        if v == target {
            return true;
        }
        // Only a copy that is the register's ONLY def holds the copied value
        // on every path.
        match crate::mach_util::sole_copy_source(func, def, v) {
            Some(src) => v = src,
            None => return false,
        }
    }
    false
}

/// A register is loop-invariant (for THIS pass's uses) iff:
///
/// * (a) it has NO def inside the loop body — so its runtime value at the
///   preheader equals the value every scalar iteration reads (VALUE
///   consistency; this is all trace equivalence needs), and
/// * (b) SOME block-resident def of it dominates the preheader — so the
///   guards' new preheader-side reads are definedness-safe. A multi-def
///   invariant like an OUTER loop's induction (init + outer-latch increment)
///   has a non-dominating LAST def; the dominating INIT is what makes the
///   read safe, so ANY dominating def suffices. A register with no def at
///   all (param-like) is read by the scalar loop itself, so reading it in
///   the preheader adds nothing new.
fn is_loop_invariant(
    func: &MachFunction,
    _def: &HashMap<u32, InstId>,
    dom: &DomTree,
    loop_insts: &HashSet<InstId>,
    preheader: BlockId,
    v: VReg,
) -> bool {
    for &id in loop_insts {
        if crate::effects::inst_defines_vreg(func.inst(id), v) {
            return false;
        }
    }
    let mut any_def = false;
    for &b in &func.block_order {
        for &id in &func.block(b).insts {
            if crate::effects::inst_defines_vreg(func.inst(id), v) {
                any_def = true;
                if dom.dominates(b, preheader) {
                    return true;
                }
            }
        }
    }
    !any_def
}

/// Opcodes permitted in the body: exactly the swap-chain vocabulary.
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        MovR | Copy | Madd | AddRI | CmpRI | CmpRR | BCond | B | LdrRI | StrRI
    )
}

// ---------------------------------------------------------------------------
// Transformation (guarded fast path in front; scalar loop untouched)
// ---------------------------------------------------------------------------

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    let x = rec.iv;
    let scalar = rec.header;

    // Fresh blocks: g0 (consts + y guard), g1 (m1 guard), g2 (m2 guard),
    // g3 (x guard), g4 (pointer setup), mb (bottom-tested main body).
    let g0 = func.create_block();
    let g1 = func.create_block();
    let g2 = func.create_block();
    let g3 = func.create_block();
    let g4 = func.create_block();
    let mb = func.create_block();
    insert_new_blocks_before(func, scalar, &[g0, g1, g2, g3, g4, mb]);

    func.add_edge(g0, scalar);
    func.add_edge(g0, g1);
    func.add_edge(g1, scalar);
    func.add_edge(g1, g2);
    func.add_edge(g2, scalar);
    func.add_edge(g2, g3);
    func.add_edge(g3, scalar);
    func.add_edge(g3, g4);
    func.add_edge(g4, mb);
    func.add_edge(mb, mb);
    func.add_edge(mb, scalar);

    // --- g0: constants + `y <u K` guard.
    let k_reg = materialize_in(func, g0, rec.k_const);
    let s_reg = materialize_in(func, g0, rec.s_const);
    let es_reg = materialize_in(func, g0, ELEM_SIZE);
    let cm1_reg = materialize_in(func, g0, rec.c_const - 1);
    let cs_reg = materialize_in(func, g0, (rec.c_const - 1) * rec.s_const);
    emit(
        func,
        g0,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.y), vreg(k_reg)],
    );
    emit(
        func,
        g0,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(scalar)],
    );
    emit(func, g0, AArch64Opcode::B, vec![block(g1)]);

    // --- g1: `m1 = y*S + (C-1) <u K` (wrap-free: y < 2^31 from g0).
    let m1 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g1,
        AArch64Opcode::Madd,
        vec![vreg(m1), vreg(rec.y), vreg(s_reg), vreg(cm1_reg)],
    );
    emit(func, g1, AArch64Opcode::CmpRR, vec![vreg(m1), vreg(k_reg)]);
    emit(
        func,
        g1,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(scalar)],
    );
    emit(func, g1, AArch64Opcode::B, vec![block(g2)]);

    // --- g2: `m2 = y + (C-1)*S <u K`.
    let m2 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g2,
        AArch64Opcode::AddRR,
        vec![vreg(m2), vreg(rec.y), vreg(cs_reg)],
    );
    emit(func, g2, AArch64Opcode::CmpRR, vec![vreg(m2), vreg(k_reg)]);
    emit(
        func,
        g2,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(scalar)],
    );
    emit(func, g2, AArch64Opcode::B, vec![block(g3)]);

    // --- g3: `x <u C` (at least one full iteration).
    emit(
        func,
        g3,
        AArch64Opcode::CmpRI,
        vec![vreg(x), imm(rec.c_const)],
    );
    emit(
        func,
        g3,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(scalar)],
    );
    emit(func, g3, AArch64Opcode::B, vec![block(g4)]);

    // --- g4: running pointers p1 = base + (y*S+x)*es, p2 = base + (x*S+y)*es.
    let i1 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g4,
        AArch64Opcode::Madd,
        vec![vreg(i1), vreg(rec.y), vreg(s_reg), vreg(x)],
    );
    let i2 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g4,
        AArch64Opcode::Madd,
        vec![vreg(i2), vreg(x), vreg(s_reg), vreg(rec.y)],
    );
    let p1 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g4,
        AArch64Opcode::Madd,
        vec![vreg(p1), vreg(i1), vreg(es_reg), vreg(rec.base)],
    );
    let p2 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g4,
        AArch64Opcode::Madd,
        vec![vreg(p2), vreg(i2), vreg(es_reg), vreg(rec.base)],
    );
    emit(func, g4, AArch64Opcode::B, vec![block(mb)]);

    // --- mb: the checked-free swap body (bottom-tested self-loop). Exact
    // scalar per-iteration trace: load p1, load p2, store p1 <- w2, store
    // p2 <- w1.
    let w1 = alloc(func, RegClass::Gpr32);
    let w2 = alloc(func, RegClass::Gpr32);
    emit(
        func,
        mb,
        AArch64Opcode::LdrRI,
        vec![vreg(w1), vreg(p1), imm(0)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::LdrRI,
        vec![vreg(w2), vreg(p2), imm(0)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::StrRI,
        vec![vreg(w2), vreg(p1), imm(0)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::StrRI,
        vec![vreg(w1), vreg(p2), imm(0)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::AddRI,
        vec![vreg(p1), vreg(p1), imm(ELEM_SIZE)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::AddRI,
        vec![vreg(p2), vreg(p2), imm(rec.s_const * ELEM_SIZE)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::AddRI,
        vec![vreg(x), vreg(x), imm(1)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::CmpRI,
        vec![vreg(x), imm(rec.c_const)],
    );
    emit(func, mb, AArch64Opcode::BCond, vec![imm(CC_LO), block(mb)]);
    emit(func, mb, AArch64Opcode::B, vec![block(scalar)]);

    // --- COMMIT.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), scalar, g0) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, scalar);
    func.add_edge(rec.preheader, g0);
    true
}

/// Materialize a `[0, u32::MAX]` constant into a fresh `Gpr64` via `Movz` +
/// `Movk`, APPENDED to `blk`.
fn materialize_in(func: &mut MachFunction, blk: BlockId, value: i64) -> VReg {
    let d = alloc(func, RegClass::Gpr64);
    let bits = value as u64;
    emit(
        func,
        blk,
        AArch64Opcode::Movz,
        vec![vreg(d), imm((bits & 0xFFFF) as i64)],
    );
    for hw in 1..4u32 {
        let chunk = (bits >> (hw * 16)) & 0xFFFF;
        if chunk != 0 {
            emit(
                func,
                blk,
                AArch64Opcode::Movk,
                vec![vreg(d), imm(chunk as i64), imm((hw * 16) as i64)],
            );
        }
    }
    d
}

// ---------------------------------------------------------------------------
// Small local IR helpers (independent copies, as in the sibling passes)
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

fn rewrite_block_target(inst: &mut MachInst, old: BlockId, new: BlockId) -> bool {
    let mut changed = false;
    for op in inst.operands.iter_mut() {
        if let MachOperand::Block(b) = op
            && *b == old
        {
            *b = new;
            changed = true;
        }
    }
    changed
}

fn remove_cfg_edge(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.block_mut(from).succs.retain(|&b| b != to);
    func.block_mut(to).preds.retain(|&b| b != from);
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

fn alloc(func: &mut MachFunction, class: RegClass) -> VReg {
    let max_existing = func
        .insts
        .iter()
        .flat_map(|inst| inst.operands.iter())
        .filter_map(MachOperand::as_vreg)
        .map(|v| v.id)
        .max()
        .unwrap_or(0);
    let mut id = func.alloc_vreg();
    while id <= max_existing {
        id = func.alloc_vreg();
    }
    VReg::new(id, class)
}

#[cfg(test)]
mod tests;
