// trust-cg-opt - SOUND NEON STENCIL (windowed-read) memory-map vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON stencil vectorizer (`neon-stencil`)
//!
//! Vectorizes counted integer *store* (map) loops whose body writes a single
//! output array from a **lane-wise** term over read-only input arrays accessed at
//! small **compile-time constant offsets** of the induction (a *windowed* /
//! *stencil* read), of the shape
//!
//! ```text
//! for i in [lo, hi) (signed i < hi):  out[i] = TERM(a[i+k1], a[i+k2], ..., b[i+k'], ...)
//! ```
//!
//! where `out` is a **store pointer** written only at index `i` (offset `0`), the
//! pointers `a, b, ...` are **only loaded** (each at one or more constant offsets
//! `a[i+K]`, `K` a small signed constant e.g. `-2,-1,0,+1,+2`), and `TERM` is a
//! lane-wise integer function of the loaded `i32` elements and 16-bit constants
//! using `+ - * & | ^ << >>` (plus the fused `madd`). At least one read must use a
//! **non-zero** offset (a pure same-index map `out[i]=f(a[i])` is left to
//! [`crate::neon_map`], which runs first). The two END streams of each base (its
//! lowest and highest offset `K`) are walked with paired NEON `LDP Qt1, Qt2` loads
//! at byte offset `(i+K)*4`; each MIDDLE stream of the same base is formed
//! **in-register** with `EXT.16B` sliding windows over the loaded end streams (see
//! *Window formation* below) instead of a third overlapping load stream. The
//! per-lane term is computed in `UNROLL = 4` independent `4 x i32` vector
//! registers (16 elements per vector iteration), and each vector is written to
//! `out[i..]` with `ST1 {Vt.4S}`. The ORIGINAL scalar loop handles the `< 16` tail
//! iterations **and** the loop's own boundary `[lo, hi)` unchanged.
//!
//! ## Window formation (`EXT.16B`)
//!
//! `EXT Vd.16B, Vn.16B, Vm.16B, #s` selects bytes `s .. s+15` of the 32-byte
//! concatenation `Vm:Vn` (`Vn` low). For a base loaded at its end offsets
//! `k_min < k_max`, a middle stream `K` (`d = K - k_min`, `e = k_max - K`, both in
//! `1..=3` so the byte shifts `4d` / `16-4e` are the proven `#4/#8/#12`) is exactly
//!
//! * sub-block `j <  UNROLL-1`: `EXT(Vmin[j], Vmin[j+1], #4d)` — bytes
//!   `16j+4d .. 16j+4d+15` of the `k_min` byte stream = elements `a[iv+K+4j ..]`;
//! * sub-block `j == UNROLL-1`: `EXT(Vmax[UNROLL-2], Vmax[UNROLL-1], #16-4e)` —
//!   the same window addressed from the TOP stream (the `k_min` stream has no
//!   `Vmin[UNROLL]` block to slide into; the `k_max` stream's last two blocks
//!   cover it exactly: `16(UNROLL-2) + 16-4e` bytes past `iv+k_max` is element
//!   `iv + k_max - e + 4(UNROLL-1) = iv + K + 4(UNROLL-1)`).
//!
//! This reads only bytes the end streams already load — the loaded byte range is a
//! strict SUBSET of the all-streams-loaded shape it replaces, so the OOB argument
//! below is unchanged. A middle whose `d` or `e` exceeds `3` (byte shift not in
//! `{4, 8, 12}` — the only immediates `encode_ext` accepts and the only ones with
//! SMT proof credit) is loaded directly, fail-closed, exactly as before; bases with
//! fewer than 3 streams have no middles and are unaffected. `STENCIL_EXT_ENABLED`
//! fail-closes the whole formation back to per-stream loads if the EXT proof were
//! ever retracted.
//!
//! It runs **after** [`crate::neon_map`] (which BAILS on any shifted read — its
//! `resolve_ai_base` forces the load index to equal the store index `i`) and
//! before `reduction_split`. Disable with `TRUST_CG_DISABLE_PASSES=neon_stencil`.
//!
//! ## Why this is SOUND — windowed reads + a store make BOTH aliasing AND OOB
//! load-bearing
//!
//! Like the other NEON map/reduction passes the transform is **purely additive**:
//! it inserts a vector main loop in front of the scalar loop and never edits the
//! scalar loop's instructions, so the scalar loop is correct by construction and
//! only the inserted vector loop needs justifying. Two facts do that, discharging
//! the two hazards the prompt calls out:
//!
//! ### (1) OOB / bounds — the halo stays inside the scalar loop's access set
//!
//! The store is at offset `0` (`out[i]`), so the vector guard enters the body only
//! when `sext(iv) + (width-1) < sext(hi)` (`width = 16`, computed in `i64` after
//! sign-extending `iv` and `hi` from `i32`, so no overflow) — exactly the
//! [`crate::neon_map`] guard. Under that guard, in a vector iteration at induction
//! value `iv` every lane `j in [0, 15]` has `iv + j` in `[lo, hi-1]` (because
//! `iv >= lo` and `iv + 15 <= hi-1`), i.e. `iv+j` is a value the *scalar* induction
//! also takes. Therefore:
//!
//! * the store `out[iv+j]` is a write the scalar loop performs at `i = iv+j`;
//! * each read `base[(iv+j)+K]` is a read the scalar loop performs at `i = iv+j`
//!   (same base, same constant `K`, same index).
//!
//! So the SET of memory addresses the vector loop touches (reads *and* writes) is a
//! **subset**, index-for-index, of the set the scalar loop touches — including the
//! halo: the lowest read `lo+minK` happens in the first vector iteration `iv=lo`
//! (which the scalar also reads at `i=lo`) and the highest read `iv_last+15+maxK`
//! satisfies `iv_last+15 <= hi-1`, so it equals `hi-1+maxK`'s scalar read at
//! `i=iv_last+15` at worst. The vector loop can thus never read `a[lo+minK-1]` or
//! `a[hi-1+maxK+1]`, nor write `out[lo-1]` or `out[hi]`. If the scalar program is
//! in-bounds, so is the vector loop, reading identical bytes; if the scalar program
//! is already OOB we introduce no *new* OOB. (No i32 overflow of `(iv+j)+K` can
//! occur for a well-defined program: a valid stencil needs `hi-1+maxK` to be a
//! real index `< size <= INT_MAX`, bounding `hi` away from `INT_MAX`, and `lo` is
//! the non-negative loop start; the guard is computed in `i64` regardless. Offsets
//! are additionally bounded `|K| <= MAX_OFFSET`.)
//!
//! ### (2) Aliasing — the store is disjoint from every read
//!
//! With a shifted read *and* a store, writing `out[i]` in a vector chunk must not
//! clobber a `base[j]` that a later lane/iteration still needs. That is provable
//! only when `out`'s memory is disjoint from every read array. We therefore require
//! (see the `R_alias` gate):
//!
//! * the store base `out` is a trust_ir **`noalias` parameter**
//!   (`MachFunction::noalias_params`), AND
//! * every read base is a **distinct** `noalias` parameter (`base.id != out.id`
//!   and `base.id in noalias_params`).
//!
//! Distinct `noalias` params name disjoint memory, so a store through `out` cannot
//! affect any load through any `base`. Hence within a vector chunk we may issue all
//! `LD1` before all `ST1` (or in any order): no store writes memory any load reads,
//! so every lane observes the same bytes the scalar loop observes, and across
//! chunks the written `out[iv..iv+16)` ranges are disjoint. An **in-place** stencil
//! (`out` == a read base, `a[i]=a[i-1]+a[i+1]`) is a genuine loop-carried
//! dependency — the scalar loop's `a[i-1]` on the RHS is the value written the
//! previous iteration — and is explicitly rejected (a read base equal to the store
//! base BAILS), never vectorized.
//!
//! If ANY premise is unprovable (store not at offset 0, a non-constant / too-large
//! offset, non-unit stride, `out` or a read base not `noalias`, `out` aliases a
//! read base, i64, a second store / call / atomic / unmodeled op, the induction
//! used as a term value, an unrecognized term op, or *no* non-zero offset — a pure
//! map) the loop is left **entirely** to the scalar path — fail-closed beats
//! miscompile.
//!
//! ## Why not i64
//!
//! i64 stencils BAIL: the vector guard needs the overflow headroom the `i32 -> i64`
//! sign-extension provides but `i64` lacks, mirroring [`crate::neon_array`] /
//! [`crate::neon_map`]. (`.4S` handles 32-bit lanes only here.)

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Lanes per NEON iteration (`4 x i32`).
const VF: i64 = 4;
/// NEON element-size operand code for `S` (32-bit) lanes.
const ELEM_S: i64 = 4;
/// NEON arrangement operand code for `.4S`.
const ARR_S4: i64 = 5;
/// AArch64 condition code for signed less-than (`LT`).
const CC_LT: i64 = 11;
/// Byte size of an `i32` array element (the only supported element width).
const ELEM_BYTES: i64 = 4;
/// Independent vector registers processed per vector iteration (ILP + fewer
/// loop iterations). `UNROLL * VF` i32 lanes are processed per iteration (16).
const UNROLL: usize = 4;
/// Largest permitted absolute stencil offset `|K|`. Small by construction (real
/// stencils use `-2..+2`); the bound keeps `K*ELEM_BYTES` inside the ADD/SUB
/// 12-bit immediate and keeps the no-i32-overflow argument airtight.
const MAX_OFFSET: i64 = 16;
/// Fail-closed switch for the `EXT.16B` in-register window formation of middle
/// streams (module docs, *Window formation*). `false` reverts every stream to
/// its own LDP load stream — the previous (slower, equally correct) shape — if
/// the `NeonExtV` SMT proof were ever retracted.
const STENCIL_EXT_ENABLED: bool = true;

/// The `neon-stencil` machine pass.
#[derive(Default)]
pub struct NeonStencilPass {
    /// Number of loops vectorized in the last run (diagnostics/tests).
    fired: usize,
}

impl NeonStencilPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonStencilPass {
    fn name(&self) -> &str {
        "neon-stencil"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        self.fired = 0;
        if self.stencil_cannot_fire(func) {
            return false;
        }
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    // Share the AnalysisCache's CFG-derived DomTree + LoopAnalysis instead of
    // recomputing per pass (see NeonArrayPass). Sound + byte-identical: both
    // analyses depend only on the CFG, which the cache invalidates on any CFG
    // change, so a shared instance equals a fresh recompute here.
    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        self.fired = 0;
        // Cheap O(1) pre-gate BEFORE building/cloning any analysis.
        if self.stencil_cannot_fire(func) {
            return false;
        }
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

impl NeonStencilPass {
    // Cheap O(1) structural pre-gate: the aliasing gate REQUIRES `out` and every
    // read base to be distinct `noalias` params and the guard-replay authority,
    // so with neither present nothing can fire — bail before any analysis. (The
    // exact pair of early returns the old `run` performed before computing
    // DomTree/loops; hoisting them here also skips the shared-analysis clone.)
    fn stencil_cannot_fire(&self, func: &MachFunction) -> bool {
        (!trust_cg_lower::guard_evidence::validator_guard_replay_authority_available()
            && !cfg!(test))
            || func.noalias_params.is_empty()
    }

    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        // Recognize all candidate loops first; applying a plan only *adds* blocks
        // (never renumbers existing block/inst ids or edits other loops' blocks),
        // so recognized data for other loops stays valid.
        let mut plans = Vec::new();
        for lp in loops.all_loops() {
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
        if changed && std::env::var("TRUST_CG_DUMP_NEONSTENCIL").is_ok() {
            eprintln!("[neon-stencil] fn={} vectorized={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// A distinct read stream: a `(base, K)` pair — the array `base` read at the
/// constant induction offset `K` (`base[i+K]`).
#[derive(Clone, Copy, PartialEq, Eq)]
struct Stream {
    base: VReg,
    k: i64,
}

/// A fully validated, lane-wise-vectorizable stencil loop.
struct Recognized {
    /// Preheader-guard block reached once before the loop.
    guard: BlockId,
    /// Block that branches into `guard`.
    preheader: BlockId,
    /// The `preheader` terminator instruction targeting `guard`.
    preheader_term: InstId,
    /// Loop-carried induction register (`+1` each iteration, `i32`).
    iv: VReg,
    /// Loop bound register (`iv < bound`, `i32`) — the loop's `hi`.
    bound: VReg,
    /// The per-iteration stored value (the stencil term), SSA def in the loop.
    term: VReg,
    /// Loop-invariant base pointer of the store `out[i]` (offset 0).
    store_base: VReg,
    /// Global def map (`vreg id -> defining InstId`).
    def: HashMap<u32, InstId>,
    /// Instruction ids that live inside the loop body.
    loop_insts: HashSet<InstId>,
    /// Map from a recognized load's result vreg id to its `(base, K)` stream.
    loads: HashMap<u32, Stream>,
    /// Distinct `(base, K)` read streams referenced by `term`, first-seen order
    /// (deterministic emission).
    streams: Vec<Stream>,
}

/// Opcodes permitted anywhere in the loop body. Anything else => BAIL (rules out
/// a SECOND store, calls, atomics, division and any unmodeled effect). Exactly
/// `StrRI` is permitted as the single output store (its uniqueness and `out[i]`
/// address are checked in [`Recognized::recognize`]). `AddRR/SubRR/AddRI/SubRI`
/// additionally cover the shifted-index computations `iv +/- K`.
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
            | LdrRI
            | StrRI
    )
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

/// `AddRI(d, s, 0)` / `MovR(d, s)` / `Copy(d, s)` copy idioms => `(d, s)`.
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

/// 16-bit `Movz` constant value of `val`, if any (may be defined anywhere the
/// global def map can see, e.g. the preheader).
fn const_value(func: &MachFunction, def: &HashMap<u32, InstId>, val: VReg) -> Option<i64> {
    let inst = func.inst(*def.get(&val.id)?);
    if inst.opcode == AArch64Opcode::Movz
        && inst.operands.len() == 2
        && let Some(v) = imm_of(&inst.operands[1])
        && (0..=0xFFFF).contains(&v)
    {
        return Some(v);
    }
    None
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

        // Whitelist every opcode in the loop body — no call/div/atomic/second
        // store/etc.
        let mut loop_insts = HashSet::new();
        for &b in [header, latch].iter() {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

        let def = build_def_map(func);

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
        let preheader_term = *func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&guard))?;

        // (R2) latch: the exit branch `BCond(LT) -> header` and its compare.
        let latch_insts = &func.block(latch).insts;
        let bcond = latch_insts
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::BCond && branch_targets(i).contains(&header))?;
        if imm_of(&bcond.operands[0]) != Some(CC_LT) {
            return None; // only signed `<` counted loops
        }
        let cmp = latch_insts
            .iter()
            .map(|&id| func.inst(id))
            .rev()
            .find(|i| i.opcode == AArch64Opcode::CmpRR)?;
        let iv = vreg_of(&cmp.operands[0])?;
        let bound = vreg_of(&cmp.operands[1])?;

        // Loop-carried writebacks in the latch: exactly ONE (the induction). A
        // stencil map carries no accumulator — a second writeback means this is a
        // reduction (left to neon-array) or an unrecognized shape.
        let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
        for &id in latch_insts {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                writebacks.push((d, s));
            }
        }
        if writebacks.len() != 1 {
            return None;
        }
        let (wb_dst, iv_src) = writebacks[0];
        if wb_dst != iv {
            return None;
        }

        // (R3) step: iv_src = AddRR(iv, +1) (or AddRI(iv, 1)).
        if !is_increment_by_one(func, &def, iv_src, iv) {
            return None;
        }

        // i32 lanes only; i64 BAILS (see module docs).
        if iv.class != RegClass::Gpr32 || bound.class != RegClass::Gpr32 {
            return None;
        }
        // The bound must be loop-invariant and available in the preheader.
        let bound_def = *def.get(&bound.id)?;
        let bound_block = block_of_inst(func, bound_def)?;
        if !dom.dominates(bound_block, preheader) {
            return None;
        }

        // (R_store) EXACTLY ONE store in the body — the output `out[i]`.
        let mut stores: Vec<InstId> = loop_insts
            .iter()
            .copied()
            .filter(|&id| func.inst(id).opcode == AArch64Opcode::StrRI)
            .collect();
        if stores.len() != 1 {
            return None;
        }
        let store = func.inst(stores.pop()?);
        if store.operands.len() != 3 || imm_of(&store.operands[2]) != Some(0) {
            return None;
        }
        let term = vreg_of(&store.operands[0])?; // stored value (stencil term)
        let store_addr = vreg_of(&store.operands[1])?;
        // The stored value must be i32 (a `.4S` lane) and defined in the loop.
        if term.class != RegClass::Gpr32 {
            return None;
        }

        let mut rec = Recognized {
            guard,
            preheader,
            preheader_term,
            iv,
            bound,
            term,
            store_base: VReg::new(0, RegClass::Gpr64), // filled below
            def,
            loop_insts,
            loads: HashMap::new(),
            streams: Vec::new(),
        };

        // Store address must be `out[i] = base + sext(iv)*4` (offset K=0 EXACTLY —
        // a shifted store would change the WRITTEN range; require `out[i]`).
        let (store_base, store_k) = rec.resolve_shifted_base(func, dom, store_addr)?;
        if store_k != 0 {
            return None; // store must be at the induction index (out[i])
        }
        rec.store_base = store_base;

        // (R_term) The stored value must be lowerable per-lane: every reachable
        // leaf is a recognized `i32` shifted array load `base[i+K]` or a 16-bit
        // constant — NOT the induction. Populates `rec.loads` / `rec.streams`.
        let mut seen = HashSet::new();
        if !rec.node_ok(func, dom, term, &mut seen) {
            return None;
        }

        // Must genuinely be a stencil: at least one read at a NON-ZERO offset.
        // A pure same-index map (`out[i]=f(a[i])`, all K==0) is left to neon-map
        // (which ran first); firing here too would double-vectorize it.
        if !rec.streams.iter().any(|s| s.k != 0) {
            return None;
        }

        // Every load in the body must be a RECOGNIZED shifted load feeding the
        // term. A stray load from another pointer (value unused in the term) would
        // not appear in `streams`; reject it so the aliasing gate cannot be
        // bypassed by an unaccounted read pointer.
        let all_loads_recognized = rec.loop_insts.iter().all(|&id| {
            let inst = func.inst(id);
            if inst.opcode != AArch64Opcode::LdrRI {
                return true;
            }
            match inst.operands.first() {
                Some(MachOperand::VReg(v)) => rec.loads.contains_key(&v.id),
                _ => false,
            }
        });
        if !all_loads_recognized {
            return None;
        }

        // (R_alias) SOUNDNESS gate — aliasing. A shifted read PLUS a store makes
        // aliasing load-bearing: prove `out` is disjoint from every read array.
        // Require `out` to be a `noalias` param AND every read base to be a
        // DISTINCT `noalias` param (`base != out`, `base in noalias`). Distinct
        // noalias params name disjoint memory, so the store cannot clobber any
        // read. An in-place stencil (a read base == `out`) is a loop-carried
        // dependency and is rejected here.
        let noalias: HashSet<u32> = func.noalias_params.iter().copied().collect();
        if !noalias.contains(&store_base.id) {
            return None;
        }
        let mut read_bases: Vec<VReg> = Vec::new();
        for s in &rec.streams {
            if s.base.id == store_base.id {
                return None; // in-place stencil: loop-carried dependency — BAIL
            }
            if !noalias.contains(&s.base.id) {
                return None; // read base could alias the store — cannot prove disjoint
            }
            if !read_bases.iter().any(|b| b.id == s.base.id) {
                read_bases.push(s.base);
            }
        }

        Some(rec)
    }

    /// Recognize an `i32` shifted address `base + sext(iv + K)*4` and return its
    /// loop-invariant `base` and constant offset `K`. The address must be
    /// `Madd(idx, es, base)` (any factor order) with `idx = Sxtw(shift)`,
    /// `es = 4`, where `shift` is `iv` (K=0) or `iv +/- c` for a small constant
    /// `c` (`|c| <= MAX_OFFSET`).
    fn resolve_shifted_base(
        &self,
        func: &MachFunction,
        dom: &DomTree,
        addr: VReg,
    ) -> Option<(VReg, i64)> {
        let madd = func.inst(*self.def.get(&addr.id)?);
        if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
            return None;
        }
        let f1 = vreg_of(&madd.operands[1])?;
        let f2 = vreg_of(&madd.operands[2])?;
        let base = vreg_of(&madd.operands[3])?;
        let es_ok = |factor: VReg| const_value(func, &self.def, factor) == Some(ELEM_BYTES);
        // One factor is the (sign-extended) shifted index, the other is `4`.
        let (idx_factor, es_factor) = if es_ok(f2) {
            (f1, f2)
        } else if es_ok(f1) {
            (f2, f1)
        } else {
            return None;
        };
        let _ = es_factor;
        let k = self.sext_index_offset(func, idx_factor)?;
        // `base` loop-invariant: its def dominates the preheader.
        let base_def = *self.def.get(&base.id)?;
        let base_block = block_of_inst(func, base_def)?;
        if !dom.dominates(base_block, self.preheader) {
            return None;
        }
        Some((base, k))
    }

    /// If `v` is `Sxtw(shift)` (defined in the loop) where `shift` is the
    /// induction offset `iv + K` for a small constant `K`, return `K`.
    fn sext_index_offset(&self, func: &MachFunction, v: VReg) -> Option<i64> {
        let &id = self.def.get(&v.id)?;
        if !self.loop_insts.contains(&id) {
            return None;
        }
        let inst = func.inst(id);
        if inst.opcode != AArch64Opcode::Sxtw || inst.operands.len() != 2 {
            return None;
        }
        let shift = vreg_of(&inst.operands[1])?;
        self.index_offset(func, shift)
    }

    /// Return `K` such that `shift == iv + K` (a compile-time constant), where
    /// `shift` is `iv` (K=0) or a loop-body `iv +/- c` with `1 <= c <= MAX_OFFSET`.
    fn index_offset(&self, func: &MachFunction, shift: VReg) -> Option<i64> {
        if shift == self.iv {
            return Some(0);
        }
        let &id = self.def.get(&shift.id)?;
        if !self.loop_insts.contains(&id) {
            return None;
        }
        let inst = func.inst(id);
        use AArch64Opcode::*;
        let small = |c: i64| (1..=MAX_OFFSET).contains(&c);
        match inst.opcode {
            AddRR => {
                let a = vreg_of(&inst.operands[1])?;
                let b = vreg_of(&inst.operands[2])?;
                if a == self.iv {
                    let c = const_value(func, &self.def, b)?;
                    if small(c) {
                        return Some(c);
                    }
                } else if b == self.iv {
                    let c = const_value(func, &self.def, a)?;
                    if small(c) {
                        return Some(c);
                    }
                }
                None
            }
            SubRR => {
                // Only `iv - c` is a stencil offset (`c - iv` is not affine in iv).
                let a = vreg_of(&inst.operands[1])?;
                let b = vreg_of(&inst.operands[2])?;
                if a == self.iv {
                    let c = const_value(func, &self.def, b)?;
                    if small(c) {
                        return Some(-c);
                    }
                }
                None
            }
            AddRI => {
                let a = vreg_of(&inst.operands[1])?;
                let c = imm_of(&inst.operands[2])?;
                if a == self.iv && small(c) {
                    return Some(c);
                }
                None
            }
            SubRI => {
                let a = vreg_of(&inst.operands[1])?;
                let c = imm_of(&inst.operands[2])?;
                if a == self.iv && small(c) {
                    return Some(-c);
                }
                None
            }
            _ => None,
        }
    }

    /// Recognize an `i32` shifted array load `dst = *(base + sext(iv+K)*4)` and
    /// return its `(base, K)` stream, loaded at offset 0.
    fn load_stream(&self, func: &MachFunction, dom: &DomTree, dst: VReg) -> Option<Stream> {
        let load = func.inst(*self.def.get(&dst.id)?);
        if load.opcode != AArch64Opcode::LdrRI
            || load.operands.len() != 3
            || dst.class != RegClass::Gpr32
            || imm_of(&load.operands[2]) != Some(0)
        {
            return None;
        }
        let addr = vreg_of(&load.operands[1])?;
        let (base, k) = self.resolve_shifted_base(func, dom, addr)?;
        Some(Stream { base, k })
    }

    /// Read-only feasibility check mirroring [`lower`]: every reachable node is a
    /// recognized `i32` shifted array load, a 16-bit constant, or an allowed
    /// lane-wise op over such. The induction is NOT a valid term value. Populates
    /// `self.loads` / `self.streams` as loads are recognized.
    fn node_ok(
        &mut self,
        func: &MachFunction,
        dom: &DomTree,
        val: VReg,
        seen: &mut HashSet<u32>,
    ) -> bool {
        if val == self.iv {
            return false; // induction is not a lane-wise term value
        }
        if const_value(func, &self.def, val).is_some() {
            return true;
        }
        if !seen.insert(val.id) {
            return true; // already validated on an earlier path
        }
        let Some(&def_id) = self.def.get(&val.id) else {
            return false; // non-const value defined outside the loop
        };
        if !self.loop_insts.contains(&def_id) {
            return false;
        }
        let opcode = func.inst(def_id).opcode;
        use AArch64Opcode::*;
        if opcode == LdrRI {
            let Some(stream) = self.load_stream(func, dom, val) else {
                return false;
            };
            self.loads.insert(val.id, stream);
            if !self.streams.contains(&stream) {
                self.streams.push(stream);
            }
            return true;
        }
        let ops = func.inst(def_id).operands.clone();
        match opcode {
            MulRR | AddRR | SubRR | AndRR | OrrRR | EorRR => {
                let (Some(a), Some(b)) = (vreg_of(&ops[1]), vreg_of(&ops[2])) else {
                    return false;
                };
                self.node_ok(func, dom, a, seen) && self.node_ok(func, dom, b, seen)
            }
            AddRI | SubRI | AndRI | OrrRI | EorRI => {
                let Some(a) = vreg_of(&ops[1]) else {
                    return false;
                };
                let ok_imm = matches!(imm_of(&ops[2]), Some(v) if (0..=0xFFFF).contains(&v));
                ok_imm && self.node_ok(func, dom, a, seen)
            }
            LslRI | LsrRI | AsrRI => {
                let Some(a) = vreg_of(&ops[1]) else {
                    return false;
                };
                let ok_sh = matches!(imm_of(&ops[2]), Some(v) if (0..=31).contains(&v));
                ok_sh && self.node_ok(func, dom, a, seen)
            }
            Madd if ops.len() == 4 => {
                let (Some(a), Some(b), Some(c)) =
                    (vreg_of(&ops[1]), vreg_of(&ops[2]), vreg_of(&ops[3]))
                else {
                    return false;
                };
                self.node_ok(func, dom, a, seen)
                    && self.node_ok(func, dom, b, seen)
                    && self.node_ok(func, dom, c, seen)
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
            vreg_of(&inst.operands[1]) == Some(iv) && imm_of(&inst.operands[2]) == Some(1)
        }
        AArch64Opcode::AddRR => {
            let a = vreg_of(&inst.operands[1]);
            let b = vreg_of(&inst.operands[2]);
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
    /// Vector register index in `0..UNROLL` currently being lowered.
    accum: usize,
    vbody: BlockId,
    preheader_term: InstId,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// Load-result vreg id -> `(base, K)` stream (from recognition).
    loads: HashMap<u32, Stream>,
    /// `(base id, K, unroll k)` -> the `.4S` vector loaded for that sub-block.
    loaded: HashMap<(u32, i64, usize), VReg>,
    const_cache: HashMap<i64, VReg>,
    /// Per-sub-block memo of already-lowered scalar values.
    memo: HashMap<u32, VReg>,
}

/// Plan the `EXT.16B` in-register window formation (module docs, *Window
/// formation*): map each MIDDLE stream `(base, K)` that can be formed from its
/// base's END streams to `(d, e)` = `(K - k_min, k_max - K)`. Only middles with
/// `d` AND `e` in `1..=3` qualify — their byte shifts `4d` / `16-4e` are the
/// proven (and encoder-accepted) `#4/#8/#12`. END streams and non-qualifying
/// middles are absent from the map and keep their own load stream (fail-closed
/// to the previous shape). `UNROLL >= 2` is required by the last-sub-block
/// formation; the plan is empty otherwise (and when `STENCIL_EXT_ENABLED` is
/// retracted).
fn plan_ext_windows(streams: &[Stream]) -> HashMap<(u32, i64), (i64, i64)> {
    let mut derived = HashMap::new();
    if !STENCIL_EXT_ENABLED || UNROLL < 2 {
        return derived;
    }
    // Per base: the lowest and highest constant offset K (the END streams).
    let mut ends: HashMap<u32, (i64, i64)> = HashMap::new();
    for s in streams {
        let e = ends.entry(s.base.id).or_insert((s.k, s.k));
        e.0 = e.0.min(s.k);
        e.1 = e.1.max(s.k);
    }
    for s in streams {
        let (kmin, kmax) = ends[&s.base.id];
        if s.k == kmin || s.k == kmax {
            continue; // END stream: always loaded
        }
        let d = s.k - kmin;
        let e = kmax - s.k;
        if (1..=3).contains(&d) && (1..=3).contains(&e) {
            derived.insert((s.base.id, s.k), (d, e));
        }
    }
    derived
}

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    let width = UNROLL as i64 * VF; // lanes per vector iteration (16)
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    insert_new_blocks_before(func, rec.guard, &[vh, vb, vl, vx]);

    // Internal edges among fresh blocks only — touching the original loop's
    // entry is deferred to the COMMIT below so a lowering failure cannot leave a
    // broken CFG.
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: sign-extend the loop bound once, materialize element size.
    let nb64 = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Sxtw,
        vec![vreg(nb64), vreg(rec.bound)],
    );
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(ELEM_BYTES)],
    );

    // --- Vector header: guard `sxtw(iv) + (width-1) < sxtw(bound)` (i64, no
    // overflow). Since the store is at offset 0, this makes the write range and
    // (by the index-correspondence argument) every halo read stay inside the
    // scalar loop's access set — enough for a full `width`-lane block.
    let gi = alloc(func, RegClass::Gpr64);
    let gilast = alloc(func, RegClass::Gpr64);
    emit(func, vh, AArch64Opcode::Sxtw, vec![vreg(gi), vreg(rec.iv)]);
    emit(
        func,
        vh,
        AArch64Opcode::AddRI,
        vec![vreg(gilast), vreg(gi), imm(width - 1)],
    );
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(gilast), vreg(nb64)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LT), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Window-formation plan (module docs, *Window formation*): per base the
    // END streams (lowest / highest `K`) get their own load stream; a MIDDLE
    // stream whose byte shifts land on the proven `EXT` immediates `#4/#8/#12`
    // is instead formed in-register from the loaded ends. Middles that do not
    // fit (shift distance > 3 lanes) keep their own load stream — fail-closed
    // to the previous shape. The plan is computed up front from `rec.streams`
    // only, so emission below cannot fail halfway.
    let derived: HashMap<(u32, i64), (i64, i64)> = plan_ext_windows(&rec.streams);

    // --- Vector body: sign-extend iv once. For each LOADED `(base, K)` stream
    // compute its start address `base + sext(iv)*4 + K*4` (`= base + (iv+K)*4`
    // in i64, no i32 wrap for a well-defined stencil) and walk it with `UNROLL/2`
    // post-index `LDP Qt1, Qt2` pair loads (each advances the pointer by 32
    // bytes), so sub-block `k` reads elements `[iv+K+4k, iv+K+4k+4)`. All input
    // loads are emitted BEFORE any store (and `out` is disjoint from every read
    // base), so no store can clobber a not-yet-read element. Derived middle
    // streams add NO loads: the loaded byte range is a SUBSET of the
    // all-streams-loaded shape (the OOB argument above is unchanged).
    let si = alloc(func, RegClass::Gpr64);
    emit(func, vb, AArch64Opcode::Sxtw, vec![vreg(si), vreg(rec.iv)]);
    let mut loaded: HashMap<(u32, i64, usize), VReg> = HashMap::new();
    for stream in &rec.streams {
        if derived.contains_key(&(stream.base.id, stream.k)) {
            continue; // formed in-register below — no load stream of its own
        }
        // p0 = base + si*4   (Madd d, n, m, a = a + n*m).
        let p0 = alloc(func, RegClass::Gpr64);
        emit(
            func,
            vb,
            AArch64Opcode::Madd,
            vec![vreg(p0), vreg(si), vreg(c_es), vreg(stream.base)],
        );
        // Apply the constant byte offset K*4 (may be negative).
        let p = if stream.k == 0 {
            p0
        } else {
            let off = stream.k * ELEM_BYTES;
            let pk = alloc(func, RegClass::Gpr64);
            if off > 0 {
                emit(
                    func,
                    vb,
                    AArch64Opcode::AddRI,
                    vec![vreg(pk), vreg(p0), imm(off)],
                );
            } else {
                emit(
                    func,
                    vb,
                    AArch64Opcode::SubRI,
                    vec![vreg(pk), vreg(p0), imm(-off)],
                );
            }
            pk
        };
        // `UNROLL/2` post-index `LDP Qt1, Qt2, [p], #32` pair loads —
        // bit-identical (little-endian) to the 4 `LD1 {Vt.4S}, [p], #16` they
        // replace: the SAME 64 bytes in the SAME order (`Qt1 = [p]`,
        // `Qt2 = [p+16]`, `p += 32`, twice), so sub-block `k` still reads
        // elements `[iv+K+4k, iv+K+4k+4)`.
        for pair in 0..UNROLL / 2 {
            let q0 = alloc(func, RegClass::Fpr128);
            let q1 = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vb,
                AArch64Opcode::NeonLdpQPost,
                vec![vreg(q0), vreg(q1), vreg(p), imm(32)],
            );
            loaded.insert((stream.base.id, stream.k, 2 * pair), q0);
            loaded.insert((stream.base.id, stream.k, 2 * pair + 1), q1);
        }
    }

    // --- Vector body: form each derived MIDDLE stream in-register with the
    // proven `EXT.16B` sliding windows over its base's loaded END streams (all
    // loads are already emitted; `EXT` is pure, so every load still precedes
    // every store). Sub-block `j < UNROLL-1` slides UP from the `k_min` stream
    // (`EXT(Vmin[j], Vmin[j+1], #4d)`); the LAST sub-block has no
    // `Vmin[UNROLL]` block to slide into and is addressed from the TOP stream
    // instead (`EXT(Vmax[UNROLL-2], Vmax[UNROLL-1], #16-4e)`) — byte-exact per
    // the module docs.
    for stream in &rec.streams {
        let Some(&(d, e)) = derived.get(&(stream.base.id, stream.k)) else {
            continue;
        };
        let kmin = stream.k - d;
        let kmax = stream.k + e;
        for j in 0..UNROLL {
            let (lo_src, hi_src, shift) = if j + 1 < UNROLL {
                (
                    loaded.get(&(stream.base.id, kmin, j)),
                    loaded.get(&(stream.base.id, kmin, j + 1)),
                    d * ELEM_BYTES,
                )
            } else {
                (
                    loaded.get(&(stream.base.id, kmax, UNROLL - 2)),
                    loaded.get(&(stream.base.id, kmax, UNROLL - 1)),
                    (VF - e) * ELEM_BYTES,
                )
            };
            // The END streams are always loaded (plan invariant); bail without
            // committing if that were ever violated.
            let (Some(&lo_src), Some(&hi_src)) = (lo_src, hi_src) else {
                return false;
            };
            let dst = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vb,
                AArch64Opcode::NeonExtV,
                vec![vreg(dst), vreg(lo_src), vreg(hi_src), imm(shift)],
            );
            loaded.insert((stream.base.id, stream.k, j), dst);
        }
    }

    // --- Vector body: a SEPARATE post-index pointer for the output store,
    // computed as `store_base + si*4` (offset 0). For each sub-block: lower TERM
    // over that sub-block's loaded lanes and ST1.4S it back, advancing by 16 bytes.
    let sp = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vb,
        AArch64Opcode::Madd,
        vec![vreg(sp), vreg(si), vreg(c_es), vreg(rec.store_base)],
    );
    let mut ctx = LowerCtx {
        iv: rec.iv,
        accum: 0,
        vbody: vb,
        preheader_term: pre,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        loads: rec.loads.clone(),
        loaded,
        const_cache: HashMap::new(),
        memo: HashMap::new(),
    };
    // Lower every sub-block's term first, then store them in PAIRS with
    // post-index `STP Qk, Qk+1, [sp], #32` — one instruction per 32 bytes, like
    // clang's `stp q, q` stencil-store shape. Byte-identical to the prior
    // per-block `ST1 {V.4S}, [sp], #16` sequence: a full-width vector term is a
    // 16-byte Q register, so the paired store writes the SAME 32 bytes in the
    // SAME order to the SAME running pointer. Any odd trailing block (UNROLL not
    // even) keeps a single ST1.
    let mut vterms: Vec<VReg> = Vec::with_capacity(UNROLL);
    for k in 0..UNROLL {
        ctx.accum = k;
        ctx.memo.clear();
        let Some(vterm) = lower(func, &mut ctx, rec.term) else {
            return false;
        };
        vterms.push(vterm);
    }
    let mut k = 0;
    while k + 1 < UNROLL {
        emit(
            func,
            vb,
            AArch64Opcode::NeonStpQPost,
            vec![vreg(vterms[k]), vreg(vterms[k + 1]), vreg(sp), imm(32)],
        );
        k += 2;
    }
    if k < UNROLL {
        emit(
            func,
            vb,
            AArch64Opcode::NeonSt1Post,
            vec![vreg(vterms[k]), vreg(sp), imm(ARR_S4)],
        );
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: advance the scalar induction by `width`.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector exit: nothing to reduce (a map has no accumulator). Fall through
    // to the original scalar loop, which writes the disjoint tail `out[V..hi)`.
    emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);

    // --- COMMIT: everything above only added fresh, unreachable blocks. Splice
    // them in front of the scalar loop by redirecting the single preheader->guard
    // edge through the vector loop. This is the point of no return; it runs only
    // after all lowering succeeded.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.guard, vh) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.guard);
    func.add_edge(rec.preheader, vh);
    func.add_edge(vx, rec.guard);

    true
}

fn lower(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> Option<VReg> {
    if val == ctx.iv {
        return None;
    }
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
    }
    // A recognized load leaf -> the vector loaded for this sub-block + stream.
    if let Some(stream) = ctx.loads.get(&val.id).copied() {
        let v = *ctx.loaded.get(&(stream.base.id, stream.k, ctx.accum))?;
        ctx.memo.insert(val.id, v);
        return Some(v);
    }
    if let Some(imm_v) = const_value(func, &ctx.def, val) {
        let v = const_vec(func, ctx, imm_v);
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
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonMulV, a, b, true)
        }
        AddRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonAddV, a, b, true)
        }
        SubRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonSubV, a, b, true)
        }
        AndRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonAndV, a, b, false)
        }
        OrrRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonOrrV, a, b, false)
        }
        EorRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            bin(func, ctx, NeonEorV, a, b, false)
        }
        AddRI | SubRI | AndRI | OrrRI | EorRI => {
            let a = lower(func, ctx, vreg_of(&ops[1])?)?;
            let cvec = const_vec(func, ctx, imm_of(&ops[2])?);
            let (nop, arr) = match opcode {
                AddRI => (NeonAddV, true),
                SubRI => (NeonSubV, true),
                AndRI => (NeonAndV, false),
                OrrRI => (NeonOrrV, false),
                _ => (NeonEorV, false),
            };
            bin(func, ctx, nop, a, cvec, arr)
        }
        LslRI | LsrRI | AsrRI => {
            let a = lower(func, ctx, vreg_of(&ops[1])?)?;
            let sh = imm_of(&ops[2])?;
            let nop = match opcode {
                LslRI => NeonShlVImm,
                LsrRI => NeonUshrVImm,
                _ => NeonSshrVImm,
            };
            let d = alloc(func, RegClass::Fpr128);
            emit(
                func,
                ctx.vbody,
                nop,
                vec![vreg(d), vreg(a), imm(sh), imm(ARR_S4)],
            );
            d
        }
        Madd => {
            let a = lower(func, ctx, vreg_of(&ops[1])?)?;
            let b = lower(func, ctx, vreg_of(&ops[2])?)?;
            let c = lower(func, ctx, vreg_of(&ops[3])?)?;
            let m = bin(func, ctx, NeonMulV, a, b, true);
            bin(func, ctx, NeonAddV, m, c, true)
        }
        _ => return None,
    };
    ctx.memo.insert(val.id, result);
    Some(result)
}

fn lower_two(
    func: &mut MachFunction,
    ctx: &mut LowerCtx,
    ops: &[MachOperand],
) -> Option<(VReg, VReg)> {
    let a = lower(func, ctx, vreg_of(ops.get(1)?)?)?;
    let b = lower(func, ctx, vreg_of(ops.get(2)?)?)?;
    Some((a, b))
}

/// Emit a same-shape binary NEON op `d = op(a, b)` in the vector body. `arr`
/// selects whether the op carries an arrangement immediate (arithmetic: `.4S`)
/// or none (bitwise logic: `.16B`, Q inferred from the FPR128 class).
fn bin(
    func: &mut MachFunction,
    ctx: &LowerCtx,
    op: AArch64Opcode,
    a: VReg,
    b: VReg,
    arr: bool,
) -> VReg {
    let d = alloc(func, RegClass::Fpr128);
    let mut operands = vec![vreg(d), vreg(a), vreg(b)];
    if arr {
        operands.push(imm(ARR_S4));
    }
    emit(func, ctx.vbody, op, operands);
    d
}

/// Materialize (once) a broadcast `4 x i32` constant vector in the preheader.
fn const_vec(func: &mut MachFunction, ctx: &mut LowerCtx, value: i64) -> VReg {
    if let Some(&v) = ctx.const_cache.get(&value) {
        return v;
    }
    let w = alloc(func, RegClass::Gpr32);
    let v = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        ctx.preheader_term,
        AArch64Opcode::Movz,
        vec![vreg(w), imm(value)],
    );
    emit_before(
        func,
        ctx.preheader_term,
        AArch64Opcode::NeonDupGen,
        vec![vreg(v), vreg(w), imm(ELEM_S)],
    );
    ctx.const_cache.insert(value, v);
    v
}

// ---------------------------------------------------------------------------
// Small local IR helpers (kept independent of neon_map.rs / neon_array.rs)
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

fn emit_before(
    func: &mut MachFunction,
    before: InstId,
    op: AArch64Opcode,
    operands: Vec<MachOperand>,
) -> InstId {
    let id = func.push_inst(MachInst::new(op, operands));
    insert_before_inst(func, before, &[id]);
    id
}

fn alloc(func: &mut MachFunction, class: RegClass) -> VReg {
    // Allocate a vreg id strictly greater than every id currently in use so we
    // never alias an existing value.
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

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    let mut map = HashMap::new();
    for (idx, inst) in func.insts.iter().enumerate() {
        if let Some(MachOperand::VReg(v)) = inst.operands.first()
            && inst.opcode.produces_value()
        {
            map.insert(v.id, InstId(idx as u32));
        }
    }
    map
}

fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    for (idx, block) in func.blocks.iter().enumerate() {
        if block.insts.contains(&target) {
            return Some(BlockId(idx as u32));
        }
    }
    None
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

fn rewrite_block_target(inst: &mut MachInst, old: BlockId, new: BlockId) -> bool {
    let mut changed = false;
    for op in &mut inst.operands {
        if matches!(op, MachOperand::Block(b) if *b == old) {
            *op = MachOperand::Block(new);
            changed = true;
        }
    }
    changed
}

fn remove_cfg_edge(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.block_mut(from).succs.retain(|&s| s != to);
    func.block_mut(to).preds.retain(|&p| p != from);
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

fn insert_before_inst(func: &mut MachFunction, before: InstId, new_insts: &[InstId]) -> bool {
    for block in &mut func.blocks {
        if let Some(pos) = block.insts.iter().position(|&id| id == before) {
            for (off, &id) in new_insts.iter().enumerate() {
                block.insts.insert(pos + off, id);
            }
            return true;
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::Signature;

    fn v(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }
    fn v64(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
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
    /// Assert the store path is fully PAIRED: `UNROLL/2` post-index `STP Q,Q,#32`
    /// and no leftover single `ST1` (UNROLL even) — byte-identical to `UNROLL`
    /// single ST1 stores (two 16-byte Q registers per pair = 32 bytes).
    fn assert_paired_stores(func: &MachFunction) {
        assert_eq!(
            count(func, AArch64Opcode::NeonStpQPost),
            UNROLL / 2,
            "expected UNROLL/2 paired STP stores"
        );
        assert_eq!(
            count(func, AArch64Opcode::NeonSt1Post),
            0,
            "no single ST1 stores remain (UNROLL even — all paired)"
        );
    }
    /// Count `NeonExtV` instructions with the given byte-shift immediate.
    fn count_ext_imm(func: &MachFunction, shift: i64) -> usize {
        func.blocks
            .iter()
            .flat_map(|blk| blk.insts.iter().copied())
            .map(|id| func.inst(id))
            .filter(|inst| {
                inst.opcode == AArch64Opcode::NeonExtV && imm_of(&inst.operands[3]) == Some(shift)
            })
            .count()
    }

    /// Build the rotated stencil loop `for i in [1,n-1): out[i] = TERM` in the
    /// exact shape `loop-latch-layout` emits (guard / header / latch).
    ///
    /// Register map: v0=base_out(store ptr), v1=base_a(load ptr),
    /// v2=base_b(load ptr), v3=n. v4=1(one/const), v40=4(es). iv=v6.
    ///
    /// `kind`: 0 => 3-point `out[i]=a[i-1]+a[i]+a[i+1]` (one read base, K=-1,0,+1);
    /// 1 => in-place `a[i]=a[i-1]+a[i+1]` (store base == read base — MUST BAIL);
    /// 2 => two-array `out[i]=a[i-1]+b[i+1]`; 3 => pure same-index map
    /// `out[i]=a[i]*2` (all K==0 — MUST BAIL, left to neon-map);
    /// 4 => 5-point `out[i]=a[i-2]+a[i-1]+a[i]+a[i+1]+a[i+2]` (three EXT-formed
    /// middles, exercising all three immediates); 5 => wide 3-point
    /// `out[i]=a[i-8]+a[i]+a[i+8]` (middle too far for EXT — keeps its load).
    fn build_stencil_loop(kind: u8) -> MachFunction {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let guard = func.create_block();
        let header = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();

        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        // store base for the in-place kind is base_a (v1), else base_out (v0).
        let store_base = if kind == 1 { 1u32 } else { 0u32 };
        // Preheader: base pointers + constants; iv=1 (lo).
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_out
        push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // base_a
        push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // base_b
        push(&mut func, bb0, Copy, vec![v(3), v(3)]); // n
        push(&mut func, bb0, Movz, vec![v(4), i(1)]); // const 1
        push(&mut func, bb0, Movz, vec![v(5), i(2)]); // const 2 (kind 3)
        push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // element size
        push(&mut func, bb0, SubRR, vec![v(41), v(3), v(4)]); // hi = n-1
        push(&mut func, bb0, MovR, vec![v(6), v(4)]); // iv = 1 (lo)
        push(&mut func, bb0, B, vec![b(guard)]);
        // Guard.
        push(&mut func, guard, CmpRR, vec![v(6), v(41)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        // Header: shifted indices + loads + term + store + step.
        let term_val: u32;
        match kind {
            4 | 5 => {
                // 4: 5-point out[i] = a[i-2]+a[i-1]+a[i]+a[i+1]+a[i+2]
                // 5: wide 3-point out[i] = a[i-8]+a[i]+a[i+8]
                let offs: &[i64] = if kind == 4 {
                    &[-2, -1, 0, 1, 2]
                } else {
                    &[-8, 0, 8]
                };
                // const 8 for the wide kind (1 and 2 exist as v4/v5).
                push(&mut func, bb0, Movz, vec![v(7), i(8)]);
                let cid = |c: i64| match c {
                    1 => 4u32,
                    2 => 5,
                    _ => 7,
                };
                let mut loads: Vec<u32> = Vec::new();
                for (r, &k) in offs.iter().enumerate() {
                    let r = r as u32;
                    let idx = if k == 0 {
                        6 // iv itself
                    } else {
                        let op = if k > 0 { AddRR } else { SubRR };
                        push(
                            &mut func,
                            header,
                            op,
                            vec![v(80 + r), v(6), v(cid(k.abs()))],
                        );
                        80 + r
                    };
                    push(&mut func, header, Sxtw, vec![v64(50 + 3 * r), v(idx)]);
                    push(
                        &mut func,
                        header,
                        Madd,
                        vec![v64(51 + 3 * r), v64(50 + 3 * r), v64(40), v64(1)],
                    );
                    push(
                        &mut func,
                        header,
                        LdrRI,
                        vec![v(52 + 3 * r), v64(51 + 3 * r), i(0)],
                    );
                    loads.push(52 + 3 * r);
                }
                let mut acc = loads[0];
                for (s, &l) in loads.iter().enumerate().skip(1) {
                    let s = s as u32;
                    push(&mut func, header, AddRR, vec![v(70 + s), v(acc), v(l)]);
                    acc = 70 + s;
                }
                term_val = acc;
            }
            3 => {
                // pure map out[i] = a[i]*2 (K=0 only).
                push(&mut func, header, Sxtw, vec![v64(20), v(6)]);
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(21), v64(20), v64(40), v64(1)],
                );
                push(&mut func, header, LdrRI, vec![v(22), v64(21), i(0)]); // a[i]
                push(&mut func, header, MulRR, vec![v(30), v(22), v(5)]); // a[i]*2
                term_val = 30;
            }
            2 => {
                // out[i] = a[i-1] + b[i+1]
                push(&mut func, header, SubRR, vec![v(10), v(6), v(4)]); // iv-1
                push(&mut func, header, AddRR, vec![v(11), v(6), v(4)]); // iv+1
                push(&mut func, header, Sxtw, vec![v64(20), v(10)]);
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(21), v64(20), v64(40), v64(1)],
                );
                push(&mut func, header, LdrRI, vec![v(22), v64(21), i(0)]); // a[i-1]
                push(&mut func, header, Sxtw, vec![v64(23), v(11)]);
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(24), v64(23), v64(40), v64(2)],
                );
                push(&mut func, header, LdrRI, vec![v(25), v64(24), i(0)]); // b[i+1]
                push(&mut func, header, AddRR, vec![v(30), v(22), v(25)]);
                term_val = 30;
            }
            _ => {
                // 3-point out[i] = a[i-1] + a[i] + a[i+1]  (kind 0 and in-place 1)
                push(&mut func, header, SubRR, vec![v(10), v(6), v(4)]); // iv-1
                push(&mut func, header, AddRR, vec![v(11), v(6), v(4)]); // iv+1
                push(&mut func, header, Sxtw, vec![v64(20), v(10)]);
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(21), v64(20), v64(40), v64(1)],
                );
                push(&mut func, header, LdrRI, vec![v(22), v64(21), i(0)]); // a[i-1]
                push(&mut func, header, Sxtw, vec![v64(23), v(6)]);
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(24), v64(23), v64(40), v64(1)],
                );
                push(&mut func, header, LdrRI, vec![v(25), v64(24), i(0)]); // a[i]
                push(&mut func, header, Sxtw, vec![v64(26), v(11)]);
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(27), v64(26), v64(40), v64(1)],
                );
                push(&mut func, header, LdrRI, vec![v(28), v64(27), i(0)]); // a[i+1]
                push(&mut func, header, AddRR, vec![v(29), v(22), v(25)]);
                push(&mut func, header, AddRR, vec![v(30), v(29), v(28)]);
                term_val = 30;
            }
        }
        // store address out[i] (K=0) and the store.
        push(&mut func, header, Sxtw, vec![v64(31), v(6)]);
        push(
            &mut func,
            header,
            Madd,
            vec![v64(32), v64(31), v64(40), v64(store_base)],
        );
        push(&mut func, header, StrRI, vec![v(term_val), v64(32), i(0)]);
        push(&mut func, header, AddRR, vec![v(33), v(6), v(4)]); // iv+1 (step)
        push(&mut func, header, B, vec![b(latch)]);
        push(&mut func, latch, AddRI, vec![v(6), v(33), i(0)]); // iv writeback
        push(&mut func, latch, CmpRR, vec![v(6), v(41)]);
        push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
        // Exit.
        push(&mut func, exit, Ret, vec![]);

        func.add_edge(bb0, guard);
        func.add_edge(guard, header);
        func.add_edge(guard, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
        func.next_vreg = 512;
        func
    }

    #[test]
    fn vectorizes_3point_stencil_when_noalias() {
        // out[i]=a[i-1]+a[i]+a[i+1]; out (v0) and a (v1) both noalias, distinct.
        let mut func = build_stencil_loop(0);
        func.noalias_params = vec![0, 1];
        let mut pass = NeonStencilPass::new();
        assert!(
            pass.run(&mut func),
            "3-point stencil (noalias) should vectorize"
        );
        assert_eq!(pass.fired(), 1);
        // Only the END streams (K=-1, K=+1) load: 2 streams * UNROLL/2 = 4 LDP;
        // the middle (K=0) is EXT-formed: UNROLL EXTs — sub-blocks 0..2 slide up
        // from K=-1 (#4 = 4*d, d=1), the last is addressed from K=+1
        // (#12 = 16-4*e, e=1). UNROLL ST1.
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            2 * UNROLL / 2,
            "4 LDP q,q"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonLd1Post),
            0,
            "LD1 replaced by LDP"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonExtV),
            UNROLL,
            "middle formed by 4 EXT"
        );
        assert_eq!(
            count_ext_imm(&func, 4),
            UNROLL - 1,
            "3x EXT #4 (slide up from K=-1)"
        );
        assert_eq!(
            count_ext_imm(&func, 12),
            1,
            "1x EXT #12 (last block from K=+1)"
        );
        assert_paired_stores(&func);
        assert!(
            count(&func, AArch64Opcode::NeonAddV) >= UNROLL,
            "vector adds"
        );
    }

    #[test]
    fn vectorizes_5point_stencil_forms_all_three_ext_imms() {
        // out[i]=a[i-2]+a[i-1]+a[i]+a[i+1]+a[i+2]; ends K=-2/K=+2 load, middles
        // K=-1 (d=1: #4,#4,#4 then e=3: #4), K=0 (d=2/e=2: #8 x4), K=+1
        // (d=3: #12 x3 then e=1: #12) are EXT-formed — every proven immediate.
        let mut func = build_stencil_loop(4);
        func.noalias_params = vec![0, 1];
        let mut pass = NeonStencilPass::new();
        assert!(
            pass.run(&mut func),
            "5-point stencil (noalias) should vectorize"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            2 * UNROLL / 2,
            "4 LDP q,q"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonExtV),
            3 * UNROLL,
            "3 middles x 4 EXT"
        );
        assert_eq!(
            count_ext_imm(&func, 4),
            UNROLL,
            "K=-1: all four windows shift #4"
        );
        assert_eq!(
            count_ext_imm(&func, 8),
            UNROLL,
            "K=0: all four windows shift #8"
        );
        assert_eq!(
            count_ext_imm(&func, 12),
            UNROLL,
            "K=+1: all four windows shift #12"
        );
        assert_paired_stores(&func);
    }

    #[test]
    fn wide_middle_stream_keeps_its_own_load_fail_closed() {
        // out[i]=a[i-8]+a[i]+a[i+8]: the middle K=0 is 8 lanes from either end —
        // no EXT immediate reaches it (only #4/#8/#12 are proven). It must keep
        // its own load stream (previous shape), NOT be mis-formed.
        let mut func = build_stencil_loop(5);
        func.noalias_params = vec![0, 1];
        let mut pass = NeonStencilPass::new();
        assert!(
            pass.run(&mut func),
            "wide 3-point stencil should still vectorize"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            3 * UNROLL / 2,
            "6 LDP q,q"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonExtV),
            0,
            "no EXT: middle too far"
        );
        assert_paired_stores(&func);
    }

    #[test]
    fn vectorizes_two_array_stencil_when_noalias() {
        // out[i]=a[i-1]+b[i+1]; out,a,b all noalias, distinct.
        let mut func = build_stencil_loop(2);
        func.noalias_params = vec![0, 1, 2];
        let mut pass = NeonStencilPass::new();
        assert!(
            pass.run(&mut func),
            "two-array stencil (noalias) should vectorize"
        );
        assert_eq!(pass.fired(), 1);
        // 2 single-offset bases (a@-1, b@+1): each is its own END stream — no
        // middles, no EXT, 2 streams * UNROLL/2 LDP; UNROLL ST1.
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL,
            "4 LDP q,q"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonExtV),
            0,
            "no middle streams: no EXT"
        );
        assert_paired_stores(&func);
    }

    #[test]
    fn bails_in_place_stencil() {
        // a[i]=a[i-1]+a[i+1] (store base == read base) is a loop-carried
        // dependency and MUST BAIL even with noalias on a.
        let mut func = build_stencil_loop(1);
        func.noalias_params = vec![0, 1, 2];
        let mut pass = NeonStencilPass::new();
        assert!(
            !pass.run(&mut func),
            "in-place stencil must BAIL (loop-carried dep)"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0, "no ST1");
    }

    #[test]
    fn bails_two_array_without_noalias() {
        // out[i]=a[i-1]+b[i+1] with a NOT noalias => could alias out => BAIL.
        let mut func = build_stencil_loop(2);
        func.noalias_params = vec![0, 2]; // out,b noalias but NOT a
        let mut pass = NeonStencilPass::new();
        assert!(!pass.run(&mut func), "read base not noalias must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0, "no ST1");
    }

    #[test]
    fn bails_when_store_base_not_noalias() {
        let mut func = build_stencil_loop(0);
        func.noalias_params = vec![1]; // a noalias but NOT out
        let mut pass = NeonStencilPass::new();
        assert!(!pass.run(&mut func), "store base not noalias must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0, "no ST1");
    }

    #[test]
    fn bails_with_no_noalias_params() {
        let mut func = build_stencil_loop(0);
        // noalias_params empty (default).
        let mut pass = NeonStencilPass::new();
        assert!(!pass.run(&mut func), "no noalias params must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0);
    }

    #[test]
    fn bails_pure_map_all_zero_offset() {
        // out[i]=a[i]*2 (all K==0) is a pure map — left to neon-map; stencil BAILS.
        let mut func = build_stencil_loop(3);
        func.noalias_params = vec![0, 1];
        let mut pass = NeonStencilPass::new();
        assert!(
            !pass.run(&mut func),
            "pure same-index map must BAIL (neon-map's job)"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0, "no ST1");
    }
}
