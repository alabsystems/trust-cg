// trust-cg-opt - SOUND NEON elementwise FP map/stencil/count vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON elementwise-FP vectorizer (`neon-fmap`)
//!
//! Vectorizes counted **elementwise floating-point** loops — the ONLY FP shapes
//! whose vectorization is reassociation-FREE — in two families:
//!
//! ```text
//! (MAP/STENCIL)  for i in [lo, hi):  out[i] = FTERM(a[i+k1], b[i+k2], ..., s, t, ...)
//! (COUNT-ABOVE)  for i in [lo, hi):  c += (a[i] >ogt t) ? 1 : 0     (INTEGER accumulate)
//! ```
//!
//! where `FTERM` is a tree of scalar `fadd`/`fsub`/`fmul`/`fdiv` over f32 or f64
//! array reads at small compile-time-constant offsets `i+K` and **loop-invariant**
//! FP scalars (constants, parameters, hoisted values — broadcast once with
//! `DUP Vd.<T>, Vn.<lane0>`), and the count family accumulates an **i32 counter**
//! (no FP accumulation at all: the lane compare `FCMGT` produces an all-ones/zero
//! mask and `acc -= mask` counts it, exactly clang's shape).
//!
//! ## Why the result is BIT-IDENTICAL to the scalar loop (the FP honesty argument)
//!
//! FP REDUCTIONS (`s += a[i]`) are NEVER touched here — vectorizing them
//! reassociates the sum and CHANGES results; they stay on the order-preserving
//! scalar path (`scalar_unroll` SERIAL mode). Elementwise FP is different in kind:
//! lane `i`'s result is exactly the scalar op-tree applied to lane `i`'s inputs —
//! no cross-lane arithmetic exists. Bit-identity then rests on one architectural
//! fact: **on AArch64 (A64), the NEON vector FP instructions `FADD/FSUB/FMUL/FDIV
//! .4S/.2D` compute, per lane, the SAME IEEE-754 operation as the scalar
//! `FADD/FSUB/FMUL/FDIV S/D form`, under the SAME FPCR** (RNE default; unlike
//! A32/NEON, A64 vector FP honors FPCR.FZ and does NOT force flush-to-zero, so
//! denormals, NaN payload propagation, signed zeros and infinities behave
//! identically scalar-vs-vector; trust-cg never writes FPCR, and neither does
//! clang without `-ffast-math`, so both run in the process-default environment).
//! NO CONTRACTION is performed: a scalar `fmul` + `fadd` pair is lowered to
//! `FMUL.<T>` + `FADD.<T>` (two roundings, exactly as the scalar loop rounds) —
//! NEVER fused into `FMLA` (one rounding), which would silently change bits.
//! Per-lane bit-identity incl. NaN/Inf/-0.0/denormal lanes is additionally pinned
//! by the differential fuzz battery (`fpmapfuzz.py`) with seeded special values.
//!
//! ## Why the transform is SOUND (memory)
//!
//! Purely additive like the sibling NEON passes: a `width`-wide (`UNROLL*vf`) main
//! vector loop is inserted in FRONT of the scalar loop, FOLLOWED by a `vf`-wide
//! VECTORIZED REMAINDER loop (one `.4S`/`.2D` per step), and the scalar loop —
//! left byte-for-byte unchanged — handles only the final `< vf` tail. The three
//! run in ascending index order (main chunk `[0,M)`, remainder `[M,M')`, scalar
//! `[M',n)`), each element exactly once, so only the two inserted loops need
//! justifying (and both share ONE argument, at widths `width` and `vf`):
//!
//! * **Bounds/OOB.** A loop admits an iteration only when `sext(iv) + (W-1) <
//!   sext(bound)` (`W = width` for the main loop, `vf` for the remainder; computed
//!   in i64 from the i32 induction and bound, so no overflow). Every lane index
//!   `l = iv..iv+W-1` is then an index the SCALAR loop also executes, so the store
//!   `out[l]` and every read `base[l+K]` (same base, same constant `K`) is an
//!   access the scalar program performs at `i = l` — each vector loop's access set
//!   is a SUBSET of the scalar loop's (the [`crate::neon_stencil`] halo argument,
//!   verbatim). The remainder loop is entered only from the main-loop exit, i.e.
//!   INSIDE any regime-C disjointness gate / i64 precheck (see `apply_map`).
//! * **Aliasing.** Regime (A) — single-array in-place same-index (`a[i]=f(a[i])`,
//!   the only pointer touched is the store base at offset 0): sound without any
//!   `noalias`, all lane loads are issued BEFORE any store of the chunk
//!   ([`crate::neon_map`]'s regime (A), verbatim). Regime (B) — anything else:
//!   the store base must be a trust_ir `noalias` param; every read stream must be
//!   either the store base itself AT OFFSET 0 (in-place same-index, e.g. saxpy's
//!   `y`) or a DISTINCT `noalias` param (any bounded offset). A shifted read of
//!   the STORE base (`out[i]=out[i-1]+…`) is a genuine loop-carried dependency
//!   and BAILS. The COUNT family performs NO store, so aliasing is irrelevant
//!   there (loads cannot conflict with loads) and no `noalias` is required.
//!
//! If ANY premise fails (i64 induction, an FP reduction / loop-carried FP value,
//! non-unit stride, an unrecognized op — including `fneg`/`fsqrt`/`fcvt`, calls,
//! atomics, a second store, offset too large, term class mismatch) the loop is
//! left ENTIRELY to the scalar path — fail-closed beats miscompile.
//!
//! ## Count-above lane math (both widths fold identically)
//!
//! `FCMGT` writes all-ones (`-1`) per true lane, so `acc_v -= mask` adds one per
//! true lane; lane counters are exact in 32 (f32 `.4S`) or 64 (f64 `.2D`) bits.
//! Because the i32 loop bound keeps `n < 2^31`, every per-lane count < 2^31, so a
//! `.2D` counter's HIGH 32 bits are always zero — the exit fold can therefore
//! combine accumulators with `.4S` adds and `UMOV.S`-extract all four 32-bit
//! lanes for BOTH widths (for `.2D` the odd `.S` lanes are the zero high halves):
//! no 32-bit lane can carry, and the extracted total is exact.
//!
//! Runs after [`crate::neon_stencil`] (integer stencils) and before
//! `reduction_split`. Disable with `TRUST_CG_DISABLE_PASSES=neon_fmap`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::effects::inst_defines_vreg;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Lanes per NEON iteration: f32 `.4S`.
const VF_F32: i64 = 4;
/// Lanes per NEON iteration: f64 `.2D`.
const VF_F64: i64 = 2;
/// INTEGER-op arrangement code for `.4S` (NeonAddV/NeonSubV/NeonSt1Post…).
const ARR_S4: i64 = 5;
/// INTEGER-op arrangement code for `.2D`.
const ARR_D2: i64 = 6;
/// FP-op arrangement code for `.4S` (NeonFaddV/…/NeonFcmgtV: 0=2S, 1=4S, 2=2D).
const FARR_S4: i64 = 1;
/// FP-op arrangement code for `.2D`.
const FARR_D2: i64 = 2;
/// NEON element-size operand code for `S` (32-bit) lanes (DUP/UMOV).
const ELEM_S: i64 = 4;
/// NEON element-size operand code for `D` (64-bit) lanes (DUP).
const ELEM_D: i64 = 8;
/// AArch64 condition code for signed less-than (`LT`).
const CC_LT: i64 = 11;
/// AArch64 condition code for signed greater-than (`GT`) — the `fcmp ogt` CSet
/// (FCMP of a NaN sets V, and GT requires `Z==0 && N==V`, so unordered => 0,
/// exactly the vector `FCMGT` NaN => 0 lane semantics).
const CC_GT: i64 = 12;
/// AArch64 condition code for equal (`EQ`) — the ROTATED forward header exit
/// `cmp iv+1, bound; b.eq exit` (clang -O1's `for(i=0;i<n;i++)` lowering).
const CC_EQ: i64 = 0;
/// AArch64 condition code for signed greater-or-equal (`GE`) — the alternate
/// rotated forward exit some layouts pick (`cmp iv+1, bound; b.ge exit`), AND
/// the rotated remainder-0 tail guard `iv >=s bound -> true exit` (skip the
/// do-while when the vector loop consumed all `n`, which would otherwise store
/// `out[n]` off the array end). SIGNED so a negative starting induction falls
/// into the scalar tail instead of comparing unsigned-huge.
const CC_GE: i64 = 10;
/// AArch64 condition code for unsigned lower-or-same (`LS`) — the regime (C)
/// runtime range-disjointness test (`a_end <=u x` or `x_end <=u a`; ADDRESSES,
/// correctly unsigned).
const CC_LS: i64 = 9;
/// Byte size of an `f32` element.
const ELEM_BYTES_F32: i64 = 4;
/// Byte size of an `f64` element.
const ELEM_BYTES_F64: i64 = 8;
/// Independent vector registers processed per vector iteration.
/// `UNROLL * VF` lanes per iteration (16 x f32 / 8 x f64 — 64 bytes).
/// MEASURED (M4, fixed-layout bench): 8 is uniformly worse (register
/// pressure — 3 streams x 8 blocks spill); 4 matches the sibling passes.
const UNROLL: usize = 4;
/// Largest permitted absolute stencil offset `|K|` (elements). Keeps `K*elem`
/// inside the ADD/SUB 12-bit immediate and the no-overflow argument airtight.
const MAX_OFFSET: i64 = 16;
/// Body schedule for the `EXT.16B` in-register window formation of middle
/// streams (the [`crate::neon_stencil`] *Window formation* scheme). The
/// 2-load-ends + EXT-derive-middle shape reads only the halo-exact byte range
/// `[iv-1, iv+width]` (128 B/iter for f32 vs 192 B for the 3-stream reload) —
/// the SAME access set the scalar loop performs, so the OOB/halo argument is
/// unchanged and bit-identity holds (EXT is a pure byte mover reading a SUBSET
/// of the loaded end streams' bytes). Selected at compile time by the trust-cg
/// process env `TRUST_CG_FSTENCIL_SCHED` (measure-first A/B); the LANDED default
/// is whichever schedule measured fastest on M4 (see `bench_fp.py` fstencil).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum StencilSched {
    /// All windows loaded (3-stream for stencil3); block-major arithmetic —
    /// each block's whole term tree (fadd..fdiv) emitted before the next
    /// block's. The historical default.
    Baseline,
    /// `Baseline` loads, but NODE-MAJOR ("transposed") arithmetic: each term
    /// node is emitted for ALL `UNROLL` blocks before the next node — clang's
    /// stencil order (all level-1 fadds, then all level-2, then all fdivs) so
    /// same-op work batches and the OoO core keeps the FP pipes saturated.
    BaselineT,
    /// 2-load ends + EXT-derive the middle window(s), permutes hoisted;
    /// block-major arithmetic.
    Ext,
    /// `Ext` loads with node-major (transposed) arithmetic.
    ExtT,
    /// `Ext`, but each block's EXTs are emitted immediately before that block's
    /// arithmetic (permute on the block's critical path — the naive port).
    ExtInterleave,
}

impl StencilSched {
    /// EXT-derive middle windows (2-load-ends) vs load every window (3-stream).
    fn ext(self) -> bool {
        matches!(
            self,
            StencilSched::Ext | StencilSched::ExtT | StencilSched::ExtInterleave
        )
    }
    /// Node-major ("transposed") arithmetic emission order.
    fn transposed(self) -> bool {
        matches!(self, StencilSched::BaselineT | StencilSched::ExtT)
    }
}

/// Resolve the map/stencil body schedule (once per `apply_map`). An explicit
/// `TRUST_CG_FSTENCIL_SCHED` env forces one schedule for ALL loops (measure-
/// first A/B forensics); unset selects the LANDED per-shape default.
///
/// LANDED DEFAULT (M4, `bench_fp.py`, best-of-15 interleaved): a STENCIL (a base
/// read at >= 2 distinct offsets — shifted windows) uses `ExtT` (2-load ends +
/// EXT-derived middles + node-major arithmetic), which TIES clang -O3
/// (fstencil32 1.38x -> 1.01x). A pure elementwise MAP (no shifted read) keeps
/// the block-major `Baseline` — node-major measured no better there and the
/// scope stays minimal (zero change to the fmap/saxpy path). NB: `Ext` WITHOUT
/// the transposed order is SLOWER than baseline (1.51x) — the two levers only
/// pay off together (block-major serializes each EXT on that block's critical
/// path; node-major batches all four EXTs for the OoO core to overlap).
fn stencil_sched(is_stencil: bool) -> StencilSched {
    match std::env::var("TRUST_CG_FSTENCIL_SCHED").ok().as_deref() {
        Some("ext_il") => StencilSched::ExtInterleave,
        Some("ext_t") => StencilSched::ExtT,
        Some("ext") | Some("1") => StencilSched::Ext,
        Some("base_t") | Some("bt") => StencilSched::BaselineT,
        Some("baseline") | Some("base") | Some("0") => StencilSched::Baseline,
        // LANDED DEFAULT (per-shape):
        _ if is_stencil => StencilSched::ExtT,
        _ => StencilSched::Baseline,
    }
}

/// The `neon-fmap` machine pass.
pub struct NeonFMapPass {
    /// Number of loops vectorized in the last run (diagnostics/tests).
    fired: usize,
    /// Emit ROTATED (bottom-tested) vector loops. Read ONCE from the environment
    /// at construction so the emission path never touches `std::env` — the
    /// decision is a plain field, which also lets tests exercise both shapes
    /// without racing on a process-global variable.
    rotate: bool,
}

impl Default for NeonFMapPass {
    fn default() -> Self {
        Self::new()
    }
}

impl NeonFMapPass {
    pub fn new() -> Self {
        Self {
            fired: 0,
            // Compile-time kill switch: `TCG_NO_FMAP_LOOP_ROTATE` (any value)
            // emits the legacy TOP-TESTED vector loops (`latch -> B header`).
            // With the switch set the object is byte-identical to the
            // pre-rotation compiler.
            rotate: std::env::var_os("TCG_NO_FMAP_LOOP_ROTATE").is_none(),
        }
    }

    /// Construct with an explicit loop-shape choice (tests / bisection).
    #[cfg(test)]
    pub(crate) fn with_rotate(rotate: bool) -> Self {
        Self { fired: 0, rotate }
    }

    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonFMapPass {
    fn name(&self) -> &str {
        "neon-fmap"
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

impl NeonFMapPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;

        // Recognize all candidate loops first; applying a plan only *adds*
        // blocks, so recognized data for other loops stays valid.
        let mut map_plans = Vec::new();
        let mut count_plans = Vec::new();
        for lp in loops.all_loops() {
            if let Some(rec) = RecognizedFMap::recognize(func, dom, lp.header, lp.latch, &lp.body) {
                map_plans.push(rec);
            } else if let Some(rec) =
                RecognizedFCount::recognize(func, dom, lp.header, lp.latch, &lp.body)
            {
                count_plans.push(rec);
            }
        }

        let mut changed = false;
        let rotate = self.rotate;
        for rec in map_plans {
            if apply_map(func, &rec, rotate) {
                self.fired += 1;
                changed = true;
            }
        }
        for rec in count_plans {
            if apply_count(func, &rec) {
                self.fired += 1;
                changed = true;
            }
        }
        if changed && std::env::var("TRUST_CG_DUMP_NEONFMAP").is_ok() {
            eprintln!("[neon-fmap] fn={} vectorized={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Shared recognition helpers
// ---------------------------------------------------------------------------

/// A distinct FP read stream: array `base` read at constant element offset `K`
/// (`base[i+K]`).
#[derive(Clone, Copy, PartialEq, Eq)]
struct Stream {
    base: VReg,
    k: i64,
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

/// 16-bit `Movz` constant value of `val`, if any.
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

/// If `v` is `Uxtw(n)` / `Sxtw(n)` (an i32->i64 widening), return the i32 source
/// `n`. Routes a MIXED (i32 element, i64-widened index/bound) ROTATED map through
/// the `.4S` path: clang's rotated form computes the widened bound `Uxtw(n)` in
/// the guard, but its i32 source `n` dominates and is what the apply re-`Sxtw`s.
/// Mirrors `neon_map::ext_source`.
fn ext_source(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<VReg> {
    let inst = func.inst(*def.get(&v.id)?);
    if matches!(inst.opcode, AArch64Opcode::Uxtw | AArch64Opcode::Sxtw) {
        vreg_of(&inst.operands[1])
    } else {
        None
    }
}

/// Recognize the ROTATED (clang -O1) FORWARD header exit test and return
/// `(bound, exit)`. The header must END with `CmpRR(iv+1, bound);
/// BCond(EQ|GE) -> <exit outside the loop body>` — clang's `for(i=0;i<n;i++)`
/// lowering (iv steps +1 from 0 so `iv+1` reaches `bound` exactly: the counted
/// trip `[0, bound)`). Adjacent CmpRR->BCond => sound flag dataflow. Fail-closed
/// on any deviation. Mirrors `neon_map::recognize_rotated_header_exit`.
fn recognize_rotated_header_exit(
    func: &MachFunction,
    header: BlockId,
    body: &HashSet<BlockId>,
    iv_src: VReg,
) -> Option<(VReg, BlockId)> {
    let insts = &func.block(header).insts;
    let p = insts.iter().position(|&id| {
        let i = func.inst(id);
        i.opcode == AArch64Opcode::BCond && branch_targets(i).iter().any(|t| !body.contains(t))
    })?;
    if p < 1 {
        return None;
    }
    let bcond = func.inst(insts[p]);
    let cc = imm_of(&bcond.operands[0])?;
    if cc != CC_EQ && cc != CC_GE {
        return None;
    }
    // The out-of-body target is the loop's true EXIT (where the scalar tail ends).
    let exit = *branch_targets(bcond).iter().find(|t| !body.contains(t))?;
    let cmp = func.inst(insts[p - 1]);
    if cmp.opcode != AArch64Opcode::CmpRR || vreg_of(&cmp.operands[0])? != iv_src {
        return None;
    }
    Some((vreg_of(&cmp.operands[1])?, exit))
}

/// True iff SOME def of `iv` lives in a block dominating `preheader` (the vector
/// loop is entered from `preheader`, so `iv` must be defined on that edge).
/// Mirrors `neon_map::iv_def_dominates_preheader`.
fn iv_def_dominates_preheader(
    func: &MachFunction,
    dom: &DomTree,
    iv: VReg,
    preheader: BlockId,
) -> bool {
    for &block_id in &func.block_order {
        if !dom.dominates(block_id, preheader) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            if inst_defines_vreg(func.inst(inst_id), iv) {
                return true;
            }
        }
    }
    false
}

/// The pieces every recognizer shares: the 2-block loop skeleton (guard /
/// preheader / exit compare) with an induction stepping by one. Handles BOTH the
/// NATIVE bottom-tested shape (exit `CmpRR(iv,bound); BCond(LT)` in the latch)
/// and the ROTATED forward shape (clang -O1 importer: latch is a pure writeback +
/// `B -> header`, exit `CmpRR(iv+1,bound); BCond(EQ|GE) -> exit` at the END of the
/// header). For the rotated shape the block model is RE-ROOTED onto the guard
/// (where clang inits `iv`) so `apply` reads a defined `iv` and can route the
/// vector exit into the do-while scalar tail behind a remainder-0 guard.
struct LoopSkeleton {
    guard: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    iv: VReg,
    bound: VReg,
    /// ROTATED FORWARD only: the loop's true EXIT block (out-of-body target of the
    /// header exit branch), for the remainder-0 tail guard. `None` for NATIVE.
    rotated_exit: Option<BlockId>,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// Latch loop-carried writebacks `(dst, src)` in latch order.
    writebacks: Vec<(VReg, VReg)>,
}

/// Recognize the loop skeleton shared by both families. `allowed` whitelists
/// every opcode permitted in the body (fail-closed on anything else).
fn recognize_skeleton(
    func: &MachFunction,
    dom: &DomTree,
    header: BlockId,
    latch: BlockId,
    body: &HashSet<BlockId>,
    allowed: fn(AArch64Opcode) -> bool,
) -> Option<LoopSkeleton> {
    // (R1) exactly a 2-block innermost loop {header, latch}.
    if header == latch || body.len() != 2 || !body.contains(&header) || !body.contains(&latch) {
        return None;
    }
    let mut loop_insts = HashSet::new();
    for &b in [header, latch].iter() {
        for &id in &func.block(b).insts {
            if !allowed(func.inst(id).opcode) {
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
    // The guard's pred count only constrains the NATIVE path (which redirects a
    // UNIQUE real-preheader edge — checked there). The ROTATED path re-roots onto
    // `guard` itself, so it is agnostic: ONE pred = a RUNTIME loop's zero-trip
    // `n>0` guard; ZERO = a CONSTANT / statically-nonzero-trip loop with no
    // guard (its header's external pred IS the entry preheader); MANY = a nested
    // inner loop's preheader (reached from several outer edges).
    let gpreds_len = func.block(guard).preds.len();
    let preheader = func.block(guard).preds.first().copied().unwrap_or(guard);
    let preheader_term = func
        .block(preheader)
        .insts
        .iter()
        .rev()
        .find(|&&id| branch_targets(func.inst(id)).contains(&guard))
        .copied();

    // Loop-carried writebacks in the latch (copy idioms), in latch order.
    let latch_insts = func.block(latch).insts.clone();
    let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
    for &id in &latch_insts {
        if let Some((d, s)) = copy_like(func.inst(id)) {
            writebacks.push((d, s));
        }
    }

    // (R2) exit test + shape. NATIVE = the exit branch lives in the LATCH; ROTATED
    // = the latch is a pure writeback + `B -> header` and the exit test is at the
    // END of the header.
    let latch_exit_bcond = latch_insts
        .iter()
        .map(|&id| func.inst(id))
        .find(|i| i.opcode == AArch64Opcode::BCond && branch_targets(i).contains(&header));

    let (vec_guard, vec_preheader, vec_preheader_term, iv, bound, rotated_exit) =
        if let Some(bcond) = latch_exit_bcond {
            // NATIVE: `CmpRR(iv, bound); BCond(LT) -> header` in the latch. Strict
            // i32 iv+bound (unchanged — the existing byte-identical native path).
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
            if iv.class != RegClass::Gpr32 || bound.class != RegClass::Gpr32 {
                return None;
            }
            // The NATIVE path redirects the UNIQUE real-preheader edge: require
            // exactly one guard pred and its branch into the guard.
            if gpreds_len != 1 {
                return None;
            }
            (guard, preheader, preheader_term?, iv, bound, None)
        } else {
            // ROTATED (clang -O1 importer): the latch is EXACTLY the writeback(s) +
            // a single `B -> header`.
            let non_copy: Vec<InstId> = latch_insts
                .iter()
                .copied()
                .filter(|&id| copy_like(func.inst(id)).is_none())
                .collect();
            if non_copy.len() != 1 || func.inst(non_copy[0]).opcode != AArch64Opcode::B {
                return None;
            }
            // The induction writeback: the dst incremented by its src.
            let (iv, iv_src) = writebacks
                .iter()
                .copied()
                .find(|&(d, s)| is_increment_by_one(func, &def, s, d))?;
            // The exit test lives at the end of the HEADER: `cmp iv+1, bound; b.eq`.
            let (bound, exit) = recognize_rotated_header_exit(func, header, body, iv_src)?;
            // A widened bound `Uxtw(n)`/`Sxtw(n)` is guard-defined — substitute its
            // dominating i32 source.
            let bound = ext_source(func, &def, bound).unwrap_or(bound);
            // Bound widths, three sub-shapes:
            //  * i32 bound + i32 iv           — the pure-i32 rotated loop;
            //  * i32 bound + i64-widened iv   — MIXED (clang widens the index; the
            //    i32 bound keeps `iv < 2^31`, so `sxtw(iv)` is the identity);
            //  * i64 bound + i64 iv           — the INLINED shape (clang computes
            //    the trip count in i64 inside an enclosing loop, e.g. dgefa's
            //    inlined daxpy `n-k-1`). `apply_map` lowers this with the proven
            //    `neon_map` i64 scheme: a signed `bound < width` precheck plus the
            //    UNSIGNED `iv <u bound-(width-1)` header guard (no sxtw, no
            //    overflow — see the wrap-freedom notes in `apply_map`).
            // Anything else BAILS.
            match (bound.class, iv.class) {
                (RegClass::Gpr32, RegClass::Gpr32)
                | (RegClass::Gpr32, RegClass::Gpr64)
                | (RegClass::Gpr64, RegClass::Gpr64) => {}
                _ => return None,
            }
            // RE-ROOT onto the guard (where iv is init'd): its `B -> header`.
            let reroot_term = *func
                .block(guard)
                .insts
                .iter()
                .rev()
                .find(|&&id| branch_targets(func.inst(id)).contains(&header))?;
            (header, guard, reroot_term, iv, bound, Some(exit))
        };

    // The bound must be loop-invariant and available in the (re-rooted) preheader.
    let bound_def = *def.get(&bound.id)?;
    let bound_block = block_of_inst(func, bound_def)?;
    if !dom.dominates(bound_block, vec_preheader) {
        return None;
    }

    // SOUNDNESS: the vector loop is entered from `vec_preheader`; `iv` must be
    // defined on that edge (rotated: init'd in the guard; native: in the real
    // preheader).
    if !iv_def_dominates_preheader(func, dom, iv, vec_preheader) {
        return None;
    }

    Some(LoopSkeleton {
        guard: vec_guard,
        preheader: vec_preheader,
        preheader_term: vec_preheader_term,
        iv,
        bound,
        rotated_exit,
        def,
        loop_insts,
        writebacks,
    })
}

/// Per-width lowering parameters, selected by the FP register class.
#[derive(Clone, Copy)]
struct Width {
    /// True for f64 (`.2D`).
    is_f64: bool,
    elem_bytes: i64,
    /// INTEGER-op arrangement code (`ARR_S4`/`ARR_D2`).
    arr: i64,
    /// FP-op arrangement code (`FARR_S4`/`FARR_D2`).
    farr: i64,
    /// DUP element-size code (`ELEM_S`/`ELEM_D`).
    elem_code: i64,
    /// Lanes per vector iteration (`UNROLL * vf`).
    width: i64,
}

impl Width {
    fn of_class(class: RegClass) -> Option<Width> {
        match class {
            RegClass::Fpr32 => Some(Width {
                is_f64: false,
                elem_bytes: ELEM_BYTES_F32,
                arr: ARR_S4,
                farr: FARR_S4,
                elem_code: ELEM_S,
                width: UNROLL as i64 * VF_F32,
            }),
            RegClass::Fpr64 => Some(Width {
                is_f64: true,
                elem_bytes: ELEM_BYTES_F64,
                arr: ARR_D2,
                farr: FARR_D2,
                elem_code: ELEM_D,
                width: UNROLL as i64 * VF_F64,
            }),
            _ => None,
        }
    }

    fn fpr_class(&self) -> RegClass {
        if self.is_f64 {
            RegClass::Fpr64
        } else {
            RegClass::Fpr32
        }
    }
}

/// Shared stream-address recognizer: `addr = Madd(idx64, elem, base)` where
/// `idx64 = Sxtw(j)` (defined in the loop) and `j` is `iv` (K = 0) or
/// `iv +/- K` (`AddRI`/`SubRI` immediate, or `AddRR`/`SubRR` with a 16-bit
/// `Movz` constant), `|K| <= MAX_OFFSET`, `base` loop-invariant. Returns
/// `(base, K)`.
#[allow(clippy::too_many_arguments)]
fn resolve_stream(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    preheader: BlockId,
    iv: VReg,
    elem_bytes: i64,
    addr: VReg,
) -> Option<Stream> {
    let madd = func.inst(*def.get(&addr.id)?);
    if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
        return None;
    }
    let f1 = vreg_of(&madd.operands[1])?;
    let f2 = vreg_of(&madd.operands[2])?;
    let base = vreg_of(&madd.operands[3])?;
    let es_ok = |factor: VReg| const_value(func, def, factor) == Some(elem_bytes);
    let idx = if es_ok(f2) {
        f1
    } else if es_ok(f1) {
        f2
    } else {
        return None;
    };

    // MIXED (ROTATED clang -O1): the i64 induction is used DIRECTLY as the address
    // index (no `Sxtw`), so `idx == iv` at element offset K=0. Only the K=0 direct
    // shape is admitted — the importer never emits an offset stencil on the i64
    // index, and a shifted i64 index would need its own overflow argument. The
    // NATIVE path always widens with `Sxtw(iv)` (Gpr32 iv != Gpr64 idx), so this
    // branch is reached ONLY by the Gpr64-iv mixed shape.
    if idx == iv && iv.class == RegClass::Gpr64 {
        let base_def = *def.get(&base.id)?;
        let base_block = block_of_inst(func, base_def)?;
        if !dom.dominates(base_block, preheader) {
            return None;
        }
        return Some(Stream { base, k: 0 });
    }

    // idx = Sxtw(j) inside the loop.
    let sxtw_id = *def.get(&idx.id)?;
    if !loop_insts.contains(&sxtw_id) {
        return None;
    }
    let sxtw = func.inst(sxtw_id);
    if sxtw.opcode != AArch64Opcode::Sxtw || sxtw.operands.len() != 2 {
        return None;
    }
    let j = vreg_of(&sxtw.operands[1])?;

    // j = iv (K=0) or iv +/- K.
    let k = if j == iv {
        0
    } else {
        let j_id = *def.get(&j.id)?;
        if !loop_insts.contains(&j_id) {
            return None;
        }
        let jinst = func.inst(j_id);
        let ops = &jinst.operands;
        match jinst.opcode {
            AArch64Opcode::AddRI if ops.len() == 3 && vreg_of(&ops[1]) == Some(iv) => {
                imm_of(&ops[2])?
            }
            AArch64Opcode::SubRI if ops.len() == 3 && vreg_of(&ops[1]) == Some(iv) => {
                -imm_of(&ops[2])?
            }
            AArch64Opcode::AddRR if ops.len() == 3 => {
                let a = vreg_of(&ops[1])?;
                let b = vreg_of(&ops[2])?;
                if a == iv {
                    const_value(func, def, b)?
                } else if b == iv {
                    const_value(func, def, a)?
                } else {
                    return None;
                }
            }
            AArch64Opcode::SubRR if ops.len() == 3 && vreg_of(&ops[1]) == Some(iv) => {
                -const_value(func, def, vreg_of(&ops[2])?)?
            }
            _ => return None,
        }
    };
    if k.abs() > MAX_OFFSET {
        return None;
    }

    // base loop-invariant: its def dominates the preheader.
    let base_def = *def.get(&base.id)?;
    let base_block = block_of_inst(func, base_def)?;
    if !dom.dominates(base_block, preheader) {
        return None;
    }
    Some(Stream { base, k })
}

/// True iff `val`'s def is OUTSIDE the loop, dominates the preheader, and is an
/// FP scalar of the loop's width — a broadcastable loop-invariant.
fn is_invariant_fp(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    preheader: BlockId,
    fpr_class: RegClass,
    val: VReg,
) -> bool {
    if val.class != fpr_class {
        return false;
    }
    let Some(&def_id) = def.get(&val.id) else {
        return false;
    };
    if loop_insts.contains(&def_id) {
        return false;
    }
    let Some(def_block) = block_of_inst(func, def_id) else {
        return false;
    };
    dom.dominates(def_block, preheader)
}

// ---------------------------------------------------------------------------
// Family 1: FP MAP / STENCIL (store loops)
// ---------------------------------------------------------------------------

/// Opcodes permitted in a MAP/STENCIL body. Anything else => BAIL (rules out a
/// second store, calls, atomics, FP compares/conversions/sqrt/neg, integer
/// arithmetic feeding the term, and any unmodeled effect).
fn allowed_map_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR
            | AddRI
            | SubRR
            | SubRI
            | Madd
            | Movz
            | MovR
            | Copy
            | CmpRR
            | CmpRI
            | BCond
            | B
            | Sxtw
            | LdrRI
            | StrRI
            | FaddRR
            | FsubRR
            | FmulRR
            | FdivRR
            | FmaddRR
    )
}

/// A fully validated, lane-wise-vectorizable FP map/stencil loop.
struct RecognizedFMap {
    guard: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    iv: VReg,
    bound: VReg,
    /// ROTATED FORWARD only: the loop's true EXIT block, for the remainder-0 tail
    /// guard `iv >= bound -> exit`. `None` for the NATIVE bottom-tested shape.
    rotated_exit: Option<BlockId>,
    /// The per-iteration stored FP value (the map term), SSA def in the loop.
    term: VReg,
    /// Per-width lowering parameters (f32 `.4S` / f64 `.2D`).
    w: Width,
    /// Loop-invariant base pointer of the store `out[i]` (offset 0 REQUIRED).
    store_base: VReg,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// Recognized load result vreg id -> index into `streams`.
    loads: HashMap<u32, usize>,
    /// Distinct `(base, K)` read streams, first-seen order.
    streams: Vec<Stream>,
    /// Loop-invariant FP scalar leaves (broadcast in the preheader),
    /// first-seen order; `invariant_ids` mirrors it for O(1) membership.
    invariants: Vec<VReg>,
    invariant_ids: HashSet<u32>,
    /// Regime (C) RUNTIME ALIAS VERSIONING. Set when the static `noalias` gate
    /// (regime B) is unprovable but the loop is a ROTATED forward map whose
    /// distinct K=0 input ranges can be proven disjoint from the store range at
    /// runtime — `apply` then emits a byte-range disjointness precheck that takes
    /// the vector loop ONLY when provably disjoint, else the untouched scalar loop
    /// (exactly clang's overlap-versioning). Sound independent of any producer
    /// `noalias` claim.
    needs_versioning: bool,
    /// Distinct input bases (`!= store_base`, all K=0) whose byte range
    /// `[x, x+n*elem)` must be proven disjoint from the store range
    /// `[a, a+n*elem)` at runtime. Empty unless `needs_versioning`.
    check_bases: Vec<VReg>,
}

impl RecognizedFMap {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        let sk = recognize_skeleton(func, dom, header, latch, body, allowed_map_op)?;

        // A map loop carries exactly ONE loop value: the induction.
        if sk.writebacks.len() != 1 {
            return None;
        }
        let (wb_dst, iv_src) = sk.writebacks[0];
        if wb_dst != sk.iv || !is_increment_by_one(func, &sk.def, iv_src, sk.iv) {
            return None;
        }

        // (R_store) EXACTLY ONE store — the output `out[i]`, offset 0.
        let mut stores: Vec<InstId> = sk
            .loop_insts
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
        let term = vreg_of(&store.operands[0])?;
        let store_addr = vreg_of(&store.operands[1])?;
        let w = Width::of_class(term.class)?; // f32/f64 selects the path; else BAIL

        let mut rec = RecognizedFMap {
            guard: sk.guard,
            preheader: sk.preheader,
            preheader_term: sk.preheader_term,
            iv: sk.iv,
            bound: sk.bound,
            rotated_exit: sk.rotated_exit,
            term,
            w,
            store_base: VReg::new(0, RegClass::Gpr64), // filled below
            def: sk.def,
            loop_insts: sk.loop_insts,
            loads: HashMap::new(),
            streams: Vec::new(),
            invariants: Vec::new(),
            invariant_ids: HashSet::new(),
            needs_versioning: false,
            check_bases: Vec::new(),
        };

        // Store address must be `out[i]` — offset EXACTLY 0 (the halo argument
        // needs the store inside the guarded lane range).
        let sstream = resolve_stream(
            func,
            dom,
            &rec.def,
            &rec.loop_insts,
            rec.preheader,
            rec.iv,
            w.elem_bytes,
            store_addr,
        )?;
        if sstream.k != 0 {
            return None;
        }
        rec.store_base = sstream.base;

        // (R_term) every reachable leaf is a recognized FP stream load or a
        // loop-invariant FP scalar; interior nodes are fadd/fsub/fmul/fdiv.
        let mut seen = HashSet::new();
        if !rec.node_ok(func, dom, term, &mut seen) {
            return None;
        }

        // Every LdrRI in the body must be a recognized term load — a load from
        // an unproven pointer (even a dead one) fails closed.
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

        // (R_alias) — regimes (A) single-array in-place / (B) static noalias /
        // (C) runtime versioning. See the module docs.
        let noalias: HashSet<u32> =
            if trust_cg_lower::guard_evidence::validator_guard_replay_authority_available()
                || cfg!(test)
            {
                func.noalias_params.iter().copied().collect()
            } else {
                HashSet::new()
            };
        let single_array_in_place = rec
            .streams
            .iter()
            .all(|s| s.base.id == rec.store_base.id && s.k == 0);
        if !single_array_in_place {
            // A SHIFTED read of the STORE base (`out[i] = out[i-1] + ...`) is a
            // genuine loop-carried dependency — BAIL in EVERY regime (a runtime
            // disjointness test cannot disprove a self-overlap).
            for s in &rec.streams {
                if s.base.id == rec.store_base.id && s.k != 0 {
                    return None;
                }
            }
            // Regime (B): STATIC noalias. The store base is a proven `noalias`
            // param and every distinct input base is another proven `noalias`
            // param (distinct restrict params name disjoint memory) or the store
            // base itself at offset 0 (in-place same-index read).
            let regime_b = noalias.contains(&rec.store_base.id)
                && rec
                    .streams
                    .iter()
                    .all(|s| s.base.id == rec.store_base.id || noalias.contains(&s.base.id));
            if !regime_b {
                // Regime (C): RUNTIME ALIAS VERSIONING. Restricted to the ROTATED
                // FORWARD importer shape (`rotated_exit` set) — the production path
                // clang guards with the same cmp/ccmp overlap check. The bound `n`
                // is a live, dominating i32 register giving the range length, and
                // `all_loads_recognized` above guarantees no foreign load escapes
                // the disjointness check. Each distinct input must be read at K=0:
                // its byte range is then EXACTLY `[x, x+n*elem)` (a shifted read
                // would slop past the range end, so it stays fail-closed). The
                // NATIVE hand-written shape keeps the regime-B contract (bails
                // without noalias) — byte-identical to HEAD.
                rec.rotated_exit?;
                let mut check_bases: Vec<VReg> = Vec::new();
                for s in &rec.streams {
                    if s.base.id == rec.store_base.id {
                        continue; // in-place read of the SAME array at the same index
                    }
                    if s.k != 0 {
                        return None; // offset input: range not exactly [x, x+n*elem)
                    }
                    if !check_bases.iter().any(|c| c.id == s.base.id) {
                        check_bases.push(s.base);
                    }
                }
                if check_bases.is_empty() {
                    return None; // nothing distinct to disambiguate — fail closed
                }
                rec.needs_versioning = true;
                rec.check_bases = check_bases;
            }
        }

        Some(rec)
    }

    /// Read-only feasibility check mirroring the lowering: every reachable node
    /// is a recognized FP stream load, a loop-invariant FP scalar, or
    /// fadd/fsub/fmul/fdiv over such. Populates `loads`/`streams`/`invariants`.
    fn node_ok(
        &mut self,
        func: &MachFunction,
        dom: &DomTree,
        val: VReg,
        seen: &mut HashSet<u32>,
    ) -> bool {
        if val.class != self.w.fpr_class() {
            return false; // integers (incl. the induction) are never FP leaves
        }
        if !seen.insert(val.id) {
            return true; // already validated on an earlier path
        }
        let Some(&def_id) = self.def.get(&val.id) else {
            return false;
        };
        if !self.loop_insts.contains(&def_id) {
            // Loop-invariant FP scalar leaf (const / param / hoisted value).
            if is_invariant_fp(
                func,
                dom,
                &self.def,
                &self.loop_insts,
                self.preheader,
                self.w.fpr_class(),
                val,
            ) {
                if self.invariant_ids.insert(val.id) {
                    self.invariants.push(val);
                }
                return true;
            }
            return false;
        }
        let inst = func.inst(def_id);
        let opcode = inst.opcode;
        use AArch64Opcode::*;
        if opcode == LdrRI {
            if inst.operands.len() != 3 || imm_of(&inst.operands[2]) != Some(0) {
                return false;
            }
            let Some(addr) = vreg_of(&inst.operands[1]) else {
                return false;
            };
            let Some(stream) = resolve_stream(
                func,
                dom,
                &self.def,
                &self.loop_insts,
                self.preheader,
                self.iv,
                self.w.elem_bytes,
                addr,
            ) else {
                return false;
            };
            let idx = match self.streams.iter().position(|s| *s == stream) {
                Some(i) => i,
                None => {
                    self.streams.push(stream);
                    self.streams.len() - 1
                }
            };
            self.loads.insert(val.id, idx);
            return true;
        }
        let ops = inst.operands.clone();
        match opcode {
            FaddRR | FsubRR | FmulRR | FdivRR if ops.len() == 3 => {
                let (Some(a), Some(b)) = (vreg_of(&ops[1]), vreg_of(&ops[2])) else {
                    return false;
                };
                self.node_ok(func, dom, a, seen) && self.node_ok(func, dom, b, seen)
            }
            // FMA `d = n*m + a` (`llvm.fmuladd`, clang -ffp-contract=on). The scalar
            // loop ALREADY performs this single fused rounding, so lowering it
            // per-lane to `NeonFmlaV` introduces NO NEW contraction — each lane is
            // the same single-rounding `n[l]*m[l] + a[l]` the scalar op computes.
            FmaddRR if ops.len() == 4 => {
                let (Some(n), Some(m), Some(a)) =
                    (vreg_of(&ops[1]), vreg_of(&ops[2]), vreg_of(&ops[3]))
                else {
                    return false;
                };
                self.node_ok(func, dom, n, seen)
                    && self.node_ok(func, dom, m, seen)
                    && self.node_ok(func, dom, a, seen)
            }
            _ => false,
        }
    }
}

/// Per-lowering context for the map family.
struct FLowerCtx {
    /// Sub-block index in `0..UNROLL` currently being lowered.
    accum: usize,
    vbody: BlockId,
    w: Width,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    loads: HashMap<u32, usize>,
    /// `(stream index, sub-block k)` -> the vector loaded for that sub-block.
    loaded: HashMap<(usize, usize), VReg>,
    /// Invariant vreg id -> its broadcast vector (preheader `DUP`).
    bcast: HashMap<u32, VReg>,
    /// Per-sub-block memo of already-lowered scalar values.
    memo: HashMap<u32, VReg>,
}

/// Plan the `EXT.16B` in-register window formation: map each MIDDLE stream's
/// index to `(d, e)` = `(K - k_min, k_max - K)` (elements) when its byte
/// shifts `d*elem` and `(VF-e)*elem` are BOTH proven/encodable `EXT`
/// immediates (`#4/#8/#12`): f32 (`elem` 4, VF 4) admits `d, e` in `1..=3`;
/// f64 (`elem` 8, VF 2) admits exactly `d == e == 1`. END streams and
/// non-qualifying middles are absent and keep their own load stream
/// (fail-closed to the all-streams-loaded shape).
fn plan_ext_windows(
    streams: &[Stream],
    w: Width,
    sched: StencilSched,
) -> HashMap<usize, (i64, i64)> {
    let mut derived = HashMap::new();
    if !sched.ext() || UNROLL < 2 {
        return derived;
    }
    let vf = w.width / UNROLL as i64;
    let ext_imm_ok = |bytes: i64| matches!(bytes, 4 | 8 | 12);
    // Per base: the lowest and highest constant offset K (the END streams).
    let mut ends: HashMap<u32, (i64, i64)> = HashMap::new();
    for s in streams {
        let e = ends.entry(s.base.id).or_insert((s.k, s.k));
        e.0 = e.0.min(s.k);
        e.1 = e.1.max(s.k);
    }
    for (sidx, s) in streams.iter().enumerate() {
        let (kmin, kmax) = ends[&s.base.id];
        if s.k == kmin || s.k == kmax {
            continue; // END stream: always loaded
        }
        let d = s.k - kmin;
        let e = kmax - s.k;
        if d >= 1 && e >= 1 && ext_imm_ok(d * w.elem_bytes) && ext_imm_ok((vf - e) * w.elem_bytes) {
            derived.insert(sidx, (d, e));
        }
    }
    derived
}

/// Emit sub-block `j`'s planned `EXT.16B` window permutes (from `emit_ext_block`
/// ops `(stream index, lo source, hi source, byte shift)`), recording each
/// result vector in `loaded` under `(stream index, j)` for the term lowering.
fn emit_ext_block(
    func: &mut MachFunction,
    vb: BlockId,
    ops: &[(usize, VReg, VReg, i64)],
    j: usize,
    loaded: &mut HashMap<(usize, usize), VReg>,
) {
    for &(sidx, lo_src, hi_src, shift) in ops {
        let dst = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonExtV,
            vec![vreg(dst), vreg(lo_src), vreg(hi_src), imm(shift)],
        );
        loaded.insert((sidx, j), dst);
    }
}

fn apply_map(func: &mut MachFunction, rec: &RecognizedFMap, rotate: bool) -> bool {
    let w = rec.w;

    // The INLINED rotated shape carries a genuinely-i64 bound (clang computes the
    // trip count in i64 inside an enclosing loop, e.g. dgefa's `n-k-1`). It takes
    // the proven `neon_map`/`neon_array` i64 scheme: a `pv` PRECHECK block (signed
    // `bound < width` -> scalar; else `main_bound = bound-(width-1)`, which cannot
    // wrap since `bound >= width >= 1`) and the UNSIGNED header guard
    // `iv <u main_bound` (iv steps `0, width, ...` and stays `<= bound`, all lanes
    // `< bound` — a SUBSET of the scalar do-while's indices `[0, bound)`).
    let i64b = rec.bound.class == RegClass::Gpr64;
    // Native NEON lane count of the width (`.4S` = 4 f32 / `.2D` = 2 f64). The
    // main loop processes `UNROLL * vf` lanes/iter; the VECTORIZED REMAINDER loop
    // below processes exactly ONE such lane block (`vf` lanes) per step.
    let vf = w.width / UNROLL as i64;

    // Regime (C) runtime alias-versioning blocks (empty unless `needs_versioning`):
    // a preamble `av[0]` (computes `n*elem` and the store range end) followed by
    // TWO check blocks per distinct input base (each a single unsigned compare +
    // branch). Created and spliced in FRONT of the vector loop.
    let av: Vec<BlockId> = if rec.needs_versioning {
        (0..1 + 2 * rec.check_bases.len())
            .map(|_| func.create_block())
            .collect()
    } else {
        Vec::new()
    };
    // i64-bound versioning: a GATE block in front of the av chain routing bounds
    // with any high bit (negative or >= 2^31) to the scalar loop, so the range
    // length `bound*elem` below cannot overflow (see the regime-C notes).
    let gate = (rec.needs_versioning && i64b).then(|| func.create_block());
    let pv = i64b.then(|| func.create_block());
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    // Vectorized-remainder loop {rh header, rb body, rl latch}: a NARROWER
    // (single `.4S`/`.2D`, `vf`-lane) copy of the main loop that consumes the
    // `< UNROLL*vf` tail the main loop leaves, before the scalar do-while. Same
    // per-lane ops/arrangement as one main sub-block => bit-identical; guarded so
    // every lane index stays `< bound` (a SUBSET of the scalar indices).
    let rh = func.create_block();
    let rb = func.create_block();
    let rl = func.create_block();
    let vx = func.create_block();
    let mut fresh: Vec<BlockId> = Vec::new();
    if let Some(gate) = gate {
        fresh.push(gate);
    }
    fresh.extend(av.iter().copied());
    if let Some(pv) = pv {
        fresh.push(pv);
    }
    fresh.extend([vh, vb, vl, rh, rb, rl, vx]);
    insert_new_blocks_before(func, rec.guard, &fresh);
    if let Some(pv) = pv {
        func.add_edge(pv, vh);
        func.add_edge(pv, rec.guard);
    }
    // ROTATED (default): each latch re-tests the header's guard and back-edges
    // STRAIGHT into the body, so a steady-state iteration costs one conditional
    // branch instead of an unconditional jump to the header plus the header's
    // own taken branch. The headers stay as the one-time zero-trip entry guards.
    func.add_edge(vh, vb);
    // Main-loop exit falls into the remainder header (NOT straight to vx).
    func.add_edge(vh, rh);
    func.add_edge(vb, vl);
    if rotate {
        func.add_edge(vl, vb);
        func.add_edge(vl, rh);
    } else {
        func.add_edge(vl, vh);
    }
    func.add_edge(rh, rb);
    func.add_edge(rh, vx);
    func.add_edge(rb, rl);
    if rotate {
        func.add_edge(rl, rb);
        func.add_edge(rl, vx);
    } else {
        func.add_edge(rl, rh);
    }
    // The vector loop's entry (after any versioning chain): the i64 precheck when
    // present, else the header guard directly.
    let vec_entry = pv.unwrap_or(vh);

    let pre = rec.preheader_term;

    // --- Preheader: element size, sign-extended bound (i32 path only — an i64
    // bound is used directly), invariant broadcasts.
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(w.elem_bytes)],
    );
    let nb64 = if i64b {
        rec.bound
    } else {
        let nb = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Sxtw,
            vec![vreg(nb), vreg(rec.bound)],
        );
        nb
    };

    // --- Regime (C): runtime range-disjointness precheck. For the store range
    // `[a, a+N)` (`N = n*elem` bytes) and each distinct input range `[x_i, x_i+N)`,
    // the pair `(a, x_i)` is DISJOINT iff `a+N <=u x_i` (store below input) OR
    // `x_i+N <=u a` (input below store) — clang's `a+n<=x || x+n<=a`. If EVERY pair
    // is disjoint the chain reaches the vector loop; the first pair that may overlap
    // branches to the (untouched) scalar loop `rec.guard`. Unsigned pointer compares
    // (`LS`), all i64. `N` cannot overflow i64: an i32 count sign-extended and
    // shifted stays `< 2^34`; an i64 count is GATED to `< 2^31` first (`LSR #31`
    // non-zero — negative or huge — routes to the scalar loop, the original
    // behavior), so the same `< 2^34` argument applies. When the ranges actually
    // overlap control routes to the scalar loop, so the vector body NEVER runs on
    // aliasing memory — sound independent of any `noalias` claim.
    if rec.needs_versioning {
        let sh = w.elem_bytes.trailing_zeros() as i64; // 4 -> 2, 8 -> 3
        let nbytes = alloc(func, RegClass::Gpr64);
        if let Some(gate) = gate {
            // i64 GATE: any high bit in the bound (negative or >= 2^31) routes to
            // the scalar loop — behavior unchanged (such bounds either never run
            // or are rejected by pv anyway), and afterwards `bound in [0, 2^31)`
            // so `bound*elem < 2^34` computes exactly.
            let hi = alloc(func, RegClass::Gpr64);
            emit(
                func,
                gate,
                AArch64Opcode::LsrRI,
                vec![vreg(hi), vreg(rec.bound), imm(31)],
            );
            emit(
                func,
                gate,
                AArch64Opcode::Cbnz,
                vec![vreg(hi), block(rec.guard)],
            );
            emit(func, gate, AArch64Opcode::B, vec![block(av[0])]);
            func.add_edge(gate, rec.guard);
            func.add_edge(gate, av[0]);
        }
        if i64b {
            emit(
                func,
                av[0],
                AArch64Opcode::LslRI,
                vec![vreg(nbytes), vreg(rec.bound), imm(sh)],
            );
        } else {
            let nb = alloc(func, RegClass::Gpr64);
            emit(
                func,
                av[0],
                AArch64Opcode::Sxtw,
                vec![vreg(nb), vreg(rec.bound)],
            );
            emit(
                func,
                av[0],
                AArch64Opcode::LslRI,
                vec![vreg(nbytes), vreg(nb), imm(sh)],
            );
        }
        let a_end = alloc(func, RegClass::Gpr64);
        emit(
            func,
            av[0],
            AArch64Opcode::AddRR,
            vec![vreg(a_end), vreg(rec.store_base), vreg(nbytes)],
        );
        emit(func, av[0], AArch64Opcode::B, vec![block(av[1])]);
        func.add_edge(av[0], av[1]);

        let n = rec.check_bases.len();
        for (i, base) in rec.check_bases.iter().enumerate() {
            let c1 = av[1 + 2 * i];
            let c2 = av[2 + 2 * i];
            // Passing EITHER sub-test proves THIS pair disjoint => next pair, or
            // (last pair) the vector loop entry.
            let ok = if i + 1 < n { av[3 + 2 * i] } else { vec_entry };
            // c1: `a_end <=u base` ?  b.ls ok ; else fall to c2.
            emit(
                func,
                c1,
                AArch64Opcode::CmpRR,
                vec![vreg(a_end), vreg(*base)],
            );
            emit(func, c1, AArch64Opcode::BCond, vec![imm(CC_LS), block(ok)]);
            emit(func, c1, AArch64Opcode::B, vec![block(c2)]);
            func.add_edge(c1, ok);
            func.add_edge(c1, c2);
            // c2: `base + N <=u a` ?  b.ls ok ; else may overlap => scalar loop.
            let x_end = alloc(func, RegClass::Gpr64);
            emit(
                func,
                c2,
                AArch64Opcode::AddRR,
                vec![vreg(x_end), vreg(*base), vreg(nbytes)],
            );
            emit(
                func,
                c2,
                AArch64Opcode::CmpRR,
                vec![vreg(x_end), vreg(rec.store_base)],
            );
            emit(func, c2, AArch64Opcode::BCond, vec![imm(CC_LS), block(ok)]);
            emit(func, c2, AArch64Opcode::B, vec![block(rec.guard)]);
            func.add_edge(c2, ok);
            func.add_edge(c2, rec.guard);
        }
    }
    let mut bcast: HashMap<u32, VReg> = HashMap::new();
    for inv in &rec.invariants {
        let v = alloc(func, RegClass::Fpr128);
        // DUP Vd.<T>, Vn.<Ts>[0] — broadcast lane 0 of the scalar FPR (S/D
        // registers alias lane 0 of the V register).
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonDupElem,
            vec![vreg(v), vreg(*inv), imm(0), imm(w.elem_code)],
        );
        bcast.insert(inv.id, v);
    }

    // The remainder header's UNSIGNED bound (i64 path only); the i32/native path
    // recomputes a signed `sxtw(iv)+(vf-1) < sxtw(bound)` guard per step instead.
    let mut main_bound_r: Option<VReg> = None;
    // The main loop's i64 unsigned bound `bound-(width-1)`, kept so BOTH the
    // header and the rotated latch can re-test against it (`None` on the
    // i32/native path, where each copy recomputes `sxtw(iv)+(width-1)`).
    let mut main_bound_m: Option<VReg> = None;

    if let Some(pv) = pv {
        // --- i64-bound PRECHECK + UNSIGNED header guard (the proven `neon_map`
        // i64 scheme). pv: `main_bound = bound - (width-1)`; SIGNED `bound <
        // width` routes to the scalar loop (covers bound <= 0 / negative — the
        // wrapped `main_bound` is dead on that path); else `bound >= width >= 1`
        // so `main_bound in [1, bound]` computes without wrap. vh: `iv <u
        // main_bound` admits only full in-bounds blocks: iv steps `0, width,
        // 2*width, ...` so every admitted block's last lane `iv+width-1 <=
        // main_bound-1+width-1 = bound-1` — a SUBSET of the scalar do-while's
        // indices `[0, bound)`. On exit `iv <= bound` exactly (final admitted iv
        // `<= bound-width`, plus one step).
        let main_bound = alloc(func, RegClass::Gpr64);
        emit(
            func,
            pv,
            AArch64Opcode::SubRI,
            vec![vreg(main_bound), vreg(rec.bound), imm(w.width - 1)],
        );
        // The REMAINDER guard's unsigned bound `bound - (vf-1)`; `bound >= width
        // >= vf` on this path (the `bound < width` precheck below routes smaller
        // bounds to the scalar loop), so `bound-(vf-1) in [1, bound]` — no wrap,
        // the same argument as `main_bound` (`vf-1 <= width-1`).
        let mbr = alloc(func, RegClass::Gpr64);
        emit(
            func,
            pv,
            AArch64Opcode::SubRI,
            vec![vreg(mbr), vreg(rec.bound), imm(vf - 1)],
        );
        main_bound_r = Some(mbr);
        emit(
            func,
            pv,
            AArch64Opcode::CmpRI,
            vec![vreg(rec.bound), imm(w.width)],
        );
        emit(
            func,
            pv,
            AArch64Opcode::BCond,
            vec![imm(CC_LT), block(rec.guard)],
        );
        emit(func, pv, AArch64Opcode::B, vec![block(vh)]);
        main_bound_m = Some(main_bound);

        // SIGNED `iv <s main_bound`: a NEGATIVE starting induction (e.g.
        // `for (i = -k; i < n; i++) y[i] = a*x[i]` over mid-array bases) must
        // ENTER the vector body (the running pointers are seeded from the real
        // `iv`, so it reads/writes exactly the scalar loop's addresses). As
        // unsigned (`LO`), a negative `iv` compared HUGE: the vector loop was
        // skipped AND the rotated exit guard then skipped the scalar tail too —
        // dropping every iteration (miscompile, caught by differential test).
        // No wrap: `bound ∈ [width, 2^63)` ⇒ `main_bound ∈ [1, 2^63)` and
        // `iv + width <= bound` on every admitted iteration.
    }
    // --- Vector header: the trip guard. i64 path: `iv <s main_bound`. Native
    // path: `sxtw(iv) + (width-1) < sxtw(bound)` (i64, no overflow) — enough for
    // a full `width`-lane block. Main loop done -> remainder header (NOT vx).
    emit_vec_trip_guard(func, vh, rec.iv, w.width, main_bound_m, nb64, vb, rh);

    // --- Window-formation plan (the [`crate::neon_stencil`] scheme, ported):
    // per base the END streams (lowest / highest `K`) get their own load
    // stream; a MIDDLE stream whose byte shifts land on the proven `EXT`
    // immediates `#4/#8/#12` is instead formed in-register from the loaded
    // ends (its bytes are a SUBSET of the end streams' — the OOB argument is
    // unchanged). Middles that do not fit keep their own load stream.
    // A STENCIL reads some base at >= 2 distinct offsets (shifted windows);
    // `rec.streams` holds distinct `(base, K)` pairs, so a base appearing in two
    // streams means two offsets. Only stencils take the new EXT/node-major
    // schedule (see `stencil_sched`); pure maps keep the block-major baseline.
    let mut base_counts: HashMap<u32, usize> = HashMap::new();
    for s in &rec.streams {
        *base_counts.entry(s.base.id).or_insert(0) += 1;
    }
    let is_stencil = base_counts.values().any(|&c| c >= 2);
    let sched = stencil_sched(is_stencil);
    let derived = plan_ext_windows(&rec.streams, w, sched);

    // --- Vector body: current index once (`sxtw(iv)`; an i64-bound loop's iv is
    // already the 64-bit index — used directly), then per LOADED stream a fresh
    // pointer `base + (si+K)*elem` walked with `UNROLL/2` post-index
    // `LDP Qt1, Qt2` pair loads (64 bytes per stream per iteration). ALL loads
    // are emitted BEFORE any store, so an in-place same-index map reads every
    // element before it is overwritten.
    let si = if i64b {
        rec.iv
    } else {
        let s = alloc(func, RegClass::Gpr64);
        emit(func, vb, AArch64Opcode::Sxtw, vec![vreg(s), vreg(rec.iv)]);
        s
    };
    let mut loaded: HashMap<(usize, usize), VReg> = HashMap::new();
    // `(base id, K)` -> stream index, for the EXT source lookups below.
    let stream_idx: HashMap<(u32, i64), usize> = rec
        .streams
        .iter()
        .enumerate()
        .map(|(i, s)| ((s.base.id, s.k), i))
        .collect();
    for (sidx, s) in rec.streams.iter().enumerate() {
        if derived.contains_key(&sidx) {
            continue; // formed in-register below — no load stream of its own
        }
        let p0 = alloc(func, RegClass::Gpr64);
        emit(
            func,
            vb,
            AArch64Opcode::Madd,
            vec![vreg(p0), vreg(si), vreg(c_es), vreg(s.base)],
        );
        // Fold the constant element offset K into the pointer (byte offset
        // K*elem, |K|*elem <= 128 — 12-bit immediate).
        let p = if s.k == 0 {
            p0
        } else {
            let p1 = alloc(func, RegClass::Gpr64);
            let (op, off) = if s.k > 0 {
                (AArch64Opcode::AddRI, s.k * w.elem_bytes)
            } else {
                (AArch64Opcode::SubRI, -s.k * w.elem_bytes)
            };
            emit(func, vb, op, vec![vreg(p1), vreg(p0), imm(off)]);
            p1
        };
        for pair in 0..UNROLL / 2 {
            let q0 = alloc(func, RegClass::Fpr128);
            let q1 = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vb,
                AArch64Opcode::NeonLdpQPost,
                vec![vreg(q0), vreg(q1), vreg(p), imm(32)],
            );
            loaded.insert((sidx, 2 * pair), q0);
            loaded.insert((sidx, 2 * pair + 1), q1);
        }
    }

    // --- Plan each derived MIDDLE stream's `EXT.16B` sliding windows over its
    // base's loaded END streams (EXT is a pure byte mover — bit-pattern-exact
    // for FP lanes; all loads are already emitted, so every load still precedes
    // every store). Sub-block `j < UNROLL-1` slides UP from the `k_min` stream
    // (`EXT(Vmin[j], Vmin[j+1], #d*elem)`); the LAST sub-block has no
    // `Vmin[UNROLL]` block and is addressed from the TOP stream instead
    // (`EXT(Vmax[UNROLL-2], Vmax[UNROLL-1], #(VF-e)*elem)`) — byte-exact per
    // the neon_stencil *Window formation* docs. Source vregs are the already
    // loaded END streams; only the EMISSION ORDER (all up-front for `Ext`, or
    // interleaved per block for `ExtInterleave`) varies below.
    let vf = w.width / UNROLL as i64;
    let mut ext_ops: Vec<Vec<(usize, VReg, VReg, i64)>> = vec![Vec::new(); UNROLL];
    for (sidx, s) in rec.streams.iter().enumerate() {
        let Some(&(d, e)) = derived.get(&sidx) else {
            continue;
        };
        let kmin_idx = stream_idx.get(&(s.base.id, s.k - d));
        let kmax_idx = stream_idx.get(&(s.base.id, s.k + e));
        for (j, block_ext_ops) in ext_ops.iter_mut().enumerate().take(UNROLL) {
            let (lo_src, hi_src, shift) = if j + 1 < UNROLL {
                (
                    kmin_idx.and_then(|&i| loaded.get(&(i, j))),
                    kmin_idx.and_then(|&i| loaded.get(&(i, j + 1))),
                    d * w.elem_bytes,
                )
            } else {
                (
                    kmax_idx.and_then(|&i| loaded.get(&(i, UNROLL - 2))),
                    kmax_idx.and_then(|&i| loaded.get(&(i, UNROLL - 1))),
                    (vf - e) * w.elem_bytes,
                )
            };
            // The END streams are always loaded (plan invariant); bail without
            // committing if that were ever violated.
            let (Some(&lo_src), Some(&hi_src)) = (lo_src, hi_src) else {
                return false;
            };
            block_ext_ops.push((sidx, lo_src, hi_src, shift));
        }
    }
    // Hoisted schedule: emit ALL window permutes ahead of the FADD chain so the
    // OoO core overlaps them (each block's EXTs are independent). The
    // interleaved schedule defers each block's EXTs to just before its term.
    if sched != StencilSched::ExtInterleave {
        for (j, block_ext_ops) in ext_ops.iter().enumerate().take(UNROLL) {
            emit_ext_block(func, vb, block_ext_ops, j, &mut loaded);
        }
    }

    // --- Separate post-index pointer for the output store.
    let sp = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vb,
        AArch64Opcode::Madd,
        vec![vreg(sp), vreg(si), vreg(c_es), vreg(rec.store_base)],
    );
    let mut ctx = FLowerCtx {
        accum: 0,
        vbody: vb,
        w,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        loads: rec.loads.clone(),
        loaded,
        // Cloned: the same preheader broadcasts feed the remainder loop below.
        bcast: bcast.clone(),
        memo: HashMap::new(),
    };
    // Lower every sub-block's term first, then store them in PAIRS with
    // post-index `STP Qk, Qk+1, [sp], #32` — one instruction per 32 bytes,
    // exactly clang's `stp q, q` stencil-store shape. Byte-identical to the
    // prior per-block `ST1 {V.4S/.2D}, [sp], #16` sequence: a full-width vector
    // term is a 16-byte Q register whatever the lane arrangement, so the paired
    // store writes the SAME 32 bytes in the SAME order to the SAME running
    // pointer (guard / pointer math unchanged). All loads were emitted above,
    // so every load still precedes every store (in-place read-before-overwrite
    // holds). Any odd trailing block (UNROLL not even) keeps a single ST1.
    let vterms: Vec<VReg> = if sched.transposed() {
        // Node-major arithmetic (all EXTs already hoisted for ExtT).
        match lower_fp_transposed(func, &mut ctx, rec.term, UNROLL) {
            Some(v) => v,
            None => return false,
        }
    } else {
        let mut vterms = Vec::with_capacity(UNROLL);
        for (k, block_ext_ops) in ext_ops.iter().enumerate().take(UNROLL) {
            // Interleaved schedule: emit block k's window permutes immediately
            // before lowering block k's term (permute on that block's critical
            // path). The hoisted schedule already emitted them all above.
            if sched == StencilSched::ExtInterleave {
                emit_ext_block(func, ctx.vbody, block_ext_ops, k, &mut ctx.loaded);
            }
            ctx.accum = k;
            ctx.memo.clear();
            let Some(vterm) = lower_fp(func, &mut ctx, rec.term) else {
                return false;
            };
            vterms.push(vterm);
        }
        vterms
    };
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
            vec![vreg(vterms[k]), vreg(sp), imm(w.arr)],
        );
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: advance the scalar induction by `width`, then (ROTATED)
    // re-test the header's guard and back-edge straight into the body.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(w.width)],
    );
    if rotate {
        emit_vec_trip_guard(func, vl, rec.iv, w.width, main_bound_m, nb64, vb, rh);
    } else {
        emit(func, vl, AArch64Opcode::B, vec![block(vh)]);
    }

    // --- VECTORIZED REMAINDER LOOP (rh/rb/rl): consume the `< UNROLL*vf` tail the
    // main loop leaves, `vf` lanes per step, before the scalar do-while. Each step
    // is exactly ONE main sub-block (single `.4S`/`.2D`), computing the SAME
    // per-lane `FADD/FSUB/FMUL/FDIV/FMLA.<T>` under the SAME arrangement, so the
    // result is bit-identical to both the main loop and the scalar path. Indices
    // are consumed in ascending order — main chunk `[0,M)`, remainder `[M,M')`,
    // scalar `[M',n)`, each element exactly once. SOUND in every regime: rh is
    // reached only from vh, i.e. INSIDE the regime-C disjointness gate / i64
    // precheck, all stream loads precede the store (in-place read-before-
    // overwrite), and the guard admits a `vf`-block only when `iv+vf-1 < bound`
    // (a SUBSET of the scalar loop's indices — the halo/OOB argument at width vf).
    if !emit_fmap_remainder(
        func,
        rec,
        w,
        vf,
        rh,
        rb,
        rl,
        vx,
        c_es,
        nb64,
        i64b,
        main_bound_r,
        &bcast,
        rotate,
    ) {
        return false;
    }

    // --- Vector exit: nothing to reduce. NATIVE: the scalar guard is a safe
    // top-test, so branch to it unconditionally. ROTATED: `rec.guard` is the
    // do-while HEADER (scalar tail), which STORES `out[iv]` before testing — safe
    // only while `iv < bound`. When the vector consumed ALL `n` (remainder 0),
    // `iv == bound`, so `iv >=u bound` branches to the true exit rather than
    // falling into the do-while (which would store `out[n]` and run off the array
    // end — the rotated-uninit-iv P0 class). For a remainder `> 0` (`iv < bound`)
    // control FALLS THROUGH to the scalar tail. i32/MIXED compares widened
    // (`sxtw`, both non-negative < 2^31); i64 compares the registers directly
    // (`iv <= bound` on every vx entry — see the pv scheme notes).
    if let Some(exit) = rec.rotated_exit {
        if i64b {
            emit(
                func,
                vx,
                AArch64Opcode::CmpRR,
                vec![vreg(rec.iv), vreg(rec.bound)],
            );
        } else {
            let gi_x = alloc(func, RegClass::Gpr64);
            emit(
                func,
                vx,
                AArch64Opcode::Sxtw,
                vec![vreg(gi_x), vreg(rec.iv)],
            );
            emit(func, vx, AArch64Opcode::CmpRR, vec![vreg(gi_x), vreg(nb64)]);
        }
        // SIGNED `>=s` (matches the fixed signed vh/rh guards; `iv >= 1` on
        // every vx entry, so signed == unsigned here — defense-in-depth for the
        // negative-start invariant).
        emit(
            func,
            vx,
            AArch64Opcode::BCond,
            vec![imm(CC_GE), block(exit)],
        );
        // fall through to `rec.guard` (the do-while scalar tail).
    } else {
        emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);
    }

    // --- COMMIT. When versioning, the preheader enters the runtime alias precheck
    // (the i64 gate when present, else `av[0]`) first; otherwise the vector entry
    // (i64 precheck / header) directly.
    let entry = if rec.needs_versioning {
        gate.unwrap_or(av[0])
    } else {
        vec_entry
    };
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.guard, entry) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.guard);
    func.add_edge(rec.preheader, entry);
    func.add_edge(vx, rec.guard);
    if let Some(exit) = rec.rotated_exit {
        func.add_edge(vx, exit);
    }

    true
}

/// Emit the VECTORIZED REMAINDER loop `{rh, rb, rl}` for a recognized FP map.
///
/// After the main `UNROLL*vf`-wide loop consumes `M = floor(n/W)*W` elements, this
/// narrower loop consumes the tail `vf` lanes (one `.4S`/`.2D`) per step until
/// `< vf` remain, which the scalar do-while then finishes. Each step is exactly
/// ONE main sub-block: every stream is loaded DIRECTLY as a single `vf`-lane Q
/// (no `EXT` window derivation — a `vf`-lane vector needs no unrolled neighbours),
/// the term is lowered by the SAME [`lower_fp`] (so the ops, arrangement `farr`,
/// and any `FMLA` fusion are identical to the main loop), and the result is stored
/// as a single Q. Per-lane bit-identity therefore rests on the SAME argument as
/// the main loop (per-lane `NEON FP == scalar FP` under the process-default FPCR).
///
/// GUARD. `rh` admits a block only when `iv + vf - 1 < bound`: on the i64 path the
/// overflow-free unsigned `iv <u main_bound_r` (`main_bound_r = bound-(vf-1)`,
/// computed in `pv` where `bound >= width >= vf`); on the i32/native path the
/// signed `sxtw(iv)+(vf-1) < sxtw(bound)` (both `< 2^31`). Either way every lane
/// index `l ∈ [iv, iv+vf)` satisfies `l < bound`, so the store `out[l]` and each
/// read `base[l+K]` is an access the scalar loop also performs — a SUBSET of the
/// scalar access set (the halo argument, verbatim, at width `vf`).
///
/// Returns `false` (fail-closed, leaving the fresh blocks dead) only if the term
/// re-lowering fails — impossible in practice, since the identical term already
/// lowered for the main loop.
#[allow(clippy::too_many_arguments)]
fn emit_fmap_remainder(
    func: &mut MachFunction,
    rec: &RecognizedFMap,
    w: Width,
    vf: i64,
    rh: BlockId,
    rb: BlockId,
    rl: BlockId,
    vx: BlockId,
    c_es: VReg,
    nb64: VReg,
    i64b: bool,
    main_bound_r: Option<VReg>,
    bcast: &HashMap<u32, VReg>,
    rotate: bool,
) -> bool {
    // --- rh: remainder header guard `iv + vf - 1 < bound` -> rb, else vx.
    // i64 path: unsigned `iv <u bound-(vf-1)` (no overflow, no sxtw). The
    // compare is SIGNED (matching the fixed vh guard; `iv >= 1` whenever rh
    // runs, so signed == unsigned here — kept signed for the negative-start
    // invariant's defense-in-depth). i32/native path: signed
    // `sxtw(iv)+(vf-1) < sxtw(bound)`.
    emit_vec_trip_guard(func, rh, rec.iv, vf, main_bound_r, nb64, rb, vx);

    // --- rb: the index (i64 iv is already the 64-bit index; i32 iv is widened).
    let si = if i64b {
        rec.iv
    } else {
        let s = alloc(func, RegClass::Gpr64);
        emit(func, rb, AArch64Opcode::Sxtw, vec![vreg(s), vreg(rec.iv)]);
        s
    };
    // Load EVERY stream directly as a single `vf`-lane Q (`LD1 {Vt.T}, [p], #16`;
    // the post-increment lands on a freshly recomputed pointer, so it is dead).
    // ALL loads precede the store below (in-place read-before-overwrite holds).
    let mut loaded: HashMap<(usize, usize), VReg> = HashMap::new();
    for (sidx, s) in rec.streams.iter().enumerate() {
        let p0 = alloc(func, RegClass::Gpr64);
        emit(
            func,
            rb,
            AArch64Opcode::Madd,
            vec![vreg(p0), vreg(si), vreg(c_es), vreg(s.base)],
        );
        // Fold the constant element offset K into the pointer (|K|*elem <= 128).
        let p = if s.k == 0 {
            p0
        } else {
            let p1 = alloc(func, RegClass::Gpr64);
            let (op, off) = if s.k > 0 {
                (AArch64Opcode::AddRI, s.k * w.elem_bytes)
            } else {
                (AArch64Opcode::SubRI, -s.k * w.elem_bytes)
            };
            emit(func, rb, op, vec![vreg(p1), vreg(p0), imm(off)]);
            p1
        };
        let q = alloc(func, RegClass::Fpr128);
        emit(
            func,
            rb,
            AArch64Opcode::NeonLd1Post,
            vec![vreg(q), vreg(p), imm(w.arr)],
        );
        loaded.insert((sidx, 0), q);
    }
    let mut ctx = FLowerCtx {
        accum: 0,
        vbody: rb,
        w,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        loads: rec.loads.clone(),
        loaded,
        bcast: bcast.clone(),
        memo: HashMap::new(),
    };
    let vterm = match lower_fp(func, &mut ctx, rec.term) {
        Some(v) => v,
        None => return false,
    };
    // Store the single `vf`-lane term (`ST1 {Vt.T}, [sp], #16`).
    let sp = alloc(func, RegClass::Gpr64);
    emit(
        func,
        rb,
        AArch64Opcode::Madd,
        vec![vreg(sp), vreg(si), vreg(c_es), vreg(rec.store_base)],
    );
    emit(
        func,
        rb,
        AArch64Opcode::NeonSt1Post,
        vec![vreg(vterm), vreg(sp), imm(w.arr)],
    );
    emit(func, rb, AArch64Opcode::B, vec![block(rl)]);

    // --- rl: advance the induction by `vf` (in place, like the main latch),
    // then (ROTATED) re-test rh's guard and back-edge straight into rb.
    emit(
        func,
        rl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(vf)],
    );
    if rotate {
        emit_vec_trip_guard(func, rl, rec.iv, vf, main_bound_r, nb64, rb, vx);
    } else {
        emit(func, rl, AArch64Opcode::B, vec![block(rh)]);
    }
    true
}

/// Lower one scalar FP term node for the current sub-block. NO CONTRACTION is
/// INTRODUCED: each scalar `FmulRR`/`FaddRR` becomes its own `FMUL.<T>`/`FADD.<T>`
/// (the scalar round-twice sequence, per lane) — never fused into an FMLA. A
/// scalar `FmaddRR` that was ALREADY fused in the source (`llvm.fmuladd`) is
/// carried to the fused per-lane `NeonFmlaV` — same single rounding, per lane.
fn lower_fp(func: &mut MachFunction, ctx: &mut FLowerCtx, val: VReg) -> Option<VReg> {
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
    }
    if let Some(&sidx) = ctx.loads.get(&val.id) {
        let v = *ctx.loaded.get(&(sidx, ctx.accum))?;
        ctx.memo.insert(val.id, v);
        return Some(v);
    }
    if let Some(&v) = ctx.bcast.get(&val.id) {
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
    // FMA `d = n*m + a`: copy the addend into a fresh Vd (FMLA is a tied
    // read-modify-write, and the addend vector may be reused), then
    // `FMLA Vd, Vn, Vm` — the SAME single rounding the scalar `FmaddRR` performs.
    if opcode == FmaddRR {
        let n_raw = vreg_of(&ops[1])?;
        let m_raw = vreg_of(&ops[2])?;
        // BY-ELEMENT fast path: when exactly ONE multiplicand is a broadcast
        // loop-invariant scalar (e.g. `da` in `y[i] += da*x[i]`), read it
        // straight from lane 0 of its own FPR via `FMLA Vd, Vstream, Vda.Ts[0]`
        // — no `DUP` broadcast, no dedicated broadcast register (the eager
        // preheader DUP for this invariant is then dead and DCE'd). The product
        // is COMMUTATIVE and the by-element lane broadcast is bit-identical to
        // the DUP broadcast, so the fused SINGLE rounding is unchanged. Falls
        // back to the DUP-broadcast `NeonFmlaV` when neither or BOTH
        // multiplicands are invariant (shapes the lane form does not cover).
        let lane_form = match (
            ctx.bcast.contains_key(&n_raw.id),
            ctx.bcast.contains_key(&m_raw.id),
        ) {
            (true, false) => Some((n_raw, m_raw)), // n = scalar da, m = stream
            (false, true) => Some((m_raw, n_raw)), // m = scalar da, n = stream
            _ => None,
        };
        if let Some((scalar_da, stream_raw)) = lane_form {
            let stream = lower_fp(func, ctx, stream_raw)?;
            let a = lower_fp(func, ctx, vreg_of(&ops[3])?)?;
            let d = alloc(func, RegClass::Fpr128);
            emit(func, ctx.vbody, NeonOrrV, vec![vreg(d), vreg(a), vreg(a)]);
            emit(
                func,
                ctx.vbody,
                NeonFmlaLaneV,
                vec![
                    vreg(d),
                    vreg(stream),
                    vreg(scalar_da),
                    imm(0),
                    imm(ctx.w.farr),
                ],
            );
            ctx.memo.insert(val.id, d);
            return Some(d);
        }
        let n = lower_fp(func, ctx, n_raw)?;
        let m = lower_fp(func, ctx, m_raw)?;
        let a = lower_fp(func, ctx, vreg_of(&ops[3])?)?;
        let d = alloc(func, RegClass::Fpr128);
        emit(func, ctx.vbody, NeonOrrV, vec![vreg(d), vreg(a), vreg(a)]);
        emit(
            func,
            ctx.vbody,
            NeonFmlaV,
            vec![vreg(d), vreg(n), vreg(m), imm(ctx.w.farr)],
        );
        ctx.memo.insert(val.id, d);
        return Some(d);
    }
    let nop = match opcode {
        FaddRR => NeonFaddV,
        FsubRR => NeonFsubV,
        FmulRR => NeonFmulV,
        FdivRR => NeonFdivV,
        _ => return None,
    };
    let a = lower_fp(func, ctx, vreg_of(&ops[1])?)?;
    let b = lower_fp(func, ctx, vreg_of(&ops[2])?)?;
    let d = alloc(func, RegClass::Fpr128);
    emit(
        func,
        ctx.vbody,
        nop,
        vec![vreg(d), vreg(a), vreg(b), imm(ctx.w.farr)],
    );
    ctx.memo.insert(val.id, d);
    Some(d)
}

/// Resolve a term leaf/node for sub-block `k` in the transposed lowering: a
/// recognized stream load (per-block vector), a broadcast invariant (block
/// independent), or a previously node-major-emitted interior node from `memo`.
fn resolve_block(
    ctx: &FLowerCtx,
    memo: &HashMap<(usize, u32), VReg>,
    id: u32,
    k: usize,
) -> Option<VReg> {
    if let Some(&sidx) = ctx.loads.get(&id) {
        return ctx.loaded.get(&(sidx, k)).copied();
    }
    if let Some(&v) = ctx.bcast.get(&id) {
        return Some(v);
    }
    memo.get(&(k, id)).copied()
}

/// Postorder (children-before-parent), de-duplicated list of the term's
/// INTERIOR op nodes (`fadd/fsub/fmul/fdiv`). Leaves (loads / invariants) are
/// resolved on demand and never listed. `None` on any unrecognized node —
/// mirrors `lower_fp`'s fail-closed contract exactly.
fn collect_term_nodes(
    func: &MachFunction,
    ctx: &FLowerCtx,
    val: VReg,
    seen: &mut HashSet<u32>,
    order: &mut Vec<u32>,
) -> Option<()> {
    if ctx.loads.contains_key(&val.id) || ctx.bcast.contains_key(&val.id) {
        return Some(()); // leaf
    }
    let &def_id = ctx.def.get(&val.id)?;
    if !ctx.loop_insts.contains(&def_id) {
        return None;
    }
    let inst = func.inst(def_id);
    let ops = inst.operands.clone();
    use AArch64Opcode::*;
    match inst.opcode {
        FaddRR | FsubRR | FmulRR | FdivRR if ops.len() == 3 => {
            collect_term_nodes(func, ctx, vreg_of(&ops[1])?, seen, order)?;
            collect_term_nodes(func, ctx, vreg_of(&ops[2])?, seen, order)?;
            if seen.insert(val.id) {
                order.push(val.id);
            }
            Some(())
        }
        FmaddRR if ops.len() == 4 => {
            collect_term_nodes(func, ctx, vreg_of(&ops[1])?, seen, order)?;
            collect_term_nodes(func, ctx, vreg_of(&ops[2])?, seen, order)?;
            collect_term_nodes(func, ctx, vreg_of(&ops[3])?, seen, order)?;
            if seen.insert(val.id) {
                order.push(val.id);
            }
            Some(())
        }
        _ => None,
    }
}

/// Node-major ("transposed") term lowering: emit each interior op node for ALL
/// `unroll` sub-blocks before the next node (children first). SAME per-lane op
/// and rounding as the block-major [`lower_fp`] — only the emission ORDER
/// differs, batching identical ops so the OoO core keeps the FP pipes saturated
/// (clang's stencil schedule: all level-1 fadds, then level-2, then fdivs).
/// Returns the per-block term vectors; `None` (fail-closed) on any unrecognized
/// node.
fn lower_fp_transposed(
    func: &mut MachFunction,
    ctx: &mut FLowerCtx,
    term: VReg,
    unroll: usize,
) -> Option<Vec<VReg>> {
    let mut order: Vec<u32> = Vec::new();
    let mut seen: HashSet<u32> = HashSet::new();
    collect_term_nodes(func, ctx, term, &mut seen, &mut order)?;

    // memo[(block, node vreg-id)] -> that node's lowered vector for the block.
    let mut memo: HashMap<(usize, u32), VReg> = HashMap::new();
    for &nid in &order {
        let &def_id = ctx.def.get(&nid)?;
        let inst = func.inst(def_id);
        let opcode = inst.opcode;
        let ops = inst.operands.clone();
        use AArch64Opcode::*;
        // FMA node: `d = n*m + a` per block via `ORR Vd,Va,Va; FMLA Vd,Vn,Vm`
        // (fused single rounding, matching the scalar `FmaddRR`).
        if opcode == FmaddRR {
            let n_v = vreg_of(&ops[1])?;
            let m_v = vreg_of(&ops[2])?;
            let a_id = vreg_of(&ops[3])?.id;
            // BY-ELEMENT fast path (the INTERLEAVED form): when exactly one
            // multiplicand is a broadcast loop-invariant scalar, every unrolled
            // block reads it from lane 0 of its own FPR via
            // `FMLA Vd_k, Vstream_k, Vda.Ts[0]` — no DUP broadcast register held
            // live across the whole interleave (the eager preheader DUP is then
            // dead and DCE'd). Bit-identical to the DUP-broadcast form. Falls
            // back to `NeonFmlaV` when neither or both multiplicands are invariant.
            let lane_form = match (
                ctx.bcast.contains_key(&n_v.id),
                ctx.bcast.contains_key(&m_v.id),
            ) {
                (true, false) => Some((n_v, m_v.id)), // n = scalar da, m = stream
                (false, true) => Some((m_v, n_v.id)), // m = scalar da, n = stream
                _ => None,
            };
            for k in 0..unroll {
                let a = resolve_block(ctx, &memo, a_id, k)?;
                let d = alloc(func, RegClass::Fpr128);
                emit(func, ctx.vbody, NeonOrrV, vec![vreg(d), vreg(a), vreg(a)]);
                if let Some((scalar_da, stream_id)) = lane_form {
                    let stream = resolve_block(ctx, &memo, stream_id, k)?;
                    emit(
                        func,
                        ctx.vbody,
                        NeonFmlaLaneV,
                        vec![
                            vreg(d),
                            vreg(stream),
                            vreg(scalar_da),
                            imm(0),
                            imm(ctx.w.farr),
                        ],
                    );
                } else {
                    let n = resolve_block(ctx, &memo, n_v.id, k)?;
                    let m = resolve_block(ctx, &memo, m_v.id, k)?;
                    emit(
                        func,
                        ctx.vbody,
                        NeonFmlaV,
                        vec![vreg(d), vreg(n), vreg(m), imm(ctx.w.farr)],
                    );
                }
                memo.insert((k, nid), d);
            }
            continue;
        }
        let nop = match opcode {
            FaddRR => NeonFaddV,
            FsubRR => NeonFsubV,
            FmulRR => NeonFmulV,
            FdivRR => NeonFdivV,
            _ => return None,
        };
        let a_id = vreg_of(&ops[1])?.id;
        let b_id = vreg_of(&ops[2])?.id;
        for k in 0..unroll {
            let a = resolve_block(ctx, &memo, a_id, k)?;
            let b = resolve_block(ctx, &memo, b_id, k)?;
            let d = alloc(func, RegClass::Fpr128);
            emit(
                func,
                ctx.vbody,
                nop,
                vec![vreg(d), vreg(a), vreg(b), imm(ctx.w.farr)],
            );
            memo.insert((k, nid), d);
        }
    }
    (0..unroll)
        .map(|k| resolve_block(ctx, &memo, term.id, k))
        .collect()
}

// ---------------------------------------------------------------------------
// Family 2: FP COUNT-ABOVE (integer accumulate — no FP accumulation)
// ---------------------------------------------------------------------------

/// Opcodes permitted in a COUNT body: the map set minus stores/FP-arith, plus
/// `Fcmp`/`CSet` (the scalar compare idiom).
fn allowed_count_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR
            | AddRI
            | Madd
            | Movz
            | MovR
            | Copy
            | CmpRR
            | CmpRI
            | BCond
            | B
            | Sxtw
            | LdrRI
            | Fcmp
            | CSet
    )
}

/// A fully validated count-above loop `c += (a[i] >ogt t) ? 1 : 0`.
struct RecognizedFCount {
    guard: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    iv: VReg,
    bound: VReg,
    /// The i32 loop-carried counter.
    acc: VReg,
    /// Per-width parameters of the COMPARED elements (f32/f64).
    w: Width,
    /// The compared array stream (offset 0).
    stream: Stream,
    /// The loop-invariant FP threshold (`Fcmp`'s rhs).
    threshold: VReg,
}

impl RecognizedFCount {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        let sk = recognize_skeleton(func, dom, header, latch, body, allowed_count_op)?;

        // The count family's `apply_count` emits NO remainder-0 tail guard, so a
        // ROTATED do-while tail would over-read `a[n]` and miscount when the vector
        // consumes all `n`. The importer's count-above shape is not the target of
        // this arc — keep count-above on the NATIVE (bottom-tested) shape only.
        if sk.rotated_exit.is_some() {
            return None;
        }

        // No store can exist (StrRI is not whitelisted), so aliasing is
        // irrelevant: the loop only reads memory.

        // Exactly TWO loop-carried writebacks: the induction and the counter.
        if sk.writebacks.len() != 2 {
            return None;
        }
        let (acc, acc_src) = {
            let (d0, s0) = sk.writebacks[0];
            let (d1, s1) = sk.writebacks[1];
            if d0 == sk.iv && is_increment_by_one(func, &sk.def, s0, sk.iv) {
                (d1, s1)
            } else if d1 == sk.iv && is_increment_by_one(func, &sk.def, s1, sk.iv) {
                (d0, s0)
            } else {
                return None;
            }
        };
        if acc.class != RegClass::Gpr32 {
            return None;
        }

        // acc_src = AddRR(acc, c) / AddRR(c, acc); c -> (through copies) CSet(GT).
        let add_id = *sk.def.get(&acc_src.id)?;
        if !sk.loop_insts.contains(&add_id) {
            return None;
        }
        let add = func.inst(add_id);
        if add.opcode != AArch64Opcode::AddRR || add.operands.len() != 3 {
            return None;
        }
        let a = vreg_of(&add.operands[1])?;
        let b = vreg_of(&add.operands[2])?;
        let c = if a == acc {
            b
        } else if b == acc {
            a
        } else {
            return None;
        };
        // Peel copy idioms (the CSet result is Gpr64, copied to Gpr32).
        let mut cur = c;
        let cset_inst = loop {
            let id = *sk.def.get(&cur.id)?;
            if !sk.loop_insts.contains(&id) {
                return None;
            }
            let inst = func.inst(id);
            if let Some((_, src)) = copy_like(inst) {
                cur = src;
                continue;
            }
            break inst.clone();
        };
        if cset_inst.opcode != AArch64Opcode::CSet || imm_of(&cset_inst.operands[1]) != Some(CC_GT)
        {
            return None; // only the `fcmp ogt` -> CSet(GT) count idiom
        }

        // Exactly ONE CSet and ONE Fcmp in the body, in the same block, with NO
        // other flag-writing instruction between them (whitelisted flag writers:
        // Fcmp, CmpRR, CmpRI).
        let mut fcmp_ids = sk
            .loop_insts
            .iter()
            .copied()
            .filter(|&id| func.inst(id).opcode == AArch64Opcode::Fcmp);
        let fcmp_id = fcmp_ids.next()?;
        if fcmp_ids.next().is_some() {
            return None;
        }
        let cset_count = sk
            .loop_insts
            .iter()
            .filter(|&&id| func.inst(id).opcode == AArch64Opcode::CSet)
            .count();
        if cset_count != 1 {
            return None;
        }
        let fcmp_block = block_of_inst(func, fcmp_id)?;
        let blk_insts = &func.block(fcmp_block).insts;
        let fcmp_pos = blk_insts.iter().position(|&id| id == fcmp_id)?;
        let cset_pos = blk_insts
            .iter()
            .position(|&id| func.inst(id).opcode == AArch64Opcode::CSet)?;
        if cset_pos <= fcmp_pos {
            return None;
        }
        for &id in &blk_insts[fcmp_pos + 1..cset_pos] {
            if matches!(
                func.inst(id).opcode,
                AArch64Opcode::Fcmp | AArch64Opcode::CmpRR | AArch64Opcode::CmpRI
            ) {
                return None; // an intervening flag write would re-bind the CSet
            }
        }

        // Fcmp(x, t): x = a recognized same-index FP load; t loop-invariant.
        let fcmp = func.inst(fcmp_id);
        if fcmp.operands.len() != 2 {
            return None;
        }
        let x = vreg_of(&fcmp.operands[0])?;
        let t = vreg_of(&fcmp.operands[1])?;
        let w = Width::of_class(x.class)?;
        if t.class != w.fpr_class() {
            return None;
        }
        let load_id = *sk.def.get(&x.id)?;
        if !sk.loop_insts.contains(&load_id) {
            return None;
        }
        let load = func.inst(load_id);
        if load.opcode != AArch64Opcode::LdrRI
            || load.operands.len() != 3
            || imm_of(&load.operands[2]) != Some(0)
        {
            return None;
        }
        let stream = resolve_stream(
            func,
            dom,
            &sk.def,
            &sk.loop_insts,
            sk.preheader,
            sk.iv,
            w.elem_bytes,
            vreg_of(&load.operands[1])?,
        )?;
        if stream.k != 0 {
            return None; // count reads at the induction index only
        }
        if !is_invariant_fp(
            func,
            dom,
            &sk.def,
            &sk.loop_insts,
            sk.preheader,
            w.fpr_class(),
            t,
        ) {
            return None;
        }

        Some(RecognizedFCount {
            guard: sk.guard,
            preheader: sk.preheader,
            preheader_term: sk.preheader_term,
            iv: sk.iv,
            bound: sk.bound,
            acc,
            w,
            stream,
            threshold: t,
        })
    }
}

fn apply_count(func: &mut MachFunction, rec: &RecognizedFCount) -> bool {
    let w = rec.w;

    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    insert_new_blocks_before(func, rec.guard, &[vh, vb, vl, vx]);
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: zeroed vector counters, element size, bound, threshold
    // broadcast.
    let vacc: Vec<VReg> = (0..UNROLL)
        .map(|_| {
            let a = alloc(func, RegClass::Fpr128);
            emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(a), imm(0)]);
            a
        })
        .collect();
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(w.elem_bytes)],
    );
    let nb64 = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Sxtw,
        vec![vreg(nb64), vreg(rec.bound)],
    );
    let tvec = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonDupElem,
        vec![vreg(tvec), vreg(rec.threshold), imm(0), imm(w.elem_code)],
    );

    // --- Vector header: the map guard, verbatim.
    let gi = alloc(func, RegClass::Gpr64);
    let gilast = alloc(func, RegClass::Gpr64);
    emit(func, vh, AArch64Opcode::Sxtw, vec![vreg(gi), vreg(rec.iv)]);
    emit(
        func,
        vh,
        AArch64Opcode::AddRI,
        vec![vreg(gilast), vreg(gi), imm(w.width - 1)],
    );
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(gilast), vreg(nb64)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LT), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Vector body: load the stream, per sub-block FCMGT mask then
    // `counter -= mask` (mask lanes are 0 / all-ones, so this adds one per true
    // lane, in the lane's own width — the proven integer SUB).
    let si = alloc(func, RegClass::Gpr64);
    emit(func, vb, AArch64Opcode::Sxtw, vec![vreg(si), vreg(rec.iv)]);
    let p = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vb,
        AArch64Opcode::Madd,
        vec![vreg(p), vreg(si), vreg(c_es), vreg(rec.stream.base)],
    );
    let mut xs: Vec<VReg> = Vec::new();
    for _pair in 0..UNROLL / 2 {
        let q0 = alloc(func, RegClass::Fpr128);
        let q1 = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonLdpQPost,
            vec![vreg(q0), vreg(q1), vreg(p), imm(32)],
        );
        xs.push(q0);
        xs.push(q1);
    }
    for (k, x) in xs.iter().enumerate() {
        let mask = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonFcmgtV,
            vec![vreg(mask), vreg(*x), vreg(tvec), imm(w.farr)],
        );
        emit(
            func,
            vb,
            AArch64Opcode::NeonSubV,
            vec![vreg(vacc[k]), vreg(vacc[k]), vreg(mask), imm(w.arr)],
        );
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(w.width)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector exit: combine counters and fold into the scalar counter.
    // Counts are < 2^31 (i32 bound), so `.2D` counters have ZERO high halves and
    // the `.4S` add/extract fold below is exact for BOTH widths (module docs).
    let mut level = vacc.clone();
    while level.len() > 1 {
        let mut next = Vec::new();
        let mut i = 0;
        while i + 1 < level.len() {
            let d = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vx,
                AArch64Opcode::NeonAddV,
                vec![vreg(d), vreg(level[i]), vreg(level[i + 1]), imm(ARR_S4)],
            );
            next.push(d);
            i += 2;
        }
        if i < level.len() {
            next.push(level[i]);
        }
        level = next;
    }
    let vsum = level[0];
    let lane_regs: Vec<VReg> = (0..VF_F32)
        .map(|lane| {
            let r = alloc(func, RegClass::Gpr32);
            emit(
                func,
                vx,
                AArch64Opcode::NeonUmovGen,
                vec![vreg(r), vreg(vsum), imm(lane), imm(ELEM_S)],
            );
            r
        })
        .collect();
    let s01 = alloc(func, RegClass::Gpr32);
    let s23 = alloc(func, RegClass::Gpr32);
    let ssum = alloc(func, RegClass::Gpr32);
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(s01), vreg(lane_regs[0]), vreg(lane_regs[1])],
    );
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(s23), vreg(lane_regs[2]), vreg(lane_regs[3])],
    );
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(ssum), vreg(s01), vreg(s23)],
    );
    // Fold INTO the counter (its initial value need not be zero); the scalar
    // tail continues from this seed.
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(rec.acc), vreg(rec.acc), vreg(ssum)],
    );
    emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);

    // --- COMMIT.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.guard, vh) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.guard);
    func.add_edge(rec.preheader, vh);
    func.add_edge(vx, rec.guard);

    true
}

// ---------------------------------------------------------------------------
// Small local IR helpers (kept independent of the sibling NEON passes)
// ---------------------------------------------------------------------------

/// Emit ONE copy of a vector loop's trip guard into `blk`: take `body` while a
/// full `width`-lane block still fits below `bound`, else leave for `exit`.
///
/// This is emitted TWICE per vector loop — once in the header (the one-time
/// zero-trip entry guard) and once at the END of the latch, after the induction
/// advance, as the rotated backedge test. Both copies are the SAME pure compare
/// over the SAME operands (`iv`, and either the precomputed unsigned i64
/// `main_bound` or the sign-extended `nb64`), with the SAME condition and the
/// SAME two targets, and each allocates its own scratch — so the latch copy is a
/// literal re-evaluation of the test the header would have performed on
/// re-entry. It redefines no live value and admits exactly the same iterations;
/// the header survives untouched, so zero-trip behavior is unchanged.
#[allow(clippy::too_many_arguments)]
fn emit_vec_trip_guard(
    func: &mut MachFunction,
    blk: BlockId,
    iv: VReg,
    width: i64,
    main_bound: Option<VReg>,
    nb64: VReg,
    body: BlockId,
    exit: BlockId,
) {
    if let Some(mb) = main_bound {
        // i64 scheme: `iv <s main_bound` where `main_bound = bound-(width-1)`
        // was computed once in the precheck block (which dominates both copies).
        emit(func, blk, AArch64Opcode::CmpRR, vec![vreg(iv), vreg(mb)]);
    } else {
        // i32/native scheme: signed `sxtw(iv) + (width-1) < sxtw(bound)`.
        let gi = alloc(func, RegClass::Gpr64);
        let gilast = alloc(func, RegClass::Gpr64);
        emit(func, blk, AArch64Opcode::Sxtw, vec![vreg(gi), vreg(iv)]);
        emit(
            func,
            blk,
            AArch64Opcode::AddRI,
            vec![vreg(gilast), vreg(gi), imm(width - 1)],
        );
        emit(
            func,
            blk,
            AArch64Opcode::CmpRR,
            vec![vreg(gilast), vreg(nb64)],
        );
    }
    emit(
        func,
        blk,
        AArch64Opcode::BCond,
        vec![imm(CC_LT), block(body)],
    );
    emit(func, blk, AArch64Opcode::B, vec![block(exit)]);
}

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
    crate::effects::build_reaching_def_map(func)
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

#[cfg(test)]
mod tests;
