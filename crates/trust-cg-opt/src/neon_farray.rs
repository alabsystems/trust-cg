// trust-cg-opt - SOUND NEON FP array-reduction vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON FP array-reduction vectorizer (`neon-farray`)
//!
//! A memory-bearing SIBLING of [`crate::neon_fpred`]: it vectorizes counted
//! **floating-point reduction** loops whose per-iteration term is a lane-wise
//! `f64` dataflow of **unit-stride array loads** and loop-invariant scalars:
//!
//! ```text
//! acc = 0.0;  for i in [i0, n):  acc += a[i] * b[i]     // fused dot
//! acc = 0.0;  for i in [i0, n):  acc += a[i]            // plain sum
//! ```
//!
//! It fuses [`crate::neon_array`]'s unit-stride load recognition (running
//! per-base pointer walked with post-index `LDP Qt1, Qt2, [p], #32` loads) with
//! [`crate::neon_fpred`]'s ORDERED SCALAR DRAIN (the bit-exactness linchpin — no
//! reassociation). The reduction root is either a PLAIN `FADD` (`acc += term`)
//! or the FUSED `FMADD` (`acc = fma(n, m, acc)` = `acc += n*m`, `llvm.fmuladd`).
//!
//! ## Why the result is BIT-IDENTICAL to the scalar loop
//!
//! FP addition is NOT associative, so a vector-lanes-then-horizontal-add
//! reduction changes the last bits (forbidden). This pass NEVER reassociates the
//! accumulation. It vectorizes ONLY the INDEPENDENT per-lane element computation
//! (the coalesced loads, and — for the PLAIN-fadd form — the per-lane `FMUL.2D`,
//! which is the SAME IEEE op per lane as the scalar `FMUL`), then folds the lane
//! results into the SINGLE scalar accumulator with ORDERED SCALAR reductions IN
//! ITERATION ORDER:
//!
//! * PLAIN form: `acc = acc + term_lane0; acc = acc + term_lane1; ...` (scalar
//!   `FADD`, extracting each lane with `NeonDupScalarD`).
//! * FUSED form: `acc = fma(n_lane0, m_lane0, acc); acc = fma(n_lane1, m_lane1,
//!   acc); ...` — the per-lane scalar `FMADD` keeps the multiply INSIDE the fma
//!   (single rounding preserved). Only the loads (and any pre-multiply lane-wise
//!   ops) are vectorized off the accumulator chain; the fused contract is NEVER
//!   split into `FMUL`+`FADD` (which would round twice and change bits).
//!
//! The fadds/fmadds into `acc` therefore happen in exactly the scalar sequence,
//! so NO reassociation occurs — bit-identical to trust-cg's scalar lowering.
//!
//! ## Why the transform is SOUND (memory / CFG)
//!
//! Purely additive, exactly like the sibling passes: a vector main loop is
//! spliced in FRONT of the scalar loop (left byte-for-byte unchanged, handles the
//! `< width` tail). The pass BAILS on any store / call / atomic (the loop is
//! PURE-READ, so there is no aliasing surface — regime-C runtime versioning is
//! unnecessary). Each vector load reads exactly the memory the scalar loop reads:
//! `a[i] = *(base + iv*es)`, `base` loop-invariant, walked by a running pointer
//! that advances `width*es` bytes per iteration in lockstep with `iv += width`
//! (`es = 8` for `f64` streams, `4` for `f32`-widen streams).
//! The bounds guard admits a vector iteration only while `iv < n - (width-1)`
//! (i64, no overflow), so every processed index is one the scalar loop also runs.
//! The ROTATED (clang) scalar tail is a do-while, so when the vector consumes ALL
//! `n` (remainder 0, `iv == n`) the drain branches to the true exit instead of
//! falling into the do-while (the remainder-0 hazard, see [`crate::neon_array`]).
//!
//! ## The `f32 -> f64` WIDENING dot (the fp-convert kernel)
//!
//! `sum += (double)a_f32[i] * (double)b_f32[i]` (`llvm.fmuladd` — the FUSED root)
//! is ALSO vectorized: each element leaf is `FcvtSD(dst_f64, LdrRI(f32, ...))` (an
//! `f32` unit-stride load fed to the exact `f32 -> f64` widen). The vector body
//! coalesces the `f32` loads (one `LDP Qt1, Qt2, [p], #32` = 8 `f32`) and widens
//! them with `FCVTL` (low half) / `FCVTL2` (high half) — each output lane an EXACT
//! per-lane `fpext` (`f32 -> f64` is lossless), halving the convert throughput vs
//! two scalar `FCVT`s per pair. The widened `.2D` vectors then feed the SAME
//! ORDERED SCALAR drain: because the fp-convert root is a FUSED `fmadd`, the drain
//! keeps the multiply FUSED per lane (`fma(a_lane, b_lane, acc)` — single rounding
//! preserved), so it is BIT-IDENTICAL to the scalar `FcvtSD`+`FMADD` loop (verified
//! bit-for-bit across FP specials). A base is either entirely `f64`-direct or
//! entirely `f32`-widen; mixing under one base ⇒ bail.
//!
//! ## Scope / fail-closed
//!
//! Recognizes the ROTATED single-block importer do-while over an `i64` induction.
//! BAILS (leaving the loop ENTIRELY to the scalar path) on: any store / call; a
//! non-unit stride; a non-`f64`/`f32`-widen leaf/intermediate; an accumulator read
//! by more than the reduction; or an extra live-out. Fail-closed beats miscompile.
//!
//! ## ASYMMETRIC DEFAULT (measured)
//!
//! * The `f32 -> f64` WIDENING recognition fires BY DEFAULT
//!   ([`NeonFArrayPass::widening_only`], the pipeline's default construction):
//!   the `FCVTL/FCVTL2` halved convert throughput is a real, bit-exact win
//!   (fp-convert dot ~1.1x).
//! * The NON-widening pure-`f64` recognition requires the FULL opt-in
//!   (`TRUST_CG_ENABLE_NEONFARRAY=1` ⇒ [`NeonFArrayPass::new`]): the
//!   ordered-drain ceiling is ~0% for `f64` reductions (the serial chain +
//!   mandatory lane-extract negate the coalesced-load win) and firing on the
//!   fused f64 ddot measurably REGRESSES ~5% by stealing the loop from
//!   scalar_unroll's extract-free unroll.
//!
//! Kill switch (disables BOTH modes): `TRUST_CG_DISABLE_PASSES=neonfarray`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Lanes per NEON `.2D` (f64) unit.
const VF: i64 = 2;
/// Independent 2-lane pairs unrolled per vector iteration (`width = VF*UNROLL`).
/// UNROLL is even so each base's loads pack into `UNROLL/2` `LDP Qt1, Qt2` pairs.
const UNROLL: i64 = 4;
/// FP-op arrangement code for `.2D` (NeonFmulV etc: 2 = 2D).
const FARR_D2: i64 = 2;
/// NEON element-size operand code for `D` (64-bit) lanes (DUP/INS/lane-extract).
const ELEM_D: i64 = 8;
/// Element size in bytes for an `f64` array (unit stride).
const ELEM_BYTES_F64: i64 = 8;
/// Element size in bytes for an `f32` array (unit stride) — the WIDENING path,
/// where each `f32` element is loaded then converted to `f64` via `FCVTL/FCVTL2`.
const ELEM_BYTES_F32: i64 = 4;
/// AArch64 condition code: signed less-than (`LT`) — the width precheck AND the
/// vector header guard (SIGNED so a negative starting induction runs the vector
/// body / scalar tail instead of comparing unsigned-huge — see the vh comments).
const CC_LT: i64 = 11;
/// AArch64 condition code: signed greater-or-equal (`GE`) — remainder-0 tail
/// guard (signed, matching the header guard).
const CC_GE: i64 = 10;
/// AArch64 condition code: equal (`EQ`).
const CC_EQ: i64 = 0;
/// AArch64 condition code: unsigned lower-or-same (`LS`) — the iota-fill runtime
/// range-disjointness test (`x_end <=u y` or `y_end <=u x`).
const CC_LS: i64 = 9;

// --- IOTA-FILL (`.4S`) path constants -------------------------------------
//
// The fp-convert FILL loop `x[j] = a + (float)j; y[j] = b + (float)j` (f32
// arrays, an int->float of the loop induction) is vectorized at `.4S`
// (4 x f32 lanes) — see [`RecognizedFill`].
/// Lanes per NEON `.4S` (f32) unit.
const VF_S: i64 = 4;
/// `.4S` pairs unrolled per vector iteration (`FILL_WIDTH = VF_S*UNROLL_S`).
/// `UNROLL_S = 2` so each stream's two `.4S` value vectors pack into ONE
/// `STP Qt1, Qt2, [p], #32` (`NeonStpQPost`) — the store sibling of the
/// reduction path's `LDP Qt1, Qt2`.
const UNROLL_S: i64 = 2;
/// f32 elements filled per vector iteration (8).
const FILL_WIDTH: i64 = VF_S * UNROLL_S;
/// FP-op arrangement code for `.4S` (NeonFaddV/NeonUcvtfV etc: 1 = 4S).
const FARR_S4: i64 = 1;
/// INTEGER-op arrangement code for `.4S` (NeonAddV on the i32 index vector: 5 = S4).
const IARR_S4: i64 = 5;
/// NEON element-size operand code for `S` (32-bit) lanes (DUP/INS/DUP-elem).
const ELEM_S: i64 = 4;

/// The `neon-farray` machine pass.
///
/// ASYMMETRIC DEFAULT (see the pipeline landing note): in the DEFAULT pipeline
/// config ([`Self::widening_only`]) the pass fires ONLY on loops containing at
/// least one `f32 -> f64` WIDENING leaf (the fp-convert kernel) — where the
/// `FCVTL/FCVTL2` halved convert throughput is a measured win (~1.1x) and the
/// result is bit-exact. NON-widening (pure-`f64`) reductions are recognized only
/// in FULL mode ([`Self::new`], opted in via `TRUST_CG_ENABLE_NEONFARRAY=1`):
/// measured on the fused f64 ddot, firing there REGRESSES ~5% by stealing the
/// loop from scalar_unroll's extract-free unroll.
pub struct NeonFArrayPass {
    fired: usize,
    /// `true` ⇒ ALSO recognize non-widening (pure-`f64`) reductions. `false`
    /// (the DEFAULT pipeline config) ⇒ only `f32 -> f64` widening loops fire.
    full: bool,
}

impl Default for NeonFArrayPass {
    /// The DEFAULT pipeline configuration: widening-only.
    fn default() -> Self {
        Self::widening_only()
    }
}

impl NeonFArrayPass {
    /// FULL mode: recognize widening AND non-widening (pure-`f64`) reductions.
    /// The pipeline uses this only under `TRUST_CG_ENABLE_NEONFARRAY=1`.
    pub fn new() -> Self {
        Self {
            fired: 0,
            full: true,
        }
    }
    /// WIDENING-ONLY mode (the pipeline DEFAULT): fire only on loops with at
    /// least one `f32 -> f64` widening leaf; bail on pure-`f64` reductions
    /// (leaving them to scalar_unroll's better extract-free unroll).
    pub fn widening_only() -> Self {
        Self {
            fired: 0,
            full: false,
        }
    }
    /// Loops vectorized in the last `run` (diagnostics/tests).
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonFArrayPass {
    fn name(&self) -> &str {
        "neon-farray"
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

impl NeonFArrayPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;

        let mut plans = Vec::new();
        let mut fill_plans = Vec::new();
        let def_map = build_def_map(func);
        for lp in loops.all_loops() {
            if let Some(rec) = Recognized::recognize(
                func, dom, &def_map, lp.header, lp.latch, &lp.body, self.full,
            ) {
                plans.push(rec);
            } else if let Some(rec) =
                RecognizedFill::recognize(func, dom, &def_map, lp.header, lp.latch, &lp.body)
            {
                fill_plans.push(rec);
            }
        }

        let mut changed = false;
        for rec in plans {
            if apply(func, &rec) {
                self.fired += 1;
                changed = true;
            }
        }
        for rec in fill_plans {
            if apply_fill(func, &rec) {
                self.fired += 1;
                changed = true;
            }
        }
        if changed && std::env::var("TRUST_CG_DUMP_NEONFARRAY").is_ok() {
            eprintln!("[neon-farray] fn={} vectorized={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// How the reduction root combines the accumulator with the per-iteration term.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Root {
    /// `acc_src = FADD(acc, term)` — the term is a lane-wise f64 dataflow that the
    /// vector body computes; the drain adds each lane into `acc` with scalar FADD.
    PlainFadd { term: VReg },
    /// `acc_src = FMADD(n, m, acc)` (= acc + n*m) — the fused dot. The vector body
    /// computes the two multiplicand vectors; the drain does scalar FMADD per lane
    /// (multiply stays fused — single rounding preserved).
    FusedFma { n: VReg, m: VReg, may_unfuse: bool },
}

/// A fully validated FP array-reduction loop.
struct Recognized {
    preheader_term: InstId,
    vec_guard: BlockId,
    preheader: BlockId,
    exit: BlockId,
    iv: VReg,
    acc: VReg,
    acc_src: VReg,
    root: Root,
    /// The loop bound register (`iv < bound`, i.e. the runtime `n`). Read directly
    /// in the preheader when `bound_const` is `None`.
    bound: VReg,
    /// A reconstructed compile-time bound (materialized fresh in the preheader);
    /// `None` ⇒ use the runtime `bound` register.
    bound_const: Option<i64>,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// Map from a recognized load's result vreg id to its (loop-invariant) base.
    loads: HashMap<u32, VReg>,
    /// Distinct base pointers referenced by the term's loads, in first-seen order.
    bases: Vec<VReg>,
    /// Ids of bases whose elements are `f32` and WIDEN to `f64` via `FCVTL/FCVTL2`
    /// (the `sum += (double)a[i]*(double)b[i]` fp-convert kernel). A base is either
    /// entirely `f64`-direct or entirely `f32`-widen; mixing under one base ⇒ bail.
    widen_bases: HashSet<u32>,
}

/// Opcodes permitted anywhere in the loop body. Anything else ⇒ BAIL (rules out
/// stores/calls/atomics and any unmodeled effect).
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        // FP compute (the term dataflow).
        FmulRR | FaddRR | FsubRR | FdivRR | FmaddRR | FnegRR
        // f32->f64 widening convert leaf (the fp-convert kernel; FcvtSD = FCVT Dd,Sn).
        | FcvtSD
        // memory loads + their address arithmetic.
        | LdrRI | Madd
        // induction step + bound materialization.
        | AddRR | AddRI | Movz | Movk
        // writebacks / copies.
        | MovR | Copy | FmovFprFpr
        // control.
        | CmpRR | CmpRI | BCond | B
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

fn copy_like(inst: &MachInst) -> Option<(VReg, VReg)> {
    match inst.opcode {
        AArch64Opcode::MovR | AArch64Opcode::Copy | AArch64Opcode::FmovFprFpr
            if inst.operands.len() == 2 =>
        {
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

fn movz_const(func: &MachFunction, def: &HashMap<u32, InstId>, val: VReg) -> Option<i64> {
    let inst = func.inst(*def.get(&val.id)?);
    if inst.opcode == AArch64Opcode::Movz
        && let Some(v) = inst.operands.get(1).and_then(imm_of)
        && inst.operands.len() == 2
    {
        return Some(v);
    }
    None
}

fn const_value(func: &MachFunction, def: &HashMap<u32, InstId>, val: VReg) -> Option<i64> {
    movz_const(func, def, val)
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
            (a == Some(iv) && b.and_then(|r| movz_const(func, def, r)) == Some(1))
                || (b == Some(iv) && a.and_then(|r| movz_const(func, def, r)) == Some(1))
        }
        _ => false,
    }
}

/// Recognize the ROTATED (clang) header exit test:
/// `CmpRR(iv+1, bound); BCond(EQ|GE) -> exit`. Returns `(bound_reg, exit, cmp)`.
fn recognize_rotated_header_exit(
    func: &MachFunction,
    header: BlockId,
    body: &HashSet<BlockId>,
    iv_src: VReg,
) -> Option<(VReg, BlockId, InstId)> {
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
    let exit = *branch_targets(bcond).iter().find(|t| !body.contains(t))?;
    let cmp_id = insts[p - 1];
    let cmp = func.inst(cmp_id);
    if cmp.opcode != AArch64Opcode::CmpRR {
        return None;
    }
    if vreg_of(&cmp.operands[0])? != iv_src {
        return None;
    }
    Some((vreg_of(&cmp.operands[1])?, exit, cmp_id))
}

impl Recognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
        full: bool,
    ) -> Option<Self> {
        // (R1) exactly a 2-block innermost loop {header, latch}.
        if header == latch || body.len() != 2 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // (R2) whitelist every opcode — no stores/calls/atomics/etc.
        let mut loop_insts = HashSet::new();
        for &b in [header, latch].iter() {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

        // `def` is supplied by the caller, built ONCE per recognition sweep.
        // Measured as ~99% of this pass's entire cost when it was rebuilt inside
        // every per-loop attempt.

        // (R3) header preds = {latch, guard}; re-root onto the guard (rotated).
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            return None;
        }
        let guard = *hpreds.iter().find(|&&b| b != latch)?;
        let preheader_term = *func
            .block(guard)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))?;

        // (R4) latch = exactly TWO copy_like writebacks + ONE `B -> header`.
        let latch_insts = func.block(latch).insts.clone();
        let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
        let mut non_copy: Vec<InstId> = Vec::new();
        for &id in &latch_insts {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                writebacks.push((d, s));
            } else {
                non_copy.push(id);
            }
        }
        if writebacks.len() != 2 {
            return None;
        }
        if non_copy.len() != 1
            || func.inst(non_copy[0]).opcode != AArch64Opcode::B
            || !branch_targets(func.inst(non_copy[0])).contains(&header)
        {
            return None;
        }

        // (R5) iv writeback = the +1 one; acc = the other (Fpr64).
        let iv_wb = writebacks
            .iter()
            .copied()
            .find(|(d, s)| is_increment_by_one(func, &def, *s, *d))?;
        let (iv, iv_src) = iv_wb;
        let (acc, acc_src) = {
            let other = writebacks.iter().find(|(d, _)| *d != iv)?;
            (other.0, other.1)
        };
        if acc == iv {
            return None;
        }
        if iv.class != RegClass::Gpr64 || acc.class != RegClass::Fpr64 {
            return None;
        }

        // (R6) rotated header exit test + the loop bound. Array reductions have a
        // RUNTIME bound (`n`, a parameter): accept the bound REGISTER when it is
        // loop-invariant (its def dominates the guard/preheader, or it is a
        // function live-in with no def), else fall back to a reconstructed constant.
        let (bound_raw, exit, cmp_id) = recognize_rotated_header_exit(func, header, body, iv_src)?;
        if bound_raw.class != RegClass::Gpr64 {
            return None;
        }
        let bound_const = crate::reaching_const::unique_reaching_const(func, cmp_id, bound_raw)
            .filter(|k| (1..=i32::MAX as i64).contains(k));
        if bound_const.is_none() {
            // Runtime bound: must be readable in the preheader (guard). A live-in
            // (param) has no def and is available everywhere; an in-loop-written,
            // non-constant bound is unmodeled ⇒ bail.
            if let Some(&bdef) = def.get(&bound_raw.id) {
                let bblock = block_of_inst(func, bdef)?;
                if !dom.dominates(bblock, guard) {
                    return None;
                }
            }
        }

        // (R7) reduction root: PLAIN `FADD(acc, term)` or FUSED `FMADD(n, m, acc)`.
        let acc_reducer = *def.get(&acc_src.id)?;
        let acc_def = func.inst(acc_reducer);
        let root = match acc_def.opcode {
            AArch64Opcode::FaddRR => {
                let x = vreg_of(&acc_def.operands[1])?;
                let y = vreg_of(&acc_def.operands[2])?;
                let term = if x == acc {
                    y
                } else if y == acc {
                    x
                } else {
                    return None;
                };
                if term == acc {
                    return None;
                }
                Root::PlainFadd { term }
            }
            AArch64Opcode::FmaddRR if acc_def.operands.len() == 4 => {
                // d = a + n*m; the addend `a` must be the accumulator.
                let n = vreg_of(&acc_def.operands[1])?;
                let m = vreg_of(&acc_def.operands[2])?;
                let a = vreg_of(&acc_def.operands[3])?;
                if a != acc || n == acc || m == acc {
                    return None;
                }
                Root::FusedFma {
                    n,
                    m,
                    may_unfuse: acc_def.flags.contains(InstFlags::FMULADD_MAY_UNFUSE),
                }
            }
            _ => return None,
        };

        // (R8) acc read ONLY by the reduction inst inside the loop.
        for &id in loop_insts.iter() {
            if id == acc_reducer {
                continue;
            }
            for op in func.inst(id).operands.iter().skip(1) {
                if vreg_of(op) == Some(acc) {
                    return None;
                }
            }
        }

        let mut rec = Recognized {
            preheader_term,
            vec_guard: header,
            preheader: guard,
            exit,
            iv,
            acc,
            acc_src,
            root,
            bound: bound_raw,
            bound_const,
            // Cloned only on a SUCCESSFUL recognition, which is rare; the cost
            // that mattered was rebuilding on every ATTEMPT.
            def: def.clone(),
            loop_insts,
            loads: HashMap::new(),
            bases: Vec::new(),
            widen_bases: HashSet::new(),
        };

        // (R9) term dataflow must be lowerable per-lane: register-only f64 dataflow
        // of unit-stride f64 loads + loop-invariant f64 leaves. Also records the
        // recognized loads / bases.
        let roots: Vec<VReg> = match rec.root {
            Root::PlainFadd { term } => vec![term],
            Root::FusedFma { n, m, .. } => vec![n, m],
        };
        let mut seen = HashSet::new();
        for r in roots {
            if !rec.node_ok(func, dom, r, &mut seen) {
                return None;
            }
        }
        // Require at least one load: pure-register reductions belong to neon_fpred.
        if rec.bases.is_empty() {
            return None;
        }

        // (R9b) ASYMMETRIC DEFAULT GATE: in the default pipeline config
        // (`full == false`) only loops containing at least one `f32 -> f64`
        // WIDENING leaf fire — the FCVTL/FCVTL2 halved convert throughput is the
        // measured win (fp-convert ~1.1x, bit-exact). Pure-`f64` reductions BAIL
        // here (measured: firing on the fused f64 ddot regresses ~5% by stealing
        // the loop from scalar_unroll's extract-free unroll); recognizing them
        // requires the full opt-in (`TRUST_CG_ENABLE_NEONFARRAY=1`).
        if !full && rec.widen_bases.is_empty() {
            return None;
        }

        // (R10) no live-outs other than {iv, iv_src, acc, acc_src}.
        let allowed_liveout: HashSet<u32> =
            [iv.id, iv_src.id, acc.id, acc_src.id].into_iter().collect();
        let body_defs = collect_body_defs(func, &rec.loop_insts);
        for (bidx, block) in func.blocks.iter().enumerate() {
            let bid = BlockId(bidx as u32);
            if body.contains(&bid) {
                continue;
            }
            for &id in &block.insts {
                for op in &func.inst(id).operands {
                    if let Some(v) = vreg_of(op)
                        && body_defs.contains(&v.id)
                        && !allowed_liveout.contains(&v.id)
                    {
                        return None;
                    }
                }
            }
        }

        Some(rec)
    }

    /// Read-only feasibility mirroring [`lower`]: every reachable node is a
    /// unit-stride f64 load, a loop-invariant f64, or an allowed lane-wise f64 op
    /// over such. Records recognized loads/bases.
    fn node_ok(
        &mut self,
        func: &MachFunction,
        dom: &DomTree,
        val: VReg,
        seen: &mut HashSet<u32>,
    ) -> bool {
        if val.class != RegClass::Fpr64 {
            return false; // f32/f16 leaves & intermediates bail (only .2D f64)
        }
        if !seen.insert(val.id) {
            return true;
        }
        let Some(&def_id) = self.def.get(&val.id) else {
            return false;
        };
        if !self.loop_insts.contains(&def_id) {
            // Defined OUTSIDE the loop ⇒ a loop-invariant f64 leaf (broadcast once).
            return true;
        }
        // A recognized unit-stride f64 load leaf?
        if let Some(base) = self.load_base(func, dom, val) {
            if !self.loads.contains_key(&val.id) {
                // A base seen as f64-direct must NOT also be an f32-widen base.
                if self.widen_bases.contains(&base.id) {
                    return false;
                }
                self.loads.insert(val.id, base);
                if !self.bases.iter().any(|b| b.id == base.id) {
                    self.bases.push(base);
                }
            }
            return true;
        }
        // A recognized unit-stride f32 load + `FcvtDS` WIDENING leaf (fp-convert)?
        if let Some(base) = self.widen_load_base(func, dom, val) {
            if !self.loads.contains_key(&val.id) {
                // A base seen as f32-widen must NOT also be an f64-direct base.
                if self.bases.iter().any(|b| b.id == base.id)
                    && !self.widen_bases.contains(&base.id)
                {
                    return false;
                }
                self.loads.insert(val.id, base);
                self.widen_bases.insert(base.id);
                if !self.bases.iter().any(|b| b.id == base.id) {
                    self.bases.push(base);
                }
            }
            return true;
        }
        let inst = func.inst(def_id);
        let ops = inst.operands.clone();
        use AArch64Opcode::*;
        match inst.opcode {
            FmulRR | FaddRR | FsubRR | FdivRR => {
                let a = match vreg_of(&ops[1]) {
                    Some(v) => v,
                    None => return false,
                };
                let b = match vreg_of(&ops[2]) {
                    Some(v) => v,
                    None => return false,
                };
                self.node_ok(func, dom, a, seen) && self.node_ok(func, dom, b, seen)
            }
            FmaddRR if ops.len() == 4 => {
                let n = vreg_of(&ops[1]);
                let m = vreg_of(&ops[2]);
                let a = vreg_of(&ops[3]);
                match (n, m, a) {
                    (Some(n), Some(m), Some(a)) => {
                        self.node_ok(func, dom, n, seen)
                            && self.node_ok(func, dom, m, seen)
                            && self.node_ok(func, dom, a, seen)
                    }
                    _ => false,
                }
            }
            FnegRR => {
                let a = match vreg_of(&ops[1]) {
                    Some(v) => v,
                    None => return false,
                };
                self.node_ok(func, dom, a, seen)
            }
            _ => false,
        }
    }

    /// Recognize a unit-stride f64 array load `dst = *(base + iv*8)` and return
    /// its loop-invariant base. The load is `LdrRI(dst[Fpr64], Madd(iv, 8, base),
    /// 0)` (factor order free). NON-widening only (f64 dst).
    fn load_base(&self, func: &MachFunction, dom: &DomTree, dst: VReg) -> Option<VReg> {
        if dst.class != RegClass::Fpr64 {
            return None;
        }
        self.strided_load_base(func, dom, dst, RegClass::Fpr64, ELEM_BYTES_F64)
    }

    /// Recognize an `f32 -> f64` WIDENING leaf `dst = (double)*(base + iv*4)` and
    /// return its loop-invariant base. The pattern is `FcvtSD(dst[Fpr64],
    /// src[Fpr32])` (FCVT Dd, Sn — the widening convert) where `src =
    /// LdrRI(src[Fpr32], Madd(iv, 4, base), 0)` — an f32 unit-stride array load
    /// fed to the exact f32->f64 widen. This is the fp-convert kernel's
    /// `(double)a_f32[i]` leaf; the vector lowering widens the coalesced f32 loads
    /// with `FCVTL/FCVTL2` (exact per-lane `fpext`), so the result is
    /// bit-identical to the scalar `FcvtSD`.
    fn widen_load_base(&self, func: &MachFunction, dom: &DomTree, dst: VReg) -> Option<VReg> {
        if dst.class != RegClass::Fpr64 {
            return None;
        }
        let &cvt_id = self.def.get(&dst.id)?;
        if !self.loop_insts.contains(&cvt_id) {
            return None;
        }
        let cvt = func.inst(cvt_id);
        if cvt.opcode != AArch64Opcode::FcvtSD || cvt.operands.len() != 2 {
            return None;
        }
        let src = vreg_of(&cvt.operands[1])?;
        if src.class != RegClass::Fpr32 {
            return None;
        }
        self.strided_load_base(func, dom, src, RegClass::Fpr32, ELEM_BYTES_F32)
    }

    /// Shared unit-stride array-load recognizer: `load_dst = LdrRI(load_dst[class],
    /// Madd(iv, es, base), 0)` with `base` loop-invariant. Returns the base.
    fn strided_load_base(
        &self,
        func: &MachFunction,
        dom: &DomTree,
        load_dst: VReg,
        class: RegClass,
        es: i64,
    ) -> Option<VReg> {
        if load_dst.class != class {
            return None;
        }
        let &load_id = self.def.get(&load_dst.id)?;
        if !self.loop_insts.contains(&load_id) {
            return None;
        }
        let load = func.inst(load_id);
        if load.opcode != AArch64Opcode::LdrRI
            || load.operands.len() != 3
            || imm_of(&load.operands[2]) != Some(0)
        {
            return None;
        }
        let addr = vreg_of(&load.operands[1])?;
        let &madd_id = self.def.get(&addr.id)?;
        if !self.loop_insts.contains(&madd_id) {
            return None;
        }
        let madd = func.inst(madd_id);
        if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
            return None;
        }
        let f1 = vreg_of(&madd.operands[1])?;
        let f2 = vreg_of(&madd.operands[2])?;
        let base = vreg_of(&madd.operands[3])?;
        let idx_ok = |f: VReg| f == self.iv;
        let es_ok = |f: VReg| const_value(func, &self.def, f) == Some(es);
        if !((idx_ok(f1) && es_ok(f2)) || (idx_ok(f2) && es_ok(f1))) {
            return None;
        }
        // `base` loop-invariant: its def dominates the preheader.
        let base_def = *self.def.get(&base.id)?;
        let base_block = block_of_inst(func, base_def)?;
        if !dom.dominates(base_block, self.preheader) {
            return None;
        }
        Some(base)
    }
}

fn collect_body_defs(func: &MachFunction, loop_insts: &HashSet<InstId>) -> HashSet<u32> {
    let mut defs = HashSet::new();
    for &id in loop_insts {
        let inst = func.inst(id);
        crate::effects::for_each_inst_def(inst, |v| {
            defs.insert(v.id);
        });
    }
    defs
}

fn block_of_inst(func: &MachFunction, id: InstId) -> Option<BlockId> {
    for (bidx, block) in func.blocks.iter().enumerate() {
        if block.insts.contains(&id) {
            return Some(BlockId(bidx as u32));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Transformation
// ---------------------------------------------------------------------------

struct LowerCtx {
    vbody: BlockId,
    preheader_term: InstId,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    loads: HashMap<u32, VReg>,
    /// (base id, pair index) -> Q register holding that pair's 2 f64 elements.
    loaded: HashMap<(u32, i64), VReg>,
    /// Per-pair cache of lowered load-dependent values (reset each pair).
    memo: HashMap<u32, VReg>,
    /// Current pair index (0..UNROLL).
    pair: i64,
    /// Persistent cache of loop-invariant f64 broadcasts.
    broadcast_cache: HashMap<u32, VReg>,
}

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    let width = VF * UNROLL; // lanes per vector iteration (8)

    // f32-widen bases pack 4 f64 pairs per LDP-Q of f32 (2 Q x FCVTL/FCVTL2), so
    // the unroll must be a positive multiple of 4. UNROLL = 4 satisfies this;
    // fail-closed if it is ever retuned to a non-multiple.
    if !rec.widen_bases.is_empty() && (UNROLL < 4 || UNROLL % 4 != 0) {
        return false;
    }

    // Fresh blocks: precheck / vector header / body / latch / exit.
    let pv = func.create_block();
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    insert_new_blocks_before(func, rec.vec_guard, &[pv, vh, vb, vl, vx]);
    func.add_edge(pv, vh);
    func.add_edge(pv, rec.vec_guard);
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: the loop bound (runtime register, or a reconstructed constant
    // materialized fresh) + fresh scalar accumulator svec = 0.0.
    let bound = match rec.bound_const {
        Some(k) => materialize_const(func, pre, k, RegClass::Gpr64),
        None => rec.bound,
    };
    // Element-size constants for the running-pointer init: 8 (f64-direct) and,
    // only when needed, 4 (f32-widen).
    let c_es8 = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es8), imm(ELEM_BYTES_F64)],
    );
    let c_es4 = if rec.widen_bases.is_empty() {
        None
    } else {
        let c = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Movz,
            vec![vreg(c), imm(ELEM_BYTES_F32)],
        );
        Some(c)
    };
    let wz = alloc(func, RegClass::Gpr64);
    emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(wz), imm(0)]);
    let svec = alloc(func, RegClass::Fpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::FmovGprFpr,
        vec![vreg(svec), vreg(wz)],
    );

    // --- Preheader: ONE running pointer per array stream: `p = base + iv*es`
    // (es = 8 for f64-direct streams, 4 for f32-widen streams).
    let ptrs: Vec<VReg> = rec
        .bases
        .iter()
        .map(|base| {
            let es = if rec.widen_bases.contains(&base.id) {
                c_es4.expect("f32-widen base requires the 4-byte element-size const")
            } else {
                c_es8
            };
            let p = alloc(func, RegClass::Gpr64);
            emit_before(
                func,
                pre,
                AArch64Opcode::Madd,
                vec![vreg(p), vreg(rec.iv), vreg(es), vreg(*base)],
            );
            p
        })
        .collect();

    // --- Precheck: `main_bound = bound - (width-1)`; SIGNED `if bound < width skip`.
    let main_bound = alloc(func, RegClass::Gpr64);
    emit(
        func,
        pv,
        AArch64Opcode::SubRI,
        vec![vreg(main_bound), vreg(bound), imm(width - 1)],
    );
    emit(
        func,
        pv,
        AArch64Opcode::CmpRI,
        vec![vreg(bound), imm(width)],
    );
    emit(
        func,
        pv,
        AArch64Opcode::BCond,
        vec![imm(CC_LT), block(rec.vec_guard)],
    );
    emit(func, pv, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector header: SIGNED `iv <s main_bound` ⇒ enter body. Signed (not
    // unsigned) is REQUIRED for a NEGATIVE starting induction (e.g.
    // `for (i = -k; i < n; i++) … x[i] …` over a mid-array base): as unsigned,
    // a negative `iv` compares HUGE, which would skip the vector loop AND then
    // drive the remainder-0 exit guard below to skip the SCALAR tail too —
    // dropping every iteration (a miscompile, caught by differential test).
    // Signed compares run the vector body for negative `iv` as well, reading
    // exactly the scalar loop's addresses (`p = base + iv*es` lockstep); no
    // wrap: `bound ∈ [width, 2^63)` (precheck) ⇒ `main_bound ∈ [1, 2^63)` and
    // `iv + width <= bound` on every admitted iteration.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LT), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Vector body: walk each stream's running pointer with post-index
    // `LDP Qt1, Qt2, [p], #32` (32 bytes) loads. Each vector iteration reads
    // `width` elements per stream in lockstep with `iv += width`, so
    // `p == base + iv*es` holds at every header eval — reading EXACTLY what the
    // scalar loop reads. Pair `k` (a `.2D` Q) holds elements `[iv+2k, iv+2k+2)`.
    //
    //  * f64-direct: UNROLL/2 LDP-Q (each 4 f64) deliver the `.2D` pairs directly.
    //  * f32-widen : UNROLL/4 LDP-Q (each 8 f32) are widened by FCVTL (low half)
    //    / FCVTL2 (high half) — exact per-lane `fpext` — into the same `.2D`
    //    (f64) pair vectors the drain consumes, bit-identical to scalar `FcvtDS`.
    let mut loaded: HashMap<(u32, i64), VReg> = HashMap::new();
    for (base, p) in rec.bases.iter().zip(&ptrs) {
        if rec.widen_bases.contains(&base.id) {
            for g in 0..UNROLL / 4 {
                let qf0 = alloc(func, RegClass::Fpr128);
                let qf1 = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonLdpQPost,
                    vec![vreg(qf0), vreg(qf1), vreg(*p), imm(32)],
                );
                // qf0 -> pairs (4g+0, 4g+1); qf1 -> pairs (4g+2, 4g+3).
                for (qi, qf) in [qf0, qf1].into_iter().enumerate() {
                    let d_lo = alloc(func, RegClass::Fpr128);
                    let d_hi = alloc(func, RegClass::Fpr128);
                    emit(
                        func,
                        vb,
                        AArch64Opcode::NeonFcvtlV,
                        vec![vreg(d_lo), vreg(qf)],
                    );
                    emit(
                        func,
                        vb,
                        AArch64Opcode::NeonFcvtl2V,
                        vec![vreg(d_hi), vreg(qf)],
                    );
                    let pair_lo = 4 * g + 2 * (qi as i64);
                    loaded.insert((base.id, pair_lo), d_lo);
                    loaded.insert((base.id, pair_lo + 1), d_hi);
                }
            }
        } else {
            for pair in 0..UNROLL / 2 {
                let q0 = alloc(func, RegClass::Fpr128);
                let q1 = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonLdpQPost,
                    vec![vreg(q0), vreg(q1), vreg(*p), imm(32)],
                );
                loaded.insert((base.id, 2 * pair), q0);
                loaded.insert((base.id, 2 * pair + 1), q1);
            }
        }
    }

    let mut ctx = LowerCtx {
        vbody: vb,
        preheader_term: pre,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        loads: rec.loads.clone(),
        loaded,
        memo: HashMap::new(),
        pair: 0,
        broadcast_cache: HashMap::new(),
    };

    // Lower the elementwise term(s) per pair into vectors, then ORDERED DRAIN.
    match rec.root {
        Root::PlainFadd { term } => {
            // Compute the per-pair term vector, then scalar-FADD each lane in order.
            let mut vterms: Vec<VReg> = Vec::with_capacity(UNROLL as usize);
            for pair in 0..UNROLL {
                ctx.pair = pair;
                ctx.memo.clear();
                let Some(vt) = lower(func, &mut ctx, term) else {
                    return false;
                };
                vterms.push(vt);
            }
            for &vt in &vterms {
                for lane in 0..VF {
                    let d = alloc(func, RegClass::Fpr64);
                    emit(
                        func,
                        vb,
                        AArch64Opcode::NeonDupScalarD,
                        vec![vreg(d), vreg(vt), imm(lane)],
                    );
                    emit(
                        func,
                        vb,
                        AArch64Opcode::FaddRR,
                        vec![vreg(svec), vreg(svec), vreg(d)],
                    );
                }
            }
        }
        Root::FusedFma { n, m, may_unfuse } => {
            // Compute the two multiplicand vectors per pair, then scalar-FMADD each
            // lane in order (multiply stays fused — single rounding preserved).
            let mut vns: Vec<VReg> = Vec::with_capacity(UNROLL as usize);
            let mut vms: Vec<VReg> = Vec::with_capacity(UNROLL as usize);
            for pair in 0..UNROLL {
                ctx.pair = pair;
                ctx.memo.clear();
                let Some(vn) = lower(func, &mut ctx, n) else {
                    return false;
                };
                let Some(vm) = lower(func, &mut ctx, m) else {
                    return false;
                };
                vns.push(vn);
                vms.push(vm);
            }
            for (&vn, &vm) in vns.iter().zip(&vms) {
                for lane in 0..VF {
                    let dn = alloc(func, RegClass::Fpr64);
                    let dm = alloc(func, RegClass::Fpr64);
                    emit(
                        func,
                        vb,
                        AArch64Opcode::NeonDupScalarD,
                        vec![vreg(dn), vreg(vn), imm(lane)],
                    );
                    emit(
                        func,
                        vb,
                        AArch64Opcode::NeonDupScalarD,
                        vec![vreg(dm), vreg(vm), imm(lane)],
                    );
                    // FMADD(svec, dn, dm, svec) = svec + dn*dm (fused, single round).
                    let fmadd = emit(
                        func,
                        vb,
                        AArch64Opcode::FmaddRR,
                        vec![vreg(svec), vreg(dn), vreg(dm), vreg(svec)],
                    );
                    if may_unfuse {
                        func.inst_mut(fmadd)
                            .flags
                            .insert(InstFlags::FMULADD_MAY_UNFUSE);
                    }
                }
            }
        }
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

    // --- Vector exit / drain: seed the scalar accumulator (a plain COPY of the
    // partial sum — bit-exact) for BOTH the scalar tail (acc) and the true-exit
    // live-out (acc_src), then guard the rotated do-while tail against remainder 0.
    emit(
        func,
        vx,
        AArch64Opcode::FmovFprFpr,
        vec![vreg(rec.acc), vreg(svec)],
    );
    emit(
        func,
        vx,
        AArch64Opcode::FmovFprFpr,
        vec![vreg(rec.acc_src), vreg(svec)],
    );
    emit(
        func,
        vx,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(bound)],
    );
    // SIGNED `iv >=s bound` (matches the signed header guard — see the vh
    // comment): a NEGATIVE `iv` must fall into the scalar do-while tail, not
    // compare unsigned-huge and branch to the exit.
    emit(
        func,
        vx,
        AArch64Opcode::BCond,
        vec![imm(CC_GE), block(rec.exit)],
    );

    // --- COMMIT: splice the vector loop in front of the scalar loop.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.vec_guard, pv) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.vec_guard);
    func.add_edge(rec.preheader, pv);
    func.add_edge(vx, rec.vec_guard);
    func.add_edge(vx, rec.exit);
    true
}

/// Lower `val` to a `.2D` (f64) NEON value for the current pair. `None` only on
/// an unexpected shape (recognition already proved lowerability).
fn lower(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> Option<VReg> {
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
    }
    // A recognized load leaf ⇒ the current pair's Q register for that base.
    if let Some(&base) = ctx.loads.get(&val.id) {
        let q = *ctx.loaded.get(&(base.id, ctx.pair))?;
        ctx.memo.insert(val.id, q);
        return Some(q);
    }
    let &def_id = ctx.def.get(&val.id)?;
    if !ctx.loop_insts.contains(&def_id) {
        // loop-invariant f64 leaf ⇒ broadcast to both lanes (once).
        let v = broadcast(func, ctx, val);
        return Some(v);
    }
    let inst = func.inst(def_id);
    let opcode = inst.opcode;
    let ops = inst.operands.clone();
    use AArch64Opcode::*;
    let result = match opcode {
        FmulRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            fbin(func, ctx, NeonFmulV, a, b)
        }
        FaddRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            fbin(func, ctx, NeonFaddV, a, b)
        }
        FsubRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            fbin(func, ctx, NeonFsubV, a, b)
        }
        FdivRR => {
            let (a, b) = lower_two(func, ctx, &ops)?;
            fbin(func, ctx, NeonFdivV, a, b)
        }
        FmaddRR => {
            // d = a + n*m (fused). Copy the addend into a fresh Vd, then FMLA.
            let n = lower(func, ctx, vreg_of(&ops[1])?)?;
            let m = lower(func, ctx, vreg_of(&ops[2])?)?;
            let a = lower(func, ctx, vreg_of(&ops[3])?)?;
            let vd = alloc(func, RegClass::Fpr128);
            emit(func, ctx.vbody, NeonOrrV, vec![vreg(vd), vreg(a), vreg(a)]);
            emit(
                func,
                ctx.vbody,
                NeonFmlaV,
                vec![vreg(vd), vreg(n), vreg(m), imm(FARR_D2)],
            );
            vd
        }
        FnegRR => {
            let a = lower(func, ctx, vreg_of(&ops[1])?)?;
            let z = zero_vec(func, ctx);
            fbin(func, ctx, NeonFsubV, z, a)
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

fn fbin(func: &mut MachFunction, ctx: &LowerCtx, op: AArch64Opcode, a: VReg, b: VReg) -> VReg {
    let d = alloc(func, RegClass::Fpr128);
    emit(
        func,
        ctx.vbody,
        op,
        vec![vreg(d), vreg(a), vreg(b), imm(FARR_D2)],
    );
    d
}

/// Broadcast a loop-invariant f64 scalar to both `.2D` lanes (once).
fn broadcast(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> VReg {
    if let Some(&v) = ctx.broadcast_cache.get(&val.id) {
        return v;
    }
    let d = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        ctx.preheader_term,
        AArch64Opcode::NeonDupElem,
        vec![vreg(d), vreg(val), imm(0), imm(ELEM_D)],
    );
    ctx.broadcast_cache.insert(val.id, d);
    d
}

fn zero_vec(func: &mut MachFunction, ctx: &mut LowerCtx) -> VReg {
    if let Some(&v) = ctx.broadcast_cache.get(&u32::MAX) {
        return v;
    }
    let d = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        ctx.preheader_term,
        AArch64Opcode::NeonMovi,
        vec![vreg(d), imm(0)],
    );
    ctx.broadcast_cache.insert(u32::MAX, d);
    d
}

fn materialize_const(func: &mut MachFunction, pre: InstId, k: i64, class: RegClass) -> VReg {
    let b = alloc(func, class);
    let lo = k & 0xFFFF;
    let hi = (k >> 16) & 0xFFFF;
    emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(b), imm(lo)]);
    if hi != 0 {
        emit_before(
            func,
            pre,
            AArch64Opcode::Movk,
            vec![vreg(b), imm(hi), imm(16)],
        );
    }
    b
}

// ===========================================================================
// IOTA-FILL: the `.4S` induction-derived STORE map (the fp-convert fill loop)
// ===========================================================================
//
// The reduction path above is PURE-READ. The fp-convert kernel ALSO has a
// store-bearing fill loop that dominates its runtime alongside the dot:
//
// ```c
// for (j = 0; j < n; ++j) { x[j] = a + (float)j; y[j] = b + (float)j; }
// ```
//
// Each stored value is a per-lane dataflow of an INT->FLOAT of the induction
// (`(float)j` = `UCVTF`/`SCVTF` of `j`, possibly via a `MovR` truncation to
// `i32`) and loop-invariant `f32` leaves (`a`, `b`), stored unit-stride. This
// is the classic IOTA pattern: the vector body materializes the induction lane
// vector `[j, j+1, j+2, j+3]` once in the preheader (a broadcast base + a
// constant `[0,1,2,3]` step, advanced by `FILL_WIDTH` each iteration),
// `UCVTF`/`SCVTF`s it to `.4S` floats, applies the SAME per-lane invariant
// arithmetic, and stores the `Q` vectors with `STP Qt1, Qt2, [p], #32`.
//
// ## Why it is BIT-IDENTICAL to the scalar loop
//
// `(float)(j+lane)` in lane `lane` is the EXACT SAME per-lane `UCVTF`/`SCVTF`
// the scalar loop performs on the same integer `j+lane` (no reassociation, no
// widening — the vector converts the identical `i32` value with the identical
// IEEE rounding). The lane index `j+lane` never overflows `i32` differently
// from the scalar loop: the vector body runs only while `iv < bound-(width-1)`
// and the bound is filtered to `[1, i32::MAX]`, so `[j, j+width) ⊂ [0, bound)`
// and the `.4S` add that builds the index vector cannot wrap where the scalar
// `i64` induction would not. The invariant per-lane arithmetic (`a + …`) is the
// SAME `.4S` FP op per lane as the scalar `f32` op. Fail-closed on any leaf that
// is not the induction cvt or a loop-invariant `f32`.
//
// ## Why the STORES are SOUND (aliasing)
//
// The loop READS no memory (values are a pure function of `j` + invariants), so
// the ONLY hazard is store/store between the distinct output streams (writing a
// whole `x`-block then a whole `y`-block reorders per-index writes vs the scalar
// interleave iff the two ranges overlap). Each stream individually writes
// DISTINCT indices, so any order within a stream is fine; between streams, the
// pass emits a REGIME-C runtime byte-range disjointness precheck
// (`x_end <=u y` or `y_end <=u x`, per unordered pair of DISTINCT bases) and
// takes the vector path ONLY when the streams are proven disjoint — otherwise
// the (untouched) scalar loop runs. A single output stream needs no guard.

/// A fully validated IV-synthesized `.4S` IOTA-FILL loop (the fp-convert fill).
struct RecognizedFill {
    preheader_term: InstId,
    vec_guard: BlockId,
    preheader: BlockId,
    exit: BlockId,
    iv: VReg,
    bound: VReg,
    bound_const: Option<i64>,
    /// `true` ⇒ the induction cvt is `UCVTF` (unsigned); `false` ⇒ `SCVTF`.
    unsigned_cvt: bool,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// The recognized unit-stride stores, in PROGRAM ORDER: `(base, value_root)`.
    stores: Vec<(VReg, VReg)>,
    /// Vreg ids of the induction cvt leaves (`(float)j`); lowered to the current
    /// pair's `.4S` float index vector.
    cvt_leaves: HashSet<u32>,
    /// Distinct store bases (dedup, first-seen order) — the disjointness set.
    bases: Vec<VReg>,
}

/// Opcodes permitted anywhere in an IOTA-FILL loop body. Anything else ⇒ BAIL
/// (rules out LOADS — there are none in a pure fill — calls, atomics, etc.).
fn allowed_fill_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        // induction int->float leaf + invariant f32 arithmetic (the stored value).
        UcvtfRR | ScvtfRR | FaddRR | FsubRR | FmulRR | FdivRR | FnegRR
        // the unit-stride store + its `Madd(iv, es, base)` address arithmetic.
        | StrRI | Madd
        // induction step + bound materialization + the iv->i32 cvt-source trunc.
        | AddRR | AddRI | Movz | Movk | MovR | Copy | FmovFprFpr
        // control (the rotated exit is `CmpRR; BCond`).
        | CmpRR | CmpRI | BCond | B
    )
}

impl RecognizedFill {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // (F1) exactly a 2-block innermost loop {header, latch}.
        if header == latch || body.len() != 2 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // (F2) whitelist every opcode — no loads/calls/atomics/etc.
        let mut loop_insts = HashSet::new();
        for &b in [header, latch].iter() {
            for &id in &func.block(b).insts {
                if !allowed_fill_op(func.inst(id).opcode) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

        // `def` is supplied by the caller, built ONCE per recognition sweep.
        // Measured as ~99% of this pass's entire cost when it was rebuilt inside
        // every per-loop attempt.

        // (F3) header preds = {latch, guard}; re-root onto the guard (rotated).
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            return None;
        }
        let guard = *hpreds.iter().find(|&&b| b != latch)?;
        let preheader_term = *func
            .block(guard)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))?;

        // (F4) latch = exactly ONE copy_like writeback (the iv) + ONE `B -> header`.
        // A fill loop carries NO accumulator — only the induction.
        let latch_insts = func.block(latch).insts.clone();
        let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
        let mut non_copy: Vec<InstId> = Vec::new();
        for &id in &latch_insts {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                writebacks.push((d, s));
            } else {
                non_copy.push(id);
            }
        }
        if writebacks.len() != 1 {
            return None;
        }
        if non_copy.len() != 1
            || func.inst(non_copy[0]).opcode != AArch64Opcode::B
            || !branch_targets(func.inst(non_copy[0])).contains(&header)
        {
            return None;
        }
        let (iv, iv_src) = writebacks[0];
        if !is_increment_by_one(func, &def, iv_src, iv) {
            return None;
        }
        if iv.class != RegClass::Gpr64 {
            return None;
        }

        // (F5) rotated header exit test + the loop bound (const, or a runtime
        // register whose def dominates the preheader — mirrors the reduction path).
        let (bound_raw, exit, cmp_id) = recognize_rotated_header_exit(func, header, body, iv_src)?;
        if bound_raw.class != RegClass::Gpr64 {
            return None;
        }
        let bound_const = crate::reaching_const::unique_reaching_const(func, cmp_id, bound_raw)
            .filter(|k| (1..=i32::MAX as i64).contains(k));
        if bound_const.is_none()
            && let Some(&bdef) = def.get(&bound_raw.id)
        {
            let bblock = block_of_inst(func, bdef)?;
            if !dom.dominates(bblock, guard) {
                return None;
            }
        }

        let mut rec = RecognizedFill {
            preheader_term,
            vec_guard: header,
            preheader: guard,
            exit,
            iv,
            bound: bound_raw,
            bound_const,
            unsigned_cvt: true,
            // Cloned only on a SUCCESSFUL recognition, which is rare; the cost
            // that mattered was rebuilding on every ATTEMPT.
            def: def.clone(),
            loop_insts,
            stores: Vec::new(),
            cvt_leaves: HashSet::new(),
            bases: Vec::new(),
        };

        // (F6) collect EVERY store. Each must be a recognized unit-stride f32 store
        // `StrRI(val[Fpr32], Madd(iv, 4, base), 0)` whose value dataflow is a
        // per-lane function of the induction cvt + loop-invariant f32 leaves.
        let mut saw_signed = false;
        let mut saw_unsigned = false;
        let mut store_ids: Vec<InstId> = rec
            .loop_insts
            .iter()
            .copied()
            .filter(|&id| func.inst(id).opcode == AArch64Opcode::StrRI)
            .collect();
        // Program order (StrRI ids are assigned in emission order within the block).
        store_ids.sort_by_key(|id| id.0);
        if store_ids.is_empty() {
            return None;
        }
        let mut seen = HashSet::new();
        for id in store_ids {
            let st = func.inst(id);
            if st.operands.len() != 3 || imm_of(&st.operands[2]) != Some(0) {
                return None;
            }
            let val = vreg_of(&st.operands[0])?;
            let addr = vreg_of(&st.operands[1])?;
            if val.class != RegClass::Fpr32 {
                return None; // only the `.4S` (f32) fill; wider fills bail
            }
            let base = rec.store_base(func, dom, addr)?;
            if !rec.node_ok(func, val, &mut seen, &mut saw_signed, &mut saw_unsigned) {
                return None;
            }
            rec.stores.push((base, val));
            if !rec.bases.iter().any(|b| b.id == base.id) {
                rec.bases.push(base);
            }
        }
        // A store value that never flows through the induction cvt (a pure
        // invariant broadcast) is not an iota fill — leave it to the scalar path.
        if rec.cvt_leaves.is_empty() {
            return None;
        }
        if saw_signed && saw_unsigned {
            return None; // mixed cvt kinds on the same induction — bail
        }
        rec.unsigned_cvt = !saw_signed;

        // (F7) no live-outs other than {iv, iv_src}: every other body-defined vreg
        // (stored values, the iota, addresses) must be body-local (the store is the
        // only consumer), so the vectorized body cannot leave a stale live-out when
        // the tail runs 0 times.
        let allowed_liveout: HashSet<u32> = [iv.id, iv_src.id].into_iter().collect();
        let body_defs = collect_body_defs(func, &rec.loop_insts);
        for (bidx, block) in func.blocks.iter().enumerate() {
            let bid = BlockId(bidx as u32);
            if body.contains(&bid) {
                continue;
            }
            for &id in &block.insts {
                for op in &func.inst(id).operands {
                    if let Some(v) = vreg_of(op)
                        && body_defs.contains(&v.id)
                        && !allowed_liveout.contains(&v.id)
                    {
                        return None;
                    }
                }
            }
        }

        Some(rec)
    }

    /// Recognize a unit-stride f32 store address `Madd(iv, 4, base)` with `base`
    /// loop-invariant, returning the base (mirror of the reduction load recognizer).
    fn store_base(&self, func: &MachFunction, dom: &DomTree, addr: VReg) -> Option<VReg> {
        let &madd_id = self.def.get(&addr.id)?;
        if !self.loop_insts.contains(&madd_id) {
            return None;
        }
        let madd = func.inst(madd_id);
        if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
            return None;
        }
        let f1 = vreg_of(&madd.operands[1])?;
        let f2 = vreg_of(&madd.operands[2])?;
        let base = vreg_of(&madd.operands[3])?;
        let idx_ok = |f: VReg| f == self.iv;
        let es_ok = |f: VReg| const_value(func, &self.def, f) == Some(ELEM_BYTES_F32);
        if !((idx_ok(f1) && es_ok(f2)) || (idx_ok(f2) && es_ok(f1))) {
            return None;
        }
        let base_def = *self.def.get(&base.id)?;
        let base_block = block_of_inst(func, base_def)?;
        if !dom.dominates(base_block, self.preheader) {
            return None;
        }
        Some(base)
    }

    /// Read-only feasibility mirroring [`lower_fill`]: every reachable node of a
    /// stored value is the induction cvt (`UCVTF`/`SCVTF` of the iv, possibly via a
    /// `MovR` truncation to i32), a loop-invariant `f32`, or an allowed lane-wise
    /// `f32` op over such. Records the cvt leaves + which cvt sign(s) appear.
    fn node_ok(
        &mut self,
        func: &MachFunction,
        val: VReg,
        seen: &mut HashSet<u32>,
        saw_signed: &mut bool,
        saw_unsigned: &mut bool,
    ) -> bool {
        if val.class != RegClass::Fpr32 {
            return false; // only `.4S` (f32) lanes
        }
        if !seen.insert(val.id) {
            return true;
        }
        let Some(&def_id) = self.def.get(&val.id) else {
            return false;
        };
        if !self.loop_insts.contains(&def_id) {
            return true; // loop-invariant f32 leaf (broadcast once)
        }
        let inst = func.inst(def_id);
        let ops = inst.operands.clone();
        use AArch64Opcode::*;
        match inst.opcode {
            UcvtfRR | ScvtfRR => {
                // The induction cvt leaf: `(float)j`. Source is the iv, or a
                // truncating copy of it (`MovR Wd, Xiv`).
                let src = match vreg_of(&ops[1]) {
                    Some(s) => s,
                    None => return false,
                };
                if !self.src_is_iv(func, src) {
                    return false;
                }
                if inst.opcode == UcvtfRR {
                    *saw_unsigned = true;
                } else {
                    *saw_signed = true;
                }
                self.cvt_leaves.insert(val.id);
                true
            }
            FaddRR | FsubRR | FmulRR | FdivRR => {
                let a = match vreg_of(&ops[1]) {
                    Some(v) => v,
                    None => return false,
                };
                let b = match vreg_of(&ops[2]) {
                    Some(v) => v,
                    None => return false,
                };
                self.node_ok(func, a, seen, saw_signed, saw_unsigned)
                    && self.node_ok(func, b, seen, saw_signed, saw_unsigned)
            }
            FnegRR => {
                let a = match vreg_of(&ops[1]) {
                    Some(v) => v,
                    None => return false,
                };
                self.node_ok(func, a, seen, saw_signed, saw_unsigned)
            }
            _ => false,
        }
    }

    /// `src` is the induction register, or a truncating copy of it (`MovR Wd, Xiv`
    /// — the `i64 -> i32` narrowing clang inserts before a 32-bit `UCVTF`).
    fn src_is_iv(&self, func: &MachFunction, src: VReg) -> bool {
        if src == self.iv {
            return true;
        }
        if let Some(&d) = self.def.get(&src.id)
            && self.loop_insts.contains(&d)
            && let Some((_, s)) = copy_like(func.inst(d))
        {
            return s == self.iv;
        }
        false
    }
}

// --- IOTA-FILL transformation ---------------------------------------------

/// Per-pair lowering context for the fill's stored-value dataflow.
struct FillLowerCtx {
    vbody: BlockId,
    preheader_term: InstId,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    cvt_leaves: HashSet<u32>,
    /// The current pair's `[(f32)(iv+4k+lane)]` index vector.
    vf: VReg,
    memo: HashMap<u32, VReg>,
    broadcast_cache: HashMap<u32, VReg>,
}

fn apply_fill(func: &mut MachFunction, rec: &RecognizedFill) -> bool {
    let width = FILL_WIDTH; // f32 elements per vector iteration (8)

    // Fresh blocks: precheck / (disjointness chain) / vector header / body /
    // latch / exit. Disjointness needs 2 blocks per unordered pair of DISTINCT
    // store bases (regime-C); a single stream needs none.
    let npairs = rec.bases.len().saturating_sub(1) * rec.bases.len() / 2;
    let pv = func.create_block();
    let guard_blocks: Vec<BlockId> = (0..2 * npairs).map(|_| func.create_block()).collect();
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    let mut new_blocks = vec![pv];
    new_blocks.extend(guard_blocks.iter().copied());
    new_blocks.extend([vh, vb, vl, vx]);
    insert_new_blocks_before(func, rec.vec_guard, &new_blocks);
    func.add_edge(pv, rec.vec_guard); // `bound < width` skip
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: the loop bound (runtime register, or a reconstructed const),
    // the element-size const (4), and ONE running store pointer per stream.
    let bound = match rec.bound_const {
        Some(k) => materialize_const(func, pre, k, RegClass::Gpr64),
        None => rec.bound,
    };
    let c_es4 = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es4), imm(ELEM_BYTES_F32)],
    );
    let ptrs: Vec<VReg> = rec
        .bases
        .iter()
        .map(|base| {
            let p = alloc(func, RegClass::Gpr64);
            emit_before(
                func,
                pre,
                AArch64Opcode::Madd,
                vec![vreg(p), vreg(rec.iv), vreg(c_es4), vreg(*base)],
            );
            p
        })
        .collect();

    // --- Preheader: the running `.4S` index vector vidx0 = [iv, iv+1, iv+2, iv+3]
    // (a broadcast of iv + the constant step [0,1,2,3]) and the per-pair / advance
    // broadcast offsets. vidx0 is loop-carried, advanced by [width; 4] each iter.
    let dup0 = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonDupGen,
        vec![vreg(dup0), vreg(rec.iv), imm(ELEM_S)],
    );
    let step0123 = materialize_iota_step(func, pre);
    let vidx0 = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonAddV,
        vec![vreg(vidx0), vreg(dup0), vreg(step0123), imm(IARR_S4)],
    );
    let vstep = dup_const_i32_s4(func, pre, width);
    // Per-pair lane offset broadcast: pair k covers lanes [VF_S*k, VF_S*k+VF_S).
    let voff: Vec<Option<VReg>> = (0..UNROLL_S)
        .map(|k| {
            if k == 0 {
                None
            } else {
                Some(dup_const_i32_s4(func, pre, VF_S * k))
            }
        })
        .collect();

    // --- Precheck (`pv`): straight-line setup FIRST (so the block's only branches
    // are its trailing `BCond`/`B` terminators): `main_bound = bound - (width-1)`,
    // then the regime-C disjointness ranges (`nbytes`, each base's `end`). Then the
    // SIGNED `if bound < width skip` and the fall-through B into the disjointness
    // chain (or directly to `vh` when there is a single output stream).
    let main_bound = alloc(func, RegClass::Gpr64);
    emit(
        func,
        pv,
        AArch64Opcode::SubRI,
        vec![vreg(main_bound), vreg(bound), imm(width - 1)],
    );
    // Distinct-base end addresses `end = base + bound*4` (only when versioning).
    let ends: Vec<(u32, VReg)> = if guard_blocks.is_empty() {
        Vec::new()
    } else {
        let nbytes = alloc(func, RegClass::Gpr64);
        emit(
            func,
            pv,
            AArch64Opcode::LslRI,
            vec![vreg(nbytes), vreg(bound), imm(2)],
        );
        rec.bases
            .iter()
            .map(|b| {
                let e = alloc(func, RegClass::Gpr64);
                emit(
                    func,
                    pv,
                    AArch64Opcode::AddRR,
                    vec![vreg(e), vreg(*b), vreg(nbytes)],
                );
                (b.id, e)
            })
            .collect()
    };
    emit(
        func,
        pv,
        AArch64Opcode::CmpRI,
        vec![vreg(bound), imm(width)],
    );
    emit(
        func,
        pv,
        AArch64Opcode::BCond,
        vec![imm(CC_LT), block(rec.vec_guard)],
    );
    let first = guard_blocks.first().copied().unwrap_or(vh);
    emit(func, pv, AArch64Opcode::B, vec![block(first)]);
    func.add_edge(pv, first);

    // Disjointness chain: prove every pair of DISTINCT store bases has
    // non-overlapping `[base, base + bound*4)` ranges; any possible overlap ⇒ the
    // untouched scalar loop. With a single stream, `guard_blocks` is empty and pv
    // fell straight through to vh above.
    emit_disjointness_chain(func, rec, &guard_blocks, &ends, vh);

    // --- Vector header: SIGNED `iv <s main_bound` ⇒ enter body (signed for the
    // NEGATIVE-start induction, exactly as the reduction path's vh — an unsigned
    // compare would skip the vector loop AND make the exit guard below skip the
    // scalar tail, dropping every store). The lane values stay bit-identical for
    // negative `iv` too: each stored lane uses `trunc32(iv)+k ≡ trunc32(iv+k)
    // (mod 2^32)`, the SAME i32 the scalar cvt consumes.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LT), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Vector body: convert each pair's index vector to `.4S` floats, lower each
    // stored value per pair, and store the two `.4S` value vectors per stream with
    // `STP Qt1, Qt2, [p], #32`.
    let cvt_op = if rec.unsigned_cvt {
        AArch64Opcode::NeonUcvtfV
    } else {
        AArch64Opcode::NeonScvtfV
    };
    let mut ctx = FillLowerCtx {
        vbody: vb,
        preheader_term: pre,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        cvt_leaves: rec.cvt_leaves.clone(),
        vf: vidx0,
        memo: HashMap::new(),
        broadcast_cache: HashMap::new(),
    };
    // Per-store, per-pair value vectors: stores[s] -> [Q_pair0, Q_pair1, ...].
    let mut store_vecs: Vec<Vec<VReg>> =
        vec![Vec::with_capacity(UNROLL_S as usize); rec.stores.len()];
    for k in 0..UNROLL_S {
        // vi_k = vidx0 + [VF_S*k; 4]  (pair 0 = vidx0).
        let vi_k = match voff[k as usize] {
            None => vidx0,
            Some(off) => {
                let d = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(d), vreg(vidx0), vreg(off), imm(IARR_S4)],
                );
                d
            }
        };
        // vf_k = cvt(vi_k) = [(float)(iv+4k), …, (float)(iv+4k+3)].
        let vf = alloc(func, RegClass::Fpr128);
        emit(func, vb, cvt_op, vec![vreg(vf), vreg(vi_k), imm(FARR_S4)]);
        ctx.vf = vf;
        ctx.memo.clear();
        for (s, (_, val)) in rec.stores.iter().enumerate() {
            let Some(q) = lower_fill(func, &mut ctx, *val) else {
                return false;
            };
            store_vecs[s].push(q);
        }
    }
    // Advance the running index vector by [width; 4] for the next iteration.
    emit(
        func,
        vb,
        AArch64Opcode::NeonAddV,
        vec![vreg(vidx0), vreg(vidx0), vreg(vstep), imm(IARR_S4)],
    );
    // Store each stream's `UNROLL_S` `.4S` vectors with one `STP Qt1, Qt2, [p], #32`.
    // `UNROLL_S == 2` guarantees exactly two value vectors per stream.
    if UNROLL_S != 2 {
        return false;
    }
    for (s, (base, _)) in rec.stores.iter().enumerate() {
        let p = ptrs[rec
            .bases
            .iter()
            .position(|b| b.id == base.id)
            .expect("base indexed")];
        let q0 = store_vecs[s][0];
        let q1 = store_vecs[s][1];
        emit(
            func,
            vb,
            AArch64Opcode::NeonStpQPost,
            vec![vreg(q0), vreg(q1), vreg(p), imm(2 * 16)],
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

    // --- Vector exit: guard the rotated do-while tail against remainder 0 (vector
    // consumed all `n`, `iv == bound` ⇒ branch to the true exit, else fall into the
    // untouched scalar do-while for the `< width` tail). SIGNED `>=s` (matches the
    // signed vh guard): a negative `iv` must run the scalar tail.
    emit(
        func,
        vx,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(bound)],
    );
    emit(
        func,
        vx,
        AArch64Opcode::BCond,
        vec![imm(CC_GE), block(rec.exit)],
    );

    // --- COMMIT: splice the vector loop in front of the scalar loop.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.vec_guard, pv) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.vec_guard);
    func.add_edge(rec.preheader, pv);
    func.add_edge(vx, rec.vec_guard);
    func.add_edge(vx, rec.exit);
    true
}

/// Emit the regime-C runtime disjointness chain into `guard_blocks` (two blocks
/// per unordered pair of DISTINCT store bases). For each pair, two sub-tests
/// (`i_end <=u j` / `j_end <=u i`); passing either proves THAT pair disjoint and
/// chains to the next pair (or `vh`). Any possible overlap ⇒ the (untouched)
/// scalar loop (`rec.vec_guard`). `ends` holds each distinct base's precomputed
/// `base + bound*4`. With a single stream, `guard_blocks` is empty (no-op).
fn emit_disjointness_chain(
    func: &mut MachFunction,
    rec: &RecognizedFill,
    guard_blocks: &[BlockId],
    ends: &[(u32, VReg)],
    vh: BlockId,
) {
    if guard_blocks.is_empty() {
        return;
    }
    let end_of = |id: u32| {
        ends.iter()
            .find(|(k, _)| *k == id)
            .map(|(_, e)| *e)
            .unwrap()
    };
    let mut pairs: Vec<(VReg, VReg)> = Vec::new();
    for i in 0..rec.bases.len() {
        for j in (i + 1)..rec.bases.len() {
            pairs.push((rec.bases[i], rec.bases[j]));
        }
    }
    let n = pairs.len();
    for (i, (bi, bj)) in pairs.iter().enumerate() {
        let c1 = guard_blocks[2 * i];
        let c2 = guard_blocks[2 * i + 1];
        let ok = if i + 1 < n {
            guard_blocks[2 * i + 2]
        } else {
            vh
        };
        // c1: `i_end <=u j` ? b.ls ok ; else fall to c2.
        emit(
            func,
            c1,
            AArch64Opcode::CmpRR,
            vec![vreg(end_of(bi.id)), vreg(*bj)],
        );
        emit(func, c1, AArch64Opcode::BCond, vec![imm(CC_LS), block(ok)]);
        emit(func, c1, AArch64Opcode::B, vec![block(c2)]);
        func.add_edge(c1, ok);
        func.add_edge(c1, c2);
        // c2: `j_end <=u i` ? b.ls ok ; else may overlap ⇒ scalar loop.
        emit(
            func,
            c2,
            AArch64Opcode::CmpRR,
            vec![vreg(end_of(bj.id)), vreg(*bi)],
        );
        emit(func, c2, AArch64Opcode::BCond, vec![imm(CC_LS), block(ok)]);
        emit(func, c2, AArch64Opcode::B, vec![block(rec.vec_guard)]);
        func.add_edge(c2, ok);
        func.add_edge(c2, rec.vec_guard);
    }
}

/// Lower `val` to a `.4S` (f32) NEON value for the current pair. `None` only on an
/// unexpected shape (recognition already proved lowerability).
fn lower_fill(func: &mut MachFunction, ctx: &mut FillLowerCtx, val: VReg) -> Option<VReg> {
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
    }
    // The induction cvt leaf ⇒ the current pair's `[(f32) index]` vector.
    if ctx.cvt_leaves.contains(&val.id) {
        ctx.memo.insert(val.id, ctx.vf);
        return Some(ctx.vf);
    }
    let &def_id = ctx.def.get(&val.id)?;
    if !ctx.loop_insts.contains(&def_id) {
        // loop-invariant f32 leaf ⇒ broadcast to all 4 lanes (once).
        let v = broadcast_fill(func, ctx, val);
        return Some(v);
    }
    let inst = func.inst(def_id);
    let opcode = inst.opcode;
    let ops = inst.operands.clone();
    use AArch64Opcode::*;
    let result = match opcode {
        FaddRR => {
            let (a, b) = lower_fill_two(func, ctx, &ops)?;
            fbin_s4(func, ctx, NeonFaddV, a, b)
        }
        FsubRR => {
            let (a, b) = lower_fill_two(func, ctx, &ops)?;
            fbin_s4(func, ctx, NeonFsubV, a, b)
        }
        FmulRR => {
            let (a, b) = lower_fill_two(func, ctx, &ops)?;
            fbin_s4(func, ctx, NeonFmulV, a, b)
        }
        FdivRR => {
            let (a, b) = lower_fill_two(func, ctx, &ops)?;
            fbin_s4(func, ctx, NeonFdivV, a, b)
        }
        FnegRR => {
            let a = lower_fill(func, ctx, vreg_of(&ops[1])?)?;
            let z = zero_vec_s4(func, ctx);
            fbin_s4(func, ctx, NeonFsubV, z, a)
        }
        _ => return None,
    };
    ctx.memo.insert(val.id, result);
    Some(result)
}

fn lower_fill_two(
    func: &mut MachFunction,
    ctx: &mut FillLowerCtx,
    ops: &[MachOperand],
) -> Option<(VReg, VReg)> {
    let a = lower_fill(func, ctx, vreg_of(ops.get(1)?)?)?;
    let b = lower_fill(func, ctx, vreg_of(ops.get(2)?)?)?;
    Some((a, b))
}

fn fbin_s4(
    func: &mut MachFunction,
    ctx: &FillLowerCtx,
    op: AArch64Opcode,
    a: VReg,
    b: VReg,
) -> VReg {
    let d = alloc(func, RegClass::Fpr128);
    emit(
        func,
        ctx.vbody,
        op,
        vec![vreg(d), vreg(a), vreg(b), imm(FARR_S4)],
    );
    d
}

/// Broadcast a loop-invariant f32 scalar to all 4 `.4S` lanes (once).
fn broadcast_fill(func: &mut MachFunction, ctx: &mut FillLowerCtx, val: VReg) -> VReg {
    if let Some(&v) = ctx.broadcast_cache.get(&val.id) {
        return v;
    }
    let d = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        ctx.preheader_term,
        AArch64Opcode::NeonDupElem,
        vec![vreg(d), vreg(val), imm(0), imm(ELEM_S)],
    );
    ctx.broadcast_cache.insert(val.id, d);
    d
}

fn zero_vec_s4(func: &mut MachFunction, ctx: &mut FillLowerCtx) -> VReg {
    if let Some(&v) = ctx.broadcast_cache.get(&u32::MAX) {
        return v;
    }
    let d = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        ctx.preheader_term,
        AArch64Opcode::NeonMovi,
        vec![vreg(d), imm(0)],
    );
    ctx.broadcast_cache.insert(u32::MAX, d);
    d
}

/// Materialize the constant `.4S` iota step `[0, 1, 2, 3]` in the preheader
/// (`MOVI Vd, #0` then `INS Vd.S[k], Wk` for k=1..3).
fn materialize_iota_step(func: &mut MachFunction, pre: InstId) -> VReg {
    let d = alloc(func, RegClass::Fpr128);
    emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(d), imm(0)]);
    for k in 1..VF_S {
        let c = alloc(func, RegClass::Gpr64);
        emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(c), imm(k)]);
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonInsGen,
            vec![vreg(d), vreg(c), imm(k), imm(ELEM_S)],
        );
    }
    d
}

/// Materialize a broadcast `.4S` i32 constant in the preheader
/// (`MOVZ Xn, #k` then `DUP Vd.4S, Wn`).
fn dup_const_i32_s4(func: &mut MachFunction, pre: InstId, k: i64) -> VReg {
    let c = materialize_const(func, pre, k, RegClass::Gpr64);
    let d = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonDupGen,
        vec![vreg(d), vreg(c), imm(ELEM_S)],
    );
    d
}

// ---------------------------------------------------------------------------
// Small local IR helpers
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

pub(crate) static FARRAY_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static FARRAY_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    if crate::neon_array::boi_timing_enabled() {
        let t = std::time::Instant::now();
        let r = build_def_map_inner(func);
        FARRAY_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        FARRAY_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return r;
    }
    build_def_map_inner(func)
}

fn build_def_map_inner(func: &MachFunction) -> HashMap<u32, InstId> {
    crate::effects::build_reaching_def_map(func)
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
