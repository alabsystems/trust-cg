// trust-cg-opt - SOUND NEON IV-synthesized FP-reduction vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON IV-synthesized FP-reduction vectorizer (`neon-fpred`)
//!
//! Vectorizes counted **floating-point reduction** loops whose per-iteration
//! term is a pure lane-wise FP dataflow of the induction variable and
//! loop-invariant scalars — no arrays, no memory:
//!
//! ```text
//! acc = 0.0;  for i in [i0, n):  acc += f(i)
//! ```
//!
//! where `f(i)` is a tree of `fadd / fsub / fmul / fdiv` and the FUSED
//! `fmadd / fmsub` (`llvm.fmuladd`) over the leaves `(double)i` (from
//! `UCVTF/SCVTF` of the integer induction) and **loop-invariant** `f64` scalars
//! (hoisted coefficients, parameters), and the reduction combines EITHER with a
//! PLAIN `FADD` (`acc = acc + f(i)` or `f(i) + acc`) — the *canonical* flops-5
//! tan-integral shape, >99 % of its runtime — OR as a FUSED accumulate
//! `acc = fmadd(n, m, acc)` (the accumulator in the ADDEND position;
//! `-ffp-contract=on` fuses `acc += n*m`), the *canonical* `flops-6/8` shape.
//! Both fold in WITHOUT reassociation (below).
//!
//! ## Why the result is BIT-IDENTICAL to the scalar loop
//!
//! The peril of vectorizing an FP reduction is REASSOCIATION: `(a+b)+(c+d)` is
//! not `((a+b)+c)+d` in IEEE-754, so a tree/parallel sum changes the last bits.
//! This pass NEVER reassociates the accumulation. It vectorizes ONLY the
//! INDEPENDENT per-lane computation of `f(i)` (2 lanes = `.2D` doubles, `UNROLL`
//! pairs per iteration), then folds the lane results into the SINGLE scalar
//! accumulator with ORDERED SCALAR `FADD`s IN THE ORIGINAL ITERATION ORDER —
//! `mov d, v.d[0]; fadd acc, acc, d; mov d, v.d[1]; fadd acc, acc, d; …` (the
//! [`AArch64Opcode::NeonDupScalarD`] lane extract + scalar `FADD`). The fadds
//! into `acc` therefore happen in exactly the scalar sequence
//! `acc += f(i); acc += f(i+1); …`, so NO reassociation occurs. This is clang
//! -O3's own emission for these kernels.
//!
//! For a FUSED accumulate `acc = fmadd(n, m, acc)` the vector body computes ONLY
//! the `n` and `m` multiplicand lanes (each a per-lane-exact op); the drain then
//! folds them in with ORDERED SCALAR FUSED `FMADD`s —
//! `mov dn, vn.d[k]; mov dm, vm.d[k]; fmadd acc, dn, dm, acc` — so each
//! iteration's contribution is the IDENTICAL single-rounded fused `acc + n(i)*
//! m(i)` the scalar loop performs, in the IDENTICAL order. The product+add
//! leaves the fused op ONLY under the `llvm.fmuladd` MAY_UNFUSE license AND the
//! `unfuse-serial-fma` pass's exact large-const-trip gate (which would split the
//! fused drain into the same rounding sequence anyway — see `drain_pair`); a
//! STRICT `llvm.fma` (no license) is never split (that would round twice — a
//! bit-level miscompile), so the result stays bit-exact either way.
//!
//! Two facts make each lane bit-identical:
//!
//! * **Per-lane ops match the scalar ops.** On A64 the NEON `FADD/FSUB/FMUL/
//!   FDIV .2D` and `FMLA/FMLS .2D` compute, per lane, the SAME IEEE operation
//!   (same FPCR, RNE default) as the scalar `S/D`-form ops. The scalar loop's
//!   `FMADD` (`llvm.fmuladd`, single rounding) is carried per lane by
//!   [`AArch64Opcode::NeonFmlaV`]/`NeonFmlsV` (also single rounding) — the fused
//!   contraction is PRESERVED, never split into `FMUL`+`FADD` (which would round
//!   twice and change bits).
//! * **`(double)i` is exact.** `UCVTF/SCVTF .2D` converts each integer lane to
//!   `f64` identically to the scalar `UCVTF/SCVTF`; the index lanes `[i, i+1]`
//!   are the exact integers the scalar loop feeds `uitofp/sitofp`.
//!
//! ## Why the transform is SOUND (memory/CFG)
//!
//! Purely additive, exactly like the sibling NEON passes: a vector main loop is
//! spliced in FRONT of the scalar loop, which is left byte-for-byte unchanged
//! and handles the `< width` tail. The vector loop touches no memory (register-
//! only term) and issues no call, so there is no aliasing or OOB surface. The
//! bounds guard admits a vector iteration only while `iv < n - (width-1)` (i64,
//! no overflow — `iv`, `n` are positive and `< 2^31`), so every processed index
//! `iv..iv+width-1` is an iteration the scalar loop also runs. A ROTATED (clang)
//! scalar tail is a do-while, sound only entered with `iv < n`; so when the
//! vector consumes ALL `n` (remainder 0, `iv == n`) the drain block branches to
//! the true loop exit instead of falling into the do-while (the remainder-0
//! hazard, see [`crate::neon_array`]).
//!
//! An in-loop `FNEG` in the term is NOT one of them and is REJECTED: there is no
//! `.2D` FNEG opcode here, and the `0.0 - x` stand-in this pass used to emit is
//! not bit-exact (it disagrees with FNEG on `x = +0.0` and on NaN — see the
//! comment on the missing `FnegRR` arm in [`lower`]).
//!
//! If ANY precondition fails — an `f32` accumulator or leaf, a non-unit step, a
//! store / call / unrecognized op, an in-loop `fneg`, a term leaf that is
//! neither the induction nor a loop-invariant `f64`, a fused accumulate whose
//! accumulator is a MULTIPLICAND rather than the addend
//! (`acc = fmadd(acc, _, _)`, a rounding-sensitive
//! multiply-recurrence), an extra live-out — the loop is left ENTIRELY to the
//! scalar path (`scalar_unroll`'s order-preserving SERIAL unroll is the
//! fallback). Fail-closed beats miscompile.
//!
//! Runs at O2/O3 immediately BEFORE `reduction_split`/`scalar_unroll` (so it gets
//! first shot at the FP-reduction loop). Disable with
//! `TRUST_CG_DISABLE_PASSES=neonfpred`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Lanes per NEON `.2D` (f64) unit.
const VF: i64 = 2;
/// Independent 2-lane pairs unrolled per vector iteration (`width = VF*UNROLL`
/// = 8 elements, matching clang -O3's flops emission).
const UNROLL: i64 = 4;
/// FP-op arrangement code for `.2D` (NeonFaddV/…/NeonFmlaV/NeonUcvtfV: 2=2D).
const FARR_D2: i64 = 2;
/// INTEGER-op arrangement code for `.2D` (NeonAddV on the i64 index vector).
const ARR_D2: i64 = 6;
/// NEON element-size operand code for `D` (64-bit) lanes (DUP/INS).
const ELEM_D: i64 = 8;
/// AArch64 condition code: signed less-than (`LT`).
const CC_LT: i64 = 11;
/// AArch64 condition code: signed greater-or-equal (`GE`).
const CC_GE: i64 = 10;
/// AArch64 condition code: equal (`EQ`).
const CC_EQ: i64 = 0;

/// The recognized reduction accumulate shape — determines the ORDERED SCALAR
/// DRAIN that folds the per-lane vector results back into the single scalar
/// accumulator WITHOUT reassociation.
#[derive(Clone, Copy)]
enum Reduction {
    /// `acc_src = FaddRR(acc, term)` (a PLAIN, commutative fadd). The vector
    /// body computes `term` per lane; the drain does, per lane in iteration
    /// order, `acc = acc + term_lane` (scalar `FADD`).
    Fadd { term: VReg },
    /// `acc_src = FmaddRR(n, m, acc)` — a FUSED accumulate with the accumulator
    /// in the ADDEND position (operand 3; `-ffp-contract=on` fuses `acc += n*m`).
    /// The vector body computes ONLY the `n` and `m` multiplicand DAGs per lane
    /// (each a per-lane-exact op); the drain does, per lane in iteration order,
    /// `acc = fmadd(n_lane, m_lane, acc)` — the IDENTICAL single-rounded fused op
    /// the scalar loop performs, in the IDENTICAL order. The product+add NEVER
    /// leaves the scalar fused op (splitting it into vector `FMUL` + scalar `FADD`
    /// would round twice — forbidden).
    Fmadd { n: VReg, m: VReg, may_unfuse: bool },
}

/// The `neon-fpred` machine pass.
#[derive(Default)]
pub struct NeonFPRedPass {
    fired: usize,
}

impl NeonFPRedPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }
    /// Loops vectorized in the last `run` (diagnostics/tests).
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonFPRedPass {
    fn name(&self) -> &str {
        "neon-fpred"
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

impl NeonFPRedPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;

        // Recognize read-only first; applying only ADDS blocks (never renumbers
        // existing ids or edits other loops), so recognized data stays valid.
        let mut plans = Vec::new();
        for lp in loops.all_loops() {
            if let Some(rec) = Recognized::recognize(func, dom, lp.header, lp.latch, &lp.body) {
                plans.push(rec);
            }
        }

        // Kill switch for the register-PRESSURE lowering tune (by-element FMLA
        // for invariant multiplicands, per-pair interleaved drain, chained pair
        // offsets). Off ⇒ the original broadcast/deferred-drain lowering.
        let pressure_tune = std::env::var("TRUST_CG_DISABLE_FPRED_PRESSURE_TUNE").is_err();

        let mut changed = false;
        for rec in plans {
            if apply(func, &rec, pressure_tune) {
                self.fired += 1;
                changed = true;
            }
        }
        if changed && std::env::var("TRUST_CG_DUMP_NEONFPRED").is_ok() {
            eprintln!("[neon-fpred] fn={} vectorized={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// A fully validated IV-synthesized FP-reduction loop.
struct Recognized {
    /// The vectorizer's preheader block (rotated: the loop's GUARD, which inits
    /// iv/acc and branches to the header). `emit_before(preheader_term, …)`
    /// materializes loop-invariant setup here.
    preheader_term: InstId,
    /// The block the fresh vector blocks are inserted BEFORE and that the vector
    /// exit falls into for the scalar tail (rotated: the loop HEADER).
    vec_guard: BlockId,
    /// The `preheader` block id (for CFG edge surgery at COMMIT).
    preheader: BlockId,
    /// The loop's true EXIT block (out-of-body target of the header exit test).
    /// The drain routes here when the vector consumes ALL `n` (remainder 0).
    exit: BlockId,
    /// Loop-carried induction register (`Gpr64`, `+1` each iteration).
    iv: VReg,
    /// Loop-carried FP accumulator (`Fpr64`).
    acc: VReg,
    /// The accumulator WRITEBACK SOURCE (`acc = acc_src` in the latch; = the
    /// header's `FaddRR` result). The rotated exit reads THIS (it leaves from
    /// the header before the latch copies it into `acc`).
    acc_src: VReg,
    /// The reduction accumulate shape + its per-iteration term root(s).
    reduction: Reduction,
    /// `true` = `UCVTF` (unsigned) induction→double; `false` = `SCVTF` (signed).
    unsigned_cvt: bool,
    /// Compile-time constant loop bound (`iv < bound`), reconstructed from the
    /// in-loop `Movz`/`Movk` chain (validated to `[1, i32::MAX]`).
    bound_const: i64,
    /// Global def map (`vreg id -> defining InstId`).
    def: HashMap<u32, InstId>,
    /// Instruction ids that live inside the loop body.
    loop_insts: HashSet<InstId>,
}

/// Opcodes permitted anywhere in the loop body. Anything else ⇒ BAIL (rules out
/// loads/stores/calls/atomics and any unmodeled effect).
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        // FP compute (the term dataflow).
        UcvtfRR | ScvtfRR | FmulRR | FaddRR | FsubRR | FdivRR | FmaddRR | FnegRR
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

/// `MovR/Copy/FmovFprFpr(d, s)` or `AddRI(d, s, 0)` copy idioms ⇒ `(d, s)`.
/// Handles the FP accumulator writeback (`FmovFprFpr`) as well as the GPR
/// induction writeback (`MovR`).
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

/// Constant value of `val` if defined by a `Movz`(+`Movk`) chain reaching a use.
/// Used to prove the `+1` step's addend register is exactly 1.
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
/// ```text
///   CmpRR(iv+1, bound)     ; the increment vs the bound (adjacent)
///   BCond(EQ|GE) -> exit   ; leave when iv+1 reaches the bound
/// ```
/// Returns `(bound_reg, exit_block, cmp_inst_id)`. Any deviation ⇒ None.
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
        return None; // must compare the STEP value (iv+1)
    }
    Some((vreg_of(&cmp.operands[1])?, exit, cmp_id))
}

impl Recognized {
    fn recognize(
        func: &MachFunction,
        _dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // (R1) exactly a 2-block innermost loop {header, latch}.
        if header == latch || body.len() != 2 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // (R2) whitelist every opcode in the loop body — no memory/call/etc.
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

        // (R3) header preds = {latch, guard}; re-root onto the guard (rotated).
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            return None;
        }
        let guard = *hpreds.iter().find(|&&b| b != latch)?;
        // The guard branches unconditionally into the header; make it the
        // vectorizer's preheader (splice the vector loop AFTER iv/acc init).
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

        // (R5) iv writeback = the one whose source is iv+1; acc = the other.
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
        // i64 induction, f64 accumulator only (f32 leaves/acc bail below).
        if iv.class != RegClass::Gpr64 || acc.class != RegClass::Fpr64 {
            return None;
        }

        // (R6) rotated header exit test + the compile-time bound.
        let (bound_raw, exit, cmp_id) = recognize_rotated_header_exit(func, header, body, iv_src)?;
        let bound_const = crate::reaching_const::unique_reaching_const(func, cmp_id, bound_raw)
            .filter(|k| (1..=i32::MAX as i64).contains(k))?;

        // (R7) reduction accumulate. TWO recognized shapes, both drained WITHOUT
        // reassociation (see the module docs):
        //   * PLAIN fadd `acc_src = FaddRR(acc, term)` / `FaddRR(term, acc)`
        //     (commutative) — drain folds `term` lanes with scalar FADD.
        //   * FUSED `acc_src = FmaddRR(n, m, acc)` — the accumulator MUST be the
        //     ADDEND (operand 3; `d = a + n*m`), i.e. `acc += n*m`. The drain
        //     folds `n`/`m` lanes with scalar FMADD (single-rounded, in order).
        // Anything else — incl. a fused op whose accumulator is a MULTIPLICAND
        // (`acc = fmadd(acc, _, _)`, a rounding-sensitive multiply-recurrence) —
        // ⇒ BAIL. Splitting or reassociating a contraction changes rounding.
        let acc_def = func.inst(*def.get(&acc_src.id)?);
        let reduction = match acc_def.opcode {
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
                Reduction::Fadd { term }
            }
            AArch64Opcode::FmaddRR if acc_def.operands.len() == 4 => {
                // `FmaddRR(d, n, m, a)` computes `d = a + n*m`. Require the
                // accumulator to be the ADDEND `a` (operand 3), and neither
                // multiplicand (operands 1/2) — `acc + n*m` is a pure add-into-acc
                // reduction, whereas `acc` as a factor is a scaling recurrence we
                // cannot fold without changing the result.
                let n = vreg_of(&acc_def.operands[1])?;
                let m = vreg_of(&acc_def.operands[2])?;
                let a = vreg_of(&acc_def.operands[3])?;
                if a != acc || n == acc || m == acc {
                    return None;
                }
                Reduction::Fmadd {
                    n,
                    m,
                    may_unfuse: acc_def.flags.contains(InstFlags::FMULADD_MAY_UNFUSE),
                }
            }
            _ => return None,
        };

        // (R8) acc read ONLY by the reduction inst inside the loop.
        let acc_reducer = *def.get(&acc_src.id)?;
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
            reduction,
            unsigned_cvt: true,
            bound_const,
            def,
            loop_insts,
        };

        // (R9) every term root must be lowerable per-lane (register-only f64
        // dataflow of the induction + loop-invariant f64 leaves). For a fused
        // accumulate, BOTH multiplicand DAGs `n` and `m` are validated (shared
        // subexpressions like `n == m` for `v*v` are tolerated by the `seen`
        // memo). Also fixes `unsigned_cvt`.
        let mut seen = HashSet::new();
        let mut saw_signed = false;
        let mut saw_unsigned = false;
        let roots_ok = match rec.reduction {
            Reduction::Fadd { term } => {
                rec.node_ok(func, term, &mut seen, &mut saw_signed, &mut saw_unsigned)
            }
            Reduction::Fmadd { n, m, .. } => {
                rec.node_ok(func, n, &mut seen, &mut saw_signed, &mut saw_unsigned)
                    && rec.node_ok(func, m, &mut seen, &mut saw_signed, &mut saw_unsigned)
            }
        };
        if !roots_ok {
            return None;
        }
        if saw_signed && saw_unsigned {
            return None; // mixed cvt kinds on the same induction — bail
        }
        rec.unsigned_cvt = !saw_signed;

        // (R10) no other live-outs than {iv, iv_src, acc, acc_src}: every other
        // body-defined vreg must be body-local (else a term intermediate could be
        // read stale when the vector consumes all n and the tail runs 0 times).
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

    /// Read-only feasibility mirroring [`lower`]: every reachable node is the
    /// induction (via `UCVTF/SCVTF`), a loop-invariant `f64`, or an allowed
    /// lane-wise `f64` op over such. Records which cvt kind(s) the induction
    /// flows through.
    fn node_ok(
        &self,
        func: &MachFunction,
        val: VReg,
        seen: &mut HashSet<u32>,
        saw_signed: &mut bool,
        saw_unsigned: &mut bool,
    ) -> bool {
        if val.class != RegClass::Fpr64 {
            return false; // f32/f16 leaves & intermediates bail (only .2D f64)
        }
        if !seen.insert(val.id) {
            return true; // already validated
        }
        let Some(&def_id) = self.def.get(&val.id) else {
            return false;
        };
        if !self.loop_insts.contains(&def_id) {
            // Defined OUTSIDE the loop body ⇒ a loop-invariant f64 leaf
            // (broadcast once). This is the induction-invariant separation.
            return true;
        }
        let inst = func.inst(def_id);
        use AArch64Opcode::*;
        match inst.opcode {
            UcvtfRR | ScvtfRR => {
                // The single induction leaf: convert of the loop-carried iv.
                if vreg_of(&inst.operands[1]) != Some(self.iv) {
                    return false;
                }
                if inst.opcode == UcvtfRR {
                    *saw_unsigned = true;
                } else {
                    *saw_signed = true;
                }
                true
            }
            FmulRR | FaddRR | FsubRR | FdivRR => {
                let a = match vreg_of(&inst.operands[1]) {
                    Some(v) => v,
                    None => return false,
                };
                let b = match vreg_of(&inst.operands[2]) {
                    Some(v) => v,
                    None => return false,
                };
                self.node_ok(func, a, seen, saw_signed, saw_unsigned)
                    && self.node_ok(func, b, seen, saw_signed, saw_unsigned)
            }
            FmaddRR if inst.operands.len() == 4 => {
                // d = a + n*m — the fused contraction (per-lane preserved).
                let n = vreg_of(&inst.operands[1]);
                let m = vreg_of(&inst.operands[2]);
                let a = vreg_of(&inst.operands[3]);
                match (n, m, a) {
                    (Some(n), Some(m), Some(a)) => {
                        self.node_ok(func, n, seen, saw_signed, saw_unsigned)
                            && self.node_ok(func, m, seen, saw_signed, saw_unsigned)
                            && self.node_ok(func, a, seen, saw_signed, saw_unsigned)
                    }
                    _ => false,
                }
            }
            // FnegRR is deliberately ABSENT (fail-closed, see the `lower`
            // comment): there is no `.2D` FNEG in this backend's opcode set and
            // the `0.0 - x` substitution that used to stand in for one is NOT
            // bit-exact — it differs from FNEG on x = +0.0 (FNEG gives -0.0,
            // `0.0 - 0.0` gives +0.0 under RNE) and on x = NaN (FNEG flips the
            // sign bit, FSUB returns the quieted operand with its sign kept).
            // A term containing an in-loop negation is therefore left ENTIRELY
            // to the scalar path.
            _ => false,
        }
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

// ---------------------------------------------------------------------------
// Transformation
// ---------------------------------------------------------------------------

/// Per-lowering context.
struct LowerCtx {
    iv: VReg,
    /// The current pair's converted double-index vector `[（double)(iv+2k),
    /// (double)(iv+2k+1)]` (returned when lowering `UCVTF/SCVTF(iv)`).
    vfi: VReg,
    vbody: BlockId,
    preheader_term: InstId,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// Per-pair cache of lowered iv-dependent values (reset each pair).
    memo: HashMap<u32, VReg>,
    /// Persistent cache of loop-invariant `f64` broadcasts (`DUP Vd.2D, Vr.D[0]`).
    broadcast_cache: HashMap<u32, VReg>,
    /// Register-PRESSURE tune (see `TRUST_CG_DISABLE_FPRED_PRESSURE_TUNE`):
    /// lower an in-loop `FMADD` whose single invariant multiplicand would need a
    /// dedicated broadcast register as the by-element `FMLA Vd, Vstream,
    /// Vinv.D[0]` instead — reading lane 0 of the invariant's OWN scalar FPR.
    /// Bit-identical (the lane broadcast reads the same f64; the fused single
    /// rounding is unchanged — the proven `neon_fmap` da-scalar pattern), but
    /// frees one live `.2D` broadcast per distinct invariant multiplicand.
    lane_fmla: bool,
}

/// The per-pair lowered term root(s), collected in iteration order before the
/// ordered scalar drain folds them into the accumulator.
enum LoweredPair {
    /// PLAIN fadd: the single lowered `term` vector for this pair.
    Fadd(VReg),
    /// FUSED accumulate: the lowered `n` and `m` multiplicand vectors — the
    /// product+add itself stays SCALAR + FUSED in the drain.
    Fmadd(VReg, VReg),
}

fn apply(func: &mut MachFunction, rec: &Recognized, pressure_tune: bool) -> bool {
    let width = VF * UNROLL; // lanes per vector iteration (8)
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    insert_new_blocks_before(func, rec.vec_guard, &[vh, vb, vl, vx]);
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: materialize the constant bound + `main_bound = bound -
    // (width-1)` (i64, exact) and seed a FRESH scalar accumulator `svec = 0.0`.
    let bound = materialize_const(func, pre, rec.bound_const, RegClass::Gpr64);
    let main_bound = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::SubRI,
        vec![vreg(main_bound), vreg(bound), imm(width - 1)],
    );
    let wz = alloc(func, RegClass::Gpr64);
    emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(wz), imm(0)]);
    let svec = alloc(func, RegClass::Fpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::FmovGprFpr,
        vec![vreg(svec), vreg(wz)],
    );

    // --- Preheader: the i64 index-vector scheme.
    //
    // UNTUNED (`TRUST_CG_DISABLE_FPRED_PRESSURE_TUNE`): a loop-CARRIED
    // `vidx0 = [iv, iv+1]` Q advanced by `vstep = [width, width]` each
    // iteration, plus `UNROLL-1` absolute per-pair offset constants
    // `voff[k] = [2k, 2k]`.
    //
    // PRESSURE tune (default): NO loop-carried Q — the vector body RECOMPUTES
    // `[iv, iv+1]` each iteration from the live scalar induction
    // (`DUP Vd.2D, Xiv` + the `[0, 1]` constant) and chains the pairs with ONE
    // `[VF, VF]` constant (`vi_k = vi_{k-1} + [2, 2]`). The lane values are
    // IDENTICAL (exact i64: `dup(iv) + [0,1] = [iv, iv+1]`; the chained adds
    // reach the same `iv+2k`, `iv+2k+1`), but only TWO invariant `.2D`
    // constants stay live across the loop — no advance step, no carried vector
    // register to spill/writeback (measured: the carried Q + its step were
    // spill-reloaded every iteration on the flops polynomial kernels).
    let mut carried: Option<(VReg, VReg)> = None; // (vidx0, vstep) — untuned
    let mut c01: Option<VReg> = None; // [0, 1] — tuned body recompute
    let voff: Vec<VReg> = if pressure_tune {
        let d = alloc(func, RegClass::Fpr128);
        emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(d), imm(0)]);
        let one = alloc(func, RegClass::Gpr64);
        emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(one), imm(1)]);
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonInsGen,
            vec![vreg(d), vreg(one), imm(1), imm(ELEM_D)],
        );
        c01 = Some(d);
        vec![dup_const_i64_pre(func, pre, VF)]
    } else {
        let vidx0 = alloc(func, RegClass::Fpr128);
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonDupGen,
            vec![vreg(vidx0), vreg(rec.iv), imm(ELEM_D)],
        );
        let iv_p1 = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::AddRI,
            vec![vreg(iv_p1), vreg(rec.iv), imm(1)],
        );
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonInsGen,
            vec![vreg(vidx0), vreg(iv_p1), imm(1), imm(ELEM_D)],
        );
        let vstep = dup_const_i64_pre(func, pre, width);
        carried = Some((vidx0, vstep));
        (0..UNROLL)
            .map(|k| {
                if k == 0 {
                    vidx0 // placeholder (pair 0 uses vidx0 directly)
                } else {
                    dup_const_i64_pre(func, pre, VF * k)
                }
            })
            .collect()
    };

    // --- Vector header: guard `iv < main_bound` (i64 signed; iv,bound positive).
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LT), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Vector body: for each pair, convert its index lanes and lower the term;
    // then drain all lane results into `svec` in ITERATION ORDER.
    //
    // PRESSURE tune: the body first recomputes `vi_0 = [iv, iv+1]` from the
    // live scalar induction (`DUP Vd.2D, Xiv` + `[0, 1]`) — no loop-carried Q.
    let vi_base = if pressure_tune {
        let dupv = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonDupGen,
            vec![vreg(dupv), vreg(rec.iv), imm(ELEM_D)],
        );
        let vi0 = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonAddV,
            vec![
                vreg(vi0),
                vreg(dupv),
                vreg(c01.expect("tuned scheme materializes [0,1]")),
                imm(ARR_D2),
            ],
        );
        vi0
    } else {
        carried.expect("untuned scheme carries vidx0").0
    };
    let mut ctx = LowerCtx {
        iv: rec.iv,
        vfi: vi_base, // overwritten per pair
        vbody: vb,
        preheader_term: pre,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        memo: HashMap::new(),
        broadcast_cache: HashMap::new(),
        lane_fmla: pressure_tune,
    };
    let cvt_op = if rec.unsigned_cvt {
        AArch64Opcode::NeonUcvtfV
    } else {
        AArch64Opcode::NeonScvtfV
    };
    // UN-FUSED drain decision for the FUSED accumulate — EXACTLY the
    // `unfuse-serial-fma` pass's semantic + profitability gates, decided inline
    // so the split products can be computed as vector `FMUL.2D` (one per pair)
    // instead of that pass's post-hoc scalar `FMUL` per lane:
    //   * the source `llvm.fmuladd` carries the MAY_UNFUSE license,
    //   * un-fusing is globally enabled (`TCG_NO_UNFUSE_SERIAL_FMA` not set),
    //   * the (always compile-time) trip bound meets the SAME large-const gate
    //     (`TCG_UNFUSE_FMA_MIN_CONST_TRIP`) — small trips stay FUSED, exactly
    //     as `unfuse-serial-fma` would leave them.
    // The resulting per-element rounding sequence is bit-identical to letting
    // `unfuse-serial-fma` split the fused drain (see [`drain_pair`]).
    let unfuse_drain = pressure_tune
        && matches!(
            rec.reduction,
            Reduction::Fmadd {
                may_unfuse: true,
                ..
            }
        )
        && crate::unfuse_serial_fma::serial_unfuse_enabled()
        && rec.bound_const >= crate::unfuse_serial_fma::serial_unfuse_min_const_trip();
    let mut terms: Vec<LoweredPair> = Vec::with_capacity(UNROLL as usize);
    let mut prev_vi = vi_base;
    for k in 0..UNROLL {
        // vi_k = vi_base + [2k, 2k]  (pair 0 = vi_base). PRESSURE tune: chain
        // `vi_k = vi_{k-1} + [VF, VF]` — identical lane values, one live
        // offset constant instead of `UNROLL-1`.
        let vi_k = if k == 0 {
            vi_base
        } else {
            let d = alloc(func, RegClass::Fpr128);
            let (base, off) = if pressure_tune {
                (prev_vi, voff[0])
            } else {
                (vi_base, voff[k as usize])
            };
            emit(
                func,
                vb,
                AArch64Opcode::NeonAddV,
                vec![vreg(d), vreg(base), vreg(off), imm(ARR_D2)],
            );
            d
        };
        prev_vi = vi_k;
        // vfi_k = cvt(vi_k) = [(double)(iv+2k), (double)(iv+2k+1)].
        let vfi = alloc(func, RegClass::Fpr128);
        emit(func, vb, cvt_op, vec![vreg(vfi), vreg(vi_k), imm(FARR_D2)]);
        ctx.vfi = vfi;
        ctx.memo.clear();
        // Lower the per-iteration term root(s) per lane. For a fused accumulate,
        // ONLY the multiplicand DAGs `n`/`m` are vectorized — the top-level
        // `acc + n*m` fusion is drained scalar+fused below (never split). `n` and
        // `m` share the SAME pair memo, so a shared subexpression (e.g. `n == m`
        // for `v*v`) is lowered once.
        let pair = match rec.reduction {
            Reduction::Fadd { term } => {
                let Some(vterm) = lower(func, &mut ctx, term) else {
                    return false;
                };
                LoweredPair::Fadd(vterm)
            }
            Reduction::Fmadd { n, m, .. } => {
                let Some(vn) = lower(func, &mut ctx, n) else {
                    return false;
                };
                let Some(vm) = lower(func, &mut ctx, m) else {
                    return false;
                };
                LoweredPair::Fmadd(vn, vm)
            }
        };
        if pressure_tune {
            // PRESSURE tune: drain pair `k` IMMEDIATELY (before pair `k+1` is
            // lowered). The scalar fold sequence on `svec` is IDENTICAL — pair
            // order, then lane order, exactly as the deferred drain below — so
            // the FP result is bit-identical; only instruction PLACEMENT moves,
            // ending each pair's `n`/`m` vector live ranges early instead of
            // keeping all `2*UNROLL` lowered vectors live until a final drain.
            drain_pair(func, vb, svec, &pair, &rec.reduction, unfuse_drain);
        } else {
            terms.push(pair);
        }
    }
    // Advance the running index vector once (UNTUNED only — the tuned body
    // recomputes it from the scalar induction each iteration).
    if let Some((vidx0, vstep)) = carried {
        emit(
            func,
            vb,
            AArch64Opcode::NeonAddV,
            vec![vreg(vidx0), vreg(vidx0), vreg(vstep), imm(ARR_D2)],
        );
    }
    // ORDERED SCALAR DRAIN — the bit-exactness linchpin. For every pair, in
    // order, extract lane 0 then lane 1 and fold into `svec` with the SAME scalar
    // op the reduction uses:
    //   * PLAIN  `acc += term`  ⇒  scalar `FADD  svec, svec, term_lane`.
    //   * FUSED  `acc += n*m`   ⇒  scalar `FMADD svec, n_lane, m_lane, svec`
    //     (single-rounded fused op, IDENTICAL to the scalar loop's per iteration).
    // This reproduces `acc (+)= f(iv); acc (+)= f(iv+1); …` in ORIGINAL order —
    // no reassociation, no double rounding.
    //
    // (PRESSURE tune: `terms` is empty — every pair was already drained in-place
    // by the SAME per-pair fold, in the SAME pair-then-lane order.)
    for pair in &terms {
        drain_pair(func, vb, svec, pair, &rec.reduction, unfuse_drain);
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
    // partial sum — NO arithmetic, bit-exact) for BOTH the scalar tail (acc) and
    // the true-exit live-out (acc_src), then guard the rotated do-while tail
    // against remainder 0 (`iv == bound` ⇒ branch to the true exit; else FALL
    // THROUGH to the header do-while with `acc = svec`, `iv = vector_end`).
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
    emit(
        func,
        vx,
        AArch64Opcode::BCond,
        vec![imm(CC_GE), block(rec.exit)],
    );

    // --- COMMIT: splice the vector loop in front of the scalar loop.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.vec_guard, vh) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.vec_guard);
    func.add_edge(rec.preheader, vh);
    func.add_edge(vx, rec.vec_guard);
    func.add_edge(vx, rec.exit);
    true
}

/// Drain ONE lowered pair into the scalar accumulator, LANE 0 THEN LANE 1 —
/// the per-pair step of the ORDERED SCALAR DRAIN (see the drain comment in
/// [`apply`]): scalar `FADD` for the plain reduction, and for the fused
/// accumulate either
///
///   * `unfuse_drain == false`: the scalar FUSED `FMADD` per lane (single
///     rounding preserved; `may_unfuse` license forwarded so the
///     `unfuse-serial-fma` pass can still make its own call), or
///   * `unfuse_drain == true` (license + the SAME large-const-trip gate the
///     `unfuse-serial-fma` pass applies — decided in [`apply`]): the UN-FUSED
///     evaluation `t = n*m; acc = acc + t` with the products computed as ONE
///     vector `FMUL.2D` per pair. Per lane this is `round(n_l*m_l)` then the
///     ordered scalar `FADD` — BIT-IDENTICAL to what `unfuse-serial-fma` makes
///     of the fused drain (its split emits the same rounding sequence in the
///     same order), but with 2 scalar `FMUL`s + 2 extra lane extracts replaced
///     by one off-chain vector multiply (matching clang's drain shape).
fn drain_pair(
    func: &mut MachFunction,
    vb: BlockId,
    svec: VReg,
    pair: &LoweredPair,
    reduction: &Reduction,
    unfuse_drain: bool,
) {
    if let LoweredPair::Fmadd(vn, vm) = *pair
        && unfuse_drain
    {
        let vt = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonFmulV,
            vec![vreg(vt), vreg(vn), vreg(vm), imm(FARR_D2)],
        );
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
        return;
    }
    for lane in 0..VF {
        match *pair {
            LoweredPair::Fadd(vterm) => {
                let d = alloc(func, RegClass::Fpr64);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonDupScalarD,
                    vec![vreg(d), vreg(vterm), imm(lane)],
                );
                emit(
                    func,
                    vb,
                    AArch64Opcode::FaddRR,
                    vec![vreg(svec), vreg(svec), vreg(d)],
                );
            }
            LoweredPair::Fmadd(vn, vm) => {
                let dn = alloc(func, RegClass::Fpr64);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonDupScalarD,
                    vec![vreg(dn), vreg(vn), imm(lane)],
                );
                let dm = alloc(func, RegClass::Fpr64);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonDupScalarD,
                    vec![vreg(dm), vreg(vm), imm(lane)],
                );
                // svec = svec + dn*dm  (scalar FMADD: d = a + n*m, a = svec).
                let fmadd = emit(
                    func,
                    vb,
                    AArch64Opcode::FmaddRR,
                    vec![vreg(svec), vreg(dn), vreg(dm), vreg(svec)],
                );
                if matches!(
                    reduction,
                    Reduction::Fmadd {
                        may_unfuse: true,
                        ..
                    }
                ) {
                    func.inst_mut(fmadd)
                        .flags
                        .insert(InstFlags::FMULADD_MAY_UNFUSE);
                }
            }
        }
    }
}

/// `val` is a loop-invariant leaf: defined OUTSIDE the loop body (recognition
/// requires every reachable node to have a def, so the entry always exists).
fn is_loop_invariant(ctx: &LowerCtx, val: VReg) -> bool {
    match ctx.def.get(&val.id) {
        Some(d) => !ctx.loop_insts.contains(d),
        None => false,
    }
}

/// Lower `val` to a `.2D` (f64) NEON value in the vector body. `None` only on an
/// unexpected shape (recognition already proved lowerability).
fn lower(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> Option<VReg> {
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
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
        UcvtfRR | ScvtfRR => {
            if vreg_of(&ops[1])? != ctx.iv {
                return None;
            }
            ctx.vfi
        }
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
            // d = a + n*m (fused). Copy the addend into a fresh Vd, then
            // FMLA Vd, Vn, Vm — the SAME single rounding per lane.
            let n_raw = vreg_of(&ops[1])?;
            let m_raw = vreg_of(&ops[2])?;
            let a_raw = vreg_of(&ops[3])?;
            // PRESSURE tune: when exactly ONE multiplicand is a loop-invariant
            // scalar (e.g. the leading polynomial coefficient in `A6*w + A5`),
            // read it straight from lane 0 of its OWN FPR via the by-element
            // `FMLA Vd, Vstream, Vinv.D[0]` — no `DUP` broadcast, no dedicated
            // broadcast register held across the loop. The product is
            // COMMUTATIVE and the lane-0 read is bit-identical to the DUP
            // broadcast, so the fused SINGLE rounding is unchanged (the proven
            // `neon_fmap` da-scalar pattern). Falls back to the DUP-broadcast
            // `NeonFmlaV` when neither or BOTH multiplicands are invariant.
            let lane_form = if ctx.lane_fmla {
                match (is_loop_invariant(ctx, n_raw), is_loop_invariant(ctx, m_raw)) {
                    (true, false) => Some((n_raw, m_raw)), // n = invariant scalar
                    (false, true) => Some((m_raw, n_raw)), // m = invariant scalar
                    _ => None,
                }
            } else {
                None
            };
            if let Some((inv, stream_raw)) = lane_form {
                let stream = lower(func, ctx, stream_raw)?;
                let a = lower(func, ctx, a_raw)?;
                let vd = alloc(func, RegClass::Fpr128);
                emit(func, ctx.vbody, NeonOrrV, vec![vreg(vd), vreg(a), vreg(a)]);
                emit(
                    func,
                    ctx.vbody,
                    NeonFmlaLaneV,
                    vec![vreg(vd), vreg(stream), vreg(inv), imm(0), imm(FARR_D2)],
                );
                vd
            } else {
                // Untuned/fallback: the ORIGINAL n, m, a lowering order (kept
                // exactly so `TRUST_CG_DISABLE_FPRED_PRESSURE_TUNE=1` codegen
                // is byte-identical to the pre-tune pass).
                let n = lower(func, ctx, n_raw)?;
                let m = lower(func, ctx, m_raw)?;
                let a = lower(func, ctx, a_raw)?;
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
        }
        // NO `FnegRR` ARM. This used to lower `-x` per lane as `0.0 - x`
        // (`NeonMovi Vz,#0` + `NeonFsubV Vd, Vz, Vx`) on the claim that it was a
        // "bit-exact fneg". IT IS NOT — `0.0 - x == -x` fails in IEEE-754 for two
        // operand classes `node_ok` freely admitted:
        //
        //   * x = +0.0 — `FNEG` yields -0.0, but `(+0.0) - (+0.0)` yields +0.0
        //     under round-to-nearest (a zero difference is +0 unless the rounding
        //     mode is toward -inf). The sign of a zero is observable: `1.0/(-0.0)`
        //     is -inf while `1.0/(+0.0)` is +inf.
        //   * x = NaN — `FNEG` is a pure sign-bit flip, while `FSUB` returns the
        //     (quieted) NaN operand with its ORIGINAL sign.
        //
        // There is no `.2D` FNEG opcode in this backend to substitute, so the
        // shape is now rejected in `node_ok` and the loop is left to the scalar
        // path. This arm is kept absent so `lower` and `node_ok` stay mirrored.
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

/// Emit `d = op(a, b)` (`.2D` FP three-same) in the vector body.
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

/// Broadcast a loop-invariant `f64` scalar to both `.2D` lanes (`DUP Vd.2D,
/// Vr.D[0]`), materialized once per invariant in the preheader.
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

/// Materialize a broadcast `.2D` i64 constant in the preheader (`DUP Vd.2D, Xn`).
fn dup_const_i64_pre(func: &mut MachFunction, pre: InstId, value: i64) -> VReg {
    let x = alloc(func, RegClass::Gpr64);
    let v = alloc(func, RegClass::Fpr128);
    emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(x), imm(value)]);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonDupGen,
        vec![vreg(v), vreg(x), imm(ELEM_D)],
    );
    v
}

/// Materialize a compile-time constant into a fresh reg before `pre` via the
/// isel `Movz`(+`Movk #hi, lsl #16`) convention (bound is validated `[1, 2^31)`).
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

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
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
