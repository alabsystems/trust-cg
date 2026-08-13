// trust-cg-opt - SOUND NEON conditional-store (predicated-map) vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON conditional-store vectorizer (`neon-condstore`)
//!
//! Vectorizes the counted **conditional-store** loop
//!
//! ```text
//! for i in 0..n (signed i < n):  if (P(a[i]))  b[i] = F(a[i], ...)
//! ```
//!
//! — a store that the scalar loop performs **only on the lanes where the
//! predicate `P` holds**. `a, b, ...` are pointers, `P` is a lane-wise integer
//! relation (`< <= > >= == ` signed/unsigned) over the loaded `i32` elements /
//! 16-bit constants / loop-invariant scalars, and `F` is a lane-wise integer
//! function of the same leaves using `+ - * & | ^ << >>` (plus `madd`).
//!
//! This is the class **both clangs give up on**: their vectorizer reports a
//! vector factor but then emits *lane-scalarised branch-per-lane* code, because
//! C11 forbids inventing a store to a lane the source did not write (another
//! agent could own it) and NEON has **no masked store**. trust-cg wins it under
//! an explicit contract (below) by lowering to a **blind full-width store**.
//!
//! ## The transform — the blind store
//!
//! Per `VF = 4`-lane block the vector body computes, for **every** lane,
//!
//! ```text
//!   b[i] = P(a[i]) ? F(a[i]) : b[i]          // OLD b[i] written back on false lanes
//! ```
//!
//! as: `mask = CMxx(a lanes)` (all-ones exactly on the lanes that store),
//! `value = F(a lanes)`, `old = LD1 b lanes`, `merged = BIT(old, value, mask)`
//! (the proven tied-def bit-insert `merged = (old & ~mask) | (value & mask)`),
//! then **one** full-width `ST1`/`STP` of `merged`. The `UNROLL = 4` sub-blocks
//! are stored in `STP` pairs, exactly like [`crate::neon_map`]. The original
//! scalar loop handles the `< 16` tail unchanged.
//!
//! ## Why this is SOUND — and the CONTRACT it needs (read this carefully)
//!
//! Like every sibling neon pass the transform is **purely additive**: it splices
//! a vector main loop in front of the untouched scalar loop, so the scalar loop
//! is correct by construction and only the vector body needs justifying. Two
//! facts do the per-lane VALUE equality, and one CONTRACT covers the extra
//! memory effect:
//!
//! * **Per-lane value equality.** The vector guard enters the body only when
//!   `sext(iv) + 15 < sext(n)` (i64 arithmetic on the sign-extended i32 bounds,
//!   no overflow), so every lane index `iv..iv+15 < n` — an index the scalar
//!   loop also visits. On each lane `mask` is `0xFFFF_FFFF` exactly when the
//!   scalar predicate holds (the faithfully-proven NEON compare, with operands
//!   swapped / polarity inverted so all-ones ⟺ *the scalar stores*), `value` is
//!   `F` mapped op-for-op onto the per-lane-proven `.4S` ops, and
//!   `BIT(old, value, mask)` yields `value` on the true lanes and the **loaded
//!   old** `b[i]` on the false lanes. So on a true lane the vector writes exactly
//!   the scalar's stored value; on a false lane it writes back the value already
//!   there.
//!
//! * **The load of `b` and computing `F` on false lanes never trap.** `b[iv..)`
//!   is in bounds (guard) and, per the contract below, writable — hence readable.
//!   `F` is restricted to **non-trapping** lane-wise arithmetic (the op
//!   whitelist excludes division and every side-effecting op), so evaluating it
//!   on a false lane and discarding the result via `BIT` is safe.
//!
//! * **THE CONTRACT — writable + single-owner range (the crux).** On a false
//!   lane the vector loop *stores* `b[i]` where the scalar loop stored *nothing*.
//!   Writing back the identical value is a no-op only if **no other agent can
//!   observe it**: the whole `b[0..n)` range must be (a) writable memory and
//!   (b) exclusively owned by this thread for the loop's duration (no concurrent
//!   reader that a spurious store could race, and — decisively — no concurrent
//!   *writer* whose store between our load and our write-back we would clobber).
//!   trust-ir HAS atomics, so a data race is *not* assumed unobservable; the
//!   contract must be **explicit**, never inferred. `noalias` alone does NOT
//!   supply it (it only asserts `b` is disjoint from the other params, not that
//!   the whole range is writable or unshared), so this pass requires **both**:
//!
//!     1. an exact validator-replayed writable + single-owner capability bound
//!        to this function, output base, and byte range. The current public
//!        TrustIR/MachIR channels do not carry such a capability, so production
//!        does not schedule this pass. In particular, neither an environment
//!        variable nor the generic guard-replay availability bit is an ownership
//!        capability; and
//!     2. the SAME aliasing disjointness [`crate::neon_map`] proves, so a store
//!        through `b` cannot clobber a not-yet-read input: either the
//!        **single-array in-place** case (`b` is the only pointer touched — the
//!        stored array is also the (only) loaded one, at the same index) which
//!        needs no `noalias`, or the **multi-pointer** case where the store base
//!        and every distinct input base root at *distinct* `noalias` params.
//!        Without a provable disjointness (e.g. a raw two-pointer form with no
//!        `noalias`, so `a` and `b` might overlap) the loop stays scalar.
//!
//! ## Fail-closed guards (BAIL preconditions)
//!
//! Anything below leaves the loop entirely scalar: the validator-issued
//! ownership capability is unavailable;
//! aliasing unprovable; the loop is not the recognized counted diamond
//! (`header` counted `i<n` test, a `then` block holding the *single* store,
//! reconverging at the latch); step != +1; the predicate is not a single
//! decodable relation (`!=` has no single all-ones NEON mask ⇒ BAIL); the store
//! address is not the width's `base + idx*elem` shape; any leaf of `P`/`F` is
//! the induction, an un-recognized load, or an unmodeled op; a second store /
//! call / atomic / division / any non-whitelisted opcode in the body; a MIXED
//! width (`Gpr32`/`Gpr64` carried values must agree). Fail-closed beats
//! miscompile.
//!
//! ## Widths
//!
//! `i32` (`.4S`, 16 lanes/iteration) and `i64` (`.2D`, 8 lanes/iteration). The
//! i64 mirror changes only mechanics, not the argument: `BIT` is
//! lane-width-agnostic whole-register logic, the five compares have proven
//! `.2D` forms (the width-parameterization arc), the loads/stores are the same
//! `LDP`/`STP` Q-register walk (8 x i64 = 64 bytes/iteration), the address
//! shape is `base + iv*8` (the index is already 64-bit — no `sxtw`), and the
//! bounds guard is the i64 precheck + unsigned form
//! (`n < 8 -> all-scalar`, then `iv <u n - 7`; see `neon_array::apply_i64` for
//! the wrap-freedom argument). The CONTRACT is width-independent — both widths
//! require the same exact validator-replayed writable/single-owner capability
//! plus the same `noalias` disjointness proof. Because no such typed capability
//! is wired today, the public pass is inert for both widths; the private
//! test-only structural runner exercises the implementation without granting
//! production authority. The transform itself stays purely additive (the
//! scalar loop is never edited).

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::MachinePass;

/// Lanes per NEON iteration (`4 x i32`).
const VF: i64 = 4;
/// Lanes per NEON iteration for the i64 (`.2D`) path (`2 x i64`).
const VF_I64: i64 = 2;
/// NEON element-size operand code for `S` (32-bit) lanes.
const ELEM_S: i64 = 4;
/// NEON element-size operand code for `D` (64-bit) lanes.
const ELEM_D: i64 = 8;
/// NEON arrangement operand code for `.4S`.
const ARR_S4: i64 = 5;
/// NEON arrangement operand code for `.2D`.
const ARR_D2: i64 = 6;
/// Byte size of an `i32` array element.
const ELEM_BYTES: i64 = 4;
/// Byte size of an `i64` array element (`.2D` path).
const ELEM_BYTES_I64: i64 = 8;
/// Independent vector registers per vector iteration (`UNROLL * VF` lanes).
const UNROLL: usize = 4;

// AArch64 condition codes (imm operands of BCond/CSet/Csel).
const CC_EQ: i64 = 0;
const CC_NE: i64 = 1;
const CC_HS: i64 = 2;
const CC_LO: i64 = 3;
const CC_HI: i64 = 8;
const CC_LS: i64 = 9;
const CC_GE: i64 = 10;
/// AArch64 condition code for signed less-than (`LT`) — the counted-loop exit.
const CC_LT: i64 = 11;
const CC_GT: i64 = 12;
const CC_LE: i64 = 13;

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `neon-condstore` machine pass.
#[derive(Default)]
pub struct NeonCondStorePass {
    fired: usize,
}

impl NeonCondStorePass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }

    /// Exercise the structural transform in this module's unit tests. This is
    /// deliberately private and test-only: it is not an authority seam and
    /// cannot be reached by a production optimization pipeline.
    #[cfg_attr(not(test), allow(dead_code))]
    fn run_with_structural_test_authority(&mut self, func: &mut MachFunction) -> bool {
        self.fired = 0;
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);

        // Recognize read-only first; applying a plan only *adds* blocks (never
        // renumbers existing ids or edits other loops), so recognized data for
        // other loops stays valid.
        let mut plans = Vec::new();
        for lp in loops.all_loops() {
            if let Some(rec) = Recognized::recognize(func, &dom, lp.header, lp.latch, &lp.body) {
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
        if changed && std::env::var("TRUST_CG_DUMP_NEONCONDSTORE").is_ok() {
            eprintln!(
                "[neon-condstore] fn={} vectorized={}",
                func.name, self.fired
            );
        }
        changed
    }
}

impl MachinePass for NeonCondStorePass {
    fn name(&self) -> &str {
        "neon-condstore"
    }

    fn run(&mut self, _func: &mut MachFunction) -> bool {
        // No TrustIR/MachIR field currently carries a validator-replayed,
        // function/value/range-bound writable+single-owner capability. Keep the
        // public pass inert until that typed evidence exists. A process-global
        // guard-replay bit or environment spelling must never authorize blind
        // stores for an unrelated buffer.
        self.fired = 0;
        false
    }
}

// ---------------------------------------------------------------------------
// Predicate decode
// ---------------------------------------------------------------------------

/// A decoded lane-wise predicate normalized to a single NEON compare whose
/// result is **all-ones per lane exactly when the scalar loop STORES that lane**.
#[derive(Clone, Copy)]
struct PredPlan {
    cmp_op: AArch64Opcode,
    /// Compare LHS (already operand-swapped for `<`/`<=` orderings).
    lhs: VReg,
    /// Compare RHS.
    rhs: VReg,
}

/// Map "store when `x cc y`" onto one of the five NEON compares (all-ones ⟺
/// predicate). `<`/`<=`/`<u`/`<=u` swap the operands of the corresponding
/// "greater" compare. `!=` has no single all-ones mask ⇒ `None` (BAIL).
fn mask_relation(store_cc: i64, x: VReg, y: VReg) -> Option<PredPlan> {
    use AArch64Opcode::*;
    let (op, swap) = match store_cc {
        CC_GT => (NeonCmgtV, false),
        CC_GE => (NeonCmgeV, false),
        CC_LT => (NeonCmgtV, true),
        CC_LE => (NeonCmgeV, true),
        CC_HI => (NeonCmhiV, false),
        CC_HS => (NeonCmhsV, false),
        CC_LO => (NeonCmhiV, true),
        CC_LS => (NeonCmhsV, true),
        CC_EQ => (NeonCmeqV, false),
        // `!=` would need CMEQ + a whole-register NOT / arm-swap; no single
        // all-ones compare exists, so fail closed.
        _ => return None,
    };
    let (lhs, rhs) = if swap { (y, x) } else { (x, y) };
    Some(PredPlan {
        cmp_op: op,
        lhs,
        rhs,
    })
}

/// Logical negation of a condition code (for a store on the BCond FALSE path).
fn invert_cc(cc: i64) -> Option<i64> {
    Some(match cc {
        CC_EQ => CC_NE,
        CC_NE => CC_EQ,
        CC_GT => CC_LE,
        CC_LE => CC_GT,
        CC_GE => CC_LT,
        CC_LT => CC_GE,
        CC_HI => CC_LS,
        CC_LS => CC_HI,
        CC_HS => CC_LO,
        CC_LO => CC_HS,
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// A fully validated, lane-wise-vectorizable conditional-store loop.
struct Recognized {
    /// Block that branches into the scalar loop `header` (spliced-before point).
    preheader: BlockId,
    /// The `preheader` terminator targeting `header`.
    preheader_term: InstId,
    /// The scalar loop header carrying the counted `iv < bound` test. Plays the
    /// role [`crate::neon_map`] calls the "guard": the vector loop is spliced in
    /// front of it and the scalar loop resumes here for the tail.
    header: BlockId,
    iv: VReg,
    bound: VReg,
    /// Predicate → NEON compare that is all-ones exactly when the store fires.
    pred: PredPlan,
    /// The per-iteration stored value (`F`), SSA def inside the loop.
    term: VReg,
    /// Loop-invariant base pointer of the store `b[i]`.
    store_base: VReg,
    /// True when the loop carries `Gpr64` values (`.2D` path: `.2D` compares,
    /// `base + iv*8` addresses, i64 precheck + unsigned guard).
    is_i64: bool,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// `iv` and every copy of it inside the loop body (for address / step checks).
    iv_copies: HashSet<u32>,
    /// Recognized load result vreg id -> loop-invariant base pointer.
    loads: HashMap<u32, VReg>,
    /// Distinct input base pointers referenced by `P`/`F` (first-seen order).
    bases: Vec<VReg>,
    /// Loop-invariant scalar leaf vreg ids (broadcast via DUP).
    inv_leaves: HashSet<u32>,
}

/// Opcodes permitted anywhere in the loop body. Extends [`crate::neon_map`]'s
/// whitelist with `CSet` (materialised predicate booleans). `StrRI` is the
/// single output store (uniqueness + `b[i]` address checked in `recognize`);
/// anything else ⇒ BAIL (rules out a second store, calls, atomics, division).
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
            | CSet
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

/// `AddRI(d, s, 0)` / `MovR(d, s)` / `Copy(d, s)` copy idioms ⇒ `(d, s)`.
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

/// Only `CmpRR`/`CmpRI` write NZCV among the whitelisted opcodes.
fn sets_flags(op: AArch64Opcode) -> bool {
    matches!(op, AArch64Opcode::CmpRR | AArch64Opcode::CmpRI)
}

/// The nearest flag-setting instruction preceding `target` in program order.
fn nearest_flag_setter_before(
    func: &MachFunction,
    block_insts: &[InstId],
    target: InstId,
) -> Option<InstId> {
    let pos = block_insts.iter().position(|&id| id == target)?;
    block_insts[..pos]
        .iter()
        .rev()
        .find(|&&id| sets_flags(func.inst(id).opcode))
        .copied()
}

impl Recognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // (R1) The conditional-store loop is an un-rotated counted DIAMOND. Its
        // body is {header, cond, then, [skip], latch}: 4 or 5 blocks (the `skip`
        // block may be fused into the latch). Rule out the 2-block map/reduction
        // loops (those belong to neon-map / neon-array).
        if header == latch || !(4..=5).contains(&body.len()) {
            return None;
        }
        if !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // Whitelist every opcode in the body — no call/div/atomic/2nd store.
        let mut loop_insts = HashSet::new();
        for &b in body {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

        let def = build_def_map(func);

        // (R2) header preds are exactly {preheader, latch}; the preheader is the
        // unique non-latch pred (the spliced-before point) and is OUTSIDE the loop.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            return None;
        }
        let preheader = *hpreds.iter().find(|&&b| b != latch)?;
        if body.contains(&preheader) {
            return None;
        }
        let preheader_term = *func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))?;

        // (R3) header: the counted exit test `CmpRR(iv,bound); BCond(LT)->cond;
        // B->exit`. `cond` (the diamond condition block) is in the body; `exit`
        // is not.
        let hinsts = &func.block(header).insts;
        let bcond_h = hinsts
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::BCond)?;
        if imm_of(&bcond_h.operands[0]) != Some(CC_LT) {
            return None;
        }
        let cond = *branch_targets(bcond_h).first()?;
        if !body.contains(&cond) || cond == header {
            return None;
        }
        let cmp_h = hinsts
            .iter()
            .map(|&id| func.inst(id))
            .rev()
            .find(|i| i.opcode == AArch64Opcode::CmpRR)?;
        let iv = vreg_of(&cmp_h.operands[0])?;
        let bound = vreg_of(&cmp_h.operands[1])?;
        // Register width selects the lowering path (mirrors neon_minmax):
        // `Gpr32` pair ⇒ `.4S`; `Gpr64` pair ⇒ `.2D`. Mixed ⇒ BAIL.
        let is_i64 = match (iv.class, bound.class) {
            (RegClass::Gpr32, RegClass::Gpr32) => false,
            (RegClass::Gpr64, RegClass::Gpr64) => true,
            _ => return None,
        };
        // The header must carry ONLY the counted test (no loads/stores/work): any
        // memory op here would not be part of the recognized diamond.
        for &id in hinsts {
            if matches!(
                func.inst(id).opcode,
                AArch64Opcode::LdrRI | AArch64Opcode::StrRI
            ) {
                return None;
            }
        }

        // Bound loop-invariant / available in the preheader.
        let bound_def = *def.get(&bound.id)?;
        if !dom.dominates(block_of_inst(func, bound_def)?, preheader) {
            return None;
        }

        // (R4) EXACTLY ONE store in the body — the conditional output `b[i]`.
        let stores: Vec<InstId> = loop_insts
            .iter()
            .copied()
            .filter(|&id| func.inst(id).opcode == AArch64Opcode::StrRI)
            .collect();
        if stores.len() != 1 {
            return None;
        }
        let store_id = stores[0];
        let store = func.inst(store_id);
        if store.operands.len() != 3 || imm_of(&store.operands[2]) != Some(0) {
            return None;
        }
        let term = vreg_of(&store.operands[0])?; // stored value F
        let store_addr = vreg_of(&store.operands[1])?;
        if term.class
            != if is_i64 {
                RegClass::Gpr64
            } else {
                RegClass::Gpr32
            }
        {
            return None;
        }
        // The store lives in the `then` block, which must reconverge at the latch.
        let then_blk = block_of_inst(func, store_id)?;
        let then_succs = &func.block(then_blk).succs;
        if then_succs.len() != 1 || then_succs[0] != latch {
            return None;
        }

        // (R5) `cond` is the diamond: `BCond(pred_cc)->Bt ; B->Bf`; `then` is one
        // arm, the other arm carries NO store/load and reaches the latch (or IS
        // the latch). `cond` must not itself contain the store.
        if then_blk == cond {
            return None;
        }
        let cinsts = func.block(cond).insts.clone();
        let bcond_c = cinsts
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::BCond)?;
        let pred_cc = imm_of(&bcond_c.operands[0])?;
        let cbt = *branch_targets(bcond_c).first()?; // BCond true target
        let cond_succs = &func.block(cond).succs;
        if cond_succs.len() != 2 || !cond_succs.contains(&then_blk) {
            return None;
        }
        let other_arm = *cond_succs.iter().find(|&&b| b != then_blk)?;
        // The non-store arm: either the latch itself, or a skip block whose only
        // successor is the latch and which holds no memory op.
        if other_arm != latch {
            if !body.contains(&other_arm) {
                return None;
            }
            let osuccs = &func.block(other_arm).succs;
            if osuccs.len() != 1 || osuccs[0] != latch {
                return None;
            }
            for &id in &func.block(other_arm).insts {
                if matches!(
                    func.inst(id).opcode,
                    AArch64Opcode::LdrRI | AArch64Opcode::StrRI
                ) {
                    return None;
                }
            }
        }
        // Store fires on the BCond TRUE path iff the then block IS the true target.
        let store_on_true = cbt == then_blk;

        // (R6) iv-copy set: `iv` and every forward copy of it inside the loop.
        let iv_copies = collect_iv_copies(func, &loop_insts, iv);

        // (R7) step +1: the latch has exactly one copy-like writeback to `iv`,
        // whose source increments an iv-copy by 1.
        let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
        for &id in &func.block(latch).insts {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                writebacks.push((d, s));
            }
        }
        let iv_src = writebacks.iter().find(|(d, _)| *d == iv).map(|(_, s)| *s)?;
        if !is_increment_by_one(func, &def, &iv_copies, iv_src) {
            return None;
        }

        // Decode the predicate: the CmpRR feeding `cond`'s BCond, with polarity
        // inverted when the store is on the FALSE path.
        let cmp_id = nearest_flag_setter_before(
            func,
            &cinsts,
            find_inst(&cinsts, func, AArch64Opcode::BCond)?,
        )?;
        let cmp = func.inst(cmp_id);
        if cmp.opcode != AArch64Opcode::CmpRR {
            return None; // only a direct register relation (fail closed on CSet/CmpRI chains)
        }
        let px = vreg_of(&cmp.operands[0])?;
        let py = vreg_of(&cmp.operands[1])?;
        let store_cc = if store_on_true {
            pred_cc
        } else {
            invert_cc(pred_cc)?
        };
        let pred = mask_relation(store_cc, px, py)?;

        let mut rec = Recognized {
            preheader,
            preheader_term,
            header,
            iv,
            bound,
            pred,
            term,
            store_base: VReg::new(0, RegClass::Gpr64),
            is_i64,
            def,
            loop_insts,
            iv_copies,
            loads: HashMap::new(),
            bases: Vec::new(),
            inv_leaves: HashSet::new(),
        };

        // Store address must be `b[i] = base + sext(iv)*4`, base loop-invariant.
        let store_base = rec.resolve_ai_base(func, dom, store_addr)?;
        rec.store_base = store_base;

        // (R8) `P` operands and `F` must be lane-wise-lowerable: every leaf is a
        // recognized `a[i]` load (same index), a 16-bit constant, or a
        // loop-invariant i32 scalar — never the induction. Populates loads/bases.
        let mut seen = HashSet::new();
        if !rec.node_ok(func, dom, rec.term, &mut seen) {
            return None;
        }
        if !rec.node_ok(func, dom, rec.pred.lhs, &mut seen)
            || !rec.node_ok(func, dom, rec.pred.rhs, &mut seen)
        {
            return None;
        }

        // (R9) ALIASING gate (contract part 2), identical to neon-map: either the
        // single-array in-place case (the only pointer touched is the store base)
        // or the multi-pointer case with distinct `noalias` roots.
        let noalias: HashSet<u32> = func.noalias_params.iter().copied().collect();
        let only_store_base = rec.bases.iter().all(|b| b.id == store_base.id);
        let no_foreign_load = rec.loop_insts.iter().all(|&id| {
            let inst = func.inst(id);
            if inst.opcode != AArch64Opcode::LdrRI {
                return true;
            }
            match inst.operands.first() {
                Some(MachOperand::VReg(v)) => rec.loads.contains_key(&v.id),
                _ => false,
            }
        });
        let single_array_in_place = only_store_base && no_foreign_load;
        if !single_array_in_place {
            let store_root = rec.underlying_noalias_param(func, &noalias, store_base)?;
            for b in &rec.bases {
                if b.id == store_base.id {
                    continue; // in-place read of the SAME array at the same index
                }
                let b_root = rec.underlying_noalias_param(func, &noalias, *b)?;
                if b_root.id == store_root.id {
                    return None; // same underlying array via a different derived ptr
                }
            }
        }

        Some(rec)
    }

    /// Recognize an `x[i]` address `base + idx*elem` (`Madd`, either factor
    /// order), returning its loop-invariant `base`:
    /// * i32 path: `idx = Sxtw(iv-copy)`, `elem = 4`.
    /// * i64 path: `idx` IS an iv-copy (already 64-bit), `elem = 8`.
    fn resolve_ai_base(&self, func: &MachFunction, dom: &DomTree, addr: VReg) -> Option<VReg> {
        let madd = func.inst(*self.def.get(&addr.id)?);
        if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
            return None;
        }
        let f1 = vreg_of(&madd.operands[1])?;
        let f2 = vreg_of(&madd.operands[2])?;
        let base = vreg_of(&madd.operands[3])?;
        let idx_ok = |factor: VReg| {
            if self.is_i64 {
                self.iv_copies.contains(&factor.id)
            } else {
                self.is_sext_iv(func, factor)
            }
        };
        let elem = if self.is_i64 {
            ELEM_BYTES_I64
        } else {
            ELEM_BYTES
        };
        let es_ok = |factor: VReg| const_value(func, &self.def, factor) == Some(elem);
        if !((idx_ok(f1) && es_ok(f2)) || (idx_ok(f2) && es_ok(f1))) {
            return None;
        }
        let base_def = *self.def.get(&base.id)?;
        if !dom.dominates(block_of_inst(func, base_def)?, self.preheader) {
            return None;
        }
        Some(base)
    }

    /// Recognize an array load `dst = *(base + idx*elem)` at offset 0.
    fn load_base(&self, func: &MachFunction, dom: &DomTree, dst: VReg) -> Option<VReg> {
        let want_class = if self.is_i64 {
            RegClass::Gpr64
        } else {
            RegClass::Gpr32
        };
        let load = func.inst(*self.def.get(&dst.id)?);
        if load.opcode != AArch64Opcode::LdrRI
            || load.operands.len() != 3
            || dst.class != want_class
            || imm_of(&load.operands[2]) != Some(0)
        {
            return None;
        }
        let addr = vreg_of(&load.operands[1])?;
        self.resolve_ai_base(func, dom, addr)
    }

    /// True iff `v` is `Sxtw(x)` (defined in the loop) with `x` an iv-copy.
    fn is_sext_iv(&self, func: &MachFunction, v: VReg) -> bool {
        let Some(&id) = self.def.get(&v.id) else {
            return false;
        };
        if !self.loop_insts.contains(&id) {
            return false;
        }
        let inst = func.inst(id);
        inst.opcode == AArch64Opcode::Sxtw
            && inst.operands.len() == 2
            && matches!(vreg_of(&inst.operands[1]), Some(x) if self.iv_copies.contains(&x.id))
    }

    /// Resolve a base pointer to the `noalias` param it is based on (mirrors
    /// [`crate::neon_map::underlying_noalias_param`]).
    fn underlying_noalias_param(
        &self,
        func: &MachFunction,
        noalias: &HashSet<u32>,
        base: VReg,
    ) -> Option<VReg> {
        let mut cur = base;
        for _ in 0..16 {
            if noalias.contains(&cur.id) {
                return Some(cur);
            }
            let inst = func.inst(*self.def.get(&cur.id)?);
            let next = match inst.opcode {
                AArch64Opcode::Madd if inst.operands.len() == 4 => vreg_of(&inst.operands[3])?,
                AArch64Opcode::AddRI if inst.operands.len() == 3 => vreg_of(&inst.operands[1])?,
                AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => {
                    vreg_of(&inst.operands[1])?
                }
                _ => return None,
            };
            cur = next;
        }
        None
    }

    /// Read-only feasibility check mirroring [`lower`]: every reachable node is a
    /// recognized `i32` load, a 16-bit constant, a loop-invariant i32 scalar, or
    /// an allowed lane-wise op over such. The induction is NOT a valid leaf.
    fn node_ok(
        &mut self,
        func: &MachFunction,
        dom: &DomTree,
        val: VReg,
        seen: &mut HashSet<u32>,
    ) -> bool {
        if self.iv_copies.contains(&val.id) {
            return false; // the induction is not a lane-wise value
        }
        if const_value(func, &self.def, val).is_some() {
            return true;
        }
        if !seen.insert(val.id) {
            return true;
        }
        let Some(&def_id) = self.def.get(&val.id) else {
            return false;
        };
        if !self.loop_insts.contains(&def_id) {
            // Loop-invariant broadcast leaf: a scalar of the loop's width whose
            // def dominates the preheader (available to DUP there).
            let Some(db) = block_of_inst(func, def_id) else {
                return false;
            };
            let want_class = if self.is_i64 {
                RegClass::Gpr64
            } else {
                RegClass::Gpr32
            };
            if val.class == want_class && dom.dominates(db, self.preheader) {
                self.inv_leaves.insert(val.id);
                return true;
            }
            return false;
        }
        let opcode = func.inst(def_id).opcode;
        use AArch64Opcode::*;
        if opcode == LdrRI {
            let Some(base) = self.load_base(func, dom, val) else {
                return false;
            };
            self.loads.insert(val.id, base);
            if !self.bases.iter().any(|b| b.id == base.id) {
                self.bases.push(base);
            }
            return true;
        }
        let ops = func.inst(def_id).operands.clone();
        // `.2D` has no integer multiply (`MUL.2D` is UNALLOCATED): any multiply
        // in an i64 predicate/term BAILS (mirrors neon_minmax's i64 path).
        if self.is_i64 && matches!(opcode, MulRR | Madd) {
            return false;
        }
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
                // i64 uses the exact hardware ranges: left `[0, 63]`, right
                // `[1, 64)` (no 0-count right-shift encoding ⇒ BAIL) — mirrors
                // neon_minmax's i64 shift gate.
                let ok_sh = if self.is_i64 {
                    match imm_of(&ops[2]) {
                        Some(v) if opcode == LslRI => (0..64).contains(&v),
                        Some(v) => (1..64).contains(&v),
                        None => false,
                    }
                } else {
                    matches!(imm_of(&ops[2]), Some(v) if (0..=31).contains(&v))
                };
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

/// `iv` plus every vreg reachable from it by forward copy_like within the loop.
fn collect_iv_copies(func: &MachFunction, loop_insts: &HashSet<InstId>, iv: VReg) -> HashSet<u32> {
    let mut set = HashSet::new();
    set.insert(iv.id);
    // Iterate to a fixpoint over loop instructions: d = copy(s) with s already
    // known to be an iv-copy makes d one too (bounded: a handful of copies).
    let mut changed = true;
    while changed {
        changed = false;
        for &id in loop_insts {
            let inst = func.inst(id);
            if let Some((d, s)) = copy_like(inst)
                && set.contains(&s.id)
                && !set.contains(&d.id)
                // exclude the latch loop-carried writeback (d == iv), which would
                // fold the *next* iv back onto iv and is not a same-iteration copy.
                && d.id != iv.id
            {
                set.insert(d.id);
                changed = true;
            }
        }
    }
    set
}

/// `iv_src == (iv-copy) + 1`.
fn is_increment_by_one(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    iv_copies: &HashSet<u32>,
    iv_src: VReg,
) -> bool {
    let Some(&id) = def.get(&iv_src.id) else {
        return false;
    };
    let inst = func.inst(id);
    match inst.opcode {
        AArch64Opcode::AddRI => {
            matches!(vreg_of(&inst.operands[1]), Some(x) if iv_copies.contains(&x.id))
                && imm_of(&inst.operands[2]) == Some(1)
        }
        AArch64Opcode::AddRR => {
            let a = vreg_of(&inst.operands[1]);
            let b = vreg_of(&inst.operands[2]);
            (matches!(a, Some(x) if iv_copies.contains(&x.id))
                && const_value(
                    func,
                    def,
                    b.unwrap_or_else(|| VReg::new(u32::MAX, RegClass::Gpr32)),
                ) == Some(1))
                || (matches!(b, Some(x) if iv_copies.contains(&x.id))
                    && const_value(
                        func,
                        def,
                        a.unwrap_or_else(|| VReg::new(u32::MAX, RegClass::Gpr32)),
                    ) == Some(1))
        }
        _ => false,
    }
}

fn find_inst(insts: &[InstId], func: &MachFunction, op: AArch64Opcode) -> Option<InstId> {
    insts.iter().copied().find(|&id| func.inst(id).opcode == op)
}

// ---------------------------------------------------------------------------
// Transformation
// ---------------------------------------------------------------------------

struct LowerCtx {
    accum: usize,
    vbody: BlockId,
    preheader_term: InstId,
    /// NEON arrangement operand code (`ARR_S4` i32 / `ARR_D2` i64).
    arr_code: i64,
    /// NEON element-size code for scalar broadcasts (`ELEM_S` / `ELEM_D`).
    elem_code: i64,
    /// Register class of the scalar half of a broadcast constant.
    const_class: RegClass,
    /// True on the i64 (`.2D`) path (multiply lowering unreachable).
    is_i64: bool,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    loads: HashMap<u32, VReg>,
    iv_copies: HashSet<u32>,
    /// `(base id, unroll k)` -> the `.4S` vector loaded for that sub-block.
    loaded: HashMap<(u32, usize), VReg>,
    const_cache: HashMap<i64, VReg>,
    inv_leaves: HashSet<u32>,
    inv_cache: HashMap<u32, VReg>,
    memo: HashMap<u32, VReg>,
}

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    // Per-width parameters (mirrors neon_minmax): i32 = `.4S` + sxtw guard;
    // i64 = `.2D` + precheck + unsigned guard.
    let (vf, elem_bytes, arr_code, elem_code, const_class) = if rec.is_i64 {
        (VF_I64, ELEM_BYTES_I64, ARR_D2, ELEM_D, RegClass::Gpr64)
    } else {
        (VF, ELEM_BYTES, ARR_S4, ELEM_S, RegClass::Gpr32)
    };
    let width = UNROLL as i64 * vf; // lanes per vector iteration (16 or 8)

    let pv = rec.is_i64.then(|| func.create_block());
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    let mut fresh: Vec<BlockId> = Vec::new();
    if let Some(pv) = pv {
        fresh.push(pv);
    }
    fresh.extend([vh, vb, vl, vx]);
    insert_new_blocks_before(func, rec.header, &fresh);

    // Internal edges among the fresh blocks only; the preheader->header redirect
    // is deferred to the COMMIT so a lowering failure cannot break the CFG.
    if let Some(pv) = pv {
        func.add_edge(pv, vh);
        func.add_edge(pv, rec.header);
    }
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: element size (+ sign-extended bound for the i32 sxtw guard).
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(elem_bytes)],
    );

    if let Some(pv) = pv {
        // --- i64 Precheck + UNSIGNED vector header (identical to neon_minmax's
        // i64 path; see the module docs and neon_array::apply_i64 for the
        // wrap-freedom argument): `bound < width -> all-scalar`, then
        // `iv <u bound - (width-1)` admits a full block.
        let main_bound = alloc(func, RegClass::Gpr64);
        emit(
            func,
            pv,
            AArch64Opcode::SubRI,
            vec![vreg(main_bound), vreg(rec.bound), imm(width - 1)],
        );
        emit(
            func,
            pv,
            AArch64Opcode::CmpRI,
            vec![vreg(rec.bound), imm(width)],
        );
        emit(
            func,
            pv,
            AArch64Opcode::BCond,
            vec![imm(CC_LT), block(rec.header)],
        );
        emit(func, pv, AArch64Opcode::B, vec![block(vh)]);

        emit(
            func,
            vh,
            AArch64Opcode::CmpRR,
            vec![vreg(rec.iv), vreg(main_bound)],
        );
        emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
        emit(func, vh, AArch64Opcode::B, vec![block(vx)]);
    } else {
        // --- i32 Vector header: guard `sxtw(iv) + (width-1) < sxtw(bound)`
        // (i64, no overflow) — a full `width`-lane block is in bounds.
        let nb64 = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Sxtw,
            vec![vreg(nb64), vreg(rec.bound)],
        );
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
    }

    // --- Vector body: the block-base index (sext(iv) on i32; iv directly on
    // i64 — already 64-bit); then LOAD every input stream AND the store
    // base `b` (for the old value written back on false lanes) with `UNROLL/2`
    // post-index `LDP Q,Q,[p],#32` pairs — all loads BEFORE any store so an
    // in-place (`a == b`) read latches every element before overwrite.
    let si = if rec.is_i64 {
        rec.iv
    } else {
        let si = alloc(func, RegClass::Gpr64);
        emit(func, vb, AArch64Opcode::Sxtw, vec![vreg(si), vreg(rec.iv)]);
        si
    };

    // Bases to load: the P/F input bases, plus the store base (deduped).
    let mut load_bases: Vec<VReg> = rec.bases.clone();
    if !load_bases.iter().any(|b| b.id == rec.store_base.id) {
        load_bases.push(rec.store_base);
    }
    let mut loaded: HashMap<(u32, usize), VReg> = HashMap::new();
    for base in &load_bases {
        let p = alloc(func, RegClass::Gpr64);
        emit(
            func,
            vb,
            AArch64Opcode::Madd,
            vec![vreg(p), vreg(si), vreg(c_es), vreg(*base)],
        );
        for pair in 0..UNROLL / 2 {
            let q0 = alloc(func, RegClass::Fpr128);
            let q1 = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vb,
                AArch64Opcode::NeonLdpQPost,
                vec![vreg(q0), vreg(q1), vreg(p), imm(32)],
            );
            loaded.insert((base.id, 2 * pair), q0);
            loaded.insert((base.id, 2 * pair + 1), q1);
        }
    }

    // Separate running store pointer over `b` (never a load pointer register).
    let sp = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vb,
        AArch64Opcode::Madd,
        vec![vreg(sp), vreg(si), vreg(c_es), vreg(rec.store_base)],
    );

    let mut ctx = LowerCtx {
        accum: 0,
        vbody: vb,
        preheader_term: pre,
        arr_code,
        elem_code,
        const_class,
        is_i64: rec.is_i64,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        loads: rec.loads.clone(),
        iv_copies: rec.iv_copies.clone(),
        loaded,
        const_cache: HashMap::new(),
        inv_leaves: rec.inv_leaves.clone(),
        inv_cache: HashMap::new(),
        memo: HashMap::new(),
    };

    // Per sub-block: mask = CMxx(P), value = F, merged = BIT(old_b, value, mask);
    // collect merged for the paired stores.
    let mut merged: Vec<VReg> = Vec::with_capacity(UNROLL);
    for k in 0..UNROLL {
        ctx.accum = k;
        ctx.memo.clear();
        // mask
        let Some(lhs) = lower(func, &mut ctx, rec.pred.lhs) else {
            return false;
        };
        let Some(rhs) = lower(func, &mut ctx, rec.pred.rhs) else {
            return false;
        };
        let mask = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            rec.pred.cmp_op,
            vec![vreg(mask), vreg(lhs), vreg(rhs), imm(arr_code)],
        );
        // value
        let Some(value) = lower(func, &mut ctx, rec.term) else {
            return false;
        };
        // old b lanes (already loaded above)
        let Some(&old_b) = ctx.loaded.get(&(rec.store_base.id, k)) else {
            return false;
        };
        // merged = BIT(old_b, value, mask): per lane `mask ? value : old_b`. The
        // tied-def `BIT` (`old_b = (old_b & ~mask) | (value & mask)`) is the
        // faithfully-proven bit-insert (neon_lowering_proofs::proof_neon_bitv_
        // lanewise_16b). `mask` and `value` are read before `old_b` is
        // overwritten, so the in-place redefinition is safe.
        emit(
            func,
            vb,
            AArch64Opcode::NeonBitV,
            vec![vreg(old_b), vreg(value), vreg(mask)],
        );
        merged.push(old_b);
    }
    // Paired post-index stores `STP Qk,Qk+1,[sp],#32` (clang's shape); a trailing
    // odd block would keep a single ST1 (UNROLL is even here, so all paired).
    let mut k = 0;
    while k + 1 < UNROLL {
        emit(
            func,
            vb,
            AArch64Opcode::NeonStpQPost,
            vec![vreg(merged[k]), vreg(merged[k + 1]), vreg(sp), imm(32)],
        );
        k += 2;
    }
    if k < UNROLL {
        emit(
            func,
            vb,
            AArch64Opcode::NeonSt1Post,
            vec![vreg(merged[k]), vreg(sp), imm(arr_code)],
        );
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: advance the induction by `width`.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector exit: fall through to the scalar loop (writes the disjoint tail).
    emit(func, vx, AArch64Opcode::B, vec![block(rec.header)]);

    // --- COMMIT: splice the fresh blocks in front of the scalar loop header
    // (through the precheck on the i64 path).
    let entry = pv.unwrap_or(vh);
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.header, entry) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.header);
    func.add_edge(rec.preheader, entry);
    func.add_edge(vx, rec.header);

    true
}

/// Lower a term/predicate-operand value to a `4 x i32` NEON value (vector body).
fn lower(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> Option<VReg> {
    if ctx.iv_copies.contains(&val.id) {
        return None;
    }
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
    }
    if let Some(base) = ctx.loads.get(&val.id).copied() {
        let v = *ctx.loaded.get(&(base.id, ctx.accum))?;
        ctx.memo.insert(val.id, v);
        return Some(v);
    }
    if let Some(imm_v) = const_value(func, &ctx.def, val) {
        let v = const_vec(func, ctx, imm_v);
        ctx.memo.insert(val.id, v);
        return Some(v);
    }
    if ctx.inv_leaves.contains(&val.id) {
        let v = inv_broadcast(func, ctx, val);
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
    // `.2D` has no integer multiply; recognition BAILED on any i64 multiply, so
    // these arms are unreachable on the i64 path — fail closed.
    if ctx.is_i64 && matches!(opcode, MulRR | Madd) {
        return None;
    }
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
                vec![vreg(d), vreg(a), imm(sh), imm(ctx.arr_code)],
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
        operands.push(imm(ctx.arr_code));
    }
    emit(func, ctx.vbody, op, operands);
    d
}

/// Materialize (once) a broadcast per-lane constant vector in the preheader.
fn const_vec(func: &mut MachFunction, ctx: &mut LowerCtx, value: i64) -> VReg {
    if let Some(&v) = ctx.const_cache.get(&value) {
        return v;
    }
    let w = alloc(func, ctx.const_class);
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
        vec![vreg(v), vreg(w), imm(ctx.elem_code)],
    );
    ctx.const_cache.insert(value, v);
    v
}

/// DUP-broadcast (once) a loop-invariant scalar to every lane, in the preheader.
fn inv_broadcast(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> VReg {
    if let Some(&v) = ctx.inv_cache.get(&val.id) {
        return v;
    }
    let v = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        ctx.preheader_term,
        AArch64Opcode::NeonDupGen,
        vec![vreg(v), vreg(val), imm(ctx.elem_code)],
    );
    ctx.inv_cache.insert(val.id, v);
    v
}

// ---------------------------------------------------------------------------
// Small local IR helpers (kept independent of the sibling neon_* passes)
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
    let mut map = HashMap::new();
    for (idx, inst) in func.insts.iter().enumerate() {
        if let Some(MachOperand::VReg(v)) = inst.operands.first()
            && produces_def(inst.opcode)
        {
            map.insert(v.id, InstId(idx as u32));
        }
    }
    map
}

fn produces_def(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    !matches!(op, CmpRR | CmpRI | BCond | B | StrRI)
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
