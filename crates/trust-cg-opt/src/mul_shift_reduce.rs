// trust-cg-opt - Multiply-by-small-constant -> shift/add-sub strength reduction (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Rewrites an integer multiply — a `MulRR`, or the multiply half of a `Madd`
//! multiply-accumulate — BY A SMALL COMPILE-TIME CONSTANT into a short
//! shift + add/sub sequence, off the hardware `MUL`/`MADD` critical path.
//!
//! # Why
//!
//! `MUL`/`MADD` are latency-3-4 on Apple cores. When the multiply sits on a
//! LOOP-CARRIED dependence (p2_collatz's odd step `c = c*3 + 1`, which isel
//! fuses to a single `MADD c, #3, #1`), that latency is the loop's speed limit.
//! LLVM instead emits `add x, c, c, lsl #1` — a 1-cycle shifted add — plus the
//! `+1`, shortening the carried path. This pass reproduces that win using only
//! the already-gate-credited `LslRI` / `AddRR` / `SubRR` opcodes (there is no
//! shifted-register ADD opcode in this backend; the ROR-shifted `EorRRShift` is
//! the only shifted-register ALU form, and it is EOR-only). A shift feeding an
//! add is 2 machine instructions but ≤ 2 cycles of latency versus the madd's
//! 3-4, and — because the shifts of `x` are independent and the addend folds in
//! parallel — the carried path is 2 cycles for the `2^k+1` shape.
//!
//! # What fires
//!
//! The signed constant `c` (sign-extended to the operation width) must be a
//! single positive power of two `2^a`, or a **one-shift** two-term form
//! `s_a·2^a + s_b·2^0` with `a > 0` and sign combination in `{(+,+), (+,-),
//! (-,+)}` — i.e. `2^a + 1`, `2^a - 1`, `1 - 2^a`. That covers `2,3,4,5,7,8,9,
//! 15,16,17,…` and negatives like `-3 = 1 - 4`, `-7 = 1 - 8`. It emits AT MOST
//! ONE `LslRI` plus one add/sub, so it is never a throughput regression.
//!
//! Deliberately BAILED (kept as the original multiply):
//!   * **Two-shift forms** — both powers ≥ 2, e.g. `6 = 4+2`, `10 = 8+2`,
//!     `24 = 16+8`. These would need two shifts + an add (3 ALU ops for one
//!     MUL); the only payoff is a latency edge for latency-bound chains, while a
//!     THROUGHPUT-bound loop (matmul's `i*24` index math) measurably regresses.
//!     Bailing keeps the pass strictly throughput-safe.
//!   * **≥3-term constants** — `11 = 8+2+1`, `13 = 8+4+1`, large primes.
//!   * `(-,-)` (e.g. `-6 = -(4+2)`) — needs a leading negate, no positive term
//!     to seed the accumulator.
//!
//! # Soundness
//!
//! Pure ring identity over Z/2^W (wrapping): `x·(s_a·2^a + s_b·2^b) ≡
//! (x<<a)·s_a + (x<<b)·s_b (mod 2^W)`, bit-exact for `wrapping_mul`; the addend
//! of a `Madd` is summed in verbatim. No overflow concern (wrapping). The
//! constant is resolved by [`unique_reaching_const`] — a sound reaching-defs
//! query that returns `Some` ONLY when exactly one `Movz`(+`Movk`)
//! materialization reaches the use — so a non-constant, ambiguous, or
//! loop-redefined multiplier resolves to `None` and BAILS. Every unproven
//! precondition (non-GPR class, mismatched widths, out-of-range shift, ≥3 term
//! constant) bails to the unchanged `MulRR`/`Madd`.
//!
//! Emits ONLY `LslRI`/`AddRR`/`SubRR` — opcodes already emitted throughout isel
//! and gate-covered — so there is NO new emittable surface and no gate impact.
//!
//! # Kill switches
//!
//! Compile-time: set `TCG_NO_MUL_SHIFT_REDUCE` (any value) — [`run`] becomes a
//! no-op. Per-pass bisect: `TRUST_CG_DISABLE_PASSES=mulshift`.
//!
//! [`run`]: MachinePass::run

use std::collections::HashMap;

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    RegClass, SourceLoc, VReg,
};

use crate::pass_manager::MachinePass;
use crate::reaching_const::{ReachingCtx, unique_reaching_const, unique_reaching_const_with};

/// Multiply-by-small-constant -> shift/add-sub strength reduction pass.
pub struct MulShiftReduce;

/// Compile-time kill switch: set `TCG_NO_MUL_SHIFT_REDUCE` (any value) to
/// disable the pass entirely.
fn pass_enabled() -> bool {
    std::env::var_os("TCG_NO_MUL_SHIFT_REDUCE").is_none()
}

impl MachinePass for MulShiftReduce {
    fn name(&self) -> &str {
        "mul-shift-reduce"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if !pass_enabled() {
            return false;
        }
        run_mul_shift_reduce(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        if !pass_enabled() {
            return false;
        }
        run_mul_shift_reduce(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        if !pass_enabled() {
            return false;
        }
        run_mul_shift_reduce(func, Some(provenance))
    }
}

fn pass_id() -> PassId {
    PassId::new("mul-shift-reduce")
}

/// A single signed power-of-two term of the multiplier decomposition:
/// `positive ? +(x<<shift) : -(x<<shift)`. `shift == 0` means the plain `x`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Term {
    positive: bool,
    shift: u32,
}

/// A validated, infallible-to-materialize rewrite of one `MulRR`/`Madd`.
#[derive(Clone, Debug)]
struct Plan {
    /// The multiplicand register `x` (the non-constant multiply operand).
    x: VReg,
    /// The `Madd` addend register `y` (result is `y + x*c`); `None` for `MulRR`.
    addend: Option<VReg>,
    /// The original result register the final emitted instruction must define.
    dst: VReg,
    /// GPR class (`Gpr32`/`Gpr64`) shared by `x`, `addend`, `dst`, all temps.
    class: RegClass,
    /// The `x*c` decomposition (1 or 2 signed power-of-two terms).
    terms: Vec<Term>,
    /// Source location copied onto the emitted instructions.
    source_loc: Option<SourceLoc>,
}

/// Inclusive magnitude ceiling on a resolvable multiplier — keeps the pass to
/// genuinely SMALL constants (the strength-reduction never fires on large
/// multipliers even when they happen to be 2-term). Well past every realistic
/// small-constant multiply; the ≤2-term structure is the real gate.
const MAX_ABS_CONST: i128 = 1 << 20;

impl MulShiftReduce {
    /// Run the pass directly on a function (tests / standalone use).
    pub fn run_on_function(&mut self, func: &mut MachFunction) -> bool {
        <Self as MachinePass>::run(self, func)
    }
}

fn run_mul_shift_reduce(
    func: &mut MachFunction,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let mut changed = false;
    // `unique_reaching_const` rebuilds three whole-function indexes on every
    // call, so resolving one constant per candidate is quadratic in the block
    // size. Phase A is explicitly an IMMUTABLE recognition pass, so ONE index
    // serves all of its queries.
    //
    // It is built exactly ONCE and never refreshed. Phase B invalidates it, and
    // re-indexing the whole function after every mutated block is a cure worse
    // than the disease on block-dense code: measured on `branchy`, refreshing
    // per block made this pass 49.4ms -> 88.4ms at 200 blocks, an 18-24% whole-
    // compile regression, because each rebuild is O(function) but serves only
    // the handful of multiplies in one block. Once stale, later blocks fall back
    // to the per-query path, which is exactly the pre-existing behaviour.
    //
    // The single build still captures the case it was written for — one large
    // block with many multiplies, where it is worth 5.6x — while bounding the
    // indexing cost at O(function) per pass run instead of O(blocks x function).
    // ONE index for the entire pass run, and Phase A for the WHOLE function
    // completes before any mutation — so the index never goes stale and every
    // query is served by it.
    //
    // The previous shape built the index once but LATCHED IT OFF at the first
    // materialized plan, after which every remaining block fell back to the
    // one-shot scan path. On block-dense code the first block containing a
    // multiply latches it, so essentially every candidate paid a whole-function
    // scan — the pass was back at its original cost (branchy measured at exact
    // parity, not faster). Splitting the phases function-wide removes the latch.
    //
    // Recognition is unaffected by hoisting it ahead of every rewrite. Phase B
    // materializes a shift/add sequence and Phase C splices the multiply out;
    // neither removes the MOVZ/MOVK that defines a multiplier constant, and the
    // only vreg a rewrite defines is the multiply's own `dst`, whose defining
    // opcode is not a move-wide either before (Mul/Madd) or after (Add/Lsl).
    // `unique_reaching_const` therefore returns the same verdict for every query
    // whether it runs before or after the earlier blocks were rewritten.
    let ctx = ReachingCtx::new(func);

    // Phase A (immutable, whole function): recognize every rewritable multiply
    // against the UNMUTATED function, building a fully-validated Plan for each.
    let mut recognized: Vec<(BlockId, Vec<InstId>, Vec<(InstId, Plan)>)> = Vec::new();
    for block_id in func.block_order.clone() {
        let block_insts = func.block(block_id).insts.clone();
        let mut plans: Vec<(InstId, Plan)> = Vec::new();
        for &inst_id in &block_insts {
            if let Some(plan) = analyze(func, Some(&ctx), inst_id) {
                plans.push((inst_id, plan));
            }
        }
        if !plans.is_empty() {
            recognized.push((block_id, block_insts, plans));
        }
    }

    for (block_id, block_insts, plans) in recognized {
        // Phase B (mutable): materialize each plan into fresh instructions.
        let mut replacements: HashMap<InstId, Vec<InstId>> = HashMap::new();
        for (inst_id, plan) in plans {
            let new_ids = materialize(func, &plan, inst_id, provenance.as_deref_mut());
            replacements.insert(inst_id, new_ids);
            changed = true;
        }

        // Phase C: splice each rewritten multiply's InstId out for its sequence.
        // The original MachInst stays inert in the arena (unreferenced, never
        // encoded) — the same delete discipline the other machine peepholes use.
        let new_insts: Vec<InstId> = block_insts
            .iter()
            .flat_map(|iid| match replacements.get(iid) {
                Some(seq) => seq.clone(),
                None => vec![*iid],
            })
            .collect();
        func.block_mut(block_id).insts = new_insts;
    }
    changed
}

/// Recognize a `MulRR` / `Madd` by a small compile-time constant and build a
/// validated [`Plan`]. Returns `None` (BAIL) on every unproven precondition.
fn analyze(func: &MachFunction, ctx: Option<&ReachingCtx>, inst_id: InstId) -> Option<Plan> {
    let inst = func.inst(inst_id);
    match inst.opcode {
        AArch64Opcode::MulRR => {
            // MulRR [dst, op1, op2] : dst = op1 * op2. Multiply commutes, so the
            // constant may be either source; the other is `x`.
            if inst.operands.len() != 3 {
                return None;
            }
            let dst = inst.operands[0].as_vreg()?;
            let op1 = inst.operands[1].as_vreg()?;
            let op2 = inst.operands[2].as_vreg()?;
            // Prefer op2 as the constant (isel's `x * C` order), then op1.
            plan_for(func, ctx, inst_id, dst, op1, op2, None)
                .or_else(|| plan_for(func, ctx, inst_id, dst, op2, op1, None))
        }
        AArch64Opcode::Madd => {
            // Madd [dst, Xn, Xm, Xa] : dst = Xa + Xn*Xm. Xn*Xm commutes; Xa is
            // the addend folded in verbatim.
            if inst.operands.len() != 4 {
                return None;
            }
            let dst = inst.operands[0].as_vreg()?;
            let xn = inst.operands[1].as_vreg()?;
            let xm = inst.operands[2].as_vreg()?;
            let xa = inst.operands[3].as_vreg()?;
            plan_for(func, ctx, inst_id, dst, xn, xm, Some(xa))
                .or_else(|| plan_for(func, ctx, inst_id, dst, xm, xn, Some(xa)))
        }
        _ => None,
    }
}

/// Try to build a plan for `dst = addend? + x * (const held by `cst`)`. `x` is
/// the multiplicand; `cst` is the candidate constant-multiplier operand.
fn plan_for(
    func: &MachFunction,
    ctx: Option<&ReachingCtx>,
    inst_id: InstId,
    dst: VReg,
    x: VReg,
    cst: VReg,
    addend: Option<VReg>,
) -> Option<Plan> {
    // All operands must be the SAME GPR class as the destination — the emitted
    // shift/add/sub derive their W-vs-X form from the destination register, so a
    // width mismatch would silently change semantics. Bail on any non-GPR class.
    let class = dst.class;
    let width = match class {
        RegClass::Gpr32 => 32u32,
        RegClass::Gpr64 => 64u32,
        _ => return None,
    };
    if x.class != class || cst.class != class {
        return None;
    }
    if let Some(y) = addend
        && y.class != class
    {
        return None;
    }

    // Resolve the multiplier to a proven unique compile-time constant, or bail.
    let raw = match ctx {
        Some(ctx) => unique_reaching_const_with(func, ctx, inst_id, cst)?,
        None => unique_reaching_const(func, inst_id, cst)?,
    };
    // Sign-extend from the operation width: a 32-bit `-3` arrives as the
    // zero-extended `0xFFFF_FFFD`; interpret it as `-3` so the compact 2-term
    // `1 - 4` decomposition is found. `x * c ≡ x * (c mod 2^W) (mod 2^W)`, so
    // re-signing the low `W` bits is value-preserving.
    let c: i128 = if width == 32 {
        i128::from(raw as i32)
    } else {
        i128::from(raw)
    };

    let terms = decompose(c, width)?;
    // A leading positive term is required to seed the additive accumulator
    // without a negate; `decompose` guarantees it, but re-check fail-closed.
    if !terms.iter().any(|t| t.positive) {
        return None;
    }

    Some(Plan {
        x,
        addend,
        dst,
        class,
        terms,
        source_loc: func.inst(inst_id).source_loc,
    })
}

/// Decompose signed `c` into AT MOST TWO signed power-of-two terms
/// `s_a·2^a (+ s_b·2^b)` with `a > b ≥ 0`, shifts `< width`, sign combination
/// restricted to `{(+), (+,+), (+,-), (-,+)}` (a leading positive always
/// exists; `(-,-)` is excluded). Returns the terms larger-shift-first, or
/// `None` if `c` needs ≥3 terms / is out of range (BAIL).
fn decompose(c: i128, width: u32) -> Option<Vec<Term>> {
    // Only genuinely small constants; `|c| <= 1` (mul by 0/1/-1) is a degenerate
    // case handled by const-fold / declarative-rewrite, not this pass.
    if c.abs() < 2 || c.abs() > MAX_ABS_CONST {
        return None;
    }
    let w = width as i128;
    for a in 1..w {
        let pa: i128 = 1i128 << a;
        // Single positive power of two: c == 2^a.
        if c == pa {
            return Some(vec![Term {
                positive: true,
                shift: a as u32,
            }]);
        }
        // Two-term: c == s_a·2^a + s_b·2^b, with b < a.
        for &sa in &[1i128, -1i128] {
            let rem = c - sa * pa;
            if rem == 0 {
                // c == s_a·2^a exactly; the +2^a single term is handled above,
                // and a lone -2^a is intentionally not emitted (needs a negate).
                continue;
            }
            let mag = rem.unsigned_abs();
            if !mag.is_power_of_two() {
                continue;
            }
            let b = mag.trailing_zeros();
            if (a as u32) <= b || b >= width {
                continue; // require distinct powers b < a, and b in range
            }
            // ONE-SHIFT restriction: require the smaller power to be 2^0, so the
            // sequence emits at most a SINGLE `LslRI` (`x<<a`) plus one add/sub
            // — `2^a ± 1` / `1 - 2^a`. A two-shift form (both powers ≥ 2, e.g.
            // `24 = 16 + 8`) would emit two shifts + an add (3 ALU ops for one
            // MUL); in a THROUGHPUT-bound loop (matmul's `i*24` index math) that
            // is a measured regression, and its only benefit is a latency edge
            // that helps solely latency-bound chains. Bailing keeps the pass
            // strictly throughput-safe (never slower). The collatz target
            // `3 = 2 + 1` is a one-shift form and still fires.
            if b != 0 {
                continue;
            }
            let sa_pos = sa > 0;
            let sb_pos = rem > 0;
            // Exclude (-,-): no positive term to seed the accumulator.
            if !sa_pos && !sb_pos {
                continue;
            }
            return Some(vec![
                Term {
                    positive: sa_pos,
                    shift: a as u32,
                },
                Term {
                    positive: sb_pos,
                    shift: b,
                },
            ]);
        }
    }
    None
}

/// Does any `Csel` read `dst` as one of its two SELECT VALUE operands
/// (positions 1/2 — the `cond ? op1 : op2` values), NOT the condition immediate?
/// Sound whole-function scan; used to gate the deferred-addend reorder to sites
/// where a downstream Csel->Csinc fold can consume the exposed `+1`.
fn dst_feeds_csel_value_arm(func: &MachFunction, dst: VReg) -> bool {
    for &bid in &func.block_order {
        for &iid in &func.block(bid).insts {
            let inst = func.inst(iid);
            if inst.opcode == AArch64Opcode::Csel && inst.operands.len() >= 3 {
                let arm1 = inst.operands[1].as_vreg() == Some(dst);
                let arm2 = inst.operands[2].as_vreg() == Some(dst);
                if arm1 || arm2 {
                    return true;
                }
            }
        }
    }
    false
}

/// Materialize a validated plan into fresh instructions and return their
/// InstIds in emission order (shifts first, then the add/sub fold whose last
/// instruction defines `dst`). Infallible: `analyze` validated every
/// precondition.
fn materialize(
    func: &mut MachFunction,
    plan: &Plan,
    old_id: InstId,
    mut provenance: Option<&mut ProvenanceMap>,
) -> Vec<InstId> {
    let class = plan.class;
    let sloc = plan.source_loc;
    let mut new_ids: Vec<InstId> = Vec::new();

    // Emit one instruction, stamping source_loc and threading provenance.
    let push_new = |func: &mut MachFunction,
                    provenance: &mut Option<&mut ProvenanceMap>,
                    new_ids: &mut Vec<InstId>,
                    opcode: AArch64Opcode,
                    operands: Vec<MachOperand>|
     -> InstId {
        let mut inst = MachInst::new(opcode, operands);
        inst.source_loc = sloc;
        let id = func.push_inst(inst);
        if let Some(p) = provenance.as_deref_mut() {
            p.record_creation(id, pass_id(), "mul->shift-add strength reduction");
        }
        new_ids.push(id);
        id
    };

    // Fast path: single positive power-of-two multiply (`MulRR x, 2^a`), no
    // addend — a lone `LslRI` straight into `dst`.
    if plan.addend.is_none() && plan.terms.len() == 1 {
        let t = plan.terms[0];
        debug_assert!(t.positive && t.shift >= 1);
        let id = push_new(
            func,
            &mut provenance,
            &mut new_ids,
            AArch64Opcode::LslRI,
            vec![
                MachOperand::VReg(plan.dst),
                MachOperand::VReg(plan.x),
                MachOperand::Imm(i64::from(t.shift)),
            ],
        );
        if let Some(p) = provenance.as_deref_mut() {
            p.record_replacement(old_id, id, pass_id());
        }
        return new_ids;
    }

    // Materialize each term's summand register: a fresh `x << shift` temp for a
    // real shift, or plain `x` for a shift-0 term. Record whether it is a
    // 1-cycle-later shift temp (for latency-minimizing fold ordering).
    struct Summand {
        positive: bool,
        reg: VReg,
        is_shift: bool,
    }
    let mut summands: Vec<Summand> = Vec::new();
    for &t in &plan.terms {
        let reg = if t.shift == 0 {
            plan.x
        } else {
            let temp = VReg::new(func.alloc_vreg(), class);
            push_new(
                func,
                &mut provenance,
                &mut new_ids,
                AArch64Opcode::LslRI,
                vec![
                    MachOperand::VReg(temp),
                    MachOperand::VReg(plan.x),
                    MachOperand::Imm(i64::from(t.shift)),
                ],
            );
            temp
        };
        summands.push(Summand {
            positive: t.positive,
            reg,
            is_shift: t.shift != 0,
        });
    }
    // ADDEND PLACEMENT. For the ALL-POSITIVE `2^k + 1` shape (a plain-`x`
    // shift-0 seed term plus one or more positive shift terms), with a `Madd`
    // addend `y`, DEFER the addend to the single OUTERMOST add — emitting
    // `(x + (x<<k)) + y` rather than the historical `(x + y) + (x<<k)`. Two
    // reasons this is the better order and never a regression:
    //   * The plain-`x` term still seeds the accumulator and the shift term is
    //     added to it, so shift-alu-fuse still folds the `x<<k` into a single
    //     `AddRRShift` (`ADD x, x, LSL #k`) — identical op count to before.
    //   * The trailing `+ y` becomes the LONE outermost op feeding the value's
    //     consumer, so a downstream `Csel`->`Csinc` fold can absorb a `+1`
    //     addend into the select's increment (p2_collatz's `c*3+1` odd arm,
    //     where `y` materializes the constant `1`).
    // SOUNDNESS: pure wrapping-add reassociation over Z/2^W. Integer `+` is
    // associative and commutative in the ring, so `(x + y) + (x<<k)` and
    // `(x + (x<<k)) + y` are the SAME sum of `{x, x<<k, y}` and are bit-exact
    // for `wrapping_mul`/`Madd`. Every OTHER decomposition shape (pure powers,
    // `2^k - 1`, `1 - 2^k`, multi-term) keeps the prior emission byte-for-byte:
    // the addend stays a ready summand folded first, exactly as before.
    // Gate the reorder on the Madd result actually FEEDING a `Csel` value arm.
    // The deferred-addend order exists ONLY to expose a `+1` for the downstream
    // Csel->Csinc fold; where the result is not a select arm (m1_call_chain's
    // `f(x) = 3x + acc` chain), the reorder buys nothing and perturbs scheduling
    // (a measured regression). Requiring a Csel consumer keeps EVERY non-select
    // 2^k+1 Madd byte-identical, and by O2/O3 pass order `if-convert` has already
    // formed the Csel that consumes this Madd's dst, so the check sees it.
    let addend_last = plan.addend.is_some()
        && plan.terms.iter().all(|t| t.positive)
        && plan.terms.iter().any(|t| t.shift == 0)
        && dst_feeds_csel_value_arm(func, plan.dst);
    // The `Madd` addend is an extra positive summand, ready before the loop body
    // (loop-invariant / early), so it sorts with the ready terms — UNLESS
    // `addend_last`, in which case it is deferred to the final outermost add.
    if let Some(y) = plan.addend
        && !addend_last
    {
        summands.push(Summand {
            positive: true,
            reg: y,
            is_shift: false,
        });
    }

    // Order for the shortest carried path: fold the 0-cycle-ready operands
    // (plain `x`, the addend) FIRST while the `x<<k` shifts compute in parallel,
    // then fold the shift temps in last. Within each list, ready-before-shift.
    let mut pos: Vec<VReg> = Vec::new();
    let mut neg: Vec<VReg> = Vec::new();
    for s in summands.iter().filter(|s| s.positive && !s.is_shift) {
        pos.push(s.reg);
    }
    for s in summands.iter().filter(|s| s.positive && s.is_shift) {
        pos.push(s.reg);
    }
    for s in summands.iter().filter(|s| !s.positive && !s.is_shift) {
        neg.push(s.reg);
    }
    for s in summands.iter().filter(|s| !s.positive && s.is_shift) {
        neg.push(s.reg);
    }

    // `analyze` guarantees at least one positive term.
    debug_assert!(!pos.is_empty());

    // Build the additive/subtractive fold: acc = pos[0]; += pos[1..]; -= neg[..].
    // Each op writes a fresh temp except the LAST, which writes `dst`.
    let mut steps: Vec<(AArch64Opcode, VReg)> = Vec::new();
    for &p in &pos[1..] {
        steps.push((AArch64Opcode::AddRR, p));
    }
    for &n in &neg {
        steps.push((AArch64Opcode::SubRR, n));
    }
    // Deferred `2^k+1`-shape addend: the FINAL outermost `+ y` (see
    // `addend_last`). Guaranteed non-empty step list overall: `addend_last`
    // implies ≥2 positive terms (a plain-`x` seed plus a positive shift), so
    // `pos` already contributes ≥1 step even before this one.
    if addend_last {
        let y = plan.addend.expect("addend_last implies a Madd addend");
        steps.push((AArch64Opcode::AddRR, y));
    }
    debug_assert!(!steps.is_empty(), "≥2 summands ⇒ ≥1 fold op");

    let n_steps = steps.len();
    let mut acc = pos[0];
    let mut last_id = old_id; // overwritten below
    for (i, (opc, rm)) in steps.into_iter().enumerate() {
        let out = if i == n_steps - 1 {
            plan.dst
        } else {
            VReg::new(func.alloc_vreg(), class)
        };
        last_id = push_new(
            func,
            &mut provenance,
            &mut new_ids,
            opc,
            vec![
                MachOperand::VReg(out),
                MachOperand::VReg(acc),
                MachOperand::VReg(rm),
            ],
        );
        acc = out;
    }

    if let Some(p) = provenance {
        p.record_replacement(old_id, last_id, pass_id());
    }
    new_ids
}

#[cfg(test)]
mod tests;
