// trust-cg-opt - SOUND NEON predicated-sum array-reduction vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON predicated-sum array-reduction vectorizer (`neon-predsum`)
//!
//! Sibling of [`crate::neon_array`] for counted integer **add**-reductions whose
//! per-iteration term contains a **lane-wise `select`** (a conditional value):
//!
//! ```text
//! s = S0;  for i in 0..n (signed i < n):  s += TERM(i)
//! ```
//!
//! where `s` is a **scalar** `i32` accumulator (register / return value — never
//! memory), the pointers are **only loaded** in the loop, and `TERM` is a
//! lane-wise `i32` function of the loaded elements / loop-invariant scalars / 16-
//! bit constants using `+ - * & | ^ << >>` **and at least one `select(icmp x,y,
//! t, f)`** whose condition operands `x,y` and arms `t,f` are themselves lane-
//! wise. Targets:
//!
//! ```text
//!   s += (a[i] > 0)   ? a[i]  : 0        // clamp-sum
//!   s += (a[i] > t)   ? 1     : 0        // count-if (t a loop-invariant scalar)
//!   s += (a[i] & 1)   ? a[i]  : 0        // masked-sum
//!   s += (a[i] < 0)   ? -a[i] : a[i]     // abs-sum
//!   s += (a[i] > b[i])? a[i]  : b[i]     // per-element-max accumulated
//! ```
//!
//! Each loaded array is walked with paired `LDP Qt1, Qt2` post-index loads; the
//! per-lane term (with each
//! `select` lowered to a NEON compare **mask** + a proven bitwise **bitselect**)
//! is accumulated into `UNROLL = 4` independent `4 x i32` vector accumulators;
//! at loop exit they are combined, horizontally reduced, folded into the scalar
//! accumulator, and the ORIGINAL scalar loop handles the `< 16` tail iterations.
//!
//! It runs immediately **after** [`crate::neon_minmax`] and before
//! [`crate::neon_map`] / [`crate::reduction_split`]. Disable with
//! `TRUST_CG_DISABLE_PASSES=neon_predsum`.
//!
//! ## Clean partition from the sibling passes (why no double-vectorization)
//!
//! * [`crate::neon_array`] claims the pure add/madd reductions. Its opcode
//!   whitelist does **not** include `CSet`/`Csel`, so it BAILS on any loop whose
//!   body contains a select — exactly the loops this pass fires on.
//! * [`crate::neon_minmax`] claims the min/max/bitwise reductions (`Csel`- or
//!   `And/Orr/Eor`-**rooted** `acc_src`). This pass's reduction root is `AddRR`,
//!   which neon-minmax rejects.
//! * This pass fires ONLY when the term contains at least one recognized select
//!   (`require_select`); a pure-arithmetic add reduction is left to neon-array.
//!
//! ## Why this is SOUND
//!
//! Like [`crate::neon_array`], the transform is **purely additive**: it inserts a
//! vector main loop in front of the scalar loop and never edits the scalar loop's
//! instructions, so the scalar loop is correct by construction. Only the inserted
//! vector loop plus the horizontal reduction need justifying, and they inherit
//! neon-array's exact i32 add-reduction machinery — the `i64` sign-extension
//! bounds guard (`sxtw(iv) + (width-1) < sxtw(n)`, `width = 16`) that admits a
//! vector iteration only when the whole 16-lane block `iv..iv+15` is `< n`, the
//! four disjoint accumulators, the balanced combine, and the fold-into-`acc`.
//! Loads are read-only and the reduction target is a register, so aliasing among
//! the read pointers is irrelevant, and add reordering is sound by two's-
//! complement associativity/commutativity.
//!
//! The one addition over neon-array is the **lane-wise select**:
//!
//! * The predicate is **per-lane**: `mask[lane]` is computed from `x[lane]`,
//!   `y[lane]`, which depend only on lane `lane`'s loaded values (and loop-
//!   invariant scalars broadcast identically to every lane). The NEON compare
//!   `CMGT/CMGE/CMEQ/CMHI/CMHS .4S` produces, in each lane, `0xFFFF_FFFF` iff the
//!   per-lane relation holds and `0` otherwise — the faithfully-proven per-lane
//!   compare semantics (`trust-cg-verify::neon_lowering_proofs`).
//! * The arms are selected **per-lane** with the branchless identity
//!   `result = f ^ ((f ^ t) & mask)`, built from the proven per-lane `EOR`/`AND`.
//!   With `mask ∈ {all-ones, all-zeros}` per lane this is exactly `t` when the
//!   predicate holds and `f` otherwise — no cross-lane interaction.
//!
//! Every ordering (`<,<=,>,>=,==,!=`, signed or unsigned) is mapped onto one of
//! the five available compares by (optionally) swapping the compare operands
//! and/or swapping the two arms (`!=` ⇒ `CMEQ` with swapped arms). So per lane
//! `vector_term == scalar_term` exactly, and the add-reduction over lanes equals
//! the scalar left-fold (mod 2^32). QED.
//!
//! ## Fail-closed guards (BAIL preconditions)
//!
//! The neon-array loop-shape guards (2-block innermost `{header, latch}`, `+1`
//! induction, signed-`<` exit, single `i32` accumulator read ONLY by the
//! reduction, loop-invariant bound, no store/call/atomic/unmodeled op) all apply,
//! plus: the reduction root is `AddRR` (not `Madd`); the term contains ≥1 select;
//! **every** select decodes unambiguously (known `CmpRR/CSet/CmpRI/Csel` chain,
//! recognized ordering cc, compare + arm operands all lane-wise); and every non-
//! load leaf is a 16-bit constant or a loop-invariant scalar of the loop's
//! width (broadcast). Anything else leaves the loop entirely scalar.
//!
//! ## i64 (`.2D`) support
//!
//! `i64` predicated sums (`Gpr64` iv/acc/bound, `a[i] = *(base + iv*8)` loads)
//! vectorize on the `.2D` path (`2 x i64` lanes, `WIDTH = UNROLL*2 = 8`):
//! * The five NEON compares (`CMEQ/CMGT/CMGE/CMHI/CMHS`) all ALLOCATE a `.2D`
//!   form (unlike min/max/mul), each with its own faithful `.2D` D-pair proof
//!   (`trust-cg-verify::neon_lowering_proofs::*_lanewise_2d`); the branchless
//!   bitselect (`EOR`/`AND`) is lane-width-agnostic whole-register logic; the
//!   accumulate/combine `ADD`/`SUB` use their proven `.2D` forms. So the
//!   headline `s += (a[i]==k) ? 1 : 0` count-eq lowers to `CMEQ.2D` + `SUB.2D`
//!   (the counting fusion), exactly clang's shape.
//! * The single-op min/max (`SMAX.2D` does not exist) and `ABS` (`.4S`-proven
//!   only) fast paths are SKIPPED on i64 — those select shapes fall through to
//!   the general compare + bitselect, which is correct for them (just not
//!   1-op); any multiply in the term BAILS (`.2D` has no integer multiply).
//! * The bounds guard is [`crate::neon_array`]'s i64 unsigned-subtraction
//!   guard behind a signed precheck (`main_bound = n-(WIDTH-1)` used only when
//!   `n >= WIDTH`; vector loop while `iv <u main_bound`) — i64 has no
//!   sign-extension headroom, so the i32 `sxtw` guard does not apply; see
//!   `neon_array::apply_i64` for the full wrap-freedom argument.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

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
/// Whether per-lane absolute value lowers via the single PROVEN `NeonAbsV`
/// (`ABS.4S`) instead of the negating `SUB` + `SMAX` pair. Gated on the FAITHFUL
/// `NeonAbsV` proof (neon_lowering_proofs::proof_neon_absv_lanewise_4s) existing
/// and the coverage gate staying green (trust-cg-verify enforces 101/101). Both
/// forms compute the exact same per-lane `|x|` (including `abs(INT_MIN) == INT_MIN`
/// by two's-complement wraparound), so this is a sound drop-in — just one op
/// instead of two. If that proof were ever retracted, flip this to `false` to
/// fail-closed to the already-correct SUB+SMAX path — never emit unproven codegen.
const ABS_NEON_ENABLED: bool = true;
/// Number of independent vector accumulators (ILP).
const UNROLL: usize = 4;
/// Number of independent vector accumulators for the NEGATED-by-mask-MAC
/// forward-chain lowerings ([`apply_chain`]: the widening `widen_sext`
/// SMLAL-by-mask arm AND the `Gpr32` `.4S` MLA-by-mask arm) — deliberately
/// WIDER than [`UNROLL`]. Both accumulates put a ~3-cycle MAC on each
/// accumulator's serial chain, so at 4 accumulators the loop is accumulate-
/// LATENCY bound below the M4's ~4-op/cycle SIMD issue floor (measured
/// register-only: 4-acc cmgt+mla = 0.75 cy/Q, exactly LLVM's 3-op
/// cmgt+and+add issue floor — no win); eight independent chains over an 8Q
/// (128-byte) iteration bury that latency under the issue floor (8-acc
/// cmgt+mla = 0.50 cy/Q; 12 accs measured no further gain) and halve the
/// per-element loop-control overhead — the measured e01 AND csI wins. This
/// changes ONLY how many instances of the already-proven per-lane ops are
/// emitted (and how long the scalar tail can be — the guard admits a block
/// only when `iv + 8*VF - 1 < N`); every per-lane value and the proof
/// surface are identical to the 4-accumulator form. A chain of ONLY
/// `!=`-negated reductions (no by-mask MAC available — the addend rides the
/// all-ZERO lanes) keeps the 4-accumulator [`UNROLL`] AND+EOR+ADD shape:
/// its 4-op/Q form is issue-bound already at 4 accumulators, so a wider
/// form buys only parity — dropped under the wins-only bar.
const UNROLL_CHAIN: usize = 8;

// AArch64 condition codes (imm operands of BCond/CSet/Csel).
const CC_EQ: i64 = 0;
const CC_NE: i64 = 1;
const CC_HS: i64 = 2;
const CC_LO: i64 = 3;
const CC_HI: i64 = 8;
const CC_LS: i64 = 9;
const CC_GE: i64 = 10;
/// AArch64 condition code for signed less-than (`LT`); the only recognized
/// counted-loop exit test.
const CC_LT: i64 = 11;
const CC_GT: i64 = 12;
const CC_LE: i64 = 13;

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `neon-predsum` machine pass.
#[derive(Default)]
pub struct NeonPredSumPass {
    fired: usize,
}

impl NeonPredSumPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonPredSumPass {
    fn name(&self) -> &str {
        "neon-predsum"
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

impl NeonPredSumPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;

        // Recognize read-only first; applying a plan only *adds* blocks (never
        // renumbers existing ids or edits other loops), so recognized data for
        // other loops stays valid.
        //
        // Dispatch: the STRICT 2-block recognizer runs first (byte-identical to
        // the shipped path); only if it bails is the FORWARD-CHAIN recognizer
        // tried (branch-diamond `if a[i] REL t { s += a[i] }` over a local
        // fixed-size array, `body.len() >= 3`). The two shapes are disjoint by
        // `body.len()` (== 2 vs >= 3), so a loop is never processed by both.
        let mut plans: Vec<Plan> = Vec::new();
        for lp in loops.all_loops() {
            if let Some(rec) = Recognized::recognize(func, dom, lp.header, lp.latch, &lp.body) {
                plans.push(Plan::Strict(rec));
            } else if let Some(chain) =
                PredSumChainRecognized::recognize(func, dom, lp.header, lp.latch, &lp.body)
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
        if changed && std::env::var("TRUST_CG_DUMP_NEONPREDSUM").is_ok() {
            eprintln!("[neon-predsum] fn={} vectorized={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Select decode
// ---------------------------------------------------------------------------

/// A decoded lane-wise select, normalized to a single NEON compare + bitselect:
/// `result = arm_else ^ ((arm_else ^ arm_if) & mask)` where
/// `mask = cmp_op(cmp_lhs, cmp_rhs)` is all-ones per lane exactly when the
/// original predicate holds. All four operand vregs are lane-wise term values.
#[derive(Clone, Copy)]
struct SelectPlan {
    /// The NEON per-lane compare opcode (one of CMGT/CMGE/CMEQ/CMHI/CMHS).
    cmp_op: AArch64Opcode,
    /// Compare LHS (`Vn`) — already operand-swapped for `<`/`<=` orderings.
    cmp_lhs: VReg,
    /// Compare RHS (`Vm`).
    cmp_rhs: VReg,
    /// Arm selected where `mask` is all-ones.
    arm_if: VReg,
    /// Arm selected where `mask` is all-zeros.
    arm_else: VReg,
}

/// Map a decoded relation `result = (x cc y) ? t : f` onto a [`SelectPlan`]
/// using only the five available NEON compares. Returns `None` for a cc that is
/// not an ordering/equality (fail closed).
fn map_relation(cc: i64, x: VReg, y: VReg, t: VReg, f: VReg) -> Option<SelectPlan> {
    use AArch64Opcode::*;
    // (compare op, swap compare operands, swap arms). A "positive" ordering maps
    // to a compare that is all-ones exactly when the predicate holds (arms as
    // given). `<`/`<=`/`<u`/`<=u` swap the operands of the "greater" compare.
    // `!=` has no direct mask: use CMEQ (the negation) and swap the arms.
    let (op, swap_ops, swap_arms) = match cc {
        CC_GT => (NeonCmgtV, false, false), // x >s y
        CC_GE => (NeonCmgeV, false, false), // x >=s y
        CC_LT => (NeonCmgtV, true, false),  // x <s y  == y >s x
        CC_LE => (NeonCmgeV, true, false),  // x <=s y == y >=s x
        CC_HI => (NeonCmhiV, false, false), // x >u y
        CC_HS => (NeonCmhsV, false, false), // x >=u y
        CC_LO => (NeonCmhiV, true, false),  // x <u y  == y >u x
        CC_LS => (NeonCmhsV, true, false),  // x <=u y == y >=u x
        CC_EQ => (NeonCmeqV, false, false), // x == y
        CC_NE => (NeonCmeqV, false, true),  // x != y  == !(x == y): swap arms
        _ => return None,                   // MI/PL/VS/VC/AL are not orderings
    };
    let (cmp_lhs, cmp_rhs) = if swap_ops { (y, x) } else { (x, y) };
    let (arm_if, arm_else) = if swap_arms { (f, t) } else { (t, f) };
    Some(SelectPlan {
        cmp_op: op,
        cmp_lhs,
        cmp_rhs,
        arm_if,
        arm_else,
    })
}

/// Decode a `Csel`-rooted lane-wise select into a [`SelectPlan`] plus the set of
/// chain instructions (`CmpRR/CSet/CmpRI/Csel`) forming it. Handles both the
/// materialised `CmpRR; CSet(cc); CmpRI(_,0); Csel(NE|EQ)` shape (what ISel emits
/// for `select(icmp)`) and the direct `CmpRR; Csel(cc)` shape. Fails closed on
/// any deviation. Does NOT require any operand to equal the accumulator (unlike
/// [`crate::neon_minmax`], the select here is a plain per-lane VALUE).
fn decode_select(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    csel_id: InstId,
) -> Option<(SelectPlan, Vec<InstId>)> {
    let csel = func.inst(csel_id);
    if csel.opcode != AArch64Opcode::Csel || csel.operands.len() != 4 {
        return None;
    }
    let t = vreg_of(&csel.operands[1])?;
    let f = vreg_of(&csel.operands[2])?;
    let cc_sel = imm_of(&csel.operands[3])?;

    let csel_block = block_of_inst(func, csel_id)?;
    let cinsts = func.block(csel_block).insts.clone();
    let flag1_id = nearest_flag_setter_before(func, &cinsts, csel_id)?;
    let flag1 = func.inst(flag1_id);

    match flag1.opcode {
        // Direct: Csel reads a real comparison directly.
        AArch64Opcode::CmpRR => {
            let x = vreg_of(&flag1.operands[0])?;
            let y = vreg_of(&flag1.operands[1])?;
            let plan = map_relation(cc_sel, x, y, t, f)?;
            Some((plan, vec![csel_id, flag1_id]))
        }
        // Indirect: `CmpRI(bool, 0)` re-tests a materialised `CSet` boolean.
        AArch64Opcode::CmpRI => {
            if imm_of(&flag1.operands[1])? != 0 {
                return None;
            }
            let boolreg = vreg_of(&flag1.operands[0])?;
            let cset_id = *def.get(&boolreg.id)?;
            let cset = func.inst(cset_id);
            if cset.opcode != AArch64Opcode::CSet || cset.operands.len() != 2 {
                return None;
            }
            let cc_real = imm_of(&cset.operands[1])?;
            // The CSet's flags come from the real comparison preceding it.
            let cset_block = block_of_inst(func, cset_id)?;
            let sinsts = func.block(cset_block).insts.clone();
            let cmp_id = nearest_flag_setter_before(func, &sinsts, cset_id)?;
            let cmp = func.inst(cmp_id);
            if cmp.opcode != AArch64Opcode::CmpRR {
                return None;
            }
            let x = vreg_of(&cmp.operands[0])?;
            let y = vreg_of(&cmp.operands[1])?;
            // `bool != 0` ⟺ cc_real; `Csel NE` picks T then, `Csel EQ` picks F.
            let (et, ef) = match cc_sel {
                CC_NE => (t, f),
                CC_EQ => (f, t),
                _ => return None,
            };
            let plan = map_relation(cc_real, x, y, et, ef)?;
            Some((plan, vec![csel_id, flag1_id, cset_id, cmp_id]))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// A fully validated, lane-wise-vectorizable predicated add reduction.
struct Recognized {
    guard: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    iv: VReg,
    acc: VReg,
    bound: VReg,
    /// The per-iteration term value (the non-`acc` operand of the `AddRR`).
    term: VReg,
    /// True when the reduction is `i64` (`Gpr64` iv/acc/bound), lowered on the
    /// `.2D` path with the unsigned-subtraction bounds guard. False = `i32`
    /// (`Gpr32`, `.4S`, sign-extension guard).
    is_i64: bool,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// Load-result vreg id -> loop-invariant base pointer.
    loads: HashMap<u32, VReg>,
    /// Distinct base pointers referenced by `term`'s loads (first-seen order).
    bases: Vec<VReg>,
    /// Decoded select plan for each `Csel`-result vreg id reachable in the term.
    selects: HashMap<u32, SelectPlan>,
    /// Loop-invariant `i32` scalar vreg ids used as leaves (broadcast via DUP).
    inv_leaves: HashSet<u32>,
}

/// Opcodes permitted anywhere in the loop body. Extends [`crate::neon_array`]'s
/// whitelist with `CSet`/`Csel` (the select lowering). Anything else ⇒ BAIL
/// (rules out stores/calls/atomics/division and any unmodeled effect).
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
            | CSet
            | Csel
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
        // (R1) exactly a 2-block innermost loop {header, latch}.
        if header == latch || body.len() != 2 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // Whitelist every opcode in the loop body.
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

        // (R2) latch: exit branch `BCond(LT) -> header` and its `CmpRR(iv,bound)`.
        let latch_insts = &func.block(latch).insts;
        let bcond = latch_insts
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::BCond && branch_targets(i).contains(&header))?;
        if imm_of(&bcond.operands[0]) != Some(CC_LT) {
            return None;
        }
        let cmp = latch_insts
            .iter()
            .map(|&id| func.inst(id))
            .rev()
            .find(|i| i.opcode == AArch64Opcode::CmpRR)?;
        let iv = vreg_of(&cmp.operands[0])?;
        let bound = vreg_of(&cmp.operands[1])?;

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
        let iv_src = writebacks.iter().find(|(d, _)| *d == iv).map(|(_, s)| *s)?;
        let (acc, acc_src) = {
            let other = writebacks.iter().find(|(d, _)| *d != iv)?;
            (other.0, other.1)
        };
        if acc == iv {
            return None;
        }

        // (R3) +1 induction.
        if !is_increment_by_one(func, &def, iv_src, iv) {
            return None;
        }

        // Register width selects the lowering path (mirrors neon_array):
        // `Gpr32` triple ⇒ the `.4S` i32 path (sign-extension guard); `Gpr64`
        // triple ⇒ the `.2D` i64 path (unsigned-subtraction guard, `.2D`
        // compares, no single-op min/max/abs). Mixed widths BAIL.
        let is_i64 = match (iv.class, acc.class, bound.class) {
            (RegClass::Gpr32, RegClass::Gpr32, RegClass::Gpr32) => false,
            (RegClass::Gpr64, RegClass::Gpr64, RegClass::Gpr64) => true,
            _ => return None,
        };

        // (R4) reduction root: `acc_src = AddRR(acc, term)` (commutative). ADD
        // ONLY — Madd/min/max/bitwise reductions belong to neon-array/neon-minmax.
        let acc_def_id = *def.get(&acc_src.id)?;
        let acc_def = func.inst(acc_def_id);
        if acc_def.opcode != AArch64Opcode::AddRR {
            return None;
        }
        let x = vreg_of(&acc_def.operands[1])?;
        let y = vreg_of(&acc_def.operands[2])?;
        let term = if x == acc {
            y
        } else if y == acc {
            x
        } else {
            return None;
        };
        if term == acc || term == iv {
            return None;
        }

        // (R4b) `acc` may be read ONLY by the reduction inst.
        for &id in loop_insts.iter() {
            if id == acc_def_id {
                continue;
            }
            let inst = func.inst(id);
            for opd in inst.operands.iter().skip(1) {
                if vreg_of(opd) == Some(acc) {
                    return None;
                }
            }
        }

        // The bound must be loop-invariant / available in the preheader.
        let bound_def = *def.get(&bound.id)?;
        let bound_block = block_of_inst(func, bound_def)?;
        if !dom.dominates(bound_block, preheader) {
            return None;
        }

        let mut rec = Recognized {
            guard,
            preheader,
            preheader_term,
            iv,
            acc,
            bound,
            term,
            is_i64,
            def,
            loop_insts,
            loads: HashMap::new(),
            bases: Vec::new(),
            selects: HashMap::new(),
            inv_leaves: HashSet::new(),
        };

        // (R5) `term` must be lane-wise-lowerable AND contain ≥1 select. Leaves
        // are recognized `a[i]` loads, 16-bit constants, or loop-invariant i32
        // scalars (never iv/acc), joined by allowed lane-wise ops / selects.
        let mut seen = HashSet::new();
        let mut has_select = false;
        if !rec.node_ok(func, dom, rec.term, &mut seen, &mut has_select) {
            return None;
        }
        // Require at least one load (a bare register reduction is not ours) AND
        // at least one select (pure add reductions belong to neon-array).
        if rec.bases.is_empty() || !has_select {
            return None;
        }

        Some(rec)
    }

    /// Recognize an array load `dst = *(base + idx*elem)` at offset 0 and
    /// return its loop-invariant `base` (mirrors [`crate::neon_array`]):
    /// * i32 path: `dst` is `Gpr32`, `idx = Sxtw(iv)`, `elem = 4`.
    /// * i64 path: `dst` is `Gpr64`, `idx = iv` directly (already 64-bit, no
    ///   sign extension), `elem = 8`.
    fn load_base(&self, func: &MachFunction, dom: &DomTree, dst: VReg) -> Option<VReg> {
        let (want_class, elem_bytes) = if self.is_i64 {
            (RegClass::Gpr64, ELEM_BYTES_I64)
        } else {
            (RegClass::Gpr32, ELEM_BYTES)
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
        let madd = func.inst(*self.def.get(&addr.id)?);
        if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
            return None;
        }
        let f1 = vreg_of(&madd.operands[1])?;
        let f2 = vreg_of(&madd.operands[2])?;
        let base = vreg_of(&madd.operands[3])?;
        let idx_ok = |factor: VReg| {
            if self.is_i64 {
                factor == self.iv
            } else {
                self.is_sext_iv(func, factor)
            }
        };
        let es_ok = |factor: VReg| const_value(func, &self.def, factor) == Some(elem_bytes);
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
            && vreg_of(&inst.operands[1]) == Some(self.iv)
    }

    /// Read-only feasibility check mirroring [`lower`]: every reachable node is a
    /// recognized `i32` array load, a 16-bit constant, a loop-invariant i32
    /// scalar, a lane-wise op, or a decodable lane-wise `select`. The induction
    /// and accumulator are NOT valid term values. Populates `loads`/`bases`/
    /// `selects`/`inv_leaves`; sets `has_select` when a select is recognized.
    fn node_ok(
        &mut self,
        func: &MachFunction,
        dom: &DomTree,
        val: VReg,
        seen: &mut HashSet<u32>,
        has_select: &mut bool,
    ) -> bool {
        if val == self.iv || val == self.acc {
            return false;
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
        // A value defined OUTSIDE the loop that is not a small constant: accept
        // as a loop-invariant broadcast leaf iff it is a scalar of the loop's
        // width whose def dominates the preheader (so it is available to DUP
        // there). Otherwise BAIL.
        if !self.loop_insts.contains(&def_id) {
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
        // A load leaf: validate its `a[i]` address and record the base.
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
        // A select: decode it and validate its compare + arm operands lane-wise.
        if opcode == Csel {
            let Some((plan, _chain)) = decode_select(func, &self.def, def_id) else {
                return false;
            };
            self.selects.insert(val.id, plan);
            *has_select = true;
            return self.node_ok(func, dom, plan.cmp_lhs, seen, has_select)
                && self.node_ok(func, dom, plan.cmp_rhs, seen, has_select)
                && self.node_ok(func, dom, plan.arm_if, seen, has_select)
                && self.node_ok(func, dom, plan.arm_else, seen, has_select);
        }
        let ops = func.inst(def_id).operands.clone();
        // `.2D` has no integer multiply: any multiply (bare `MulRR` or the
        // fused `Madd`) BAILS the whole i64 term, leaving the loop scalar.
        if self.is_i64 && matches!(opcode, MulRR | Madd) {
            return false;
        }
        match opcode {
            MulRR | AddRR | SubRR | AndRR | OrrRR | EorRR => {
                let (Some(a), Some(b)) = (vreg_of(&ops[1]), vreg_of(&ops[2])) else {
                    return false;
                };
                self.node_ok(func, dom, a, seen, has_select)
                    && self.node_ok(func, dom, b, seen, has_select)
            }
            AddRI | SubRI | AndRI | OrrRI | EorRI => {
                let Some(a) = vreg_of(&ops[1]) else {
                    return false;
                };
                let ok_imm = matches!(imm_of(&ops[2]), Some(v) if (0..=0xFFFF).contains(&v));
                ok_imm && self.node_ok(func, dom, a, seen, has_select)
            }
            LslRI | LsrRI | AsrRI => {
                let Some(a) = vreg_of(&ops[1]) else {
                    return false;
                };
                // Per-lane shift-by-immediate ranges (mirrors neon_array): the
                // i64 path uses the exact hardware ranges — left `[0, 63]`,
                // right `[1, 64)` (no 0-count right-shift encoding ⇒ BAIL).
                let ok_sh = if self.is_i64 {
                    match imm_of(&ops[2]) {
                        Some(v) if opcode == LslRI => (0..64).contains(&v),
                        Some(v) => (1..64).contains(&v),
                        None => false,
                    }
                } else {
                    matches!(imm_of(&ops[2]), Some(v) if (0..=31).contains(&v))
                };
                ok_sh && self.node_ok(func, dom, a, seen, has_select)
            }
            Madd if ops.len() == 4 => {
                let (Some(a), Some(b), Some(c)) =
                    (vreg_of(&ops[1]), vreg_of(&ops[2]), vreg_of(&ops[3]))
                else {
                    return false;
                };
                self.node_ok(func, dom, a, seen, has_select)
                    && self.node_ok(func, dom, b, seen, has_select)
                    && self.node_ok(func, dom, c, seen, has_select)
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
// Forward-chain (branch-diamond) recognition
//
// A near-clone of the just-landed `neon_minmax` forward-chain recognizer,
// generalized from min/max to the predicated ADD reduction. It targets the
// bounds-guarded `while i < N` shape the bridge emits for a condsum over a
// LOCAL fixed-size array (`if a[i] REL t { s += a[i] }`), whose per-iteration
// bounds checks are elided to pass-throughs and whose conditional add is a
// control-flow branch DIAMOND rather than the strict two-block loop the
// [`Recognized`] path above matches. By the reassociation
//   `select(cond, acc + a[i], acc) == acc + select(cond, a[i], 0)`
// each iteration's contribution is the lane-wise term `select(a[i] REL t,
// a[i], 0)`, reduced by ADD — so this reuses the SAME already-shipped masked
// select lowering (`select(cond, K, 0) == mask & K`) and the SAME i32 `.4S`
// add-reduction machinery (paired LDP, four accumulators, horizontal fold),
// only fronted by a different recognizer. Everything is file-local (the
// per-pass-owns-its-helpers pattern); the sibling passes are never referenced.
//
// WIDENING i64-accumulator form (`s: i64 += a_i32[iv] as i64`, the e01 shape):
// a reduction whose accumulator is `Gpr64` is accepted IFF its then-arm
// contribution is the in-loop `Sxtw(x)` of a lane-wise `Gpr32` `x` (`as i64` of
// an i32 IS sign-extension; a zero-extension is a different program and BAILS
// fail-closed — `Uxtw` is not even whitelisted). The mask/AND lowering is
// UNCHANGED (`masked = select(pred, x, 0)` per `.4S` lane); only the accumulate
// widens: `vacc.2D[j] += sext64(masked_half[j])` via the faithfully-proven
// SADDW/SADDW2 signed widening add-wide (structurally LLVM's `cmgt.4s +
// and.16b + saddw.2d + saddw2.2d` codegen for this loop; per-lane identical to
// the SMLAL-by-ones MAC it replaced, since `sext64(x) * sext64(1) ==
// sext64(x)`, minus the ones splat and the multiply-pipe latency). Per lane
// `sext64(masked)` equals the scalar term exactly: `sext64(0) == 0` where the
// predicate fails, `sext64(a[iv]) == a[iv] as i64` (negatives included) where
// it holds; `.2D` lane width == the i64 acc width, so wrap is identically mod
// 2^64 and no extra N bound applies.
// ---------------------------------------------------------------------------

/// A recognized, ready-to-apply plan for one loop: either the strict two-block
/// reduction ([`Recognized`], byte-identical to the shipped path) or a
/// forward-chain branch-diamond reduction ([`PredSumChainRecognized`]).
enum Plan {
    Strict(Recognized),
    Chain(PredSumChainRecognized),
}

/// The loop-continue / bounds-guard limit of a forward `while iv <u N` chain: a
/// constant `CmpRI(iv, Imm(N))` (the folded form the bridge emits for a local
/// fixed-size array) or a register `CmpRR(iv, N_reg)`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ChainBound {
    Const(i64),
    Reg(VReg),
}

/// The block set of one recognized condsum branch diamond (EXCLUDING the join,
/// which continues the chain walk).
struct DiamondInfo {
    compare: BlockId,
    join: BlockId,
    blocks: Vec<BlockId>,
}

/// One recognized predicated-add reduction inside a forward chain. Encodes the
/// per-lane term `masked_addend = select(cond, addend, 0)`:
/// * `cmp_op(cmp_lhs, cmp_rhs)` is the per-lane compare mask (all-ones iff the
///   original branch predicate `a[iv] REL t` holds);
/// * `addend` is the lane-wise value added on the "then" arm (`a[iv]` or a
///   lane-wise function of it);
/// * `adds_when_mask_true` says whether the addend is accumulated where the mask
///   is all-ones (`true`, e.g. `>`/`==`) or all-zeros (`false`, e.g. a `!=`
///   whose only available compare is the negation `CMEQ`, or a fall-through
///   "then" edge).
struct PredSumReduction {
    acc: VReg,
    cmp_op: AArch64Opcode,
    cmp_lhs: VReg,
    cmp_rhs: VReg,
    addend: VReg,
    adds_when_mask_true: bool,
    /// True for the WIDENING i64-accumulator form `s(i64) += (addend_i32 as
    /// i64)`: `acc` is `Gpr64` and the scalar then-arm contribution is the
    /// SIGN-extension `Sxtw(addend)` of the lane-wise `Gpr32` `addend`. Lowered
    /// by accumulating `sext64(masked_lane)` into `.2D` accumulators via the
    /// faithfully-proven SADDW/SADDW2 signed widening add-wide (`acc.d[j] +=
    /// sext64(x)` — per-lane identical to the SMLAL-by-ones MAC it replaced,
    /// `sext64(x)*sext64(1) == sext64(x)`, minus the ones splat and the
    /// multiply latency). False = the shipped `Gpr32`/`.4S` accumulate.
    widen_sext: bool,
}

/// A fully validated forward-chain, branch-diamond, K-reduction predicated-add
/// loop (i32 `.4S` elements, `Gpr64` induction / `Gpr32` accumulators — the
/// mixed-width shape the bridge emits for a local fixed-size array — or, per
/// reduction, a `Gpr64` accumulator fed by the SIGN-extended widening form
/// `s(i64) += a_i32[iv] as i64`; see [`PredSumReduction::widen_sext`]).
struct PredSumChainRecognized {
    /// The loop header (== the vectorizer's splice point / `guard`).
    guard: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    iv: VReg,
    /// Compile-time loop bound `N` (constant, `[1, i32::MAX]`).
    bound: i64,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// Load-result vreg id -> loop-invariant base pointer.
    loads: HashMap<u32, VReg>,
    /// Distinct base pointers referenced by the reductions' terms (first-seen).
    bases: Vec<VReg>,
    /// Decoded select plan for each embedded `Csel` reachable in a term.
    selects: HashMap<u32, SelectPlan>,
    /// Loop-invariant `Gpr32` scalar vreg ids used as leaves (broadcast via DUP).
    inv_leaves: HashSet<u32>,
    reductions: Vec<PredSumReduction>,
}

/// Build a def map (`vreg id -> defining InstId`) considering ONLY instructions
/// that are LIVE (reachable through `block_order`). The flat [`build_def_map`]
/// iterates the raw instruction storage, which can still contain DEAD
/// instructions that earlier passes (bounds-check-elim) unhooked from their
/// blocks but left in `func.insts` — e.g. a detached `TrapBoundsCheckExact`
/// whose `operand0` is a READ of the induction copy. That dead duplicate def
/// would shadow the live in-block def and break the copy / address walks. This
/// restricts to the current CFG. When a vreg has multiple LIVE defs (loop-
/// carried phis: `iv`, each `acc`) the last in block/program order wins, which
/// the chain walkers tolerate because they check `== iv` / `== acc` BEFORE
/// following a def. Mirrors `neon_minmax::build_live_def_map` (the "key fix").
fn build_live_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    let mut map = HashMap::new();
    for &bid in &func.block_order {
        for &id in &func.block(bid).insts {
            let inst = func.inst(id);
            if let Some(MachOperand::VReg(v)) = inst.operands.first()
                && produces_def(inst.opcode)
            {
                map.insert(v.id, id);
            }
        }
    }
    map
}

/// Count the definitions of `v` inside `loop_insts`.
fn count_loop_defs(func: &MachFunction, loop_insts: &HashSet<InstId>, v: VReg) -> usize {
    loop_insts
        .iter()
        .filter(|&&id| {
            let inst = func.inst(id);
            produces_def(inst.opcode)
                && matches!(inst.operands.first(), Some(MachOperand::VReg(d)) if d.id == v.id)
        })
        .count()
}

/// True iff `v` reaches `iv` through value-preserving copy links. Matches `iv`
/// EXACTLY and never strips PAST it, so it never follows the latch `iv = iv+1`
/// writeback and never mistakes a shifted index for `iv`. Also reused with
/// `target = acc` to test "is a copy of acc" WITHOUT following the acc's own
/// (loop-carried) latch writeback. Mirrors `neon_minmax::same_as_iv`.
fn same_as_iv(func: &MachFunction, def: &HashMap<u32, InstId>, mut v: VReg, iv: VReg) -> bool {
    for _ in 0..16 {
        if v == iv {
            return true;
        }
        let Some(&d) = def.get(&v.id) else {
            return false;
        };
        match copy_like(func.inst(d)) {
            Some((dst, src)) if dst == v => v = src,
            _ => return false,
        }
    }
    false
}

/// Follow value-preserving copy chains to the underlying value (bounded). Used
/// only on single-def registers, never on the multi-def induction / acc.
fn strip_copies(func: &MachFunction, def: &HashMap<u32, InstId>, mut v: VReg) -> VReg {
    for _ in 0..16 {
        let Some(&d) = def.get(&v.id) else {
            return v;
        };
        match copy_like(func.inst(d)) {
            Some((dst, src)) if dst == v => v = src,
            _ => return v,
        }
    }
    v
}

/// Recognize the terminating guard diamond `cmp x, N; b.lo t_lo; b t_b` (last
/// three instructions) with the unsigned-`LO` taken edge `t_lo` IN the loop and
/// the fall-through `t_b` OUT of it. `N` is a constant immediate (`CmpRI`) or a
/// register (`CmpRR`). Fail-closed on any other shape. Mirrors
/// `neon_minmax::recognize_chain_guard`.
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
        || imm_of(&bcond.operands[0])? != CC_LO
    {
        return None;
    }
    let (x, bound) = match cmp.opcode {
        AArch64Opcode::CmpRR => (
            vreg_of(&cmp.operands[0])?,
            ChainBound::Reg(vreg_of(&cmp.operands[1])?),
        ),
        AArch64Opcode::CmpRI => (
            vreg_of(&cmp.operands[0])?,
            ChainBound::Const(imm_of(&cmp.operands[1])?),
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
/// register-resolves-to-the-constant. Mirrors `neon_minmax::chain_bound_agrees`.
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

/// Recognize an `a[iv]` load (i32 `.4S` element, offset 0): `dst = *(base +
/// idx*4)` with `dst` a `Gpr32`, `idx` a copy of `iv` (mixed `Gpr64` induction
/// used directly) OR `Sxtw(iv)` (pure-i32 addressing), the element size the
/// constant `4`, and `base` loop-invariant (its def dominates the preheader).
/// Returns `base`. Mirrors `neon_minmax::chain_load_base`. Fail-closed otherwise.
fn chain_load_base(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    dst: VReg,
    iv: VReg,
    preheader: BlockId,
) -> Option<VReg> {
    if dst.class != RegClass::Gpr32 {
        return None;
    }
    let load = func.inst(*def.get(&dst.id)?);
    if load.opcode != AArch64Opcode::LdrRI
        || load.operands.len() != 3
        || imm_of(&load.operands[2]) != Some(0)
    {
        return None;
    }
    let addr = vreg_of(&load.operands[1])?;
    let madd = func.inst(*def.get(&addr.id)?);
    if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
        return None;
    }
    let f1 = vreg_of(&madd.operands[1])?;
    let f2 = vreg_of(&madd.operands[2])?;
    let base = vreg_of(&madd.operands[3])?;
    let is_sext_iv = |factor: VReg| -> bool {
        let Some(&id) = def.get(&factor.id) else {
            return false;
        };
        let inst = func.inst(id);
        inst.opcode == AArch64Opcode::Sxtw
            && inst.operands.len() == 2
            && vreg_of(&inst.operands[1]).is_some_and(|s| same_as_iv(func, def, s, iv))
    };
    let idx_ok = |factor: VReg| same_as_iv(func, def, factor, iv) || is_sext_iv(factor);
    let es_ok = |factor: VReg| const_value(func, def, factor) == Some(ELEM_BYTES);
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

/// Walk BACKWARD from a diamond tail (a block that assigns the result) up a
/// single-pred pass-through chain to the 2-successor SPLIT (compare) block.
/// Returns `(split, entry, path)` where `entry` is the split's successor that
/// begins this side and `path` is every block from `entry` down to `tail`.
/// Generalizes `neon_minmax::walk_back_to_split`.
///
/// A 2-successor block that is a REDUNDANT
/// in-loop bounds guard on the path is SKIPPED (treated as a pass-through) rather
/// than mistaken for the diamond's compare split. Such a guard is
/// `cmp iv, N; b.lo <in>; b <out>` where `<in>` is the block we came from (so it
/// continues toward the tail), `<out>` leaves the loop body, `iv` is the
/// induction, and the guard's bound AGREES with the loop's own bound `loop_bound`
/// (== `N`). The bridge leaves one of these on the `then` arm of `if a[i] REL t {
/// s += a[i] }` when it fails to prove the reload's bounds check redundant.
///
/// SOUND to elide from the diamond: the vector loop only runs for
/// `iv ∈ [0, N-width]`, and every index it processes is `< N == guard-bound`, so
/// the guard's in-loop edge is ALWAYS taken there — the `<out>` (panic/OOB) edge
/// is dead over the vectorized range. The untouched scalar loop still performs
/// the guard for the `< width` tail, so its trap behaviour is preserved
/// verbatim. Requiring bound AGREEMENT (not merely "some" guard) is what rules
/// out a guard `iv < M` with `M < N`, which could trap in the scalar loop at an
/// index the vector loop would blindly sum.
fn walk_back_to_split_thru_guards(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    iv: VReg,
    loop_bound: Option<ChainBound>,
    tail: BlockId,
) -> Option<(BlockId, BlockId, Vec<BlockId>)> {
    let mut path = vec![tail];
    let mut cur = tail;
    for _ in 0..64 {
        let preds = &func.block(cur).preds;
        if preds.len() != 1 {
            return None;
        }
        let p = preds[0];
        let ps = &func.block(p).succs;
        match ps.len() {
            2 => {
                // A redundant in-loop bounds guard whose in-edge is `cur` and
                // whose bound matches the loop bound is a pass-through: skip it
                // and keep walking toward the real compare split.
                if let Some(lb) = loop_bound
                    && let Some((gx, gb, t_lo)) = recognize_chain_guard(func, p, body)
                    && t_lo == cur
                    && same_as_iv(func, def, gx, iv)
                    && chain_bound_agrees(func, def, lb, gb)
                {
                    path.push(p);
                    cur = p;
                    continue;
                }
                return Some((p, cur, path));
            }
            1 => {
                path.push(p);
                cur = p;
            }
            _ => return None,
        }
    }
    None
}

/// Materialize a non-negative i32-range constant into a fresh preheader vreg of
/// `class` via the isel `Movz`(+`Movk`) convention. Used for the compile-time
/// vector guard limit, which `apply_chain` cannot read from a register (the loop
/// bound is a folded immediate inside the loop). Mirrors
/// `neon_minmax::materialize_const`.
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

/// Read-only lane-wise validator for the chain's term values (compare operands
/// and addends). Mirrors [`Recognized::node_ok`] but uses [`chain_load_base`]
/// (the mixed `Gpr64`-direct / `Sxtw(iv)` addressing) and does NOT require the
/// term to contain a select — the diamond's branch IS the predicate. Populates
/// the shared `loads` / `bases` / `selects` / `inv_leaves` maps (which
/// `apply_chain` reuses through the existing [`lower`]). Rejects the induction
/// and any reduction accumulator as a lane-wise value (fail closed).
struct ChainValidator<'a> {
    func: &'a MachFunction,
    dom: &'a DomTree,
    def: &'a HashMap<u32, InstId>,
    loop_insts: &'a HashSet<InstId>,
    iv: VReg,
    accs: HashSet<u32>,
    preheader: BlockId,
    loads: HashMap<u32, VReg>,
    bases: Vec<VReg>,
    selects: HashMap<u32, SelectPlan>,
    inv_leaves: HashSet<u32>,
    seen: HashSet<u32>,
}

impl ChainValidator<'_> {
    fn node_ok(&mut self, val: VReg) -> bool {
        // Never a lane-wise value: the induction or any reduction accumulator.
        if val == self.iv || self.accs.contains(&val.id) {
            return false;
        }
        if const_value(self.func, self.def, val).is_some() {
            return true;
        }
        if !self.seen.insert(val.id) {
            return true;
        }
        let Some(&def_id) = self.def.get(&val.id) else {
            return false;
        };
        // A value defined OUTSIDE the loop that is not a small constant: accept
        // as a loop-invariant broadcast leaf iff it is a `Gpr32` scalar whose def
        // dominates the preheader (available to DUP there). Otherwise BAIL.
        if !self.loop_insts.contains(&def_id) {
            let Some(db) = block_of_inst(self.func, def_id) else {
                return false;
            };
            if val.class == RegClass::Gpr32 && self.dom.dominates(db, self.preheader) {
                self.inv_leaves.insert(val.id);
                return true;
            }
            return false;
        }
        let opcode = self.func.inst(def_id).opcode;
        use AArch64Opcode::*;
        // A load leaf: validate its `a[iv]` address and record the base.
        if opcode == LdrRI {
            let Some(base) =
                chain_load_base(self.func, self.def, self.dom, val, self.iv, self.preheader)
            else {
                return false;
            };
            self.loads.insert(val.id, base);
            if !self.bases.iter().any(|b| b.id == base.id) {
                self.bases.push(base);
            }
            return true;
        }
        // An embedded select: decode it and validate its compare + arm operands.
        if opcode == Csel {
            let Some((plan, _chain)) = decode_select(self.func, self.def, def_id) else {
                return false;
            };
            self.selects.insert(val.id, plan);
            return self.node_ok(plan.cmp_lhs)
                && self.node_ok(plan.cmp_rhs)
                && self.node_ok(plan.arm_if)
                && self.node_ok(plan.arm_else);
        }
        let ops = self.func.inst(def_id).operands.clone();
        match opcode {
            MulRR | AddRR | SubRR | AndRR | OrrRR | EorRR => {
                let (Some(a), Some(b)) = (vreg_of(&ops[1]), vreg_of(&ops[2])) else {
                    return false;
                };
                self.node_ok(a) && self.node_ok(b)
            }
            AddRI | SubRI | AndRI | OrrRI | EorRI => {
                let Some(a) = vreg_of(&ops[1]) else {
                    return false;
                };
                let ok_imm = matches!(imm_of(&ops[2]), Some(v) if (0..=0xFFFF).contains(&v));
                ok_imm && self.node_ok(a)
            }
            LslRI | LsrRI | AsrRI => {
                let Some(a) = vreg_of(&ops[1]) else {
                    return false;
                };
                let ok_sh = matches!(imm_of(&ops[2]), Some(v) if (0..=31).contains(&v));
                ok_sh && self.node_ok(a)
            }
            Madd if ops.len() == 4 => {
                let (Some(a), Some(b), Some(c)) =
                    (vreg_of(&ops[1]), vreg_of(&ops[2]), vreg_of(&ops[3]))
                else {
                    return false;
                };
                self.node_ok(a) && self.node_ok(b) && self.node_ok(c)
            }
            _ => false,
        }
    }
}

/// Recognize ONE predicated-add reduction from its branch diamond. `result` is
/// the per-iteration value written back to `acc` in the latch; it MUST have
/// exactly two in-loop `MovR` defs (the then/else tails). One tail is a copy of
/// `acc` (the identity / `+0` arm); the other is `acc + addend` (the `+a[iv]`
/// arm). Decodes the split compare `a[iv] REL t` into a [`PredSumReduction`]
/// and returns it with the diamond's block set. Fail-closed on any deviation.
/// Analog of `neon_minmax::recognize_minmax_diamond`.
#[allow(clippy::too_many_arguments)]
fn recognize_predsum_diamond(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    body: &HashSet<BlockId>,
    iv: VReg,
    acc: VReg,
    result: VReg,
    loop_bound: Option<ChainBound>,
    validator: &mut ChainValidator<'_>,
) -> Option<(PredSumReduction, DiamondInfo)> {
    // The result phi is materialized as exactly TWO in-loop `MovR` defs.
    let mut tails: Vec<(BlockId, VReg)> = Vec::new();
    for &id in loop_insts {
        let inst = func.inst(id);
        if !produces_def(inst.opcode) {
            continue;
        }
        if !matches!(inst.operands.first(), Some(MachOperand::VReg(d)) if d.id == result.id) {
            continue;
        }
        let (d, s) = copy_like(inst)?; // both defs must be plain copies
        if d != result {
            return None;
        }
        tails.push((block_of_inst(func, id)?, s));
    }
    if tails.len() != 2 {
        return None;
    }

    // One tail assigns a COPY of `acc` (else: `+0`); the other assigns `acc +
    // addend` (then: `+a[iv]`).
    let is_acc = |src: VReg| same_as_iv(func, def, src, acc);
    let (else_tail, then_tail) = if is_acc(tails[0].1) && !is_acc(tails[1].1) {
        (tails[0], tails[1])
    } else if is_acc(tails[1].1) && !is_acc(tails[0].1) {
        (tails[1], tails[0])
    } else {
        return None;
    };

    // then_tail src == `AddRR(acc-copy, addend)` (commutative).
    let then_src = strip_copies(func, def, then_tail.1);
    let add_inst = func.inst(*def.get(&then_src.id)?);
    if add_inst.opcode != AArch64Opcode::AddRR || add_inst.operands.len() != 3 {
        return None;
    }
    let ax = vreg_of(&add_inst.operands[1])?;
    let ay = vreg_of(&add_inst.operands[2])?;
    let addend = if is_acc(ax) {
        ay
    } else if is_acc(ay) {
        ax
    } else {
        return None;
    };
    if addend == acc || addend == iv {
        return None;
    }
    // WIDENING (i64-accumulator) form: when `acc` is `Gpr64`, the ONLY accepted
    // then-arm contribution is the in-loop SIGN-extension `Sxtw(x)` of a
    // lane-wise `Gpr32` value `x` — the shape the bridge emits for
    // `s(i64) += a_i32[iv] as i64` (`as i64` of an `i32` IS sext). The `x` is
    // recorded as the reduction's `addend` and the sext is re-established per
    // lane by the SADDW/SADDW2 lowering. Everything else BAILS fail-closed:
    // in particular a ZERO-extension (`u32 as u64` — a different program on
    // negative bit patterns) is never on this path (`Uxtw` is not even in
    // [`allowed_loop_op`], and a non-`Sxtw` root is rejected right here), so
    // the sign axes can never be crossed.
    let widen_sext = acc.class == RegClass::Gpr64;
    let addend = if widen_sext {
        let sxtw_id = *def.get(&addend.id)?;
        if !loop_insts.contains(&sxtw_id) {
            return None;
        }
        let sxtw = func.inst(sxtw_id);
        if sxtw.opcode != AArch64Opcode::Sxtw || sxtw.operands.len() != 2 {
            return None;
        }
        let x = vreg_of(&sxtw.operands[1])?;
        if x.class != RegClass::Gpr32 {
            return None;
        }
        x
    } else {
        addend
    };
    if addend == acc || addend == iv {
        return None;
    }
    // The addend must be lane-wise (records its load base / broadcast leaf).
    if !validator.node_ok(addend) {
        return None;
    }

    // Both tails trace back through pass-throughs to the SAME split (compare),
    // and converge at ONE join block.
    let (split_then, entry_then, path_then) =
        walk_back_to_split_thru_guards(func, def, body, iv, loop_bound, then_tail.0)?;
    let (split_else, entry_else, path_else) =
        walk_back_to_split_thru_guards(func, def, body, iv, loop_bound, else_tail.0)?;
    if split_then != split_else {
        return None;
    }
    let compare = split_then;
    let then_join = &func.block(then_tail.0).succs;
    let else_join = &func.block(else_tail.0).succs;
    if then_join.len() != 1 || else_join.len() != 1 || then_join[0] != else_join[0] {
        return None;
    }
    let join = then_join[0];

    // Decode the split: `cmp cx, cy; b.<cc> t_target; b f_target`. Only the
    // DIRECT `CmpRR; BCond` form (no CSet materialization, no CmpRI constant
    // compare — a follow-on).
    let c_insts = &func.block(compare).insts;
    let bcond_id = *c_insts
        .iter()
        .rev()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::BCond)?;
    let bcond = func.inst(bcond_id);
    let cc = imm_of(&bcond.operands[0])?;
    let t_target = *branch_targets(bcond).first()?;
    let last = *c_insts.last()?;
    if func.inst(last).opcode != AArch64Opcode::B {
        return None;
    }
    let f_target = *branch_targets(func.inst(last)).first()?;
    // The two edges must be exactly the two diamond entries; `add_on_taken` says
    // whether the BCond-taken (predicate-holds) edge is the `+a[iv]` side.
    let add_on_taken = if t_target == entry_then && f_target == entry_else {
        true
    } else if t_target == entry_else && f_target == entry_then {
        false
    } else {
        return None;
    };
    let cmp_id = nearest_flag_setter_before(func, c_insts, bcond_id)?;
    let cmp = func.inst(cmp_id);
    if cmp.opcode != AArch64Opcode::CmpRR {
        return None;
    }
    let cx = vreg_of(&cmp.operands[0])?;
    let cy = vreg_of(&cmp.operands[1])?;
    if !validator.node_ok(cx) || !validator.node_ok(cy) {
        return None;
    }

    // Reassociate to `select(pred, addend, 0)` and normalize via the proven
    // [`map_relation`]. The taken edge (predicate holds) carries `addend` when
    // `add_on_taken`, else `0`; the fall-through carries the other. `iv` is a
    // safe zero-SENTINEL — it is a `Gpr64` induction, so it can never equal the
    // `Gpr32` addend, and `map_relation` only ever plumbs the two arms through
    // to `arm_if` / `arm_else` (possibly swapping them for `!=`). Reading back
    // which of `arm_if` / `arm_else` map_relation assigned the real addend to
    // tells us whether to accumulate where the mask is all-ones or all-zeros.
    if addend == iv {
        return None;
    }
    let zero_sentinel = iv;
    let (t_arm, f_arm) = if add_on_taken {
        (addend, zero_sentinel)
    } else {
        (zero_sentinel, addend)
    };
    let plan = map_relation(cc, cx, cy, t_arm, f_arm)?;
    let adds_when_mask_true = if plan.arm_if == addend {
        true
    } else if plan.arm_else == addend {
        false
    } else {
        return None;
    };

    let mut blocks = vec![compare];
    blocks.extend(path_then);
    blocks.extend(path_else);
    Some((
        PredSumReduction {
            acc,
            cmp_op: plan.cmp_op,
            cmp_lhs: plan.cmp_lhs,
            cmp_rhs: plan.cmp_rhs,
            addend,
            adds_when_mask_true,
            widen_sext,
        },
        DiamondInfo {
            compare,
            join,
            blocks,
        },
    ))
}

impl PredSumChainRecognized {
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

        // Whitelist every opcode across EVERY body block (no store/call/div/etc).
        // The absence of `StrRI` here makes every `a[iv]` load LOOP-STABLE (the
        // diamond's compare candidate equals its then-block reload).
        let mut loop_insts = HashSet::new();
        for &b in body {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

        // REQUIRED: the block-order-restricted def map (see [`build_live_def_map`]).
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
        // The induction is the `Gpr64` `usize` counter of a `for i in 0..N`
        // loop (the mixed i64-index / i32-element shape the bridge emits for a
        // local fixed-size array). A `Gpr32` induction is not vectorized here.
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

        // Every accumulator is a distinct `Gpr32` (the shipped `.4S` accumulate)
        // or `Gpr64` (the WIDENING `s(i64) += a_i32[iv] as i64` form, which
        // additionally requires an `Sxtw`-rooted addend — enforced per diamond
        // in [`recognize_predsum_diamond`]) with EXACTLY ONE in-loop def (its
        // latch writeback). Collect them first so the diamond validator can
        // reject a term that reads any accumulator as a lane-wise value.
        let mut accs: HashSet<u32> = HashSet::new();
        for (acc, _) in &result_wbs {
            if !matches!(acc.class, RegClass::Gpr32 | RegClass::Gpr64)
                || acc.id == iv.id
                || !accs.insert(acc.id)
            {
                return None;
            }
            if count_loop_defs(func, &loop_insts, *acc) != 1 {
                return None;
            }
        }

        let mut validator = ChainValidator {
            func,
            dom,
            def: &def,
            loop_insts: &loop_insts,
            iv,
            accs: accs.clone(),
            preheader,
            loads: HashMap::new(),
            bases: Vec::new(),
            selects: HashMap::new(),
            inv_leaves: HashSet::new(),
            seen: HashSet::new(),
        };

        // The loop's own `iv <u N` bound, taken from the header loop-continue
        // guard. Used to soundly skip a redundant same-`N` bounds guard the
        // bridge may leave on a diamond's `then` arm (the un-elided reload
        // check); a `then`-arm guard is only elided when its bound AGREES with
        // this one (see [`walk_back_to_split_thru_guards`]).
        let loop_bound: Option<ChainBound> = recognize_chain_guard(func, header, body)
            .filter(|(gx, _, _)| same_as_iv(func, &def, *gx, iv))
            .map(|(_, gb, _)| gb);

        // Recognize each reduction's branch diamond (predicated ADD).
        let mut reductions: Vec<PredSumReduction> = Vec::new();
        let mut diamond_map: HashMap<BlockId, DiamondInfo> = HashMap::new();
        for (acc, result) in &result_wbs {
            let (red, dinfo) = recognize_predsum_diamond(
                func,
                &def,
                &loop_insts,
                body,
                iv,
                *acc,
                *result,
                loop_bound,
                &mut validator,
            )?;
            if diamond_map.insert(dinfo.compare, dinfo).is_some() {
                return None; // two reductions sharing one compare block => BAIL
            }
            reductions.push(red);
        }

        // Walk the chain header -> ... -> latch, classifying every block as the
        // loop-continue / bounds guard, a condsum diamond, or a pass-through, and
        // proving SINGLE-N agreement + full coverage.
        let bound = Self::walk_chain(func, &def, body, header, latch, iv, &diamond_map)?;
        // The bound must be a COMPILE-TIME constant `N` — either the folded
        // immediate (`CmpRI`) or a register holding a small `Movz` constant (the
        // shape the bridge emits for `const N: usize = ...`, `cmp iv, Nreg`).
        // `apply_chain` materializes `main_bound = N - (width-1)` at compile time,
        // so a non-const (truly variable) bound is not supported here.
        let n = match bound {
            ChainBound::Const(n) => n,
            ChainBound::Reg(r) => const_value(func, &def, r)?,
        };
        if !(1..=i32::MAX as i64).contains(&n) {
            return None;
        }

        // Release the validator's borrows of `def` / `loop_insts` (it holds them
        // by reference) before moving those into the recognized plan.
        let ChainValidator {
            loads,
            bases,
            selects,
            inv_leaves,
            ..
        } = validator;

        Some(PredSumChainRecognized {
            guard: header,
            preheader,
            preheader_term,
            iv,
            bound: n,
            def,
            loop_insts,
            loads,
            bases,
            selects,
            inv_leaves,
            reductions,
        })
    }

    /// Classify the chain and return its single loop bound. Fail-closed on any
    /// block off the header->latch structure or a limit disagreement. Mirrors
    /// `neon_minmax::ChainRecognized::walk_chain`.
    fn walk_chain(
        func: &MachFunction,
        def: &HashMap<u32, InstId>,
        body: &HashSet<BlockId>,
        header: BlockId,
        latch: BlockId,
        iv: VReg,
        diamond_map: &HashMap<BlockId, DiamondInfo>,
    ) -> Option<ChainBound> {
        let mut visited: HashSet<BlockId> = HashSet::new();
        let mut bound: Option<ChainBound> = None;
        let mut cur = header;
        for _ in 0..(body.len() + 1) {
            if !body.contains(&cur) || visited.contains(&cur) {
                return None;
            }
            if cur == latch {
                visited.insert(latch);
                break;
            }
            let succs = &func.block(cur).succs;
            let in_body = succs.iter().filter(|s| body.contains(s)).count();
            let out_body = succs.len() - in_body;
            if succs.len() == 2 && in_body == 1 && out_body == 1 {
                // Loop-continue / surviving bounds-guard diamond.
                let (x, b, t_lo) = recognize_chain_guard(func, cur, body)?;
                if !same_as_iv(func, def, x, iv) {
                    return None;
                }
                match bound {
                    Some(bb) if !chain_bound_agrees(func, def, bb, b) => return None,
                    None => bound = Some(b),
                    _ => {}
                }
                visited.insert(cur);
                cur = t_lo;
            } else if succs.len() == 2 && in_body == 2 {
                // Condsum branch diamond (must be a recognized reduction's).
                let dinfo = diamond_map.get(&cur)?;
                for &b in &dinfo.blocks {
                    if !body.contains(&b) || !visited.insert(b) {
                        return None;
                    }
                }
                if !body.contains(&dinfo.join) {
                    return None;
                }
                cur = dinfo.join;
            } else if succs.len() == 1 && in_body == 1 {
                // Pass-through (its bounds guard was elided).
                visited.insert(cur);
                cur = succs[0];
            } else {
                return None;
            }
        }
        // Every body block accounted for exactly once, and the header must have
        // established the bound (there is at least the loop-continue guard).
        if visited.len() != body.len() {
            return None;
        }
        bound
    }
}

/// Vectorize a [`PredSumChainRecognized`] forward-chain predicated-add loop
/// (i32 `.4S` elements, K independent reductions). A chain containing any
/// `adds_when_mask_true` or [`PredSumReduction::widen_sext`] reduction takes
/// the WIDE shape: [`UNROLL_CHAIN`] (8) independent accumulators over an 8Q
/// bottom-tested single-block vector loop (see the constant's doc), with the
/// accumulate lowered as a NEGATED by-mask MAC — SMLAL/SMLAL2-by-mask into
/// `.2D` accumulators for the widening shape, MLA.4S-by-mask for the `Gpr32`
/// shape — drained via a wrapping `SubRR` fold (see the accumulate arms). A
/// chain of only `!=`-negated reductions keeps the shipped [`UNROLL`] (4)
/// top-tested AND+EOR+ADD shape. Purely ADDITIVE: splices a vector main loop
/// between the preheader and the header and never edits the scalar chain, so
/// the scalar loop remains correct by construction and finishes the
/// `< width` tail (15 / 31 elements max).
fn apply_chain(func: &mut MachFunction, rec: &PredSumChainRecognized) -> bool {
    let vf = VF;
    let arr_code = ARR_S4;
    let elem_code = ELEM_S;
    let const_class = RegClass::Gpr32;
    // A chain with any NEGATED-accumulate reduction takes the WIDE shape
    // ([`UNROLL_CHAIN`] accumulators, single-block bottom-tested loop): the
    // widening (`widen_sext`) SMLAL-by-mask arm and the `Gpr32` `.4S`
    // MLA-by-mask arm (both `adds_when_mask_true` forms) are 2-3-op/Q shapes
    // whose 3-cycle accumulate latency needs 8 independent chains to reach
    // the M4's SIMD ISSUE floor (measured: 4-acc MLA = 0.75 cy/Q latency-
    // bound == LLVM's 3-op floor, 8-acc = 0.50 cy/Q, 12 = no further gain —
    // the measured e01/csI wins). A chain of ONLY `!=`-negated reductions
    // keeps the shipped 4-accumulator top-tested AND+EOR+ADD shape unchanged
    // (4 ops/Q, already at the issue floor at 4 accumulators).
    let wide = rec
        .reductions
        .iter()
        .any(|red| red.widen_sext || red.adds_when_mask_true);
    let unroll = if wide { UNROLL_CHAIN } else { UNROLL };
    let width = unroll as i64 * vf; // 32 wide / 16 narrow

    // WIDE: single-block BOTTOM-TESTED vector loop (the `strided_store_unroll`
    // shape): `vh` is the once-per-entry guard, `vb` self-loops on its own
    // bottom `iv <u main_bound` re-test (one taken branch per iteration,
    // matching LLVM's `subs; b.ne` loop control), `vx` drains. The guard
    // condition is IDENTICAL to the top-tested form — `iv <u main_bound` is
    // (re-)tested before every body execution, first in `vh`, then at the
    // bottom of `vb` — so exactly the same iterations run.
    // NARROW: the shipped top-tested `vh -> vb -> vl -> vh` shape.
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = if wide {
        None
    } else {
        Some(func.create_block())
    };
    let vx = func.create_block();
    if let Some(vl) = vl {
        insert_new_blocks_before(func, rec.guard, &[vh, vb, vl, vx]);
        func.add_edge(vh, vb);
        func.add_edge(vh, vx);
        func.add_edge(vb, vl);
        func.add_edge(vl, vh);
    } else {
        insert_new_blocks_before(func, rec.guard, &[vh, vb, vx]);
        func.add_edge(vh, vb);
        func.add_edge(vh, vx);
        func.add_edge(vb, vb);
        func.add_edge(vb, vx);
    }

    let pre = rec.preheader_term;

    // --- Preheader: per-reduction `unroll` zeroed vector accumulators
    // (MOVI 0 = the ADD identity).
    let vacc: Vec<Vec<VReg>> = rec
        .reductions
        .iter()
        .map(|_| {
            (0..unroll)
                .map(|_| {
                    let a = alloc(func, RegClass::Fpr128);
                    emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(a), imm(0)]);
                    a
                })
                .collect()
        })
        .collect();

    // --- Guard bound. The scalar loop-continue is `iv <u N` (UNSIGNED `LO`), so
    // the vector guard is UNSIGNED too. `N` is a compile-time constant in
    // `[1, i32::MAX]`, so the guard limit `main = N - (width-1)` (the largest
    // `iv` whose full `width`-block fits in `[0, N)`) is computed at COMPILE
    // time; when `N < width` no full block fits and we use `0` so `iv <u 0`
    // never passes (the scalar loop does everything). `iv` is `Gpr64`, matching
    // the scalar's 64-bit `CmpRI(iv, N)` bit-for-bit.
    let main_bound_k = if rec.bound >= width {
        rec.bound - (width - 1)
    } else {
        0
    };
    let main_bound = materialize_const(func, pre, main_bound_k, RegClass::Gpr64);

    // --- Preheader: element-size const + one running pointer per candidate base
    // (`p = base + iv0*elem`, the `Gpr64` induction used directly — the exact
    // mixed i64-index / i32-element addressing the scalar loop performs).
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(ELEM_BYTES)],
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
                vec![vreg(p), vreg(rec.iv), vreg(c_es), vreg(*base)],
            );
            p
        })
        .collect();

    // --- Vector header: UNSIGNED guard `iv <u main_bound` (== `iv+width-1 <u
    // N`), matching the scalar's `iv <u N` loop-continue in the same 64-bit width.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Vector body loads. NARROW: all paired post-index LDPs up front (the
    // shipped shape). WIDE: each LDP is emitted right before the two Q-blocks
    // that consume it (interleaved), bounding Fpr128 peak liveness to the
    // `unroll` accumulators + the in-flight pair + temps — well inside the
    // 32-register vector file for the linear-scan allocator.
    let mut loaded: HashMap<(u32, usize), VReg> = HashMap::new();
    if !wide {
        for (base, p) in rec.bases.iter().zip(&ptrs) {
            for pair in 0..unroll / 2 {
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
        iv: rec.iv,
        acc: rec.iv, // reset to each reduction's acc below (never a lane value)
        accum: 0,
        vbody: vb,
        preheader_term: pre,
        arr_code,
        elem_code,
        const_class,
        is_i64: false,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        loads: rec.loads.clone(),
        selects: rec.selects.clone(),
        inv_leaves: rec.inv_leaves.clone(),
        loaded,
        const_cache: HashMap::new(),
        inv_cache: HashMap::new(),
        memo: HashMap::new(),
    };
    for k in 0..unroll {
        if wide && k % 2 == 0 {
            // Load the Q-pair for blocks {k, k+1} from every base's running
            // pointer (post-index +32 walks it across the pairs).
            for (base, p) in rec.bases.iter().zip(&ptrs) {
                let q0 = alloc(func, RegClass::Fpr128);
                let q1 = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonLdpQPost,
                    vec![vreg(q0), vreg(q1), vreg(*p), imm(32)],
                );
                ctx.loaded.insert((base.id, k), q0);
                ctx.loaded.insert((base.id, k + 1), q1);
            }
        }
        ctx.accum = k;
        ctx.memo.clear();
        for (ri, red) in rec.reductions.iter().enumerate() {
            ctx.acc = red.acc;
            let acc = vacc[ri]
                .get(k)
                .copied()
                .expect("one vector accumulator per unrolled lane");
            let Some(lhs) = lower(func, &mut ctx, red.cmp_lhs) else {
                return false;
            };
            let Some(rhs) = lower(func, &mut ctx, red.cmp_rhs) else {
                return false;
            };
            let Some(addv) = lower(func, &mut ctx, red.addend) else {
                return false;
            };
            // mask = cmp_op(lhs, rhs): per-lane all-ones iff the predicate holds.
            let mask = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vb,
                red.cmp_op,
                vec![vreg(mask), vreg(lhs), vreg(rhs), imm(arr_code)],
            );
            // Accumulate. When the addend is added on the all-ONES mask lanes
            // (`adds_when_mask_true`), the mask lane {-1, 0} IS the multiplier
            // of a NEGATED by-mask MAC — SMLAL/SMLAL2 for the widening i64
            // shape, MLA.4S for the `Gpr32` shape — collapsing the masking AND
            // into the accumulate (drain closes with one wrapping SubRR).
            // Otherwise (the `!=`/CMEQ negation adds on the all-ZERO lanes)
            // the masked value is `addend ^ (mask & addend) == addend & ~mask`
            // from proven per-lane AND / EOR, accumulated positively.
            if red.widen_sext && red.adds_when_mask_true {
                // WIDENING accumulate by SMLAL-BY-MASK (NEGATED): the compare
                // mask lane is exactly `-1` (all-ones) when the predicate
                // holds and `0` otherwise, so the faithfully-proven
                // SMLAL/SMLAL2 per-lane obligation
                // `acc.d[j] += sext64(a.s[j]) * sext64(m.s[j])` (SMLAL covers
                // `.4S` lanes {0,1}, SMLAL2 lanes {2,3}; arbitrary Vm lanes —
                // the same obligation the widening-dot vectorizer discharges)
                // contributes `sext64(a) * (-1) == -sext64(a)` on a TRUE lane
                // and `0` on a FALSE lane, all mod 2^64. The accumulators thus
                // hold the NEGATED predicated sum, and the drain folds them
                // into the scalar accumulator with a single wrapping `SubRR`
                // (`acc - (-sum) == acc + sum` mod 2^64 — exact for every
                // input incl. `i32::MIN` lanes and i64 wrap, since the `.2D`
                // lane width equals the scalar acc width). This drops the
                // masking AND entirely: 3 vector ops per Q-block instead of
                // 4, which is what takes the loop from LLVM parity to a win —
                // the M4 sustains ~4 of these ops/cycle regardless of mix, so
                // runtime tracks the op count.
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonSmlalV,
                    vec![vreg(acc), vreg(addv), vreg(mask), imm(arr_code)],
                );
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonSmlal2V,
                    vec![vreg(acc), vreg(addv), vreg(mask), imm(arr_code)],
                );
                continue;
            }
            if red.adds_when_mask_true {
                // `Gpr32` (`.4S`) accumulate by MLA-BY-MASK (NEGATED): the
                // compare mask lane is exactly `-1` (all-ones) when the
                // predicate holds and `0` otherwise, so the faithfully-proven
                // MLA.4S per-lane obligation
                // `acc.s[i] += a.s[i] * m.s[i]` (mod 2^32; arbitrary Vm lanes)
                // contributes `a * (-1) == -a mod 2^32` on a TRUE lane —
                // exact for EVERY i32 including `i32::MIN` (unconditionally
                // `(-1)*a ≡ -a (mod 2^32)`) — and `0` on a FALSE lane. The
                // accumulators thus hold the NEGATED predicated sum, and the
                // drain folds them into the scalar accumulator with a single
                // wrapping `SubRR` (`acc - (-sum) == acc + sum` mod 2^32 —
                // the scalar acc is a wrapping i32, i.e. the same mod-2^32
                // group, so every lane value is identical to the scalar
                // predicated add). This collapses the masking AND and the
                // accumulate ADD into ONE op: 2 vector ops per Q-block
                // instead of 3, below LLVM's cmgt+and+add issue floor —
                // the M4 sustains ~4 of these ops/cycle regardless of mix,
                // so runtime tracks the op count (the exact SMLAL-by-mask
                // trick above, at `.4S` width). MLA's Vd is a TIED def-use
                // (the accumulate READS it — has_tied_def_use).
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonMlaV,
                    vec![vreg(acc), vreg(addv), vreg(mask), imm(arr_code)],
                );
                continue;
            }
            // Only the `!=`-negated select arm reaches here (both
            // `adds_when_mask_true` forms take the by-mask MAC arms above):
            // the addend is added on the all-ZERO mask lanes, so the masked
            // value is `addend ^ (mask & addend) == addend & ~mask` — built
            // from proven per-lane AND / EOR.
            let masked = {
                let t = bin(func, &ctx, AArch64Opcode::NeonAndV, mask, addv, false);
                bin(func, &ctx, AArch64Opcode::NeonEorV, addv, t, false)
            };
            if red.widen_sext {
                // WIDENING accumulate (the `!=`-negated select arm, where the
                // addend is added on the all-ZERO mask lanes and the masked
                // value is built by AND+EOR): `vacc.2D[j] += sext64(masked.4S
                // lane)` via the faithfully-proven SADDW/SADDW2 signed
                // widening add-wide (SADDW covers `.4S` lanes {0,1}, SADDW2
                // lanes {2,3}). Per lane this equals the scalar predicated i64
                // add EXACTLY: a non-contributing lane adds `sext64(0) == 0`;
                // a contributing lane adds `sext64(a_lane)` — the scalar
                // `as i64` term, INCLUDING negative values (sext reproduces
                // the sign). The `.2D` lane width (64) equals the scalar acc
                // width, so wrap is identically mod 2^64 and no extra N bound
                // is needed. SADDW is the ISA's plain THREE-OPERAND form (Vd
                // pure def, the i64 addend Vn a SEPARATE use — NOT tied);
                // passing the same vreg as Vd and Vn accumulates in place.
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonSaddwV,
                    vec![vreg(acc), vreg(acc), vreg(masked), imm(arr_code)],
                );
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonSaddw2V,
                    vec![vreg(acc), vreg(acc), vreg(masked), imm(arr_code)],
                );
            } else {
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(acc), vreg(acc), vreg(masked), imm(arr_code)],
                );
            }
        }
    }
    if let Some(vl) = vl {
        // --- NARROW: separate latch block advances iv by width (top-tested).
        emit(func, vb, AArch64Opcode::B, vec![block(vl)]);
        emit(
            func,
            vl,
            AArch64Opcode::AddRI,
            vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
        );
        emit(func, vl, AArch64Opcode::B, vec![block(vh)]);
    } else {
        // --- WIDE bottom test: advance iv by width IN PLACE (every body use
        // of the lane values is complete; the body itself never reads `iv` —
        // the loads walk post-index running pointers), then re-test the SAME
        // unsigned guard `iv <u main_bound` at the bottom: continue
        // (self-loop) or fall through to the drain.
        emit(
            func,
            vb,
            AArch64Opcode::AddRI,
            vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
        );
        emit(
            func,
            vb,
            AArch64Opcode::CmpRR,
            vec![vreg(rec.iv), vreg(main_bound)],
        );
        emit(func, vb, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
        emit(func, vb, AArch64Opcode::B, vec![block(vx)]);
    }

    // --- Vector exit: for each reduction combine its accumulators (balanced
    // tree), horizontally reduce (UMOV each lane + scalar add), and ADD-fold into
    // the scalar accumulator (still holding its pre-loop seed — the vector loop
    // never wrote it; the scalar tail continues from here). A WIDENING reduction
    // drains in the `.2D` shape (2 i64 lanes per accumulator, `Gpr64` scalars —
    // neon_array's proven `.2D` drain); a `Gpr32` reduction drains in the shipped
    // `.4S` shape, byte-identically.
    for (ri, red) in rec.reductions.iter().enumerate() {
        let (r_arr, r_lanes, r_elem, r_class) = if red.widen_sext {
            (ARR_D2, VF_I64, ELEM_D, RegClass::Gpr64)
        } else {
            (arr_code, vf, elem_code, const_class)
        };
        let mut level = vacc[ri].clone();
        while level.len() > 1 {
            let mut next = Vec::new();
            let mut i = 0;
            while i + 1 < level.len() {
                let d = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vx,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(d), vreg(level[i]), vreg(level[i + 1]), imm(r_arr)],
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
        let lane_regs: Vec<VReg> = (0..r_lanes)
            .map(|lane| {
                let w = alloc(func, r_class);
                emit(
                    func,
                    vx,
                    AArch64Opcode::NeonUmovGen,
                    vec![vreg(w), vreg(vsum), imm(lane), imm(r_elem)],
                );
                w
            })
            .collect();
        let mut fold = lane_regs.clone();
        while fold.len() > 1 {
            let mut next = Vec::new();
            let mut i = 0;
            while i + 1 < fold.len() {
                let d = alloc(func, r_class);
                emit(
                    func,
                    vx,
                    AArch64Opcode::AddRR,
                    vec![vreg(d), vreg(fold[i]), vreg(fold[i + 1])],
                );
                next.push(d);
                i += 2;
            }
            if i < fold.len() {
                next.push(fold[i]);
            }
            fold = next;
        }
        // A by-mask MAC reduction (SMLAL-by-mask on the widening i64 shape,
        // MLA-by-mask on the `Gpr32` `.4S` shape — every `adds_when_mask_true`
        // arm) accumulated the NEGATED predicated sum (see the accumulate arms
        // above): fold it into the scalar accumulator with a wrapping SUB
        // (`acc - (-sum) == acc + sum`, mod 2^64 resp. mod 2^32 — the lane
        // width equals the scalar accumulator width in both shapes, so the
        // fold is exact for every input incl. `i32::MIN` lanes and wrap);
        // the `!=`-negated shape accumulated positively and folds with the
        // plain wrapping ADD.
        let fold_op = if red.adds_when_mask_true {
            AArch64Opcode::SubRR
        } else {
            AArch64Opcode::AddRR
        };
        emit(
            func,
            vx,
            fold_op,
            vec![vreg(red.acc), vreg(red.acc), vreg(fold[0])],
        );
    }
    emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);

    // --- COMMIT: splice the fresh blocks between the preheader and the header.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.guard, vh) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.guard);
    func.add_edge(rec.preheader, vh);
    func.add_edge(vx, rec.guard);
    true
}

// ---------------------------------------------------------------------------
// Transformation
// ---------------------------------------------------------------------------

struct LowerCtx {
    iv: VReg,
    acc: VReg,
    accum: usize,
    vbody: BlockId,
    preheader_term: InstId,
    /// NEON arrangement operand code for same-shape arithmetic/compare ops
    /// (`ARR_S4` for the i32 `.4S` path, `ARR_D2` for the i64 `.2D` path).
    arr_code: i64,
    /// NEON element-size code for scalar broadcasts (`ELEM_S` / `ELEM_D`).
    elem_code: i64,
    /// Register class of the scalar half of a broadcast constant.
    const_class: RegClass,
    /// True on the i64 (`.2D`) path: multiply lowering is unreachable
    /// (recognition BAILS) and the single-op min/max/abs fast paths are
    /// skipped (no `.2D` SMAX/…; `ABS` proof is `.4S`-only).
    is_i64: bool,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    loads: HashMap<u32, VReg>,
    selects: HashMap<u32, SelectPlan>,
    inv_leaves: HashSet<u32>,
    loaded: HashMap<(u32, usize), VReg>,
    const_cache: HashMap<i64, VReg>,
    /// Loop-invariant scalar vreg id -> its DUP-broadcast `4 x i32` (persists
    /// across accumulators; the value is identical in every lane and iteration).
    inv_cache: HashMap<u32, VReg>,
    /// Per-accumulator memo of already-lowered scalar values.
    memo: HashMap<u32, VReg>,
}

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    // Per-width parameters: lanes per vector iteration, element size, NEON
    // codes, and the horizontal-reduce shape. i32 = `.4S` (sign-extension
    // guard); i64 = `.2D` (precheck + unsigned guard — see the module docs and
    // `neon_array::apply_i64` for the full soundness argument).
    let (vf, elem_bytes, arr_code, elem_code, const_class) = if rec.is_i64 {
        (VF_I64, ELEM_BYTES_I64, ARR_D2, ELEM_D, RegClass::Gpr64)
    } else {
        (VF, ELEM_BYTES, ARR_S4, ELEM_S, RegClass::Gpr32)
    };
    let width = UNROLL as i64 * vf;

    // Fresh blocks. The i64 path gets an extra PRECHECK block (`pv`) carrying
    // the signed `n < WIDTH` skip in front of the unsigned vector header.
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
    insert_new_blocks_before(func, rec.guard, &fresh);

    // Internal edges among the fresh blocks only — the preheader->guard redirect
    // is deferred to the COMMIT so a lowering failure cannot leave a broken CFG.
    if let Some(pv) = pv {
        func.add_edge(pv, vh);
        func.add_edge(pv, rec.guard);
    }
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: UNROLL zeroed vector accumulators (MOVI 0).
    let vacc: Vec<VReg> = (0..UNROLL)
        .map(|_| {
            let a = alloc(func, RegClass::Fpr128);
            emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(a), imm(0)]);
            a
        })
        .collect();

    // --- Preheader: the element-size constant + ONE RUNNING POINTER per array
    // stream (`p = base + idx0*elem_bytes`; the preheader runs once, before the
    // loop). i32 additionally sign-extends `iv`/`bound` (the sxtw guard); i64
    // uses `iv` directly (already 64-bit).
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(elem_bytes)],
    );
    let main_bound = alloc(func, RegClass::Gpr64);
    let si0 = if rec.is_i64 {
        rec.iv
    } else {
        let nb64 = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Sxtw,
            vec![vreg(nb64), vreg(rec.bound)],
        );
        // `main_bound = sxtw(bound) - (width-1)` — exact in i64 (sxtw(bound)
        // is in i32 range so the subtract cannot wrap).
        emit_before(
            func,
            pre,
            AArch64Opcode::SubRI,
            vec![vreg(main_bound), vreg(nb64), imm(width - 1)],
        );
        let si0 = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Sxtw,
            vec![vreg(si0), vreg(rec.iv)],
        );
        si0
    };
    let ptrs: Vec<VReg> = rec
        .bases
        .iter()
        .map(|base| {
            let p = alloc(func, RegClass::Gpr64);
            // p = base + si0*elem   (Madd d, n, m, a = a + n*m).
            emit_before(
                func,
                pre,
                AArch64Opcode::Madd,
                vec![vreg(p), vreg(si0), vreg(c_es), vreg(*base)],
            );
            p
        })
        .collect();

    if let Some(pv) = pv {
        // --- i64 Precheck: `main_bound = n - (WIDTH-1)`; SIGNED `n < WIDTH`
        // skips the vector loop entirely (covers n <= 0 and negative-as-signed
        // n; `main_bound`'s wrap is dead on the skip path). Otherwise
        // `main_bound` is exact in [1, 2^63-WIDTH].
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
            vec![imm(CC_LT), block(rec.guard)],
        );
        emit(func, pv, AArch64Opcode::B, vec![block(vh)]);

        // --- i64 Vector header: UNSIGNED `iv <u main_bound` ⇒ full 8-lane
        // block in bounds (see neon_array::apply_i64 for the wrap-freedom
        // proof; iv and main_bound are both < 2^63 on this path).
        emit(
            func,
            vh,
            AArch64Opcode::CmpRR,
            vec![vreg(rec.iv), vreg(main_bound)],
        );
        emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
        emit(func, vh, AArch64Opcode::B, vec![block(vx)]);
    } else {
        // --- i32 Vector header: guard `sxtw(iv) < main_bound` — algebraically
        // `sxtw(iv) + (width-1) < sxtw(bound)` with the add hoisted (exact:
        // both sides stay within i32 range in i64 arithmetic, so neither form
        // can wrap) — enough for a full `width`-lane block.
        let gi = alloc(func, RegClass::Gpr64);
        emit(func, vh, AArch64Opcode::Sxtw, vec![vreg(gi), vreg(rec.iv)]);
        emit(
            func,
            vh,
            AArch64Opcode::CmpRR,
            vec![vreg(gi), vreg(main_bound)],
        );
        emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LT), block(vb)]);
        emit(func, vh, AArch64Opcode::B, vec![block(vx)]);
    }

    // --- Vector body: walk each stream's RUNNING pointer with `UNROLL/2`
    // post-index `LDP Qt1, Qt2, [p], #32` pair loads — bit-identical
    // (little-endian) to the per-vector `LD1`s they replace: the SAME 64 bytes
    // per iteration in the SAME order, so accumulator `k` still reads elements
    // `[iv+vf*k, iv+vf*(k+1))`. The pointer advances by exactly
    // `width*elem_bytes = 64` bytes per iteration while the latch advances
    // `iv` by `width`, so `p == base + idx*elem` holds at every header
    // evaluation (the guard keeps `iv` wrap-free).
    let mut loaded: HashMap<(u32, usize), VReg> = HashMap::new();
    for (base, p) in rec.bases.iter().zip(&ptrs) {
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

    let mut ctx = LowerCtx {
        iv: rec.iv,
        acc: rec.acc,
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
        selects: rec.selects.clone(),
        inv_leaves: rec.inv_leaves.clone(),
        loaded,
        const_cache: HashMap::new(),
        inv_cache: HashMap::new(),
        memo: HashMap::new(),
    };
    for (k, &acc) in vacc.iter().enumerate().take(UNROLL) {
        ctx.accum = k;
        ctx.memo.clear();
        // Root-select COUNTING fusion: when the reduction term is EXACTLY
        // `select(cond, 1, 0)`, the accumulate is `acc -= mask` — the compare
        // mask is `-1` per true lane and `0` per false lane, so subtracting it
        // adds exactly the selected 1/0 (clang's CMEQ+SUB shape). One proven
        // SUB replaces the `mask & 1` AND plus the accumulate ADD. The
        // arm-swapped mirror `select(cond, 0, 1)` (e.g. from `!=`) accumulates
        // `acc += mask + 1` (`-1+1 = 0` where cond holds, `0+1 = 1` otherwise).
        // `plan.arm_if` is what the ALL-ONES mask selects (map_relation already
        // folded any operand/arm swaps), so the const checks are cc-agnostic.
        // Only fires at the term ROOT (the AddRR operand itself); embedded
        // selects keep the general paths in `lower_select`. Width-agnostic:
        // the compares and ADD/SUB all have proven `.2D` forms, so the i64
        // count-eq lowers to `CMEQ.2D` + `SUB.2D` here.
        if let Some(plan) = ctx.selects.get(&rec.term.id).copied() {
            let if1 = const_value(func, &ctx.def, plan.arm_if) == Some(1)
                && const_value(func, &ctx.def, plan.arm_else) == Some(0);
            let if0 = const_value(func, &ctx.def, plan.arm_if) == Some(0)
                && const_value(func, &ctx.def, plan.arm_else) == Some(1);
            if if1 || if0 {
                let Some(lhs) = lower(func, &mut ctx, plan.cmp_lhs) else {
                    return false;
                };
                let Some(rhs) = lower(func, &mut ctx, plan.cmp_rhs) else {
                    return false;
                };
                let mask = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    plan.cmp_op,
                    vec![vreg(mask), vreg(lhs), vreg(rhs), imm(ctx.arr_code)],
                );
                if if1 {
                    // acc -= mask  ==  acc += select(cond, 1, 0) per lane.
                    emit(
                        func,
                        vb,
                        AArch64Opcode::NeonSubV,
                        vec![vreg(acc), vreg(acc), vreg(mask), imm(ctx.arr_code)],
                    );
                } else {
                    // acc += (mask + 1)  ==  acc += select(cond, 0, 1) per lane.
                    let ones = const_vec(func, &mut ctx, 1);
                    let t = bin(func, &ctx, AArch64Opcode::NeonAddV, mask, ones, true);
                    emit(
                        func,
                        vb,
                        AArch64Opcode::NeonAddV,
                        vec![vreg(acc), vreg(acc), vreg(t), imm(ctx.arr_code)],
                    );
                }
                continue;
            }
        }
        let Some(vterm) = lower(func, &mut ctx, rec.term) else {
            return false;
        };
        emit(
            func,
            vb,
            AArch64Opcode::NeonAddV,
            vec![vreg(acc), vreg(acc), vreg(vterm), imm(ctx.arr_code)],
        );
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: advance iv by width.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector exit: combine accumulators (balanced adds), horizontally reduce
    // (UMOV each lane + scalar add), then fold into the scalar accumulator.
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
                vec![
                    vreg(d),
                    vreg(level[i]),
                    vreg(level[i + 1]),
                    imm(ctx.arr_code),
                ],
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
    let lane_regs: Vec<VReg> = (0..vf)
        .map(|lane| {
            let w = alloc(func, ctx.const_class);
            emit(
                func,
                vx,
                AArch64Opcode::NeonUmovGen,
                vec![vreg(w), vreg(vsum), imm(lane), imm(ctx.elem_code)],
            );
            w
        })
        .collect();
    // Balanced scalar fold of the extracted lanes, then ADD into `acc` (never
    // overwrite: preserves a non-zero initial `acc`; the scalar tail continues
    // from here). 4 lanes (i32) or 2 lanes (i64).
    let mut fold = lane_regs.clone();
    while fold.len() > 1 {
        let mut next = Vec::new();
        let mut i = 0;
        while i + 1 < fold.len() {
            let d = alloc(func, ctx.const_class);
            emit(
                func,
                vx,
                AArch64Opcode::AddRR,
                vec![vreg(d), vreg(fold[i]), vreg(fold[i + 1])],
            );
            next.push(d);
            i += 2;
        }
        if i < fold.len() {
            next.push(fold[i]);
        }
        fold = next;
    }
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(rec.acc), vreg(rec.acc), vreg(fold[0])],
    );
    emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);

    // --- COMMIT: splice the fresh blocks in front of the scalar loop (through
    // the precheck on the i64 path).
    let entry = pv.unwrap_or(vh);
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.guard, entry) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.guard);
    func.add_edge(rec.preheader, entry);
    func.add_edge(vx, rec.guard);

    true
}

/// Lower a term value to a `4 x i32` NEON value (in the vector body).
fn lower(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> Option<VReg> {
    if val == ctx.iv || val == ctx.acc {
        return None;
    }
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
    }
    // A recognized load leaf -> the vector loaded for this accumulator.
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
    // A loop-invariant i32 scalar leaf -> DUP-broadcast once in the preheader.
    if ctx.inv_leaves.contains(&val.id) {
        let v = inv_broadcast(func, ctx, val);
        ctx.memo.insert(val.id, v);
        return Some(v);
    }
    let &def_id = ctx.def.get(&val.id)?;
    if !ctx.loop_insts.contains(&def_id) {
        return None;
    }
    // A recognized select -> compare mask + branchless bitselect.
    if let Some(plan) = ctx.selects.get(&val.id).copied() {
        let result = lower_select(func, ctx, plan)?;
        ctx.memo.insert(val.id, result);
        return Some(result);
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

/// Recognize a select that is exactly a per-lane min/max of its two compare
/// operands (`(x REL y) ? x : y` or `? y : x`), so it can be emitted as ONE
/// faithfully-proven `SMAX/SMIN/UMAX/UMIN .4S` instead of the 4-op bitselect.
/// The compare must be an ordering (not `CMEQ`) and the two arms must be exactly
/// the two compare operands. Because the mask is `lhs > rhs` (strict) or
/// `lhs >= rhs`:
/// * arms `(if=lhs, else=rhs)` returns the larger ⇒ MAX;
/// * arms `(if=rhs, else=lhs)` returns the smaller ⇒ MIN.
///   `min`/`max` are commutative, so the operand order passed to the NEON op is
///   irrelevant. Signedness comes from the compare (`CMGT/CMGE` ⇒ signed).
fn try_minmax(plan: &SelectPlan) -> Option<AArch64Opcode> {
    use AArch64Opcode::*;
    let signed = match plan.cmp_op {
        NeonCmgtV | NeonCmgeV => true,
        NeonCmhiV | NeonCmhsV => false,
        _ => return None, // CMEQ (from ==/!=) is not an ordering
    };
    if plan.arm_if == plan.cmp_lhs && plan.arm_else == plan.cmp_rhs {
        Some(if signed { NeonSmaxV } else { NeonUmaxV })
    } else if plan.arm_if == plan.cmp_rhs && plan.arm_else == plan.cmp_lhs {
        Some(if signed { NeonSminV } else { NeonUminV })
    } else {
        None
    }
}

/// Recognize a select that computes per-lane absolute value, `(x < 0) ? -x : x`
/// (or the `>= 0` mirror `(x >= 0) ? x : -x`), so it lowers to the single proven
/// `ABS.4S` (`NeonAbsV`) — or, fail-closed, the negating `SUB` plus one proven
/// `SMAX` (`smax(x, 0-x) == |x|`) — replacing the 5-op compare + bitselect. Returns
/// the two term arms `(pos, neg)`; the abs is `abs(pos)` (`== smax(pos, neg)`),
/// where `pos` is lowered through [`lower`] (and `neg` too, only on the SUB+SMAX
/// fallback).
///
/// Soundness — `abs(pos) == smax(pos, neg)` equals the select ONLY when BOTH hold,
/// and both are verified structurally here (anything else falls through to the
/// bitselect):
///   (a) `neg == 0 - pos` — so `smax(pos, neg) == smax(pos, -pos) == max(pos, -pos)`
///       `== |pos|`;
///   (b) the compare is a signed sign-test that routes `neg` exactly when
///       `pos < 0` (equivalently `pos` when non-negative) — so the *select* also
///       equals `max(pos, -pos)`.
/// Matches clang's `ABS.4S` on every input including INT_MIN: `0 - INT_MIN`
/// wraps to INT_MIN, `abs(INT_MIN) == smax(INT_MIN, INT_MIN) == INT_MIN`, and the
/// select likewise picks `neg == INT_MIN` — all agree. The `pos == 0` boundary
/// yields 0 for every CMGT/CMGE routing (checked case-by-case), so we need not
/// distinguish them.
fn try_abs(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    plan: &SelectPlan,
) -> Option<(VReg, VReg)> {
    use AArch64Opcode::*;
    // (a) Is `cand` defined as `SubRR(0, base)` (a negation)?  Returns `base`.
    let neg_base = |cand: VReg| -> Option<VReg> {
        let inst = func.inst(*def.get(&cand.id)?);
        if inst.opcode != SubRR || inst.operands.len() != 3 {
            return None;
        }
        let lhs = vreg_of(&inst.operands[1])?;
        let rhs = vreg_of(&inst.operands[2])?;
        (const_value(func, def, lhs) == Some(0)).then_some(rhs)
    };
    // Identify (pos, neg) with neg = 0 - pos and pos the *other* arm.
    let (pos, neg) = if let Some(base) = neg_base(plan.arm_if) {
        (plan.arm_else == base).then_some((plan.arm_else, plan.arm_if))?
    } else {
        let base = neg_base(plan.arm_else)?;
        (plan.arm_if == base).then_some((plan.arm_if, plan.arm_else))?
    };
    // (b) compare must be a SIGNED sign-test against zero on `pos`.
    if !matches!(plan.cmp_op, NeonCmgtV | NeonCmgeV) {
        return None; // unsigned/equality compares are never abs
    }
    // mask all-ones (predicate true) selects `arm_if`. Determine whether the
    // predicate is "pos < 0" (0 REL pos) or "pos >= 0" (pos REL 0).
    let pred_is_neg = if const_value(func, def, plan.cmp_lhs) == Some(0) && plan.cmp_rhs == pos {
        true // 0 >(=) pos  ==  pos <(=) 0
    } else if const_value(func, def, plan.cmp_rhs) == Some(0) && plan.cmp_lhs == pos {
        false // pos >(=) 0
    } else {
        return None;
    };
    // Routing consistency: predicate-true must pick the correct arm.
    //   pred_is_neg  => pick neg  => arm_if is the neg arm
    //   !pred_is_neg => pick pos  => arm_if is the pos arm
    let arm_if_is_neg = plan.arm_if == neg;
    (if pred_is_neg {
        arm_if_is_neg
    } else {
        !arm_if_is_neg
    })
    .then_some((pos, neg))
}

/// Lower a decoded lane-wise select. Exact `|x|` becomes a single proven `ABS.4S`
/// (`NeonAbsV`, or fail-closed to `SUB` + `SMAX` = `smax(x, 0-x)`); an exact min/max
/// of the compare operands becomes a single proven `SMAX/SMIN/UMAX/UMIN`; otherwise
/// emit `mask = CMxx(lhs, rhs)`
/// followed by the branchless per-lane bitselect
/// `result = else ^ ((else ^ if) & mask)`, built only from faithfully-proven
/// per-lane NEON compare + `EOR`/`AND`.
fn lower_select(func: &mut MachFunction, ctx: &mut LowerCtx, plan: SelectPlan) -> Option<VReg> {
    // Fastest path: per-lane absolute value. With the PROVEN `NeonAbsV` (`ABS.4S`)
    // this is a SINGLE op `abs(pos)`; otherwise it fails-closed to the (also proven)
    // negating `SUB` (`0 - pos`) + one `SMAX` (`smax(pos, 0-pos)`). Both compute the
    // exact same `|x|`, including `abs(INT_MIN) == INT_MIN`. i32 ONLY: the `NeonAbsV`
    // proof (and its encoder) are `.4S`-only and `SMAX.2D` does not exist in the ISA,
    // so the i64 path SKIPS this and takes the general compare + bitselect below
    // (correct, just not single-op).
    if !ctx.is_i64
        && let Some((pos, neg)) = try_abs(func, &ctx.def, &plan)
    {
        let p = lower(func, ctx, pos)?;
        let d = alloc(func, RegClass::Fpr128);
        if ABS_NEON_ENABLED {
            emit(
                func,
                ctx.vbody,
                AArch64Opcode::NeonAbsV,
                vec![vreg(d), vreg(p), imm(ARR_S4)],
            );
        } else {
            let n = lower(func, ctx, neg)?;
            emit(
                func,
                ctx.vbody,
                AArch64Opcode::NeonSmaxV,
                vec![vreg(d), vreg(p), vreg(n), imm(ARR_S4)],
            );
        }
        return Some(d);
    }
    let lhs = lower(func, ctx, plan.cmp_lhs)?;
    let rhs = lower(func, ctx, plan.cmp_rhs)?;
    // Fast path: an exact min/max of the compare operands is a single op. i32
    // ONLY: baseline NEON has no `.2D` SMAX/SMIN/UMAX/UMIN (the encoder rejects
    // them fail-closed), so the i64 path falls through to the compare +
    // bitselect, which computes the same per-lane min/max in 4 proven `.2D`/
    // whole-register ops.
    if !ctx.is_i64
        && let Some(mm) = try_minmax(&plan)
    {
        let d = alloc(func, RegClass::Fpr128);
        emit(
            func,
            ctx.vbody,
            mm,
            vec![vreg(d), vreg(lhs), vreg(rhs), imm(ARR_S4)],
        );
        return Some(d);
    }
    // mask = cmp_op(lhs, rhs): per-lane all-ones iff the predicate holds.
    let mask = alloc(func, RegClass::Fpr128);
    emit(
        func,
        ctx.vbody,
        plan.cmp_op,
        vec![vreg(mask), vreg(lhs), vreg(rhs), imm(ctx.arr_code)],
    );
    // Masked-constant fast path: `select(cond, K, 0)` == `mask & K` (one proven
    // AND), when the ELSE arm is a constant zero. Sound for ANY K because the
    // per-lane mask is all-ones/all-zeros: `mask & K == K` where the predicate
    // holds and `== 0` otherwise — exactly the select. Replaces the 3-op bitselect
    // (which here degenerates to `eor(0,K); and; eor(0,·)` — two zero-eor no-ops).
    // Covers count-eq `(a==x)?1:0` and predicated masking `(a>t)?a:0`.
    if const_value(func, &ctx.def, plan.arm_else) == Some(0) {
        let a_if = lower(func, ctx, plan.arm_if)?;
        return Some(bin(func, ctx, AArch64Opcode::NeonAndV, mask, a_if, false));
    }
    let a_if = lower(func, ctx, plan.arm_if)?;
    let a_else = lower(func, ctx, plan.arm_else)?;
    // result = a_else ^ ((a_else ^ a_if) & mask).
    let x1 = bin(func, ctx, AArch64Opcode::NeonEorV, a_else, a_if, false);
    let x2 = bin(func, ctx, AArch64Opcode::NeonAndV, x1, mask, false);
    let result = bin(func, ctx, AArch64Opcode::NeonEorV, a_else, x2, false);
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
        operands.push(imm(ctx.arr_code));
    }
    emit(func, ctx.vbody, op, operands);
    d
}

/// Materialize (once) a broadcast `4 x i32` constant vector in the preheader.
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

/// DUP-broadcast (once) a loop-invariant scalar register to every lane, in the
/// preheader (the value dominates the preheader, so it is available).
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
    !matches!(op, CmpRR | CmpRI | BCond | B)
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
