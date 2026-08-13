// trust-cg-opt - SOUND NEON min/max & bitwise array-reduction vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON min/max & bitwise array-reduction vectorizer (`neon-minmax`)
//!
//! Sibling of [`crate::neon_array`] for the **associative, commutative
//! non-add** integer array reductions
//!
//! ```text
//! m = M0;  for i in 0..n (signed i < n):  m = REDUCE(m, TERM(a[i], b[i], ...))
//! ```
//!
//! where `REDUCE` is one of **signed/unsigned min/max** (expressed in the IR as
//! `select(icmp <pred>, ...)`) or **bitwise AND / OR / XOR**, `m` is a **scalar**
//! `i32` accumulator (register / return value — never memory), the pointers are
//! **only loaded** in the loop, and `TERM` is a lane-wise `i32` function of the
//! loaded elements and 16-bit constants (`+ - * & | ^ << >>`). Each loaded array
//! is walked with paired `LDP Qt1, Qt2` post-index loads; the per-lane term is
//! combined into `UNROLL = 4`
//! independent `4 x i32` vector accumulators — each **seeded with the reduction
//! identity** — using the matching NEON per-lane op (`SMAX/SMIN/UMAX/UMIN` or
//! `AND/ORR/EOR .4S`); at loop exit the accumulators are combined with the SAME
//! op, horizontally reduced, folded into the scalar accumulator, and the ORIGINAL
//! scalar loop handles the `< 16` tail iterations.
//!
//! It runs immediately **after** [`crate::neon_array`] (which claims the ADD /
//! MADD reductions and BAILS on min/max/bitwise) and before
//! [`crate::reduction_split`]. It fires only on the shapes it can prove
//! lane-wise-equivalent and BAILS (leaving the loop untouched) on everything
//! else. Disable with `TRUST_CG_DISABLE_PASSES=neon_minmax`.
//!
//! ## AFFINE IOTA terms (the induction variable in the term)
//!
//! The plain-reduction term language admits the bare induction variable as an
//! **affine iota leaf**: `r ^= (i+1) ^ a[i]` (the Shootout `puzzle` kernel),
//! `r |= (i*3) & a[i]`, etc. Reusing the argmin index machinery, the iv lowers
//! to a per-accumulator POSITION VECTOR `pos_k = splat(iv0) + [0..vf) + vf*k`
//! advanced by `splat(width)` per iteration — lane `l` of `pos_k` holds, at
//! every iteration, EXACTLY the scalar iv value for the element accumulator
//! `k` folds into lane `l` (all adds wrap mod 2^lane-width identically to the
//! scalar iv arithmetic). So per lane `vector_term == scalar_term` exactly,
//! and the comm+assoc reduction over the lanes equals the scalar left-fold —
//! the established argument, unchanged. Deliberately scoped to AFFINE iv
//! terms: a product of two iv-carrying factors (`i*i`) or a right-shift of an
//! iv-carrying value BAILS (`Recognized::subtree_uses_iv`); the argmin
//! probe still forbids iv in its VALUE term (the index is tracked
//! separately). A term with no iv use emits no iota — byte-identical output.
//! `iv ± K` is further STRENGTH-REDUCED to its own loop-carried position
//! vector seeded `base ± K` (the per-iteration `pos + splat(K)` add folds
//! into the seed — clang's index-vector shape; see `shift_of_iv`).
//!
//! ## argmin / argmax (index-tracking)
//!
//! A second, index-tracking mode (`ArgRecognized`, `apply_arg`) vectorizes
//! **argmin / argmax** loops with THREE loop-carried values (iv + best-value +
//! best-index) whose value and index both update under a SINGLE **strict**
//! min/max compare:
//!
//! ```text
//! bv = M0; bi = I0;
//! for i in 0..n:  let v = TERM(a[i]);  if v <strict> bv { bv = v; bi = i; }
//! ```
//!
//! LLVM's cost model refuses this class (measured ~2x-slower verdict, remarks
//! captured) yet native measurement shows a large NEON win. Per accumulator the
//! vector body carries a value vector (identity-seeded) and a parallel INDEX
//! vector (seeded with each lane's FIRST position `iv0 + 4k + [0,1,2,3]`,
//! incremented by 16/iter); both are updated by the SAME per-lane compare mask
//! (`CMGT`/`CMHI` `.4S`, `ReduceOp::d2_pick_cand_cmp`) via the proven tied-`BIT`
//! bitselect (`vidx = mask ? pos : vidx`).
//!
//! **Tie-breaking is the soundness crux.** With a STRICT compare the scalar loop
//! is a left-fold of the **(value, min-index) lexicographic monoid** over
//! strictly-increasing positions: on a value tie the update does NOT fire, so the
//! EARLIER index survives (first occurrence). That monoid is associative AND
//! commutative — combine((v1,i1),(v2,i2)) keeps the better value, ties to
//! `min(i1,i2)` — so splitting it across 16 lanes and re-combining reproduces the
//! exact first-occurrence result PROVIDED ties break on the INDEX VALUE, not lane
//! order. The exit therefore extracts all 16 `(value, index)` lane pairs and,
//! together with the pre-loop `(M0, I0)`, folds them with a scalar lexicographic
//! reduce (better value wins; equal value ⇒ smaller index wins), seeding the
//! untouched scalar tail. Seeding each index lane with its FIRST position makes
//! the identity-collision case (a lane whose min value equals the reduction
//! identity, so BIT never fires) still report the correct first position.
//! NON-STRICT selects (`<=`) implement LAST-occurrence — a different monoid — and
//! BAIL (`cc_true_on_equal`).
//!
//! **The tie-break argument is WIDTH-INDEPENDENT.** Nothing in it mentions the
//! lane width: the scalar loop is the same left-fold of the (value, min-index)
//! lexicographic monoid whether the values are i32 or i64, the monoid is
//! associative+commutative on ANY totally-ordered value domain, and the exit
//! fold breaks ties on the INDEX VALUE — never on lane position or lane count.
//! So the i64 (`.2D`, `WIDTH = UNROLL*2 = 8` lanes) mirror needs NO new
//! soundness argument: only the mechanics change — the per-lane strict compare
//! is `CMGT.2D`/`CMHI.2D` (the width-parameterized proven compares the `.2D`
//! value reduce already uses), both selects are the same lane-width-agnostic
//! tied-`BIT`, the index iota/`DUP`/`UMOV` move to D-element codes, and the
//! bounds guard is the i64 precheck + unsigned form (see the i64 section
//! below). Ties on `INT64_MIN`/`UINT64_MAX` duplicates fold to the smallest
//! index exactly as on i32.
//!
//! ## Why this is SOUND
//!
//! Like [`crate::neon_array`], the transform is **purely additive**: it inserts a
//! vector main loop in front of the scalar loop and never edits the scalar loop's
//! instructions. The scalar loop is therefore correct by construction; only the
//! inserted vector loop plus the horizontal fold need justifying.
//!
//! * **Loads are read-only ⇒ vectorizing them cannot change memory.** The pass
//!   BAILS on any store / call / atomic / unmodeled effect (whitelist). The
//!   reduction target is a **register**, so aliasing among the read pointers is
//!   irrelevant.
//! * **The vector loads read exactly the memory the scalar loop reads.** The
//!   `i64` sign-extension bounds guard (`sxtw(iv) + (width-1) < sxtw(n)`,
//!   `width = 16`) admits a vector iteration only when the full 16-lane block
//!   `iv..iv+15` is `< n` — identical to [`crate::neon_array`].
//! * **`SMAX/SMIN/UMAX/UMIN` and `AND/OR/XOR` are associative AND commutative on
//!   the whole `i32` domain** (unlike add they do not even wrap), so splitting
//!   the reduction across `UNROLL` accumulators and combining them is EXACT —
//!   each accumulator lane holds `REDUCE` over a disjoint subset of the processed
//!   elements, identical to the scalar left-fold regardless of grouping.
//! * **Identity seeding is what makes a partial accumulator neutral.** Each
//!   accumulator lane is initialised to the reduction identity — `SMAX: INT_MIN`,
//!   `SMIN: INT_MAX`, `UMAX: 0`, `UMIN: UINT_MAX`, `AND: all-ones`, `OR/XOR: 0` —
//!   so a lane that (in the guarded full-block regime it never is) saw no element
//!   contributes nothing. The scalar accumulator's pre-loop value `M0` is **folded
//!   in** at the exit (never overwritten before it is consumed), so
//!   `REDUCE(M0, <vector partial>)` seeds the scalar tail: when 0 vector
//!   iterations run, the fold is `REDUCE(M0, identity, …) = M0` and the untouched
//!   scalar loop does everything. QED.
//!
//! ## The `select(icmp)` → min/max decode
//!
//! Instruction selection lowers `m = (a[i] `cmp` m) ? a[i] : m` to a four-inst
//! chain `CmpRR(x,y); CSet(bool, cc_real); CmpRI(bool,0); Csel(dst,T,F,NE)` (it
//! materialises the `i1` and re-tests it). `decode_relation` collapses the
//! chain back to `dst = (x cc_real y) ? T : F` and proves it computes exactly one
//! of `SMAX/SMIN/UMAX/UMIN` over `{cand, acc}` — from the comparison signedness
//! and the direction of the picked operand — or BAILS. The direct
//! `CmpRR; Csel(cc)` shape is handled too. Any ambiguous cc / operand pairing
//! fails closed.
//!
//! ## i64 (`.2D`) support
//!
//! `i64` reductions (`Gpr64` iv/acc/bound, `a[i] = *(base + iv*8)` loads)
//! vectorize on the `.2D` path (`2 x i64` lanes, `WIDTH = UNROLL*2 = 8`):
//! * **min/max**: baseline NEON has NO `.2D` `SMAX/SMIN/UMAX/UMIN` (the encoder
//!   rejects them fail-closed), so the per-lane reduce is the 4-op branchless
//!   compare + bitselect `acc = acc ^ ((acc ^ cand) & mask)` with
//!   `mask = CMGT.2D`/`CMHI.2D` oriented so all-ones picks `cand` — each op
//!   faithfully proven (`*_lanewise_2d` obligations; `EOR`/`AND` are
//!   lane-width-agnostic whole-register logic). With per-lane
//!   `mask ∈ {all-ones, all-zeros}` this is exactly `REDUCE(acc, cand)`; on the
//!   equal boundary the mask is 0 and `acc` is kept — `min/max(a,a) = a` either
//!   way. MEASURED (2e7 i64, DRAM-resident): the 2-ops/element chain beats the
//!   1-cmp+1-csel/element scalar loop ~3.9x and TIES clang's cmgt+bsl shape
//!   (both bandwidth-bound) — so it is WIRED, not bailed.
//! * **bitwise AND/OR/XOR**: the whole-register `.16B` ops are lane-width
//!   agnostic — identical codegen, i64 lanes just fold 2-at-a-time.
//! * **product (`Mul`)**: BAILS — `.2D` has no integer multiply (`MUL.2D` is
//!   UNALLOCATED; nothing sound to emit, scalar keeps it correct).
//! * The horizontal fold extracts the 2 `i64` lanes (`UMOV.D`) and folds with
//!   the scalar `CMP`+`CSEL` / bitwise op, seeding `REDUCE(M0, …)` as on i32.
//! * The bounds guard is [`crate::neon_array`]'s i64 unsigned-subtraction guard
//!   behind a signed `n < WIDTH` precheck (no sign-extension headroom on i64);
//!   see `neon_array::apply_i64` for the wrap-freedom argument.

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
/// Number of independent vector accumulators (ILP).
const UNROLL: usize = 4;
/// Whether the i64 (`.2D`) min/max reduce uses the single PROVEN `NeonBitV`
/// (`BIT.16B`, tied destination — clang's exact `cmgt+bit` shape) instead of
/// the 3-op `EOR/AND/EOR` bitselect after the compare. Gated on the FAITHFUL
/// `NeonBitV` proof (neon_lowering_proofs::proof_neon_bitv_lanewise_16b: the
/// BSL/BIT/BIF wiring confusions all REFUTE) and the coverage gate staying
/// green. Both forms compute the exact same per-lane select; if that proof
/// were ever retracted, flip this to `false` to fail-closed to the (kept,
/// proven, slower) EOR/AND/EOR chain — never emit unproven codegen.
const MINMAX_BIT_ENABLED: bool = true;

// AArch64 condition codes (imm operands of BCond/CSet/Csel).
const CC_EQ: i64 = 0;
const CC_NE: i64 = 1;
const CC_HS: i64 = 2;
const CC_LO: i64 = 3;
const CC_HI: i64 = 8;
const CC_LS: i64 = 9;
const CC_GE: i64 = 10;
const CC_LT: i64 = 11;
const CC_GT: i64 = 12;
const CC_LE: i64 = 13;

// ---------------------------------------------------------------------------
// Reduction operator
// ---------------------------------------------------------------------------

/// The associative+commutative reduction operator this pass vectorizes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReduceOp {
    Smax,
    Smin,
    Umax,
    Umin,
    And,
    Or,
    Xor,
    /// Product reduction `p *= a[i]` — integer multiply is associative and
    /// commutative (mod 2^32). Per-lane `MUL.4S` (already faithfully proven,
    /// `NeonMulV`), identity `1`, horizontal fold via scalar `MulRR`.
    Mul,
}

/// The per-lane reduction identity (`4 x i32` broadcast).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Identity {
    /// All lanes `0` (UMAX, OR, XOR).
    Zero,
    /// All lanes `0xFFFF_FFFF` (UMIN, AND).
    AllOnes,
    /// All lanes `0x8000_0000` = `INT_MIN` (SMAX).
    IntMin,
    /// All lanes `0x7FFF_FFFF` = `INT_MAX` (SMIN).
    IntMax,
    /// All lanes `0x0000_0001` = `1` (MUL — the multiplicative identity).
    One,
}

impl ReduceOp {
    /// The NEON per-lane vector opcode used to accumulate and to combine.
    fn vec_op(self) -> AArch64Opcode {
        use AArch64Opcode::*;
        match self {
            ReduceOp::Smax => NeonSmaxV,
            ReduceOp::Smin => NeonSminV,
            ReduceOp::Umax => NeonUmaxV,
            ReduceOp::Umin => NeonUminV,
            ReduceOp::And => NeonAndV,
            ReduceOp::Or => NeonOrrV,
            ReduceOp::Xor => NeonEorV,
            ReduceOp::Mul => NeonMulV,
        }
    }

    /// Whether [`Self::vec_op`] carries an arrangement immediate (`.4S`
    /// arithmetic min/max/mul) or none (bitwise logic, `.16B`, Q from class).
    fn vec_op_has_arr(self) -> bool {
        matches!(
            self,
            ReduceOp::Smax | ReduceOp::Smin | ReduceOp::Umax | ReduceOp::Umin | ReduceOp::Mul
        )
    }

    fn identity(self) -> Identity {
        match self {
            ReduceOp::Smax => Identity::IntMin,
            ReduceOp::Smin => Identity::IntMax,
            ReduceOp::Umax => Identity::Zero,
            ReduceOp::Umin => Identity::AllOnes,
            ReduceOp::And => Identity::AllOnes,
            ReduceOp::Or => Identity::Zero,
            ReduceOp::Xor => Identity::Zero,
            ReduceOp::Mul => Identity::One,
        }
    }

    fn is_minmax(self) -> bool {
        matches!(
            self,
            ReduceOp::Smax | ReduceOp::Smin | ReduceOp::Umax | ReduceOp::Umin
        )
    }

    /// For a min/max op on the `.2D` path: the NEON compare opcode and whether
    /// the CAND operand goes on the compare's LEFT, such that the mask is
    /// all-ones exactly when the reduce picks `cand` over `acc`:
    ///   Smax: `CMGT(cand, acc)`   Smin: `CMGT(acc, cand)`
    ///   Umax: `CMHI(cand, acc)`   Umin: `CMHI(acc, cand)`
    /// (On the equal boundary the mask is 0 and `acc` is kept — the same value.)
    fn d2_pick_cand_cmp(self) -> (AArch64Opcode, bool) {
        match self {
            ReduceOp::Smax => (AArch64Opcode::NeonCmgtV, true),
            ReduceOp::Smin => (AArch64Opcode::NeonCmgtV, false),
            ReduceOp::Umax => (AArch64Opcode::NeonCmhiV, true),
            ReduceOp::Umin => (AArch64Opcode::NeonCmhiV, false),
            _ => (AArch64Opcode::NeonCmgtV, true), // unused for bitwise/mul
        }
    }

    /// For a min/max op: the condition code for the scalar `CMP; CSEL` fold
    /// `acc = REDUCE(acc, w)` (pick `w` over `acc` when this cc holds on
    /// `w - acc`). Undefined for bitwise ops.
    fn fold_cc(self) -> i64 {
        match self {
            ReduceOp::Smax => CC_GT,
            ReduceOp::Smin => CC_LT,
            ReduceOp::Umax => CC_HI,
            ReduceOp::Umin => CC_LO,
            _ => CC_AL_UNUSED,
        }
    }

    /// For a bitwise op: the scalar GPR opcode used for the horizontal fold.
    fn scalar_fold_op(self) -> AArch64Opcode {
        use AArch64Opcode::*;
        match self {
            ReduceOp::And => AndRR,
            ReduceOp::Or => OrrRR,
            ReduceOp::Xor => EorRR,
            ReduceOp::Mul => MulRR,
            _ => AndRR, // unused for min/max
        }
    }
}

/// Placeholder cc for the never-taken bitwise branch of [`ReduceOp::fold_cc`].
const CC_AL_UNUSED: i64 = 14;

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// A recognized vectorization plan: a 2-carried min/max/bitwise reduction, or a
/// 3-carried index-tracking argmin/argmax.
enum Plan {
    Reduce(Recognized),
    Arg(ArgRecognized),
    /// A forward bounds-guarded chain of K branch-diamond min/max reductions.
    Chain(ChainRecognized),
}

/// The `neon-minmax` machine pass.
#[derive(Default)]
pub struct NeonMinMaxPass {
    fired: usize,
}

impl NeonMinMaxPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonMinMaxPass {
    fn name(&self) -> &str {
        "neon-minmax"
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

impl NeonMinMaxPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;

        // Recognize read-only first; applying a plan only *adds* blocks (never
        // renumbers existing ids or edits other loops), so recognized data for
        // other loops stays valid. Try the index-tracking argmin/argmax shape
        // (3 carried vars) first; it and the 2-carried min/max reductions are
        // mutually exclusive on the writeback count, so ordering is only a
        // micro-optimization.
        // Escape hatch (differential testing): disable ONLY the forward-chain
        // branch-diamond path, leaving the proven 2-block reduction / argmin
        // paths intact, so the scalar output can be compared against the
        // vectorized one.
        let chain_off = std::env::var_os("TCG_NO_CHAIN_MINMAX").is_some();
        let mut plans = Vec::new();
        for lp in loops.all_loops() {
            if let Some(arg) = ArgRecognized::recognize(func, dom, lp.header, lp.latch, &lp.body) {
                plans.push(Plan::Arg(arg));
            } else if let Some(rec) =
                Recognized::recognize(func, dom, lp.header, lp.latch, &lp.body)
            {
                plans.push(Plan::Reduce(rec));
            } else if !chain_off
                && let Some(chain) =
                    ChainRecognized::recognize(func, dom, lp.header, lp.latch, &lp.body)
            {
                plans.push(Plan::Chain(chain));
            }
        }

        let mut changed = false;
        for plan in plans {
            let ok = match plan {
                Plan::Reduce(rec) => apply(func, &rec),
                Plan::Arg(arg) => apply_arg(func, &arg),
                Plan::Chain(chain) => apply_chain(func, &chain),
            };
            if ok {
                self.fired += 1;
                changed = true;
            }
        }
        if changed && std::env::var("TRUST_CG_DUMP_NEONMINMAX").is_ok() {
            eprintln!("[neon-minmax] fn={} vectorized={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// A fully validated, lane-wise-vectorizable min/max/bitwise array reduction.
struct Recognized {
    guard: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    iv: VReg,
    acc: VReg,
    bound: VReg,
    /// The reduction operator.
    op: ReduceOp,
    /// The per-iteration term value (the `cand` combined into `acc`).
    term: VReg,
    /// True when the reduction is `i64` (`Gpr64` iv/acc/bound), lowered on the
    /// `.2D` path (compare+bitselect min/max, precheck + unsigned guard).
    is_i64: bool,
    /// Whether the term walker may admit a bare use of the induction variable as
    /// an AFFINE IOTA LEAF (lowered to a per-lane position vector `iv + lane`).
    /// Set `true` only on the plain reduction path (`recognize`); the argmin
    /// probe leaves it `false` so an index-derived value term still BAILS —
    /// argmin already tracks the index separately and must not double-count it.
    allow_iv: bool,
    /// Set by [`Self::node_ok`] when the term actually references the iv (only
    /// possible when `allow_iv`). Drives whether [`apply`] emits the iota
    /// position machinery; a term with no iv use stays byte-identical to before.
    uses_iv: bool,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// Load-result vreg id -> loop-invariant base pointer.
    loads: HashMap<u32, VReg>,
    /// Distinct base pointers referenced by `term`'s loads (first-seen order).
    bases: Vec<VReg>,
}

/// Opcodes permitted anywhere in the loop body. Anything else ⇒ BAIL. Extends
/// [`crate::neon_array`]'s whitelist with `CSet`/`Csel` (the select lowering).
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

/// Only `CmpRR`/`CmpRI` write NZCV among the whitelisted opcodes. Used to trace
/// the flags feeding a `CSet`/`Csel`.
fn sets_flags(op: AArch64Opcode) -> bool {
    matches!(op, AArch64Opcode::CmpRR | AArch64Opcode::CmpRI)
}

/// The nearest flag-setting instruction preceding `target` in `block_insts`
/// (program order), i.e. the one whose NZCV a flag-reader at `target` consumes.
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

/// Signed/unsigned relational direction of a min/max-relevant condition code,
/// applied as `lhs DIR rhs`. `(true, ..)` = signed, `(false, ..)` = unsigned.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Dir {
    Gt,
    Ge,
    Lt,
    Le,
}

fn flip(d: Dir) -> Dir {
    match d {
        Dir::Gt => Dir::Lt,
        Dir::Ge => Dir::Le,
        Dir::Lt => Dir::Gt,
        Dir::Le => Dir::Ge,
    }
}

fn cc_relation(cc: i64) -> Option<(bool, Dir)> {
    match cc {
        CC_GT => Some((true, Dir::Gt)),
        CC_GE => Some((true, Dir::Ge)),
        CC_LT => Some((true, Dir::Lt)),
        CC_LE => Some((true, Dir::Le)),
        CC_HI => Some((false, Dir::Gt)),
        CC_HS => Some((false, Dir::Ge)),
        CC_LO => Some((false, Dir::Lt)),
        CC_LS => Some((false, Dir::Le)),
        _ => None, // EQ/NE/MI/PL/VS/VC/AL are not orderings → BAIL
    }
}

/// Prove that `dst = (x cc y) ? t : f` computes exactly one of
/// `SMAX/SMIN/UMAX/UMIN` over `{cand, acc}`, where `cand` is the non-`acc`
/// operand. Returns `(op, cand)` or `None` (ambiguous ⇒ fail closed).
fn decode_relation(
    x: VReg,
    y: VReg,
    cc: i64,
    t: VReg,
    f: VReg,
    acc: VReg,
) -> Option<(ReduceOp, VReg)> {
    // cand = the non-acc select operand; exactly one of {t,f} must be acc.
    let cand = if t == acc {
        f
    } else if f == acc {
        t
    } else {
        return None;
    };
    if cand == acc {
        return None;
    }
    // The compare operands must be exactly {cand, acc}.
    if !((x == cand && y == acc) || (x == acc && y == cand)) {
        return None;
    }
    // The select operands must be exactly {cand, acc} (already partly checked).
    if !((t == cand && f == acc) || (t == acc && f == cand)) {
        return None;
    }
    let (signed, dir) = cc_relation(cc)?;
    // Rewrite `x DIR y` as `p FINAL q` with p = sel_true (t), q = sel_false (f).
    let final_dir = if x == t {
        dir // (x,y) = (t,f) = (p,q)
    } else if x == f {
        flip(dir) // (x,y) = (f,t) = (q,p) ⇒ p FLIP(dir) q
    } else {
        return None;
    };
    // The select returns `p` when the relation holds. It is MAX iff it returns
    // the greater operand: `p FINAL q` is a "greater" relation (Gt/Ge).
    let is_max = matches!(final_dir, Dir::Gt | Dir::Ge);
    let op = match (signed, is_max) {
        (true, true) => ReduceOp::Smax,
        (true, false) => ReduceOp::Smin,
        (false, true) => ReduceOp::Umax,
        (false, false) => ReduceOp::Umin,
    };
    Some((op, cand))
}

/// Decode a `Csel`-rooted min/max reduction. Returns `(op, cand, chain)` where
/// `chain` is the set of instruction ids forming the reduction (so `acc` may be
/// read within them). Handles both the direct `CmpRR; Csel(cc)` shape and the
/// materialised `CmpRR; CSet(cc); CmpRI(_,0); Csel(NE|EQ)` shape.
fn decode_csel_reduction(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    csel_id: InstId,
    acc: VReg,
) -> Option<(ReduceOp, VReg, Vec<InstId>)> {
    let csel = func.inst(csel_id);
    if csel.operands.len() != 4 {
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
            let (op, cand) = decode_relation(x, y, cc_sel, t, f, acc)?;
            Some((op, cand, vec![csel_id, flag1_id]))
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
            // The CSet's flags come from the real comparison.
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
            let (op, cand) = decode_relation(x, y, cc_real, et, ef, acc)?;
            Some((op, cand, vec![csel_id, flag1_id, cset_id, cmp_id]))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// argmin / argmax recognition (index-tracking dual-select loops)
// ---------------------------------------------------------------------------

/// The effective decoded facts of a `Csel`: `dst = (x cc_real y) ? t : f`, plus
/// the flag-defining `CmpRR` id and the full instruction chain. Handles the
/// direct `CmpRR; Csel(cc)` shape and the materialised
/// `CmpRR; CSet(cc_real); CmpRI(bool,0); Csel(NE|EQ)` shape (the `EQ` variant is
/// normalised by swapping `t`/`f`, so `t` is ALWAYS the operand picked when the
/// underlying predicate `(x cc_real y)` holds).
struct CselFacts {
    /// Id of the `CmpRR` whose NZCV this select ultimately consumes.
    cmp_id: InstId,
    /// Compare operands.
    x: VReg,
    y: VReg,
    /// Effective condition on `(x, y)` under which `t` is selected.
    cc_real: i64,
    /// Selected when `(x cc_real y)`.
    t: VReg,
    /// Selected otherwise.
    f: VReg,
    /// All instruction ids forming this select's decode.
    chain: Vec<InstId>,
}

/// Decode a `Csel` to [`CselFacts`] (`dst = (x cc_real y) ? t : f`). Mirrors the
/// two shapes [`decode_csel_reduction`] handles, but keeps the comparison /
/// condition explicit (needed to prove two selects share one comparison).
fn resolve_csel(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    csel_id: InstId,
) -> Option<CselFacts> {
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
        // Direct: the Csel reads a real comparison's flags.
        AArch64Opcode::CmpRR => {
            let x = vreg_of(&flag1.operands[0])?;
            let y = vreg_of(&flag1.operands[1])?;
            Some(CselFacts {
                cmp_id: flag1_id,
                x,
                y,
                cc_real: cc_sel,
                t,
                f,
                chain: vec![csel_id, flag1_id],
            })
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
            let cset_block = block_of_inst(func, cset_id)?;
            let sinsts = func.block(cset_block).insts.clone();
            let cmp_id = nearest_flag_setter_before(func, &sinsts, cset_id)?;
            let cmp = func.inst(cmp_id);
            if cmp.opcode != AArch64Opcode::CmpRR {
                return None;
            }
            let x = vreg_of(&cmp.operands[0])?;
            let y = vreg_of(&cmp.operands[1])?;
            // `bool != 0` ⟺ `(x cc_real y)`; `Csel NE` picks `t` then, `Csel EQ`
            // picks `f` — normalise so `t` is picked exactly when the predicate
            // holds.
            let (nt, nf) = match cc_sel {
                CC_NE => (t, f),
                CC_EQ => (f, t),
                _ => return None,
            };
            Some(CselFacts {
                cmp_id,
                x,
                y,
                cc_real,
                t: nt,
                f: nf,
                chain: vec![csel_id, flag1_id, cset_id, cmp_id],
            })
        }
        _ => None,
    }
}

/// Whether `(x cc y)` is TRUE when `x == y` (a reflexive / non-strict cc).
/// Strict orderings (`GT/LT/HI/LO`) and `NE` are false on equality; the closed
/// orderings (`GE/LE/HS/LS`) and `EQ` are true. Used to reject NON-strict
/// argmin/argmax selects — those take the LAST occurrence, a different monoid
/// than the strict first-occurrence one this pass reproduces.
fn cc_true_on_equal(cc: i64) -> bool {
    matches!(cc, CC_GE | CC_LE | CC_HS | CC_LS | CC_EQ)
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

        // Register width selects the lowering path: `Gpr32` triple ⇒ `.4S`
        // (single-op min/max, sign-extension guard); `Gpr64` triple ⇒ `.2D`
        // (compare+bitselect min/max, precheck + unsigned guard). Mixed ⇒ BAIL.
        let is_i64 = match (iv.class, acc.class, bound.class) {
            (RegClass::Gpr32, RegClass::Gpr32, RegClass::Gpr32) => false,
            (RegClass::Gpr64, RegClass::Gpr64, RegClass::Gpr64) => true,
            _ => return None,
        };

        // (R4) reduction: `acc_src` is `<Bitwise>RR(acc, cand)` or a min/max
        // `Csel` chain. ADD/MADD are NOT ours (left to neon_array) ⇒ BAIL.
        let acc_def_id = *def.get(&acc_src.id)?;
        let acc_def = func.inst(acc_def_id);
        let (op, term, reduction_chain): (ReduceOp, VReg, Vec<InstId>) = match acc_def.opcode {
            AArch64Opcode::AndRR
            | AArch64Opcode::OrrRR
            | AArch64Opcode::EorRR
            | AArch64Opcode::MulRR => {
                let x = vreg_of(&acc_def.operands[1])?;
                let y = vreg_of(&acc_def.operands[2])?;
                let cand = if x == acc {
                    y
                } else if y == acc {
                    x
                } else {
                    return None;
                };
                let op = match acc_def.opcode {
                    AArch64Opcode::AndRR => ReduceOp::And,
                    AArch64Opcode::OrrRR => ReduceOp::Or,
                    AArch64Opcode::MulRR => ReduceOp::Mul,
                    _ => ReduceOp::Xor,
                };
                (op, cand, vec![acc_def_id])
            }
            AArch64Opcode::Csel => decode_csel_reduction(func, &def, acc_def_id, acc)?,
            _ => return None,
        };
        if term == acc || term == iv {
            return None;
        }
        // `.2D` has no integer multiply: an i64 PRODUCT reduction cannot be
        // vectorized soundly (MUL.2D is UNALLOCATED) — BAIL to scalar.
        if is_i64 && op == ReduceOp::Mul {
            return None;
        }

        // (R4b) `acc` may be read ONLY within the reduction chain instructions.
        let chain: HashSet<InstId> = reduction_chain.iter().copied().collect();
        for &id in loop_insts.iter() {
            if chain.contains(&id) {
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
            op,
            term,
            is_i64,
            allow_iv: true,
            uses_iv: false,
            def,
            loop_insts,
            loads: HashMap::new(),
            bases: Vec::new(),
        };

        // (R5) `term` must be lane-wise-lowerable: leaves are recognized `a[i]`
        // loads, 16-bit constants, or the AFFINE IOTA iv (never acc), joined by
        // allowed lane-wise ops. Populates `loads`/`bases`; sets `uses_iv`.
        let mut seen = HashSet::new();
        if !rec.node_ok(func, dom, rec.term, &mut seen) {
            return None;
        }
        // Require at least one load (a bare register reduction is not ours).
        if rec.bases.is_empty() {
            return None;
        }

        Some(rec)
    }

    /// Recognize an array load `dst = *(base + idx*elem)` at offset 0 and
    /// return its loop-invariant `base` (mirrors [`crate::neon_array`]):
    /// * i32 path: `dst` is `Gpr32`, `idx = Sxtw(iv)`, `elem = 4`.
    /// * i64 path: `dst` is `Gpr64`, `idx = iv` directly, `elem = 8`.
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

    fn node_ok(
        &mut self,
        func: &MachFunction,
        dom: &DomTree,
        val: VReg,
        seen: &mut HashSet<u32>,
    ) -> bool {
        // The accumulator is never a valid term value (the vector loop carries no
        // intermediate scalar acc — re-associating the reduction requires the
        // term be acc-free).
        if val == self.acc {
            return false;
        }
        // The induction variable: on the plain reduction path (`allow_iv`) admit
        // it as an AFFINE IOTA LEAF — [`lower`] materializes, per accumulator, the
        // exact per-lane scalar iv values `iv0 + width*t + vf*k + [0..vf)` as a
        // position vector, so any two's-complement arithmetic built ON it (the
        // whitelisted lane-wise ops) computes `scalar_term(iv=that lane)` exactly,
        // including every 32-bit wrap. The reduction is a comm+assoc monoid, so
        // splitting these exact per-iteration terms across lanes/accumulators and
        // recombining reproduces the scalar left-fold. The argmin probe leaves
        // `allow_iv=false` (it tracks the index separately) and still BAILS here.
        if val == self.iv {
            if !self.allow_iv {
                return false;
            }
            self.uses_iv = true;
            return true;
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
        // `.2D` has no integer multiply: any multiply in an i64 term BAILS.
        if self.is_i64 && matches!(opcode, MulRR | Madd) {
            return false;
        }
        match opcode {
            MulRR => {
                let (Some(a), Some(b)) = (vreg_of(&ops[1]), vreg_of(&ops[2])) else {
                    return false;
                };
                // AFFINE-only iv guard: a product of two iv-carrying factors is a
                // NON-AFFINE (quadratic `iv*iv`, `iv*(iv+1)`, …) iv term — BAIL.
                // The iota lanes would still compute it soundly per-lane, but the
                // extension is deliberately scoped to affine iv terms (`c*iv+d`);
                // `affine * iv-free` (`iv*3`, `iv*a[i]`) stays affine and fires.
                if self.subtree_uses_iv(func, a, 64) && self.subtree_uses_iv(func, b, 64) {
                    return false;
                }
                self.node_ok(func, dom, a, seen) && self.node_ok(func, dom, b, seen)
            }
            AddRR | SubRR | AndRR | OrrRR | EorRR => {
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
                // A RIGHT shift of an iv-carrying value is non-affine (`iv >> k`
                // is not linear) — BAIL to stay within the affine scope. A LEFT
                // shift `iv << k == iv * 2^k` is affine and fires.
                if matches!(opcode, LsrRI | AsrRI) && self.subtree_uses_iv(func, a, 64) {
                    return false;
                }
                // i64 uses the exact hardware ranges: left `[0, 63]`, right
                // `[1, 64)` (no 0-count right-shift encoding ⇒ BAIL).
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
                // `Madd(a,b,c) = a + b*c`; the product `b*c` with two iv-carrying
                // factors is non-affine — BAIL (mirrors the bare `MulRR` guard).
                if self.subtree_uses_iv(func, b, 64) && self.subtree_uses_iv(func, c, 64) {
                    return false;
                }
                self.node_ok(func, dom, a, seen)
                    && self.node_ok(func, dom, b, seen)
                    && self.node_ok(func, dom, c, seen)
            }
            _ => false,
        }
    }

    /// Whether the value tree rooted at `val` references the induction variable
    /// as an ARITHMETIC leaf (not merely as a load address — a load's result is
    /// an opaque per-lane value, iv-free for affine-scoping purposes). Bounded to
    /// `depth` hops; exhaustion returns `true` (conservative: forces the affine
    /// multiply/right-shift guards to BAIL rather than admit an unbounded tree).
    fn subtree_uses_iv(&self, func: &MachFunction, val: VReg, depth: u32) -> bool {
        if val == self.iv {
            return true;
        }
        if depth == 0 {
            return true;
        }
        let Some(&id) = self.def.get(&val.id) else {
            return false;
        };
        if !self.loop_insts.contains(&id) {
            return false; // loop-invariant / preheader value: iv-free
        }
        let inst = func.inst(id);
        // A recognized `a[i]` load result is treated as an opaque iv-free value
        // (its iv-dependence lives in the address, which is validated separately).
        if inst.opcode == AArch64Opcode::LdrRI {
            return false;
        }
        inst.operands
            .iter()
            .skip(1)
            .filter_map(vreg_of)
            .any(|op| self.subtree_uses_iv(func, op, depth - 1))
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
// argmin / argmax recognition
// ---------------------------------------------------------------------------

/// A fully validated, lane-wise-vectorizable **argmin / argmax** loop:
///
/// ```text
/// bv = M0; bi = I0;
/// for i in 0..n (signed i < n):
///     let v = TERM(a[i], ...);       // the compared "value"
///     if v <strict> bv { bv = v; bi = i; }   // dual select under ONE compare
/// ```
///
/// Two carried values update under a SINGLE strict min/max compare: `bv` takes
/// the better value, `bi` takes the current index. The strict `<`/`>` is the
/// soundness crux — it makes the scalar loop a left-fold of the **(value,
/// min-index) lexicographic monoid** over strictly-increasing positions (on a
/// value tie the earlier index is kept). That monoid is associative AND
/// commutative, so splitting it across lanes/accumulators and re-combining —
/// breaking value ties by the smaller INDEX VALUE (not lane order) — reproduces
/// the exact FIRST-occurrence result. Non-strict (`<=`) selects take the LAST
/// occurrence (a different monoid) and BAIL.
struct ArgRecognized {
    guard: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    iv: VReg,
    /// The value accumulator (`bv`) — its pre-loop value `M0` is folded in at
    /// exit, exactly like [`Recognized::acc`].
    best_val: VReg,
    /// The index accumulator (`bi`) — its pre-loop value `I0` is folded in too.
    best_idx: VReg,
    bound: VReg,
    /// The min/max operator (`Smin`/`Smax`/`Umin`/`Umax` only).
    op: ReduceOp,
    /// The per-iteration compared value (`v`, the select's `cand`).
    term: VReg,
    /// True when the loop carries `Gpr64` values (`.2D` path: CMGT/CMHI.2D +
    /// BIT, D-element iota/DUP/UMOV, i64 precheck + unsigned guard).
    is_i64: bool,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    loads: HashMap<u32, VReg>,
    bases: Vec<VReg>,
}

impl ArgRecognized {
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
        // Whitelist every opcode in the loop body (same set as the reductions).
        let mut loop_insts = HashSet::new();
        for &blk in [header, latch].iter() {
            for &id in &func.block(blk).insts {
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

        // Loop-carried writebacks: EXACTLY three (iv, best_val, best_idx). This
        // is what distinguishes argmin/argmax from the 2-carried min/max
        // reductions `Recognized` claims.
        let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
        for &id in latch_insts {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                writebacks.push((d, s));
            }
        }
        if writebacks.len() != 3 {
            return None;
        }
        let iv_src = writebacks.iter().find(|(d, _)| *d == iv).map(|(_, s)| *s)?;
        if !is_increment_by_one(func, &def, iv_src, iv) {
            return None;
        }
        let others: Vec<(VReg, VReg)> = writebacks
            .iter()
            .copied()
            .filter(|(d, _)| *d != iv)
            .collect();
        if others.len() != 2 {
            return None;
        }

        // Register width selects the lowering path (exactly like `Recognized`):
        // an all-`Gpr32` carried set ⇒ `.4S`; all-`Gpr64` ⇒ `.2D`. Mixed ⇒ BAIL.
        let is_i64 = match (iv.class, bound.class) {
            (RegClass::Gpr32, RegClass::Gpr32) => false,
            (RegClass::Gpr64, RegClass::Gpr64) => true,
            _ => return None,
        };
        let want_class = if is_i64 {
            RegClass::Gpr64
        } else {
            RegClass::Gpr32
        };
        if others.iter().any(|(d, _)| d.class != want_class) {
            return None;
        }

        // Try both role assignments of the two non-iv writebacks. Only the true
        // (best_val, best_idx) pairing validates: the index select picks `iv`
        // (never a load), so decoding it as a value reduction fails.
        for &(bv, bi) in &[(0usize, 1usize), (1, 0)] {
            let (best_val, best_val_src) = others[bv];
            let (best_idx, best_idx_src) = others[bi];
            if best_val == iv || best_idx == iv || best_val == best_idx {
                continue;
            }
            if let Some(rec) = try_build_arg(
                func,
                dom,
                guard,
                preheader,
                preheader_term,
                iv,
                bound,
                best_val,
                best_val_src,
                best_idx,
                best_idx_src,
                is_i64,
                &def,
                &loop_insts,
            ) {
                return Some(rec);
            }
        }
        None
    }
}

/// Validate one (best_val, best_idx) role assignment and, on success, build the
/// [`ArgRecognized`] plan. Decodes the value select as a min/max reduction and
/// proves the index select is the SAME strict compare selecting `iv`.
#[allow(clippy::too_many_arguments)]
fn try_build_arg(
    func: &MachFunction,
    dom: &DomTree,
    guard: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    iv: VReg,
    bound: VReg,
    best_val: VReg,
    best_val_src: VReg,
    best_idx: VReg,
    best_idx_src: VReg,
    is_i64: bool,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
) -> Option<ArgRecognized> {
    // --- Value select: `bv' = (v cmp bv) ? v : bv`, a min/max over {cand, bv}.
    let bv_def = *def.get(&best_val_src.id)?;
    if func.inst(bv_def).opcode != AArch64Opcode::Csel {
        return None;
    }
    let vf = resolve_csel(func, def, bv_def)?;
    let (op, cand) = decode_relation(vf.x, vf.y, vf.cc_real, vf.t, vf.f, best_val)?;
    if !op.is_minmax() {
        return None;
    }
    // STRICTNESS: the value must NOT update when `cand == best_val` (else the
    // paired index would take the LAST occurrence — a different monoid). The
    // update (pick `cand`) fires on the predicate `P = (x cc_real y)` iff
    // `vf.t == cand`, otherwise on `¬P`. `P` is true on equality iff the cc is
    // non-strict; require the update to be FALSE on equality.
    let cand_when_p = vf.t == cand;
    let p_on_equal = cc_true_on_equal(vf.cc_real);
    let update_on_equal = if cand_when_p { p_on_equal } else { !p_on_equal };
    if update_on_equal {
        return None;
    }

    // --- Index select: same compare (same CmpRR / predicate) picking {iv, bi}.
    let bi_def = *def.get(&best_idx_src.id)?;
    if func.inst(bi_def).opcode != AArch64Opcode::Csel {
        return None;
    }
    let idxf = resolve_csel(func, def, bi_def)?;
    if idxf.cmp_id != vf.cmp_id || idxf.x != vf.x || idxf.y != vf.y || idxf.cc_real != vf.cc_real {
        return None;
    }
    // The index select's operands are exactly {iv, best_idx}; `iv` is picked
    // when the predicate holds iff `idxf.t == iv`.
    let iv_when_p = if idxf.t == iv && idxf.f == best_idx {
        true
    } else if idxf.t == best_idx && idxf.f == iv {
        false
    } else {
        return None;
    };
    // The index must update EXACTLY when the value does (pick `iv` iff pick
    // `cand`) — same predicate polarity.
    if iv_when_p != cand_when_p {
        return None;
    }
    if cand == iv || cand == best_val || cand == best_idx {
        return None;
    }

    // The bound must be loop-invariant / available in the preheader.
    let bound_def = *def.get(&bound.id)?;
    let bound_block = block_of_inst(func, bound_def)?;
    if !dom.dominates(bound_block, preheader) {
        return None;
    }

    // (R4b) `best_val` may be read ONLY within the value select's chain, and
    // `best_idx` ONLY within the index select's chain. This confines both
    // accumulators to their selects — in particular it guarantees the value
    // term `cand` reads neither (the vector loop tracks no intermediate scalar
    // bv/bi), so re-associating the reduction is sound.
    let vchain: HashSet<InstId> = vf.chain.iter().copied().collect();
    let ichain: HashSet<InstId> = idxf.chain.iter().copied().collect();
    for &id in loop_insts.iter() {
        let inst = func.inst(id);
        for opd in inst.operands.iter().skip(1) {
            if vreg_of(opd) == Some(best_val) && !vchain.contains(&id) {
                return None;
            }
            if vreg_of(opd) == Some(best_idx) && !ichain.contains(&id) {
                return None;
            }
        }
    }

    // (R5) `cand` must be lane-wise-lowerable: recognized `a[i]` loads / 16-bit
    // constants joined by allowed lane-wise ops, never iv/bv/bi. Reuse the
    // PROVEN `Recognized` walker via a probe (acc = best_val); best_idx is
    // already excluded by R4b above. The probe carries the width, so the i64
    // path inherits the `.2D` restrictions (no multiply, i64 shift ranges,
    // `elem = 8` loads indexed by iv directly).
    let mut probe = Recognized {
        guard,
        preheader,
        preheader_term,
        iv,
        acc: best_val,
        bound,
        op,
        term: cand,
        is_i64,
        // argmin tracks the index SEPARATELY; a value term that reads iv would
        // double-count it, so the probe forbids the iota leaf and BAILS on any
        // iv use in `cand` (unchanged pre-existing behavior).
        allow_iv: false,
        uses_iv: false,
        def: def.clone(),
        loop_insts: loop_insts.clone(),
        loads: HashMap::new(),
        bases: Vec::new(),
    };
    let mut seen = HashSet::new();
    if !probe.node_ok(func, dom, cand, &mut seen) {
        return None;
    }
    if probe.bases.is_empty() {
        return None;
    }

    Some(ArgRecognized {
        guard,
        preheader,
        preheader_term,
        iv,
        best_val,
        best_idx,
        bound,
        op,
        term: cand,
        is_i64,
        def: probe.def,
        loop_insts: probe.loop_insts,
        loads: probe.loads,
        bases: probe.bases,
    })
}

// ---------------------------------------------------------------------------
// Forward bounds-guarded CHAIN min/max reduction (branch-diamond form)
// ---------------------------------------------------------------------------
//
// The bridge lowers a `for i in 0..N { if a[i] > mx { mx = a[i] } if a[i] < mn
// { mn = a[i] } }` scan NOT as a strict 2-block loop with `Csel`-materialized
// min/max (the [`Recognized`] shape), but as a MULTI-BLOCK LINEAR CHAIN whose
// per-array min/max update is a CONTROL-FLOW BRANCH DIAMOND
// (`cmp a[i], acc; b.<rel> then; b else` with the then-block RELOADING `a[i]`)
// and whose loop-continue guard is a folded CONSTANT bound
// (`CmpRI(iv, Imm(N))`), spread over a chain of blocks whose per-access bounds
// checks the AArch64 bounds-check-elimination pass has already reduced to
// pass-throughs. It also carries K >= 1 INDEPENDENT reductions in one loop
// (`mx` and `mn` share the induction).
//
// This path mirrors `neon_map::recognize_forward_chain`'s SHAPE recognition but
// recognizes MIN/MAX from the branch diamond directly (reusing the proven
// [`decode_relation`] to fix the operator/orientation) and generalizes to K
// accumulators. It is intentionally SCOPED to the shape the beat-llvm probe
// emits and fails closed on anything else:
//   * i32 element / `.4S` ONLY (no `.2D` bitselect here); the induction may be
//     `Gpr64` (usize `i`) or `Gpr32` (mixed addressing).
//   * each reduction's per-iteration term is a DIRECT `a[iv]` load (no affine
//     iota / arithmetic term — those keep the scalar loop);
//   * min/max operators ONLY (`Smax`/`Smin`/`Umax`/`Umin`), decoded from a
//     DIRECT `CmpRR; BCond` diamond (no `CSet` materialization);
//   * the loop-continue bound is a compile-time CONSTANT `N in [1, i32::MAX]`.
//
// ## Why this is SOUND
//
// The transform is purely ADDITIVE (like all the neon passes): `apply_chain`
// splices a vector main loop in FRONT of the scalar loop header and NEVER edits
// the scalar chain, so the scalar tail `[V, N)` remains correct by
// construction. The only new obligation is that the vector loop touch only
// in-bounds memory and compute each reduction faithfully:
//   * IN-BOUNDS (additive-subset): the scalar loop reads `a[iv]` for `iv in
//     [0, N)` with its per-access bounds checks already ELIDED by
//     bounds-check-elim — i.e. it is a THEOREM that `a[iv]` is in bounds for
//     `iv in [0, N)`, so `N <= a.len()`. The vector loop admits a block only
//     while `iv + width-1 < N`, reading `a[iv .. iv+width) subseteq [0, N)` — a
//     SUBSET of the indices the scalar loop already reads (same base, same
//     induction) — hence also in bounds. Single-N agreement across the header
//     loop-continue and any surviving bounds guard is still required.
//   * FAITHFUL: each reduction is `acc = REDUCE(acc, a[iv])` with `REDUCE` an
//     associative+commutative min/max monoid; the recognizer proves the branch
//     diamond computes exactly `min/max(a[iv], acc)` (the then-block's reloaded
//     value is the SAME `a[iv]` — no store exists in the loop body, guaranteed
//     by the opcode whitelist). Re-associating across lanes/accumulators and
//     horizontally reducing reproduces the scalar left-fold; the exit fold
//     seeds with the scalar accumulator's pre-loop value `M0` (still live —
//     the vector loop never wrote it).
// Fail-closed on ANY deviation.

/// The loop-continue / bounds-guard limit of a forward `while iv <u N` chain.
/// A constant `CmpRI(iv, Imm(N))` (the folded form the bridge emits, d10) or a
/// register `CmpRR(iv, N_reg)`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ChainBound {
    Const(i64),
    Reg(VReg),
}

/// Which side of a min/max branch diamond a value resolves to.
enum ChainSide {
    /// A value-preserving copy chain to the reduction accumulator.
    Acc,
    /// A recognized `a[iv]` load (the compared candidate).
    Cand,
}

/// One recognized min/max reduction inside a forward chain.
struct ChainReduction {
    op: ReduceOp,
    /// The loop-carried accumulator (its latch-writeback destination).
    acc: VReg,
    /// Loop-invariant base pointer of the candidate load (`a[iv]`); its lane-wise
    /// loaded value IS the per-iteration term.
    base: VReg,
}

/// The block set of one recognized min/max branch diamond (EXCLUDING the join,
/// which continues the chain walk).
struct DiamondInfo {
    compare: BlockId,
    join: BlockId,
    blocks: Vec<BlockId>,
}

/// A fully validated forward-chain, branch-diamond, K-reduction min/max loop.
struct ChainRecognized {
    /// The loop header (== the vectorizer's splice point / `guard`).
    guard: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    iv: VReg,
    bound: i64,
    reductions: Vec<ChainReduction>,
    /// Distinct candidate base pointers (first-seen order).
    bases: Vec<VReg>,
}

/// True iff `v` reaches `iv` through value-preserving copy links (mirrors
/// `neon_map::same_as_iv`). Matches `iv` EXACTLY and never strips PAST it, so it
/// never follows the latch `iv = iv+1` writeback and never mistakes a shifted
/// index for `iv`. Also reused with `target = acc` to test "is a copy of acc"
/// WITHOUT following the acc's own (loop-carried) latch writeback.
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
/// only on single-def limit registers, never on the multi-def induction/acc.
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
/// register (`CmpRR`). Mirrors `neon_map::recognize_chain_guard`, generalized to
/// the folded `CmpRI(iv, Imm(N))` form. Fail-closed on any other shape.
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
/// register-resolves-to-the-constant.
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
/// Returns `base`. Fail-closed otherwise.
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

/// Canonicalize a diamond value to the accumulator or the candidate load
/// (strips value-preserving copies, stopping at `acc`). Returns `None` on
/// anything else — a load from a DIFFERENT base BAILS (never conflated with the
/// candidate).
#[allow(clippy::too_many_arguments)]
fn chain_canon(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    v: VReg,
    acc: VReg,
    base: VReg,
    iv: VReg,
    preheader: BlockId,
) -> Option<ChainSide> {
    let mut cur = v;
    for _ in 0..16 {
        if same_as_iv(func, def, cur, acc) {
            return Some(ChainSide::Acc);
        }
        if let Some(b) = chain_load_base(func, def, dom, cur, iv, preheader) {
            return (b == base).then_some(ChainSide::Cand);
        }
        let &d = def.get(&cur.id)?;
        match copy_like(func.inst(d)) {
            Some((dst, src)) if dst == cur => cur = src,
            _ => return None,
        }
    }
    None
}

/// Walk BACKWARD from a diamond tail (a block that assigns the result) up a
/// single-pred pass-through chain to the 2-successor SPLIT (compare) block.
/// Returns `(split, entry, path)` where `entry` is the split's successor that
/// begins this side and `path` is every block from `entry` down to `tail`.
fn walk_back_to_split(
    func: &MachFunction,
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
            2 => return Some((p, cur, path)),
            1 => {
                path.push(p);
                cur = p;
            }
            _ => return None,
        }
    }
    None
}

impl ChainRecognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // A strict 2-block loop is handled by the existing shapes; the chain has
        // header + latch + at least one middle block.
        if header == latch || body.len() < 3 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // Whitelist every opcode across EVERY body block (no store/call/div/etc).
        // The absence of `StrRI` here is what makes every `a[iv]` load LOOP-STABLE
        // (the diamond's compare candidate equals its then-block reload).
        let mut loop_insts = HashSet::new();
        for &b in body {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

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
        // (the mixed i64-index / i32-element shape the bridge emits, d10). A
        // `Gpr32` induction is not vectorized by this path (fail-closed).
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

        // Recognize each reduction's branch diamond (i32 `.4S`, min/max only).
        let mut reductions: Vec<ChainReduction> = Vec::new();
        let mut bases: Vec<VReg> = Vec::new();
        let mut diamond_map: HashMap<BlockId, DiamondInfo> = HashMap::new();
        for (acc, result) in &result_wbs {
            let (acc, result) = (*acc, *result);
            if acc.class != RegClass::Gpr32 || acc == iv {
                return None;
            }
            // acc distinct across reductions.
            if reductions.iter().any(|r| r.acc == acc) {
                return None;
            }
            // The accumulator has EXACTLY ONE def inside the loop body (the latch
            // writeback) — any other in-loop write would break the monoid model.
            if count_loop_defs(func, &loop_insts, acc) != 1 {
                return None;
            }
            let (red, dinfo) =
                recognize_minmax_diamond(func, dom, &def, &loop_insts, iv, acc, result, preheader)?;
            if !bases.iter().any(|b| b.id == red.base.id) {
                bases.push(red.base);
            }
            if diamond_map.insert(dinfo.compare, dinfo).is_some() {
                return None; // two reductions sharing one compare block => BAIL
            }
            reductions.push(red);
        }

        // Walk the chain header -> ... -> latch, classifying every block as the
        // loop-continue / bounds guard, a min/max diamond, or a pass-through, and
        // proving SINGLE-N agreement + full coverage.
        let bound = Self::walk_chain(func, &def, body, header, latch, iv, &diamond_map)?;
        let ChainBound::Const(n) = bound else {
            return None; // only compile-time constant bounds (d10's folded form)
        };
        if !(1..=i32::MAX as i64).contains(&n) {
            return None;
        }

        Some(ChainRecognized {
            guard: header,
            preheader,
            preheader_term,
            iv,
            bound: n,
            reductions,
            bases,
        })
    }

    /// Classify the chain and return its single loop bound. Fail-closed on any
    /// block off the header->latch structure or a limit disagreement.
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
                // Min/max branch diamond (must be a recognized reduction's).
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

/// Build a def map (`vreg id -> defining InstId`) considering ONLY instructions
/// that are LIVE (reachable through `block_order`). The shared [`build_def_map`]
/// iterates the flat instruction storage, which can still contain DEAD
/// instructions that earlier passes (if-convert / bounds-check-elim) unhooked
/// from their blocks but left in `func.insts`; a dead duplicate def would
/// shadow the live one and break the copy/address walks. This restricts to the
/// current CFG. When a vreg has multiple LIVE defs (loop-carried phis: `iv`,
/// each `acc`) the last in block/program order wins, which the chain walkers
/// tolerate because they check `== iv`/`== acc` BEFORE following a def.
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

/// Count the number of definitions of `v` inside `loop_insts`.
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

/// Recognize ONE min/max reduction from its branch diamond. `result` is the
/// per-iteration min/max value written back to `acc` in the latch; it MUST have
/// exactly two in-loop `MovR` defs (the then/else tails). Proves the diamond
/// computes `acc = min/max(a[iv], acc)` and returns the reduction + its block
/// set. Fail-closed on any deviation.
#[allow(clippy::too_many_arguments)]
fn recognize_minmax_diamond(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    acc: VReg,
    result: VReg,
    preheader: BlockId,
) -> Option<(ChainReduction, DiamondInfo)> {
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

    // One tail assigns `acc` (else), the other a candidate `a[iv]` load (then).
    let acc_side = |src: VReg| same_as_iv(func, def, src, acc);
    let (acc_tail, cand_tail) = if acc_side(tails[0].1) && !acc_side(tails[1].1) {
        (tails[0], tails[1])
    } else if acc_side(tails[1].1) && !acc_side(tails[0].1) {
        (tails[1], tails[0])
    } else {
        return None;
    };
    let base = chain_load_base(func, def, dom, cand_tail.1, iv, preheader)?;

    // Both tails trace back through pass-throughs to the SAME split (compare).
    let (c_cand, entry_cand, path_cand) = walk_back_to_split(func, cand_tail.0)?;
    let (c_acc, entry_acc, path_acc) = walk_back_to_split(func, acc_tail.0)?;
    if c_cand != c_acc {
        return None;
    }
    let compare = c_cand;

    // Both tails converge at ONE join block.
    let cand_join = &func.block(cand_tail.0).succs;
    let acc_join = &func.block(acc_tail.0).succs;
    if cand_join.len() != 1 || acc_join.len() != 1 || cand_join[0] != acc_join[0] {
        return None;
    }
    let join = cand_join[0];

    // Decode the split: `cmp cx, cy; b.<cc> t_target; b f_target`.
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
    // The two edges must be exactly the two diamond entries.
    if !((t_target == entry_cand && f_target == entry_acc)
        || (t_target == entry_acc && f_target == entry_cand))
    {
        return None;
    }
    // Only the DIRECT `CmpRR; BCond` form (no CSet materialization).
    let cmp_id = nearest_flag_setter_before(func, c_insts, bcond_id)?;
    let cmp = func.inst(cmp_id);
    if cmp.opcode != AArch64Opcode::CmpRR {
        return None;
    }
    let cx = vreg_of(&cmp.operands[0])?;
    let cy = vreg_of(&cmp.operands[1])?;

    // The value written on the TAKEN edge vs the FALL-THROUGH edge.
    let (taken_src, fall_src) = if t_target == entry_cand {
        (cand_tail.1, acc_tail.1)
    } else {
        (acc_tail.1, cand_tail.1)
    };

    // Canonicalize every operand to {acc, cand} and reuse the proven
    // `decode_relation`: `result = (cx cc cy) ? taken_src : fall_src` is a
    // min/max over {a[iv], acc}.
    let cand_repr = cand_tail.1;
    let canon = |v: VReg| -> Option<VReg> {
        match chain_canon(func, def, dom, v, acc, base, iv, preheader)? {
            ChainSide::Acc => Some(acc),
            ChainSide::Cand => Some(cand_repr),
        }
    };
    let (op, decoded_cand) = decode_relation(
        canon(cx)?,
        canon(cy)?,
        cc,
        canon(taken_src)?,
        canon(fall_src)?,
        acc,
    )?;
    if !op.is_minmax() || decoded_cand != cand_repr {
        return None;
    }

    let mut blocks = vec![compare];
    blocks.extend(path_cand);
    blocks.extend(path_acc);
    Some((
        ChainReduction { op, acc, base },
        DiamondInfo {
            compare,
            join,
            blocks,
        },
    ))
}

/// Materialize a non-negative i32-range constant into a fresh preheader vreg of
/// `class` via the isel `Movz`(+`Movk`) convention (mirrors
/// `neon_array::materialize_const_bound`). Used for the compile-time vector
/// guard limit, which `apply_chain` cannot read from a register (the loop bound
/// is a folded immediate inside the loop).
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

/// Vectorize a [`ChainRecognized`] forward-chain min/max loop (i32 `.4S`, K
/// independent reductions). Purely ADDITIVE: splices a vector main loop between
/// the preheader and the header and never edits the scalar chain.
fn apply_chain(func: &mut MachFunction, rec: &ChainRecognized) -> bool {
    let vf = VF;
    let arr_code = ARR_S4;
    let elem_code = ELEM_S;
    let const_class = RegClass::Gpr32;
    let width = UNROLL as i64 * vf; // 16

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

    // --- Preheader: per-reduction UNROLL accumulators seeded with the reduction
    // identity.
    let vacc: Vec<Vec<VReg>> = rec
        .reductions
        .iter()
        .map(|red| {
            (0..UNROLL)
                .map(|_| emit_identity(func, pre, red.op.identity(), false))
                .collect()
        })
        .collect();

    // --- Guard bound. The scalar loop-continue is `iv <u N` (UNSIGNED `LO`), so
    // the vector guard must be UNSIGNED TOO — a signed compare would admit a
    // (hypothetical) high-bit-set `iv` the scalar loop skips, reading OOB. `N` is
    // a compile-time constant in `[1, i32::MAX]`, so the guard limit
    // `main = N - (width-1)` (the largest `iv` whose full `width`-block fits in
    // `[0, N)`) is computed at COMPILE time; when `N < width` no full block fits
    // and we use `0` so the unsigned guard `iv <u 0` NEVER passes (the scalar
    // loop does everything). `iv` is `Gpr64`, so the compare matches the scalar's
    // 64-bit `CmpRI(iv, N)` bit-for-bit.
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

    // --- Vector header: UNSIGNED guard `iv <u main_bound` (== `iv+width-1 <u N`),
    // matching the scalar's `iv <u N` loop-continue in the same (64-bit) width.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Vector body: paired post-index LDP per base, then per accumulator per
    // reduction `vacc = REDUCE(vacc, loaded)`.
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
    for k in 0..UNROLL {
        for (ri, red) in rec.reductions.iter().enumerate() {
            let Some(&vterm) = loaded.get(&(red.base.id, k)) else {
                return false;
            };
            let acc = vacc[ri]
                .get(k)
                .copied()
                .expect("one vector accumulator per unrolled lane");
            emit_vreduce(func, vb, red.op, false, arr_code, acc, [acc, vterm]);
        }
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

    // --- Vector exit: for each reduction combine its accumulators (balanced
    // tree), horizontally reduce, and fold into the scalar accumulator (still
    // holding its pre-loop value M0 — the vector loop never wrote it).
    for (ri, red) in rec.reductions.iter().enumerate() {
        let mut level = vacc[ri].clone();
        while level.len() > 1 {
            let mut next = Vec::new();
            let mut i = 0;
            while i + 1 < level.len() {
                let d = alloc(func, RegClass::Fpr128);
                emit_vreduce(
                    func,
                    vx,
                    red.op,
                    false,
                    arr_code,
                    d,
                    [level[i], level[i + 1]],
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
                let w = alloc(func, const_class);
                emit(
                    func,
                    vx,
                    AArch64Opcode::NeonUmovGen,
                    vec![vreg(w), vreg(vsum), imm(lane), imm(elem_code)],
                );
                w
            })
            .collect();
        fold_into_acc(func, vx, red.op, red.acc, &lane_regs, const_class);
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
    /// The scalar induction vreg. When the term uses it as an AFFINE IOTA leaf
    /// (`!posv.is_empty()`), [`lower`] returns `posv[accum]` for it — the
    /// per-lane position vector holding this accumulator's exact scalar iv
    /// values this iteration.
    iv: VReg,
    /// Per-accumulator running position vector `iv0 + width*t + vf*k + [0..vf)`
    /// (empty when the term has no iv use — the byte-identical legacy path).
    posv: Vec<VReg>,
    /// Per-accumulator IMMUTABLE first-position base (`iv0 + vf*k + [0..vf)`,
    /// preheader-computed) used to seed SHIFTED iotas.
    iota_bases: Vec<VReg>,
    /// SHIFTED-IOTA fold: `iv ± K` lowers to its own loop-carried position
    /// vector (seeded `base ± K` in the preheader, advanced by `width` per
    /// iteration) instead of a per-iteration `pos + splat(K)` add — clang's
    /// index-vector shape, one op cheaper per accumulator-iteration. Vectors
    /// created while lowering the CURRENT accumulator collect here; [`apply`]
    /// drains them and emits their advances after the accumulate.
    pending_advances: Vec<VReg>,
    /// Set when the BARE iv was lowered (via `posv`); [`apply`] advances
    /// `posv[k]` only then (a term using only `iv ± K` leaves posv unused).
    used_bare_iv: bool,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    loads: HashMap<u32, VReg>,
    loaded: HashMap<(u32, usize), VReg>,
    const_cache: HashMap<i64, VReg>,
    memo: HashMap<u32, VReg>,
}

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    // Per-width parameters (mirrors neon_predsum): i32 = `.4S` + sxtw guard;
    // i64 = `.2D` + precheck + unsigned guard.
    let (vf, elem_bytes, arr_code, elem_code, const_class) = if rec.is_i64 {
        (VF_I64, ELEM_BYTES_I64, ARR_D2, ELEM_D, RegClass::Gpr64)
    } else {
        (VF, ELEM_BYTES, ARR_S4, ELEM_S, RegClass::Gpr32)
    };
    let width = UNROLL as i64 * vf;

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

    if let Some(pv) = pv {
        func.add_edge(pv, vh);
        func.add_edge(pv, rec.guard);
    }
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: UNROLL accumulators, each seeded with the identity.
    let vacc: Vec<VReg> = (0..UNROLL)
        .map(|_| emit_identity(func, pre, rec.op.identity(), rec.is_i64))
        .collect();

    // --- Preheader: AFFINE IOTA position vectors (only when the term reads iv).
    // Reuses the argmin index machinery: `pos0 = splat(iv0) + [0..vf)`, and per
    // accumulator `k` a running `posv[k] = pos0 + vf*k` advanced by `splat(width)`
    // each iteration. Lane `l` of `posv[k]` therefore holds `iv0 + width*t + vf*k
    // + l` at iteration `t` — EXACTLY the scalar iv that the scalar loop would use
    // for the element accumulator `k` processes into lane `l`. Every add wraps
    // mod 2^(32|64) identically to scalar `iv` arithmetic. Empty otherwise (the
    // legacy path emits nothing new — byte-identical).
    let (posv, iota_bases, width_splat): (Vec<VReg>, Vec<VReg>, Option<VReg>) = if rec.uses_iv {
        let iota = build_iota(func, pre, vf, elem_code, const_class);
        let dup_iv = alloc(func, RegClass::Fpr128);
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonDupGen,
            vec![vreg(dup_iv), vreg(rec.iv), imm(elem_code)],
        );
        let pos0 = alloc(func, RegClass::Fpr128);
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonAddV,
            vec![vreg(pos0), vreg(dup_iv), vreg(iota), imm(arr_code)],
        );
        let mut posv = Vec::with_capacity(UNROLL);
        let mut bases = Vec::with_capacity(UNROLL);
        for k in 0..UNROLL {
            let base_off = if k == 0 {
                pos0
            } else {
                let s = splat_const(func, pre, vf * k as i64, elem_code, const_class);
                let p = alloc(func, RegClass::Fpr128);
                emit_before(
                    func,
                    pre,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(p), vreg(pos0), vreg(s), imm(arr_code)],
                );
                p
            };
            // Independent register (advanced in place each iteration); the
            // immutable base also seeds shifted iotas (`iv ± K`).
            posv.push(vcopy(func, pre, base_off));
            bases.push(base_off);
        }
        let width_splat = splat_const(func, pre, width, elem_code, const_class);
        (posv, bases, Some(width_splat))
    } else {
        (Vec::new(), Vec::new(), None)
    };

    // --- Preheader: element-size constant + ONE RUNNING POINTER per stream
    // (`p = base + idx0*elem`); the i32 path also sign-extends iv/bound for the
    // sxtw guard, the i64 path uses iv directly (already 64-bit).
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
        // `main_bound = sxtw(bound) - (width-1)` — exact in i64 (sxtw(bound) is
        // in i32 range so the subtract cannot wrap).
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
        // --- i64 Precheck + UNSIGNED vector header (see the module docs and
        // neon_array::apply_i64 for the wrap-freedom argument).
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
        // both sides stay within i32 range in i64 arithmetic).
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
    // post-index `LDP Qt1, Qt2, [p], #32` pair loads — the SAME 64 bytes per
    // iteration in the SAME order, so accumulator `k` still reads elements
    // `[iv+vf*k, iv+vf*(k+1))`. The pointer advances by `width*elem = 64`
    // bytes per iteration while the latch advances `iv` by `width`, so
    // `p == base + idx*elem` holds at every header evaluation (the guard keeps
    // `iv` wrap-free). Then combine per accumulator.
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
        accum: 0,
        vbody: vb,
        preheader_term: pre,
        arr_code,
        elem_code,
        const_class,
        is_i64: rec.is_i64,
        iv: rec.iv,
        posv: posv.clone(),
        iota_bases: iota_bases.clone(),
        pending_advances: Vec::new(),
        used_bare_iv: false,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        loads: rec.loads.clone(),
        loaded,
        const_cache: HashMap::new(),
        memo: HashMap::new(),
    };
    for k in 0..UNROLL {
        ctx.accum = k;
        ctx.memo.clear();
        let Some(vterm) = lower(func, &mut ctx, rec.term) else {
            return false;
        };
        // vacc[k] = REDUCE(vacc[k], vterm)  (per lane).
        emit_vreduce(
            func,
            vb,
            rec.op,
            rec.is_i64,
            arr_code,
            vacc[k],
            [vacc[k], vterm],
        );
        // Advance this accumulator's iotas AFTER lowering consumed them this
        // iteration (`pos += splat(width)` — next iteration's lane positions):
        // posv[k] only if the BARE iv was lowered, plus every shifted iota
        // (`iv ± K`) created for this accumulator.
        if let Some(ws) = width_splat {
            if ctx.used_bare_iv {
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(posv[k]), vreg(posv[k]), vreg(ws), imm(arr_code)],
                );
            }
            for sh in std::mem::take(&mut ctx.pending_advances) {
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(sh), vreg(sh), vreg(ws), imm(arr_code)],
                );
            }
        }
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

    // --- Vector exit: combine accumulators with the SAME op (balanced tree),
    // horizontally reduce, then fold into the scalar accumulator.
    let mut level = vacc.clone();
    while level.len() > 1 {
        let mut next = Vec::new();
        let mut i = 0;
        while i + 1 < level.len() {
            // On the i64 min/max path, combine IN PLACE into level[i] (dead
            // afterwards) so the tied-destination BIT applies to the combine
            // tree too (clang's shape); otherwise a fresh destination.
            let d = if rec.is_i64 && rec.op.is_minmax() {
                level[i]
            } else {
                alloc(func, RegClass::Fpr128)
            };
            emit_vreduce(
                func,
                vx,
                rec.op,
                rec.is_i64,
                arr_code,
                d,
                [level[i], level[i + 1]],
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
            let w = alloc(func, const_class);
            emit(
                func,
                vx,
                AArch64Opcode::NeonUmovGen,
                vec![vreg(w), vreg(vsum), imm(lane), imm(elem_code)],
            );
            w
        })
        .collect();

    // Fold the lanes INTO the scalar accumulator (`acc` still holds its
    // pre-loop value M0 — the vector loop never wrote it). The fold consumes M0
    // before overwriting `acc` on the final step, so when 0 vector iterations
    // ran (all lanes = identity) the result is exactly M0.
    fold_into_acc(func, vx, rec.op, rec.acc, &lane_regs, const_class);
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

// ---------------------------------------------------------------------------
// argmin / argmax transformation
// ---------------------------------------------------------------------------

/// Broadcast a small constant across every lane in the preheader
/// (`Movz Wt/Xt, #v` + `DUP Vd.4S/.2D, Wt/Xt`). Both already-modeled opcodes;
/// `elem_code`/`const_class` select the lane width.
fn splat_const(
    func: &mut MachFunction,
    before: InstId,
    value: i64,
    elem_code: i64,
    const_class: RegClass,
) -> VReg {
    let w = alloc(func, const_class);
    emit_before(func, before, AArch64Opcode::Movz, vec![vreg(w), imm(value)]);
    let v = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        before,
        AArch64Opcode::NeonDupGen,
        vec![vreg(v), vreg(w), imm(elem_code)],
    );
    v
}

/// Materialize the per-lane index iota `[0, 1, .., vf-1]` in the preheader:
/// `MOVI Vd, #0` (all lanes 0 ⇒ lane 0 done) then `INS Vd.S/D[j], Wj/Xj` for
/// `j ∈ [1, vf)`. MOVI / INS / Movz are already-modeled (allowlisted permute /
/// const) opcodes. `.4S` iota is `[0,1,2,3]`; `.2D` iota is `[0,1]`.
fn build_iota(
    func: &mut MachFunction,
    before: InstId,
    vf: i64,
    elem_code: i64,
    const_class: RegClass,
) -> VReg {
    let v = alloc(func, RegClass::Fpr128);
    emit_before(func, before, AArch64Opcode::NeonMovi, vec![vreg(v), imm(0)]);
    for lane in 1..vf {
        let w = alloc(func, const_class);
        emit_before(func, before, AArch64Opcode::Movz, vec![vreg(w), imm(lane)]);
        emit_before(
            func,
            before,
            AArch64Opcode::NeonInsGen,
            vec![vreg(v), vreg(w), imm(lane), imm(elem_code)],
        );
    }
    v
}

/// Copy a `.16B` vector register (`ORR Vd, Vn, Vn` = the ISA `MOV Vd, Vn`).
/// `NeonOrrV` is a faithfully-proven whole-register op.
fn vcopy(func: &mut MachFunction, before: InstId, src: VReg) -> VReg {
    let d = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        before,
        AArch64Opcode::NeonOrrV,
        vec![vreg(d), vreg(src), vreg(src)],
    );
    d
}

/// Per-lane branchless select `acc = mask ? src : acc` (in place). Uses the
/// PROVEN tied-destination `BIT` (`acc ^= (acc ^ src) & mask`) when enabled, else
/// the fail-closed proven `EOR/AND/EOR` bitselect — mirrors [`emit_vreduce`]'s
/// i64 min/max path. `mask` is `.4S`/`.2D`, all-ones/all-zeros per lane (`BIT`
/// and the bitselect chain are lane-width-agnostic whole-register logic).
fn emit_bitselect_inplace(
    func: &mut MachFunction,
    block: BlockId,
    acc: VReg,
    src: VReg,
    mask: VReg,
) {
    if MINMAX_BIT_ENABLED {
        emit(
            func,
            block,
            AArch64Opcode::NeonBitV,
            vec![vreg(acc), vreg(src), vreg(mask)],
        );
        return;
    }
    let x1 = alloc(func, RegClass::Fpr128);
    emit(
        func,
        block,
        AArch64Opcode::NeonEorV,
        vec![vreg(x1), vreg(acc), vreg(src)],
    );
    let x2 = alloc(func, RegClass::Fpr128);
    emit(
        func,
        block,
        AArch64Opcode::NeonAndV,
        vec![vreg(x2), vreg(x1), vreg(mask)],
    );
    emit(
        func,
        block,
        AArch64Opcode::NeonEorV,
        vec![vreg(acc), vreg(acc), vreg(x2)],
    );
}

/// Vectorize an [`ArgRecognized`] argmin/argmax loop (i32 `.4S` / i64 `.2D`).
///
/// PURELY ADDITIVE (like [`apply`]): a vector main loop is spliced in front of
/// the untouched scalar loop, which handles the `< width` tail (`width` = 16
/// i32 lanes or 8 i64 lanes). Per accumulator `k` (lanes `vf*k..vf*(k+1)`) two
/// vectors are carried:
/// * `vval[k]` — the running min/max VALUE, seeded with the reduction identity.
/// * `vidx[k]` — the running best INDEX, seeded with the lane's FIRST position
///   `iv0 + vf*k + [0..vf)` (so an all-identity lane reports its first
///   position, the correct first-occurrence when the min value equals the
///   identity).
///
/// Each iteration: `mask = (v <strict-better> vval)` (`CMGT`/`CMHI` `.4S`/`.2D`,
/// oriented by [`ReduceOp::d2_pick_cand_cmp`]); `vval = mask ? v : vval` (= the
/// min/max); `vidx = mask ? pos : vidx` (same mask, the width-agnostic tied
/// `BIT`); `pos += width`. STRICT compare ⇒ on a per-lane value tie the mask is
/// 0 and the EARLIER index is kept.
///
/// At exit the `width` `(value, index)` lane pairs are folded — together with
/// the pre-loop `(M0, I0)` — by a scalar **(value, min-index) lexicographic**
/// reduce (better value wins; ties break to the smaller INDEX VALUE), and
/// written back into `best_val`/`best_idx` to seed the scalar tail.
/// Commutative+associative (width-independently — see the module docs), so this
/// equals the scalar loop's first-occurrence left-fold.
fn apply_arg(func: &mut MachFunction, rec: &ArgRecognized) -> bool {
    // Per-width parameters (mirrors `apply`): i32 = `.4S` + sxtw guard; i64 =
    // `.2D` + precheck + unsigned guard.
    let (vf, elem_bytes, arr_code, elem_code, const_class) = if rec.is_i64 {
        (VF_I64, ELEM_BYTES_I64, ARR_D2, ELEM_D, RegClass::Gpr64)
    } else {
        (VF, ELEM_BYTES, ARR_S4, ELEM_S, RegClass::Gpr32)
    };
    let width = UNROLL as i64 * vf;

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
    if let Some(pv) = pv {
        func.add_edge(pv, vh);
        func.add_edge(pv, rec.guard);
    }
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: value accumulators seeded with the identity.
    let vval: Vec<VReg> = (0..UNROLL)
        .map(|_| emit_identity(func, pre, rec.op.identity(), rec.is_i64))
        .collect();

    // --- Preheader: index infrastructure. `pos0 = splat(iv0) + [0..vf)`; the
    // per-accumulator running position `pos_k = pos0 + vf*k`; the index
    // accumulator `vidx[k]` is seeded with that same first-position vector.
    let iota = build_iota(func, pre, vf, elem_code, const_class);
    let dup_iv = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonDupGen,
        vec![vreg(dup_iv), vreg(rec.iv), imm(elem_code)],
    );
    let pos0 = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonAddV,
        vec![vreg(pos0), vreg(dup_iv), vreg(iota), imm(arr_code)],
    );
    let mut posv: Vec<VReg> = Vec::with_capacity(UNROLL);
    let mut vidx: Vec<VReg> = Vec::with_capacity(UNROLL);
    for k in 0..UNROLL {
        // The lane-offset base for accumulator k: pos0 (k==0) or pos0 + vf*k.
        let base_off = if k == 0 {
            pos0
        } else {
            let s = splat_const(func, pre, vf * k as i64, elem_code, const_class);
            let p = alloc(func, RegClass::Fpr128);
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonAddV,
                vec![vreg(p), vreg(pos0), vreg(s), imm(arr_code)],
            );
            p
        };
        // Separate registers: `posv[k]` is incremented every iteration; `vidx[k]`
        // is BIT-updated. Both start at the lane's first position.
        posv.push(vcopy(func, pre, base_off));
        vidx.push(vcopy(func, pre, base_off));
    }
    let width_splat = splat_const(func, pre, width, elem_code, const_class);

    // --- Preheader: element-size const, guard bound, running pointers
    // (identical to `apply`'s same-width path).
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
        // --- i64 Precheck + UNSIGNED vector header (identical to `apply`'s i64
        // path; see the module docs and neon_array::apply_i64 for the
        // wrap-freedom argument).
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

        emit(
            func,
            vh,
            AArch64Opcode::CmpRR,
            vec![vreg(rec.iv), vreg(main_bound)],
        );
        emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
        emit(func, vh, AArch64Opcode::B, vec![block(vx)]);
    } else {
        // --- i32 Vector header: guard `sxtw(iv) < main_bound`.
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

    // --- Vector body: paired post-index loads per stream, then per accumulator
    // the compare-masked value + index update and the position increment.
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
        accum: 0,
        vbody: vb,
        preheader_term: pre,
        arr_code,
        elem_code,
        const_class,
        is_i64: rec.is_i64,
        // argmin's value term is iv-free (the probe forbids it), so no iota
        // position vectors are threaded — the index is tracked by `posv`/`vidx`
        // in this function directly, not through `lower`.
        iv: rec.iv,
        posv: Vec::new(),
        iota_bases: Vec::new(),
        pending_advances: Vec::new(),
        used_bare_iv: false,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        loads: rec.loads.clone(),
        loaded,
        const_cache: HashMap::new(),
        memo: HashMap::new(),
    };
    let (cmp_op, cand_left) = rec.op.d2_pick_cand_cmp();
    for k in 0..UNROLL {
        ctx.accum = k;
        ctx.memo.clear();
        let Some(vterm) = lower(func, &mut ctx, rec.term) else {
            return false;
        };
        // mask = (v <strict-better> vval[k]) — all-ones exactly when the reduce
        // would replace vval[k] with v (STRICT: 0 on a per-lane tie).
        let (cl, cr) = if cand_left {
            (vterm, vval[k])
        } else {
            (vval[k], vterm)
        };
        let mask = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            cmp_op,
            vec![vreg(mask), vreg(cl), vreg(cr), imm(arr_code)],
        );
        // vval[k] = mask ? v : vval[k]  (= min/max); vidx[k] = mask ? pos : vidx[k].
        emit_bitselect_inplace(func, vb, vval[k], vterm, mask);
        emit_bitselect_inplace(func, vb, vidx[k], posv[k], mask);
        // pos += width (next iteration's lane positions).
        emit(
            func,
            vb,
            AArch64Opcode::NeonAddV,
            vec![
                vreg(posv[k]),
                vreg(posv[k]),
                vreg(width_splat),
                imm(arr_code),
            ],
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

    // --- Vector exit: fold the `width` (value, index) lane pairs — plus the
    // pre-loop (M0, I0) — by a scalar (value, min-index) lexicographic reduce,
    // then write the result into best_val/best_idx to seed the scalar tail.
    let better_cc = rec.op.fold_cc(); // strict better: LT/GT/HI/LO
    let mut run_val = rec.best_val; // M0 (read-only initial value)
    let mut run_idx = rec.best_idx; // I0
    for k in 0..UNROLL {
        for lane in 0..vf {
            let vl_lane = alloc(func, const_class);
            emit(
                func,
                vx,
                AArch64Opcode::NeonUmovGen,
                vec![vreg(vl_lane), vreg(vval[k]), imm(lane), imm(elem_code)],
            );
            let il_lane = alloc(func, const_class);
            emit(
                func,
                vx,
                AArch64Opcode::NeonUmovGen,
                vec![vreg(il_lane), vreg(vidx[k]), imm(lane), imm(elem_code)],
            );
            // take = (vl BETTER run_val) OR (vl == run_val AND il < run_idx).
            emit(
                func,
                vx,
                AArch64Opcode::CmpRR,
                vec![vreg(vl_lane), vreg(run_val)],
            );
            let g_better = alloc(func, RegClass::Gpr64);
            emit(
                func,
                vx,
                AArch64Opcode::CSet,
                vec![vreg(g_better), imm(better_cc)],
            );
            let g_eq = alloc(func, RegClass::Gpr64);
            emit(func, vx, AArch64Opcode::CSet, vec![vreg(g_eq), imm(CC_EQ)]);
            emit(
                func,
                vx,
                AArch64Opcode::CmpRR,
                vec![vreg(il_lane), vreg(run_idx)],
            );
            let g_lt = alloc(func, RegClass::Gpr64);
            emit(func, vx, AArch64Opcode::CSet, vec![vreg(g_lt), imm(CC_LT)]);
            let g_tie = alloc(func, RegClass::Gpr64);
            emit(
                func,
                vx,
                AArch64Opcode::AndRR,
                vec![vreg(g_tie), vreg(g_eq), vreg(g_lt)],
            );
            let g_take = alloc(func, RegClass::Gpr64);
            emit(
                func,
                vx,
                AArch64Opcode::OrrRR,
                vec![vreg(g_take), vreg(g_better), vreg(g_tie)],
            );
            emit(func, vx, AArch64Opcode::CmpRI, vec![vreg(g_take), imm(0)]);
            let nv = alloc(func, const_class);
            emit(
                func,
                vx,
                AArch64Opcode::Csel,
                vec![vreg(nv), vreg(vl_lane), vreg(run_val), imm(CC_NE)],
            );
            let ni = alloc(func, const_class);
            emit(
                func,
                vx,
                AArch64Opcode::Csel,
                vec![vreg(ni), vreg(il_lane), vreg(run_idx), imm(CC_NE)],
            );
            run_val = nv;
            run_idx = ni;
        }
    }
    // Commit the folded result into the carried scalars (safe: their pre-loop
    // values were only READ, as the initial run_val/run_idx above).
    emit(
        func,
        vx,
        AArch64Opcode::MovR,
        vec![vreg(rec.best_val), vreg(run_val)],
    );
    emit(
        func,
        vx,
        AArch64Opcode::MovR,
        vec![vreg(rec.best_idx), vreg(run_idx)],
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

/// Emit `d = REDUCE(a, b)` (per-lane vector op) in `block`.
///
/// * i32 (or bitwise at any width): the single matching NEON op.
/// * i64 min/max (`.2D` — NO single-op form exists): the 4-op branchless
///   compare + bitselect `d = a ^ ((a ^ b) & mask)` where `mask` is the
///   `.2D` compare oriented so all-ones picks `b` over `a`
///   ([`ReduceOp::d2_pick_cand_cmp`]). With per-lane mask in {all-ones, 0}
///   this is exactly `REDUCE(a, b)`; on the equal boundary the mask is 0 and
///   `a` is kept (the same value). Every op is faithfully proven (`CMGT/CMHI`
///   `.2D` D-pair obligations; `EOR`/`AND` whole-register). `d` may alias `a`
///   (the accumulate) — `a` is only READ before the final write of `d`.
fn emit_vreduce(
    func: &mut MachFunction,
    block: BlockId,
    op: ReduceOp,
    is_i64: bool,
    arr_code: i64,
    d: VReg,
    inputs: [VReg; 2],
) {
    let [a, b] = inputs;
    if is_i64 && op.is_minmax() {
        let (cmp_op, cand_left) = op.d2_pick_cand_cmp();
        let (cl, cr) = if cand_left { (b, a) } else { (a, b) };
        let mask = alloc(func, RegClass::Fpr128);
        emit(
            func,
            block,
            cmp_op,
            vec![vreg(mask), vreg(cl), vreg(cr), imm(arr_code)],
        );
        if MINMAX_BIT_ENABLED && d == a {
            // The PROVEN single-op insert: BIT(d/a, b, mask) computes
            // `a ^ ((a ^ b) & mask)` in place — operand 0 is a TIED def-use
            // (the insert READS Vd); see `has_tied_def_use`. This is clang's
            // exact `cmgt.2d` + `bit.16b` accumulate shape.
            emit(
                func,
                block,
                AArch64Opcode::NeonBitV,
                vec![vreg(d), vreg(b), vreg(mask)],
            );
            return;
        }
        // Fail-closed (or fresh-destination) path: the 3-op EOR/AND/EOR
        // bitselect over proven whole-register ops.
        let x1 = alloc(func, RegClass::Fpr128);
        emit(
            func,
            block,
            AArch64Opcode::NeonEorV,
            vec![vreg(x1), vreg(a), vreg(b)],
        );
        let x2 = alloc(func, RegClass::Fpr128);
        emit(
            func,
            block,
            AArch64Opcode::NeonAndV,
            vec![vreg(x2), vreg(x1), vreg(mask)],
        );
        emit(
            func,
            block,
            AArch64Opcode::NeonEorV,
            vec![vreg(d), vreg(a), vreg(x2)],
        );
        return;
    }
    let mut operands = vec![vreg(d), vreg(a), vreg(b)];
    if op.vec_op_has_arr() {
        operands.push(imm(arr_code));
    }
    emit(func, block, op.vec_op(), operands);
}

/// Fold the horizontally-extracted lane values into the scalar accumulator
/// `acc` (which currently holds the pre-loop value M0), overwriting `acc` with
/// `REDUCE(M0, lane0, lane1, lane2, lane3)`.
fn fold_into_acc(
    func: &mut MachFunction,
    block: BlockId,
    op: ReduceOp,
    acc: VReg,
    lanes: &[VReg],
    class: RegClass,
) {
    let mut running = acc;
    for (i, &w) in lanes.iter().enumerate() {
        let last = i + 1 == lanes.len();
        let dst = if last { acc } else { alloc(func, class) };
        if op.is_minmax() {
            // CMP w, running ; CSEL dst, w, running, fold_cc
            //   ⇒ dst = (fold_cc holds on w-running) ? w : running = REDUCE(running, w)
            emit(
                func,
                block,
                AArch64Opcode::CmpRR,
                vec![vreg(w), vreg(running)],
            );
            emit(
                func,
                block,
                AArch64Opcode::Csel,
                vec![vreg(dst), vreg(w), vreg(running), imm(op.fold_cc())],
            );
        } else {
            // dst = running <bitwise> w
            emit(
                func,
                block,
                op.scalar_fold_op(),
                vec![vreg(dst), vreg(running), vreg(w)],
            );
        }
        running = dst;
    }
}

/// Materialize the per-lane reduction identity as a fresh vector in the
/// preheader (built entirely from already-modeled opcodes). `is_i64` selects
/// the lane width (`.4S` vs `.2D` — the byte-replicating `MOVI` identities are
/// width-agnostic; the shifted ones use the width's shift amount / element
/// code).
fn emit_identity(func: &mut MachFunction, pre: InstId, id: Identity, is_i64: bool) -> VReg {
    let (arr_code, elem_code, const_class, sign_shift) = if is_i64 {
        (ARR_D2, ELEM_D, RegClass::Gpr64, 63)
    } else {
        (ARR_S4, ELEM_S, RegClass::Gpr32, 31)
    };
    match id {
        Identity::Zero => {
            let v = alloc(func, RegClass::Fpr128);
            emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(v), imm(0)]);
            v
        }
        Identity::AllOnes => {
            // MOVI Vd.16B, #0xFF ⇒ every byte 0xFF ⇒ all-ones per lane (any width).
            let v = alloc(func, RegClass::Fpr128);
            emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(v), imm(0xFF)]);
            v
        }
        Identity::IntMax => {
            // INT_MAX = all-ones >>u 1  (per lane, either width).
            let a = alloc(func, RegClass::Fpr128);
            emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(a), imm(0xFF)]);
            let v = alloc(func, RegClass::Fpr128);
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonUshrVImm,
                vec![vreg(v), vreg(a), imm(1), imm(arr_code)],
            );
            v
        }
        Identity::IntMin => {
            // INT_MIN = 1 << (lane_bits - 1)  (per lane).
            let w = alloc(func, const_class);
            emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(w), imm(1)]);
            let a = alloc(func, RegClass::Fpr128);
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonDupGen,
                vec![vreg(a), vreg(w), imm(elem_code)],
            );
            let v = alloc(func, RegClass::Fpr128);
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonShlVImm,
                vec![vreg(v), vreg(a), imm(sign_shift), imm(arr_code)],
            );
            v
        }
        Identity::One => {
            // 1 per lane: materialize 1 in a GPR and broadcast it with DUP (no
            // byte-replicate MOVI, which would give 0x0101…). Both Movz and
            // NeonDupGen are already-modeled ops. (Unreachable on i64 — the
            // product reduction BAILS there — but correct if ever reached.)
            let w = alloc(func, const_class);
            emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(w), imm(1)]);
            let v = alloc(func, RegClass::Fpr128);
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonDupGen,
                vec![vreg(v), vreg(w), imm(elem_code)],
            );
            v
        }
    }
}

/// Lower a term value to a `4 x i32` NEON value (in the vector body).
fn lower(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> Option<VReg> {
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
    }
    // The AFFINE IOTA leaf: the bare induction variable -> this accumulator's
    // per-lane position vector (holding the exact scalar iv values this
    // iteration). Only populated when recognition set `uses_iv`.
    if val == ctx.iv && !ctx.posv.is_empty() {
        let v = *ctx.posv.get(ctx.accum)?;
        ctx.used_bare_iv = true;
        ctx.memo.insert(val.id, v);
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
    let &def_id = ctx.def.get(&val.id)?;
    if !ctx.loop_insts.contains(&def_id) {
        return None;
    }
    let inst = func.inst(def_id);
    let opcode = inst.opcode;
    let ops = inst.operands.clone();
    use AArch64Opcode::*;
    // SHIFTED-IOTA fold: `iv + K` / `iv - K` becomes its own loop-carried
    // position vector — seeded `iota_base[accum] ± K` in the preheader and
    // advanced by `splat(width)` per iteration (registered on
    // `pending_advances`) — instead of a per-iteration `pos + splat(K)` add.
    // Lane `l` holds `(iv0 + vf*k + l ± K) + width*t = scalar (iv ± K)` at
    // every iteration `t`, wrapping mod 2^lane-width exactly like the scalar
    // AddRI/SubRI — the same per-lane-exactness argument as the bare iota,
    // one op cheaper per accumulator-iteration (clang's index-vector shape).
    if !ctx.posv.is_empty()
        && let Some(k) = shift_of_iv(func, ctx, opcode, &ops)
        && k != 0
    {
        let v = emit_shifted_iota(func, ctx, k);
        ctx.memo.insert(val.id, v);
        return Some(v);
    }
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

/// Decode `val = iv ± K` (a shifted-iota candidate): `AddRI(iv, K)`,
/// `SubRI(iv, K)`, `AddRR(iv, const)` (either operand order), or
/// `SubRR(iv, const)`. Returns the SIGNED shift. `const - iv` is NOT a shift
/// (slope -1) and falls through to the generic per-iteration lowering.
fn shift_of_iv(
    func: &MachFunction,
    ctx: &LowerCtx,
    opcode: AArch64Opcode,
    ops: &[MachOperand],
) -> Option<i64> {
    use AArch64Opcode::*;
    match opcode {
        AddRI if vreg_of(&ops[1]) == Some(ctx.iv) => imm_of(&ops[2]),
        SubRI if vreg_of(&ops[1]) == Some(ctx.iv) => imm_of(&ops[2]).map(|k| -k),
        AddRR => {
            let a = vreg_of(&ops[1])?;
            let b = vreg_of(&ops[2])?;
            if a == ctx.iv {
                const_value(func, &ctx.def, b)
            } else if b == ctx.iv {
                const_value(func, &ctx.def, a)
            } else {
                None
            }
        }
        SubRR if vreg_of(&ops[1]) == Some(ctx.iv) => {
            const_value(func, &ctx.def, vreg_of(&ops[2])?).map(|k| -k)
        }
        _ => None,
    }
}

/// Materialize the shifted iota for `iv + k` (`k != 0`, `|k| <= 0xFFFF`): a
/// fresh loop-carried vector seeded `iota_base[accum] ± |k|` in the preheader
/// (proven `ADD`/`SUB` per-lane ops; the splat is const_vec-cached) and
/// registered for the per-iteration `+= splat(width)` advance.
fn emit_shifted_iota(func: &mut MachFunction, ctx: &mut LowerCtx, k: i64) -> VReg {
    let base = ctx.iota_bases[ctx.accum];
    let ks = const_vec(func, ctx, k.unsigned_abs() as i64);
    let sh = alloc(func, RegClass::Fpr128);
    let op = if k > 0 {
        AArch64Opcode::NeonAddV
    } else {
        AArch64Opcode::NeonSubV
    };
    emit_before(
        func,
        ctx.preheader_term,
        op,
        vec![vreg(sh), vreg(base), vreg(ks), imm(ctx.arr_code)],
    );
    ctx.pending_advances.push(sh);
    sh
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

// ---------------------------------------------------------------------------
// Small local IR helpers (kept independent of neon_array.rs / neon_reduce.rs)
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
