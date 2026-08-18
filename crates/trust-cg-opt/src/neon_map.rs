// trust-cg-opt - SOUND NEON elementwise memory-MAP/STORE vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON memory-map vectorizer (`neon-map`)
//!
//! Vectorizes counted integer *store* (map) loops whose body writes a single
//! output array from a **lane-wise** term over read-only input arrays, of the
//! shape
//!
//! ```text
//! for i in 0..n (signed i < n):  a[i] = TERM(b[i], c[i], ...)
//! ```
//!
//! where `a` is a **store pointer**, the pointers `b, c, ...` are **only loaded**
//! in the loop, and `TERM` is a lane-wise integer function of the loaded `i32`
//! elements, 16-bit constants, and **loop-invariant scalar registers**
//! (broadcast to every lane via `DUP`) using `+ - * & | ^ << >>` (plus the
//! fused `madd`). The store-form **matmul row update**
//! `c[j] = c[j] + s*b[j]` — a saxpy where `s = A[i][k]` is a loop-invariant
//! scalar and the row bases `c = C + i*N`, `b = B + k*N` are *derived* row
//! pointers — is the motivating case: `s` DUP-broadcasts once, and each derived
//! base is resolved to the `noalias` param it is *based on* for the aliasing
//! gate (see regime (B)). The important special case is the SINGLE-ARRAY **in-place** map
//! `a[i] = f(a[i], a[i], ...)` — where the only array touched is `a` itself, read
//! and written at the same index `i` — which is vectorized **without any
//! `noalias` attribute** (see the two regimes under *Why this is SOUND*). Each
//! loaded array is walked with paired NEON `LDP Qt1, Qt2` post-index loads, the per-lane
//! term is computed in `UNROLL = 4` independent `4 x i32` vector registers (16
//! elements per vector iteration), and each vector is written back to `a[]` with
//! a NEON `ST1 {Vt.4S}`. The ORIGINAL scalar loop handles the `< 16` tail
//! iterations unchanged.
//!
//! It runs **after** [`crate::neon_array`] / [`crate::neon_reduce`] (which handle
//! *reductions* and BAIL on any store) and **before** [`crate::reduction_split`].
//! Disable with `TRUST_CG_DISABLE_PASSES=neon_map`.
//!
//! ## Why this is SOUND — the store makes ALIASING load-bearing
//!
//! Like the reduction vectorizers, the transform is **purely additive**: it
//! inserts a vector main loop in front of the scalar loop and never edits the
//! scalar loop's instructions. The scalar loop is therefore correct by
//! construction; only the inserted vector loop needs justifying. Two facts do
//! that:
//!
//! * **The vector loop writes exactly the memory `a[0..V)` the scalar loop would
//!   write, with the same per-lane values, and reads exactly `x[iv..iv+16)` of
//!   each input.** The recognized store/load addresses are all
//!   `base + sext(iv)*4` (a `gep i32` at the SAME index `i`), unit stride. The
//!   vector guard enters the body only when `sext(iv) + 15 < sext(n)` (computed
//!   in `i64` after sign-extending both from `i32`, so no overflow), so every
//!   lane index `iv..iv+15 < n` — an index the scalar loop also accesses. Each
//!   accumulator's per-lane term maps every scalar op to the `.4S` op proven
//!   per-lane-equivalent in `trust-cg-verify` (`ADD/SUB/MUL/AND/ORR/EOR`, plus
//!   immediate `SHL/USHR/SSHR`). The vector loop advances `iv` by 16 and exits
//!   with `iv = V` (a multiple of 16, `V <= n`); the unchanged scalar loop then
//!   writes the disjoint tail `a[V..n)`. So `a[0..n)` is written exactly once,
//!   with the scalar values.
//!
//! * **No store can clobber a not-yet-read input (aliasing).** This is the crux,
//!   and it is decided by one of two independently-sound regimes:
//!
//!   * **(A) SINGLE-ARRAY IN-PLACE — no `noalias` needed.** When the ONLY pointer
//!     the loop touches is the store base `a` — every load in the body is a
//!     recognized `a[i]` at the SAME index as the store and there is no other
//!     load / store / call / atomic — the loop is exactly
//!     `for i<n: a[i] = f(a[i], a[i], ...)`. Aliasing is load-bearing ONLY when
//!     **two distinct accessed pointers** can overlap; with exactly one accessed
//!     pointer there is no second access to alias, so whether `a` aliases some
//!     *other* (never-accessed-in-loop) param is irrelevant. Per element the
//!     scalar loop reads `a[i]` (every use sees the same value — nothing writes
//!     `a[i]` first) then writes `a[i]`; the vector body issues all `LD1` of
//!     `a[iv..iv+16)` **before** any `ST1` to the same range (separate post-index
//!     pointers over identical addresses), latching every element into a lane
//!     before overwrite, with disjoint ranges across iterations. Multi-use of the
//!     loaded value (`x*x*x`) is supported — a load leaf memoizes to one vector
//!     register. So the vector loop is byte-for-byte equal to the scalar loop for
//!     ANY aliasing of the unused-in-loop params.
//!   * **(B) MULTI-POINTER — `noalias` REQUIRED.** If a *distinct* input base
//!     pointer appears (`a[i]=g(a[i],b[i])`, or the matmul `c[j]+=s*b[j]`), two
//!     distinct pointers are accessed and disjointness must be proven. Bases may
//!     be *derived* row pointers (`crow = C + i*N*4`) rather than raw params, so
//!     each base is resolved to the **`noalias` param it is *based on*** by
//!     walking its pointer-derivation chain (`Madd`/`AddRI`/copy —
//!     `underlying_noalias_param`). Under the `noalias` (C `restrict`) contract a
//!     pointer based on param `C` never aliases one based on a *distinct* param
//!     `B`, so: the store base must root at a `noalias` param AND every input
//!     base `x` must be either (i) the *identical* vreg as the store base
//!     (in-place, same index) or (ii) rooted at a *distinct* `noalias` param. A
//!     second derived pointer into the *same* underlying param at a different
//!     offset is NOT proven disjoint, so it BAILS. The load/store index ranges
//!     are identical per iteration (same-index reads only — a shifted stencil
//!     `a[i±k]` has a different index expression and fails the address check, so
//!     it BAILS).
//!
//! If ANY premise is unprovable (regime (B) base not `noalias`, non-unit stride,
//! shifted read, i64 accumulator, a second store / call / atomic / unmodeled op,
//! the induction used as a term value, an unrecognized term op) the loop is left
//! **entirely** to the scalar path — fail-closed beats miscompile.
//!
//! ## i64 (`.2D`) support
//!
//! `i64` maps (`Gpr64` iv/bound/term, `x[i] = *(base + iv*8)` addresses)
//! vectorize on the `.2D` path (`2 x i64` lanes, `WIDTH = UNROLL*2 = 8`) for
//! the **non-multiply** lane-wise ops that exist at `.2D` — `add`, `sub`,
//! `and`, `or`, `xor`, `shl`, `ushr`, `sshr` (each with a faithful `.2D`
//! D-pair proof; the bitwise ops are lane-width-agnostic whole-register
//! logic). Any multiply in the term (`b[i]*k`, the fused `madd`) BAILS —
//! `MUL.2D` is UNALLOCATED in the ISA (the encoder rejects it fail-closed),
//! so an `a[i] = b[i]*k + c` map stays scalar and only its non-multiply
//! siblings vectorize. Because `i64` has no `i32→i64` sign-extension headroom,
//! the bounds guard is [`crate::neon_array`]'s unsigned-subtraction guard
//! behind a signed `n < WIDTH` precheck (see `neon_array::apply_i64` for the
//! wrap-freedom argument); the aliasing regimes (A)/(B) are width-independent
//! and unchanged.
//!
//! ## REVERSE (descending) counted loops
//!
//! `for i = n-1; i >= 0; i--: a[i] = TERM` (step `-1`, `iv >= 0` signed-GE
//! exit) vectorizes with **descending block addressing**: the vector body
//! processes the block `[iv-(width-1), iv]` (block-start `si = iv-(width-1)`,
//! the same ascending lane order within the block) and the latch steps `iv`
//! DOWN by `width`. This is sound because a map's lanes are **independent** —
//! iteration `i` touches exactly `a[i]`/`x[i]` and nothing else — so the SET
//! of (index, stored value) pairs is direction-invariant and any store order
//! writes byte-identical memory. The guard is a plain signed `iv >= width-1`
//! compare against a CONSTANT (no addition ⇒ no overflow; width-uniform for
//! i32/i64, so no i64 precheck block): it admits the block `[iv-(width-1),
//! iv] ⊆ [0, init_iv]`, a subset of the indices the scalar loop itself
//! accesses, and on exit (`iv < width-1`) the untouched scalar loop finishes
//! the low tail `a[iv..=0]` — `[0, init_iv]` is covered exactly once. The
//! aliasing regimes (A)/(B) apply UNCHANGED (direction does not relax the
//! `noalias` gate: NATIVE reverse multi-pointer maps without `noalias` still
//! BAIL).
//!
//! ### ROTATED REVERSE (clang -O1) + runtime versioning
//!
//! clang -O1 lowers `for(i=n-1;i>=0;i--) y[i] += x[i]` to a ROTATED loop whose
//! phi `iv` counts the trip-count DOWN from `n` to `1`, folding the decrement
//! and the array index into ONE register: the header computes `idx = iv - 1`
//! (`AddRR(iv, negone)`), addresses `x[idx]`/`y[idx]` with it, and the latch
//! writes it back (`iv = idx`); the exit test lives in the HEADER as
//! `cmp iv, 1; b.gt <latch>` (continue while `iv > 1`, so the last body runs at
//! `iv==1`, index `0`). This is recognized as a descending map with **top index
//! `iv-1`** — the block-start offset becomes `si = iv - width` (guard
//! `iv >= width`, one more than the native `iv-(width-1)` / `iv >= width-1`) and
//! the vector-exit tail guard is `iv < 1 -> true-exit` (the do-while tail reads
//! index `iv-1`, safe only while `iv >= 1`). Because clang's arrays are
//! non-`restrict` and `MachFunction.noalias_params` is never populated in
//! production, this shape takes **regime (C) runtime alias versioning** (the same
//! byte-range disjointness guard as the forward path): the range length `n` is
//! the loop's INITIAL iv (`uxtw(n)`, recovered from the guard), and
//! `[base, base + n*elem)` is the SAME bytes visited up or down, so the guard is
//! direction-independent. Fail-closed on any deviation (compare RHS `!= 1`,
//! non-`iv-1` index, unrecoverable count).
//!
//! Only `<` (forward), `>= 0` (native reverse) and the rotated `iv > 1` (reverse)
//! exits are recognized; anything else stays scalar.
//!
//! ## Select diamonds: SIGNED min/max/CLAMP terms (CHAIN shape, `.4S` only)
//!
//! The bridge lowers `a[i] = if v>HI {HI} else if v<LO {LO} else {v}` (the
//! elementwise clamp, e.g. `d12_saturate`) NOT to `Csel` but to branchy MOV-arm
//! DIAMONDS inside the chain: a split `cmp v, HI; b.gt; b`, arms that are pure
//! `[MovR d, _; B join]` blocks (the else arm nesting one more compare diamond
//! for the LO test), and a join that forwards the merged register toward the
//! store. `recognize_select_region` parses these regions fail-closed (exact
//! block shapes, single-pred arms, join preds exactly the arm tails, compare
//! adjacent to its branch) and maps them onto the FAITHFULLY-PROVEN
//! `SMIN.4S`/`SMAX.4S` lanewise ops:
//!
//! * a single diamond whose arms are exactly the two compare operands is a
//!   signed MIN or MAX (`match_select_minmax` — the eight cc/arm pairings each
//!   carry an exact total identity, ties included);
//! * the nested two-diamond form is the two-sided CLAMP
//!   `smin(smax(v, LO), HI)`, accepted ONLY when the decoded constants prove
//!   `LO <= HI` (the composition identity is FALSE otherwise — see
//!   `recognize_select_region` for the four polarity forms and their proofs).
//!
//! UNSIGNED orderings (`u32` clamps compare `HI/HS/LO/LS`) never map to the
//! SIGNED SMIN/SMAX (that would mis-order sign-bit values — a silent
//! miscompile) and BAIL, as does ANY unmatched arm/polarity/bound shape. The
//! merged select destination is multi-def (one def per arm), so it is resolved
//! exclusively through `Recognized::selects` — never the def map — and the
//! ITERATION-LOCALITY gate (`validate_chain_locality`) proves every OTHER
//! in-loop-defined register is a plain per-iteration temporary (single def, no
//! use before def in chain order, nothing visible outside the loop): the vector
//! loop replaces whole iterations, so no hidden loop-carried scalar state may
//! survive recognition. The wrapping story is unchanged: the clamp compares the
//! WRAPPED `v` (e.g. `a[i].wrapping_add(r)` lowered per-lane by the proven
//! `ADD.4S`) exactly as the scalar loop does.

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
/// AArch64 condition code for signed less-than (`LT`).
const CC_LT: i64 = 11;
/// AArch64 condition code for signed greater-than-or-equal (`GE`) — the reverse
/// (descending) counted-loop `iv >= 0` continue test.
const CC_GE: i64 = 10;
/// AArch64 condition code for equal (`EQ`) — the rotated forward exit `iv+1==bound`.
const CC_EQ: i64 = 0;
/// AArch64 condition code for unsigned less-than (`LO`/`CC`).
const CC_LO: i64 = 3;
/// AArch64 condition code for unsigned lower-or-same (`LS`, i.e. `<=` unsigned) —
/// the runtime alias-versioning range-disjointness test (`a_end <=u x` or
/// `x_end <=u a`) in regime (C).
const CC_LS: i64 = 9;
/// AArch64 condition code for unsigned greater-than-or-equal (`HS`/`CS`) — the
/// rotated tail guard `iv >= bound` (vector consumed all `n`, skip the do-while).
const CC_HS: i64 = 2;
/// AArch64 condition code for signed greater-than (`GT`) — the ROTATED REVERSE
/// (clang -O1 `for(i=n-1;i>=0;i--)`) header continue test `iv > 1 -> latch`. The
/// phi `iv` counts the trip-count DOWN from `n` to `1`; the array index is
/// `iv - 1` (so the last body runs at `iv==1`, index `0`).
const CC_GT: i64 = 12;
/// AArch64 condition code for signed less-than-or-equal (`LE`) — accepted (with
/// `LT`) as a select-diamond ordering; ties pick equal values, so `LE` and `LT`
/// map to the SAME min/max (see [`match_select_minmax`]).
const CC_LE: i64 = 13;
/// Byte size of an `i32` array element.
const ELEM_BYTES: i64 = 4;
/// Byte size of an `i64` array element (`.2D` path).
const ELEM_BYTES_I64: i64 = 8;
/// Independent vector registers processed per vector iteration (ILP + fewer
/// loop iterations). `UNROLL * VF` i32 lanes are processed per iteration (16).
const UNROLL: usize = 4;

/// DIAGNOSTIC (`TCG_NEONMAP_TRACE`): report the exact structural gate a
/// candidate loop dies on. Recognition is a long chain of `return None`s, and
/// attributing a decline by reading the disassembly has been wrong every time it
/// was tried in this campaign — this prints the predicate instead.
#[inline]
fn nm_trace(args: std::fmt::Arguments<'_>) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ON.get_or_init(|| std::env::var_os("TCG_NEONMAP_TRACE").is_some()) {
        eprintln!("[neon-map] {args}");
    }
}

/// Kill switch for the shared-preheader relaxation below: set
/// `TCG_NO_NEONMAP_SHARED_PREHEADER=1` to restore the old `gpreds.len() == 1`
/// gate on every shape.
fn legacy_shared_preheader_gate() -> bool {
    static F: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *F.get_or_init(|| std::env::var_os("TCG_NO_NEONMAP_SHARED_PREHEADER").is_some())
}

macro_rules! nm_bail {
    ($($t:tt)*) => {{
        nm_trace(format_args!($($t)*));
        return None;
    }};
}

/// The `neon-map` machine pass.
#[derive(Default)]
pub struct NeonMapPass {
    /// Number of loops vectorized in the last run (diagnostics/tests).
    fired: usize,
}

impl NeonMapPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonMapPass {
    fn name(&self) -> &str {
        "neon-map"
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

impl NeonMapPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;
        // NOTE: unlike the original noalias-gated version, we can NO LONGER skip
        // functions with no `noalias` params — the provably-safe SINGLE-ARRAY
        // IN-PLACE case (`a[i]=f(a[i],...)`, the only pointer touched is the
        // store base) vectorizes WITHOUT any noalias attr (see the `R_alias`
        // gate). The multi-pointer path still requires noalias. Recognition is
        // linear and bails fast on non-map loops, so running it unconditionally
        // is cheap; correctness (fail-closed) is unaffected.

        // Recognize all candidate loops first; applying a plan only *adds* blocks
        // (never renumbers existing block/inst ids or edits other loops' blocks),
        // so recognized data for other loops stays valid.
        let mut plans = Vec::new();
        for lp in loops.all_loops() {
            nm_trace(format_args!(
                "fn={} consider header=b{} latch=b{} body={:?} hpreds={:?}",
                func.name,
                lp.header.0,
                lp.latch.0,
                {
                    let mut v: Vec<u32> = lp.body.iter().map(|b| b.0).collect();
                    v.sort_unstable();
                    v
                },
                func.block(lp.header)
                    .preds
                    .iter()
                    .map(|b| b.0)
                    .collect::<Vec<_>>()
            ));
            if let Some(rec) = Recognized::recognize(func, dom, lp.header, lp.latch, &lp.body) {
                nm_trace(format_args!(
                    "fn={} header=b{} RECOGNIZED",
                    func.name, lp.header.0
                ));
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
        if changed && std::env::var("TRUST_CG_DUMP_NEONMAP").is_ok() {
            eprintln!("[neon-map] fn={} vectorized={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// A fully validated, lane-wise-vectorizable memory-map loop.
struct Recognized {
    /// Preheader-guard block reached once before the loop.
    guard: BlockId,
    /// ROTATED FORWARD shape only: the loop's true EXIT block. The clang do-while
    /// scalar tail (`cmp iv+1,bound; b.eq exit`) is sound only when entered with
    /// `iv < bound`. When the vector loop consumes ALL `n` elements (n a multiple of
    /// the vector width ⇒ remainder 0), `apply` must route the vector exit HERE, not
    /// into the do-while, which would STORE `a[n]` and run off the end. `None` for
    /// the native / reverse shapes (no exit routing needed).
    rotated_exit: Option<BlockId>,
    /// Block that branches into `guard`.
    preheader: BlockId,
    /// The `preheader` terminator instruction targeting `guard`.
    preheader_term: InstId,
    /// Loop-carried induction register (`+1` forward / `-1` reverse each
    /// iteration).
    iv: VReg,
    /// Loop bound register. Forward (`!descending`): the `iv < bound` upper
    /// limit. Reverse (`descending`): the zero register the `iv >= 0` exit test
    /// compares against (or the iv itself as a placeholder for the `CmpRI(iv,0)`
    /// form — unused by the descending apply, which guards on the constant
    /// `width-1`).
    bound: VReg,
    /// CHAIN shape only: when the bounds-guard limit is a `CmpRI` IMMEDIATE
    /// (`iv <u K`, fixed array length `K <= 4095`), the constant `K`. `bound` is
    /// then a zero PLACEHOLDER never read; `apply` materializes `K` with a
    /// preheader `Movz` (exact: `K` is non-negative and 16-bit) and uses that
    /// register everywhere it would use `bound`. `None` for a register bound.
    bound_imm: Option<i64>,
    /// True when the counted loop DECREMENTS (`step -1`, `iv >= 0` exit): the
    /// map is vectorized with DESCENDING block addressing — sub-block `k` of the
    /// vector body processes elements `[iv-(width-1)+vf*k, .. +vf)`, and the
    /// vector loop walks `iv` down by `width` while `iv >= width-1`. The lanes of
    /// a map are independent, so processing the same elements in descending block
    /// order stores byte-identical memory. Forward loops keep the ascending path
    /// unchanged (byte-identical).
    descending: bool,
    /// True when recognized as the FORWARD bounds-guarded `while iv<N` CHAIN shape
    /// (`recognize_forward_chain`) rather than a strict 2-block loop: the body is a
    /// linear chain of blocks split by in-loop `iv <u N` bounds-check diamonds, all
    /// agreeing on ONE limit register `N` (== loop bound == every array length). It
    /// is always a forward i32/mixed (`.4S`) map; it only relaxes the shared tail's
    /// bound-width check (the loop-continue compares the possibly-i64 iv directly
    /// against an i64 length), and `apply` treats it exactly like a native forward
    /// map (safe top-test scalar guard, no exit routing).
    chain: bool,
    /// The per-iteration stored value (the map term), SSA def inside the loop.
    term: VReg,
    /// True when the map is `i64` (`Gpr64` iv/bound/term), lowered on the
    /// `.2D` path with the precheck + unsigned-subtraction bounds guard.
    is_i64: bool,
    /// Loop-invariant base pointer of the store `a[i]`.
    store_base: VReg,
    /// Global def map (`vreg id -> defining InstId`).
    def: HashMap<u32, InstId>,
    /// Instruction ids that live inside the loop body.
    loop_insts: HashSet<InstId>,
    /// Map from a recognized load's result vreg id to its (loop-invariant) base
    /// pointer register. Every non-constant leaf of `term` is one of these.
    loads: HashMap<u32, VReg>,
    /// Distinct input base pointers referenced by `term`'s loads, first-seen
    /// order (deterministic emission).
    bases: Vec<VReg>,
    /// Loop-invariant scalar vreg ids used as `term` leaves (broadcast via DUP,
    /// e.g. the matmul row scalar `s = A[i][k]` in `c[j] += s*b[j]`). Each is a
    /// value of the loop's width whose def dominates the preheader.
    inv_leaves: HashSet<u32>,
    /// CHAIN shape only: recognized select-diamond values (merged dest vreg id
    /// -> the signed min/max/clamp it computes). A select dest is MULTI-def (one
    /// def per arm), so `node_ok`/`lower` resolve it HERE — never through the
    /// (last-write-wins) def map. Empty for the 2-block shapes.
    selects: HashMap<u32, SelExpr>,
    /// Per-register LIVE def count (see [`build_def_count`]): the single-def
    /// gate for the copy-following term path and `const_signed`.
    def_count: HashMap<u32, u32>,
    /// Regime (C) RUNTIME ALIAS VERSIONING. Set when regime (B)'s STATIC
    /// `noalias` disjointness gate is unprovable, so `apply` emits a byte-range
    /// disjointness precheck guarding the vector loop: it branches to the
    /// (untouched) scalar loop when the store range may overlap any input range at
    /// runtime, and to the vector loop ONLY when they are proven disjoint. Sound
    /// independent of any producer `noalias` claim. Restricted to FORWARD i32
    /// (`.4S`) maps with no foreign load.
    needs_versioning: bool,
    /// Distinct input bases (`≠ store_base`) whose byte range `[x, x+n*elem)` must
    /// be proven disjoint from the store range `[a, a+n*elem)` at runtime (regime
    /// C). Empty unless `needs_versioning`.
    check_bases: Vec<VReg>,
    /// ROTATED REVERSE (clang -O1) only: the array INDEX register `iv - 1` used in
    /// every load/store address (clang folds the decrement and the index into one
    /// register: the latch writeback `iv = iv - 1` reuses the same value as the
    /// header's addressing index). `resolve_ai_base` accepts this register as the
    /// index in addition to `Sxtw(iv)`/`iv`. `None` for forward and native-reverse.
    rev_index: Option<VReg>,
    /// ROTATED REVERSE only: the i64 register holding the loop's INITIAL `iv` value
    /// (`uxtw(n)` = the element COUNT `n`), recovered from the preheader. The store
    /// range is `[base, base + count*elem)` — direction-independent, so regime (C)
    /// uses this in place of `sxtw(bound)` (which is a zero placeholder on the
    /// descending path). Must dominate the preheader. `None` otherwise.
    rev_count: Option<VReg>,
}

/// Opcodes permitted anywhere in the loop body. Anything else => BAIL (rules out
/// a SECOND store, calls, atomics, division and any unmodeled effect). Exactly
/// `StrRI` is permitted as the single output store (its uniqueness and `a[i]`
/// address are checked in [`Recognized::recognize`]). `TrapBoundsCheckExact` is a
/// pure, side-effect-free array-bounds-check proof carrier (`cmp;b.lo;brk` that
/// only ever traps on OUT-of-bounds); it is admitted here and then validated by
/// the SINGLE-N agreement in [`Recognized::recognize_tail`] (index == iv, limit ==
/// the constant loop bound), exactly as `neon_bytesum` does — this proves the
/// vectorized `[0,N)` range is in bounds, so the carrier is subsumed and the
/// vector loop (which is left carrier-free) reads only memory the scalar loop
/// also reads.
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
            | Uxtw
            | LdrRI
            | StrRI
            | TrapBoundsCheckExact
    )
}

/// If `v` is `Uxtw(n)` / `Sxtw(n)` (an i32->i64 widening), return the i32 source
/// `n`. Used to route a MIXED (i32 store/term, i64-widened index) rotated map
/// through the i32 `.4S` path: clang's rotated form computes the widened bound
/// `Uxtw(n)` inside the guard block (which does not dominate the vectorizer's
/// preheader), but its i32 source `n` dominates and is what the i32 apply
/// re-`Sxtw`s. Mirrors `neon_array::ext_source`.
fn ext_source(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<VReg> {
    let inst = func.inst(*def.get(&v.id)?);
    if matches!(inst.opcode, AArch64Opcode::Uxtw | AArch64Opcode::Sxtw) {
        vreg_of(&inst.operands[1])
    } else {
        None
    }
}

/// Recognize the ROTATED (clang -O1, folded at O2) FORWARD header exit test and
/// return the loop bound. The header must END with `CmpRR(iv+1, bound);
/// BCond(EQ|GE) -> <exit outside the loop body>` — clang's `for(i=0;i<n;i++)`
/// lowering, whose CSet/CmpRI boolean-materialize idiom the O2 peephole folds to
/// this direct compare-branch. iv steps +1 from 0 so iv+1 reaches bound exactly:
/// the counted trip [0, bound). Adjacent CmpRR->BCond => sound flag dataflow.
/// Fail-closed on any deviation. Mirrors `neon_array::recognize_rotated_header_exit`.
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

/// SIGNED constant value of `val` from its def: `Movz imm` (`imm` itself,
/// `[0, 0xFFFF]`) or `Movn imm` (`!imm` = `-(imm+1)`, the negative-constant
/// materialization the bridge emits for e.g. `-100` — the same signed value at
/// both W and X width). Used ONLY by the select-diamond min/max/clamp matcher,
/// where the value participates in a PROOF (`lo <= hi`, arm == compare bound),
/// so it is stricter than [`const_value`]: the register must have exactly ONE
/// def in the whole function (a second def — e.g. a following `Movk`
/// page-extend — would make the decoded value wrong for some path; fail-closed)
/// and that def must be LIVE (attached to a block).
fn const_signed(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    def_count: &HashMap<u32, u32>,
    val: VReg,
) -> Option<i64> {
    if def_count.get(&val.id).copied() != Some(1) {
        return None;
    }
    let def_id = *def.get(&val.id)?;
    block_of_inst(func, def_id)?;
    let inst = func.inst(def_id);
    if inst.operands.len() != 2 {
        return None;
    }
    let v = imm_of(&inst.operands[1])?;
    if !(0..=0xFFFF).contains(&v) {
        return None;
    }
    match inst.opcode {
        AArch64Opcode::Movz => Some(v),
        AArch64Opcode::Movn => Some(-(v + 1)),
        _ => None,
    }
}

/// Per-register def COUNT over every LIVE instruction (block-attached — ghost
/// instructions removed from blocks by earlier passes never execute and must
/// not count). Single-def registers are the only ones whose [`build_def_map`]
/// entry is unambiguous; the select-diamond recognizer and the copy-following
/// term path require `def_count == 1` before trusting a def-map lookup.
fn build_def_count(func: &MachFunction) -> HashMap<u32, u32> {
    let mut count: HashMap<u32, u32> = HashMap::new();
    for block in &func.blocks {
        for &id in &block.insts {
            let inst = func.inst(id);
            if inst.produces_value()
                && let Some(MachOperand::VReg(v)) = inst.operands.first()
            {
                *count.entry(v.id).or_insert(0) += 1;
            }
        }
    }
    count
}

/// A chain bounds-guard limit: either a register `N` (the `CmpRR` form) or a
/// small constant `K` (the `CmpRI` form the bridge emits when the fixed array
/// length fits the 12-bit compare immediate, e.g. `[i32; 2048]`). The walk's
/// SINGLE-N agreement treats a register that materializes `K` and the immediate
/// `K` as the same limit; `apply` re-materializes an immediate limit with a
/// preheader `Movz` (exact: `K` is non-negative and `<= 4095 < 2^15`).
#[derive(Clone, Copy)]
enum ChainBound {
    Reg(VReg),
    Imm(i64),
}

/// Recognize a block's terminating array-bounds-check diamond `CmpRR(x, N) |
/// CmpRI(x, K); BCond(LO, t_lo); B(t_b)` (the last three instructions), where the
/// `b.lo`-taken target `t_lo` is IN the loop `body` (the `iv < N` continue edge)
/// and the fall-through `t_b` is OUT of the body (the panic/exit edge). Returns
/// `(x, bound, t_lo)`. Fail-closed on any other terminator shape — the compare
/// must IMMEDIATELY precede the branch (so it reads exactly that compare's
/// flags), the condition must be unsigned `LO`, the immediate form must carry a
/// plain in-range `[0, 4095]` value, and the two edges must split cleanly in/out
/// of the body (mirrors the strict decode discipline of the AArch64
/// bounds-check-elimination guard parser).
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
    let bound = match cmp.opcode {
        AArch64Opcode::CmpRR if cmp.operands.len() == 2 => {
            ChainBound::Reg(vreg_of(&cmp.operands[1])?)
        }
        // The immediate `iv <u K` form: K is the 12-bit unsigned compare
        // immediate (a fixed array length `<= 4095`). Anything out of that range
        // is not a shape the bridge emits for this guard — fail closed.
        AArch64Opcode::CmpRI if cmp.operands.len() == 2 => {
            let k = imm_of(&cmp.operands[1])?;
            if !(0..=4095).contains(&k) {
                return None;
            }
            ChainBound::Imm(k)
        }
        _ => return None,
    };
    let x = vreg_of(&cmp.operands[0])?;
    let t_lo = *branch_targets(bcond).first()?;
    let t_b = *branch_targets(br).first()?;
    // The taken (`b.lo`, iv<N true) edge continues INTO the body; the fall-through
    // leaves it. Exactly one of each — anything else BAILS.
    if !body.contains(&t_lo) || body.contains(&t_b) {
        return None;
    }
    Some((x, bound, t_lo))
}

// ---------------------------------------------------------------------------
// Select-diamond (min/max/clamp) recognition — the bridge's branchy lowering of
// `a[i] = if v>HI {HI} else if v<LO {LO} else {v}` (and single min/max ifs).
// ---------------------------------------------------------------------------

/// The RHS of a select split's compare: a register or the `CmpRI` immediate.
#[derive(Clone, Copy)]
enum CmpRhs {
    Reg(VReg),
    Imm(i64),
}

/// A per-lane SIGNED min/max/clamp VALUE recognized from a MOV-arm select
/// diamond in the chain body, keyed by the diamond's merged destination
/// register in `Recognized::selects`. Lowered with the faithfully-proven
/// `SMIN.4S` / `SMAX.4S` lanewise ops (`.4S` ONLY — baseline NEON has no `.2D`
/// SMIN/SMAX, and the i64 path BAILS at recognition).
#[derive(Clone)]
enum SelExpr {
    /// `smin(a, b)` (`is_min`) / `smax(a, b)` — both operands are ordinary
    /// lane-wise term nodes, validated by `node_ok` like any other operand.
    MinMax { is_min: bool, a: VReg, b: VReg },
    /// `smin(smax(v, lo), hi)` — the two-sided clamp. `lo`/`hi` are the
    /// materialized constant registers; `const_signed(lo) <= const_signed(hi)`
    /// was PROVEN at recognition (the clamp identity is FALSE without it).
    Clamp { v: VReg, lo: VReg, hi: VReg },
}

/// Bookkeeping for a NESTED (inner) select of a clamp: its merged destination,
/// its two arm-copy def instructions, and the single join-block forwarding copy
/// that is its ONLY permitted use.
struct InnerSel {
    dest: VReg,
    def_insts: [InstId; 2],
    forward_use: InstId,
}

/// A fully parsed select-diamond region hanging off one chain split block.
struct SelRegion {
    /// The merged select destination (multi-def: one def per arm).
    dest: VReg,
    expr: SelExpr,
    /// The block where both arms re-join — the chain continues here.
    join: BlockId,
    /// Diamond-internal blocks consumed by the region (arms + inner join), in
    /// deterministic order; the chain walk marks them visited.
    consumed: Vec<BlockId>,
    /// The EXACT def instructions of `dest` (the two arm-tail copies).
    dest_def_insts: [InstId; 2],
    /// Present when the region nests an inner select (the clamp shape).
    inner: Option<InnerSel>,
}

/// Terminating compare-select split of `blk`: the LAST THREE instructions are
/// exactly `Cmp{RR,RI}(x, rhs); BCond(cc, t_blk); B(f_blk)` with BOTH targets
/// inside the loop body (a bounds guard exits the body; a select never does).
/// The compare IMMEDIATELY precedes the `BCond`, so the branch reads exactly
/// that compare's flags. Returns `(x, rhs, cc, t_blk, f_blk)`.
fn select_split(
    func: &MachFunction,
    blk: BlockId,
    body: &HashSet<BlockId>,
) -> Option<(VReg, CmpRhs, i64, BlockId, BlockId)> {
    let insts = &func.block(blk).insts;
    let n = insts.len();
    if n < 3 {
        return None;
    }
    let cmp = func.inst(insts[n - 3]);
    let bcond = func.inst(insts[n - 2]);
    let br = func.inst(insts[n - 1]);
    if bcond.opcode != AArch64Opcode::BCond || br.opcode != AArch64Opcode::B {
        return None;
    }
    let rhs = match cmp.opcode {
        AArch64Opcode::CmpRR if cmp.operands.len() == 2 => CmpRhs::Reg(vreg_of(&cmp.operands[1])?),
        AArch64Opcode::CmpRI if cmp.operands.len() == 2 => CmpRhs::Imm(imm_of(&cmp.operands[1])?),
        _ => return None,
    };
    let x = vreg_of(&cmp.operands[0])?;
    let cc = imm_of(&bcond.operands[0])?;
    let t_blk = *branch_targets(bcond).first()?;
    let f_blk = *branch_targets(br).first()?;
    if !body.contains(&t_blk) || !body.contains(&f_blk) || t_blk == f_blk {
        return None;
    }
    Some((x, rhs, cc, t_blk, f_blk))
}

/// A `[copy(d, s); B(j)]` MOV arm block (EXACTLY those two instructions).
/// Returns `(d, s, j, copy_inst)`.
fn mov_arm(func: &MachFunction, blk: BlockId) -> Option<(VReg, VReg, BlockId, InstId)> {
    let insts = &func.block(blk).insts;
    if insts.len() != 2 {
        return None;
    }
    let (d, s) = copy_like(func.inst(insts[0]))?;
    let br = func.inst(insts[1]);
    if br.opcode != AArch64Opcode::B {
        return None;
    }
    Some((d, s, *branch_targets(br).first()?, insts[0]))
}

/// True iff `blk`'s predecessor SET is exactly `expected` (no duplicates, no
/// extra entry paths — an unaccounted edge into a diamond block could reach the
/// join without executing an arm copy, so it MUST bail).
fn preds_exactly(func: &MachFunction, blk: BlockId, expected: &[BlockId]) -> bool {
    let preds = &func.block(blk).preds;
    preds.len() == expected.len() && expected.iter().all(|e| preds.contains(e))
}

/// Match a plain select `d = (x cc rhs) ? t : f` (values read at the split's
/// compare; NO instruction between the compare and the arm copies can write any
/// register — the split ends `Cmp;BCond;B` and each arm is a pure `[copy;B]`
/// block — so vreg identity means value identity) onto a signed MIN or MAX.
///
/// EXACT i32 identities, each total over ALL values including ties (at `x == y`
/// both sides of a tie are the same value, so `GT` vs `GE` / `LT` vs `LE` pick
/// bit-identical results and map to the SAME op):
///
/// ```text
///   x >s y ? x : y == smax(x,y)      x >s y ? y : x == smin(x,y)
///   x >=s y ? x : y == smax(x,y)     x >=s y ? y : x == smin(x,y)
///   x <s y ? x : y == smin(x,y)      x <s y ? y : x == smax(x,y)
///   x <=s y ? x : y == smin(x,y)     x <=s y ? y : x == smax(x,y)
/// ```
///
/// An arm matches the compare RHS either as the IDENTICAL register or as a
/// single-def materialized constant EQUAL to the compared constant (`Movz` /
/// `Movn` vs the `CmpRI` immediate). The `x` side must be the identical
/// register. ONLY the four SIGNED orderings are accepted: an UNSIGNED compare
/// (`HI/HS/LO/LS`, e.g. a `u32` clamp) must NOT map to SMIN/SMAX (wrong order
/// for values with the sign bit set — a silent miscompile) and BAILS here, as
/// does `EQ/NE` and any arm pairing other than exactly `{x, rhs}` — e.g. a
/// swapped/inverted arm order that would silently flip min<->max.
///
/// Returns `(is_min, a, b)` where `a`/`b` are the two SSA operand registers
/// (min/max are commutative, so operand order is irrelevant; the rhs-side
/// operand is the ARM register — the exact value the scalar select produces).
#[allow(clippy::too_many_arguments)]
fn match_select_minmax(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    def_count: &HashMap<u32, u32>,
    cc: i64,
    x: VReg,
    rhs: CmpRhs,
    t: VReg,
    f: VReg,
) -> Option<(bool, VReg, VReg)> {
    let is_gt = cc == CC_GT || cc == CC_GE;
    let is_lt = cc == CC_LT || cc == CC_LE;
    if !is_gt && !is_lt {
        return None; // unsigned / equality / flag conds: NOT a signed min/max
    }
    let matches_rhs = |a: VReg| match rhs {
        CmpRhs::Reg(r) => {
            a.id == r.id
                || matches!(
                    (
                        const_signed(func, def, def_count, a),
                        const_signed(func, def, def_count, r),
                    ),
                    (Some(ka), Some(kr)) if ka == kr
                )
        }
        CmpRhs::Imm(k) => const_signed(func, def, def_count, a) == Some(k),
    };
    if t.id == x.id && matches_rhs(f) {
        // (x cc y) ? x : y — GT/GE selects the larger => MAX; LT/LE => MIN.
        Some((is_lt, x, f))
    } else if matches_rhs(t) && f.id == x.id {
        // (x cc y) ? y : x — GT/GE selects the smaller => MIN; LT/LE => MAX.
        Some((is_gt, x, t))
    } else {
        None
    }
}

/// One resolved diamond arm: a plain leaf value, or a NESTED single min/max
/// select (the clamp's inner diamond), each with the arm's TAIL block (the
/// block whose `B` enters the join).
enum ArmVal {
    Leaf(VReg),
    Nested {
        is_min: bool,
        a: VReg,
        b: VReg,
        inner: InnerSel,
    },
}

/// Resolve one arm of a select region rooted at `split`. Returns
/// `(dest, value, join, tail, consumed, dest_def)`.
///
/// * MOV arm: the block is exactly `[copy(d, s); B(j)]`.
/// * NESTED arm (depth 1, the clamp): the block is a PURE compare block
///   (exactly `Cmp;BCond;B`, both targets in body) whose two targets are MOV
///   arms agreeing on an inner dest `d2` and inner join `j2`; `j2`'s preds are
///   exactly those two arms and `j2` is itself a MOV arm forwarding `d2` into
///   the outer dest (`[copy(d, d2); B(j)]`). The inner select MUST match a
///   signed min/max (fail-closed) — an arbitrary inner select has no SMIN/SMAX
///   lowering.
fn resolve_select_arm(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    def_count: &HashMap<u32, u32>,
    body: &HashSet<BlockId>,
    split: BlockId,
    blk: BlockId,
) -> Option<(VReg, ArmVal, BlockId, BlockId, Vec<BlockId>, InstId)> {
    if !preds_exactly(func, blk, &[split]) {
        return None;
    }
    if let Some((d, s, j, copy_id)) = mov_arm(func, blk) {
        return Some((d, ArmVal::Leaf(s), j, blk, vec![blk], copy_id));
    }
    // Nested inner select: `blk` must be a PURE compare block (no other insts —
    // nothing may redefine the outer compare's operands between the two
    // compares, and a pure `Cmp;BCond;B` block writes no register).
    if func.block(blk).insts.len() != 3 {
        return None;
    }
    let (x2, rhs2, cc2, t2, f2) = select_split(func, blk, body)?;
    if !preds_exactly(func, t2, &[blk]) || !preds_exactly(func, f2, &[blk]) || t2 == f2 {
        return None;
    }
    let (d2_t, tv2, j2_t, copy_t) = mov_arm(func, t2)?;
    let (d2_f, fv2, j2_f, copy_f) = mov_arm(func, f2)?;
    if d2_t != d2_f || j2_t != j2_f {
        return None;
    }
    let (d2, j2) = (d2_t, j2_t);
    if !body.contains(&j2) || !preds_exactly(func, j2, &[t2, f2]) {
        return None;
    }
    // The inner join forwards the inner dest into the outer dest and enters the
    // outer join: `[copy(d, d2); B(j)]`.
    let (d, fwd_src, j, fwd_id) = mov_arm(func, j2)?;
    if fwd_src != d2 {
        return None;
    }
    let (is_min, a, b) = match_select_minmax(func, def, def_count, cc2, x2, rhs2, tv2, fv2)?;
    // Anti-cycle: the inner dest must not appear among its own operands (a
    // multi-def register is only ever modeled through `Recognized::selects`).
    if [x2.id, a.id, b.id].contains(&d2.id) || d.id == d2.id {
        return None;
    }
    Some((
        d,
        ArmVal::Nested {
            is_min,
            a,
            b,
            inner: InnerSel {
                dest: d2,
                def_insts: [copy_t, copy_f],
                forward_use: fwd_id,
            },
        },
        j,
        j2,
        vec![blk, t2, f2, j2],
        fwd_id,
    ))
}

/// Recognize a whole select-diamond REGION at chain block `split` and map it to
/// a [`SelExpr`] — a signed single min/max, or the two-sided constant CLAMP.
///
/// ## Clamp soundness — the composition identities
///
/// The nested source `if v>HI {HI} else if v<LO {LO} else {v}` does NOT make
/// each branch an independent min/max (the outer else-value is the INNER select,
/// not `v`), so the composition is proven as a whole. For all i32 `v` and
/// constants `LO <=s HI`, `clamp(v) = smin(smax(v, LO), HI)` satisfies (3-case
/// split): `v >s HI => smax(v,LO) = v` (since `v > HI >= LO`) `=> smin = HI`;
/// `v <s LO => smax = LO, smin(LO, HI) = LO` (since `LO <= HI`); otherwise
/// `smax = v, smin = v`. The FOUR accepted diamond polarities each equal that
/// clamp — case-checked against the scalar select (`K1` = the outer compared
/// constant, `K2` = the inner min/max constant, `x` the clamped value):
///
/// 1. `x >s K1 ? K1 : smax(x,K2)`, `K2 <= K1` == `clamp(x, K2, K1)`:
///    `x > K1` => both `K1` (smax passes `x` through, smin caps); `x <= K1` =>
///    both `smax(x,K2)` (it is `<= K1`: both `x` and `K2` are).
/// 2. `x <s K1 ? K1 : smin(x,K2)`, `K1 <= K2` == `clamp(x, K1, K2)`:
///    `x < K1` => both `K1`; `x >= K1` => both `smin(x,K2)` (it is `>= K1`).
/// 3. `x >s K1 ? smin(x,K2) : K1`, `K1 <= K2` == `clamp(x, K1, K2)`:
///    `x > K1` => both `smin(x,K2)` (`>= K1`: both operands are); `x <= K1` =>
///    both `K1` (`smax(smin(x,K2),K1)`: `smin(x,K2) <= x <= K1`).
/// 4. `x <s K1 ? smax(x,K2) : K1`, `K2 <= K1` == `clamp(x, K2, K1)`:
///    `x < K1` => both `smax(x,K2)` (`<= K1`: both operands are); `x >= K1` =>
///    both `K1` (`smax(x,K2) = x >= K1`, smin caps to `K1`).
///
/// The bound inequality is checked on the DECODED constants (fail-closed when
/// either is not a provable single-def `Movz`/`Movn`); a crossed clamp
/// (`LO > HI`) does NOT equal the min/max composition and BAILS. GE/LE variants
/// of the outer compare are accepted: ties pick the compared constant on one
/// side and an expression EQUAL to it on the other (case-checked in the
/// identities above with `>=`/`<=` boundaries included).
///
/// Everything else — both arms nested, an inner select over a DIFFERENT value
/// than the outer compare's LHS, unsigned/equality conditions, unmatched arm
/// values — BAILS, which bails the whole loop (fail-closed to scalar).
fn recognize_select_region(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    def_count: &HashMap<u32, u32>,
    body: &HashSet<BlockId>,
    split: BlockId,
) -> Option<SelRegion> {
    let (x, rhs, cc, t_blk, f_blk) = select_split(func, split, body)?;
    // NORMALIZE a constant-on-the-left compare: `if K < v` lowers to
    // `Cmp(K_reg, v)`, but the clamp matcher needs `x` to be the DATA value.
    // `K cc v ⟺ v cc' K` with the exact mirror GT<->LT / GE<->LE (total for
    // all i32 values); the select arms are untouched. Only applied when the
    // LHS is a provable constant and the RHS register is not (both-constant
    // splits are left alone and simply fail the matchers — fail-closed).
    let (x, rhs, cc) = match rhs {
        CmpRhs::Reg(r)
            if const_signed(func, def, def_count, x).is_some()
                && const_signed(func, def, def_count, r).is_none() =>
        {
            let mirrored = match cc {
                CC_GT => CC_LT,
                CC_GE => CC_LE,
                CC_LT => CC_GT,
                CC_LE => CC_GE,
                _ => cc,
            };
            (r, CmpRhs::Reg(x), mirrored)
        }
        _ => (x, rhs, cc),
    };
    let is_gt = cc == CC_GT || cc == CC_GE;
    let is_lt = cc == CC_LT || cc == CC_LE;
    if !is_gt && !is_lt {
        return None;
    }
    let (d_t, tv, j_t, tail_t, consumed_t, def_t) =
        resolve_select_arm(func, def, def_count, body, split, t_blk)?;
    let (d_f, fv, j_f, tail_f, consumed_f, def_f) =
        resolve_select_arm(func, def, def_count, body, split, f_blk)?;
    if d_t != d_f || j_t != j_f {
        return None;
    }
    let (dest, join) = (d_t, j_t);
    if !body.contains(&join) || join == split {
        return None;
    }
    // The join is entered EXACTLY by the two arm tails: no third path can reach
    // the continuation without executing an arm copy of `dest`.
    if !preds_exactly(func, join, &[tail_t, tail_f]) {
        return None;
    }
    // The signed constant of the outer compare bound (for the clamp inequality),
    // when decodable.
    let rhs_const = |leaf: VReg| -> Option<i64> {
        match rhs {
            CmpRhs::Imm(k) => Some(k),
            CmpRhs::Reg(_) => const_signed(func, def, def_count, leaf),
        }
    };
    let matches_rhs = |a: VReg| match rhs {
        CmpRhs::Reg(r) => {
            a.id == r.id
                || matches!(
                    (
                        const_signed(func, def, def_count, a),
                        const_signed(func, def, def_count, r),
                    ),
                    (Some(ka), Some(kr)) if ka == kr
                )
        }
        CmpRhs::Imm(k) => const_signed(func, def, def_count, a) == Some(k),
    };
    // The inner min/max of a clamp must be over the SAME value `x` the outer
    // compare tests, with a decodable constant on the other side.
    let inner_of = |a: VReg, b: VReg| -> Option<(VReg, i64)> {
        if a.id == x.id {
            Some((b, const_signed(func, def, def_count, b)?))
        } else if b.id == x.id {
            Some((a, const_signed(func, def, def_count, a)?))
        } else {
            None
        }
    };
    let (expr, inner, dest_def_insts) = match (tv, fv) {
        (ArmVal::Leaf(t), ArmVal::Leaf(f)) => {
            let (is_min, a, b) = match_select_minmax(func, def, def_count, cc, x, rhs, t, f)?;
            (SelExpr::MinMax { is_min, a, b }, None, [def_t, def_f])
        }
        // Forms 1 & 2: constant on the TRUE side, nested min/max on the FALSE side.
        (
            ArmVal::Leaf(t),
            ArmVal::Nested {
                is_min,
                a,
                b,
                inner,
            },
        ) => {
            if !matches_rhs(t) {
                return None;
            }
            let k1 = rhs_const(t)?;
            let (k2_reg, k2) = inner_of(a, b)?;
            let expr = if is_gt && !is_min && k2 <= k1 {
                // Form 1: x > K1 ? K1 : smax(x, K2) == clamp(x, K2, K1).
                SelExpr::Clamp {
                    v: x,
                    lo: k2_reg,
                    hi: t,
                }
            } else if is_lt && is_min && k1 <= k2 {
                // Form 2: x < K1 ? K1 : smin(x, K2) == clamp(x, K1, K2).
                SelExpr::Clamp {
                    v: x,
                    lo: t,
                    hi: k2_reg,
                }
            } else {
                return None; // wrong polarity / crossed bounds: NOT a clamp
            };
            (expr, Some(inner), [def_t, def_f])
        }
        // Forms 3 & 4: nested min/max on the TRUE side, constant on the FALSE side.
        (
            ArmVal::Nested {
                is_min,
                a,
                b,
                inner,
            },
            ArmVal::Leaf(f),
        ) => {
            if !matches_rhs(f) {
                return None;
            }
            let k1 = rhs_const(f)?;
            let (k2_reg, k2) = inner_of(a, b)?;
            let expr = if is_gt && is_min && k1 <= k2 {
                // Form 3: x > K1 ? smin(x, K2) : K1 == clamp(x, K1, K2).
                SelExpr::Clamp {
                    v: x,
                    lo: f,
                    hi: k2_reg,
                }
            } else if is_lt && !is_min && k2 <= k1 {
                // Form 4: x < K1 ? smax(x, K2) : K1 == clamp(x, K2, K1).
                SelExpr::Clamp {
                    v: x,
                    lo: k2_reg,
                    hi: f,
                }
            } else {
                return None; // wrong polarity / crossed bounds: NOT a clamp
            };
            (expr, Some(inner), [def_t, def_f])
        }
        (ArmVal::Nested { .. }, ArmVal::Nested { .. }) => return None,
    };
    // Anti-cycle: the merged dest must not appear among the expression's
    // operands or the compare (a multi-def register is only modeled through
    // `Recognized::selects`, never through the def map).
    let operand_ids: Vec<u32> = match &expr {
        SelExpr::MinMax { a, b, .. } => vec![x.id, a.id, b.id],
        SelExpr::Clamp { v, lo, hi } => vec![x.id, v.id, lo.id, hi.id],
    };
    if operand_ids.contains(&dest.id) {
        return None;
    }
    if let Some(i) = &inner
        && (operand_ids.contains(&i.dest.id) || i.dest.id == dest.id)
    {
        return None;
    }
    let mut consumed = consumed_t;
    consumed.extend(consumed_f);
    Some(SelRegion {
        dest,
        expr,
        join,
        consumed,
        dest_def_insts,
        inner,
    })
}

/// ITERATION-LOCALITY gate for the CHAIN shape.
///
/// The map transform's additive argument needs every scalar register the body
/// defines (other than the induction) to be a PER-ITERATION TEMPORARY: the
/// vector loop replaces whole iterations without executing the scalar body's
/// register updates, so any register carrying state ACROSS iterations (a stealth
/// accumulator `acc = acc + g(i)` hiding in a mid-chain block) or OUT of the
/// loop would end up wrong. This gate proves locality structurally, per register
/// `r` defined by a loop instruction (`r != iv`, which carries the iteration by
/// design and is stepped faithfully by the vector latch):
///
/// * RECOGNIZED SELECT DESTS (multi-def by construction — one def per diamond
///   arm): the defs must be EXACTLY the region's two arm copies, every use must
///   sit at a chain position AT/AFTER the diamond's join (on the single walked
///   path the join dominates all later blocks, so every use sees THIS
///   iteration's merged value — a use before the split would read the PREVIOUS
///   iteration's), and nothing outside the loop may touch `r`. An INNER select
///   dest is stricter: its only use anywhere is the join's forwarding copy.
/// * EVERYTHING ELSE: exactly ONE def in the loop, NO def or use outside the
///   loop, no self-use in the defining instruction, and every use STRICTLY
///   AFTER the def in chain order — i.e. plain forward SSA dataflow within one
///   iteration. A use at/before the def is a back-edge-carried read (the
///   accumulator shape) and BAILS; a use outside the loop is live-out state and
///   BAILS. Fail-closed: anything unclassifiable bails the whole loop.
fn validate_chain_locality(
    func: &MachFunction,
    body: &HashSet<BlockId>,
    order: &HashMap<BlockId, usize>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    regions: &[SelRegion],
) -> bool {
    // Chain position of every loop instruction: (block order, index in block).
    let mut pos: HashMap<InstId, (usize, usize)> = HashMap::new();
    for (&blk, &bo) in order {
        for (io, &id) in func.block(blk).insts.iter().enumerate() {
            pos.insert(id, (bo, io));
        }
    }
    // In-loop defs per register id.
    let mut defs: HashMap<u32, Vec<InstId>> = HashMap::new();
    for &blk in body {
        for &id in &func.block(blk).insts {
            let inst = func.inst(id);
            if inst.produces_value()
                && let Some(MachOperand::VReg(v)) = inst.operands.first()
            {
                defs.entry(v.id).or_default().push(id);
            }
        }
    }
    // Every register id TOUCHED (def or use) by any live instruction OUTSIDE the
    // loop body.
    let mut outside_touch: HashSet<u32> = HashSet::new();
    for block in &func.blocks {
        for &id in &block.insts {
            if loop_insts.contains(&id) {
                continue;
            }
            for op in &func.inst(id).operands {
                if let MachOperand::VReg(v) = op {
                    outside_touch.insert(v.id);
                }
            }
        }
    }
    // Select-region bookkeeping.
    let mut outer_sel: HashMap<u32, (usize, [InstId; 2])> = HashMap::new();
    let mut inner_sel: HashMap<u32, ([InstId; 2], InstId)> = HashMap::new();
    for region in regions {
        let Some(&join_ord) = order.get(&region.join) else {
            return false;
        };
        outer_sel.insert(region.dest.id, (join_ord, region.dest_def_insts));
        if let Some(inner) = &region.inner {
            inner_sel.insert(inner.dest.id, (inner.def_insts, inner.forward_use));
        }
    }
    // Uses of `rid` among the loop instructions, excluding the given def insts
    // (an instruction that re-defines `rid` would itself be in the def list).
    let uses_of = |rid: u32, def_insts: &[InstId]| -> Vec<InstId> {
        let mut uses = Vec::new();
        for &blk in body {
            for &id in &func.block(blk).insts {
                if def_insts.contains(&id) {
                    continue;
                }
                if func
                    .inst(id)
                    .operands
                    .iter()
                    .any(|op| matches!(op, MachOperand::VReg(v) if v.id == rid))
                {
                    uses.push(id);
                }
            }
        }
        uses
    };
    for (&rid, dlist) in &defs {
        if rid == iv.id {
            continue; // the induction: stepped faithfully by the vector latch
        }
        if outside_touch.contains(&rid) {
            return false; // state visible outside the loop — not a temporary
        }
        if let Some(&(join_ord, def_insts)) = outer_sel.get(&rid) {
            if dlist.len() != 2 || !dlist.iter().all(|d| def_insts.contains(d)) {
                return false; // a def besides the two arm copies
            }
            for use_id in uses_of(rid, &def_insts) {
                match pos.get(&use_id) {
                    Some(&(bo, _)) if bo >= join_ord => {}
                    _ => return false, // used before the merge — prior-iteration value
                }
            }
        } else if let Some(&(def_insts, forward_use)) = inner_sel.get(&rid) {
            if dlist.len() != 2 || !dlist.iter().all(|d| def_insts.contains(d)) {
                return false;
            }
            // The inner dest's ONLY use is the join's forwarding copy.
            if uses_of(rid, &def_insts) != vec![forward_use] {
                return false;
            }
        } else {
            if dlist.len() != 1 {
                return false; // multi-def non-select temp: ambiguous dataflow
            }
            let def_id = dlist[0];
            let Some(&def_pos) = pos.get(&def_id) else {
                return false;
            };
            // No self-use: `r = op(r, ...)` reads the PREVIOUS iteration's value
            // on every pass but the first — loop-carried state.
            if func.inst(def_id).operands[1..]
                .iter()
                .any(|op| matches!(op, MachOperand::VReg(v) if v.id == rid))
            {
                return false;
            }
            for use_id in uses_of(rid, &[def_id]) {
                match pos.get(&use_id) {
                    Some(&use_pos) if use_pos > def_pos => {}
                    _ => return false, // use at/before the def — back-edge carried
                }
            }
        }
    }
    true
}

/// True iff `v` reaches `iv` through value-preserving copy links
/// (`MovR`/`Copy`/`AddRI(_,0)`) — i.e. `v` IS the induction or a copy of it.
/// Bounded walk; matches `iv` EXACTLY and never strips PAST it, so it does not
/// follow the latch writeback `iv = iv+1` and therefore never mistakes a distinct
/// `iv+1` stencil index for `iv` (soundness-critical: shifted reads must BAIL).
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

/// Follow value-preserving copy chains (`MovR`/`Copy`/`AddRI(_,0)`) to the
/// underlying value (bounded). Used only on single-def limit registers, never on
/// the multi-def induction.
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

/// Two bounds/limit registers agree iff they are the SAME register (after
/// value-preserving copy stripping) or resolve to the SAME 16-bit constant.
fn bound_agrees(func: &MachFunction, def: &HashMap<u32, InstId>, a: VReg, b: VReg) -> bool {
    if strip_copies(func, def, a) == strip_copies(func, def, b) {
        return true;
    }
    matches!(
        (const_value(func, def, a), const_value(func, def, b)),
        (Some(x), Some(y)) if x == y
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
        if header == latch || body.is_empty() || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // Whitelist every opcode across EVERY body block — no call/div/atomic/
        // second store/etc. A strict 2-block {header, latch} map has exactly those
        // two blocks; a bounds-guarded test-first `while i<N` map splits its
        // straight-line body across a LINEAR CHAIN of blocks joined by in-loop
        // `iv <u N` bounds-check diamonds (all still whitelisted CmpRR/BCond/B),
        // recognized by `recognize_forward_chain`.
        let mut loop_insts = HashSet::new();
        for &b in body {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    nm_bail!(
                        "G1 opcode not allowed in body: b{} {:?}",
                        b.0,
                        func.inst(id).opcode
                    );
                }
                loop_insts.insert(id);
            }
        }

        // Shape dispatch. The classic strict 2-block loop (native trust_ir /
        // clang-rotated forward|reverse) goes through `recognize_two_block`;
        // anything else — including the FORWARD bounds-guarded `while i<N` chain
        // the bridge emits for `for i in 0..N { a[i] = TERM }` over fixed-size
        // arrays — goes through `recognize_forward_chain`. Both build the shape
        // then run the SHARED store/term/alias tail (`recognize_tail`).
        if body.len() == 2
            && let Some(rec) =
                Self::recognize_two_block(func, dom, header, latch, body, &loop_insts)
        {
            return Some(rec);
        }
        nm_trace(format_args!(
            "G2 two-block path declined (body.len={}), trying forward-chain",
            body.len()
        ));
        Self::recognize_forward_chain(func, dom, header, latch, body, &loop_insts)
    }

    /// Recognize the classic strict 2-block `{header, latch}` map loop (native
    /// trust_ir forward/reverse or clang-rotated forward/reverse). This is the
    /// ORIGINAL recognizer, unchanged except that the shared store/term/alias tail
    /// is now factored into [`Recognized::recognize_tail`].
    fn recognize_two_block(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
        loop_insts: &HashSet<InstId>,
    ) -> Option<Self> {
        let def = build_def_map(func);

        // (R6) header preds are exactly {latch, guard}; guard has one pred.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            nm_bail!(
                "G3 header preds not {{latch,guard}}: preds={:?} latch=b{}",
                hpreds.iter().map(|b| b.0).collect::<Vec<_>>(),
                latch.0
            );
        }
        let guard = *hpreds.iter().find(|&&b| b != latch)?;
        let gpreds = &func.block(guard).preds;
        // SHAPE-FRAGILITY FIX (`TCG_NO_NEONMAP_SHARED_PREHEADER` restores the old
        // behaviour). The single-entry `guard` is a requirement of the NATIVE shape
        // ONLY, which splices its vector preamble into the block BEFORE the guard
        // (`preheader`) because the guard itself must survive as the scalar loop's
        // top test. The two ROTATED shapes RE-ROOT onto the guard and overwrite
        // `preheader`/`preheader_term` unread, so for them `gpreds.len() == 1` was
        // never load-bearing — it just happened to hold for the block shape clang
        // -O1/-O2 emits.
        //
        // It stops holding the moment the producer is any good: when clang hoists a
        // loop-invariant entry guard out of an enclosing loop (`-O3` on a nest like
        // `for k { for i { y[i] += x[i] } }`), the inner loop's entry block IS the
        // outer loop's header, which has two predecessors (outer preheader + outer
        // latch) — and a perfectly ordinary `y[i]+=x[i]` stopped vectorizing purely
        // because of that. What the rotated path actually needs is that the guard
        // reach the header on a single edge it may retarget, which `apply` gets from
        // `reroot_term` and the dominance checks in `recognize_tail` — none of which
        // care how many ways control arrives AT the guard. Splicing into a
        // multi-entry guard re-runs the preamble once per entry to the loop, which is
        // exactly the contract the preamble already has.
        if gpreds.len() != 1 && legacy_shared_preheader_gate() {
            nm_bail!(
                "G4 guard b{} has {} preds ({:?}), want exactly 1 [legacy]",
                guard.0,
                gpreds.len(),
                gpreds.iter().map(|b| b.0).collect::<Vec<_>>()
            );
        }
        // `Some` exactly when the classic dedicated-guard shape holds. The NATIVE arm
        // below requires it; the rotated arms never read it.
        let native_entry: Option<(BlockId, InstId)> = if gpreds.len() == 1 {
            let preheader = gpreds[0];
            func.block(preheader)
                .insts
                .iter()
                .rev()
                .find(|&&id| branch_targets(func.inst(id)).contains(&guard))
                .map(|&t| (preheader, t))
        } else {
            None
        };
        // Mutable copies: the ROTATED FORWARD shape RE-ROOTS the vectorizer's block
        // model onto the GUARD (clang inits iv AND computes the bound there, then
        // unconditionally branches to the header). Making the GUARD the vectorizer's
        // preheader lets `apply` splice the vector loop AFTER iv-init and route the
        // vector exit into the HEADER (do-while scalar tail) — with a tail guard for
        // the remainder-0 case. See neon_array for the full rationale.
        //
        // Each of the three shape arms below (native / rotated-forward /
        // rotated-reverse) assigns all three or bails, so there is no default: the
        // NATIVE arm takes them from `native_entry`, the rotated arms re-root onto
        // the guard. (Leaving them uninitialized is what lets the compiler check
        // that claim — it was previously masked by a dead initializer.)
        let vec_preheader: BlockId;
        let vec_guard: BlockId;
        let vec_preheader_term: Option<InstId>;
        // ROTATED FORWARD only: the loop's true exit block (set in the rotated branch).
        let mut rotated_exit: Option<BlockId> = None;
        // ROTATED REVERSE (clang -O1) only: the array-index register `iv-1` and the
        // i64 initial-iv (= element count `n`). Set in the reverse-rotated branch.
        let mut rev_index: Option<VReg> = None;
        let mut rev_count: Option<VReg> = None;

        // (R2) The exit test + loop-carried writeback. Two loop SHAPES:
        //  * NATIVE (trust_ir): the LATCH holds the exit branch to the header and
        //    its compare — forward `CmpRR(iv,bound); BCond(LT)` or reverse `iv>=0;
        //    BCond(GE)`.
        //  * ROTATED (clang -O1): the latch is the SOLE iv writeback + `B->header`;
        //    the exit test lives at the end of the HEADER. FORWARD is
        //    `CmpRR(iv+1,bound); BCond(EQ|GE)->exit`; REVERSE is
        //    `CmpRI(iv,1); BCond(GT)->latch` with the index folded as `iv-1`.
        // The single loop-carried writeback (the induction) is in the latch in
        // BOTH shapes.
        let latch_insts_v = func.block(latch).insts.clone();
        let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
        for &id in &latch_insts_v {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                writebacks.push((d, s));
            }
        }
        if writebacks.len() != 1 {
            return None;
        }
        let (wb_dst, iv_src) = writebacks[0];

        let latch_exit_bcond = latch_insts_v
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::BCond && branch_targets(i).contains(&header));

        let (iv, bound, descending) = if let Some(bcond) = latch_exit_bcond {
            // NATIVE shape: the guard survives as the scalar loop's top test, so the
            // vector preamble goes in the block BEFORE it — which must therefore be
            // the guard's SOLE predecessor.
            let Some((preheader, preheader_term)) = native_entry else {
                nm_bail!(
                    "G4 native shape needs a dedicated single-entry guard; b{} has {} preds",
                    guard.0,
                    gpreds.len()
                );
            };
            vec_preheader = preheader;
            vec_guard = guard;
            vec_preheader_term = Some(preheader_term);
            let descending = match imm_of(&bcond.operands[0])? {
                CC_LT => false,
                CC_GE => true,
                _ => return None,
            };
            let cmp = latch_insts_v
                .iter()
                .map(|&id| func.inst(id))
                .rev()
                .find(|i| {
                    i.opcode == AArch64Opcode::CmpRR
                        || (descending && i.opcode == AArch64Opcode::CmpRI)
                })?;
            let iv = vreg_of(&cmp.operands[0])?;
            let bound = if descending {
                match cmp.opcode {
                    AArch64Opcode::CmpRI => {
                        if imm_of(&cmp.operands[1])? != 0 {
                            return None;
                        }
                        iv // placeholder — unused on the descending path
                    }
                    AArch64Opcode::CmpRR => {
                        let z = vreg_of(&cmp.operands[1])?;
                        if const_value(func, &def, z) != Some(0) {
                            return None;
                        }
                        z
                    }
                    _ => return None,
                }
            } else {
                if cmp.opcode != AArch64Opcode::CmpRR {
                    return None;
                }
                vreg_of(&cmp.operands[1])?
            };
            (iv, bound, descending)
        } else {
            // ROTATED shape (clang -O1): latch = the single writeback + `B->header`;
            // the exit test lives at the end of the HEADER. FORWARD (`iv+1==bound`)
            // and REVERSE (`iv > 1`, index `iv-1`) sub-shapes.
            let non_copy: Vec<InstId> = latch_insts_v
                .iter()
                .copied()
                .filter(|&id| copy_like(func.inst(id)).is_none())
                .collect();
            if non_copy.len() != 1 || func.inst(non_copy[0]).opcode != AArch64Opcode::B {
                return None;
            }
            // RE-ROOT onto the guard (where iv is init'd), so the vector loop reads a
            // DEFINED iv and the exit routes to the do-while tail (guarded) not a
            // re-init of iv. See neon_array::recognize.
            let reroot_term = *func
                .block(guard)
                .insts
                .iter()
                .rev()
                .find(|&&id| branch_targets(func.inst(id)).contains(&header))?;
            if is_increment_by_one(func, &def, iv_src, wb_dst) {
                // ROTATED FORWARD `for(i=0;i<n;i++)`.
                let (bound, exit) = recognize_rotated_header_exit(func, header, body, iv_src)?;
                // Widened bound `Uxtw(n)` is guard-defined — substitute the i32 source.
                let bound = ext_source(func, &def, bound).unwrap_or(bound);
                rotated_exit = Some(exit);
                vec_preheader = guard;
                vec_guard = header;
                vec_preheader_term = Some(reroot_term);
                (wb_dst, bound, false)
            } else if is_decrement_by_one(func, &def, iv_src, wb_dst) {
                // ROTATED REVERSE `for(i=n-1;i>=0;i--)`. clang lowers this to a phi
                // `iv` counting the trip-count DOWN from `n` to `1`, folding the
                // decrement and the array index into ONE register: the latch
                // writeback `iv = iv - 1` REUSES the exact `iv-1` value the header
                // uses to address `x[iv-1]`/`y[iv-1]`. So `iv_src` IS the index.
                // The header exit test is `cmp iv, 1; b.gt <latch>` (continue while
                // iv > 1; the last body runs at iv==1 -> index 0). The element COUNT
                // is the loop's initial iv (`uxtw(n)`), recovered from the guard.
                let (exit, init_iv) =
                    recognize_rotated_reverse_header_exit(func, &def, header, guard, body, wb_dst)?;
                // The reverse index register must be an i64 index (clang widens the
                // index to i64; the i32 `.4S` element path uses it directly, MIXED).
                if iv_src.class != RegClass::Gpr64 {
                    return None;
                }
                // Count must dominate the (re-rooted) preheader so the regime-C
                // byte-range guard can materialize `count*elem` there.
                let init_def = *def.get(&init_iv.id)?;
                let init_block = block_of_inst(func, init_def)?;
                if init_iv.class != RegClass::Gpr64 || !dom.dominates(init_block, guard) {
                    return None;
                }
                rotated_exit = Some(exit);
                vec_preheader = guard;
                vec_guard = header;
                vec_preheader_term = Some(reroot_term);
                rev_index = Some(iv_src);
                rev_count = Some(init_iv);
                (wb_dst, wb_dst, true) // bound is a placeholder on the descending path
            } else {
                return None;
            }
        };
        if wb_dst != iv {
            return None;
        }

        // (R3) step: `iv_src = AddRR/AddRI(iv, +1)` forward, or
        // `SubRR/SubRI(iv, 1)` / `AddRI(iv, -1)` reverse.
        let step_ok = if descending {
            is_decrement_by_one(func, &def, iv_src, iv)
        } else {
            is_increment_by_one(func, &def, iv_src, iv)
        };
        if !step_ok {
            return None;
        }

        let mut rec = Recognized {
            guard: vec_guard,
            rotated_exit,
            preheader: vec_preheader,
            preheader_term: vec_preheader_term?,
            iv,
            bound,
            bound_imm: None,
            term: VReg::new(0, RegClass::Gpr32), // filled by recognize_tail
            is_i64: false,                       // filled by recognize_tail
            descending,
            chain: false,
            store_base: VReg::new(0, RegClass::Gpr64), // filled by recognize_tail
            def,
            loop_insts: loop_insts.clone(),
            loads: HashMap::new(),
            bases: Vec::new(),
            inv_leaves: HashSet::new(),
            selects: HashMap::new(),
            def_count: build_def_count(func),
            needs_versioning: false,
            check_bases: Vec::new(),
            rev_index,
            rev_count,
        };
        rec.recognize_tail(func, dom)?;
        Some(rec)
    }

    /// Recognize a FORWARD test-first counted map `for i in 0..N { a[i] = TERM }`
    /// whose body is a LINEAR CHAIN of blocks split by in-loop ARRAY BOUNDS-CHECK
    /// diamonds. The bridge lowers each `a[i]`/`b[i]` access over a fixed-size
    /// array to its OWN `cmp iv, len; b.lo <next>; b <panic>` guard (never elided
    /// to a compact carrier, and never a strict 2-block loop), so the straight-line
    /// map body is spread over several blocks
    /// `header(iv<N?) -> g1 -> g2 -> ... -> latch -> header`, every non-latch block
    /// ending `b.lo` INTO the next in-loop block and `b` OUT to a shared panic/exit
    /// block; the latch is the sole `iv = iv+1` writeback + back-edge. CSE folds
    /// every length/limit to ONE register.
    ///
    /// ## Why this is SOUND (single-N agreement)
    ///
    /// The transform is purely ADDITIVE (see the module docs): `apply` splices a
    /// vector main loop in front of the header and NEVER edits the scalar chain,
    /// which is therefore correct by construction. The only new obligation is that
    /// the vector loop touch only in-bounds memory. We fire ONLY when the
    /// loop-continue limit AND every in-loop bounds-guard limit are the SAME
    /// register `N`, each compared against a copy of the SAME induction `iv`.
    /// Because each guard is precisely the array bounds check `iv <u a.len()`
    /// (panic otherwise), agreeing on ONE `N` proves `N == a.len()` for EVERY array
    /// the body touches. `apply`'s forward header admits a vector block only while
    /// `iv+width-1 < N`, so every vector access lies in `[0, N) = [0, a.len())` —
    /// exactly the region the scalar guards permit — and the untouched scalar chain
    /// finishes the `[V, N)` tail (its own header guard rejects the empty tail, so
    /// no exit routing is needed). Fail-closed on ANY deviation (a guard against a
    /// different limit or a non-`iv` index, a non-`b.lo`/`b` diamond, an edge that
    /// re-enters the body, or a body block off the single header->latch chain).
    ///
    /// FORWARD i32/mixed (`.4S`) only; the aliasing regime (A/B/C) is decided by
    /// the shared tail exactly as for the 2-block shape (distinct arrays take the
    /// regime-C runtime range-disjointness precheck).
    fn recognize_forward_chain(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
        loop_insts: &HashSet<InstId>,
    ) -> Option<Self> {
        let def = build_def_map(func);

        // header preds = {latch, preheader}; the preheader edge branches into it.
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

        // The SINGLE induction writeback lives in the latch: `iv = MovR(iv_src)`
        // with `iv_src = iv + 1`. There is NO exit test in the latch — a
        // test-first while loop keeps the exit in the header guard chain. The
        // latch may hold OTHER value-preserving copies (the bridge moves e.g. a
        // select-diamond's merged value into the store operand with a `MovR`
        // right before the `StrRI`): those are ordinary whitelisted body
        // instructions, constrained like every other one by the ITERATION-
        // LOCALITY gate below — but exactly ONE latch copy may be an induction
        // step (two counters is not this shape).
        let latch_insts = func.block(latch).insts.clone();
        let mut inductions: Vec<VReg> = Vec::new();
        for &id in &latch_insts {
            if let Some((d, s)) = copy_like(func.inst(id))
                && is_increment_by_one(func, &def, s, d)
            {
                inductions.push(d);
            }
        }
        if inductions.len() != 1 {
            return None;
        }
        let iv = inductions[0];
        // The latch's ONLY successor is the header (the back-edge), and its last
        // instruction is that unconditional branch — no guard of its own.
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

        // Walk the chain header -> ... -> latch. Each NON-latch block is EITHER:
        //   * a bounds-guard DIAMOND (two successors) `cmp x, N; b.lo <in-body>;
        //     b <out-of-body>` — the loop-continue (header) and any surviving array
        //     bounds check — with `x` a copy of `iv` and `N` the SAME register
        //     across all diamonds (single-N agreement); or
        //   * a PASS-THROUGH block (one successor, in body) whose array bounds check
        //     was already eliminated by the dominated-guard bounds-check-elim pass
        //     (its `iv < N` guard is dominated by the header's, so the access is
        //     still `iv < N`). Its accesses are the SAME `a[iv]` the scalar loop
        //     performs; the vector loop reads a SUBSET `[0,V) ⊆ [0,N)` of those
        //     indices (same addresses), so it is sound whenever the scalar loop is
        //     — the additive-subset argument the module relies on throughout.
        // The header (walk start) MUST be a diamond so the loop has an exit and the
        // bound register `N` is established. The chain must be a SIMPLE path
        // covering EVERY body block exactly once and ending at the latch. Any
        // surviving `TrapBoundsCheckExact` carriers are validated (index == iv,
        // limit == the constant `N`) by `recognize_tail`.
        let def_count = build_def_count(func);
        let mut bound_reg: Option<VReg> = None;
        let mut bound_imm: Option<i64> = None;
        let mut selects: HashMap<u32, SelExpr> = HashMap::new();
        let mut regions: Vec<SelRegion> = Vec::new();
        // ITERATION order of the chain's blocks (position on the single
        // header->latch path), used by the locality gate below.
        let mut order: HashMap<BlockId, usize> = HashMap::new();
        let mut visited: HashSet<BlockId> = HashSet::new();
        let mut cur = header;
        loop {
            if !body.contains(&cur) || !visited.insert(cur) {
                return None;
            }
            order.insert(cur, order.len());
            if cur == latch {
                break;
            }
            let succs = &func.block(cur).succs;
            let next = if succs.len() == 2 {
                if let Some((x, bnd, t_lo)) = recognize_chain_guard(func, cur, body) {
                    // Bounds-guard diamond: validate index/single-N; continue
                    // in-body. Register and immediate limits AGREE iff they are
                    // provably the same value.
                    if !same_as_iv(func, &def, x, iv) {
                        return None;
                    }
                    match (bnd, bound_reg, bound_imm) {
                        (ChainBound::Reg(n), None, None) => bound_reg = Some(n),
                        (ChainBound::Reg(n), Some(b), None) if bound_agrees(func, &def, b, n) => {}
                        (ChainBound::Reg(n), None, Some(k))
                            if const_value(func, &def, n) == Some(k) => {}
                        (ChainBound::Imm(k), None, None) => bound_imm = Some(k),
                        (ChainBound::Imm(k), Some(b), None)
                            if const_value(func, &def, b) == Some(k) => {}
                        (ChainBound::Imm(k), None, Some(k0)) if k == k0 => {}
                        _ => return None,
                    }
                    t_lo
                } else {
                    let region = recognize_select_region(func, &def, &def_count, body, cur)?;
                    // A min/max/clamp SELECT diamond (both edges stay in-body).
                    // The header must already have established the exit + bound
                    // (a select never exits the loop, so it cannot be first).
                    if bound_reg.is_none() && bound_imm.is_none() {
                        return None;
                    }
                    // Consume the diamond-internal blocks (arms + inner join) as
                    // part of the walked chain; continue at the join. One region
                    // per merged dest, dests never shared with an inner dest.
                    for &b in &region.consumed {
                        if !body.contains(&b) || !visited.insert(b) {
                            return None;
                        }
                        order.insert(b, order.len());
                    }
                    if selects.contains_key(&region.dest.id) {
                        return None;
                    }
                    if let Some(inner) = &region.inner
                        && (selects.contains_key(&inner.dest.id) || inner.dest.id == region.dest.id)
                    {
                        return None;
                    }
                    selects.insert(region.dest.id, region.expr.clone());
                    let join = region.join;
                    regions.push(region);
                    join
                }
            } else if succs.len() == 1 {
                // Pass-through (bounds guard eliminated): flow to the single in-body
                // successor. The header is never a pass-through (it needs the exit
                // diamond), so the bound is already set by the time we reach one.
                if (bound_reg.is_none() && bound_imm.is_none()) || !body.contains(&succs[0]) {
                    return None;
                }
                succs[0]
            } else {
                return None;
            };
            cur = next;
        }
        if visited.len() != body.len() {
            return None; // some body block is not on the header->latch chain
        }
        // ITERATION-LOCALITY gate: every register defined inside the loop other
        // than the induction must be a per-iteration temporary — no hidden
        // loop-carried scalar state may survive, because the vector loop replaces
        // whole iterations WITHOUT executing the scalar body's register updates.
        if !validate_chain_locality(func, body, &order, loop_insts, iv, &regions) {
            return None;
        }
        // There is at least the header's loop-continue guard; an immediate limit
        // leaves `bound` as a placeholder that `apply` re-materializes via Movz.
        let bound = match (bound_reg, bound_imm) {
            (Some(b), None) => b,
            (None, Some(_)) => VReg::new(0, RegClass::Gpr32),
            _ => return None,
        };

        let mut rec = Recognized {
            guard: header,
            rotated_exit: None,
            preheader,
            preheader_term,
            iv,
            bound,
            bound_imm,
            term: VReg::new(0, RegClass::Gpr32), // filled by recognize_tail
            is_i64: false,                       // filled by recognize_tail
            descending: false,
            chain: true,
            store_base: VReg::new(0, RegClass::Gpr64), // filled by recognize_tail
            def,
            loop_insts: loop_insts.clone(),
            loads: HashMap::new(),
            bases: Vec::new(),
            inv_leaves: HashSet::new(),
            selects,
            def_count,
            needs_versioning: false,
            check_bases: Vec::new(),
            rev_index: None,
            rev_count: None,
        };
        rec.recognize_tail(func, dom)?;
        Some(rec)
    }

    /// SHARED tail for both shape recognizers. `self` arrives with the SHAPE fields
    /// set (guard/preheader/preheader_term/iv/bound/descending/chain/def/loop_insts/
    /// rotated_exit/rev_*) and the term/is_i64/store_base/loads/bases/inv_leaves/
    /// versioning fields as placeholders. This recognizes the single output store
    /// and its per-lane term, picks the element/index width, and decides the
    /// aliasing regime — filling those fields or BAILING (fail-closed).
    fn recognize_tail(&mut self, func: &MachFunction, dom: &DomTree) -> Option<()> {
        // (R_store) EXACTLY ONE store in the body — the output `a[i]`.
        let mut stores: Vec<InstId> = self
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
        let term = vreg_of(&store.operands[0])?; // stored value (map term)
        let store_addr = vreg_of(&store.operands[1])?;
        self.term = term;

        // Register width selects the lowering path. The ELEMENT width is the
        // stored-value (`term`) width — `Gpr32` ⇒ the `.4S` i32 path, `Gpr64` ⇒
        // the `.2D` i64 path (no multiply). The induction may be WIDER than the
        // element (MIXED i64-index / i32-element): the i64 iv is used DIRECTLY in
        // `base + iv*elem` and stays i32-range, so the i32 `.4S` apply path `Sxtw`s
        // it faithfully. Only these exact (iv, term) width pairs are recognized.
        self.is_i64 = match (self.iv.class, term.class) {
            (RegClass::Gpr32, RegClass::Gpr32) => false,
            (RegClass::Gpr64, RegClass::Gpr64) => true,
            (RegClass::Gpr64, RegClass::Gpr32) => false,
            _ => return None,
        };
        // Forward: the (variable) bound must be loop-invariant (its def dominates
        // the preheader, so `apply` can `Sxtw` it for the guard). Its class must
        // match the ELEMENT width (the pure-i32 / `ext_source`-recovered MIXED
        // case), OR — for the bounds-guarded `while i<N` CHAIN, whose loop-continue
        // compares the possibly-i64 iv DIRECTLY against an i64 length register —
        // the INDEX (iv) width. `apply` `Sxtw`s the bound either way (`SXTW` reads
        // the low 32 bits, exact for a non-negative i32-range length), so a Gpr64
        // length is faithful. Reverse: the "bound" is a constant-0 placeholder.
        if !self.descending && self.bound_imm.is_none() {
            if self.bound.class != term.class && !(self.chain && self.bound.class == self.iv.class)
            {
                return None;
            }
            let bound_def = *self.def.get(&self.bound.id)?;
            let bound_block = block_of_inst(func, bound_def)?;
            if !dom.dominates(bound_block, self.preheader) {
                return None;
            }
        }
        // An IMMEDIATE chain bound needs no invariance/width check: `apply`
        // materializes the non-negative 12-bit constant with a preheader Movz.

        // SOUNDNESS: the vector loop is entered from the (possibly re-rooted)
        // preheader; iv MUST be defined on that edge (fail-closed to scalar else).
        if !iv_def_dominates_preheader(func, dom, self.iv, self.preheader) {
            return None;
        }

        // SINGLE-N carrier agreement (mirrors `neon_bytesum`). Every surviving
        // `TrapBoundsCheckExact [_, index, Imm(limit)]` in the body must check the
        // SAME induction at index `iv` against a `limit` EQUAL to the constant loop
        // bound `N` — i.e. `loop-bound == every carrier limit == the array length`.
        // This proves the vectorized `[0,N)` range is entirely in bounds, so the
        // carrier is subsumed and the (carrier-free) vector loop reads only memory
        // the scalar loop also reads. A carrier over a different index/limit, or a
        // non-constant bound, BAILS (fail-closed). No carriers => vacuously true.
        for &id in &self.loop_insts {
            let inst = func.inst(id);
            if inst.opcode != AArch64Opcode::TrapBoundsCheckExact {
                continue;
            }
            let index = inst.operands.get(1).and_then(vreg_of)?;
            let limit = inst.operands.get(2).and_then(imm_of)?;
            let bound_const = self
                .bound_imm
                .or_else(|| const_value(func, &self.def, self.bound));
            if !same_as_iv(func, &self.def, index, self.iv) || bound_const != Some(limit) {
                return None;
            }
        }

        // Store address must be `a[i] = base + <idx>*elem`, base loop-invariant.
        let store_base = self.resolve_ai_base(func, dom, store_addr)?;
        self.store_base = store_base;

        // (R_term) The stored value must be lowerable per-lane: every reachable
        // leaf is a recognized `x[i]` load (same index) / 16-bit constant /
        // loop-invariant scalar — NOT the induction. Populates loads/bases/inv_leaves.
        let mut seen = HashSet::new();
        if !self.node_ok(func, dom, term, &mut seen) {
            return None;
        }

        // (R_alias) SOUNDNESS gate — three mutually-exclusive, independently-sound
        // regimes (see the module docs):
        //   (A) SINGLE-ARRAY IN-PLACE — no `noalias` needed (only the store base is
        //       ever accessed, read-then-write per index).
        //   (B) MULTI-POINTER STATIC `noalias` — distinct proven-`noalias` bases.
        //   (C) RUNTIME ALIAS VERSIONING — a byte-range disjointness precheck.
        let noalias: HashSet<u32> =
            if trust_cg_lower::guard_evidence::validator_guard_replay_authority_available()
                || cfg!(test)
            {
                func.noalias_params.iter().copied().collect()
            } else {
                HashSet::new()
            };

        // Regime (A) predicate: every recognized load base is the store base AND
        // there is no *unrecognized* load in the body (check every `LdrRI`).
        let only_store_base = self.bases.iter().all(|b| b.id == store_base.id);
        let loads = &self.loads;
        let no_foreign_load = self.loop_insts.iter().all(|&id| {
            let inst = func.inst(id);
            if inst.opcode != AArch64Opcode::LdrRI {
                return true;
            }
            match inst.operands.first() {
                Some(MachOperand::VReg(v)) => loads.contains_key(&v.id),
                _ => false,
            }
        });
        let single_array_in_place = only_store_base && no_foreign_load;

        if !single_array_in_place && !self.regime_b_static_disjoint(func, &noalias, store_base) {
            // Regime (C): RUNTIME ALIAS VERSIONING. `apply` emits a byte-range
            // disjointness precheck comparing the store range `[a, a+n*elem)`
            // against each distinct input range and takes the vector loop ONLY when
            // provably disjoint, else the untouched scalar loop. Restricted to
            // FORWARD i32 (`.4S`) with no foreign load (the CHAIN shape qualifies:
            // forward, i32/mixed, every load range-checkable). ROTATED REVERSE
            // versions via `rev_count`; NATIVE reverse fail-closes.
            if self.is_i64 || !no_foreign_load {
                return None;
            }
            if self.descending && (self.rotated_exit.is_none() || self.rev_count.is_none()) {
                return None;
            }
            let mut check_bases: Vec<VReg> = Vec::new();
            for b in &self.bases {
                if b.id == store_base.id {
                    continue; // in-place read of the SAME array at same index
                }
                if !check_bases.iter().any(|c| c.id == b.id) {
                    check_bases.push(*b);
                }
            }
            if check_bases.is_empty() {
                return None; // no distinct input to disambiguate — fail closed
            }
            self.needs_versioning = true;
            self.check_bases = check_bases;
        }
        // Regime (A) needs no aliasing proof — one array, read-then-write per
        // index — so it falls through and vectorizes.
        Some(())
    }

    /// Regime (B): try to prove multi-pointer disjointness STATICALLY via the
    /// `noalias` (restrict) contract. Returns `true` iff proven (no runtime guard
    /// needed). A `false` result means "not statically provable" — the caller may
    /// fall back to regime (C) runtime versioning. Pure (never mutates `self`).
    fn regime_b_static_disjoint(
        &self,
        func: &MachFunction,
        noalias: &HashSet<u32>,
        store_base: VReg,
    ) -> bool {
        let Some(store_root) = self.underlying_noalias_param(func, noalias, store_base) else {
            return false;
        };
        for b in &self.bases {
            if b.id == store_base.id {
                continue; // in-place read of the SAME array at the same index
            }
            let Some(b_root) = self.underlying_noalias_param(func, noalias, *b) else {
                return false;
            };
            if b_root.id == store_root.id {
                // Same underlying array via a DIFFERENT derived pointer: the two
                // derived offsets are not proven disjoint statically.
                return false;
            }
        }
        true
    }

    /// Recognize an `a[i]` address `base + idx*elem` and return its
    /// loop-invariant `base`. The address must be `Madd(idx, k, base)` (any
    /// factor order) with `idx = Sxtw(iv)`/`k = 4` (i32) or `idx = iv`
    /// directly/`k = 8` (i64 — the induction is already 64-bit).
    fn resolve_ai_base(&self, func: &MachFunction, dom: &DomTree, addr: VReg) -> Option<VReg> {
        let elem_bytes = if self.is_i64 {
            ELEM_BYTES_I64
        } else {
            ELEM_BYTES
        };
        let madd = func.inst(*self.def.get(&addr.id)?);
        if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
            return None;
        }
        let f1 = vreg_of(&madd.operands[1])?;
        let f2 = vreg_of(&madd.operands[2])?;
        let base = vreg_of(&madd.operands[3])?;
        let idx_ok = |factor: VReg| {
            if self.is_i64 {
                // i64: the induction is already 64-bit — accept it or a
                // value-preserving copy of it (`same_as_iv` matches `iv` exactly and
                // never strips past it into `iv+1`, so a stencil `a[i+1]` BAILS).
                same_as_iv(func, &self.def, factor, self.iv)
            } else {
                // i32 (`.4S`) path: index is `Sxtw(iv)` (pure-i32 loop) OR the i64
                // induction used DIRECTLY — or a value-preserving COPY of it (the
                // bounds-guarded `while` chain addresses `a[i]` through a MovR copy
                // of the iv) — (MIXED i32-element / i64-index: sound because the
                // sxtw bounds guard proves the iv stays i32-range and the apply
                // path re-`Sxtw`s it). Mirrors `neon_array::load_base`'s mixed idx.
                // ROTATED REVERSE: the index is the reverse-index register `iv-1`
                // (clang folds the decrement into the addressing index); the
                // descending apply recomputes the block-start index from `iv`
                // itself, so this only pins recognition to the `iv-1` addressing.
                self.is_sext_iv(func, factor)
                    || same_as_iv(func, &self.def, factor, self.iv)
                    || Some(factor) == self.rev_index
            }
        };
        let es_ok = |factor: VReg| const_value(func, &self.def, factor) == Some(elem_bytes);
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

    /// Recognize an array load `dst = *(base + idx*elem)` at offset 0 (the
    /// loop's width) and return its loop-invariant `base`.
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

    /// True iff `v` is `Sxtw(iv)` defined inside the loop body.
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

    /// Resolve a (loop-invariant) base pointer to the `noalias` **param it is
    /// based on**, walking the pointer-derivation chain. A base is either the
    /// param directly, or a row/offset pointer `p + idx*scale` (`Madd`, the gep
    /// lowering) / `p + imm` (`AddRI`) / an identity copy of such. Each step
    /// keeps the SAME underlying object (`result` is *based on* `p`), so the
    /// `noalias` (restrict) disjointness of the ROOT param transfers to every
    /// derived pointer. Returns the root iff it is a proven `noalias` param;
    /// `None` (BAIL) for any unrecognized derivation — fail-closed. Only these
    /// exact base-preserving shapes are traced (an `AddRR` of two registers is
    /// NOT, since either could be the pointer — ambiguous, so BAIL).
    fn underlying_noalias_param(
        &self,
        func: &MachFunction,
        noalias: &HashSet<u32>,
        base: VReg,
    ) -> Option<VReg> {
        let mut cur = base;
        // Bounded walk (chains are short: at most a handful of gep steps).
        for _ in 0..16 {
            if noalias.contains(&cur.id) {
                return Some(cur);
            }
            let inst = func.inst(*self.def.get(&cur.id)?);
            let next = match inst.opcode {
                // `p + idx*scale`: operand[3] is the base pointer `p`.
                AArch64Opcode::Madd if inst.operands.len() == 4 => vreg_of(&inst.operands[3])?,
                // `p + imm`: operand[1] is the base pointer `p`.
                AArch64Opcode::AddRI if inst.operands.len() == 3 => vreg_of(&inst.operands[1])?,
                // identity copy of a base.
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
    /// recognized `i32` array load, a 16-bit constant, or an allowed lane-wise op
    /// over such. The induction is NOT a valid term value. Populates
    /// `self.loads` / `self.bases` as loads are recognized.
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
        // A recognized select-diamond value: signed per-lane min/max/clamp. It is
        // MULTI-def (one def per arm), so it resolves HERE — never through the
        // last-write-wins def map. `.4S` ONLY: baseline NEON has no `.2D`
        // SMIN/SMAX (the encoder rejects them fail-closed), so an i64 map with a
        // select BAILS.
        if let Some(expr) = self.selects.get(&val.id).cloned() {
            if self.is_i64 {
                return false;
            }
            if !seen.insert(val.id) {
                return true;
            }
            return match expr {
                SelExpr::MinMax { a, b, .. } => {
                    self.node_ok(func, dom, a, seen) && self.node_ok(func, dom, b, seen)
                }
                SelExpr::Clamp { v, lo, hi } => {
                    self.node_ok(func, dom, v, seen)
                        && self.node_ok(func, dom, lo, seen)
                        && self.node_ok(func, dom, hi, seen)
                }
            };
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
            // A non-constant value defined OUTSIDE the loop body: accept as a
            // loop-invariant broadcast leaf iff it is a scalar of the loop's
            // width whose def dominates the preheader (so it is available to DUP
            // there — e.g. the matmul row scalar `s = A[i][k]`, loop-invariant in
            // the inner `j` loop). Broadcasting `s` to every lane and computing
            // the per-lane op is bit-exact for integer `+ - * & | ^`. Otherwise
            // BAIL (fail-closed).
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
        // `.2D` has no integer multiply: any multiply in an i64 term BAILS
        // (MUL.2D is UNALLOCATED — nothing sound to emit).
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
                self.node_ok(func, dom, a, seen)
                    && self.node_ok(func, dom, b, seen)
                    && self.node_ok(func, dom, c, seen)
            }
            // CHAIN only: a value-preserving in-loop copy (the bridge moves the
            // merged select value into the store operand with `MovR`). Followed
            // ONLY when the copy dest is SINGLE-def — the chain locality gate
            // proved every non-select in-loop def is; a multi-def dest would
            // make this def-map lookup ambiguous, and the multi-def values we
            // model (induction, select dests) were already handled above.
            MovR | Copy if self.chain && ops.len() == 2 => {
                let Some(s) = vreg_of(&ops[1]) else {
                    return false;
                };
                self.def_count.get(&val.id).copied() == Some(1) && self.node_ok(func, dom, s, seen)
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

/// True iff `v` materializes the constant `-1`. Recognizes `Movn(d, 0)` (move
/// NOT-0 = all-ones = -1, the shape clang uses to add `-1` for a reverse
/// induction). `Movz` cannot express `-1` in its 16-bit unsigned immediate, so
/// only `Movn 0` qualifies here (fail-closed on anything else).
fn is_neg_one(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> bool {
    let Some(&id) = def.get(&v.id) else {
        return false;
    };
    let inst = func.inst(id);
    inst.opcode == AArch64Opcode::Movn
        && inst.operands.len() == 2
        && imm_of(&inst.operands[1]) == Some(0)
}

/// Whether `iv_src` is `iv - 1` (the reverse counted-loop step). Matches
/// `SubRI(iv, 1)`, `SubRR(iv, one_const)`, `AddRI(iv, -1)`, or `AddRR(iv, -1)`
/// (the last being clang -O1's `add iv, negone` where `negone = Movn 0`) — the
/// shapes the layout pass / clang emit for a `for(i=..;i>=0;i--)` induction.
fn is_decrement_by_one(
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
        AArch64Opcode::SubRI => {
            vreg_of(&inst.operands[1]) == Some(iv) && imm_of(&inst.operands[2]) == Some(1)
        }
        AArch64Opcode::SubRR => {
            vreg_of(&inst.operands[1]) == Some(iv)
                && const_value(func, def, vreg_of(&inst.operands[2]).unwrap_or(iv)) == Some(1)
        }
        AArch64Opcode::AddRI => {
            vreg_of(&inst.operands[1]) == Some(iv) && imm_of(&inst.operands[2]) == Some(-1)
        }
        // `iv + (-1)` with `-1` in a register (clang -O1 `Movn 0`). Either operand
        // order (commutative add).
        AArch64Opcode::AddRR => {
            let a = vreg_of(&inst.operands[1]);
            let b = vreg_of(&inst.operands[2]);
            (a == Some(iv) && b.is_some_and(|r| is_neg_one(func, def, r)))
                || (b == Some(iv) && a.is_some_and(|r| is_neg_one(func, def, r)))
        }
        _ => false,
    }
}

/// Recognize the ROTATED REVERSE header exit `cmp iv, 1; b.gt <latch>` (clang
/// -O1's `for(i=n-1;i>=0;i--)`: the phi `iv` counts DOWN from `n` to `1` and the
/// loop CONTINUES to the latch while `iv > 1`). Returns the loop's true EXIT
/// block (the header's out-of-body branch target) and the i64 register holding
/// the INITIAL `iv` value (= the element count `n`, recovered from `iv`'s copy in
/// the guard). Fail-closed on any deviation:
/// * the compare RHS must be exactly the constant `1` — this pins the last body
///   iteration to `iv==1` (index `0`), so the covered index range is `[0, n-1]`
///   and the count equals the initial `iv`; any other constant would mean a
///   different low bound and a wrong count/range.
/// * the continue branch must be `b.gt` targeting a block INSIDE the loop body,
///   with the header's unconditional branch leaving the body (the exit).
/// * `iv`'s initial value must be a copy (`MovR`/`Copy`/`AddRI 0`) of a single i64
///   register defined in the guard (clang's `iv = uxtw(n)`), so the count is a
///   stable, dominating SSA value — not the loop-carried multi-def `iv` itself.
fn recognize_rotated_reverse_header_exit(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    header: BlockId,
    guard: BlockId,
    body: &HashSet<BlockId>,
    iv: VReg,
) -> Option<(BlockId, VReg)> {
    let insts = &func.block(header).insts;
    // The header's continue test: `cmp iv, 1; b.gt <in-body target>`.
    let p = insts.iter().position(|&id| {
        let i = func.inst(id);
        i.opcode == AArch64Opcode::BCond
            && imm_of(&i.operands[0]) == Some(CC_GT)
            && branch_targets(i).iter().any(|t| body.contains(t))
    })?;
    if p < 1 {
        return None;
    }
    let cmp = func.inst(insts[p - 1]);
    let cmp_iv = match cmp.opcode {
        AArch64Opcode::CmpRI => {
            if imm_of(&cmp.operands[1]) != Some(1) {
                return None;
            }
            vreg_of(&cmp.operands[0])?
        }
        AArch64Opcode::CmpRR => {
            if const_value(func, def, vreg_of(&cmp.operands[1])?) != Some(1) {
                return None;
            }
            vreg_of(&cmp.operands[0])?
        }
        _ => return None,
    };
    if cmp_iv != iv {
        return None;
    }
    // The loop's true EXIT is the header's out-of-body branch target.
    let exit = *func
        .block(header)
        .succs
        .iter()
        .find(|t| !body.contains(t))?;
    // Recover the initial iv (= count). `iv` is a multi-def loop-carried register;
    // find its definition inside the GUARD and take the copied source.
    let init_src = func.block(guard).insts.iter().rev().find_map(|&id| {
        let inst = func.inst(id);
        if matches!(inst.operands.first(), Some(MachOperand::VReg(d)) if *d == iv) {
            copy_like(inst).map(|(_, s)| s)
        } else {
            None
        }
    })?;
    Some((exit, init_src))
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
    /// NEON arrangement operand code (`ARR_S4` i32 / `ARR_D2` i64).
    arr_code: i64,
    /// NEON element-size code for scalar broadcasts (`ELEM_S` / `ELEM_D`).
    elem_code: i64,
    /// Register class of the scalar half of a broadcast constant.
    const_class: RegClass,
    /// True on the i64 (`.2D`) path (multiply lowering unreachable).
    is_i64: bool,
    /// True on the CHAIN shape (enables the copy-following / select paths the
    /// chain recognizer validated; the 2-block shapes never populate them).
    chain: bool,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// Load-result vreg id -> base pointer (from recognition).
    loads: HashMap<u32, VReg>,
    /// Recognized select-diamond values (dest id -> min/max/clamp expr).
    selects: HashMap<u32, SelExpr>,
    /// Per-register LIVE def count (single-def gate for copy following).
    def_count: HashMap<u32, u32>,
    /// `(base id, unroll k)` -> the `.4S` vector loaded for that sub-block.
    loaded: HashMap<(u32, usize), VReg>,
    const_cache: HashMap<i64, VReg>,
    /// Loop-invariant scalar leaf vreg ids (broadcast via DUP once each).
    inv_leaves: HashSet<u32>,
    /// Loop-invariant scalar vreg id -> its DUP-broadcast vector (persists across
    /// sub-blocks: the value is the same in every lane and every unroll copy).
    inv_cache: HashMap<u32, VReg>,
    /// Per-sub-block memo of already-lowered scalar values.
    memo: HashMap<u32, VReg>,
}

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    // Per-width parameters: i32 = `.4S` + sxtw guard; i64 = `.2D` + precheck +
    // unsigned guard (see the module docs' i64 section).
    let (vf, elem_bytes, arr_code, elem_code, const_class) = if rec.is_i64 {
        (VF_I64, ELEM_BYTES_I64, ARR_D2, ELEM_D, RegClass::Gpr64)
    } else {
        (VF, ELEM_BYTES, ARR_S4, ELEM_S, RegClass::Gpr32)
    };
    let width = UNROLL as i64 * vf; // lanes per vector iteration (16 / 8)

    // An IMMEDIATE chain bound (`iv <u K`, `K` in `[0, 4095]`): re-materialize
    // `K` once in the preheader — `rec.bound` is a placeholder never read. The
    // value is non-negative and 16-bit, so `Movz` is exact at either width and
    // the guard's `Sxtw` reproduces exactly `K`.
    let bound = if let Some(k) = rec.bound_imm {
        let b = alloc(
            func,
            if rec.is_i64 {
                RegClass::Gpr64
            } else {
                RegClass::Gpr32
            },
        );
        emit_before(
            func,
            rec.preheader_term,
            AArch64Opcode::Movz,
            vec![vreg(b), imm(k)],
        );
        b
    } else {
        rec.bound
    };

    // DESCENDING block-start offset: the block ends at the current TOP index and
    // spans `width` indices, so its start `si = <top> - (width-1)`. NATIVE reverse
    // has top index == `iv` (`si = iv-(width-1)`, guard `iv >= width-1`). ROTATED
    // REVERSE (clang -O1) has top index == `iv-1` (the phi counts to 1, index is
    // `iv-1`), so `si = (iv-1)-(width-1) = iv-width` and the guard is `iv >= width`
    // — i.e. exactly `width-1` shifted by one. Computed from `iv` directly (the
    // apply never uses the scalar `iv-1` index register).
    let desc_blk_off = if rec.rotated_exit.is_some() {
        width
    } else {
        width - 1
    };

    // The i64 forward path needs a signed `n < WIDTH` precheck before its
    // unsigned guard. The descending path needs NO precheck: its guard is the
    // signed `iv >= width-1` (no addition, no overflow, and the loop's upper
    // limit is the initial iv, which only ever decreases), so it is width-uniform.
    let pv = (rec.is_i64 && !rec.descending).then(|| func.create_block());
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    // Regime (C) runtime alias-versioning blocks: a preamble (`av[0]`, computes
    // `n*elem` and the store range end) followed by TWO check blocks per distinct
    // input base (each a single unsigned compare + branch, the canonical
    // `CmpRR;BCond;B` shape). `needs_versioning` is only ever set on the i32 path
    // (no `pv`).
    let av: Vec<BlockId> = if rec.needs_versioning {
        (0..1 + 2 * rec.check_bases.len())
            .map(|_| func.create_block())
            .collect()
    } else {
        Vec::new()
    };
    let mut fresh: Vec<BlockId> = Vec::new();
    fresh.extend(av.iter().copied());
    if let Some(pv) = pv {
        fresh.push(pv);
    }
    fresh.extend([vh, vb, vl, vx]);
    insert_new_blocks_before(func, rec.guard, &fresh);

    // Internal edges among fresh blocks only — touching the original loop's
    // entry is deferred to the COMMIT below so a lowering failure cannot leave a
    // broken CFG.
    if let Some(pv) = pv {
        func.add_edge(pv, vh);
        func.add_edge(pv, rec.guard);
    }
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    // --- Regime (C): emit the runtime range-disjointness precheck. For the store
    // range `[a, a+N)` (`N = count*elem` bytes) and each distinct input range
    // `[x_i, x_i+N)`, the pair `(a, x_i)` is DISJOINT iff `a+N <=u x_i` (store
    // entirely below input) OR `x_i+N <=u a` (input entirely below store) —
    // clang's `a+n<=x || x+n<=a`. If EVERY pair is disjoint the chain reaches the
    // vector loop; the first pair that may overlap branches to the scalar loop
    // (`rec.guard`), which is left completely untouched. Unsigned pointer compares
    // (`LS`), all in i64. The element COUNT is the i32 loop bound `n` (forward
    // only). `N` does not overflow i64: an i32 count sign-extended and shifted by 2
    // stays `< 2^34` (the store range end `a+N` is one-past the array). When the
    // ranges actually overlap the guard routes to the scalar loop, so the vector
    // body NEVER runs on aliasing memory — sound independent of any `noalias`
    // claim. When `count <= 0` the vector header's own in-bounds guard rejects the
    // block regardless of how this precheck routes, so a misroute is still safe.
    // `needs_versioning` is FORWARD i32 only, so the count is the i32 loop bound.
    if rec.needs_versioning {
        let vec_entry = pv.unwrap_or(vh);
        let sh = elem_bytes.trailing_zeros() as i64; // 4 -> 2
        let nbytes = alloc(func, RegClass::Gpr64);
        // Range length `n*elem`. FORWARD: `sxtw(bound) << 2`. ROTATED REVERSE:
        // `rev_count` is ALREADY the i64 count `uxtw(n)` (a non-negative i32-range
        // value), so shift it directly — `rec.bound` is a zero placeholder on the
        // descending path and must NOT be sign-extended for the length.
        if let Some(count) = rec.rev_count {
            emit(
                func,
                av[0],
                AArch64Opcode::LslRI,
                vec![vreg(nbytes), vreg(count), imm(sh)],
            );
        } else {
            let nb = alloc(func, RegClass::Gpr64);
            emit(
                func,
                av[0],
                AArch64Opcode::Sxtw,
                vec![vreg(nb), vreg(bound)],
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
            // Passing either sub-test proves THIS pair disjoint => proceed to the
            // next pair, or (last pair) to the vector loop.
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

    let pre = rec.preheader_term;

    // --- Preheader: materialize the element size (+ the i32 path's
    // sign-extended bound for the sxtw guard).
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(elem_bytes)],
    );

    if rec.descending {
        // --- Descending vector header: enter the body only while a FULL block
        // ending at the current top index is in bounds — i.e. `iv >= desc_blk_off`
        // (signed; `width-1` native / `width` rotated-reverse). No upper check is
        // needed: the vector loop starts at the loop's initial iv and only
        // decrements, so `iv <= init`, and the block is a subset of the indices the
        // scalar loop accesses. The guard is a plain signed compare against a
        // constant (no addition ⇒ no overflow), width-uniform across i32/i64.
        emit(
            func,
            vh,
            AArch64Opcode::CmpRI,
            vec![vreg(rec.iv), imm(desc_blk_off)],
        );
        emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_GE), block(vb)]);
        emit(func, vh, AArch64Opcode::B, vec![block(vx)]);
    } else if let Some(pv) = pv {
        // --- i64 Precheck: `main_bound = n - (WIDTH-1)`; SIGNED `n < WIDTH`
        // skips the vector loop (covers n <= 0 / negative-as-signed n; the
        // wrapped `main_bound` is dead on the skip path). Then the UNSIGNED
        // header `iv <u main_bound` admits only full in-bounds blocks — see
        // `neon_array::apply_i64` for the wrap-freedom argument.
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
        // --- i32 Vector header: guard `sxtw(iv) + (width-1) < sxtw(bound)`
        // (i64 arithmetic, no overflow) — enough for a full `width`-lane block.
        let nb64 = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Sxtw,
            vec![vreg(nb64), vreg(bound)],
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

    // --- Vector body: compute the current index once (`sxtw(iv)` on i32; `iv`
    // itself on i64 — already 64-bit). For each INPUT stream, compute its base
    // address `base + idx*elem` and walk it with `UNROLL/2` post-index
    // `LDP Qt1, Qt2, [p], #32` pair loads — the SAME 64 bytes per iteration in
    // the SAME order, so sub-block `k` still reads elements
    // `[iv+vf*k, iv+vf*(k+1))`. All input loads are emitted BEFORE any store,
    // so an in-place map reads every element before it is overwritten.
    // The block-START index `si` (i64). Forward: `si = iv` (the block is
    // `[iv, iv+width)`). Descending: `si = iv - (width-1)` (the block is
    // `[iv-(width-1), iv]`), computed in i64 — the guard guarantees `iv >=
    // width-1` so `si >= 0`, and sub-block `k`'s lanes hold the exact scalar
    // indices `si+vf*k .. +vf`, which the per-lane term maps identically. Because
    // the map's lanes are independent, storing these same elements in descending
    // block order produces byte-identical memory to the scalar reverse loop.
    let si = if rec.is_i64 {
        if rec.descending {
            let d = alloc(func, RegClass::Gpr64);
            emit(
                func,
                vb,
                AArch64Opcode::SubRI,
                vec![vreg(d), vreg(rec.iv), imm(desc_blk_off)],
            );
            d
        } else {
            rec.iv
        }
    } else {
        let s = alloc(func, RegClass::Gpr64);
        emit(func, vb, AArch64Opcode::Sxtw, vec![vreg(s), vreg(rec.iv)]);
        if rec.descending {
            let d = alloc(func, RegClass::Gpr64);
            emit(
                func,
                vb,
                AArch64Opcode::SubRI,
                vec![vreg(d), vreg(s), imm(desc_blk_off)],
            );
            d
        } else {
            s
        }
    };
    let mut loaded: HashMap<(u32, usize), VReg> = HashMap::new();
    for base in &rec.bases {
        let p = alloc(func, RegClass::Gpr64);
        // p = base + si*elem   (Madd d, n, m, a = a + n*m).
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

    // --- Vector body: a SEPARATE post-index pointer for the output store, freshly
    // computed as `store_base + si*elem` (never the same register as any input load
    // pointer, so in-place load and store advance independently over the same
    // addresses). For each sub-block: lower TERM over that sub-block's loaded
    // lanes and ST1 it back, advancing the pointer by 16 bytes.
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
        arr_code,
        elem_code,
        const_class,
        is_i64: rec.is_i64,
        chain: rec.chain,
        def: rec.def.clone(),
        loop_insts: rec.loop_insts.clone(),
        loads: rec.loads.clone(),
        selects: rec.selects.clone(),
        def_count: rec.def_count.clone(),
        loaded,
        const_cache: HashMap::new(),
        inv_leaves: rec.inv_leaves.clone(),
        inv_cache: HashMap::new(),
        memo: HashMap::new(),
    };
    // Lower every sub-block's term first, then store them in PAIRS with
    // post-index `STP Qk, Qk+1, [sp], #32` — one instruction per 32 bytes, like
    // clang's `stp q, q` map-store shape. Byte-identical to the prior per-block
    // `ST1 {V.T}, [sp], #16` sequence: a full-width vector term is a 16-byte Q
    // register whatever the lane arrangement, so the paired store writes the
    // SAME 32 bytes in the SAME order to the SAME running pointer. Any odd
    // trailing block (UNROLL not even) keeps a single ST1.
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
            vec![vreg(vterms[k]), vreg(sp), imm(arr_code)],
        );
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: step the scalar induction by `width` — FORWARD `+width`
    // (next ascending block) or DESCENDING `-width` (next lower block). The
    // untouched scalar loop resumes from this iv: forward it writes the disjoint
    // tail `a[V..n)`; descending it writes the disjoint low tail `a[iv..=0]`
    // (iv < width-1 on exit), so `[0, init]` is covered exactly once either way.
    emit(
        func,
        vl,
        if rec.descending {
            AArch64Opcode::SubRI
        } else {
            AArch64Opcode::AddRI
        },
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector exit: a map has no accumulator (nothing to reduce). ROTATED: guard
    // the do-while scalar tail against the exhausted (remainder-0) case.
    //   * FORWARD: when the vector consumed ALL `n` elements `iv == bound`, so
    //     `iv >=u bound` branches to the true exit rather than falling into the
    //     do-while (which would STORE `a[n]` and run off the end). For remainder > 0
    //     (`iv < bound`) control FALLS THROUGH to the scalar loop.
    //   * ROTATED REVERSE: the do-while body accesses index `iv-1`, so it is only
    //     safe while `iv >= 1`. When the vector consumed the low tail down through
    //     index 0, `iv <= 0`, so `iv < 1` (signed `b.lt`) branches to the true exit;
    //     otherwise FALLS THROUGH to the do-while, which writes the disjoint low
    //     tail `[0, iv-1]`. So `[0, n-1]` is covered exactly once either way.
    // NATIVE: rec.guard is a safe top-test; branch unconditionally.
    if let Some(exit) = rec.rotated_exit {
        if rec.descending {
            emit(func, vx, AArch64Opcode::CmpRI, vec![vreg(rec.iv), imm(1)]);
            emit(
                func,
                vx,
                AArch64Opcode::BCond,
                vec![imm(CC_LT), block(exit)],
            );
        } else {
            // iv and bound share a register class (checked in recognize), so a
            // direct unsigned compare is exact for both the .4S and .2D paths.
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
                vec![imm(CC_HS), block(exit)],
            );
        }
    } else {
        emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);
    }

    // --- COMMIT: splice the fresh blocks in front of the scalar loop (through
    // the precheck on the i64 path). Point of no return; runs only after all
    // lowering succeeded. When versioning, the preheader enters the runtime alias
    // precheck (regime C) first; otherwise the vector precheck/header directly.
    let entry = if rec.needs_versioning {
        av[0]
    } else {
        pv.unwrap_or(vh)
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

fn lower(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> Option<VReg> {
    if val == ctx.iv {
        return None;
    }
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
    }
    // A recognized select-diamond value -> the faithfully-proven SMIN/SMAX.4S
    // lanewise ops (multi-def dest: resolved here, NEVER through the def map;
    // `.4S` only — recognition bailed any i64 select). The CLAMP emits
    // `smin(smax(v, lo), hi)`: exactly the composition whose per-lane equality
    // with the scalar nested select was proven at recognition (`lo <= hi`).
    if let Some(expr) = ctx.selects.get(&val.id).cloned() {
        use AArch64Opcode::{NeonSmaxV, NeonSminV};
        if ctx.is_i64 {
            return None;
        }
        let d = match expr {
            SelExpr::MinMax { is_min, a, b } => {
                let va = lower(func, ctx, a)?;
                let vb = lower(func, ctx, b)?;
                bin(
                    func,
                    ctx,
                    if is_min { NeonSminV } else { NeonSmaxV },
                    va,
                    vb,
                    true,
                )
            }
            SelExpr::Clamp { v, lo, hi } => {
                let vv = lower(func, ctx, v)?;
                let vlo = lower(func, ctx, lo)?;
                let vhi = lower(func, ctx, hi)?;
                let m = bin(func, ctx, NeonSmaxV, vv, vlo, true);
                bin(func, ctx, NeonSminV, m, vhi, true)
            }
        };
        ctx.memo.insert(val.id, d);
        return Some(d);
    }
    // A recognized load leaf -> the vector loaded for this sub-block.
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
    // A loop-invariant scalar leaf -> DUP-broadcast once in the preheader.
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
        // CHAIN only: a value-preserving in-loop copy of a SINGLE-def value —
        // lower the source; the copy adds nothing per-lane. Mirrors `node_ok`
        // exactly (fail-closed on a multi-def dest).
        MovR | Copy if ctx.chain && ops.len() == 2 => {
            if ctx.def_count.get(&val.id).copied() != Some(1) {
                return None;
            }
            lower(func, ctx, vreg_of(&ops[1])?)?
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
/// preheader (the value dominates the preheader, so it is available). The
/// per-lane op over this broadcast is bit-exact with the scalar op against the
/// same `s` in every iteration.
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

/// SOUNDNESS for the ROTATED shape (see the identical guard in neon_array):
/// `apply` rewires preheader -> vector-header, BYPASSING the block where clang
/// inits the induction (the "guard"). If iv is defined only there, the vector
/// loop reads an UNINITIALIZED iv (P0). Require some definition of `iv` to
/// DOMINATE the preheader (native shape: yes; clang rotated shape: no).
/// Fail-closed to scalar otherwise.
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
            let inst = func.inst(inst_id);
            if inst.opcode.produces_value()
                && matches!(inst.operands.first(), Some(MachOperand::VReg(v)) if *v == iv)
            {
                return true;
            }
        }
    }
    false
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
    /// Count the runtime alias-versioning disjointness branches (`BCond` with the
    /// unsigned `LS` condition). Regime (C) emits exactly TWO per distinct input
    /// base checked, so this is `2 * check_bases.len()` on a versioned map and `0`
    /// on any statically-proven (regime A/B) map.
    fn count_ls_guard(func: &MachFunction) -> usize {
        func.blocks
            .iter()
            .flat_map(|blk| blk.insts.iter().copied())
            .filter(|&id| {
                let i = func.inst(id);
                i.opcode == AArch64Opcode::BCond && imm_of(&i.operands[0]) == Some(CC_LS)
            })
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

    /// Build the rotated map loop `for i in 0..n: a[i] = TERM` in the exact shape
    /// `loop-latch-layout` emits (guard / header / latch).
    ///
    /// Register map: v0=base_a(store ptr), v1=n, v2=base_b(load ptr),
    /// v10=base_c(load ptr). v3=0, v4=1, v40=4(es). iv=v5.
    /// `kind`: 0 => a[i]=b[i]+c[i] (two inputs); 1 => in-place a[i]=a[i]*2c
    /// where 2c is a const, BUT with a dead `b[i]` load also present (so it is a
    /// multi-pointer body — exercises the noalias path); 2 => a[i]=b[i]+c[i] but
    /// base_a==base_b; 3 => PURE single-array in-place multi-use
    /// `a[i]=a[i]*a[i]*a[i]` with NO foreign load at all (regime (A)).
    fn build_map_loop(kind: u8) -> MachFunction {
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
        // Preheader: base pointers + constants; iv=0.
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a
        push(&mut func, bb0, Copy, vec![v(1), v(1)]); // n
        push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // base_b
        push(&mut func, bb0, Copy, vec![v64(10), v64(10)]); // base_c
        push(&mut func, bb0, Movz, vec![v(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v(4), i(1)]);
        push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // element size
        push(&mut func, bb0, Movz, vec![v(41), i(2)]); // const 2 (for kind 1)
        push(&mut func, bb0, MovR, vec![v(5), v(3)]); // iv = 0
        push(&mut func, bb0, B, vec![b(guard)]);
        // Guard.
        push(&mut func, guard, CmpRR, vec![v(5), v(1)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        // Header: addresses + loads + term + store + step.
        push(&mut func, header, Sxtw, vec![v64(10 + 100), v(5)]); // sxtw iv -> v110
        // load b[i] — only for kinds that actually reference a foreign pointer
        // (kind 3 is a PURE single-array in-place body: no b[i] load at all).
        if kind != 3 {
            push(
                &mut func,
                header,
                Madd,
                vec![v64(20), v64(110), v64(40), v64(2)],
            );
            push(&mut func, header, LdrRI, vec![v(21), v64(20), i(0)]); // b[i]
        }
        let term_val: u32 = match kind {
            1 => {
                // in-place a[i] = a[i]*2 : load a[i], mul by const 2.
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(30), v64(110), v64(40), v64(0)],
                );
                push(&mut func, header, LdrRI, vec![v(31), v64(30), i(0)]); // a[i]
                push(&mut func, header, MulRR, vec![v(50), v(31), v(41)]); // a[i]*2
                50
            }
            3 => {
                // PURE in-place multi-use a[i] = a[i]*a[i]*a[i] (one load of a[i],
                // used THREE times — exercises load-leaf memoization). No b load.
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(30), v64(110), v64(40), v64(0)],
                );
                push(&mut func, header, LdrRI, vec![v(31), v64(30), i(0)]); // a[i]
                push(&mut func, header, MulRR, vec![v(50), v(31), v(31)]); // a*a
                push(&mut func, header, MulRR, vec![v(51), v(50), v(31)]); // (a*a)*a
                51
            }
            _ => {
                // a[i] = b[i] + c[i]
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(25), v64(110), v64(40), v64(10)],
                );
                push(&mut func, header, LdrRI, vec![v(26), v64(25), i(0)]); // c[i]
                push(&mut func, header, AddRR, vec![v(50), v(21), v(26)]); // b+c
                50
            }
        };
        // store address a[i] and the store.
        push(
            &mut func,
            header,
            Madd,
            vec![v64(60), v64(110), v64(40), v64(0)],
        );
        push(&mut func, header, StrRI, vec![v(term_val), v64(60), i(0)]);
        push(&mut func, header, AddRR, vec![v(70), v(5), v(4)]); // iv+1
        push(&mut func, header, B, vec![b(latch)]);
        push(&mut func, latch, AddRI, vec![v(5), v(70), i(0)]); // iv writeback
        push(&mut func, latch, CmpRR, vec![v(5), v(1)]);
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

    /// Build the rotated REVERSE map loop `for i=n-1; i>=0; i--: a[i] = TERM` in
    /// the shape `loop-latch-layout` emits — mirrors [`build_map_loop`] but with a
    /// decrementing induction (`SubRR(iv, 1)`), the `iv >= 0` (CC_GE) exit test
    /// comparing against a zero register, and the same `base + sext(iv)*4`
    /// addressing. `kind` matches [`build_map_loop`].
    fn build_map_loop_reverse(kind: u8) -> MachFunction {
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
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a
        push(&mut func, bb0, Copy, vec![v(1), v(1)]); // n
        push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // base_b
        push(&mut func, bb0, Copy, vec![v64(10), v64(10)]); // base_c
        push(&mut func, bb0, Movz, vec![v(3), i(0)]); // ZERO (the `iv >= 0` rhs)
        push(&mut func, bb0, Movz, vec![v(4), i(1)]); // ONE (the step)
        push(&mut func, bb0, Movz, vec![v64(40), i(4)]);
        push(&mut func, bb0, Movz, vec![v(41), i(2)]);
        push(&mut func, bb0, SubRR, vec![v(5), v(1), v(4)]); // iv = n-1
        push(&mut func, bb0, B, vec![b(guard)]);
        // Guard: iv >= 0 (CC_GE against the zero register v3).
        push(&mut func, guard, CmpRR, vec![v(5), v(3)]);
        push(&mut func, guard, BCond, vec![i(CC_GE), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        // Header: addresses + loads + term + store + descending step.
        push(&mut func, header, Sxtw, vec![v64(110), v(5)]);
        if kind != 3 {
            push(
                &mut func,
                header,
                Madd,
                vec![v64(20), v64(110), v64(40), v64(2)],
            );
            push(&mut func, header, LdrRI, vec![v(21), v64(20), i(0)]); // b[i]
        }
        let term_val: u32 = match kind {
            1 => {
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(30), v64(110), v64(40), v64(0)],
                );
                push(&mut func, header, LdrRI, vec![v(31), v64(30), i(0)]);
                push(&mut func, header, MulRR, vec![v(50), v(31), v(41)]);
                50
            }
            3 => {
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(30), v64(110), v64(40), v64(0)],
                );
                push(&mut func, header, LdrRI, vec![v(31), v64(30), i(0)]);
                push(&mut func, header, MulRR, vec![v(50), v(31), v(31)]);
                push(&mut func, header, MulRR, vec![v(51), v(50), v(31)]);
                51
            }
            _ => {
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(25), v64(110), v64(40), v64(10)],
                );
                push(&mut func, header, LdrRI, vec![v(26), v64(25), i(0)]);
                push(&mut func, header, AddRR, vec![v(50), v(21), v(26)]);
                50
            }
        };
        push(
            &mut func,
            header,
            Madd,
            vec![v64(60), v64(110), v64(40), v64(0)],
        );
        push(&mut func, header, StrRI, vec![v(term_val), v64(60), i(0)]);
        push(&mut func, header, SubRR, vec![v(70), v(5), v(4)]); // iv-1
        push(&mut func, header, B, vec![b(latch)]);
        push(&mut func, latch, AddRI, vec![v(5), v(70), i(0)]); // iv writeback
        push(&mut func, latch, CmpRR, vec![v(5), v(3)]); // iv vs 0
        push(&mut func, latch, BCond, vec![i(CC_GE), b(header)]);
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
    fn vectorizes_reverse_in_place_regime_a() {
        // REVERSE single-array in-place `for i=n-1..0: a[i]=a[i]*a[i]*a[i]` — no
        // noalias needed (regime A). Must fire with DESCENDING addressing.
        let mut func = build_map_loop_reverse(3);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(pass.run(&mut func), "reverse in-place map should vectorize");
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        // Descending block-start `iv-(width-1)`: a SubRI by width-1 (15) in the
        // vector body, and the latch steps iv DOWN by width (SubRI ..,16).
        assert!(
            count(&func, AArch64Opcode::SubRI) >= 2,
            "block-start (iv-15) + latch decrement (iv-16)"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL / 2,
            "2 LDP q,q"
        );
    }

    #[test]
    fn vectorizes_reverse_two_input_when_all_noalias() {
        // REVERSE `for i=n-1..0: a[i]=b[i]+c[i]` — the acceptance shape. Fires
        // with noalias on all three bases (regime B, distinct roots).
        let mut func = build_map_loop_reverse(0);
        func.noalias_params = vec![0, 2, 10];
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "reverse two-input map (noalias) should vectorize"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL,
            "4 LDP q,q"
        );
        assert_paired_stores(&func);
    }

    #[test]
    fn bails_reverse_two_input_without_noalias() {
        // NATIVE REVERSE multi-pointer with NO noalias must BAIL. Regime (C) runtime
        // versioning is enabled for the ROTATED REVERSE (clang -O1) shape only,
        // where the range length `n` is recoverable from the loop's INITIAL iv. The
        // NATIVE reverse shape (`build_map_loop_reverse`, exit test in the latch)
        // has NO recovered count — its length would need `iv+1` from an unrecovered
        // initial iv — so it still fail-closes (rotated_exit is None). Static
        // disjointness (regime B) is unprovable without noalias, so it stays scalar.
        let mut func = build_map_loop_reverse(0);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(
            !pass.run(&mut func),
            "native reverse multi-pointer w/o noalias must BAIL"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonStpQPost),
            0,
            "no store emitted"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonSt1Post),
            0,
            "no store emitted"
        );
    }

    /// Build the ROTATED REVERSE map loop clang -O1 emits for
    /// `for(i=n-1;i>=0;i--) y[i] += x[i];` (kind 0 adds a distinct input `x`;
    /// kind 3 is the pure single-array in-place `y[i] += y[i]`). The phi `iv`
    /// (v5, Gpr64) counts the trip DOWN from `n` to `1`; the array INDEX is
    /// `iv-1` (v8 = `AddRR(iv, negone)`, `negone = Movn 0`), which the latch
    /// writeback `iv = MovR(iv-1)` reuses. The header exit test is
    /// `cmp iv, 1; b.gt <latch>` (continue while iv>1). iv is initialized in the
    /// GUARD as a copy of the i64 count `v6` (clang's `uxtw(n)`).
    ///
    /// Register map: v0=base_y (store + in-place input), v2=base_x (distinct
    /// input), v6=count (i64), v40=4 (es), v7=-1 (Movn), iv=v5.
    fn build_map_loop_rotated_reverse(kind: u8, nested: bool) -> MachFunction {
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
        // Preheader: base pointers + the i64 count + constants.
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_y (store)
        push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // base_x (distinct input)
        push(&mut func, bb0, Copy, vec![v64(6), v64(6)]); // count n (i64, uxtw(n))
        push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // element size
        push(&mut func, bb0, Movn, vec![v64(7), i(0)]); // negone = -1
        push(&mut func, bb0, B, vec![b(guard)]);
        // Guard (rotated preheader): iv = count; unconditional B -> header.
        push(&mut func, guard, MovR, vec![v64(5), v64(6)]); // iv = n
        push(&mut func, guard, B, vec![b(header)]);
        // Header: index = iv-1; loads; term; store; exit test.
        push(&mut func, header, AddRR, vec![v64(8), v64(5), v64(7)]); // idx = iv-1
        push(
            &mut func,
            header,
            Madd,
            vec![v64(30), v64(8), v64(40), v64(0)],
        ); // &y[idx]
        push(&mut func, header, LdrRI, vec![v(31), v64(30), i(0)]); // y[idx]
        let term_val: u32 = match kind {
            3 => {
                // PURE in-place: y[idx] += y[idx] (double); no distinct input.
                push(&mut func, header, AddRR, vec![v(50), v(31), v(31)]);
                50
            }
            _ => {
                push(
                    &mut func,
                    header,
                    Madd,
                    vec![v64(20), v64(8), v64(40), v64(2)],
                ); // &x[idx]
                push(&mut func, header, LdrRI, vec![v(21), v64(20), i(0)]); // x[idx]
                push(&mut func, header, AddRR, vec![v(50), v(31), v(21)]); // y[idx]+x[idx]
                50
            }
        };
        push(&mut func, header, StrRI, vec![v(term_val), v64(30), i(0)]); // store y[idx]
        push(&mut func, header, CmpRI, vec![v64(5), i(1)]); // cmp iv, 1
        push(&mut func, header, BCond, vec![i(CC_GT), b(latch)]); // continue if iv>1
        push(&mut func, header, B, vec![b(exit)]);
        // Latch: iv = idx (= iv-1); B -> header.
        push(&mut func, latch, MovR, vec![v64(5), v64(8)]);
        push(&mut func, latch, B, vec![b(header)]);
        func.add_edge(bb0, guard);
        func.add_edge(guard, header);
        func.add_edge(header, latch);
        func.add_edge(header, exit);
        func.add_edge(latch, header);
        if nested {
            // The clang -O3 NEST: `for k in 0..K { for i=n-1;i>=0;i-- { ... } }`
            // with the `n > 0` entry test hoisted out of the whole nest. The inner
            // loop's entry block is then the OUTER loop's header, i.e. `guard` has
            // TWO predecessors (outer preheader `bb0` + outer latch). Everything
            // about the inner loop is unchanged — this is exactly the difference
            // that used to turn the vectorizer off.
            let olatch = func.create_block();
            let done = func.create_block();
            push(&mut func, exit, B, vec![b(olatch)]);
            push(&mut func, olatch, AddRI, vec![v(60), v(60), i(1)]);
            push(&mut func, olatch, CmpRI, vec![v(60), i(1000)]);
            push(&mut func, olatch, BCond, vec![i(CC_LT), b(guard)]);
            push(&mut func, olatch, B, vec![b(done)]);
            push(&mut func, done, Ret, vec![]);
            func.add_edge(exit, olatch);
            func.add_edge(olatch, guard);
            func.add_edge(olatch, done);
        } else {
            push(&mut func, exit, Ret, vec![]);
        }
        func.next_vreg = 512;
        func
    }

    #[test]
    fn versions_rotated_reverse_accumulate_without_noalias() {
        // The ary3 acceptance shape: rotated reverse `for(i=n-1;i>=0;i--) y[i]+=x[i]`
        // over non-restrict arrays. Static disjointness is unprovable, so regime (C)
        // RUNTIME versioning fires with the recovered count and descending block
        // addressing. Vectorizes: 2 arrays (in-place y + distinct x) * 2 pairs = 4
        // LDP q,q, 2 paired STP, and one distinct-input range check (2 LS guards).
        let mut func = build_map_loop_rotated_reverse(0, false);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "rotated reverse accumulate must VERSION (regime C)"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL,
            "4 LDP q,q"
        );
        assert_paired_stores(&func);
        assert_eq!(
            count_ls_guard(&func),
            2,
            "one distinct input -> 2 LS range guards"
        );
        // Descending block-start `iv-width` (SubRI ..,16) + latch decrement by width
        // (SubRI ..,16); and the reverse tail guard `iv < 1` (a CmpRI ..,1).
        assert!(
            count(&func, AArch64Opcode::SubRI) >= 2,
            "block-start + latch decrement"
        );
        // Scalar fallback preserved for the alias/remainder tail.
        assert_eq!(count(&func, AArch64Opcode::StrRI), 1, "scalar store kept");
    }

    #[test]
    fn vectorizes_rotated_reverse_in_place_double() {
        // Pure single-array in-place rotated reverse `y[i]+=y[i]` (regime A — the
        // only pointer touched is the store base). No noalias, no runtime guard.
        let mut func = build_map_loop_rotated_reverse(3, false);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "rotated reverse in-place double must vectorize"
        );
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        // One array read in place: 1 base * 2 pairs = 2 LDP q,q; regime A => no guard.
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL / 2,
            "2 LDP q,q"
        );
        assert_eq!(count_ls_guard(&func), 0, "regime A takes no runtime guard");
    }

    #[test]
    fn vectorizes_rotated_reverse_with_multi_entry_guard() {
        // SHAPE FRAGILITY (the ary3 -O3 witness). Same inner loop as
        // `versions_rotated_reverse_accumulate_without_noalias`, but the loop sits
        // inside an enclosing loop whose entry test has been hoisted out of the
        // nest, so the inner loop's entry block is the OUTER loop's header and has
        // TWO predecessors. Nothing about the inner loop changed, so it must still
        // vectorize: the rotated path re-roots onto the guard and never reads the
        // block before it.
        let mut func = build_map_loop_rotated_reverse(0, true);
        let header = (0..func.blocks.len() as u32)
            .map(BlockId)
            .find(|&b| func.block(b).preds.len() == 2 && func.block(b).succs.len() == 2)
            .expect("inner header has 2 preds and 2 succs");
        let guard = *func
            .block(header)
            .preds
            .iter()
            .find(|&&p| func.block(p).succs.len() == 1)
            .expect("the guard is the header pred with a single successor");
        assert_eq!(
            func.block(guard).preds.len(),
            2,
            "precondition: the guard is multi-entry (outer preheader + outer latch)"
        );
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "a multi-entry guard must NOT disable the rotated map vectorizer"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL,
            "4 LDP q,q"
        );
        assert_paired_stores(&func);
        assert_eq!(count(&func, AArch64Opcode::StrRI), 1, "scalar tail kept");
    }

    #[test]
    fn bails_native_shape_when_guard_is_multi_entry() {
        // The NATIVE shape keeps its guard as the scalar loop's top test and puts
        // the vector preamble in the block BEFORE it, so it still REQUIRES a
        // dedicated single-entry guard. Fail-closed must be preserved there — the
        // relaxation is rotated-only.
        let mut func = build_map_loop(0);
        func.noalias_params = vec![0, 2, 10];
        // Give the native guard a second entry. `build_map_loop` creates blocks in
        // the order entry, guard, header, latch, exit.
        let guard = BlockId(func.entry.0 + 1);
        assert_eq!(
            func.block(guard).preds.len(),
            1,
            "guard starts single-entry"
        );
        assert_eq!(func.block(guard).succs.len(), 2, "guard is the top test");
        let extra = func.create_block();
        let id = func.push_inst(MachInst::new(AArch64Opcode::B, vec![b(guard)]));
        func.append_inst(extra, id);
        func.add_edge(extra, guard);
        assert_eq!(func.block(guard).preds.len(), 2);
        let mut pass = NeonMapPass::new();
        assert!(
            !pass.run(&mut func),
            "native shape must still fail-closed on a multi-entry guard"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonStpQPost), 0);
    }

    #[test]
    fn bails_rotated_reverse_when_compare_not_one() {
        // Fail-closed: if the header exit compares `iv` against a constant other
        // than 1, the covered index range is NOT `[0, n-1]` and the recovered count
        // would be wrong, so recognition must BAIL (no vector store emitted).
        let mut func = build_map_loop_rotated_reverse(0, false);
        // Rewrite the header `CmpRI(iv, 1)` to `CmpRI(iv, 2)`.
        let ids: Vec<InstId> = func.blocks.iter().flat_map(|b| b.insts.clone()).collect();
        for id in ids {
            let inst = func.inst_mut(id);
            if inst.opcode == AArch64Opcode::CmpRI
                && matches!(inst.operands.get(1), Some(MachOperand::Imm(1)))
            {
                inst.operands[1] = MachOperand::Imm(2);
            }
        }
        let mut pass = NeonMapPass::new();
        assert!(
            !pass.run(&mut func),
            "rotated reverse with cmp!=1 must BAIL"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonStpQPost),
            0,
            "no store emitted"
        );
    }

    #[test]
    fn vectorizes_two_input_add_when_all_noalias() {
        let mut func = build_map_loop(0);
        // a=v0, b=v2, c=v10 all noalias.
        func.noalias_params = vec![0, 2, 10];
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "should fire on `a[i]=b[i]+c[i]` (noalias)"
        );
        assert_eq!(pass.fired(), 1);
        // 4 sub-blocks * 2 input arrays = 8 LD1 (as 4 LDP q,q); 2 paired STP;
        // 4 vector adds.
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL,
            "4 LDP q,q"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonLd1Post),
            0,
            "LD1 replaced by LDP"
        );
        assert_paired_stores(&func);
        assert!(
            count(&func, AArch64Opcode::NeonAddV) >= UNROLL,
            "vector adds"
        );
    }

    #[test]
    fn versions_when_store_base_not_noalias() {
        // Store base `a` (v0) NOT marked noalias => STATIC disjointness (regime B)
        // fails, so regime (C) RUNTIME ALIAS VERSIONING fires: the map vectorizes
        // behind a runtime range-disjointness guard, scalar loop kept as fallback.
        let mut func = build_map_loop(0);
        func.noalias_params = vec![2, 10]; // b,c noalias but NOT a
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "must VERSION (not bail) when store base not noalias"
        );
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        // 2 distinct inputs (b,c) * 2 disjointness sub-tests = 4 LS guards.
        assert_eq!(count_ls_guard(&func), 4, "runtime alias guard present");
        // Scalar fallback preserved: the original scalar store still exists.
        assert_eq!(count(&func, AArch64Opcode::StrRI), 1, "scalar store kept");
    }

    #[test]
    fn versions_when_input_base_not_noalias() {
        // Store base noalias but an INPUT (c=v10) is not => static disjointness
        // unprovable => regime (C) runtime versioning fires (sound at runtime).
        let mut func = build_map_loop(0);
        func.noalias_params = vec![0, 2]; // a,b noalias but NOT c
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "must VERSION when an input base not noalias"
        );
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        assert_eq!(count_ls_guard(&func), 4, "runtime alias guard present");
        assert_eq!(count(&func, AArch64Opcode::StrRI), 1, "scalar store kept");
    }

    #[test]
    fn versions_with_no_noalias_params_at_all() {
        // No noalias attrs at all: static disjointness is unprovable, so the
        // multi-pointer map takes regime (C) runtime versioning — the common
        // "two separate callocs, no restrict" C shape (`a[i]=b[i]+c[i]`).
        let mut func = build_map_loop(0);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(pass.run(&mut func), "must VERSION with no noalias params");
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        assert_eq!(count_ls_guard(&func), 4, "runtime alias guard present");
        assert_eq!(count(&func, AArch64Opcode::StrRI), 1, "scalar store kept");
    }

    #[test]
    fn vectorizes_in_place_when_noalias() {
        // in-place a[i]=a[i]*2 with a (v0) noalias, same-index read => sound.
        let mut func = build_map_loop(1);
        func.noalias_params = vec![0, 2];
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "in-place same-index map should vectorize"
        );
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
    }

    #[test]
    fn vectorizes_in_place_without_any_noalias() {
        // RELAXED regime (A): PURE in-place multi-use a[i]=a[i]*a[i]*a[i], NO
        // noalias attr at all. The only pointer touched is the store base `a` at
        // the same index, so this is provably sound irrespective of aliasing and
        // MUST now vectorize. Multi-use of the loaded lane must be supported.
        let mut func = build_map_loop(3);
        // noalias_params intentionally empty (no `restrict`/noalias in source).
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "single-array in-place map must vectorize WITHOUT noalias"
        );
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        // Reads the SAME array it writes: 1 base * UNROLL sub-blocks = 4 LD1.
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL / 2,
            "2 LDP q,q"
        );
    }

    #[test]
    fn in_place_with_dead_foreign_load_bails_without_noalias() {
        // Conservative: kind 1 is in-place `a[i]=a[i]*2` BUT carries a DEAD
        // `b[i]` load (distinct pointer). Even though `b`'s value is unused, the
        // loop touches a second pointer's memory, so regime (A) does NOT apply
        // and — with no noalias — it must BAIL (fail-closed, not miscompile).
        let mut func = build_map_loop(1);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(
            !pass.run(&mut func),
            "in-place body with a foreign load must BAIL without noalias"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0, "no ST1");
    }

    #[test]
    fn two_pointer_versions_without_noalias() {
        // Two DISTINCT accessed pointers (a[i]=b[i]+c[i]) with NO noalias: static
        // disjointness is unprovable, so instead of BAILing the map is guarded by
        // a RUNTIME range-disjointness check (regime C) — the vector body runs
        // ONLY when b,c are proven at runtime not to overlap the store `a`,
        // otherwise the untouched scalar loop runs. This is sound (the guard is
        // load-bearing), not a weakening of the aliasing contract.
        let mut func = build_map_loop(0);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "two-pointer map without noalias must VERSION"
        );
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        // The runtime guard MUST be present — vectorizing WITHOUT it would be the
        // miscompile this test guards against.
        assert_eq!(
            count_ls_guard(&func),
            4,
            "runtime alias guard MUST be present"
        );
        assert_eq!(
            count(&func, AArch64Opcode::StrRI),
            1,
            "scalar fallback kept"
        );
    }

    // -----------------------------------------------------------------------
    // i64 (`.2D`) width parameterization
    // -----------------------------------------------------------------------

    /// Build the i64 map `for i in 0..n (i64): a[i] = b[i] OP c` with `Gpr64`
    /// iv/bound/term and the i64 address shape `Madd(iv, 8, base)`.
    /// `mul` selects `b[i] * 2` (must BAIL — no MUL.2D) vs `b[i] + 7` (fires).
    fn build_map_loop_i64(mul: bool) -> MachFunction {
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
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a (store)
        push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // n (i64)
        push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // base_b (load)
        push(&mut func, bb0, Movz, vec![v64(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v64(4), i(1)]);
        push(&mut func, bb0, Movz, vec![v64(40), i(8)]); // element size 8
        push(&mut func, bb0, Movz, vec![v64(41), i(7)]); // const operand
        push(&mut func, bb0, MovR, vec![v64(5), v64(3)]); // iv = 0
        push(&mut func, bb0, B, vec![b(guard)]);
        push(&mut func, guard, CmpRR, vec![v64(5), v64(1)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        // Header: load b[i], term, store a[i], step.
        push(
            &mut func,
            header,
            Madd,
            vec![v64(20), v64(5), v64(40), v64(2)],
        );
        push(&mut func, header, LdrRI, vec![v64(21), v64(20), i(0)]); // b[i]
        if mul {
            push(&mut func, header, MulRR, vec![v64(50), v64(21), v64(41)]);
        } else {
            push(&mut func, header, AddRR, vec![v64(50), v64(21), v64(41)]);
        }
        push(
            &mut func,
            header,
            Madd,
            vec![v64(60), v64(5), v64(40), v64(0)],
        );
        push(&mut func, header, StrRI, vec![v64(50), v64(60), i(0)]);
        push(&mut func, header, AddRR, vec![v64(70), v64(5), v64(4)]); // iv+1
        push(&mut func, header, B, vec![b(latch)]);
        push(&mut func, latch, AddRI, vec![v64(5), v64(70), i(0)]);
        push(&mut func, latch, CmpRR, vec![v64(5), v64(1)]);
        push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
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
    fn vectorizes_i64_add_map_on_2d() {
        let mut func = build_map_loop_i64(false);
        func.noalias_params = vec![0, 2];
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "i64 `a[i]=b[i]+7` must vectorize on .2D"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL / 2,
            "2 LDP q,q"
        );
        // Paired STP stores are width-agnostic (raw 16-byte Q moves), so i64
        // .2D uses the SAME #32 pair store — byte-identical to two ST1 {V.2D}.
        assert_paired_stores(&func);
        // Every arrangement-carrying ADD must be `.2D` (imm code 6). The STP
        // pair store carries the #32 post-index, not an arrangement.
        for blk in &func.blocks {
            for &id in &blk.insts {
                let inst = func.inst(id);
                if inst.opcode == AArch64Opcode::NeonAddV {
                    let arr = inst.operands.last().and_then(|op| match op {
                        MachOperand::Imm(x) => Some(*x),
                        _ => None,
                    });
                    assert_eq!(arr, Some(6), "i64 map must emit .2D (code 6)");
                }
            }
        }
    }

    #[test]
    fn i64_mul_map_bails_no_mul_2d() {
        // `a[i] = b[i]*7`: MUL.2D is UNALLOCATED — must BAIL (fail-closed),
        // even with full noalias.
        let mut func = build_map_loop_i64(true);
        func.noalias_params = vec![0, 2];
        let mut pass = NeonMapPass::new();
        assert!(
            !pass.run(&mut func),
            "i64 multiply map must BAIL (no MUL.2D)"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0, "no ST1");
        assert_eq!(count(&func, AArch64Opcode::NeonMulV), 0, "no vector MUL");
    }

    // -----------------------------------------------------------------------
    // Matmul row update (store-form saxpy): the loop-invariant scalar leaf +
    // derived-row-base (based-on noalias) extensions.
    // -----------------------------------------------------------------------

    /// Build the matmul inner `for j<n: crow[j] = crow[j] + s*brow[j]` where the
    /// C row base `crow = <cparam> + rowC*4` and the B row base
    /// `brow = <bparam> + rowB*4` are DERIVED pointers (as a real matmul emits),
    /// and `s` (v3) is a loop-invariant scalar. The term is the fused
    /// `Madd(s, brow[j], crow[j])` the frontend produces. `cparam`/`bparam` pick
    /// which formal pointer each row base is derived from (to drive the
    /// underlying-noalias resolution and its negatives).
    /// Params: v0=C(ptr), v1=B(ptr), v2=n(i32), v3=s(i32). iv=v20.
    fn build_matmul_inner(cparam: u32, bparam: u32) -> MachFunction {
        let mut func = MachFunction::new("mm".to_string(), Signature::new(vec![], vec![]));
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
        // Preheader: params (self-copies), constants, derived row bases, iv=0.
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // C
        push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // B
        push(&mut func, bb0, Copy, vec![v(2), v(2)]); // n
        push(&mut func, bb0, Copy, vec![v(3), v(3)]); // s (loop-invariant scalar)
        push(&mut func, bb0, Movz, vec![v(4), i(0)]);
        push(&mut func, bb0, Movz, vec![v(5), i(1)]);
        push(&mut func, bb0, Movz, vec![v64(6), i(4)]); // element size
        // rowC/rowB indices + sext, then crow/brow = <param> + row*4.
        push(&mut func, bb0, Movz, vec![v64(7), i(64)]); // rowC (bytes-scaled elems)
        push(&mut func, bb0, Movz, vec![v64(10), i(128)]); // rowB
        push(
            &mut func,
            bb0,
            Madd,
            vec![v64(9), v64(7), v64(6), v64(cparam)],
        ); // crow
        push(
            &mut func,
            bb0,
            Madd,
            vec![v64(12), v64(10), v64(6), v64(bparam)],
        ); // brow
        push(&mut func, bb0, MovR, vec![v(20), v(4)]); // iv = 0
        push(&mut func, bb0, B, vec![b(guard)]);
        // Guard.
        push(&mut func, guard, CmpRR, vec![v(20), v(2)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        // Header: &crow[j], cv; &brow[j], bv; term = s*bv + cv; store; step.
        push(&mut func, header, Sxtw, vec![v64(21), v(20)]); // sext(iv)
        push(
            &mut func,
            header,
            Madd,
            vec![v64(22), v64(21), v64(6), v64(9)],
        ); // &crow[j]
        push(&mut func, header, LdrRI, vec![v(23), v64(22), i(0)]); // cv
        push(
            &mut func,
            header,
            Madd,
            vec![v64(24), v64(21), v64(6), v64(12)],
        ); // &brow[j]
        push(&mut func, header, LdrRI, vec![v(25), v64(24), i(0)]); // bv
        push(&mut func, header, Madd, vec![v(26), v(3), v(25), v(23)]); // s*bv + cv
        push(&mut func, header, StrRI, vec![v(26), v64(22), i(0)]); // crow[j] = ... (in-place addr v22)
        push(&mut func, header, AddRR, vec![v(27), v(20), v(5)]); // iv+1
        push(&mut func, header, B, vec![b(latch)]);
        push(&mut func, latch, AddRI, vec![v(20), v(27), i(0)]);
        push(&mut func, latch, CmpRR, vec![v(20), v(2)]);
        push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
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
    fn vectorizes_matmul_row_update_with_invariant_scalar() {
        // crow derived from C (v0, noalias), brow from B (v1, noalias). The
        // store-form saxpy `crow[j] = crow[j] + s*brow[j]` must vectorize:
        // loop-invariant `s` DUP-broadcast, MUL.4S + ADD.4S per lane, paired STP.
        let mut func = build_matmul_inner(0, 1);
        func.noalias_params = vec![0, 1];
        let mut pass = NeonMapPass::new();
        assert!(pass.run(&mut func), "matmul row update must vectorize");
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        assert!(
            count(&func, AArch64Opcode::NeonMulV) >= UNROLL,
            "vector MUL (s*b)"
        );
        assert!(
            count(&func, AArch64Opcode::NeonAddV) >= UNROLL,
            "vector ADD (c+prod)"
        );
        // Exactly one DUP: the loop-invariant scalar broadcast once.
        assert_eq!(count(&func, AArch64Opcode::NeonDupGen), 1, "one DUP(s)");
        // crow read AND written in-place + brow read = 2 input streams.
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL,
            "2 streams * 2 LDP"
        );
    }

    #[test]
    fn matmul_row_update_versions_without_noalias() {
        // No noalias attrs: static disjointness of crow (store+in-place read) vs
        // brow (read) is unprovable, so regime (C) runtime versioning guards the
        // row update. crow is in-place (== store base, skipped); only brow needs a
        // runtime range check => 2 LS guards.
        let mut func = build_matmul_inner(0, 1);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(pass.run(&mut func), "matmul without noalias must VERSION");
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        assert_eq!(
            count_ls_guard(&func),
            2,
            "one distinct input (brow) => 2 LS guards"
        );
        assert_eq!(
            count(&func, AArch64Opcode::StrRI),
            1,
            "scalar fallback kept"
        );
    }

    #[test]
    fn matmul_row_update_versions_when_load_root_not_noalias() {
        // crow roots at C (noalias) but brow roots at B which is NOT noalias:
        // static disjointness unprovable => regime (C) runtime versioning.
        let mut func = build_matmul_inner(0, 1);
        func.noalias_params = vec![0]; // only C
        let mut pass = NeonMapPass::new();
        assert!(pass.run(&mut func), "non-noalias load root must VERSION");
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        assert_eq!(count_ls_guard(&func), 2, "brow runtime range check");
        assert_eq!(
            count(&func, AArch64Opcode::StrRI),
            1,
            "scalar fallback kept"
        );
    }

    #[test]
    fn matmul_row_update_versions_when_bases_share_underlying_param() {
        // Both row bases derived from the SAME param C at DIFFERENT offsets: static
        // disjointness fails (rows could overlap), but a RUNTIME range check on the
        // actual crow/brow pointers decides it soundly — disjoint rows vectorize,
        // overlapping rows fall to the scalar loop. Regime (C) versioning fires.
        let mut func = build_matmul_inner(0, 0); // crow AND brow based on C
        func.noalias_params = vec![0, 1];
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "distinct derived pointers into the same array must VERSION at runtime"
        );
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        assert_eq!(count_ls_guard(&func), 2, "brow-vs-crow runtime range check");
        assert_eq!(
            count(&func, AArch64Opcode::StrRI),
            1,
            "scalar fallback kept"
        );
    }

    // ---------------------------------------------------------------------
    // FORWARD bounds-guarded `while i<N` CHAIN shape (recognize_forward_chain).
    // ---------------------------------------------------------------------

    /// Build the FORWARD test-first `while i<N { a[i] = TERM }` map the bridge
    /// emits for a fixed-size array: a LINEAR CHAIN of blocks split by in-loop
    /// `iv <u N` array-bounds-check diamonds. Each non-latch block ends
    /// `cmp <iv copy>, N; b.lo <next in-body>; b <panic/exit out-of-body>`; the
    /// store lives in the latch, which is the sole `iv=iv+1` writeback + back-edge.
    /// EVERY guard compares a MovR copy of the iv against the SAME limit register
    /// `v5` (single-N agreement == loop bound == array length). Register map:
    /// v0=base_a, v1=base_b (Gpr64); v5=N (Gpr64 const limit); v40=4 (es);
    /// v58=k (Gpr32 loop-invariant scalar); iv=v59 (Gpr64, MIXED i64-index /
    /// i32-element). `kind`: 0 => two-input `a[i]=a[i]*k+b[i]` (distinct arrays,
    /// regime C versions); 3 => single-array in-place `a[i]=a[i]*a[i]*a[i]`
    /// (regime A, no versioning).
    fn build_chain_map_loop(kind: u8) -> MachFunction {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let header = func.create_block();
        let g_a = func.create_block();
        let g_b = func.create_block();
        let latch = func.create_block();
        let abort = func.create_block();
        let exit = func.create_block();
        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        let two_input = kind == 0;
        // Preheader.
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a def
        push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // base_b def
        push(&mut func, bb0, Movz, vec![v64(5), i(4096)]); // N (shared limit)
        push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // element size
        push(&mut func, bb0, Copy, vec![v(58), v(58)]); // k (invariant scalar, NOT a Movz)
        push(&mut func, bb0, Movz, vec![v64(57), i(0)]); // iv init value
        push(&mut func, bb0, MovR, vec![v64(59), v64(57)]); // iv = 0
        push(&mut func, bb0, B, vec![b(header)]);
        // Header: the loop-continue guard `iv <u N`.
        push(&mut func, header, MovR, vec![v64(63), v64(59)]);
        push(&mut func, header, CmpRR, vec![v64(63), v64(5)]);
        push(&mut func, header, BCond, vec![i(CC_LO), b(g_a)]);
        push(&mut func, header, B, vec![b(exit)]);
        // g_a: address a[i] via a COPY of iv, load a[i], compute, then the a[i]
        // bounds guard.
        push(&mut func, g_a, MovR, vec![v64(66), v64(59)]); // iv copy for the address
        push(
            &mut func,
            g_a,
            Madd,
            vec![v64(73), v64(66), v64(40), v64(0)],
        ); // a[i] addr
        push(&mut func, g_a, LdrRI, vec![v(75), v64(73), i(0)]); // a[i]
        let term_val: u32 = if two_input {
            push(&mut func, g_a, MulRR, vec![v(76), v(75), v(58)]); // a[i]*k
            87 // set below after the add
        } else {
            push(&mut func, g_a, MulRR, vec![v(76), v(75), v(75)]); // a*a
            push(&mut func, g_a, MulRR, vec![v(78), v(76), v(75)]); // (a*a)*a
            78
        };
        push(&mut func, g_a, MovR, vec![v64(67), v64(59)]); // iv copy for the guard
        push(&mut func, g_a, CmpRR, vec![v64(67), v64(5)]);
        push(&mut func, g_a, BCond, vec![i(CC_LO), b(g_b)]);
        push(&mut func, g_a, B, vec![b(abort)]);
        // g_b: only meaningful for the two-input map — load b[i], add, then the b[i]
        // bounds guard. For the single-array map it is a pure PASS-THROUGH guard
        // block (keeps the chain topology uniform; b.lo -> latch).
        push(&mut func, g_b, MovR, vec![v64(77), v64(59)]); // iv copy for the address
        if two_input {
            push(
                &mut func,
                g_b,
                Madd,
                vec![v64(84), v64(77), v64(40), v64(1)],
            ); // b[i] addr
            push(&mut func, g_b, LdrRI, vec![v(86), v64(84), i(0)]); // b[i]
            push(&mut func, g_b, AddRR, vec![v(87), v(76), v(86)]); // a[i]*k + b[i]
        }
        push(&mut func, g_b, MovR, vec![v64(88), v64(59)]); // iv copy for the guard
        push(&mut func, g_b, CmpRR, vec![v64(88), v64(5)]);
        push(&mut func, g_b, BCond, vec![i(CC_LO), b(latch)]);
        push(&mut func, g_b, B, vec![b(abort)]);
        // Latch: store a[i] (iv used DIRECTLY), step, writeback, back-edge.
        push(
            &mut func,
            latch,
            Madd,
            vec![v64(95), v64(59), v64(40), v64(0)],
        ); // a[i] store addr
        push(&mut func, latch, StrRI, vec![v(term_val), v64(95), i(0)]);
        push(&mut func, latch, AddRI, vec![v64(99), v64(59), i(1)]); // iv+1
        push(&mut func, latch, MovR, vec![v64(59), v64(99)]); // writeback
        push(&mut func, latch, B, vec![b(header)]);
        push(&mut func, abort, Ret, vec![]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, header);
        func.add_edge(header, g_a);
        func.add_edge(header, exit);
        func.add_edge(g_a, g_b);
        func.add_edge(g_a, abort);
        func.add_edge(g_b, latch);
        func.add_edge(g_b, abort);
        func.add_edge(latch, header);
        func.next_vreg = 512;
        func
    }

    #[test]
    fn chain_two_input_versions_without_noalias() {
        // `for i in 0..N { a[i] = a[i]*k + b[i] }` over distinct fixed-size arrays,
        // no noalias: the bounds-guarded while-chain must be recognized and VERSION
        // at runtime (regime C) on the distinct input base `b`.
        let mut func = build_chain_map_loop(0);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "forward chain saxpy map should vectorize"
        );
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        // mul.4s (a*k) + add.4s (+b), a DUP-broadcast k, and the regime-C
        // disjointness precheck (2 LS guards for the single distinct base `b`).
        assert_eq!(
            count(&func, AArch64Opcode::NeonMulV),
            UNROLL,
            "per-lane a*k"
        );
        assert!(count(&func, AArch64Opcode::NeonDupGen) >= 1, "k broadcast");
        assert_eq!(
            count_ls_guard(&func),
            2,
            "runtime a-vs-b range disjointness"
        );
        assert_eq!(
            count(&func, AArch64Opcode::StrRI),
            1,
            "scalar chain kept intact"
        );
    }

    #[test]
    fn chain_single_array_in_place_regime_a() {
        // `for i in 0..N { a[i] = a[i]*a[i]*a[i] }` — single array, regime A: fires
        // with NO noalias and NO runtime versioning.
        let mut func = build_chain_map_loop(3);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "forward chain in-place map should vectorize"
        );
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        assert_eq!(count_ls_guard(&func), 0, "regime A needs no runtime check");
        // one load of a[i] reused thrice: exactly UNROLL paired LDP (no b stream).
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL / 2,
            "single a stream"
        );
    }

    #[test]
    fn chain_bails_on_mismatched_bound() {
        // SINGLE-N agreement: if any in-loop bounds guard compares against a
        // DIFFERENT limit than the loop-continue, the vector range is not provably
        // in bounds for that array — must BAIL (fail-closed).
        let mut func = build_chain_map_loop(0);
        // Redefine the g_b guard's limit to a fresh, different constant register.
        let bb0 = func.entry;
        let vdiff = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![v64(200), i(2048)]));
        func.block_mut(bb0).insts.insert(0, vdiff);
        // Retarget g_b's CmpRR (v88, v5) -> (v88, v200).
        for blk in 0..func.blocks.len() {
            let ids: Vec<InstId> = func.block(BlockId(blk as u32)).insts.clone();
            for id in ids {
                let inst = func.inst_mut(id);
                if inst.opcode == AArch64Opcode::CmpRR
                    && inst.operands[0] == v64(88)
                    && inst.operands[1] == v64(5)
                {
                    inst.operands[1] = v64(200);
                }
            }
        }
        let mut pass = NeonMapPass::new();
        assert!(
            !pass.run(&mut func),
            "mismatched bounds-guard limit must BAIL"
        );
        assert_eq!(pass.fired(), 0);
    }

    #[test]
    fn chain_bails_on_non_iv_guard_index() {
        // A guard that does not test (a copy of) the induction proves nothing about
        // the vector range — must BAIL.
        let mut func = build_chain_map_loop(0);
        // Point g_a's guard compare LHS at base_a (v0) instead of an iv copy.
        for blk in 0..func.blocks.len() {
            let ids: Vec<InstId> = func.block(BlockId(blk as u32)).insts.clone();
            for id in ids {
                let inst = func.inst_mut(id);
                if inst.opcode == AArch64Opcode::CmpRR
                    && inst.operands[0] == v64(67)
                    && inst.operands[1] == v64(5)
                {
                    inst.operands[0] = v64(0);
                }
            }
        }
        let mut pass = NeonMapPass::new();
        assert!(!pass.run(&mut func), "non-iv guard index must BAIL");
        assert_eq!(pass.fired(), 0);
    }

    #[test]
    fn chain_bails_on_foreign_store() {
        // A SECOND store in the body is not the single recognized output — BAIL.
        let mut func = build_chain_map_loop(0);
        // Add a second StrRI into g_b (stores b[i] value to the a[i] slot addr).
        let extra = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![v(86), v64(84), i(0)],
        ));
        // Insert before g_b's terminating guard (keep the diamond last-3 intact is
        // not required here — the extra store makes recognize_tail's store count 2).
        let g_b = BlockId(3);
        func.block_mut(g_b).insts.insert(0, extra);
        let mut pass = NeonMapPass::new();
        assert!(!pass.run(&mut func), "a second store must BAIL");
        assert_eq!(pass.fired(), 0);
    }

    #[test]
    fn chain_bails_on_inverted_guard_edges() {
        // A guard whose `b.lo` (iv<N taken) edge leaves the body is not the
        // `iv<N -> continue` diamond this recognizer proves in-bounds — BAIL.
        let mut func = build_chain_map_loop(0);
        // g_a = BlockId(2): retarget its b.lo from g_b(in body) to abort(out).
        let g_a = BlockId(2);
        let ids: Vec<InstId> = func.block(g_a).insts.clone();
        for id in ids {
            let inst = func.inst_mut(id);
            if inst.opcode == AArch64Opcode::BCond {
                inst.operands[1] = b(BlockId(5)); // abort, out of body
            }
        }
        let mut pass = NeonMapPass::new();
        assert!(!pass.run(&mut func), "inverted guard edges must BAIL");
        assert_eq!(pass.fired(), 0);
    }

    /// Build the forward chain where the header is the ONLY bounds diamond and the
    /// intermediate blocks are PASS-THROUGHS: `g_a` has NO guard at all (its
    /// `a[i]` bounds check was eliminated by the dominated-guard bounds-check-elim
    /// pass) and `g_b` carries a still-live `TrapBoundsCheckExact [iv, iv, N]`
    /// (single-N carrier). Term: `a[i] = a[i]*k + b[i]` (two distinct arrays).
    /// `carrier_limit` overrides the carrier's limit for the negative control.
    fn build_chain_carrier_passthrough(carrier_limit: i64) -> MachFunction {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let header = func.create_block();
        let g_a = func.create_block();
        let g_b = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();
        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a
        push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // base_b
        push(&mut func, bb0, Movz, vec![v64(5), i(4096)]); // N (bound)
        push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // es
        push(&mut func, bb0, Copy, vec![v(58), v(58)]); // k (invariant scalar)
        push(&mut func, bb0, Movz, vec![v64(57), i(0)]);
        push(&mut func, bb0, MovR, vec![v64(59), v64(57)]); // iv=0
        push(&mut func, bb0, B, vec![b(header)]);
        // Header: loop-continue diamond (the only guard).
        push(&mut func, header, MovR, vec![v64(63), v64(59)]);
        push(&mut func, header, CmpRR, vec![v64(63), v64(5)]);
        push(&mut func, header, BCond, vec![i(CC_LO), b(g_a)]);
        push(&mut func, header, B, vec![b(exit)]);
        // g_a: PASS-THROUGH (guard eliminated) — load a[i], mul, unconditional B.
        push(&mut func, g_a, MovR, vec![v64(66), v64(59)]);
        push(
            &mut func,
            g_a,
            Madd,
            vec![v64(73), v64(66), v64(40), v64(0)],
        );
        push(&mut func, g_a, LdrRI, vec![v(75), v64(73), i(0)]);
        push(&mut func, g_a, MulRR, vec![v(76), v(75), v(58)]);
        push(&mut func, g_a, B, vec![b(g_b)]);
        // g_b: carrier PASS-THROUGH — load b[i], add, live TrapBoundsCheckExact, B.
        push(&mut func, g_b, MovR, vec![v64(77), v64(59)]);
        push(
            &mut func,
            g_b,
            Madd,
            vec![v64(84), v64(77), v64(40), v64(1)],
        );
        push(&mut func, g_b, LdrRI, vec![v(86), v64(84), i(0)]);
        push(&mut func, g_b, AddRR, vec![v(87), v(76), v(86)]);
        push(
            &mut func,
            g_b,
            TrapBoundsCheckExact,
            vec![v64(59), v64(59), i(carrier_limit)],
        );
        push(&mut func, g_b, B, vec![b(latch)]);
        // Latch: store, step, writeback, back-edge.
        push(
            &mut func,
            latch,
            Madd,
            vec![v64(95), v64(59), v64(40), v64(0)],
        );
        push(&mut func, latch, StrRI, vec![v(87), v64(95), i(0)]);
        push(&mut func, latch, AddRI, vec![v64(99), v64(59), i(1)]);
        push(&mut func, latch, MovR, vec![v64(59), v64(99)]);
        push(&mut func, latch, B, vec![b(header)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, header);
        func.add_edge(header, g_a);
        func.add_edge(header, exit);
        func.add_edge(g_a, g_b);
        func.add_edge(g_b, latch);
        func.add_edge(latch, header);
        func.next_vreg = 512;
        func
    }

    #[test]
    fn chain_passthrough_and_carrier_vectorizes() {
        // Header-only diamond + a pass-through block (eliminated guard) + a live
        // single-N carrier (limit == loop bound) — must vectorize and VERSION.
        let mut func = build_chain_carrier_passthrough(4096);
        assert!(func.noalias_params.is_empty());
        let mut pass = NeonMapPass::new();
        assert!(
            pass.run(&mut func),
            "passthrough+carrier chain should vectorize"
        );
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        assert_eq!(
            count_ls_guard(&func),
            2,
            "runtime a-vs-b range disjointness"
        );
    }

    #[test]
    fn chain_bails_on_carrier_limit_mismatch() {
        // A live carrier whose limit != the loop bound breaks single-N agreement:
        // the vector `[0,N)` range is not proven in bounds for that array — BAIL.
        let mut func = build_chain_carrier_passthrough(2048); // != N (4096)
        let mut pass = NeonMapPass::new();
        assert!(
            !pass.run(&mut func),
            "carrier limit != loop bound must BAIL"
        );
        assert_eq!(pass.fired(), 0);
    }

    // ---------------------------------------------------------------------
    // Select-diamond min/max/CLAMP (the bridge's branchy `if v>HI {HI} else if
    // v< LO {LO} else {v}` lowering) + the `CmpRI` immediate chain bound.
    // ---------------------------------------------------------------------

    /// Build the EXACT machine shape the bridge emits for the in-place clamp
    /// `while i<2048 { v = a[i]+k; a[i] = if v>100 {100} else if v< -100 {-100}
    /// else {v} }` over a LOCAL `[i32; 2048]` (mirrors the d12_saturate dump):
    /// header `cmp iv, #2048; b.lo` (IMMEDIATE bound), a body block ending in the
    /// OUTER select split, MOV-arm diamonds with the merged dest `v56` (outer) /
    /// `v60` (inner), a forwarding inner join, an empty outer join, and the store
    /// via a latch `MovR` copy of the merged value.
    ///
    /// Register map: v0=base_a, v40=4(es), v53=Movz(100), v57=Movn(99) (= -100),
    /// v58=k (invariant scalar), iv=v59 (Gpr64, MIXED index).
    ///
    /// `kind`: 0 => the exact clamp (fires: SMAX+SMIN);
    ///         1 => outer polarity FLIPPED (`b.lt` picking 100) — a silent
    ///              min<->max flip if trusted, so it must BAIL;
    ///         2 => CROSSED bounds (outer `> -100 ? -100 : smax(v,100)`) — the
    ///              clamp identity needs `lo <= hi`, must BAIL;
    ///         3 => outer condition UNSIGNED (`b.hi`) — SMIN/SMAX are SIGNED,
    ///              must BAIL (the u32 clamp control);
    ///         4 => SINGLE MIN only (no inner diamond): `if v>100 {100} else
    ///              {v}` (fires: SMIN, no SMAX);
    ///         5 => kind 0 + a STEALTH ACCUMULATOR (`acc = acc + a[i]` hidden
    ///              mid-chain, acc init'd in the preheader) — loop-carried
    ///              scalar state the vector loop would skip, must BAIL;
    ///         6 => kind 4 + a use of the merged dest BEFORE the split (reads
    ///              the PREVIOUS iteration's merged value), must BAIL.
    fn build_chain_clamp_loop(kind: u8) -> MachFunction {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let header = func.create_block();
        let g_a = func.create_block(); // body + OUTER select split
        let arm_hi = func.create_block(); // taken arm: merged = 100
        let inner = func.create_block(); // pure-compare inner split (clamp kinds)
        let arm_lo = func.create_block(); // inner taken arm: d2 = -100
        let arm_v = func.create_block(); // inner fall-through arm: d2 = v
        let ijoin = func.create_block(); // inner join: forwards d2 -> merged
        let join = func.create_block(); // outer join (empty pass-through)
        let latch = func.create_block();
        let exit = func.create_block();
        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        let single = kind == 4 || kind == 6;
        // Preheader: base, constants, invariant scalar, iv=0.
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a
        push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // element size
        push(&mut func, bb0, Movz, vec![v(53), i(100)]); // HI = 100
        push(&mut func, bb0, Movn, vec![v(57), i(99)]); // LO = -100
        push(&mut func, bb0, Copy, vec![v(58), v(58)]); // k (invariant scalar)
        if kind == 5 {
            push(&mut func, bb0, Movz, vec![v(91), i(0)]); // acc = 0
        }
        push(&mut func, bb0, Movz, vec![v64(44), i(0)]);
        push(&mut func, bb0, MovR, vec![v64(59), v64(44)]); // iv = 0
        push(&mut func, bb0, B, vec![b(header)]);
        // Header: `iv <u 2048` IMMEDIATE-bound loop-continue diamond.
        push(&mut func, header, MovR, vec![v64(63), v64(59)]);
        push(&mut func, header, CmpRI, vec![v64(63), i(2048)]);
        push(&mut func, header, BCond, vec![i(CC_LO), b(g_a)]);
        push(&mut func, header, B, vec![b(exit)]);
        // g_a: load a[i], v = a[i]+k, then the OUTER select split.
        push(&mut func, g_a, MovR, vec![v64(66), v64(59)]);
        push(
            &mut func,
            g_a,
            Madd,
            vec![v64(73), v64(66), v64(40), v64(0)],
        );
        push(&mut func, g_a, LdrRI, vec![v(49), v64(73), i(0)]);
        if kind == 6 {
            // Use of the MERGED dest before the split: reads the PREVIOUS
            // iteration's value — the select model would be wrong here.
            push(&mut func, g_a, AddRR, vec![v(92), v(56), v(49)]);
        }
        if kind == 5 {
            // Stealth accumulator: acc += a[i] (writeback mid-chain, not latch).
            push(&mut func, g_a, AddRR, vec![v(90), v(91), v(49)]);
            push(&mut func, g_a, MovR, vec![v(91), v(90)]);
        }
        push(&mut func, g_a, AddRR, vec![v(52), v(49), v(58)]); // v = a[i]+k
        match kind {
            2 => {
                // Crossed bounds: outer tests `v > -100`, picks -100.
                push(&mut func, g_a, CmpRR, vec![v(52), v(57)]);
                push(&mut func, g_a, BCond, vec![i(CC_GT), b(arm_hi)]);
            }
            1 => {
                // Flipped polarity: `v < 100 ? 100 : ...`.
                push(&mut func, g_a, CmpRI, vec![v(52), i(100)]);
                push(&mut func, g_a, BCond, vec![i(CC_LT), b(arm_hi)]);
            }
            3 => {
                // Unsigned ordering: `v >u 100 ? 100 : ...`.
                push(&mut func, g_a, CmpRI, vec![v(52), i(100)]);
                push(&mut func, g_a, BCond, vec![i(8), b(arm_hi)]); // CC_HI
            }
            _ => {
                push(&mut func, g_a, CmpRI, vec![v(52), i(100)]);
                push(&mut func, g_a, BCond, vec![i(CC_GT), b(arm_hi)]);
            }
        }
        push(
            &mut func,
            g_a,
            B,
            vec![b(if single { arm_v } else { inner })],
        );
        // arm_hi: merged = the outer bound constant.
        push(
            &mut func,
            arm_hi,
            MovR,
            vec![v(56), if kind == 2 { v(57) } else { v(53) }],
        );
        push(&mut func, arm_hi, B, vec![b(join)]);
        if single {
            // Single-min shape: the fall-through arm assigns v directly.
            push(&mut func, arm_v, MovR, vec![v(56), v(52)]);
            push(&mut func, arm_v, B, vec![b(join)]);
        } else {
            // inner: pure compare block `v < LO` (crossed kind 2: `v < 100`).
            push(
                &mut func,
                inner,
                CmpRR,
                vec![v(52), if kind == 2 { v(53) } else { v(57) }],
            );
            push(&mut func, inner, BCond, vec![i(CC_LT), b(arm_lo)]);
            push(&mut func, inner, B, vec![b(arm_v)]);
            // arm_lo: d2 = LO; arm_v: d2 = v; ijoin: merged = d2.
            push(
                &mut func,
                arm_lo,
                MovR,
                vec![v(60), if kind == 2 { v(53) } else { v(57) }],
            );
            push(&mut func, arm_lo, B, vec![b(ijoin)]);
            push(&mut func, arm_v, MovR, vec![v(60), v(52)]);
            push(&mut func, arm_v, B, vec![b(ijoin)]);
            push(&mut func, ijoin, MovR, vec![v(56), v(60)]);
            push(&mut func, ijoin, B, vec![b(join)]);
        }
        // join: empty pass-through into the latch.
        push(&mut func, join, B, vec![b(latch)]);
        // Latch: store the merged value through a MovR copy, step, back-edge.
        push(
            &mut func,
            latch,
            Madd,
            vec![v64(95), v64(59), v64(40), v64(0)],
        );
        push(&mut func, latch, MovR, vec![v(70), v(56)]);
        push(&mut func, latch, StrRI, vec![v(70), v64(95), i(0)]);
        push(&mut func, latch, AddRI, vec![v64(99), v64(59), i(1)]);
        push(&mut func, latch, MovR, vec![v64(59), v64(99)]);
        push(&mut func, latch, B, vec![b(header)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, header);
        func.add_edge(header, g_a);
        func.add_edge(header, exit);
        func.add_edge(g_a, arm_hi);
        if single {
            func.add_edge(g_a, arm_v);
            func.add_edge(arm_v, join);
        } else {
            func.add_edge(g_a, inner);
            func.add_edge(inner, arm_lo);
            func.add_edge(inner, arm_v);
            func.add_edge(arm_lo, ijoin);
            func.add_edge(arm_v, ijoin);
            func.add_edge(ijoin, join);
        }
        func.add_edge(arm_hi, join);
        func.add_edge(join, latch);
        func.add_edge(latch, header);
        func.next_vreg = 512;
        func
    }

    #[test]
    fn chain_clamp_diamond_fires_smax_smin() {
        // The d12 in-place clamp: fires on regime A with per-sub-block
        // ADD + SMAX (lo) + SMIN (hi) and the IMMEDIATE bound materialized.
        let mut func = build_chain_clamp_loop(0);
        let mut pass = NeonMapPass::new();
        assert!(pass.run(&mut func), "clamp diamond chain should vectorize");
        assert_eq!(pass.fired(), 1);
        assert_paired_stores(&func);
        assert_eq!(count(&func, AArch64Opcode::NeonAddV), UNROLL, "a[i]+k");
        assert_eq!(
            count(&func, AArch64Opcode::NeonSmaxV),
            UNROLL,
            "smax(v, lo)"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonSminV),
            UNROLL,
            "smin(., hi)"
        );
        assert_eq!(
            count_ls_guard(&func),
            0,
            "in-place: regime A, no versioning"
        );
        assert_eq!(count(&func, AArch64Opcode::StrRI), 1, "scalar loop intact");
    }

    #[test]
    fn chain_clamp_inverted_polarity_bails() {
        // `v < 100 ? 100 : smax(v,-100)` is NOT a clamp (form 2 needs an inner
        // SMIN): trusting it would silently flip min<->max — must BAIL.
        let mut func = build_chain_clamp_loop(1);
        let mut pass = NeonMapPass::new();
        assert!(!pass.run(&mut func), "flipped outer polarity must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonSminV), 0);
    }

    #[test]
    fn chain_clamp_crossed_bounds_bails() {
        // Outer bound -100, inner bound 100: `lo <= hi` fails, and the min/max
        // composition does NOT equal the scalar nested select — must BAIL.
        let mut func = build_chain_clamp_loop(2);
        let mut pass = NeonMapPass::new();
        assert!(!pass.run(&mut func), "crossed clamp bounds must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonSmaxV), 0);
    }

    #[test]
    fn chain_unsigned_select_bails() {
        // A `u32` clamp compares UNSIGNED (`b.hi`): SMIN/SMAX order values by
        // SIGNED comparison and would mis-clamp any lane with the sign bit set —
        // must BAIL (stays scalar).
        let mut func = build_chain_clamp_loop(3);
        let mut pass = NeonMapPass::new();
        assert!(!pass.run(&mut func), "unsigned select ordering must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonSminV), 0);
    }

    #[test]
    fn chain_single_min_diamond_fires() {
        // `a[i] = if v>100 {100} else {v}` == smin(v, 100): fires with SMIN
        // only.
        let mut func = build_chain_clamp_loop(4);
        let mut pass = NeonMapPass::new();
        assert!(pass.run(&mut func), "single-min diamond should vectorize");
        assert_eq!(pass.fired(), 1);
        assert_eq!(count(&func, AArch64Opcode::NeonSminV), UNROLL, "smin only");
        assert_eq!(count(&func, AArch64Opcode::NeonSmaxV), 0, "no smax");
    }

    #[test]
    fn chain_stealth_accumulator_bails() {
        // A mid-chain `acc = acc + a[i]` is loop-carried scalar state the vector
        // loop would silently skip — the ITERATION-LOCALITY gate must BAIL.
        let mut func = build_chain_clamp_loop(5);
        let mut pass = NeonMapPass::new();
        assert!(!pass.run(&mut func), "stealth accumulator must BAIL");
        assert_eq!(pass.fired(), 0);
    }

    #[test]
    fn chain_select_dest_use_before_join_bails() {
        // A use of the merged select dest BEFORE the split reads the PREVIOUS
        // iteration's merged value — the select model would be wrong; BAIL.
        let mut func = build_chain_clamp_loop(6);
        let mut pass = NeonMapPass::new();
        assert!(
            !pass.run(&mut func),
            "pre-split use of select dest must BAIL"
        );
        assert_eq!(pass.fired(), 0);
    }
}
