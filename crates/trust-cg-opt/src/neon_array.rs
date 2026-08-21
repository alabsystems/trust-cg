// trust-cg-opt - SOUND NEON array-reduction vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON array-reduction vectorizer (`neon-array`)
//!
//! Vectorizes counted integer reduction loops whose term reads from **read-only
//! memory**, of the shape
//!
//! ```text
//! s = 0;  for i in 0..n (signed i < n):  s += TERM(load(a, i), load(b, i), ...)
//! ```
//!
//! where `s` is a **scalar** `i32` accumulator (a register / the return value,
//! never a memory location), the pointers `a, b, ...` are **only loaded** in the
//! loop (never stored), and `TERM` is a **lane-wise** integer function of the
//! loaded `i32` elements and 16-bit constants using `+  -  *  &  |  ^  <<  >>`
//! (plus the fused `s = madd(load_a, load_b, s)` = `s += load_a*load_b`, i.e.
//! dot product). Each loaded array is walked with paired NEON `LDP Qt1, Qt2`
//! post-index loads (32 bytes per instruction) and the
//! per-lane term is accumulated into `UNROLL = 4` independent `4 x i32` vector
//! accumulators (for ILP); at loop exit they are combined, horizontally reduced,
//! and the ORIGINAL scalar loop handles the `< 16` tail iterations.
//!
//! It runs **after** [`crate::neon_reduce`] (which handles *register*-computed
//! reductions and BAILS on any load) and **before** [`crate::reduction_split`].
//! It fires only on the shapes it can prove lane-wise-equivalent and BAILS
//! (leaving the loop untouched) on everything else. Disable with
//! `TRUST_CG_DISABLE_PASSES=neon_array`.
//!
//! ## Why this is SOUND
//!
//! Like [`crate::neon_reduce`], the transform is **purely additive**: it inserts
//! a vector main loop in front of the scalar loop and never edits the scalar
//! loop's instructions. The scalar loop is therefore correct by construction;
//! only the inserted vector loop plus the horizontal reduction need justifying.
//!
//! * **Loads are read-only ⇒ vectorizing them cannot change memory.** The pass
//!   BAILS on any store / call / atomic / unmodeled effect in the loop body
//!   (whitelist), so the only memory accesses are the recognized loads. Because
//!   the reduction target `s` is a **register** (not a store to a possibly-
//!   aliased array), aliasing *among the read pointers* is irrelevant — two
//!   reads never conflict. The only observable reordering is of the reduction's
//!   additions, which is sound by two's-complement add associativity /
//!   commutativity (the same argument as `reduction_split` / `neon_reduce`).
//!
//! * **The vector loads read exactly the memory the scalar loop reads.** Each
//!   recognized load is `a[i] = *(base + sext(i)*4)` (a `gep i32`). The vector
//!   guard enters the body only when `sext(iv) + (width-1) < sext(n)`
//!   (`width = 16`), computed in `i64` after sign-extending both `iv` and `n`
//!   from `i32` — so no overflow is possible and every lane index `iv..iv+15`
//!   satisfies `index < n`, i.e. is an index the scalar loop also accesses. The
//!   `LD1 {Vt.4S}` for accumulator `k` reads the 4 contiguous `i32` at
//!   `base + (iv + 4k)*4`, exactly the elements `a[iv+4k .. iv+4k+3]`.
//!
//! * **Per-lane the vector term equals the scalar term.** Every scalar op is
//!   mapped to the NEON `.4S` op proven per-lane-equivalent in
//!   `trust-cg-verify/src/vectorization_proofs.rs` (`ADD/SUB/MUL/AND/ORR/EOR`,
//!   `SHL/USHR/SSHR` immediate); a loaded leaf maps to the corresponding lane of
//!   its array's vector load; constants are identical in every lane.
//!
//! Each accumulator adds `vterm_k` every vector iteration over its own disjoint
//! set of lane indices, so combining the four accumulators (balanced vector
//! adds) and summing the four lanes reproduces `sum_{j in [iv0,V)} TERM(j) (mod
//! 2^32)` regardless of grouping — the reduction-split argument lifted into the
//! vector domain. The vector loop never writes the scalar `acc`, so at the exit
//! it still holds its pre-loop initial value; that partial sum is **added into**
//! `acc` (not overwritten), so a non-zero initial accumulator (`s = 5; for i: s
//! += a[i]`) is preserved. The unchanged scalar loop then adds `TERM(j)` for
//! `j in [V, n)` starting from that seed. QED.
//!
//! ## Fail-closed guards (BAIL preconditions)
//!
//! Every one of these must hold or the loop is left entirely to the scalar path
//! (see `Recognized::recognize`): a single innermost `{header, latch}` loop
//! with a dominating guard + preheader (the rotated shape `loop-latch-layout`
//! emits); a `+1` induction; the exact signed-`<` (cc=LT) exit test; a single
//! `i32` accumulator read ONLY by the reduction; an `s += TERM` (or fused
//! `s = madd(a,b,s)`) reduction; a `TERM` slice built only from allowed
//! lane-wise ops whose leaves are **recognized array loads** — for i32,
//! `LdrRI(base + sext(iv)*4, 0)`; for i64, `LdrRI(base + iv*8, 0)` (no sign
//! extension, `iv` already 64-bit) — with a loop-invariant `base`, or 16-bit
//! constants — and **at least one load** (pure register reductions are left to
//! `neon_reduce`); the induction usable as a term value only as an **AFFINE
//! IOTA leaf** (see below); and NO store / call / atomic / unrecognized op
//! anywhere in the loop body.
//!
//! ## AFFINE IOTA terms (the induction variable in the term)
//!
//! The term language admits the bare induction variable as an **affine iota
//! leaf**: `s += (i*3+7) ^ a[i]`, `s += (i+1) + a[i]`, etc. (mirrors
//! [`crate::neon_minmax`]'s iota extension; the machinery is the argmin index
//! tracking). The iv lowers to a per-accumulator POSITION VECTOR
//! `pos_k = splat(iv0) + [0..vf) + vf*k` advanced by `splat(width)` per
//! iteration, whose lane `l` holds EXACTLY the scalar iv value for the element
//! accumulator `k` folds into lane `l` — every add wraps mod 2^lane-width
//! identically to scalar iv arithmetic, so per lane `vector_term ==
//! scalar_term` exactly and the two's-complement add-reduction argument is
//! unchanged. Deliberately scoped to AFFINE iv terms: a product of two
//! iv-carrying factors (`i*i`) or a right-shift of an iv-carrying value BAILS
//! (`Recognized::subtree_uses_iv`). A term with no iv use emits no iota —
//! byte-identical output. `iv ± K` is further STRENGTH-REDUCED to its own
//! loop-carried position vector seeded `base ± K` (the per-iteration
//! `pos + splat(K)` add folds into the seed; see `shift_of_iv`). The
//! widening TRACK B is untouched (its term is a single narrow load).
//!
//! ## i64 (`.2D`) support
//!
//! `i64` reductions (`Gpr64` iv/acc/bound) are vectorized on the `.2D` path
//! (`2 x i64` lanes, `WIDTH = UNROLL*2 = 8`) for the **non-multiply** lane-wise
//! ops that exist at `.2D` — `add`, `sub`, `and`, `or`, `xor`, `shl`, `ushr`,
//! `sshr`. Any multiply in the term (`a[i]*b[i]`, `a[i]*c`, or a fused
//! dot-product `madd`) BAILS, because `.2D` has no integer multiply. Because
//! `i64` has no `i32→i64` sign-extension headroom, a **different** provably-sound
//! bounds guard is used — an unsigned-subtraction guard behind a signed
//! precheck (`main_bound = n-(WIDTH-1)` computed only when `n >= WIDTH`; the
//! vector loop runs while `iv <u main_bound`; a signed `n < WIDTH` precheck
//! skips the vector loop, matching the scalar `slt` loop's 0-iteration behaviour
//! when `n <= 0` or `n` is negative-as-signed). See `apply_i64` for the full
//! argument.
//!
//! ## Widening byte/half reductions (`s(i32) += ext(a[i8/i16][i])`, TRACK B)
//!
//! When the `i32` reduction's TERM is EXACTLY a widening narrow load —
//! `Uxtb/Sxtb(LdrbRI(base + sext(iv)))` (i8) or `Uxth/Sxth(LdrhRI(base +
//! sext(iv)*2))` (i16) — or EXACTLY the SWAR `ctpop` of a ZERO-extended byte
//! load (`s += popcount(a_u8[i])`), the loop takes the WIDENING path
//! (`apply_widen`): each 128-bit `LDP`-loaded Q register holds 16 (i8) / 8
//! (i16) elements, which are collapsed to 4 x i32 per-group sums with the
//! FAITHFULLY-PROVEN pairwise-widening adds — `UADDLP` (zext) or `SADDLP`
//! (sext) `.16B→.8H→.4S` (i8) / `.8H→.4S` (i16) — and accumulated into the
//! usual four `.4S` accumulators. The byte-popcount kernel instead uses the
//! proven `CNT.16B` + `UDOT` accumulate (or the `CNT` + `UADDLP` chain when
//! UDOT is disabled).
//!
//! WHY THE WIDENING CHAIN IS EXACT (the overflow/signedness argument): each
//! `.4S` output lane covers one aligned 4-byte group (i8) / 2-halfword group
//! (i16) of the loaded vector.
//! * zext i8: `UADDLP .16B→.8H` computes `zext16(b0)+zext16(b1) <= 510` — exact
//!   in 16 bits; `UADDLP .8H→.4S` computes the 4-byte group sum `<= 1020` —
//!   exact in 32 bits. So the lane equals `zext32(b0)+…+zext32(b3)` exactly,
//!   the very values the scalar loop adds.
//! * sext i8: `SADDLP .16B→.8H` computes `sext16(b0)+sext16(b1) in [-256,254]` —
//!   exact in i16; `SADDLP .8H→.4S` gives the group sum `in [-512,508]` — exact
//!   in i32, equal to `sext32(b0)+…+sext32(b3) mod 2^32`.
//! * zext/sext i16: the single `UADDLP/SADDLP .8H→.4S` pair-sum is `<= 131070` /
//!   `in [-65536,65534]` — exact in 32 bits, equal to the two `zext32/sext32`
//!   element values' sum.
//! * popcount u8: `CNT.16B` gives `popcount(b)` per byte (`= ctpop(zext32(b))`,
//!   the scalar term — zext adds no set bits, which is WHY only `Uxtb` loads
//!   are accepted here: a SIGN-extended byte would contribute up to 24 extra
//!   set bits and BAILS); the `UADDLP` chain (or the `UDOT` ones-accumulate)
//!   sums the 4 per-byte counts per lane, `<= 32` — exact.
//!   From there the equivalence argument is the unchanged i32 one: the `.4S`
//!   accumulator adds wrap mod 2^32 exactly like the scalar `i32` accumulator,
//!   and two's-complement add associativity/commutativity lets the per-group /
//!   per-accumulator regrouping reproduce the scalar left-fold mod 2^32. The
//!   bounds guard is the i32 sign-extension guard with `WIDTH = 64` (i8) / `32`
//!   (i16). Any other term shape (extra arithmetic around the ext, sign-extended
//!   popcount, mixed widths) BAILS to the scalar loop.
//!
//! ## Widening ABS-SUM (`s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))`, TRACK D)
//!
//! The bridge lowers `s: i64 += (a[i].wrapping_add(r)).unsigned_abs() as i64`
//! (over an i32 array, `r` loop-invariant) as a forward CHAIN whose body holds a
//! branchy two's-complement absolute value — an ABS DIAMOND
//! (`recognize_abs_diamond`): `CmpRI(x, #0); BCond(LT)` splitting to a
//! `0 - x` arm and an identity arm that both write one "phi" register, joined
//! and then ZERO-extended (`Uxtw`) into the i64 accumulator. When the chain walk
//! finds EXACTLY one such diamond behind the loop's `iv <u N` guard and the
//! reduction term is EXACTLY `Uxtw(copy*(phi))` with `x` a recognized i32
//! `a[iv]` load (optionally `+` one loop-invariant i32 addend), the loop lowers
//! via `apply_abs_widen`: `ADD.4S(q, dup(inv))` + the FAITHFULLY-PROVEN
//! `ABS.4S` + the FAITHFULLY-PROVEN pairwise widening ACCUMULATE `UADALP` into
//! `.2D` i64 accumulators — ONE op per Q under LLVM's `abs.4s + uaddw.2d +
//! uaddw2.2d` pair (all opcodes gate-credited — see the soundness
//! walkthrough on `apply_abs_widen`, including why the extension MUST be the
//! unsigned UADALP, why `i32::MIN` lanes are exact, and why the adjacent-pair
//! grouping is a pure mod-2^64 reassociation). Any deviation — a `Sxtw`
//! root, extra arm instructions, a third writer of the phi, a second diamond,
//! any other term consuming the diamond — BAILS to the scalar loop.

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
/// NEON arrangement operand code for `.16B` (CNT input; UADDLP `.16B→.8H` input).
const ARR_B16: i64 = 1;
/// NEON arrangement operand code for `.8H` (UADDLP `.8H→.4S` input).
const ARR_H8: i64 = 3;

/// Whether the `ctpop(i32)` reduction lowers via the proven NEON popcount fold
/// (`CNT.16B` + two `UADDLP`) instead of the per-lane SWAR `.4S` chain. Gated on
/// the FAITHFUL `NeonCntV`/`NeonUaddlpV` proofs (neon_lowering_proofs) existing
/// and the coverage gate staying green (trust-cg-verify enforces 100/100). The
/// fold is a drop-in for the SWAR term (same per-i32-lane popcount), just far
/// cheaper. If those proofs were ever retracted, flip this to `false` to
/// fail-closed to the already-correct SWAR chain — never emit unproven codegen.
const CTPOP_NEON_ENABLED: bool = true;
/// Whether a popcount reduction whose TERM is EXACTLY `ctpop(x)` accumulates via
/// the proven `UDOT.4S` fast path (`CNT.16B` then `UDOT(acc, cnt, ones.16B)` — 2
/// compute ops, matching clang) instead of `CNT` + two `UADDLP` + `ADD` (4 ops).
/// With an all-ones byte vector, each i32 lane of the UDOT accumulates the sum
/// of its 4 per-byte popcounts: `acc[i] += popcount(x[i])` — algebraically
/// identical to adding the UADDLP-folded counts. Gated on the FAITHFUL
/// `NeonUdotV` proof (neon_lowering_proofs::proof_neon_udotv_lanewise_4s: the
/// D-pair obligation models the ACCUMULATE — dot-without-accumulate, SDOT
/// sign-extension, and wrong-byte-group all REFUTE) and the coverage gate
/// staying green. If that proof were ever retracted, flip this to `false` to
/// fail-closed to the (kept, proven, slower) CNT+UADDLP chain — never emit
/// unproven codegen. Nested `ctpop` uses (e.g. `2*ctpop(x)`) always take the
/// UADDLP chain: UDOT is an accumulate and only sound at the term root.
///
/// FEAT_DotProd is assumed present (every Apple M-series has it) — the same
/// Apple-M target assumption as the LSE atomics; there is no per-feature
/// machinery in the backend to gate on.
const CTPOP_UDOT_ENABLED: bool = true;
/// AArch64 condition code for signed less-than (`LT`).
const CC_LT: i64 = 11;
/// AArch64 condition code for unsigned less-than (`LO`/`CC`).
const CC_LO: i64 = 3;
/// AArch64 condition code for equal (`EQ`).
const CC_EQ: i64 = 0;
/// AArch64 condition code for signed greater-than-or-equal (`GE`).
const CC_GE: i64 = 10;
/// AArch64 condition code for unsigned greater-than-or-equal (`HS`/`CS`).
const CC_HS: i64 = 2;
/// Byte size of an `i32` array element.
const ELEM_BYTES: i64 = 4;
/// Byte size of an `i64` array element (`.2D` path).
const ELEM_BYTES_I64: i64 = 8;
/// Number of independent vector accumulators (ILP). `UNROLL * VF` i32 lanes are
/// processed per vector iteration (16 with VF=4); `UNROLL * VF_I64` i64 lanes
/// (8 with VF_I64=2) on the `.2D` path.
const UNROLL: usize = 4;
/// Accumulator count for the WIDENING DOT (TRACK C, [`apply_dot_widen`]) ONLY.
/// The SMLAL/UMLAL `.2D` accumulate latency is ~3cy and each accumulator eats
/// two chained MACs per iteration, so 4 accumulators leave the loop
/// latency-bound ~2x off the MAC/load throughput floor; 8 accumulators reach
/// it (measured on Apple M4: 6.27 -> ~3.4 cy/16elem). 8 accs + the in-flight
/// loaded Q's stay within the 24 non-callee-saved FPR128s (v0-v7, v16-v31)
/// because the body interleaves loads with the MACs that consume them
/// (pair-group emission: peak ~12 live Q's). The OTHER tracks keep
/// [`UNROLL`] = 4: the plain i32 dot (TRACK A) is load-bound and measurably
/// regresses when widened, and the abs-sum (TRACK D) is vector-throughput
/// bound where extra accumulators buy nothing.
const UNROLL_DOT: usize = 8;

/// The `neon-array` machine pass.
#[derive(Default)]
pub struct NeonArrayPass {
    /// Number of loops vectorized in the last run (diagnostics/tests).
    fired: usize,
}

impl NeonArrayPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonArrayPass {
    fn name(&self) -> &str {
        "neon-array"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    // Share the AnalysisCache's CFG-derived DomTree + LoopAnalysis instead of
    // recomputing them (the neon recognizer family each rebuilt its own — up to
    // 11x redundant DomTree/LoopAnalysis per function). Both analyses depend only
    // on the CFG, which the cache invalidates on any CFG-fingerprint change, so a
    // shared instance is byte-for-byte identical to a fresh recompute here.
    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loops = analyses.loop_analysis(func).clone();
        let changed = {
            let dom = analyses.domtree(func);
            self.run_core(func, dom, &loops)
        };
        // On a FIRE we mutate the CFG; drop the shared analyses so no downstream
        // pass reads a stale loop tree. Zero cost in the common no-fire path
        // (the compile-time hot path); guarantees byte-identical output vs a
        // fresh per-pass recompute regardless of cfg-fingerprint precision.
        if changed {
            analyses.invalidate();
        }
        changed
    }
}

impl NeonArrayPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;

        // Recognize all candidate loops read-only first; applying a plan only
        // *adds* blocks (never renumbers existing block/inst ids or edits other
        // loops' blocks), so recognized data for other loops stays valid.
        let mut plans = Vec::new();
        let boi_t0 = boi_timing_enabled().then(|| {
            (
                std::time::Instant::now(),
                BOI_NANOS.load(std::sync::atomic::Ordering::Relaxed),
                BOI_CALLS.load(std::sync::atomic::Ordering::Relaxed),
                BDM_NANOS.load(std::sync::atomic::Ordering::Relaxed),
                BDM_CALLS.load(std::sync::atomic::Ordering::Relaxed),
            )
        });
        // `build_def_map` walks every block's instruction list. It was rebuilt
        // inside EVERY `recognize` call, i.e. once per natural loop, and measured
        // at 99.6% of the entire recognition phase (110.5ms of 110.9ms on
        // many_fns n=200). The sweep is explicitly read-only — applying a plan
        // happens in the second loop below — so one map is valid throughout.
        let def_map = build_def_map(func);
        for lp in loops.all_loops() {
            if let Some(rec) =
                Recognized::recognize(func, dom, &def_map, lp.header, lp.latch, &lp.body)
            {
                plans.push(rec);
            }
        }
        if let Some((t0, n0, c0, d0, dc0)) = boi_t0 {
            let total_us = t0.elapsed().as_micros() as u64;
            let boi_us = (BOI_NANOS.load(std::sync::atomic::Ordering::Relaxed) - n0) / 1000;
            let calls = BOI_CALLS.load(std::sync::atomic::Ordering::Relaxed) - c0;
            let bdm_us = (BDM_NANOS.load(std::sync::atomic::Ordering::Relaxed) - d0) / 1000;
            let bdm_calls = BDM_CALLS.load(std::sync::atomic::Ordering::Relaxed) - dc0;
            let pct = |x: u64| {
                if total_us > 0 {
                    100.0 * x as f64 / total_us as f64
                } else {
                    0.0
                }
            };
            eprintln!(
                "TCG_TIME_BOI fn={} recognize_total={}us block_of_inst={}us/{}calls/{:.1}% build_def_map={}us/{}calls/{:.1}%",
                func.name,
                total_us,
                boi_us,
                calls,
                pct(boi_us),
                bdm_us,
                bdm_calls,
                pct(bdm_us),
            );
            eprintln!(
                "TCG_TIME_SIBLINGS bytesum_build_def_map={}us/{}calls bitrev_build_def_map={}us/{}calls",
                crate::neon_bytesum::BYTESUM_NANOS.load(std::sync::atomic::Ordering::Relaxed)
                    / 1000,
                crate::neon_bytesum::BYTESUM_CALLS.load(std::sync::atomic::Ordering::Relaxed),
                crate::neon_bitrev::BITREV_NANOS.load(std::sync::atomic::Ordering::Relaxed) / 1000,
                crate::neon_bitrev::BITREV_CALLS.load(std::sync::atomic::Ordering::Relaxed),
            );
            eprintln!(
                "TCG_TIME_RD inblock={}us/{}hits fixpoint={}us/{}miss memo_hits={}",
                crate::reaching_const::RD_INBLOCK_NANOS.load(std::sync::atomic::Ordering::Relaxed)
                    / 1000,
                crate::reaching_const::RD_INBLOCK_HITS.load(std::sync::atomic::Ordering::Relaxed),
                crate::reaching_const::RD_FIXPOINT_NANOS.load(std::sync::atomic::Ordering::Relaxed)
                    / 1000,
                crate::reaching_const::RD_FIXPOINT_HITS.load(std::sync::atomic::Ordering::Relaxed),
                crate::reaching_const::RD_MEMO_HITS.load(std::sync::atomic::Ordering::Relaxed),
            );
            eprintln!(
                "TCG_TIME_TAIL farray={}us/{} fill={}us/{} strided={}us/{} macrow={}us/{}",
                crate::neon_farray::FARRAY_NANOS.load(std::sync::atomic::Ordering::Relaxed) / 1000,
                crate::neon_farray::FARRAY_CALLS.load(std::sync::atomic::Ordering::Relaxed),
                crate::neon_fill::FILL_NANOS.load(std::sync::atomic::Ordering::Relaxed) / 1000,
                crate::neon_fill::FILL_CALLS.load(std::sync::atomic::Ordering::Relaxed),
                crate::strided_store_unroll::STRIDED_NANOS
                    .load(std::sync::atomic::Ordering::Relaxed)
                    / 1000,
                crate::strided_store_unroll::STRIDED_CALLS
                    .load(std::sync::atomic::Ordering::Relaxed),
                crate::mac_row_unroll::MACROW_NANOS.load(std::sync::atomic::Ordering::Relaxed)
                    / 1000,
                crate::mac_row_unroll::MACROW_CALLS.load(std::sync::atomic::Ordering::Relaxed),
            );
            eprintln!(
                "TCG_TIME_VEC vectorize_build_def_map={}us/{}calls",
                crate::vectorize::VEC_BDM_NANOS.load(std::sync::atomic::Ordering::Relaxed) / 1000,
                crate::vectorize::VEC_BDM_CALLS.load(std::sync::atomic::Ordering::Relaxed),
            );
        }

        let mut changed = false;
        for rec in plans {
            let applied = if rec.widen.is_some() {
                apply_widen(func, &rec)
            } else if rec.dot.is_some() {
                apply_dot_widen(func, &rec)
            } else if rec.abs.is_some() {
                apply_abs_widen(func, &rec)
            } else if rec.is_i64 {
                apply_i64(func, &rec)
            } else {
                apply(func, &rec)
            };
            if applied {
                self.fired += 1;
                changed = true;
            }
        }
        if changed && std::env::var("TRUST_CG_DUMP_NEONARRAY").is_ok() {
            eprintln!("[neon-array] fn={} vectorized={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// The `TERM` value to lower per lane.
#[derive(Clone, Copy)]
enum Term {
    /// A single SSA value defining the whole term.
    Value(VReg),
    /// A fused `a * b` (from a reduction expressed as `madd(a, b, acc)`).
    MulPair(VReg, VReg),
    /// The per-iteration term of a REASSOCIATED reduction `acc = (acc OP x) OP y`,
    /// where OP is the (associative + commutative) reduction operator. clang
    /// left-folds `acc ⊕ a[i] ⊕ (i+1)` as `(acc ⊕ a[i]) ⊕ (i+1)`, nesting `acc`
    /// one level deep; reassociation gives the true per-iteration contribution
    /// `x OP y` = `a[i] OP (i+1)`, combined with the SAME reduction op. Lowered by
    /// combining the two sub-terms with `reduce_op.vector_op()`.
    OpPair(VReg, VReg),
}

/// The widening narrow-element load kinds recognized by the WIDENING
/// reduction mode (`s(i32) += ext(a[i8/i16][i])`). The extend opcode and the
/// load opcode must agree (fail-closed): `Uxtb`/`Sxtb` over `LdrbRI`,
/// `Uxth`/`Sxth` over `LdrhRI`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum WidenKind {
    /// `Uxtb(LdrbRI(base + sext(iv), 0))` — u8 zero-extended to i32.
    ZextB,
    /// `Sxtb(LdrbRI(base + sext(iv), 0))` — i8 sign-extended to i32.
    SextB,
    /// `Uxth(LdrhRI(base + sext(iv)*2, 0))` — u16 zero-extended to i32.
    ZextH,
    /// `Sxth(LdrhRI(base + sext(iv)*2, 0))` — i16 sign-extended to i32.
    SextH,
}

impl WidenKind {
    /// Signed (sext) kinds lower through the proven `SADDLP`; unsigned (zext)
    /// through the proven `UADDLP`.
    fn is_signed(self) -> bool {
        matches!(self, WidenKind::SextB | WidenKind::SextH)
    }
    /// Byte kinds need the two-step `.16B→.8H→.4S` chain; half kinds one step.
    fn is_byte(self) -> bool {
        matches!(self, WidenKind::ZextB | WidenKind::SextB)
    }
    /// Bytes per array element (1 or 2).
    fn elem_bytes(self) -> i64 {
        if self.is_byte() { 1 } else { 2 }
    }
    /// Elements per 128-bit Q register (16 bytes / element size).
    fn lanes_per_q(self) -> i64 {
        if self.is_byte() { 16 } else { 8 }
    }
}

/// A recognized WIDENING reduction plan: the term is exactly one widening
/// narrow load (`pop == false`, the widening sum) or exactly the SWAR `ctpop`
/// of a ZERO-extended byte load (`pop == true`, the byte-popcount kernel).
#[derive(Clone, Copy)]
struct WidenPlan {
    kind: WidenKind,
    /// Term is `ctpop(zext8(load))` (lower via `CNT.16B`) rather than the bare
    /// extended load. Only `WidenKind::ZextB` — popcount is byte-local only
    /// under ZERO extension (sext would add up to 24 set bits).
    pop: bool,
    /// The single loop-invariant array base pointer.
    base: VReg,
}

/// A recognized WIDENING DOT plan (TRACK C): the i64 reduction term is exactly
/// `MulPair(ext(a_i32[i]), ext(b_i32[i]))` — an i32->i64 widening multiply of two
/// i32 array loads — lowered via the widening multiply-accumulate-long
/// `SMLAL.2D + SMLAL2.2D` (signed) or `UMLAL.2D + UMLAL2.2D` (unsigned) into `.2D`
/// i64 accumulators. The `.2D` path has no NATIVE integer multiply, so this
/// WIDENING MAC is the only multiply shape the i64 vectorizer can lower.
#[derive(Clone, Copy)]
struct DotPlan {
    /// `true` => both factors are `Sxtw` (SIGNED) -> SMLAL/SMLAL2; `false` => both
    /// `Uxtw` (UNSIGNED) -> UMLAL/UMLAL2. MIXED signedness has no single widening
    /// MAC and BAILS at recognition.
    signed: bool,
    /// The two DISTINCT (or, for `a[i]*a[i]`, coincident) loop-invariant i32 array
    /// base pointers, in operand order (`a`, `b`).
    base_a: VReg,
    base_b: VReg,
}

/// A recognized WIDENING ABS-SUM plan (TRACK D): the i64 reduction term is
/// exactly `Uxtw(abs_bits(a_i32[i] [+ inv]))` — the ZERO-extended
/// two's-complement absolute-value bit pattern of an i32 array element
/// (optionally shifted by one loop-invariant i32 addend first), computed by the
/// chain's ABS DIAMOND ([`AbsDiamond`]). Lowered by [`apply_abs_widen`] via
/// `ADD.4S` + `ABS.4S` + the pairwise widening `UADALP` accumulate into `.2D`
/// i64 accumulators.
#[derive(Clone, Copy)]
struct AbsPlan {
    /// The single loop-invariant i32 array base pointer.
    base: VReg,
    /// Loop-invariant i32 addend applied BEFORE the abs (`abs(a[i] + inv)`),
    /// broadcast with the proven `NeonDupGen`; `None` = plain `abs(a[i])`.
    inv: Option<VReg>,
}

/// The associative + commutative reduction operator `acc = acc OP term`.
///
/// All three share identity **0** (so the `MOVI 0` vector-accumulator init is
/// reused unchanged) and reorder soundly across the 4 disjoint-slice
/// accumulators + horizontal fold — the same argument as [`crate::reduction_split`]:
/// `Add` wraps mod 2^w, `Xor` is its own inverse, `Or` is idempotent; each is
/// commutative and associative so any grouping of the elements (plus the pre-loop
/// seed folded in at exit) reproduces the scalar left-fold. `And` is deliberately
/// EXCLUDED — its identity is all-ones, not 0, so it cannot share the zeroed init.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ReduceOp {
    Add,
    Xor,
    Or,
}

impl ReduceOp {
    /// NEON lane-wise vector form (`.4S`/`.2D`) used for the per-iteration
    /// accumulate and the balanced accumulator combine at loop exit.
    fn vector_op(self) -> AArch64Opcode {
        match self {
            ReduceOp::Add => AArch64Opcode::NeonAddV,
            ReduceOp::Xor => AArch64Opcode::NeonEorV,
            ReduceOp::Or => AArch64Opcode::NeonOrrV,
        }
    }
    /// Scalar GPR form used for the horizontal lane fold and seeding the vector
    /// partial into the (possibly non-zero pre-loop) scalar accumulator.
    fn scalar_op(self) -> AArch64Opcode {
        match self {
            ReduceOp::Add => AArch64Opcode::AddRR,
            ReduceOp::Xor => AArch64Opcode::EorRR,
            ReduceOp::Or => AArch64Opcode::OrrRR,
        }
    }
}

/// A fully validated, lane-wise-vectorizable array-reduction loop.
struct Recognized {
    /// The reduction operator `acc = acc OP term` (Add / Xor / Or).
    reduce_op: ReduceOp,
    /// Preheader-guard block reached once before the loop.
    guard: BlockId,
    /// ROTATED shape only: the loop's true EXIT block. The scalar tail is a clang
    /// do-while (`cmp iv+1,bound; b.eq exit`) that is sound only when entered with
    /// `iv < bound`. When the vector loop consumes ALL `n` elements (n a multiple
    /// of the vector width ⇒ remainder 0), `apply` must route the vector exit here
    /// — NOT into the do-while, which would read `a[n]` and loop forever (iv==n is
    /// never == n by the `+1` test). `None` for the NATIVE shape (its `guard` is a
    /// top-test that re-checks `iv < bound` and is safe with remainder 0).
    rotated_exit: Option<BlockId>,
    /// Block that branches into `guard`.
    preheader: BlockId,
    /// The `preheader` terminator instruction targeting `guard`.
    preheader_term: InstId,
    /// Loop-carried induction register (`+1` each iteration, `i32`).
    iv: VReg,
    /// Loop-carried accumulator register (`i32`).
    acc: VReg,
    /// The accumulator WRITEBACK SOURCE (`acc = acc_wb_src` in the latch; = the
    /// header's `acc OP term` result). In the ROTATED shape the loop EXIT reads
    /// THIS vreg (the exit leaves from the header, after `acc_wb_src` is computed
    /// but before the latch copies it into `acc`). When the vector fully consumes
    /// `n` and `apply` branches straight to the exit, the drain must seed
    /// `acc_wb_src` (not just `acc`) or the exit reads a stale value. For the i32
    /// path regalloc usually coalesces `acc`/`acc_wb_src` into one register; for
    /// i64 they are distinct — so the seed copy is mandatory. Unused on the NATIVE
    /// path (no exit routing).
    acc_wb_src: VReg,
    /// Loop bound register (`iv < bound`, `i32`).
    bound: VReg,
    /// The RECONSTRUCTED compile-time value of `bound`, set when (and only
    /// when) the register route cannot work — the bound is materialized
    /// INSIDE the loop (clang's constant trip count: an in-loop `Movz`+`Movk`
    /// chain whose def does not dominate the vectorizer preheader). Proven by
    /// the sound reaching-definitions fold at the loop's exit compare
    /// ([`crate::reaching_const::unique_reaching_const`]) and validated to
    /// `[1, i32::MAX]` (positive: the rotated do-while's ≥1-trip contract;
    /// i32-range: the `.4S` sign-extension guard arithmetic stays exact).
    /// When set, the apply paths materialize this value FRESH in the
    /// preheader and never read `bound` at runtime.
    bound_const: Option<i64>,
    /// The step instruction `iv_src = AddRR/AddRI(iv, +1)` proven by (R3).
    /// [`Self::node_ok`] / [`lower`] use it to admit the step value `iv+1`
    /// as a SHIFTED AFFINE IOTA leaf even when the `+1` operand's vreg id is
    /// multi-def function-wide (isel reuses ids, so `const_value`'s naive
    /// def-map lookup fails; the step was instead proven by the reaching-def
    /// fold at this instruction).
    step_inst: Option<InstId>,
    /// The per-iteration term to lower.
    term: Term,
    /// True when the reduction is `i64` (`Gpr64` iv/acc/bound), lowered on the
    /// `.2D` path with the unsigned-subtraction bounds guard. False = `i32`
    /// (`Gpr32`, `.4S`, sign-extension guard).
    is_i64: bool,
    /// Global def map (`vreg id -> defining InstId`).
    def: HashMap<u32, InstId>,
    /// Instruction ids that live inside the loop body.
    loop_insts: HashSet<InstId>,
    /// Map from a recognized load's result vreg id to its (loop-invariant) base
    /// pointer register. Every leaf of `term` that is not a constant is one of
    /// these loads.
    loads: HashMap<u32, VReg>,
    /// Distinct base pointers referenced by `term`'s loads, in first-seen order
    /// (deterministic emission).
    bases: Vec<VReg>,
    /// Set when the loop is a WIDENING byte/half reduction (see [`WidenPlan`]);
    /// mutually exclusive with `is_i64`. Lowered by [`apply_widen`].
    widen: Option<WidenPlan>,
    /// Set when the loop is an i64 WIDENING DOT (see [`DotPlan`]): `is_i64` with a
    /// `MulPair(ext(a_i32[i]), ext(b_i32[i]))` term, lowered via SMLAL/UMLAL by
    /// [`apply_dot_widen`]. Mutually exclusive with `widen`.
    dot: Option<DotPlan>,
    /// Set when the loop is an i64 WIDENING ABS-SUM (see [`AbsPlan`]): `is_i64`
    /// with the term `Uxtw(abs_bits(a_i32[i] [+ inv]))` routed through the
    /// chain's ABS DIAMOND, lowered via ADD.4S + ABS.4S + UADALP by
    /// [`apply_abs_widen`]. Mutually exclusive with `widen`/`dot`.
    abs: Option<AbsPlan>,
    /// Set by [`Self::node_ok`] when the term references the induction variable
    /// as an AFFINE IOTA LEAF (`c*iv + d`, e.g. `(i*3+7) ^ a[i]`). Drives whether
    /// [`apply`] / [`apply_i64`] emit the per-lane position machinery; a term
    /// with no iv use stays byte-identical to before. Never set on the widening
    /// path (its term is a single narrow load).
    uses_iv: bool,
}

/// Opcodes permitted anywhere in the loop body. Anything else ⇒ BAIL (rules out
/// stores/calls/atomics/division and any unmodeled effect). `LdrRI` (a plain
/// register+0 load) and its address arithmetic (`Sxtw`, `Madd`) are permitted in
/// addition to [`crate::neon_reduce`]'s register-only whitelist; the loads must
/// still pass the exact `a[i]` address check in [`Recognized::load_base`].
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
            | Movk
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
            | LdrbRI
            | LdrhRI
            | Uxtb
            | Sxtb
            | Uxth
            | Sxth
    )
}

fn vreg_of(op: &MachOperand) -> Option<VReg> {
    match op {
        MachOperand::VReg(v) => Some(*v),
        _ => None,
    }
}

/// If `v` is `Uxtw(n)` / `Sxtw(n)` (an i32->i64 widening), return the i32 source
/// `n`. Used to route a MIXED (i32 acc, i64-widened index) rotated reduction
/// through the i32 `.4S` path: the widened bound is computed inside the loop's
/// GUARD block (so it does not dominate the vectorizer's preheader), but its i32
/// source `n` is computed earlier (a function arg / entry value that DOES
/// dominate) and is exactly what the i32 apply path re-`Sxtw`s.
fn ext_source(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<VReg> {
    let inst = func.inst(*def.get(&v.id)?);
    if matches!(inst.opcode, AArch64Opcode::Uxtw | AArch64Opcode::Sxtw) {
        vreg_of(&inst.operands[1])
    } else {
        None
    }
}

/// Recognize the ROTATED (clang -O1, folded at O2) header exit test and return
/// the loop bound.
///
/// Requires the header to END with EXACTLY (positions p-1, p):
/// ```text
///   CmpRR(iv+1, bound)          ; the increment vs the bound
///   BCond(EQ|GE) -> <exit>      ; leave the loop iff iv+1 reaches bound
/// ```
/// (the O2 peephole folds clang's `CSet(EQ); CmpRI(#0); BCond(NE)` boolean-
/// materialize idiom into this direct compare-branch). The CmpRR must be
/// IMMEDIATELY before the BCond so it is the flag producer (no intervening
/// clobber). The compared value must be `iv_src` (= iv+1, the step); with iv
/// starting at 0 and stepping +1, `iv+1` reaches `bound` EXACTLY, so "leave when
/// iv+1 == bound" (EQ) or "iv+1 >= bound" (GE) is the counted trip `[0, bound)` —
/// the identical loop, bottom-tested in the header instead of the latch. ANY
/// deviation (other CC, non-adjacent compare, compared value not iv+1, exit
/// target inside the loop) returns None — fail-closed, leaving the loop scalar.
fn recognize_rotated_header_exit(
    func: &MachFunction,
    header: BlockId,
    body: &HashSet<BlockId>,
    _iv: VReg,
    iv_src: VReg,
) -> Option<(VReg, BlockId, InstId)> {
    let insts = &func.block(header).insts;
    // The exit BCond: a conditional branch leaving the loop body.
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
        return None; // only "leave when iv+1 (>)= bound" — the counted [0,bound)
    }
    // The out-of-body target is the loop's true EXIT block (where the scalar tail
    // terminates). apply routes the vector exit here when the vector consumes ALL
    // `n` elements (remainder 0), instead of falling into the do-while scalar tail.
    let exit = *branch_targets(bcond).iter().find(|t| !body.contains(t))?;
    // The flag producer must be the CmpRR immediately before it.
    let cmp_id = insts[p - 1];
    let cmp = func.inst(cmp_id);
    if cmp.opcode != AArch64Opcode::CmpRR {
        return None;
    }
    if vreg_of(&cmp.operands[0])? != iv_src {
        return None; // must compare the STEP value (iv+1), else trip count differs
    }
    // The compare's InstId is returned so the caller can, when the bound's def
    // does not dominate the preheader, attempt the SOUND reaching-def constant
    // reconstruction AT THIS USE POINT (the in-loop `Movz`+`Movk` trip count).
    Some((vreg_of(&cmp.operands[1])?, exit, cmp_id))
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

/// Shift-zero `Movz` constant value of `val`, if any (may be defined anywhere
/// the global def map can see, e.g. the preheader). The proof-covered release
/// subset permits the 2-operand form and an explicit `LSL #0`; nonzero shifts
/// are non-emittable and must not be normalized by this consumer.
fn const_value(func: &MachFunction, def: &HashMap<u32, InstId>, val: VReg) -> Option<i64> {
    let inst = func.inst(*def.get(&val.id)?);
    if inst.opcode == AArch64Opcode::Movz
        && let Some(v) = inst.operands.get(1).and_then(imm_of)
        && (0..=0xFFFF).contains(&v)
    {
        match inst.operands.len() {
            2 => return Some(v),
            3 if imm_of(&inst.operands[2]) == Some(0) => return Some(v),
            _ => {}
        }
    }
    None
}

/// Reconstruct a ROTATED loop's compile-time constant bound: the value the
/// compared bound register is GUARANTEED to hold at the exit `CmpRR`, proven
/// by the sound reaching-definitions fold
/// ([`crate::reaching_const::unique_reaching_const`] — exactly one reaching
/// def, an isel `Movz`(+`Movk`) chain, no other in-loop redefinition). The
/// value is restricted to `[1, i32::MAX]`: positive so the do-while's
/// ≥1-trip contract holds, i32-range so the `.4S` path's sign-extension
/// guard arithmetic stays exact (and conservatively small for the i64 path).
/// `None` ⇒ the caller BAILS to the scalar loop.
fn reconstruct_const_bound(func: &MachFunction, bound_cmp: Option<(VReg, InstId)>) -> Option<i64> {
    let (raw, cmp_id) = bound_cmp?;
    let k = crate::reaching_const::unique_reaching_const(func, cmp_id, raw)?;
    (1..=i32::MAX as i64).contains(&k).then_some(k)
}

/// The upper limit of a bounds-guarded `while i<N` chain diamond: either a limit
/// REGISTER (`CmpRR(iv, N)` — the array-length register CSE folds every guard
/// onto, the form `neon_map` fires on) or a compile-time CONSTANT
/// (`CmpRI(iv, Imm(N))` — what the bridge emits for a FIXED-SIZE array whose
/// length is a literal, e.g. `[i32; 2048]`). Generalizing over both is the
/// crucial superset `neon_map`'s register-only guard lacks: d09's `for i in
/// 0..2048` folds the limit to an IMMEDIATE, so a naive register-only mirror
/// would bail.
#[derive(Clone, Copy)]
enum ChainBound {
    Reg(VReg),
    Const(i64),
}

/// Recognize a block's terminating array-bounds-check diamond
/// `Cmp(x, N); BCond(LO, t_lo); B(t_b)` (the last three instructions), where the
/// `b.lo`-taken target `t_lo` is IN the loop `body` (the `iv <u N` continue edge)
/// and the fall-through `t_b` is OUT of the body (the panic/exit edge). Accepts
/// BOTH `CmpRR(x, N_reg)` and `CmpRI(x, Imm(N))`, returning the compared value
/// `x`, the [`ChainBound`], the in-body target, and the compare's `InstId` (the
/// use point for a possible reaching-def constant reconstruction). Fail-closed on
/// any other terminator shape — the compare must IMMEDIATELY precede the branch
/// (so it reads exactly that compare's flags), the condition must be unsigned
/// `LO`, and the two edges must split cleanly in/out of the body. Mirrors
/// `neon_map::recognize_chain_guard`, generalized to the constant-bound form.
fn recognize_chain_guard(
    func: &MachFunction,
    blk: BlockId,
    body: &HashSet<BlockId>,
) -> Option<(VReg, ChainBound, BlockId, InstId)> {
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
    let x = vreg_of(&cmp.operands[0])?;
    let bound = match cmp.opcode {
        AArch64Opcode::CmpRR => ChainBound::Reg(vreg_of(&cmp.operands[1])?),
        AArch64Opcode::CmpRI => ChainBound::Const(imm_of(&cmp.operands[1])?),
        _ => return None,
    };
    let t_lo = *branch_targets(bcond).first()?;
    let t_b = *branch_targets(br).first()?;
    // The taken (`b.lo`, iv<N true) edge continues INTO the body; the fall-through
    // leaves it. Exactly one of each — anything else BAILS.
    if !body.contains(&t_lo) || body.contains(&t_b) {
        return None;
    }
    Some((x, bound, t_lo, insts[n - 3]))
}

/// A recognized in-chain ABS DIAMOND (TRACK D): the branchy two's-complement
/// absolute value the bridge emits for `unsigned_abs()` / `wrapping_abs()`:
///
/// ```text
///   split:  ...; CmpRI(x, #0); BCond(LT, neg); B(pos)
///   neg:    SubRR(t, zero, x); MovR(phi, t); B(join)     ; phi = (0 - x) mod 2^32
///   pos:    MovR(phi, x); B(join)                        ; phi = x
/// ```
///
/// (or the mirrored `BCond(GE, pos); B(neg)`). At the join, `phi` holds the
/// two's-complement abs BIT PATTERN `abs_bits(x) = x <s 0 ? (0 - x) mod 2^32 : x`
/// — EXACTLY the u32 value `(x as i32).unsigned_abs()` for EVERY input including
/// `i32::MIN` (`0 - 0x8000_0000` wraps to `0x8000_0000` = 2^31 = the
/// `unsigned_abs` result).
#[derive(Clone, Copy)]
struct AbsDiamond {
    /// The split block (ends with the `CmpRI(x, #0)` sign test).
    split: BlockId,
    /// The two arm blocks `[neg, pos]`.
    arms: [BlockId; 2],
    /// The join block (both arms' single successor).
    join: BlockId,
    /// The two-def result register both arms write (`abs_bits(x)` at the join).
    phi: VReg,
    /// The compared / conditionally-negated i32 value.
    x: VReg,
    /// The negating arm's zero register (`phi = zero - x`). The diamond
    /// recognizer proved its def-map def is a `Movz #0`; the tail additionally
    /// proves it is the UNIQUE def and available at the split
    /// ([`Recognized::recognize_widening_abs`]).
    zero: VReg,
}

/// Recognize a chain block terminating in an ABS DIAMOND (see [`AbsDiamond`]).
/// EXACT-shape, fail-closed:
/// * the split ends with `CmpRI(x, #0); BCond(LT|GE, ..); B(..)` (the compare
///   IMMEDIATELY before the branch, so it is the flag producer) with `x` an i32;
/// * `LT` routes the TAKEN edge to the NEGATING arm, `GE` to the IDENTITY arm —
///   any other condition returns `None`;
/// * both arms are in-body, have the split as their ONLY predecessor and the
///   SAME single in-body successor (the join), whose preds are EXACTLY the two
///   arms — so every path to the join wrote `phi` in one of the arms;
/// * the NEGATING arm is EXACTLY `SubRR(t, zero, x); MovR(phi, t); B` with
///   `zero` a proven constant 0 — i.e. `phi = (0 - x) mod 2^32`;
/// * the IDENTITY arm is EXACTLY `MovR(phi, x); B`.
///
/// Returns the diamond; the caller consumes the arm blocks and continues the
/// chain walk at the join. NOTE: this validates the DIAMOND only — the caller
/// ([`Recognized::recognize_widening_abs`]) still proves `phi` has no third
/// in-loop writer and that the term routes through it.
fn recognize_abs_diamond(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    split: BlockId,
) -> Option<AbsDiamond> {
    let insts = &func.block(split).insts;
    let n = insts.len();
    if n < 3 {
        return None;
    }
    let cmp = func.inst(insts[n - 3]);
    let bcond = func.inst(insts[n - 2]);
    let br = func.inst(insts[n - 1]);
    if cmp.opcode != AArch64Opcode::CmpRI
        || bcond.opcode != AArch64Opcode::BCond
        || br.opcode != AArch64Opcode::B
        || imm_of(&cmp.operands[1])? != 0
    {
        return None;
    }
    let x = vreg_of(&cmp.operands[0])?;
    if x.class != RegClass::Gpr32 {
        return None;
    }
    let t = *branch_targets(bcond).first()?;
    let f = *branch_targets(br).first()?;
    // The condition routes the SIGN: `LT` taken ⇔ `x <s 0` ⇒ taken edge is the
    // NEGATING arm; `GE` taken ⇔ `x >=s 0` ⇒ taken edge is the IDENTITY arm.
    let (neg_b, pos_b) = match imm_of(&bcond.operands[0])? {
        CC_LT => (t, f),
        CC_GE => (f, t),
        _ => return None,
    };
    if neg_b == pos_b
        || neg_b == split
        || pos_b == split
        || !body.contains(&neg_b)
        || !body.contains(&pos_b)
    {
        return None;
    }
    // Both arms: single pred (the split) + the same single successor (the join).
    for &arm in &[neg_b, pos_b] {
        let preds = &func.block(arm).preds;
        if preds.len() != 1 || preds[0] != split {
            return None;
        }
        if func.block(arm).succs.len() != 1 {
            return None;
        }
    }
    let join = func.block(neg_b).succs[0];
    if func.block(pos_b).succs[0] != join || !body.contains(&join) || join == split {
        return None;
    }
    // The join's preds are EXACTLY the two arms: no third path can reach the
    // phi read without executing one arm's write.
    let jpreds = &func.block(join).preds;
    if jpreds.len() != 2 || !jpreds.contains(&neg_b) || !jpreds.contains(&pos_b) {
        return None;
    }
    // NEGATING arm: EXACTLY `SubRR(t, zero, x); MovR(phi, t); B`.
    let ni = &func.block(neg_b).insts;
    if ni.len() != 3 {
        return None;
    }
    let sub = func.inst(ni[0]);
    if sub.opcode != AArch64Opcode::SubRR || sub.operands.len() != 3 {
        return None;
    }
    let neg_t = vreg_of(&sub.operands[0])?;
    let zero = vreg_of(&sub.operands[1])?;
    if const_value(func, def, zero) != Some(0) || vreg_of(&sub.operands[2])? != x {
        return None;
    }
    let mov_n = func.inst(ni[1]);
    if mov_n.opcode != AArch64Opcode::MovR {
        return None;
    }
    let (phi_n, src_n) = copy_like(mov_n)?;
    if src_n != neg_t || func.inst(ni[2]).opcode != AArch64Opcode::B {
        return None;
    }
    // IDENTITY arm: EXACTLY `MovR(phi, x); B`.
    let pi = &func.block(pos_b).insts;
    if pi.len() != 2 {
        return None;
    }
    let mov_p = func.inst(pi[0]);
    if mov_p.opcode != AArch64Opcode::MovR {
        return None;
    }
    let (phi_p, src_p) = copy_like(mov_p)?;
    if src_p != x || func.inst(pi[1]).opcode != AArch64Opcode::B {
        return None;
    }
    // Both arms write the SAME i32 phi, which is not `x` itself.
    if phi_n != phi_p || phi_n.class != RegClass::Gpr32 || phi_n.id == x.id {
        return None;
    }
    Some(AbsDiamond {
        split,
        arms: [neg_b, pos_b],
        join,
        phi: phi_n,
        x,
        zero,
    })
}

/// True iff `v` reaches `iv` through value-preserving copy links
/// (`MovR`/`Copy`/`AddRI(_,0)`) — i.e. `v` IS the induction or a copy of it.
/// Bounded walk; matches `iv` EXACTLY and never strips PAST it, so it does not
/// follow the latch writeback `iv = iv+1` and never mistakes a distinct `iv+1`
/// index for `iv`. Mirrors `neon_map::same_as_iv`.
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
/// the multi-def induction. Mirrors `neon_map::strip_copies`.
/// Resolve a register READ inside the loop to a LOOP-INVARIANT register whose
/// value at loop entry equals the in-loop-observed value on EVERY iteration —
/// the register the vector preheader may read.
///
/// A register whose defs ALL lie outside the loop body is invariant across the
/// loop, and because the ORIGINAL loop reads it (directly or through the copy
/// chain below) on every iteration, its reaching value at the preheader IS the
/// value every in-loop read observes — no single-def-dominates-preheader
/// requirement (which FAILS for merged variables like a Vec length carried
/// through a preceding growth loop: multiple defs, each on its own path, none
/// dominating). Otherwise the register must have exactly ONE def anywhere — an
/// in-loop value-preserving copy — and the walk steps to its source. Anything
/// else (an in-loop non-copy def, several defs with any inside the loop)
/// returns None: fail-closed to the scalar loop.
/// Step a register through GLOBALLY-SINGLE-DEF value-preserving copies only,
/// returning the first register that is not one (multi-def, def-less past the
/// first step, or defined by a non-copy). Unlike [`strip_copies`], this NEVER
/// consults the last-def-wins def map on a multi-def register — the map entry
/// there is an ARBITRARY def, and resolving through it let a foreign value
/// masquerade as the loop bound (review repro: a merged multi-def `N` whose
/// stale map entry aliased a different length register). Multi-def registers
/// TERMINATE the walk and are compared by identity only.
fn strict_copy_root(func: &MachFunction, mut v: VReg) -> VReg {
    for _ in 0..16 {
        let defs: Vec<InstId> = func
            .blocks
            .iter()
            .flat_map(|b| b.insts.iter().copied())
            .filter(|&id| inst_defines(func.inst(id), v.id))
            .collect();
        let [d] = defs.as_slice() else {
            return v;
        };
        match copy_like(func.inst(*d)) {
            Some((dst, src)) if dst == v => v = src,
            _ => return v,
        }
    }
    v
}

/// STRICT [`ChainBound`] agreement for the forward chain: registers agree iff
/// their [`strict_copy_root`]s are IDENTICAL; a register agrees with a constant
/// iff its root is globally single-def and that def materializes exactly that
/// constant. Never resolves through a multi-def register's arbitrary def-map
/// entry (the review-demonstrated foreign-length hazard).
fn strict_chain_bound_agrees(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    a: ChainBound,
    b: ChainBound,
) -> bool {
    let single_def_const = |r: VReg, k: i64| {
        let root = strict_copy_root(func, r);
        let ndefs = func
            .blocks
            .iter()
            .flat_map(|blk| blk.insts.iter().copied())
            .filter(|&id| inst_defines(func.inst(id), root.id))
            .count();
        ndefs == 1 && const_value(func, def, root) == Some(k)
    };
    match (a, b) {
        (ChainBound::Const(x), ChainBound::Const(y)) => x == y,
        (ChainBound::Reg(x), ChainBound::Reg(y)) => {
            strict_copy_root(func, x) == strict_copy_root(func, y)
        }
        (ChainBound::Reg(r), ChainBound::Const(k)) | (ChainBound::Const(k), ChainBound::Reg(r)) => {
            single_def_const(r, k)
        }
    }
}

fn resolve_loop_invariant(
    func: &MachFunction,
    loop_insts: &HashSet<InstId>,
    mut v: VReg,
) -> Option<VReg> {
    for _ in 0..16 {
        let defs: Vec<InstId> = func
            .blocks
            .iter()
            .flat_map(|b| b.insts.iter().copied())
            .filter(|&id| inst_defines(func.inst(id), v.id))
            .collect();
        if defs.iter().all(|id| !loop_insts.contains(id)) {
            // Invariant (a def-less register — e.g. a parameter — is trivially
            // so).
            return Some(v);
        }
        let [d] = defs.as_slice() else {
            return None;
        };
        match copy_like(func.inst(*d)) {
            Some((dst, src)) if dst == v => v = src,
            _ => return None,
        }
    }
    None
}

/// The recognized loop SHAPE, produced by [`Recognized::two_block_shape`] /
/// [`Recognized::recognize_forward_chain`] and consumed by the shared
/// reduction/term/width tail [`Recognized::recognize_tail`].
struct Shape {
    /// Loop-carried induction register (`+1` each iteration).
    iv: VReg,
    /// The induction writeback SOURCE (`iv = iv_src`, `iv_src = iv + 1`).
    iv_src: VReg,
    /// Loop-carried accumulator register.
    acc: VReg,
    /// The accumulator writeback SOURCE (`acc = acc_src`, the reduction result).
    acc_src: VReg,
    /// Loop bound register. For a CONSTANT chain bound this is a PLACEHOLDER
    /// carrying the accumulator's register class only (never read by `apply`,
    /// which materializes `bound_const` fresh instead).
    bound: VReg,
    /// Pre-seeded compile-time bound (the CONSTANT chain limit), validated to
    /// `[1, i32::MAX]`. `None` when the tail must derive it (register bound).
    bound_const: Option<i64>,
    /// The RAW compared bound operand + the exit compare's `InstId`, for the
    /// tail's reaching-def constant reconstruction when the bound reg's def does
    /// not dominate the preheader.
    bound_cmp: Option<(VReg, InstId)>,
    /// ROTATED 2-block shape only: the loop's true exit block (exit routing).
    rotated_exit: Option<BlockId>,
    /// The (possibly re-rooted) vectorizer preheader.
    preheader: BlockId,
    /// The (possibly re-rooted) vectorizer guard.
    guard: BlockId,
    /// The `preheader` terminator branching into `guard`.
    preheader_term: InstId,
    /// FORWARD-CHAIN shape only: the single ABS DIAMOND the chain walk consumed
    /// (TRACK D). When set, the ONLY admissible reduction is the i64 widening
    /// abs-sum through it — anything else BAILS (fail-closed).
    abs_diamond: Option<AbsDiamond>,
}

impl Recognized {
    /// Dispatch: the strict 2-block `{header, latch}` loop (native trust_ir /
    /// clang-rotated forward|reverse) goes through [`Self::recognize_two_block`];
    /// a multi-block body — the FORWARD bounds-guarded `while i<N` CHAIN the
    /// bridge emits for `for i in 0..N { acc OP= TERM }` over fixed-size arrays —
    /// goes through [`Self::recognize_forward_chain`]. Both build the SHAPE, then
    /// run the SHARED reduction/term/width tail [`Self::recognize_tail`].
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        if header == latch || body.is_empty() || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }
        if body.len() == 2 {
            Self::recognize_two_block(func, dom, def, header, latch, body)
        } else {
            Self::recognize_forward_chain(func, dom, def, header, latch, body)
        }
    }

    /// The strict 2-block `{header, latch}` recognizer (native / rotated). Builds
    /// the SHAPE then runs the shared tail. UNCHANGED from the original recognizer
    /// except that the shared reduction/term/width tail is now
    /// [`Self::recognize_tail`].
    fn recognize_two_block(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // Whitelist every opcode in the loop body — no store/call/div/etc.
        let mut loop_insts = HashSet::new();
        for &b in body {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

        // `def` is supplied by the caller, built ONCE per recognition sweep.

        // (R6) header preds are exactly {latch, guard}.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            return None;
        }
        let guard = *hpreds.iter().find(|&&b| b != latch)?;
        let gpreds_len = func.block(guard).preds.len();
        // The NATIVE shape requires the single-pred guard/preheader pair (the
        // splice redirects that one edge; re-checked in the native R2 branch
        // below). The ROTATED shape instead RE-ROOTS the vectorizer's block
        // model onto the GUARD itself, so it tolerates a multi-pred guard —
        // e.g. an ENCLOSING outer-loop header (entry + outer back-edge) that
        // branches unconditionally into the reduction header when clang elided
        // the len>0 check for a constant trip count. The guard then re-runs
        // once per OUTER iteration, re-zeroing the fresh vector accumulators
        // and re-seeding iv/acc exactly like the scalar guard — sound. Seed
        // the mutable model with (guard, guard's branch-to-header); the
        // rotated R2 branch overwrites it with the identical values.
        let (preheader, preheader_term) = if gpreds_len == 1 {
            let p = func.block(guard).preds[0];
            let t = *func
                .block(p)
                .insts
                .iter()
                .rev()
                .find(|&&id| branch_targets(func.inst(id)).contains(&guard))?;
            (p, t)
        } else {
            let t = *func
                .block(guard)
                .insts
                .iter()
                .rev()
                .find(|&&id| branch_targets(func.inst(id)).contains(&header))?;
            (guard, t)
        };
        // Mutable copies: the ROTATED shape RE-ROOTS the vectorizer's block model
        // onto the GUARD (see the override in the rotated R2 branch below).
        let (mut vec_preheader, mut vec_guard, mut vec_preheader_term) =
            (preheader, guard, preheader_term);
        // ROTATED shape only: the loop's true exit block (set in the rotated branch).
        let mut rotated_exit: Option<BlockId> = None;
        // ROTATED shape only: the RAW compared bound operand + the exit CmpRR's
        // InstId — the use point for the reaching-def constant reconstruction
        // when the bound's def does not dominate the preheader.
        let mut bound_cmp: Option<(VReg, InstId)> = None;

        // (R2) The exit test + loop-carried writebacks. Two loop SHAPES are
        // accepted; the writebacks (two `copy_like`) live in the LATCH in both.
        //  * NATIVE (trust_ir): the LATCH also holds the exit test —
        //    `CmpRR(iv, bound); BCond(LT) -> header`.
        //  * ROTATED (clang -O1, the importer's shape): the latch is PURE
        //    writebacks + `B -> header`; the exit test lives at the END of the
        //    HEADER as `CmpRR(iv+1, bound); CSet(EQ); CmpRI(#0); BCond(NE) -> exit`
        //    (== "leave when iv+1 hits bound"). Since iv starts at 0 and steps by
        //    +1, iv+1 reaches bound EXACTLY, so the trip is [0, bound) — the same
        //    counted loop, just bottom-tested-in-header.
        let latch_insts = func.block(latch).insts.clone();
        let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
        for &id in &latch_insts {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                writebacks.push((d, s));
            }
        }
        if writebacks.len() != 2 {
            return None;
        }
        let latch_exit_bcond = latch_insts
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::BCond && branch_targets(i).contains(&header));

        let (iv, bound) = if let Some(bcond) = latch_exit_bcond {
            // NATIVE shape.
            if gpreds_len != 1 {
                return None; // the native splice needs the single-pred preheader
            }
            if imm_of(&bcond.operands[0]) != Some(CC_LT) {
                return None; // only signed `<` counted loops
            }
            let cmp = latch_insts
                .iter()
                .map(|&id| func.inst(id))
                .rev()
                .find(|i| i.opcode == AArch64Opcode::CmpRR)?;
            (vreg_of(&cmp.operands[0])?, vreg_of(&cmp.operands[1])?)
        } else {
            // ROTATED shape. The latch must be PURE writebacks + `B -> header`
            // (the two copies plus one unconditional branch, nothing else with an
            // effect); the iv writeback is the one whose source is `dst + 1`.
            let non_copy: Vec<InstId> = latch_insts
                .iter()
                .copied()
                .filter(|&id| copy_like(func.inst(id)).is_none())
                .collect();
            if non_copy.len() != 1 || func.inst(non_copy[0]).opcode != AArch64Opcode::B {
                return None;
            }
            let iv_wb = writebacks
                .iter()
                .copied()
                .find(|(d, s)| is_increment_by_one(func, &def, *s, *d))?;
            let (bound, exit, cmp_id) =
                recognize_rotated_header_exit(func, header, body, iv_wb.0, iv_wb.1)?;
            rotated_exit = Some(exit);
            bound_cmp = Some((bound, cmp_id));
            // If the bound is an i64 WIDENING of an i32 (`Uxtw(n)`), substitute its
            // i32 source `n` (an entry value that dominates everything) so the i32
            // apply path can re-`Sxtw` it. Enables the i32-acc / i64-index case.
            let bound = ext_source(func, &def, bound).unwrap_or(bound);
            // ROTATED block-model RE-ROOT (soundness — see the uninit-iv P0): clang
            // inits the induction AND computes the bound in the GUARD block, then
            // unconditionally branches to the header. Make the GUARD the
            // vectorizer's preheader, so `apply` splices the vector loop AFTER the
            // iv-init (iv=0 in scope — no uninitialized read) and BETWEEN guard and
            // header, and routes the vector exit into the HEADER (scalar tail) —
            // NOT back through the guard (which would re-init iv and double-process
            // [0, vector_trip)). apply inserts vh..vx before `vec_guard`=header and
            // rewires guard->header to guard->vh; vx falls into header.
            vec_preheader = guard;
            vec_guard = header;
            vec_preheader_term = *func
                .block(guard)
                .insts
                .iter()
                .rev()
                .find(|&&id| branch_targets(func.inst(id)).contains(&header))?;
            (iv_wb.0, bound)
        };

        // iv writeback source; acc is the OTHER writeback target.
        let iv_src = writebacks.iter().find(|(d, _)| *d == iv).map(|(_, s)| *s)?;
        let (acc, acc_src) = {
            let other = writebacks.iter().find(|(d, _)| *d != iv)?;
            (other.0, other.1)
        };
        if acc == iv {
            return None;
        }

        Self::recognize_tail(
            func,
            dom,
            def,
            loop_insts,
            Shape {
                iv,
                iv_src,
                acc,
                acc_src,
                bound,
                bound_const: None,
                bound_cmp,
                rotated_exit,
                preheader: vec_preheader,
                guard: vec_guard,
                preheader_term: vec_preheader_term,
                abs_diamond: None,
            },
        )
    }

    /// The FORWARD bounds-guarded `while i<N` CHAIN recognizer (mirrors
    /// `neon_map::recognize_forward_chain`, generalized to the constant-bound
    /// guard d09/d10 emit). The straight-line reduction body is spread over a
    /// LINEAR CHAIN `header(iv<N?) -> g1 -> ... -> latch -> header`: the header
    /// (and any surviving array bounds check) is an `iv <u N` DIAMOND, the rest
    /// are PASS-THROUGH blocks whose bounds check `aarch64-bounds-check-elim`
    /// already eliminated; the latch holds the reduction, the `iv=iv+1`
    /// writeback, the `acc` writeback, and the back-edge (no exit test — a
    /// test-first while).
    ///
    /// ## Why SOUND (single-N agreement + additive-subset)
    ///
    /// `apply` splices a vector main loop in FRONT of the header and NEVER edits
    /// the scalar chain (correct by construction). We fire ONLY when the
    /// loop-continue limit AND every in-loop bounds-guard limit are the SAME `N`,
    /// each compared against a copy of the induction — so `N == a.len()` for every
    /// array the body reads. `apply`'s forward header (`rec.guard` = the loop
    /// header's own top-test, no exit routing) admits a vector block only while
    /// `iv+width-1 < N`, so every vector access lies in `[0, N) = [0, a.len())` —
    /// a SUBSET of the indices the scalar chain reads at the SAME addresses — and
    /// the untouched scalar chain finishes the `[V, N)` tail. Because the reduction
    /// target is a REGISTER `acc` (not memory), read/read aliasing of the input
    /// streams is benign — no versioning is needed. A surviving
    /// `TrapBoundsCheckExact` carrier is admitted by the CHAIN path ONLY under
    /// validation (the register analogue of neon_bytesum's carrier arm): its
    /// index must be the iv through value-preserving copies and its length must
    /// join the single-N agreement — so the carrier is exactly this loop's own
    /// `a[iv]` guard against the SAME `N` the vector header re-proves
    /// (`iv+width-1 < N` ⊇ each lane's `idx < N`), and it survives untouched in
    /// the scalar tail. A carrier over ANY other index or length is evidence of
    /// an access the vector plan does not model and BAILS the whole loop.
    /// Fail-closed on ANY deviation.
    fn recognize_forward_chain(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // Whitelist every opcode across EVERY body block (mirror neon_map:635) —
        // a hidden second store / foreign load / call / div in a MIDDLE block
        // still BAILS. The CHAIN path additionally admits `TrapBoundsCheckExact`
        // carriers (collected here, validated STRICTLY against the iv and the
        // single N once the walk resolves the bound) — the TWO-BLOCK recognizer
        // deliberately does not (its latch/guard shapes were never audited for
        // them; fail-closed there). At this stage the slice load is still the
        // FORM 1 `Madd`+`LdrRI` pair (`ext_addr` fuses `LdrRO` only later), so
        // no scaled register-offset admission is needed.
        let mut loop_insts = HashSet::new();
        let mut carriers: Vec<InstId> = Vec::new();
        for &b in body {
            for &id in &func.block(b).insts {
                let op = func.inst(id).opcode;
                if op == AArch64Opcode::TrapBoundsCheckExact {
                    carriers.push(id);
                } else if !allowed_loop_op(op) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

        // `def` is supplied by the caller, built ONCE per recognition sweep.

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

        // The latch holds the loop-carried writebacks — EXACTLY two `copy_like`
        // (iv + acc) — plus the reduction, the step, and the sole back-edge
        // `B -> header`. There is NO exit test in the latch (a test-first while
        // keeps the exit in the header guard chain). A TRACK D latch ADDITIONALLY
        // re-copies the abs diamond's phi into a local temp before widening it
        // (`MovR t, phi; Uxtw ...; ...`): that copy's dst is consumed by a LATER
        // latch instruction, which a loop-carried writeback's never is (its value
        // crosses the back edge). Only when MORE than two copies are found (a
        // shape that always BAILed before) are the locally-consumed ones dropped —
        // recognition is strictly firing-monotone over the previous behaviour.
        let latch_insts = func.block(latch).insts.clone();
        let mut cands: Vec<(usize, VReg, VReg)> = Vec::new();
        for (pos, &id) in latch_insts.iter().enumerate() {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                cands.push((pos, d, s));
            }
        }
        if cands.len() > 2 {
            cands.retain(|&(pos, d, _)| {
                !latch_insts[pos + 1..].iter().any(|&id| {
                    let inst = func.inst(id);
                    let mut reads = false;
                    crate::effects::aarch64_for_each_use_position(
                        inst.opcode,
                        inst.operands.len(),
                        |p| {
                            if let Some(MachOperand::VReg(u)) = inst.operands.get(p)
                                && u.id == d.id
                            {
                                reads = true;
                            }
                        },
                    );
                    reads
                })
            });
        }
        let writebacks: Vec<(VReg, VReg)> = cands.into_iter().map(|(_, d, s)| (d, s)).collect();
        if writebacks.len() != 2 {
            return None;
        }
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
        // iv writeback = the `dst+1` one; acc = the other.
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

        // Walk the chain header -> ... -> latch. Each NON-latch block is EITHER a
        // bounds-guard DIAMOND (two succs, validated by `recognize_chain_guard`
        // with an iv-copy index and single-N agreement) OR a PASS-THROUGH (one
        // in-body succ, its bounds check already elided — dominated by the
        // header's `iv < N` guard, so its access is the SAME `a[iv]` the scalar
        // loop does). The header (walk start) MUST be a diamond so the loop has an
        // exit and the bound is established. The chain must be a SIMPLE path
        // covering EVERY body block exactly once and ending at the latch.
        let mut bound: Option<ChainBound> = None;
        let mut header_cmp: Option<InstId> = None;
        // At most ONE in-chain ABS DIAMOND (TRACK D); its arm blocks are part of
        // the walked chain (consumed below), its join continues it.
        let mut abs_diamond: Option<AbsDiamond> = None;
        let mut visited: HashSet<BlockId> = HashSet::new();
        let mut cur = header;
        loop {
            if !body.contains(&cur) || !visited.insert(cur) {
                return None;
            }
            if cur == latch {
                break;
            }
            let succs = &func.block(cur).succs;
            let next = if succs.len() == 2 {
                if let Some((x, n, t_lo, cmp_id)) = recognize_chain_guard(func, cur, body) {
                    // Bounds-guard diamond: validate index/single-N; continue
                    // in-body.
                    if !same_as_iv(func, &def, x, iv) {
                        return None;
                    }
                    match bound {
                        Some(b) if !strict_chain_bound_agrees(func, &def, b, n) => return None,
                        None => {
                            bound = Some(n);
                            header_cmp = Some(cmp_id);
                        }
                        _ => {}
                    }
                    t_lo
                } else if bound.is_some()
                    && abs_diamond.is_none()
                    && let Some(d) = recognize_abs_diamond(func, &def, body, cur)
                {
                    // TRACK D ABS DIAMOND: consume both arm blocks and continue
                    // at the join. `bound.is_some()` is LOAD-BEARING: it proves
                    // the diamond sits BEHIND the loop's `iv <u N` exit guard
                    // (the header), so the vector exit's tail routing into the
                    // header re-checks the bound BEFORE any body access — a
                    // diamond-first (rotated) chain must never match. The tail
                    // later REQUIRES the reduction term to route through this
                    // diamond (fail-closed).
                    for arm in d.arms {
                        if !visited.insert(arm) {
                            return None;
                        }
                    }
                    abs_diamond = Some(d);
                    d.join
                } else {
                    return None;
                }
            } else if succs.len() == 1 {
                // Pass-through (bounds guard eliminated): flow to the single
                // in-body successor. The header is never a pass-through (it needs
                // the exit diamond), so `bound` is already set here.
                if bound.is_none() || !body.contains(&succs[0]) {
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
        let bound = bound?; // the header's loop-continue guard established it

        // Every `TrapBoundsCheckExact` carrier in the body must be THIS loop's
        // own `a[iv]` guard against the SAME single N: `[base, index, len]`
        // with index == iv (through value-preserving copies) and len joining
        // the single-N agreement — the register analogue of neon_bytesum's
        // carrier arm. The vector header re-proves `iv+width-1 <u N`, a
        // superset of each lane's `idx <u N`, so the carrier's condition holds
        // for every vector access and the carrier itself survives untouched in
        // the scalar tail. Any other index/length BAILS.
        // STRICT resolution only (review repro): `strip_copies`/`same_as_iv`
        // ride the last-def-wins def map, whose entry for a MULTI-DEF register
        // is arbitrary — and merged multi-def bounds are exactly what
        // `resolve_loop_invariant` newly admits. Every register consulted here
        // steps only through globally-single-def copies (`strict_copy_root`);
        // multi-def registers terminate the walk and compare by IDENTITY, so a
        // foreign length can never masquerade as the loop bound.
        for &cid in &carriers {
            let cinst = func.inst(cid);
            if cinst.operands.len() != 3 {
                return None;
            }
            let index = vreg_of(&cinst.operands[1])?;
            if strict_copy_root(func, index) != iv {
                return None;
            }
            match (bound, &cinst.operands[2]) {
                (ChainBound::Reg(b), MachOperand::VReg(l)) => {
                    if strict_copy_root(func, *l) != strict_copy_root(func, b) {
                        return None;
                    }
                }
                (ChainBound::Const(k), MachOperand::Imm(v)) => {
                    if *v != k {
                        return None;
                    }
                }
                // Register-vs-constant agreement would need const resolution
                // through the multi-def-hazardous map — fail closed.
                _ => return None,
            }
        }

        // Resolve the bound. A CONSTANT limit (`CmpRI`, d09's `[i32; 2048]`) is
        // validated to `[1, i32::MAX]` EXACTLY like `reconstruct_const_bound` and
        // carried as `bound_const`; `apply` materializes it fresh in the preheader
        // (never reads a register). Its placeholder register carries the
        // ACCUMULATOR's class so the tail's `(iv.class, acc.class, bound.class)`
        // width-dispatch lands on the correct arm (e.g. d09's Gpr64-iv/Gpr32-acc
        // MIXED `.4S`). A REGISTER limit reuses the tail's existing invariance /
        // reconstruction path.
        let (bound_vreg, bound_const, bound_cmp) = match bound {
            ChainBound::Const(k) => {
                if !(1..=i32::MAX as i64).contains(&k) {
                    return None;
                }
                (VReg::new(acc.id, acc.class), Some(k), None)
            }
            ChainBound::Reg(n) => (n, None, header_cmp.map(|id| (n, id))),
        };

        Self::recognize_tail(
            func,
            dom,
            def,
            loop_insts,
            Shape {
                iv,
                iv_src,
                acc,
                acc_src,
                bound: bound_vreg,
                bound_const,
                bound_cmp,
                rotated_exit: None,
                preheader,
                guard: header,
                preheader_term,
                abs_diamond,
            },
        )
    }

    /// SHARED reduction/term/width tail for both shape recognizers. Arrives with
    /// the SHAPE fields set (iv/iv_src/acc/acc_src/bound/bound_const/bound_cmp/
    /// rotated_exit/preheader/guard/preheader_term); recognizes the reduction
    /// operator and per-lane term, picks the element/index width, validates the
    /// bound/iv availability + the lane-wise term — or BAILS (fail-closed).
    fn recognize_tail(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        loop_insts: HashSet<InstId>,
        shape: Shape,
    ) -> Option<Self> {
        let Shape {
            iv,
            iv_src,
            acc,
            acc_src,
            bound,
            bound_const: bound_const_seed,
            bound_cmp,
            rotated_exit,
            preheader: vec_preheader,
            guard: vec_guard,
            preheader_term: vec_preheader_term,
            abs_diamond,
        } = shape;
        // `bound` may be re-rooted below through value-preserving copies.
        let mut bound = bound;

        // (R3) step: iv_src = AddRR(iv, +1)  (or AddRI(iv, 1)).
        if !is_increment_by_one(func, &def, iv_src, iv) {
            return None;
        }

        // (R4) reduction: acc_src defined by a COMMUTATIVE associative recurrence
        // `acc = acc OP term` — `AddRR`, `EorRR`, or `OrrRR` (each identity 0) —
        // or the fused add `Madd(a, b, acc)` (term = a*b, add-only). For the
        // associative bitwise/add ops, ALSO accept a left-folded `(acc OP z) OP y`
        // where acc is nested one level (`OpPair` term = `z OP y`); this is how
        // clang emits `acc ⊕ a[i] ⊕ (i+1)`.
        let acc_def = func.inst(*def.get(&acc_src.id)?);
        // Returns (term, nested_reduction_inst_id). `nested` is the inner
        // `OP(acc, z)` when the reduction was left-folded, else None.
        let comm_term = |op: AArch64Opcode, acc_def: &MachInst| -> Option<(Term, Option<InstId>)> {
            let x = vreg_of(&acc_def.operands[1])?;
            let y = vreg_of(&acc_def.operands[2])?;
            if x == acc {
                return Some((Term::Value(y), None));
            }
            if y == acc {
                return Some((Term::Value(x), None));
            }
            // Reassociation: one operand's def is `op(acc, z)` (SAME op, acc
            // nested). `(acc op z) op other = acc op (z op other)`.
            let try_nested = |nested: VReg, other: VReg| -> Option<(Term, Option<InstId>)> {
                let nid = *def.get(&nested.id)?;
                let ninst = func.inst(nid);
                if ninst.opcode != op || ninst.operands.len() != 3 {
                    return None;
                }
                let a = vreg_of(&ninst.operands[1])?;
                let b = vreg_of(&ninst.operands[2])?;
                let z = if a == acc {
                    b
                } else if b == acc {
                    a
                } else {
                    return None;
                };
                Some((Term::OpPair(z, other), Some(nid)))
            };
            try_nested(x, y).or_else(|| try_nested(y, x))
        };
        let (reduce_op, term, nested_op) = match acc_def.opcode {
            AArch64Opcode::AddRR => {
                let (t, n) = comm_term(AArch64Opcode::AddRR, acc_def)?;
                (ReduceOp::Add, t, n)
            }
            AArch64Opcode::EorRR => {
                let (t, n) = comm_term(AArch64Opcode::EorRR, acc_def)?;
                (ReduceOp::Xor, t, n)
            }
            AArch64Opcode::OrrRR => {
                let (t, n) = comm_term(AArch64Opcode::OrrRR, acc_def)?;
                (ReduceOp::Or, t, n)
            }
            AArch64Opcode::Madd if acc_def.operands.len() == 4 => {
                let a = vreg_of(&acc_def.operands[1])?;
                let b = vreg_of(&acc_def.operands[2])?;
                let c = vreg_of(&acc_def.operands[3])?;
                if c != acc || a == acc || b == acc {
                    return None;
                }
                (ReduceOp::Add, Term::MulPair(a, b), None)
            }
            _ => return None,
        };

        // (R4b) acc must be read ONLY by the reduction inst (and, when
        // reassociated, the nested reduction inst) inside the loop.
        let acc_reducer = *def.get(&acc_src.id)?;
        for &id in loop_insts.iter() {
            if id == acc_reducer || Some(id) == nested_op {
                continue;
            }
            let inst = func.inst(id);
            for op in inst.operands.iter().skip(1) {
                if vreg_of(op) == Some(acc) {
                    return None;
                }
            }
        }

        // Register width selects the lowering path. All three of iv/acc/bound
        // must share a width. `Gpr32` ⇒ the `.4S` i32 path (sign-extension
        // guard). `Gpr64` ⇒ the `.2D` i64 path (unsigned-subtraction guard);
        // i64 has no sign-extension headroom, so the guard is different, and
        // `.2D` has no integer multiply, so any multiply in the term BAILS
        // below. Mixed widths BAIL. `bound_const_seed` is `Some` for a CONSTANT
        // chain bound (the placeholder `bound` carries `acc`'s class so this
        // dispatch routes correctly without ever reading a bound register).
        let mut bound_const = bound_const_seed;
        let is_i64 = match (iv.class, acc.class, bound.class) {
            (RegClass::Gpr32, RegClass::Gpr32, RegClass::Gpr32) => false,
            (RegClass::Gpr64, RegClass::Gpr64, RegClass::Gpr64) => true,
            // MIXED: an i32 reduction (`.4S`) driven by clang's i64-WIDENED index,
            // with the bound already substituted to its i32 source (Gpr32). The
            // i32 apply path `Sxtw`s iv/bound; the i64 iv is i32-range (it runs
            // [0, bound) and bound is an i32), so `Sxtw(iv)` recovers it faithfully.
            (RegClass::Gpr64, RegClass::Gpr32, RegClass::Gpr32) => false,
            // MIXED with an i64 bound register: lowerable only when the bound is
            // a RECONSTRUCTIBLE constant (clang compares the widened i64 index
            // against a constant trip count materialized INSIDE the loop). An
            // i32-RANGE constant acts as the Gpr32 bound for the `.4S` path —
            // the apply paths materialize it fresh in the preheader, and the
            // same "iv runs [0, bound) ⊂ i32" argument as the arm above holds.
            (RegClass::Gpr64, RegClass::Gpr32, RegClass::Gpr64) => {
                bound_const = Some(reconstruct_const_bound(func, bound_cmp)?);
                false
            }
            _ => return None,
        };
        // i64 has no NATIVE `.2D` integer multiply. A fused dot-product reduction
        // (`s = madd(a, b, acc)`) on the `.2D` path is vectorizable ONLY as a
        // WIDENING dot `s(i64) += ext(a_i32[i]) * ext(b_i32[i])` via the widening
        // multiply-accumulate-long SMLAL/UMLAL (TRACK C, dispatched AFTER `rec` is
        // built below — it needs `rec`'s def/load recognition). Any OTHER i64
        // multiply BAILS there (fail-closed to the scalar loop).
        // The bound must be loop-invariant and available in the preheader (its
        // def block dominates the preheader), so the preheader can `Sxtw` it —
        // UNLESS it was (or can be) reconstructed as a compile-time constant,
        // which the apply paths materialize fresh in the preheader instead of
        // ever reading the register.
        if bound_const.is_none() {
            let bound_def = *def.get(&bound.id)?;
            let bound_block = block_of_inst(func, bound_def)?;
            if !dom.dominates(bound_block, vec_preheader) {
                // The guard may compare against an IN-LOOP COPY of the
                // invariant limit (the bounds-guarded chain re-copies `len`
                // every iteration: `MovR t, len; CmpRR iv, t`). Re-root
                // through the loop's own value-preserving copies to a
                // LOOP-INVARIANT register (`resolve_loop_invariant`): all its
                // defs lie outside the body, so its loop-entry value is
                // exactly what the guard compares on every iteration and the
                // vector preheader may read it — this deliberately does NOT
                // require a single def dominating the preheader, which fails
                // for merged variables (a Vec length carried through a
                // preceding growth loop). Fall back to the constant
                // reconstruction; bail if neither holds (fail-closed).
                match resolve_loop_invariant(func, &loop_insts, bound) {
                    Some(root) if root.class == bound.class => bound = root,
                    _ => {
                        bound_const = Some(reconstruct_const_bound(func, bound_cmp)?);
                    }
                }
            }
        }

        // SOUNDNESS: the vector loop is entered from the (possibly re-rooted)
        // preheader; the iv MUST be defined on that edge (see
        // iv_def_dominates_preheader). For the rotated shape vec_preheader is the
        // GUARD where iv is init'd (so this now PASSES); for the native shape it is
        // the real preheader. If a rotated loop's iv init isn't in the guard this
        // fails -> fail-closed to scalar.
        if !iv_def_dominates_preheader(func, dom, iv, vec_preheader) {
            return None;
        }

        // The in-loop Movz/Movk whitelist admits the constant-bound
        // materialization chain — but a move-wide RE-DEFINING a loop-carried
        // register (the iv, the acc, or either writeback source) would change
        // the recurrences the transform models (`Movk`'s operand 0 is a
        // def-use). Likewise a move-wide redefining the BOUND register is only
        // acceptable when that chain IS the reconstructed constant (verified
        // unique at the exit compare); with a register bound it would mean the
        // preheader-read value differs from the compared one. BAIL on any of
        // these — fail-closed to the scalar loop.
        for &id in loop_insts.iter() {
            let inst = func.inst(id);
            if matches!(inst.opcode, AArch64Opcode::Movz | AArch64Opcode::Movk)
                && let Some(MachOperand::VReg(d)) = inst.operands.first()
            {
                if [iv.id, acc.id, iv_src.id, acc_src.id].contains(&d.id) {
                    return None;
                }
                if d.id == bound.id && bound_const.is_none() {
                    return None;
                }
            }
        }

        // The step instruction (`iv_src = iv + 1`, proven by R3): node_ok /
        // lower admit its RESULT as the shifted affine iota `iv + 1` (see the
        // field docs). Only meaningful when it is the loop's own instruction.
        let step_inst = def
            .get(&iv_src.id)
            .copied()
            .filter(|i| loop_insts.contains(i));

        let mut rec = Recognized {
            reduce_op,
            guard: vec_guard,
            rotated_exit,
            preheader: vec_preheader,
            preheader_term: vec_preheader_term,
            iv,
            acc,
            acc_wb_src: acc_src,
            bound,
            bound_const,
            step_inst,
            term,
            is_i64,
            // Cloned only on a SUCCESSFUL recognition, which is rare. The cost
            // that mattered was rebuilding this map on every ATTEMPT; that now
            // happens once per sweep.
            def: def.clone(),
            loop_insts,
            loads: HashMap::new(),
            bases: Vec::new(),
            widen: None,
            dot: None,
            abs: None,
            uses_iv: false,
        };

        // TRACK D: i64 WIDENING ABS-SUM through the chain's ABS DIAMOND. When
        // the chain walk consumed a diamond, the ONLY reduction this recognizer
        // admits is the exact `s(i64) += Uxtw(abs_bits(a_i32[i] [+ inv]))`
        // add-reduction routed through that diamond's phi — anything else (a
        // non-i64 width, a non-add reduction, a term not rooted at the diamond)
        // BAILS, leaving the loop scalar. Dispatched BEFORE every other track so
        // no other lowering can ever fire on a loop containing a diamond.
        if let Some(d) = abs_diamond {
            if !rec.is_i64 || rec.reduce_op != ReduceOp::Add {
                return None;
            }
            let Term::Value(v) = rec.term else {
                return None;
            };
            {
                let plan = rec.recognize_widening_abs(func, dom, v, &d)?;
                rec.abs = Some(plan);
                return Some(rec);
            }
        }

        // TRACK C: i64 WIDENING DOT via the widening multiply-accumulate-long.
        // The `.2D` path has no native integer multiply, so a fused dot reduction
        // `s(i64) += ext(a_i32[i]) * ext(b_i32[i])` is the ONLY multiply shape the
        // i64 path can vectorize — through SMLAL/SMLAL2 (signed) or UMLAL/UMLAL2
        // (unsigned). Recognized here (after `rec` is built, so the load/base
        // recognition is available); ANY other i64 `MulPair` (or a non-recognizable
        // widening dot) BAILS — fail-closed to the scalar loop, exactly as the old
        // pre-`rec` guard did.
        if rec.is_i64
            && let Term::MulPair(fa, fb) = rec.term
        {
            {
                let plan = rec.recognize_widening_dot(func, dom, fa, fb)?;
                rec.dot = Some(plan);
                return Some(rec);
            }
        }

        // TRACK B: WIDENING byte/half reduction recognition — runs BEFORE the
        // generic lane-wise walk because its leaves (`Uxtb(LdrbRI(..))` etc.)
        // are not valid generic term nodes. Fires only on the EXACT shapes
        // `s += ext(a[i])` / `s += ctpop(zext8(a[i]))`; anything else falls
        // through to the generic walk (and, for these leaves, BAILS there).
        // Widening (`s += ext(a[i])` / ctpop) is an ADD-only sum idiom; XOR/OR
        // reductions never take it (their zero-extended-load terms lower fine on
        // the generic per-lane path below).
        if !is_i64
            && rec.reduce_op == ReduceOp::Add
            && let Term::Value(v) = rec.term
            && let Some(plan) = rec.recognize_widen(func, dom, v)
        {
            rec.widen = Some(plan);
            return Some(rec);
        }

        // (R5) term must be lowerable per-lane: every reachable leaf is a
        // recognized `i32` array load `a[i]` or a 16-bit constant (NOT the
        // induction or accumulator), joined by allowed lane-wise ops. This walk
        // also populates `rec.loads` / `rec.bases`.
        let mut seen = HashSet::new();
        let ok = match rec.term {
            Term::Value(v) => rec.node_ok(func, dom, v, &mut seen),
            Term::MulPair(a, b) | Term::OpPair(a, b) => {
                rec.node_ok(func, dom, a, &mut seen) && rec.node_ok(func, dom, b, &mut seen)
            }
        };
        if !ok {
            return None;
        }

        // Require at least one load: pure register reductions belong to
        // `neon_reduce` (which ran first) / `reduction_split`.
        if rec.bases.is_empty() {
            return None;
        }

        Some(rec)
    }

    /// Recognize an array load `dst = *(base + idx*elem)` and return its
    /// loop-invariant `base`. The address must be exactly `Madd(idx, k, base)`
    /// (any factor order), loaded at offset 0, where:
    /// * i32 path: `dst` is `Gpr32`, `idx = Sxtw(iv)` (the `i32→i64` widening),
    ///   `k = 4`.
    /// * i64 path: `dst` is `Gpr64`, `idx = iv` **directly** (already 64-bit, no
    ///   sign extension), `k = 8`.
    fn load_base(&self, func: &MachFunction, _dom: &DomTree, dst: VReg) -> Option<VReg> {
        let (want_class, elem_bytes) = if self.is_i64 {
            (RegClass::Gpr64, ELEM_BYTES_I64)
        } else {
            (RegClass::Gpr32, ELEM_BYTES)
        };
        let load = func.inst(*self.def.get(&dst.id)?);

        // FORM 1: LdrRI(dst[want_class], addr[Gpr64], Imm(0)).
        if load.opcode != AArch64Opcode::LdrRI
            || load.operands.len() != 3
            || dst.class != want_class
            || imm_of(&load.operands[2]) != Some(0)
        {
            return None;
        }
        let addr = vreg_of(&load.operands[1])?;
        // The address: Madd(addr, f1, f2, base) = base + f1*f2.
        let madd = func.inst(*self.def.get(&addr.id)?);
        if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
            return None;
        }
        let f1 = vreg_of(&madd.operands[1])?;
        let f2 = vreg_of(&madd.operands[2])?;
        // Resolve the base through the loop's value-preserving copies to its
        // LOOP-INVARIANT root: the bounds-guarded chain re-copies the slice
        // base every iteration, and a merged base (a Vec pointer carried
        // through a preceding growth loop) has no single def dominating the
        // preheader — invariance (all defs outside the body) is the sound
        // criterion, and copies cannot change the address, so the vector
        // preheader reading the root loads the SAME addresses the scalar
        // loop does.
        let base = resolve_loop_invariant(func, &self.loop_insts, vreg_of(&madd.operands[3])?)?;
        // One factor is the index (`sext(iv)` for i32, `iv` itself for i64), the
        // other is the constant element size (4 for i32, 8 for i64).
        let idx_ok = |factor: VReg| {
            if self.is_i64 {
                same_as_iv(func, &self.def, factor, self.iv)
            } else {
                // i32 lane path: index is `Sxtw(iv)` (pure-i32 loop) OR the i64
                // induction used directly (MIXED i32-acc / i64-index — clang/the
                // bridge index the i32 array with the widened i64 IV; sound because
                // the width check proved the i64 iv is i32-range). In the
                // bounds-guarded CHAIN the index is a value-preserving COPY of the
                // iv (a pass-through block re-copies it before addressing), so match
                // through the copy chain via same_as_iv (`iv` itself is the
                // degenerate case).
                self.is_sext_iv(func, factor) || same_as_iv(func, &self.def, factor, self.iv)
            }
        };
        let es_ok = |factor: VReg| const_value(func, &self.def, factor) == Some(elem_bytes);
        if !((idx_ok(f1) && es_ok(f2)) || (idx_ok(f2) && es_ok(f1))) {
            return None;
        }
        // Invariance established by `resolve_loop_invariant` above.
        Some(base)
    }

    /// TRACK C: recognize the i64 WIDENING DOT term `MulPair(fa, fb)` where each
    /// factor is an i32->i64 widening extend of an `a_i32[i]` load — `Sxtw` for
    /// the SIGNED dot (lowered via SMLAL/SMLAL2) or `Uxtw` for the UNSIGNED dot
    /// (UMLAL/UMLAL2). MIXED signedness has no single widening MAC and BAILS. Both
    /// loads must be i32 (`Gpr32`) `a[i]` loads at the induction index from
    /// loop-invariant bases. Populates `loads`/`bases` on success; leaves them
    /// untouched on failure (fail-closed — the caller BAILS).
    fn recognize_widening_dot(
        &mut self,
        func: &MachFunction,
        dom: &DomTree,
        fa: VReg,
        fb: VReg,
    ) -> Option<DotPlan> {
        // Both factors must be i32->i64 widening extends of the SAME signedness.
        let (la, signed_a) = self.unwrap_widen_ext(func, fa)?;
        let (lb, signed_b) = self.unwrap_widen_ext(func, fb)?;
        if signed_a != signed_b {
            return None; // mixed sign: no single-instruction widening MAC
        }
        // Each widened value must be a distinct i32 array load `a[i]` from a
        // loop-invariant base (the same address recognition the i32 dot uses,
        // forced to the i32 element width even though the accumulator is i64).
        let base_a = self.widening_load_base(func, dom, la)?;
        let base_b = self.widening_load_base(func, dom, lb)?;
        // Record the two load streams (id -> base) and the base order, DEDUPED
        // (a self-dot `a[i]*a[i]` shares one base; apply_dot_widen keys loads by
        // base, so both factors then resolve to the SAME loaded Q — correct).
        self.loads.insert(la.id, base_a);
        self.loads.insert(lb.id, base_b);
        for base in [base_a, base_b] {
            if !self.bases.iter().any(|b| b.id == base.id) {
                self.bases.push(base);
            }
        }
        Some(DotPlan {
            signed: signed_a,
            base_a,
            base_b,
        })
    }

    /// If `v` is `Sxtw(x)` (signed) or `Uxtw(x)` (unsigned) — an i32->i64 widening
    /// defined INSIDE the loop — return `(x, signed)`. The widening extend is what
    /// makes a `.2D` dot a WIDENING MAC (SMLAL/UMLAL); a factor that is not a
    /// widening extend cannot be a widening dot and BAILS.
    fn unwrap_widen_ext(&self, func: &MachFunction, v: VReg) -> Option<(VReg, bool)> {
        let id = *self.def.get(&v.id)?;
        if !self.loop_insts.contains(&id) {
            return None;
        }
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::Sxtw if inst.operands.len() == 2 => {
                Some((vreg_of(&inst.operands[1])?, true))
            }
            AArch64Opcode::Uxtw if inst.operands.len() == 2 => {
                Some((vreg_of(&inst.operands[1])?, false))
            }
            _ => None,
        }
    }

    /// Recognize an i32 array load `dst = *(base + iv*4)` for the WIDENING DOT:
    /// the loaded element is i32 (`Gpr32`, element size 4) even though the
    /// reduction accumulator is i64. Mirrors [`Self::load_base`]'s i32 branch but
    /// is usable on the `is_i64` path (where `load_base` would demand a
    /// `Gpr64`/element-8 load). The index is `iv` directly (already 64-bit on the
    /// i64 path — the i32 array indexed by the i64 induction; `same_as_iv` also
    /// threads value-preserving copies).
    fn widening_load_base(&self, func: &MachFunction, dom: &DomTree, dst: VReg) -> Option<VReg> {
        let load = func.inst(*self.def.get(&dst.id)?);
        if load.opcode != AArch64Opcode::LdrRI
            || load.operands.len() != 3
            || dst.class != RegClass::Gpr32
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
        // One factor is the index (`iv`, threaded through copies), the other the
        // i32 element size (4).
        let idx_ok = |factor: VReg| {
            same_as_iv(func, &self.def, factor, self.iv) || self.is_sext_iv(func, factor)
        };
        let es_ok = |factor: VReg| const_value(func, &self.def, factor) == Some(ELEM_BYTES);
        if !((idx_ok(f1) && es_ok(f2)) || (idx_ok(f2) && es_ok(f1))) {
            return None;
        }
        // `base` must be loop-invariant (its def dominates the preheader).
        let base_def = *self.def.get(&base.id)?;
        let base_block = block_of_inst(func, base_def)?;
        if !dom.dominates(base_block, self.preheader) {
            return None;
        }
        Some(base)
    }

    /// Number of loop-body instructions that DEFINE vreg id `id` (any def or
    /// def-use operand position, per the shared effects role model — the same
    /// model DCE/regalloc use, so multi-def loads (`LdpRI`) and def-use
    /// modifies (`Movk`) are counted exactly).
    fn count_loop_defs(&self, func: &MachFunction, id: u32) -> usize {
        self.loop_insts
            .iter()
            .filter(|&&i| inst_defines(func.inst(i), id))
            .count()
    }

    /// TRACK D: recognize the i64 WIDENING ABS-SUM term rooted at `v` —
    /// `Uxtw(copy*(phi))` where `phi` is THE chain's ABS DIAMOND result
    /// (`phi = abs_bits(x)`) and the diamond's compared value `x` is either a
    /// recognized i32 `a[iv]` load or `AddRR(load, inv)` with a loop-invariant
    /// i32 addend (either operand order). Populates `loads`/`bases` on success;
    /// the caller BAILS on `None` (fail-closed).
    ///
    /// The `Uxtw` root is REQUIRED: the scalar term is `unsigned_abs() as i64`
    /// — a ZERO-extension of the u32 abs bit pattern. The vector side
    /// reproduces it with the unsigned `UADALP` pairwise widening accumulate
    /// (`acc_j += zext64(lane_2j) + zext64(lane_2j+1)`). A `Sxtw` root would be a DIFFERENT function
    /// (sign-extension diverges on lanes with `abs_bits >= 2^31`, i.e. the
    /// `x == i32::MIN` lane, where `zext = 2^31` but `sext = -2^31`) and must
    /// NEVER match — signed/unsigned confusion here is a miscompile.
    fn recognize_widening_abs(
        &mut self,
        func: &MachFunction,
        dom: &DomTree,
        v: VReg,
        d: &AbsDiamond,
    ) -> Option<AbsPlan> {
        // Root: a single-def in-loop `Uxtw` (i32 -> i64 ZERO-extend).
        let root_id = *self.def.get(&v.id)?;
        if !self.loop_insts.contains(&root_id) || self.count_loop_defs(func, v.id) != 1 {
            return None;
        }
        let root = func.inst(root_id);
        if root.opcode != AArch64Opcode::Uxtw || root.operands.len() != 2 {
            return None;
        }
        // The Uxtw (and, below, every copy feeding it) must sit AT or AFTER the
        // diamond's join: on the linear chain, a block dominated by the join
        // executes after BOTH arm writes in the SAME iteration, so the phi it
        // reads is THIS iteration's `abs_bits(x)` — a read reachable without
        // passing the join (e.g. inside one arm) could see a STALE value on the
        // other path and must BAIL.
        let root_blk = block_of_inst(func, root_id)?;
        if !dom.dominates(d.join, root_blk) {
            return None;
        }
        // Thread SINGLE-def value-preserving copies from the Uxtw source back
        // to the diamond's phi (the latch re-copies the phi before widening).
        // `strip_copies` is NOT usable here: phi is deliberately MULTI-def (one
        // write per arm) and the def map holds an arbitrary one — stepping
        // through it would land inside a single arm.
        let mut w = vreg_of(&root.operands[1])?;
        for _ in 0..16 {
            if w.id == d.phi.id {
                break;
            }
            if self.count_loop_defs(func, w.id) != 1 {
                return None;
            }
            let wid = *self.def.get(&w.id)?;
            if !self.loop_insts.contains(&wid) {
                return None;
            }
            let wblk = block_of_inst(func, wid)?;
            if !dom.dominates(d.join, wblk) {
                return None; // a pre-join copy could capture a stale phi
            }
            let (dst, src) = copy_like(func.inst(wid))?;
            if dst != w {
                return None;
            }
            w = src;
        }
        if w != d.phi {
            return None;
        }
        // The phi is written EXACTLY twice inside the loop. The diamond
        // recognizer proved both ARM copies write it, so exactly-two ⇒ the arm
        // copies are its ONLY in-loop writers — no third path can change the
        // joined value.
        if self.count_loop_defs(func, d.phi.id) != 2 {
            return None;
        }
        // The negating arm's ZERO register: the scalar `phi = zero - x` is a
        // NEGATION only if `zero` really holds 0 at the arm. The diamond
        // recognizer proved its def-map def is `Movz #0`; here prove that def
        // is UNIQUE function-wide (a reused id could make the map resolve a
        // non-reaching writer), never written in the loop, and available at the
        // split (its block dominates it).
        if self.count_loop_defs(func, d.zero.id) != 0 || count_defs_global(func, d.zero.id) != 1 {
            return None;
        }
        let zid = *self.def.get(&d.zero.id)?;
        let zblk = block_of_inst(func, zid)?;
        if !dom.dominates(zblk, d.split) {
            return None;
        }
        // The compared/negated value `x`: exactly ONE in-loop def, ON the chain
        // (never inside an arm), in a block dominating the split — so the
        // scalar loop recomputes it before the sign test on EVERY iteration,
        // exactly as the vector lanes recompute their copy.
        if self.count_loop_defs(func, d.x.id) != 1 {
            return None;
        }
        let xid = *self.def.get(&d.x.id)?;
        if !self.loop_insts.contains(&xid) {
            return None;
        }
        let xblk = block_of_inst(func, xid)?;
        if xblk == d.arms[0] || xblk == d.arms[1] || !dom.dominates(xblk, d.split) {
            return None;
        }
        let xinst = func.inst(xid);
        // x = a[iv] (plain abs-sum) or AddRR(a[iv], inv) (invariant shift).
        let (loaded, base, inv) = match xinst.opcode {
            AArch64Opcode::LdrRI => {
                let base = self.widening_load_base(func, dom, d.x)?;
                (d.x, base, None)
            }
            AArch64Opcode::AddRR if xinst.operands.len() == 3 => {
                let a = vreg_of(&xinst.operands[1])?;
                let b = vreg_of(&xinst.operands[2])?;
                let ((load_v, base), other) =
                    if let Some(base) = self.widening_load_base(func, dom, a) {
                        ((a, base), b)
                    } else {
                        let base = self.widening_load_base(func, dom, b)?;
                        ((b, base), a)
                    };
                // The addend must be a loop-invariant i32: NEVER written inside
                // the loop, exactly ONE def function-wide (with a reused multi-
                // def id the def map cannot identify the REACHING definition),
                // and that def dominates the vectorizer preheader (so the
                // preheader `DUP` reads the very value every scalar iteration
                // reads).
                if other.class != RegClass::Gpr32
                    || self.count_loop_defs(func, other.id) != 0
                    || count_defs_global(func, other.id) != 1
                {
                    return None;
                }
                let oid = *self.def.get(&other.id)?;
                let oblk = block_of_inst(func, oid)?;
                if !dom.dominates(oblk, self.preheader) {
                    return None;
                }
                (load_v, base, Some(other))
            }
            _ => return None,
        };
        // The load result: exactly ONE in-loop def, on the chain, dominating
        // the split (same argument as `x`).
        if self.count_loop_defs(func, loaded.id) != 1 {
            return None;
        }
        let lid = *self.def.get(&loaded.id)?;
        if !self.loop_insts.contains(&lid) {
            return None;
        }
        let lblk = block_of_inst(func, lid)?;
        if lblk == d.arms[0] || lblk == d.arms[1] || !dom.dominates(lblk, d.split) {
            return None;
        }
        self.loads.insert(loaded.id, base);
        if !self.bases.iter().any(|bs| bs.id == base.id) {
            self.bases.push(base);
        }
        Some(AbsPlan { base, inv })
    }

    /// Recognize the WIDENING reduction term (TRACK B): EXACTLY a widening
    /// narrow load, or EXACTLY the SWAR `ctpop` of a ZERO-extended byte load.
    /// Populates `loads`/`bases` on success; leaves them untouched on failure
    /// (fail-closed to the generic walk, which BAILS on these leaves).
    fn recognize_widen(
        &mut self,
        func: &MachFunction,
        dom: &DomTree,
        v: VReg,
    ) -> Option<WidenPlan> {
        if v == self.iv || v == self.acc {
            return None;
        }
        // (a) the widening SUM: term IS the extended load.
        if let Some((kind, loaded, base)) = self.widen_leaf(func, dom, v) {
            self.loads.insert(loaded.id, base);
            self.bases.push(base);
            return Some(WidenPlan {
                kind,
                pop: false,
                base,
            });
        }
        // (b) the byte POPCOUNT: term IS the width-32 SWAR popcount whose single
        // input is a ZERO-extended byte load (`s += popcount(a_u8[i])`). The
        // whole SWAR chain is data-dependent on the load, so with the root and
        // the leaf both defined inside the loop every intermediate is too (a
        // load-dependent value cannot be computed before the load). ZextB ONLY:
        // popcount is byte-local only under zero extension — `Sxtb` replicates
        // the sign bit into 24 extra positions and MUST bail (sign trap).
        let root_def = *self.def.get(&v.id)?;
        if !self.loop_insts.contains(&root_def) {
            return None;
        }
        if let Some(inner) = detect_ctpop_swar_i32(func, &self.def, v)
            && let Some((kind, loaded, base)) = self.widen_leaf(func, dom, inner)
            && kind == WidenKind::ZextB
        {
            self.loads.insert(loaded.id, base);
            self.bases.push(base);
            return Some(WidenPlan {
                kind,
                pop: true,
                base,
            });
        }
        None
    }

    /// Recognize a widening narrow-load leaf `v = ext(load(a[i]))` and return
    /// `(kind, load_result, base)`. NON-mutating (the caller records). The
    /// extend and the load must both be in-loop `Gpr32` ops at offset 0, with
    /// the exact `a[i]` address:
    /// * i8:  `LdrbRI(AddRR(base, sext(iv)), 0)` (either operand order; also
    ///   accepts the equivalent `Madd(sext(iv), 1, base)` form), ext `Uxtb`/`Sxtb`.
    /// * i16: `LdrhRI(Madd(sext(iv), 2, base), 0)` (factor order free), ext
    ///   `Uxth`/`Sxth`.
    ///   `base` must be loop-invariant (def dominates the preheader).
    fn widen_leaf(
        &self,
        func: &MachFunction,
        dom: &DomTree,
        v: VReg,
    ) -> Option<(WidenKind, VReg, VReg)> {
        if v.class != RegClass::Gpr32 {
            return None;
        }
        let &ext_id = self.def.get(&v.id)?;
        if !self.loop_insts.contains(&ext_id) {
            return None;
        }
        let ext = func.inst(ext_id);
        if ext.operands.len() != 2 {
            return None;
        }
        let (kind, load_op) = match ext.opcode {
            AArch64Opcode::Uxtb => (WidenKind::ZextB, AArch64Opcode::LdrbRI),
            AArch64Opcode::Sxtb => (WidenKind::SextB, AArch64Opcode::LdrbRI),
            AArch64Opcode::Uxth => (WidenKind::ZextH, AArch64Opcode::LdrhRI),
            AArch64Opcode::Sxth => (WidenKind::SextH, AArch64Opcode::LdrhRI),
            _ => return None,
        };
        let loaded = vreg_of(&ext.operands[1])?;
        if loaded.class != RegClass::Gpr32 || loaded == self.iv || loaded == self.acc {
            return None;
        }
        let &load_id = self.def.get(&loaded.id)?;
        if !self.loop_insts.contains(&load_id) {
            return None;
        }
        let load = func.inst(load_id);
        if load.opcode != load_op
            || load.operands.len() != 3
            || imm_of(&load.operands[2]) != Some(0)
        {
            return None;
        }
        let addr = vreg_of(&load.operands[1])?;
        let base = self.widen_addr_base(func, addr, kind)?;
        // `base` must be loop-invariant: its def dominates the preheader.
        let base_def = *self.def.get(&base.id)?;
        let base_block = block_of_inst(func, base_def)?;
        if !dom.dominates(base_block, self.preheader) {
            return None;
        }
        Some((kind, loaded, base))
    }

    /// Resolve the narrow `a[i]` address for [`Self::widen_leaf`]: the exact
    /// unit-stride `base + sext(iv) * elem_bytes` shape for the kind's element
    /// size. Returns the base register (invariance checked by the caller).
    fn widen_addr_base(&self, func: &MachFunction, addr: VReg, kind: WidenKind) -> Option<VReg> {
        let &addr_def = self.def.get(&addr.id)?;
        if !self.loop_insts.contains(&addr_def) {
            return None;
        }
        let inst = func.inst(addr_def);
        match inst.opcode {
            // i8's `*1` gep folds to a plain add: `AddRR(base, sext(iv))`.
            AArch64Opcode::AddRR if kind.is_byte() && inst.operands.len() == 3 => {
                let a = vreg_of(&inst.operands[1])?;
                let b = vreg_of(&inst.operands[2])?;
                if self.is_sext_iv(func, a) {
                    Some(b)
                } else if self.is_sext_iv(func, b) {
                    Some(a)
                } else {
                    None
                }
            }
            // `Madd(idx, es, base)` (factor order free) with es == elem_bytes.
            AArch64Opcode::Madd if inst.operands.len() == 4 => {
                let f1 = vreg_of(&inst.operands[1])?;
                let f2 = vreg_of(&inst.operands[2])?;
                let base = vreg_of(&inst.operands[3])?;
                let idx_ok = |f: VReg| self.is_sext_iv(func, f);
                let es_ok = |f: VReg| const_value(func, &self.def, f) == Some(kind.elem_bytes());
                if (idx_ok(f1) && es_ok(f2)) || (idx_ok(f2) && es_ok(f1)) {
                    Some(base)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// True iff `v` is `Sxtw(x)` — where `x` is (a copy of) the induction —
    /// defined inside the loop body. Accepts a value-preserving COPY of `iv`
    /// (`MovR`/`Copy`/`AddRI(_,0)` chain) as the widened source: the
    /// bounds-guarded CHAIN's pass-through blocks re-copy the iv before the
    /// address `Madd`, so the index is `Sxtw(iv_copy)` (the 2-block shape's
    /// `Sxtw(iv)` is the degenerate zero-copy case).
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
            && matches!(
                vreg_of(&inst.operands[1]),
                Some(s) if same_as_iv(func, &self.def, s, self.iv)
            )
    }

    /// Read-only feasibility check mirroring [`lower`]: every reachable node is a
    /// recognized `i32` array load, a 16-bit constant, or an allowed lane-wise op
    /// over such. The induction and accumulator are NOT valid term values.
    /// Populates `self.loads` / `self.bases` as loads are recognized.
    fn node_ok(
        &mut self,
        func: &MachFunction,
        dom: &DomTree,
        val: VReg,
        seen: &mut HashSet<u32>,
    ) -> bool {
        if val == self.acc {
            return false; // the recurrence is not a lane-wise term value
        }
        // The induction variable: admit it as an AFFINE IOTA LEAF. [`lower`]
        // materializes, per accumulator, the exact per-lane scalar iv values as a
        // position vector, so any two's-complement arithmetic built on it computes
        // `scalar_term(iv=that lane)` exactly (all 32-bit wraps included). The
        // add-reduction is a comm+assoc monoid, so splitting these per-iteration
        // terms across lanes/accumulators reproduces the scalar left-fold.
        if val == self.iv {
            self.uses_iv = true;
            return true;
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
        // The proven STEP instruction (`iv_src = iv + 1`, R3): admit its
        // result as the SHIFTED AFFINE IOTA `iv + 1` (clang's reassociated
        // `acc ^ a[i] ^ (i+1)` reads it through a truncating MovR) even when
        // the `+1` operand's vreg id is multi-def function-wide — invisible
        // to `const_value`'s naive def map, but proven by the reaching-def
        // fold at recognition. [`lower`] maps it to `iota_base + 1`.
        if Some(def_id) == self.step_inst {
            self.uses_iv = true;
            return true;
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
        // Re-borrow operands after the load path (which mutates self) to keep the
        // borrow checker happy across the recursive calls.
        let ops = func.inst(def_id).operands.clone();
        // `.2D` (i64) has no integer multiply: any multiply (bare `MulRR` or the
        // fused `Madd`) BAILS the whole term, leaving the loop scalar.
        if self.is_i64 && matches!(opcode, MulRR | Madd) {
            return false;
        }
        match opcode {
            MulRR => {
                let (Some(a), Some(b)) = (vreg_of(&ops[1]), vreg_of(&ops[2])) else {
                    return false;
                };
                // AFFINE-only iv guard: a product of two iv-carrying factors is a
                // NON-AFFINE (quadratic) iv term — BAIL (deliberately scoped out;
                // `affine * iv-free`, e.g. `iv*3` / `iv*a[i]`, stays admitted).
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
                // Full 32-bit logical/arith immediates (const_vec now
                // materializes them via MOVZ+MOVK) — enables the SWAR popcount
                // term's masks (0x5555_5555, 0x3333_3333, 0x0f0f_0f0f, …).
                let ok_imm = matches!(imm_of(&ops[2]), Some(v) if (0..=0xFFFF_FFFF).contains(&v));
                ok_imm && self.node_ok(func, dom, a, seen)
            }
            LslRI | LsrRI | AsrRI => {
                let Some(a) = vreg_of(&ops[1]) else {
                    return false;
                };
                // A RIGHT shift of an iv-carrying value is non-affine — BAIL to
                // stay within the affine scope (a LEFT shift `iv << k == iv*2^k`
                // is affine and admitted).
                if matches!(opcode, LsrRI | AsrRI) && self.subtree_uses_iv(func, a, 64) {
                    return false;
                }
                // Per-lane shift-by-immediate ranges. The i32 path is left
                // byte-for-byte unchanged (`0..=31`). The i64 path uses the
                // exact hardware ranges: left shift `[0, 63]`; right shift
                // (USHR/SSHR) `[1, 64)` — the hardware has no 0-count
                // right-shift encoding, so BAIL on a right-shift-by-0
                // (fail-closed to the scalar loop) rather than emit an invalid
                // instruction.
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
                // `Madd(a,b,c) = a + b*c`; a product `b*c` of two iv-carrying
                // factors is non-affine — BAIL (mirrors the `MulRR` guard).
                if self.subtree_uses_iv(func, b, 64) && self.subtree_uses_iv(func, c, 64) {
                    return false;
                }
                self.node_ok(func, dom, a, seen)
                    && self.node_ok(func, dom, b, seen)
                    && self.node_ok(func, dom, c, seen)
            }
            MovR | Copy if ops.len() == 2 => {
                // A move/copy of a term value — INCLUDING an i64->i32 truncation
                // of an affine iota (`trunc(iv+1)`, clang's `(int)(i+1)` for an
                // i32 term over an i64-widened IV). Pass through to the source;
                // `lower` rebuilds the value per-lane in the i32 lane width, so
                // the truncation is implicit and exact (the iota is i32-range).
                match vreg_of(&ops[1]) {
                    Some(src) => self.node_ok(func, dom, src, seen),
                    None => false,
                }
            }
            _ => false,
        }
    }

    /// Whether the value tree rooted at `val` references the induction variable
    /// as an ARITHMETIC leaf (a load result is an opaque per-lane value, iv-free
    /// for affine-scoping). Bounded to `depth` hops; exhaustion returns `true`
    /// (conservative — forces the affine multiply/right-shift guards to BAIL).
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
        if matches!(
            inst.opcode,
            AArch64Opcode::LdrRI | AArch64Opcode::LdrbRI | AArch64Opcode::LdrhRI
        ) {
            return false; // a load result is an opaque iv-free value
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
            // The step operand must be the constant 1: via the cheap
            // single-def map, or — when isel REUSED the step vreg id across
            // the function (multi-def; the naive map resolves to an arbitrary
            // unrelated def) — via the SOUND reaching-definitions fold AT
            // THIS AddRR (exactly one def reaches it, a Movz #1, and the id
            // is not redefined inside the loop before the use). Both fail
            // closed to "not a +1 step" ⇒ the loop stays scalar.
            let step_is_one = |s: Option<VReg>| -> bool {
                let Some(s) = s else { return false };
                const_value(func, def, s) == Some(1)
                    || crate::reaching_const::unique_reaching_const(func, id, s) == Some(1)
            };
            (a == Some(iv) && step_is_one(b)) || (b == Some(iv) && step_is_one(a))
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
    acc: VReg,
    /// The reduction operator — used to combine the two halves of an `OpPair`
    /// (reassociated) term with the matching NEON vector op.
    reduce_op: ReduceOp,
    /// Accumulator index in `0..UNROLL` currently being lowered.
    accum: usize,
    vbody: BlockId,
    preheader_term: InstId,
    /// NEON arrangement operand code for same-shape arithmetic/shift ops
    /// (`ARR_S4` for the i32 `.4S` path, `ARR_D2` for the i64 `.2D` path).
    arr_code: i64,
    /// NEON element-size code used when broadcasting a scalar constant
    /// (`ELEM_S` for i32, `ELEM_D` for i64).
    elem_code: i64,
    /// Register class of the scalar half of a broadcast constant (`Gpr32` for
    /// i32, `Gpr64` for i64).
    const_class: RegClass,
    /// True on the i64 (`.2D`) path. Multiply lowering is unreachable there
    /// (recognition BAILS on any multiply) but fails closed if ever reached.
    is_i64: bool,
    /// Per-accumulator running AFFINE IOTA position vector `iv0 + width*t + vf*k
    /// + [0..vf)` (empty unless the term reads iv — the byte-identical legacy
    /// path). [`lower`] returns `posv[accum]` for the bare induction variable.
    posv: Vec<VReg>,
    /// Per-accumulator IMMUTABLE first-position base (`iv0 + vf*k + [0..vf)`,
    /// preheader-computed) used to seed SHIFTED iotas (`iv ± K`).
    iota_bases: Vec<VReg>,
    /// Shifted iotas created while lowering the CURRENT accumulator; the apply
    /// loops drain these and emit their `+= splat(width)` advances after the
    /// accumulate (mirrors [`crate::neon_minmax`]'s shifted-iota fold).
    pending_advances: Vec<VReg>,
    /// Set when the BARE iv was lowered via `posv`; the apply loops advance
    /// `posv[k]` only then.
    used_bare_iv: bool,
    /// The loop's proven STEP instruction (`iv_src = iv + 1`) — its result
    /// lowers as the shifted iota `iv + 1` (see [`Recognized::step_inst`]).
    step_inst: Option<InstId>,
    def: HashMap<u32, InstId>,
    loop_insts: HashSet<InstId>,
    /// Load-result vreg id -> base pointer (from recognition).
    loads: HashMap<u32, VReg>,
    /// `(base id, accumulator k)` -> the `.4S` vector loaded for that block.
    loaded: HashMap<(u32, usize), VReg>,
    const_cache: HashMap<i64, VReg>,
    /// Per-accumulator memo of already-lowered scalar values.
    memo: HashMap<u32, VReg>,
}

/// Emit the ROTATED scalar-tail guard at the END of the vector-drain block `vx`.
///
/// The clang-rotated scalar tail (`rec.guard` = the loop header) is a DO-WHILE
/// whose exit test is `cmp iv+1, bound; b.eq/b.ge exit` — sound only when entered
/// with `iv < bound` (so `iv+1` can reach `bound`). The vector loop steps `iv` by
/// the vector width, so when `n` is a multiple of that width the vector consumes
/// ALL `n` elements and leaves `iv == bound` (remainder 0). Falling straight into
/// the do-while there reads `a[n]` and — since `iv+1 == n+1` never equals `n` —
/// loops forever off the end of the array (SIGSEGV). So: test `iv >= bound` and
/// branch to the true loop `exit` (acc is already finalized in `vx`); for
/// remainder > 0 (`iv < bound`) control FALLS THROUGH to the do-while exactly as
/// before. `signed` picks the comparison: the i32/widen paths `Sxtw` both sides
/// and use signed `GE` (mirroring the vector header's `sxtw(iv) < main_bound`);
/// the i64 path compares the 64-bit regs directly with unsigned `HS` (mirroring
/// its unsigned `CC_LO` header guard). Edges are added by the caller's COMMIT.
///
/// The exit reads the accumulator WRITEBACK SOURCE (`acc_wb_src`), not `acc`
/// (the exit leaves from the header before the latch copies `acc_wb_src` into
/// `acc`). The drain has just seeded `acc` with the full reduction, so copy it
/// into `acc_wb_src` before the branch. When regalloc coalesces the two (common
/// on the i32 path) this is a `mov x,x` and folds away.
struct RotatedTailGuard {
    iv: VReg,
    bound: VReg,
    acc: VReg,
    acc_wb_src: VReg,
    signed: bool,
}

fn emit_rotated_tail_guard(
    func: &mut MachFunction,
    vx: BlockId,
    exit: BlockId,
    guard: RotatedTailGuard,
) {
    let RotatedTailGuard {
        iv,
        bound,
        acc,
        acc_wb_src,
        signed,
    } = guard;
    emit(
        func,
        vx,
        AArch64Opcode::MovR,
        vec![vreg(acc_wb_src), vreg(acc)],
    );
    if signed {
        let gx = alloc(func, RegClass::Gpr64);
        let nb = alloc(func, RegClass::Gpr64);
        emit(func, vx, AArch64Opcode::Sxtw, vec![vreg(gx), vreg(iv)]);
        emit(func, vx, AArch64Opcode::Sxtw, vec![vreg(nb), vreg(bound)]);
        emit(func, vx, AArch64Opcode::CmpRR, vec![vreg(gx), vreg(nb)]);
        emit(
            func,
            vx,
            AArch64Opcode::BCond,
            vec![imm(CC_GE), block(exit)],
        );
    } else {
        emit(func, vx, AArch64Opcode::CmpRR, vec![vreg(iv), vreg(bound)]);
        emit(
            func,
            vx,
            AArch64Opcode::BCond,
            vec![imm(CC_HS), block(exit)],
        );
    }
}

/// Materialize a RECONSTRUCTED constant bound (`rec.bound_const`, validated
/// to `[1, i32::MAX]` by recognition) into a fresh vreg before `pre` via the
/// isel `Movz`(+`Movk #hi, lsl #16`) convention. Used when the loop's bound
/// register is defined INSIDE the loop (so it cannot be read from the
/// preheader); the apply paths substitute this register for `rec.bound`
/// everywhere.
fn materialize_const_bound(func: &mut MachFunction, pre: InstId, k: i64, class: RegClass) -> VReg {
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

/// The register the apply paths must read the loop bound from: `rec.bound`
/// itself, or — for a reconstructed constant bound — a fresh preheader
/// materialization (never read `rec.bound`, whose def is inside the loop).
fn bound_reg(func: &mut MachFunction, rec: &Recognized, pre: InstId) -> VReg {
    match rec.bound_const {
        Some(k) => {
            let class = if rec.is_i64 {
                RegClass::Gpr64
            } else {
                RegClass::Gpr32
            };
            materialize_const_bound(func, pre, k, class)
        }
        None => rec.bound,
    }
}

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    let width = UNROLL as i64 * VF; // lanes per vector iteration (16)
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    insert_new_blocks_before(func, rec.guard, &[vh, vb, vl, vx]);

    // Internal edges among the fresh blocks only — touching the original loop's
    // entry is deferred to the COMMIT below so a lowering failure cannot leave a
    // broken CFG.
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;
    // A reconstructed constant bound is materialized FRESH here (rec.bound's
    // def is inside the loop and cannot be read from the preheader).
    let bound = bound_reg(func, rec, pre);

    // --- Preheader: UNROLL independent zeroed vector accumulators (MOVI 0).
    let vacc: Vec<VReg> = (0..UNROLL)
        .map(|_| {
            let a = alloc(func, RegClass::Fpr128);
            emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(a), imm(0)]);
            a
        })
        .collect();

    // --- Preheader: AFFINE IOTA position vectors (only when the term reads iv).
    let (posv, iota_bases, width_splat): (Vec<VReg>, Vec<VReg>, Option<VReg>) = if rec.uses_iv {
        let (p, b, ws) = build_position_vectors(
            func,
            pre,
            rec.iv,
            PositionVectorSpec {
                vf: VF,
                width,
                arr_code: ARR_S4,
                elem_code: ELEM_S,
                const_class: RegClass::Gpr32,
            },
        );
        (p, b, Some(ws))
    } else {
        (Vec::new(), Vec::new(), None)
    };

    // --- Preheader: sign-extend the loop bound once; precompute the guard
    // bound `main_bound = sxtw(bound) - (width-1)` (exact in i64 — sxtw(bound)
    // is in i32 range so the subtract cannot wrap); and initialize ONE RUNNING
    // POINTER per array stream: `p = base + sxtw(iv)*ELEM_BYTES` (iv here is
    // the loop's initial index — the preheader runs once, before the loop).
    let nb64 = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Sxtw,
        vec![vreg(nb64), vreg(bound)],
    );
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(ELEM_BYTES)],
    );
    let main_bound = alloc(func, RegClass::Gpr64);
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
    let ptrs: Vec<VReg> = rec
        .bases
        .iter()
        .map(|base| {
            let p = alloc(func, RegClass::Gpr64);
            // p = base + si0*4   (Madd d, n, m, a = a + n*m).
            emit_before(
                func,
                pre,
                AArch64Opcode::Madd,
                vec![vreg(p), vreg(si0), vreg(c_es), vreg(*base)],
            );
            p
        })
        .collect();

    // --- Vector header: guard `sxtw(iv) < main_bound` — algebraically the old
    // `sxtw(iv) + (width-1) < sxtw(bound)` with the add hoisted to the
    // preheader (exact: both sides stay within i32 range in i64 arithmetic, so
    // neither form can wrap) — enough for a full `width`-lane block.
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

    // --- Vector body: walk each stream's RUNNING pointer with `UNROLL/2`
    // post-index `LDP Qt1, Qt2, [p], #32` pair loads — bit-identical
    // (little-endian) to the 4 `LD1 {Vt.4S}, [p], #16` they replace: the SAME
    // 64 bytes per iteration in the SAME order (`Qt1 = [p]`, `Qt2 = [p+16]`,
    // `p += 32`, twice), so accumulator `k` still reads elements
    // `[iv+4k, iv+4k+4)`. The pointer advances by exactly
    // `width*ELEM_BYTES = 64` bytes per iteration while the latch advances
    // `iv` by `width`, so `p == base + sxtw(iv)*4` holds at every header
    // evaluation — the guard keeps `iv` wrap-free (see the module soundness
    // note), exactly matching the per-iteration `sxtw`+`madd` re-derivation
    // this replaces.
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

    // --- Term-root ctpop -> the PROVEN UDOT accumulate fast path. When TERM is
    // EXACTLY `ctpop(x)` (the SWAR tree at the term ROOT), each accumulator uses
    // `CNT.16B` + `UDOT(acc, cnt, ones.16B)` — 2 compute ops (clang's shape)
    // instead of CNT + 2x UADDLP + ADD. Detect once here (deterministic) and
    // materialize the all-ones byte vector ONCE in the preheader
    // (`MOVI Vd.16B, #1`). Nested ctpop uses fall through to the generic
    // lowering below (its CNT+UADDLP chain — proven, slower); if the UDOT proof
    // were ever retracted, CTPOP_UDOT_ENABLED fails closed the same way.
    let udot_inner = match rec.term {
        // UDOT accumulates into a SUM; only valid for the Add reduction.
        Term::Value(v)
            if rec.reduce_op == ReduceOp::Add && CTPOP_NEON_ENABLED && CTPOP_UDOT_ENABLED =>
        {
            detect_ctpop_swar_i32(func, &rec.def, v)
        }
        _ => None,
    };
    let vones = udot_inner.map(|_| {
        let ones = alloc(func, RegClass::Fpr128);
        emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(ones), imm(1)]);
        ones
    });

    // --- Vector body: for each accumulator, lower TERM over that accumulator's
    // loaded lanes and accumulate. Constants are shared across accumulators (the
    // per-lane `memo` is reset per accumulator; `const_cache` persists).
    let mut ctx = LowerCtx {
        iv: rec.iv,
        acc: rec.acc,
        reduce_op: rec.reduce_op,
        accum: 0,
        vbody: vb,
        preheader_term: pre,
        arr_code: ARR_S4,
        elem_code: ELEM_S,
        const_class: RegClass::Gpr32,
        is_i64: false,
        posv: posv.clone(),
        iota_bases: iota_bases.clone(),
        pending_advances: Vec::new(),
        used_bare_iv: false,
        step_inst: rec.step_inst,
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
        // Term-root `ctpop(x)` -> the PROVEN UDOT accumulate (see above):
        // `CNT.16B` gives the 16 per-byte popcounts, then `UDOT(acc, cnt, ones)`
        // adds each i32 lane's 4 byte-counts straight into that lane of the
        // accumulator: `acc[i] += popcount(x[i])` — algebraically identical to
        // the UADDLP+UADDLP+ADD it replaces. `NeonUdotV` operand 0 is a TIED
        // def-use (the accumulate READS Vd) — see `has_tied_def_use`; a plain
        // def would let regalloc/DCE treat the running sum as dead.
        if let (Some(inner), Some(ones)) = (udot_inner, vones) {
            let Some(vinner) = lower(func, &mut ctx, inner) else {
                return false;
            };
            let cnt = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vb,
                AArch64Opcode::NeonCntV,
                vec![vreg(cnt), vreg(vinner), imm(ARR_B16)],
            );
            emit(
                func,
                vb,
                AArch64Opcode::NeonUdotV,
                vec![vreg(vacc[k]), vreg(cnt), vreg(ones), imm(ARR_B16)],
            );
            continue;
        }
        let Some(vterm) = lower_term(func, &mut ctx, rec.term) else {
            return false;
        };
        emit(
            func,
            vb,
            rec.reduce_op.vector_op(),
            vec![vreg(vacc[k]), vreg(vacc[k]), vreg(vterm), imm(ARR_S4)],
        );
        // Advance this accumulator's iotas AFTER lowering consumed them:
        // posv[k] only if the BARE iv was lowered, plus every shifted iota
        // (`iv ± K`) created for this accumulator.
        if let Some(ws) = width_splat {
            if ctx.used_bare_iv {
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(posv[k]), vreg(posv[k]), vreg(ws), imm(ARR_S4)],
                );
            }
            for sh in std::mem::take(&mut ctx.pending_advances) {
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(sh), vreg(sh), vreg(ws), imm(ARR_S4)],
                );
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

    // --- Vector exit: combine the accumulators (balanced vector reductions),
    // then horizontally reduce (UMOV each lane + scalar op) and seed the scalar
    // acc. The op is the reduction operator (add / xor / or).
    let mut level = vacc.clone();
    while level.len() > 1 {
        let mut next = Vec::new();
        let mut i = 0;
        while i + 1 < level.len() {
            let d = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vx,
                rec.reduce_op.vector_op(),
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
    let lane_regs: Vec<VReg> = (0..VF)
        .map(|lane| {
            let w = alloc(func, RegClass::Gpr32);
            emit(
                func,
                vx,
                AArch64Opcode::NeonUmovGen,
                vec![vreg(w), vreg(vsum), imm(lane), imm(ELEM_S)],
            );
            w
        })
        .collect();
    let s01 = alloc(func, RegClass::Gpr32);
    let s23 = alloc(func, RegClass::Gpr32);
    let ssum = alloc(func, RegClass::Gpr32);
    let sop = rec.reduce_op.scalar_op();
    emit(
        func,
        vx,
        sop,
        vec![vreg(s01), vreg(lane_regs[0]), vreg(lane_regs[1])],
    );
    emit(
        func,
        vx,
        sop,
        vec![vreg(s23), vreg(lane_regs[2]), vreg(lane_regs[3])],
    );
    emit(func, vx, sop, vec![vreg(ssum), vreg(s01), vreg(s23)]);
    // Fold the vector partial INTO the scalar accumulator. The vector loop never
    // writes `acc`, so at this point `acc` still holds its pre-loop initial value
    // (which need NOT be the identity, e.g. `s = 5; for i: s += a[i]`);
    // combining `ssum` via the reduction op rather than overwriting keeps that
    // initial value. The scalar tail then continues from this seed. `acc OP ssum`
    // is sound for any initial acc because OP is associative + commutative.
    emit(
        func,
        vx,
        sop,
        vec![vreg(rec.acc), vreg(rec.acc), vreg(ssum)],
    );
    // ROTATED: guard the do-while tail against remainder 0 (falls through to
    // rec.guard=header otherwise). NATIVE: rec.guard is a safe top-test; branch to
    // it unconditionally.
    if let Some(exit) = rec.rotated_exit {
        emit_rotated_tail_guard(
            func,
            vx,
            exit,
            RotatedTailGuard {
                iv: rec.iv,
                bound,
                acc: rec.acc,
                acc_wb_src: rec.acc_wb_src,
                signed: true,
            },
        );
    } else {
        emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);
    }

    // --- COMMIT: everything above only added fresh, unreachable blocks (plus
    // dead preheader inits). Now splice them in front of the scalar loop by
    // redirecting the single preheader->guard edge through the vector loop. This
    // is the point of no return; it runs only after all lowering succeeded.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.guard, vh) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.guard);
    func.add_edge(rec.preheader, vh);
    func.add_edge(vx, rec.guard);
    if let Some(exit) = rec.rotated_exit {
        func.add_edge(vx, exit);
    }

    true
}

/// Vectorize an `i64` array-reduction on the `.2D` path (`2 x i64` lanes).
///
/// ## The sound i64 bounds guard (why no lane ever reads out of bounds)
///
/// `i64` has no sign-extension headroom (the i32 path widened `iv`/`n` to `i64`
/// so `iv + (WIDTH-1)` could never overflow), so a different, provably-sound
/// guard is used. Let `WIDTH = UNROLL * VF_I64 = 8` be the indices consumed per
/// vector iteration, and let `n` be the loop's signed bound (`slt`, the only
/// recognized exit test).
///
/// A dedicated **precheck** block runs once before the vector loop:
///
/// ```text
///   main_bound = n - (WIDTH-1)          // n - 7, computed unconditionally
///   if (n <s WIDTH) goto scalar_guard;  // SIGNED compare: skip the vector loop
///   goto vector_header;
/// ```
///
/// * If `n <s WIDTH` — which covers `n <= 0` **and** any `n` that is negative as
///   signed (`n >= 2^63`), and small positive `n < 8` — the vector loop is
///   skipped entirely and the untouched scalar loop runs. For `n <= 0` the
///   scalar `slt` loop runs 0 iterations, so the transform also does 0 vector +
///   0 tail iterations: identical, and **no lane is read**. (`main_bound` may
///   wrap here, but it is dead on this path.)
/// * Otherwise `n >= WIDTH = 8`, so `n` is a positive signed value in
///   `[8, 2^63-1]` and `main_bound = n - 7` lands in `[1, 2^63-8]` — no
///   underflow, no overflow.
///
/// The vector header then loops on an **unsigned** compare:
///
/// ```text
///   while (iv <u main_bound) { body reads a[iv .. iv+7]; iv += 8; }
/// ```
///
/// Because `iv` starts at the loop's initial index (`0`) and every value taken
/// is `< main_bound = n - 7 < 2^63`, all of `iv` and `main_bound` are
/// non-negative and below `2^63`, so unsigned and signed compare agree. For any
/// processed `iv` we have `iv <u n-7`, hence `iv + 7 < n` (no `u64` overflow
/// since `iv+7 < n <= 2^63-1`), so **every** lane index `iv .. iv+7` satisfies
/// `index < n` — an index the scalar loop also reads. The four accumulators walk
/// disjoint 2-lane windows `[iv+2k, iv+2k+2)` inside `[iv, iv+8)`, all `< n`.
///
/// On exit `iv` is the first multiple of `WIDTH` that is `>= main_bound = n-7`;
/// from `iv_last <u n-7` (`iv_last <= n-8`) we get `iv = iv_last + 8 <= n`, so
/// the unchanged scalar tail (`slt`, from this `iv`) finishes `[iv, n)` with a
/// valid non-negative index. Vector `[0, iv)` ⊎ scalar `[iv, n)` = `[0, n)`,
/// each index read exactly where the scalar loop read it. QED.
fn apply_i64(func: &mut MachFunction, rec: &Recognized) -> bool {
    let width = UNROLL as i64 * VF_I64; // indices per vector iteration (8)

    // Fresh blocks: precheck / vector header / body / latch / exit.
    let pv = func.create_block();
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    insert_new_blocks_before(func, rec.guard, &[pv, vh, vb, vl, vx]);

    // Internal edges among the fresh blocks only (the precheck's skip edge to
    // the original guard is an existing block target and is safe to add now; the
    // preheader→guard redirect is deferred to the COMMIT).
    func.add_edge(pv, vh);
    func.add_edge(pv, rec.guard);
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;
    // A reconstructed constant bound is materialized FRESH here (rec.bound's
    // def is inside the loop and cannot be read from the preheader).
    let bound = bound_reg(func, rec, pre);

    // --- Preheader: UNROLL zeroed vector accumulators (MOVI 0 = all lanes 0),
    // and the element-size constant (8) used by each stream's address math.
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
        vec![vreg(c_es), imm(ELEM_BYTES_I64)],
    );

    // --- Preheader: AFFINE IOTA position vectors on `.2D` (only when the term
    // reads iv). The `.2D` iota is `[0,1]`; the D-element DUP/INS/ADD all have
    // proven `.2D` forms — width-parametric with the `.4S` path.
    let (posv, iota_bases, width_splat): (Vec<VReg>, Vec<VReg>, Option<VReg>) = if rec.uses_iv {
        let (p, b, ws) = build_position_vectors(
            func,
            pre,
            rec.iv,
            PositionVectorSpec {
                vf: VF_I64,
                width,
                arr_code: ARR_D2,
                elem_code: ELEM_D,
                const_class: RegClass::Gpr64,
            },
        );
        (p, b, Some(ws))
    } else {
        (Vec::new(), Vec::new(), None)
    };

    // --- Precheck: `main_bound = n - (WIDTH-1)`; SIGNED `if n < WIDTH skip`.
    // `main_bound` is dead when the skip is taken, so its wrap for `n < WIDTH`
    // is harmless; when the skip is NOT taken `n >= WIDTH >= 1` so `main_bound`
    // is exact in `[1, 2^63-WIDTH]`.
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

    // --- Vector header: UNSIGNED `iv < main_bound` ⇒ enter the body.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Preheader: initialize ONE RUNNING POINTER per array stream:
    // `p = base + iv*8` (iv is already 64-bit — no sign extension; the
    // preheader runs once with the loop's initial index).
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

    // --- Vector body: walk each stream's RUNNING pointer with `UNROLL/2`
    // post-index `LDP Qt1, Qt2, [p], #32` pair loads — bit-identical
    // (little-endian) to the 4 `LD1 {Vt.2D}, [p], #16` they replace: the SAME
    // 64 bytes per iteration in the SAME order (`Qt1 = [p]`, `Qt2 = [p+16]`,
    // `p += 32`, twice), so accumulator `k` still reads elements
    // `[iv+2k, iv+2k+2)`. The pointer advances by exactly
    // `width*ELEM_BYTES_I64 = 64` bytes per iteration while the latch advances
    // `iv` by `width`, so `p == base + iv*8` holds at every header evaluation
    // (iv is wrap-free inside the vector loop — see the i64 bounds-guard note
    // above), exactly matching the per-iteration `madd` re-derivation this
    // replaces.
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
        reduce_op: rec.reduce_op,
        accum: 0,
        vbody: vb,
        preheader_term: pre,
        arr_code: ARR_D2,
        elem_code: ELEM_D,
        const_class: RegClass::Gpr64,
        is_i64: true,
        posv: posv.clone(),
        iota_bases: iota_bases.clone(),
        pending_advances: Vec::new(),
        used_bare_iv: false,
        step_inst: rec.step_inst,
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
        let Some(vterm) = lower_term(func, &mut ctx, rec.term) else {
            return false;
        };
        emit(
            func,
            vb,
            rec.reduce_op.vector_op(),
            vec![vreg(vacc[k]), vreg(vacc[k]), vreg(vterm), imm(ARR_D2)],
        );
        // Advance this accumulator's `.2D` iotas after lowering consumed them:
        // posv[k] only if the BARE iv was lowered, plus every shifted iota.
        if let Some(ws) = width_splat {
            if ctx.used_bare_iv {
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(posv[k]), vreg(posv[k]), vreg(ws), imm(ARR_D2)],
                );
            }
            for sh in std::mem::take(&mut ctx.pending_advances) {
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(sh), vreg(sh), vreg(ws), imm(ARR_D2)],
                );
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

    // --- Vector exit: combine accumulators (balanced `.2D` adds), horizontally
    // reduce the 2 i64 lanes (UMOV each lane to a GPR + scalar add), then seed
    // the scalar accumulator by ADDING (never overwriting — preserves a non-zero
    // initial `acc`). The scalar tail continues from this seed.
    let mut level = vacc.clone();
    while level.len() > 1 {
        let mut next = Vec::new();
        let mut i = 0;
        while i + 1 < level.len() {
            let d = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vx,
                rec.reduce_op.vector_op(),
                vec![vreg(d), vreg(level[i]), vreg(level[i + 1]), imm(ARR_D2)],
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
    let lane0 = alloc(func, RegClass::Gpr64);
    let lane1 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vx,
        AArch64Opcode::NeonUmovGen,
        vec![vreg(lane0), vreg(vsum), imm(0), imm(ELEM_D)],
    );
    emit(
        func,
        vx,
        AArch64Opcode::NeonUmovGen,
        vec![vreg(lane1), vreg(vsum), imm(1), imm(ELEM_D)],
    );
    let ssum = alloc(func, RegClass::Gpr64);
    let sop = rec.reduce_op.scalar_op();
    emit(func, vx, sop, vec![vreg(ssum), vreg(lane0), vreg(lane1)]);
    emit(
        func,
        vx,
        sop,
        vec![vreg(rec.acc), vreg(rec.acc), vreg(ssum)],
    );
    // ROTATED: guard the do-while tail against remainder 0 (unsigned, matching the
    // .2D path's CC_LO header guard). NATIVE: unconditional branch to the safe
    // top-test guard.
    if let Some(exit) = rec.rotated_exit {
        emit_rotated_tail_guard(
            func,
            vx,
            exit,
            RotatedTailGuard {
                iv: rec.iv,
                bound,
                acc: rec.acc,
                acc_wb_src: rec.acc_wb_src,
                signed: false,
            },
        );
    } else {
        emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);
    }

    // --- COMMIT: splice the fresh blocks in front of the scalar loop by
    // redirecting the single preheader→guard edge through the precheck. Point of
    // no return; runs only after all lowering succeeded.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.guard, pv) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.guard);
    func.add_edge(rec.preheader, pv);
    func.add_edge(vx, rec.guard);
    if let Some(exit) = rec.rotated_exit {
        func.add_edge(vx, exit);
    }

    true
}

/// Vectorize an i64 WIDENING DOT (`s(i64) += ext(a_i32[i]) * ext(b_i32[i])`) —
/// TRACK C — via the widening multiply-accumulate-long SMLAL/SMLAL2 (signed) or
/// UMLAL/UMLAL2 (unsigned). A HYBRID of [`apply`]'s i32 `.4S` Q-pair LOADS and
/// [`apply_i64`]'s `.2D` i64 bounds guard + horizontal drain: the loads are i32
/// (4 lanes per Q), but each accumulator is `.2D` (2 i64 lanes) and the widening
/// MAC folds a whole i32 Q (both `.4S` halves) into it.
///
/// `WIDTH = UNROLL_DOT * 4 = 32` i32 elements are consumed per vector iteration —
/// one i32 Q (4 lanes) per accumulator. [`UNROLL_DOT`] = 8 (not [`UNROLL`] = 4)
/// because the widening MAC's ~3-cycle accumulate latency x 2 chained MACs per
/// accumulator is the binding constraint (see the constant's doc). Per
/// accumulator `k`, with `qa_k`/`qb_k` the i32 Q loaded for each stream:
/// ```text
///   SMLAL.2D  vacc[k], qa_k, qb_k   ; lanes {0,1}: vacc[k].d[j] += a[j]*b[j]
///   SMLAL2.2D vacc[k], qa_k, qb_k   ; lanes {2,3}: vacc[k].d[j] += a[2+j]*b[2+j]
/// ```
/// so accumulator `k`'s two i64 lanes hold `sum a[even]*b[even]` and
/// `sum a[odd]*b[odd]` of its stripe. The drain sums all lanes into the scalar
/// accumulator (IDENTICAL to [`apply_i64`]).
///
/// ## Soundness
///
/// The bounds guard is [`apply_i64`]'s (iv/bound are `Gpr64`): a precheck
/// `main_bound = bound - (WIDTH-1)`, SIGNED skip `if bound < WIDTH`, UNSIGNED
/// header `iv < main_bound` — so every processed `iv` satisfies
/// `iv + WIDTH-1 < bound`, and all `WIDTH` i32 indices `iv..iv+31` are read
/// in bounds (the exact argument in apply_i64's doc, here WIDTH=32). The reduction
/// split needs NO extra N-bound (unlike apply_widen's `8*N < 2^31`): the `.2D`
/// lane accumulator width (64) EQUALS the scalar acc width (64), so per-lane i64
/// adds wrap mod 2^64 IDENTICALLY to the scalar; and each SMLAL/UMLAL lane equals
/// the scalar `ext(a)*ext(b)` term EXACTLY by the faithful `all_neon_smlal_proofs`
/// obligation (i32xi32->i64, no truncation). The eight disjoint-stripe accumulators
/// + horizontal fold + scalar tail reproduce the scalar left-fold (comm + assoc
///   mod 2^64) — verified overflow-inclusive.
fn apply_dot_widen(func: &mut MachFunction, rec: &Recognized) -> bool {
    let Some(plan) = rec.dot else {
        return false; // unreachable: dispatched on rec.dot.is_some()
    };
    // i32 elements consumed per vector iteration (one i32 Q per accumulator).
    let width = UNROLL_DOT as i64 * VF; // 32

    // The widening MAC opcodes (low + high `.4S` half), signed or unsigned.
    let (mlal_lo, mlal_hi) = if plan.signed {
        (AArch64Opcode::NeonSmlalV, AArch64Opcode::NeonSmlal2V)
    } else {
        (AArch64Opcode::NeonUmlalV, AArch64Opcode::NeonUmlal2V)
    };

    // Fresh blocks: precheck / vector header / body / latch / exit (apply_i64's).
    let pv = func.create_block();
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    insert_new_blocks_before(func, rec.guard, &[pv, vh, vb, vl, vx]);
    func.add_edge(pv, vh);
    func.add_edge(pv, rec.guard);
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;
    let bound = bound_reg(func, rec, pre);

    // --- Preheader: UNROLL_DOT zeroed `.2D` accumulators (MOVI 0), + the i32
    // element-size constant (4) used by each stream's address math.
    let vacc: Vec<VReg> = (0..UNROLL_DOT)
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
        vec![vreg(c_es), imm(ELEM_BYTES)],
    );

    // --- Precheck: `main_bound = bound - (WIDTH-1)`; SIGNED `if bound < WIDTH skip`
    // (apply_i64's guard; iv/bound are already 64-bit — no Sxtw). `main_bound` is
    // dead when the skip is taken, so its wrap for `bound < WIDTH` is harmless.
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

    // --- Vector header: UNSIGNED `iv < main_bound` ⇒ enter the body.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Preheader: one RUNNING POINTER per stream `p = base + iv*4` (i32
    // elements; iv is already 64-bit — the preheader runs once).
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

    // --- Vector body: walk each stream's pointer with `UNROLL_DOT/2` post-index
    // `LDP Qt1, Qt2, [p], #32` pair loads — 8 i32 Q's per stream = 32 i32
    // elements = 128 bytes/iteration (the pointer advances 128 bytes while the
    // latch advances iv by WIDTH=32, so `p == base + iv*4` at every header).
    //
    // Emission is INTERLEAVED in pair groups — for each Q pair: the group's LDP
    // per stream, then the 4 widening MACs (2 accumulators) that consume those
    // Q's — so loaded Q's die within their group and peak FPR128 pressure stays
    // ~UNROLL_DOT + 4 in-flight Q's (= 12), well inside the 24 non-callee-saved
    // v-regs. An all-loads-first order would keep 2*UNROLL_DOT = 16 loaded Q's
    // + 8 accumulators = 24 live at once — exactly the budget, and one spill in
    // this loop would forfeit the accumulator-latency win. The group order is
    // pure emission scheduling: the ops are the same, and the k-th accumulator
    // still folds exactly the k-th Q of each stream.
    let mut loaded: HashMap<(u32, usize), VReg> = HashMap::new();
    for pair in 0..UNROLL_DOT / 2 {
        for (base, p) in rec.bases.iter().zip(&ptrs) {
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

        // Per accumulator of this group, fold one i32 Q of each stream via the
        // widening MAC — SMLAL.2D (low `.4S` half {0,1}) then SMLAL2.2D (high
        // {2,3}). Vd (vacc[k]) is a tied def-use accumulator (see
        // effects::has_tied_def_use): the two ops chain read-modify-write on
        // the same accumulator register.
        for k in [2 * pair, 2 * pair + 1] {
            let (Some(&qa), Some(&qb)) = (
                loaded.get(&(plan.base_a.id, k)),
                loaded.get(&(plan.base_b.id, k)),
            ) else {
                return false;
            };
            emit(
                func,
                vb,
                mlal_lo,
                vec![vreg(vacc[k]), vreg(qa), vreg(qb), imm(ARR_S4)],
            );
            emit(
                func,
                vb,
                mlal_hi,
                vec![vreg(vacc[k]), vreg(qa), vreg(qb), imm(ARR_S4)],
            );
        }
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: advance the scalar induction by WIDTH.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector exit: balanced `.2D` combine + 2-lane horizontal reduce (UMOV
    // D[0]/D[1] to GPRs) + scalar ADD seed into `acc` (IDENTICAL to apply_i64; the
    // widening dot is add-only, so the reduction operator is always ADD).
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
                vec![vreg(d), vreg(level[i]), vreg(level[i + 1]), imm(ARR_D2)],
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
    let lane0 = alloc(func, RegClass::Gpr64);
    let lane1 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vx,
        AArch64Opcode::NeonUmovGen,
        vec![vreg(lane0), vreg(vsum), imm(0), imm(ELEM_D)],
    );
    emit(
        func,
        vx,
        AArch64Opcode::NeonUmovGen,
        vec![vreg(lane1), vreg(vsum), imm(1), imm(ELEM_D)],
    );
    let ssum = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(ssum), vreg(lane0), vreg(lane1)],
    );
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(rec.acc), vreg(rec.acc), vreg(ssum)],
    );
    // ROTATED: guard the do-while tail against remainder 0 (unsigned, matching the
    // .2D CC_LO header guard). NATIVE: unconditional branch to the safe top-test.
    if let Some(exit) = rec.rotated_exit {
        emit_rotated_tail_guard(
            func,
            vx,
            exit,
            RotatedTailGuard {
                iv: rec.iv,
                bound,
                acc: rec.acc,
                acc_wb_src: rec.acc_wb_src,
                signed: false,
            },
        );
    } else {
        emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);
    }

    // --- COMMIT (identical to apply_i64): splice the fresh blocks in front of the
    // scalar loop by redirecting the preheader→guard edge through the precheck.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.guard, pv) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.guard);
    func.add_edge(rec.preheader, pv);
    func.add_edge(vx, rec.guard);
    if let Some(exit) = rec.rotated_exit {
        func.add_edge(vx, exit);
    }

    true
}

/// Vectorize the i64 WIDENING ABS-SUM reduction — TRACK D —
/// `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))` via `ADD.4S` (invariant
/// broadcast) + the FAITHFULLY-PROVEN `ABS.4S` + the FAITHFULLY-PROVEN
/// pairwise widening ACCUMULATE `UADALP` into `.2D` i64 accumulators —
/// replacing the earlier UADDW/UADDW2 pair (2 ops per Q) with ONE op: 3 SIMD
/// ops per Q instead of 4, under LLVM's `abs.4s + uaddw.2d + uaddw2.2d`
/// issue floor (measured on M4: the 3-op form runs 0.75 cy/Q vs the 4-op
/// form's 1.05, already issue-bound at the 4 accumulators kept here).
/// Structure (fresh blocks, i64 bounds guard, `.2D` drain, commit) is
/// [`apply_dot_widen`]'s; only the per-accumulator TERM differs. Per i32 Q
/// `q_k` (4 lanes), with `vinv = DUP(inv)` hoisted to the preheader:
/// ```text
///   t = ADD.4S(q_k, vinv)   ; wrap-mod-2^32 lane add (omitted w/o inv)
///   u = ABS.4S(t)           ; two's-complement per-lane abs bit pattern
///   UADALP vacc[k].2D, u.4S ; acc_j += zext64(u_{2j}) + zext64(u_{2j+1})
/// ```
/// (`UADALP`'s Vd is a TIED def-use accumulator — the accumulate READS it,
/// like the UDOT/xMLAL class; see `has_tied_def_use`.)
///
/// ## Soundness (per-lane exactness incl. `i32::MIN`; zext-not-sext;
/// pair-grouping reassociation)
///
/// The scalar per-iteration term (validated by [`recognize_abs_diamond`] +
/// [`Recognized::recognize_widening_abs`]) is `Uxtw(abs_bits(x))`, `x =
/// wrap32(a[i] + inv)`, `abs_bits(x) = x <s 0 ? (0 - x) mod 2^32 : x`. Per lane:
/// * the scalar `AddRR` (Gpr32) and the vector `ADD.4S` both wrap mod 2^32 —
///   identical bit patterns (the proven lane-wise `NeonAddV` semantics), and
///   the DUP'd `inv` lane equals the scalar register on every lane;
/// * the FAITHFULLY-PROVEN `ABS.4S` (`NeonAbsV`,
///   `neon_lowering_proofs::proof_neon_absv_lanewise_4s`) computes exactly
///   `abs_bits` per lane — including the boundary `abs_bits(0x8000_0000) =
///   0x8000_0000` (two's-complement wraparound), which IS
///   `unsigned_abs(i32::MIN) = 2^31` as a u32 bit pattern, so the scalar
///   diamond and the vector agree on EVERY input;
/// * the scalar `Uxtw` ZERO-extends that u32 pattern to i64; the proven
///   `UADALP` (unsigned pairwise widening accumulate, D-pair obligation in
///   `all_neon_uadalp_proofs`) computes `acc_j + zext64(u_{2j}) +
///   zext64(u_{2j+1})` — the SAME zero-extension of the SAME four abs lanes
///   the replaced UADDW/UADDW2 pair added (which grouped source lanes
///   {0,2}/{1,3} into the two `.2D` lanes where UADALP groups the adjacent
///   {0,1}/{2,3}). The per-`.2D`-lane grouping DIFFERS, but the drain sums
///   BOTH `.2D` lanes of the combined accumulator into ONE scalar i64, so
///   the difference is a pure REASSOCIATION of modular (mod-2^64) addition —
///   the folded total is identical for every input (unlike FP, modular add
///   is exactly associative/commutative). A signed `SADALP` here would
///   sign-extend and be WRONG for every lane with `u_j >= 2^31` (exactly the
///   `i32::MIN` lanes); recognition therefore REQUIRES the `Uxtw` root, this
///   lowering only ever emits the unsigned form, and no signed form is even
///   encodable (`encode_uadalp` pins `U=1`).
///   The `.2D` accumulator lane width (64) equals the scalar accumulator width,
///   so per-lane adds wrap mod 2^64 identically; the four disjoint-stripe
///   accumulators + balanced combine + 2-lane fold + the UNTOUCHED scalar tail
///   `[V, n)` reproduce the scalar left-fold by two's-complement add
///   commutativity/associativity mod 2^64 — no extra bound on `n` is needed. The
///   bounds guard is [`apply_i64`]'s (WIDTH = 16): a vector block runs only when
///   `iv + 15 < n` (unsigned, behind the signed `n < 16` precheck), so every
///   vector load reads indices the scalar loop also reads; the transform is
///   purely ADDITIVE (the scalar chain is never edited). QED.
fn apply_abs_widen(func: &mut MachFunction, rec: &Recognized) -> bool {
    let Some(plan) = rec.abs else {
        return false; // unreachable: dispatched on rec.abs.is_some()
    };
    // i32 elements consumed per vector iteration (one i32 Q per accumulator).
    let width = UNROLL as i64 * VF; // 16

    // Fresh blocks: precheck / vector header / body / latch / exit.
    let pv = func.create_block();
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    insert_new_blocks_before(func, rec.guard, &[pv, vh, vb, vl, vx]);
    func.add_edge(pv, vh);
    func.add_edge(pv, rec.guard);
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;
    let bound = bound_reg(func, rec, pre);

    // --- Preheader: UNROLL zeroed `.2D` accumulators (MOVI 0); the i32
    // element-size constant (4) for the address math; the invariant-addend
    // broadcast (the proven general-register DUP). (No ones splat: UADDW takes
    // the addend directly — nothing to multiply by.)
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
        vec![vreg(c_es), imm(ELEM_BYTES)],
    );
    let vinv = plan.inv.map(|r| {
        let q = alloc(func, RegClass::Fpr128);
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonDupGen,
            vec![vreg(q), vreg(r), imm(ELEM_S)],
        );
        q
    });
    // --- Preheader: the single RUNNING POINTER `p = base + iv*4` (iv is
    // already 64-bit; the preheader runs once per loop entry).
    let ptr = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Madd,
        vec![vreg(ptr), vreg(rec.iv), vreg(c_es), vreg(plan.base)],
    );

    // --- Precheck: `main_bound = bound - (WIDTH-1)`; SIGNED `if bound < WIDTH
    // skip` ([`apply_i64`]'s guard; iv/bound are 64-bit). `main_bound` is dead
    // when the skip is taken, so its wrap for `bound < WIDTH` is harmless.
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

    // --- Vector header: UNSIGNED `iv < main_bound` ⇒ enter the body.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Vector body: walk the stream with `UNROLL/2` post-index
    // `LDP Qt1, Qt2, [p], #32` pair loads — 4 i32 Q's = 16 elements = 64
    // bytes/iteration (the latch advances iv by WIDTH=16, so `p == base + iv*4`
    // at every header).
    let mut qs: Vec<VReg> = Vec::with_capacity(UNROLL);
    for _ in 0..UNROLL / 2 {
        let q0 = alloc(func, RegClass::Fpr128);
        let q1 = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonLdpQPost,
            vec![vreg(q0), vreg(q1), vreg(ptr), imm(32)],
        );
        qs.push(q0);
        qs.push(q1);
    }
    // --- Vector body: per accumulator, the invariant add + abs + ONE
    // pairwise widening UADALP accumulate (tied def-use Vd: the accumulate
    // READS vacc[k] as the addend — has_tied_def_use). Replaces the
    // UADDW/UADDW2 pair: the SAME four zext64(u_j) terms enter the
    // accumulator's two `.2D` lanes, only grouped by ADJACENT pairs
    // ({0,1}/{2,3} instead of {0,2}/{1,3}) — a pure mod-2^64 reassociation
    // under the both-lanes drain (see the soundness walkthrough above).
    for (k, &q) in qs.iter().enumerate() {
        let t = match vinv {
            Some(vi) => {
                let s = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(s), vreg(q), vreg(vi), imm(ARR_S4)],
                );
                s
            }
            None => q,
        };
        let u = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonAbsV,
            vec![vreg(u), vreg(t), imm(ARR_S4)],
        );
        emit(
            func,
            vb,
            AArch64Opcode::NeonUadalpV,
            vec![vreg(vacc[k]), vreg(u), imm(ARR_S4)],
        );
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: advance the scalar induction by WIDTH.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector exit: balanced `.2D` combine + 2-lane horizontal reduce +
    // scalar ADD seed into `acc` (IDENTICAL to apply_dot_widen; the abs-sum is
    // add-only by recognition).
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
                vec![vreg(d), vreg(level[i]), vreg(level[i + 1]), imm(ARR_D2)],
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
    let lane0 = alloc(func, RegClass::Gpr64);
    let lane1 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vx,
        AArch64Opcode::NeonUmovGen,
        vec![vreg(lane0), vreg(vsum), imm(0), imm(ELEM_D)],
    );
    emit(
        func,
        vx,
        AArch64Opcode::NeonUmovGen,
        vec![vreg(lane1), vreg(vsum), imm(1), imm(ELEM_D)],
    );
    let ssum = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(ssum), vreg(lane0), vreg(lane1)],
    );
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(rec.acc), vreg(rec.acc), vreg(ssum)],
    );
    // FORWARD chain only (rotated_exit is always None here): the guard is the
    // loop's own `iv <u N` top-test, safe with remainder 0.
    if let Some(exit) = rec.rotated_exit {
        emit_rotated_tail_guard(
            func,
            vx,
            exit,
            RotatedTailGuard {
                iv: rec.iv,
                bound,
                acc: rec.acc,
                acc_wb_src: rec.acc_wb_src,
                signed: false,
            },
        );
    } else {
        emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);
    }

    // --- COMMIT (identical to apply_dot_widen): splice the fresh blocks in
    // front of the scalar loop by redirecting the preheader→guard edge through
    // the precheck.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.guard, pv) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.guard);
    func.add_edge(rec.preheader, pv);
    func.add_edge(vx, rec.guard);
    if let Some(exit) = rec.rotated_exit {
        func.add_edge(vx, exit);
    }

    true
}

/// Vectorize a WIDENING byte/half reduction (`s(i32) += ext(a[i8/i16][i])` or
/// `s(i32) += ctpop(zext8(a[i]))`) — TRACK B. Structure and bounds guard are
/// the i32 `.4S` path's ([`apply`]) with `WIDTH = UNROLL * lanes_per_q` (64
/// for i8, 32 for i16) narrow ELEMENTS consumed per vector iteration; only the
/// per-accumulator TERM lowering differs (the fixed widening chain — see the
/// module-level soundness argument for why each `.4S` lane is the EXACT i32
/// group sum):
/// * sum, i8:  `UADDLP/SADDLP .16B→.8H` then `.8H→.4S`, then `ADD.4S` into the
///   accumulator (zext → the proven `NeonUaddlpV`; sext → the proven
///   `NeonSaddlpV`).
/// * sum, i16: one `UADDLP/SADDLP .8H→.4S`, then `ADD.4S`.
/// * pop (u8 only): `CNT.16B` then the proven `UDOT(acc, cnt, ones.16B)`
///   accumulate (2 ops, clang's shape); when `CTPOP_UDOT_ENABLED` is off,
///   fail-closed to the proven `CNT` + `UADDLP`x2 + `ADD.4S` chain.
fn apply_widen(func: &mut MachFunction, rec: &Recognized) -> bool {
    let Some(plan) = rec.widen else {
        return false; // unreachable: dispatched on rec.widen.is_some()
    };
    let lanes_per_q = plan.kind.lanes_per_q();
    let width = UNROLL as i64 * lanes_per_q; // elements per vector iteration
    let elem_bytes = plan.kind.elem_bytes();

    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    insert_new_blocks_before(func, rec.guard, &[vh, vb, vl, vx]);

    // Internal edges among the fresh blocks only — the preheader→guard redirect
    // is deferred to the COMMIT (a lowering failure cannot break the CFG).
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;
    // A reconstructed constant bound is materialized FRESH here (rec.bound's
    // def is inside the loop and cannot be read from the preheader).
    let bound = bound_reg(func, rec, pre);

    // --- Preheader: UNROLL zeroed `.4S` vector accumulators (MOVI 0).
    let vacc: Vec<VReg> = (0..UNROLL)
        .map(|_| {
            let a = alloc(func, RegClass::Fpr128);
            emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(a), imm(0)]);
            a
        })
        .collect();
    // The all-ones byte vector for the UDOT accumulate (pop kernels only).
    let vones = (plan.pop && CTPOP_NEON_ENABLED && CTPOP_UDOT_ENABLED).then(|| {
        let ones = alloc(func, RegClass::Fpr128);
        emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(ones), imm(1)]);
        ones
    });

    // --- Preheader: sign-extend the loop bound once; `main_bound =
    // sxtw(bound) - (width-1)` (exact in i64 — sxtw(bound) is in i32 range so
    // the subtract cannot wrap); ONE RUNNING POINTER for the single stream:
    // `p = base + sxtw(iv)*elem_bytes` (iv here is the loop's initial index).
    let nb64 = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Sxtw,
        vec![vreg(nb64), vreg(bound)],
    );
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(elem_bytes)],
    );
    let main_bound = alloc(func, RegClass::Gpr64);
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
    let p = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Madd,
        vec![vreg(p), vreg(si0), vreg(c_es), vreg(plan.base)],
    );

    // --- Vector header: guard `sxtw(iv) < main_bound` — the i32 path's
    // sign-extension guard (both sides stay in i32 range in i64 arithmetic, so
    // nothing wraps) — enough for a full `width`-ELEMENT block: every element
    // index `iv .. iv+width-1` is `< n`, an index the scalar loop also reads.
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

    // --- Vector body: 2 post-index `LDP Qt1, Qt2, [p], #32` pair loads = 4 Q
    // registers = 64 bytes per iteration; Q register `k` holds elements
    // `[iv + lanes_per_q*k, iv + lanes_per_q*(k+1))` (little-endian: byte j of
    // the register IS element iv + lanes_per_q*k + j/elem_bytes's byte). The
    // pointer advances by exactly `width*elem_bytes = 64` bytes per iteration
    // while the latch advances `iv` by `width`, so `p == base +
    // sxtw(iv)*elem_bytes` holds at every header evaluation (the guard keeps
    // `iv` wrap-free).
    let mut qs: Vec<VReg> = Vec::with_capacity(UNROLL);
    for _pair in 0..UNROLL / 2 {
        let q0 = alloc(func, RegClass::Fpr128);
        let q1 = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonLdpQPost,
            vec![vreg(q0), vreg(q1), vreg(p), imm(32)],
        );
        qs.push(q0);
        qs.push(q1);
    }

    // --- Vector body: per accumulator, the FIXED widening chain (see the fn
    // doc + module soundness note; every op is faithfully proven).
    let widen_op = if plan.kind.is_signed() {
        AArch64Opcode::NeonSaddlpV
    } else {
        AArch64Opcode::NeonUaddlpV
    };
    for k in 0..UNROLL {
        let q = qs[k];
        if plan.pop {
            // ctpop kernel: CNT.16B gives the 16 per-byte popcounts.
            let cnt = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vb,
                AArch64Opcode::NeonCntV,
                vec![vreg(cnt), vreg(q), imm(ARR_B16)],
            );
            if let Some(ones) = vones {
                // Proven UDOT accumulate: acc[i] += sum of the lane's 4 byte
                // counts (each *1). Operand 0 is a TIED def-use.
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonUdotV,
                    vec![vreg(vacc[k]), vreg(cnt), vreg(ones), imm(ARR_B16)],
                );
            } else {
                // Fail-closed chain: two proven UADDLPs then ADD.4S.
                let h = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonUaddlpV,
                    vec![vreg(h), vreg(cnt), imm(ARR_B16)],
                );
                let s4 = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonUaddlpV,
                    vec![vreg(s4), vreg(h), imm(ARR_H8)],
                );
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAddV,
                    vec![vreg(vacc[k]), vreg(vacc[k]), vreg(s4), imm(ARR_S4)],
                );
            }
            continue;
        }
        // Widening SUM: collapse the Q register's narrow elements to 4 x i32
        // EXACT group sums (zext -> UADDLP, sext -> SADDLP), then ADD.4S.
        let s4 = if plan.kind.is_byte() {
            let h = alloc(func, RegClass::Fpr128);
            emit(func, vb, widen_op, vec![vreg(h), vreg(q), imm(ARR_B16)]);
            let s4 = alloc(func, RegClass::Fpr128);
            emit(func, vb, widen_op, vec![vreg(s4), vreg(h), imm(ARR_H8)]);
            s4
        } else {
            let s4 = alloc(func, RegClass::Fpr128);
            emit(func, vb, widen_op, vec![vreg(s4), vreg(q), imm(ARR_H8)]);
            s4
        };
        emit(
            func,
            vb,
            AArch64Opcode::NeonAddV,
            vec![vreg(vacc[k]), vreg(vacc[k]), vreg(s4), imm(ARR_S4)],
        );
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: advance the scalar induction by `width` ELEMENTS.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector exit: identical to the i32 path — combine the `.4S`
    // accumulators (balanced adds), horizontally reduce (UMOV each lane +
    // scalar adds), and ADD into the scalar accumulator (never overwrite:
    // preserves a non-zero initial `acc`; the scalar tail continues from it).
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
    let lane_regs: Vec<VReg> = (0..VF)
        .map(|lane| {
            let w = alloc(func, RegClass::Gpr32);
            emit(
                func,
                vx,
                AArch64Opcode::NeonUmovGen,
                vec![vreg(w), vreg(vsum), imm(lane), imm(ELEM_S)],
            );
            w
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
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(rec.acc), vreg(rec.acc), vreg(ssum)],
    );
    // ROTATED: guard the do-while tail against remainder 0 (signed sxtw+GE, as the
    // widen path Sxtw's iv/bound like the i32 path). NATIVE: unconditional branch.
    if let Some(exit) = rec.rotated_exit {
        emit_rotated_tail_guard(
            func,
            vx,
            exit,
            RotatedTailGuard {
                iv: rec.iv,
                bound,
                acc: rec.acc,
                acc_wb_src: rec.acc_wb_src,
                signed: true,
            },
        );
    } else {
        emit(func, vx, AArch64Opcode::B, vec![block(rec.guard)]);
    }

    // --- COMMIT: splice the fresh blocks in front of the scalar loop.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.guard, vh) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.guard);
    func.add_edge(rec.preheader, vh);
    func.add_edge(vx, rec.guard);
    if let Some(exit) = rec.rotated_exit {
        func.add_edge(vx, exit);
    }

    true
}

/// Lower `term` to a `4 x i32` NEON value (in the vector body). Returns `None`
/// only on an unexpected shape (recognition already proved lowerability).
fn lower_term(func: &mut MachFunction, ctx: &mut LowerCtx, term: Term) -> Option<VReg> {
    match term {
        Term::Value(v) => lower(func, ctx, v),
        Term::MulPair(a, b) => {
            // `.2D` has no integer multiply; recognition already BAILED on i64
            // multiply, so this is unreachable on the i64 path — fail closed.
            if ctx.is_i64 {
                return None;
            }
            let va = lower(func, ctx, a)?;
            let vb = lower(func, ctx, b)?;
            Some(bin(func, ctx, AArch64Opcode::NeonMulV, va, vb, true))
        }
        Term::OpPair(a, b) => {
            // Reassociated term `a OP b`, OP = the reduction operator (add/xor/or,
            // all with `.4S` and `.2D` vector forms). Lower each half per-lane and
            // combine with the SAME vector op.
            let va = lower(func, ctx, a)?;
            let vb = lower(func, ctx, b)?;
            Some(bin(func, ctx, ctx.reduce_op.vector_op(), va, vb, true))
        }
    }
}

fn lower(func: &mut MachFunction, ctx: &mut LowerCtx, val: VReg) -> Option<VReg> {
    if val == ctx.acc {
        return None;
    }
    if let Some(&v) = ctx.memo.get(&val.id) {
        return Some(v);
    }
    // The AFFINE IOTA leaf: the bare induction variable -> this accumulator's
    // per-lane position vector (holding the exact scalar iv values this
    // iteration). Only populated when recognition set `uses_iv`.
    if val == ctx.iv {
        if ctx.posv.is_empty() {
            return None;
        }
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
    // The proven STEP instruction (`iv_src = iv + 1`, R3): lower its result
    // as the shifted iota `iv + 1`. The `+1` operand's vreg id may be
    // multi-def function-wide — invisible to `const_value`/`shift_of_iv` —
    // but was proven by the reaching-def fold at recognition. (For the
    // single-def case this emits EXACTLY what the `shift_of_iv` path below
    // would: `iota_base[accum] + splat(1)`, advanced per iteration.)
    if Some(def_id) == ctx.step_inst {
        if ctx.posv.is_empty() {
            return None; // fail closed: recognition always sets uses_iv here
        }
        let v = emit_shifted_iota(func, ctx, 1);
        ctx.memo.insert(val.id, v);
        return Some(v);
    }
    // ctpop(i32) SWAR idiom -> the PROVEN NEON popcount fold (CNT.16B + two
    // UADDLP) instead of the ~15-op per-lane SWAR `.4S` chain. Both produce the
    // SAME per-i32-lane popcount, so this is a sound drop-in for the term (any
    // input `x`: fold(lower(x)) == swar_lower(x) per lane). Only on the i32 `.4S`
    // path; the i64 `.2D` path and any structural mismatch fall through to the
    // existing (already-correct) SWAR lowering below.
    if CTPOP_NEON_ENABLED
        && !ctx.is_i64
        && let Some(inner) = detect_ctpop_swar_i32(func, &ctx.def, val)
    {
        let vinner = lower(func, ctx, inner)?;
        let result = emit_popcount_fold(func, ctx.vbody, vinner);
        ctx.memo.insert(val.id, result);
        return Some(result);
    }
    let inst = func.inst(def_id);
    let opcode = inst.opcode;
    let ops = inst.operands.clone();
    use AArch64Opcode::*;
    // SHIFTED-IOTA fold: `iv ± K` becomes its own loop-carried position vector
    // — seeded `iota_base[accum] ± K` in the preheader and advanced by
    // `splat(width)` per iteration — instead of a per-iteration `pos +
    // splat(K)` add. Lane `l` holds `(iv0 + vf*k + l ± K) + width*t = scalar
    // (iv ± K)` at every iteration `t`, wrapping mod 2^lane-width exactly like
    // the scalar AddRI/SubRI — the same per-lane-exactness argument as the
    // bare iota, one op cheaper per accumulator-iteration.
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
        MovR | Copy => {
            // Pass through a move/copy (incl. an i64->i32 truncation of an affine
            // iota): the source is rebuilt per-lane in the i32 lane width.
            return lower(func, ctx, vreg_of(&ops[1])?);
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

/// Materialize the shifted iota for `iv + k` (`k != 0`): a fresh loop-carried
/// vector seeded `iota_base[accum] ± |k|` in the preheader (proven per-lane
/// `ADD`/`SUB`; the splat comes from the 32-bit-capable, cached [`const_vec`])
/// and registered for the per-iteration `+= splat(width)` advance.
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
    // Materialize the full 32-bit lane value in a GPR: MOVZ of the low
    // halfword, then MOVK of the high halfword when non-zero (so masks like
    // 0x5555_5555 used by the SWAR popcount term work, not just 16-bit
    // constants). Both are already-modeled, proven ops.
    let lo = value & 0xFFFF;
    let hi = (value >> 16) & 0xFFFF;
    emit_before(
        func,
        ctx.preheader_term,
        AArch64Opcode::Movz,
        vec![vreg(w), imm(lo)],
    );
    if hi != 0 {
        emit_before(
            func,
            ctx.preheader_term,
            AArch64Opcode::Movk,
            vec![vreg(w), imm(hi), imm(16)],
        );
    }
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
// ctpop(i32) SWAR idiom recognition + proven NEON popcount fold
// ---------------------------------------------------------------------------
//
// `trust_ir` `ctpop i32 %x` has no scalar AArch64 instruction, so isel expands it
// to the width-32 SWAR bit-twiddle (isel.rs `emit_ctpop_swar`):
//   t1 = x >> 1;            paired = t1 & 0x5555_5555;   t3 = x - paired
//   low  = t3 & 0x3333_3333;  t5 = t3 >> 2;  high = t5 & 0x3333_3333;  t7 = low+high
//   t9 = t7 + (t7 >> 4);    t10 = t9 & 0x0f0f_0f0f
//   t12 = t10 + (t10 >> 8); t14 = t12 + (t12 >> 16);     root = t14 & 0x3f
// [`detect_ctpop_swar_i32`] matches that EXACT tree (exact masks/shifts, add
// commutativity handled) rooted at `root` and returns its single input `x`. Any
// deviation returns `None`, so the caller falls back to the SWAR `.4S` lowering
// (correct, just slower) — never a miscompile.

fn swar_inst<'a>(
    func: &'a MachFunction,
    def: &HashMap<u32, InstId>,
    v: VReg,
) -> Option<&'a MachInst> {
    Some(func.inst(*def.get(&v.id)?))
}

/// `AndRI(_, src, imm)` -> `(src, imm)`.
fn swar_and_imm(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<(VReg, i64)> {
    let inst = swar_inst(func, def, v)?;
    if inst.opcode == AArch64Opcode::AndRI && inst.operands.len() == 3 {
        Some((vreg_of(&inst.operands[1])?, imm_of(&inst.operands[2])?))
    } else {
        None
    }
}

/// `LsrRI(_, src, sh)` -> `(src, sh)`.
fn swar_lsr_imm(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<(VReg, i64)> {
    let inst = swar_inst(func, def, v)?;
    if inst.opcode == AArch64Opcode::LsrRI && inst.operands.len() == 3 {
        Some((vreg_of(&inst.operands[1])?, imm_of(&inst.operands[2])?))
    } else {
        None
    }
}

/// `SubRR(_, a, b)` -> `(a, b)`.
fn swar_sub_rr(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<(VReg, VReg)> {
    let inst = swar_inst(func, def, v)?;
    if inst.opcode == AArch64Opcode::SubRR && inst.operands.len() == 3 {
        Some((vreg_of(&inst.operands[1])?, vreg_of(&inst.operands[2])?))
    } else {
        None
    }
}

/// `AddRR(_, a, b)` -> `(a, b)`.
fn swar_add_rr(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<(VReg, VReg)> {
    let inst = swar_inst(func, def, v)?;
    if inst.opcode == AArch64Opcode::AddRR && inst.operands.len() == 3 {
        Some((vreg_of(&inst.operands[1])?, vreg_of(&inst.operands[2])?))
    } else {
        None
    }
}

/// If `v = AddRR(a, b)` where one operand is the other `LsrRI`-shifted right by
/// `shift`, return the un-shifted base operand (`x` in `x + (x >> shift)`).
/// Handles ADD commutativity.
fn swar_add_self_lsr(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    v: VReg,
    shift: i64,
) -> Option<VReg> {
    let (a, b) = swar_add_rr(func, def, v)?;
    if let Some((s, sh)) = swar_lsr_imm(func, def, b)
        && sh == shift
        && s == a
    {
        return Some(a);
    }
    if let Some((s, sh)) = swar_lsr_imm(func, def, a)
        && sh == shift
        && s == b
    {
        return Some(b);
    }
    None
}

/// Match `low + high` where `low = X & 0x3333_3333` and
/// `high = (X >> 2) & 0x3333_3333`, returning the common `X`. Handles the ADD's
/// operand order.
fn swar_pairs(func: &MachFunction, def: &HashMap<u32, InstId>, a: VReg, b: VReg) -> Option<VReg> {
    let try_order = |lo: VReg, hi: VReg| -> Option<VReg> {
        let (x, m_lo) = swar_and_imm(func, def, lo)?;
        if m_lo != 0x3333_3333 {
            return None;
        }
        let (shifted, m_hi) = swar_and_imm(func, def, hi)?;
        if m_hi != 0x3333_3333 {
            return None;
        }
        let (src, sh) = swar_lsr_imm(func, def, shifted)?;
        if sh != 2 || src != x {
            return None;
        }
        Some(x)
    };
    try_order(a, b).or_else(|| try_order(b, a))
}

/// If `root` is EXACTLY the width-32 SWAR population count of a single value,
/// return that value (the `ctpop` input). Structural, constant-exact match; any
/// deviation returns `None`.
fn detect_ctpop_swar_i32(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    root: VReg,
) -> Option<VReg> {
    // root = t14 & 0x3f
    let (t14, m) = swar_and_imm(func, def, root)?;
    if m != 0x3f {
        return None;
    }
    // t14 = t12 + (t12 >> 16)
    let t12 = swar_add_self_lsr(func, def, t14, 16)?;
    // t12 = t10 + (t10 >> 8)
    let t10 = swar_add_self_lsr(func, def, t12, 8)?;
    // t10 = t9 & 0x0f0f_0f0f
    let (t9, m) = swar_and_imm(func, def, t10)?;
    if m != 0x0f0f_0f0f {
        return None;
    }
    // t9 = t7 + (t7 >> 4)
    let t7 = swar_add_self_lsr(func, def, t9, 4)?;
    // t7 = (t3 & 0x3333_3333) + ((t3 >> 2) & 0x3333_3333)
    let (pa, pb) = swar_add_rr(func, def, t7)?;
    let t3 = swar_pairs(func, def, pa, pb)?;
    // t3 = t0 - ((t0 >> 1) & 0x5555_5555)
    let (t0, paired) = swar_sub_rr(func, def, t3)?;
    let (t1, m) = swar_and_imm(func, def, paired)?;
    if m != 0x5555_5555 {
        return None;
    }
    let (t0b, sh) = swar_lsr_imm(func, def, t1)?;
    if sh != 1 || t0b != t0 {
        return None;
    }
    Some(t0)
}

/// Emit the PROVEN popcount fold over a 128-bit `.4S` vector `v` (lane k = some
/// i32): `CNT.16B` (16 per-byte popcounts) -> `UADDLP .16B→.8H` -> `UADDLP
/// .8H→.4S`, yielding a `.4S` vector whose lane k is `popcount(v_lane_k)`. Each
/// op is credited by a faithful D-pair proof (NeonCntV / NeonUaddlpV).
///
/// This is the general (value-producing) form, used when the ctpop is NESTED
/// inside a larger term. A term-root `ctpop(x)` instead takes the UDOT
/// accumulate fast path in `apply` (2 compute ops); the UADDLP chain here stays
/// proven and in place both as the nested fallback and as the fail-closed path
/// if `CTPOP_UDOT_ENABLED` is ever flipped off.
fn emit_popcount_fold(func: &mut MachFunction, block: BlockId, v: VReg) -> VReg {
    let cnt = alloc(func, RegClass::Fpr128);
    emit(
        func,
        block,
        AArch64Opcode::NeonCntV,
        vec![vreg(cnt), vreg(v), imm(ARR_B16)],
    );
    let h = alloc(func, RegClass::Fpr128);
    emit(
        func,
        block,
        AArch64Opcode::NeonUaddlpV,
        vec![vreg(h), vreg(cnt), imm(ARR_B16)],
    );
    let s = alloc(func, RegClass::Fpr128);
    emit(
        func,
        block,
        AArch64Opcode::NeonUaddlpV,
        vec![vreg(s), vreg(h), imm(ARR_H8)],
    );
    s
}

// ---------------------------------------------------------------------------
// Small local IR helpers (kept independent of neon_reduce.rs / vectorize.rs)
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

// ---------------------------------------------------------------------------
// AFFINE IOTA position machinery (shared by apply / apply_i64 when the term
// reads the induction variable). Mirrors neon_minmax's argmin index vectors.
// ---------------------------------------------------------------------------

/// Broadcast a small constant across every lane in the preheader
/// (`Movz Wt/Xt,#v` + `DUP Vd.4S/.2D, Wt/Xt`). Both already-modeled/proven ops.
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
/// `MOVI Vd,#0` (lane 0 done) then `INS Vd.S/D[j], Wj` for `j ∈ [1, vf)`. `.4S`
/// iota is `[0,1,2,3]`; `.2D` iota is `[0,1]`. MOVI/INS/Movz are already-modeled.
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

/// Copy a vector register (`ORR Vd, Vn, Vn` = ISA `MOV Vd, Vn`), a faithfully
/// proven whole-register op — gives each `posv[k]` an independent register.
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

/// Build the per-accumulator AFFINE IOTA position vectors in the preheader and
/// the per-iteration `splat(width)` increment. `posv[k]` lane `l` starts at
/// `iv0 + vf*k + l`; the caller advances each by `width_splat` per iteration, so
/// at iteration `t` it holds `iv0 + width*t + vf*k + l` — exactly the scalar iv
/// for the element accumulator `k` folds into lane `l`. Only called when the
/// term reads iv; returns `(posv, iota_bases, width_splat)` — the bases are the
/// IMMUTABLE preheader first-position values used to seed shifted iotas.
struct PositionVectorSpec {
    vf: i64,
    width: i64,
    arr_code: i64,
    elem_code: i64,
    const_class: RegClass,
}

fn build_position_vectors(
    func: &mut MachFunction,
    pre: InstId,
    iv: VReg,
    spec: PositionVectorSpec,
) -> (Vec<VReg>, Vec<VReg>, VReg) {
    let PositionVectorSpec {
        vf,
        width,
        arr_code,
        elem_code,
        const_class,
    } = spec;
    let iota = build_iota(func, pre, vf, elem_code, const_class);
    let dup_iv = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonDupGen,
        vec![vreg(dup_iv), vreg(iv), imm(elem_code)],
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
        posv.push(vcopy(func, pre, base_off));
        bases.push(base_off);
    }
    let width_splat = splat_const(func, pre, width, elem_code, const_class);
    (posv, bases, width_splat)
}

/// SOUNDNESS for the ROTATED shape: `apply` rewires preheader -> vector-header,
/// BYPASSING the block where clang initializes the induction register (the loop
/// "guard"). If the iv is defined ONLY in that bypassed block, the vector loop
/// reads an UNINITIALIZED iv (P0 — it then usually falls to the scalar tail, but
/// occasionally runs with a garbage index and miscompiles) and, on exit through
/// the guard, the scalar tail re-runs from 0. Require that SOME definition of
/// `iv` DOMINATES the preheader (true for trust-cg's NATIVE shape — iv init is in
/// the preheader; FALSE for clang's rotated shape — iv init is in the guard).
/// Fail-closed to scalar otherwise. Regression: uninitialized-iv read found by
/// the alias-versioning workflow's adversarial n=0..140 differential.
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
            if crate::effects::inst_defines_vreg(func.inst(inst_id), iv) {
                return true;
            }
        }
    }
    false
}

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    if boi_timing_enabled() {
        let t = std::time::Instant::now();
        let r = build_def_map_inner(func);
        BDM_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        BDM_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return r;
    }
    build_def_map_inner(func)
}

pub(crate) static BDM_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static BDM_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn build_def_map_inner(func: &MachFunction) -> HashMap<u32, InstId> {
    crate::effects::build_reaching_def_map(func)
}

/// True iff `inst` DEFINES vreg id `id` at any def or def-use operand position,
/// per the shared effects role model (the model DCE/regalloc use) — so multi-def
/// loads (`LdpRI`/`NeonLdpQPost`) and def-use modifies (`Movk`) count exactly.
/// Used by the TRACK D single-def rigor checks.
fn inst_defines(inst: &MachInst, id: u32) -> bool {
    let mut hit = false;
    crate::effects::aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| {
        if let Some(MachOperand::VReg(dst)) = inst.operands.get(pos)
            && dst.id == id
        {
            hit = true;
        }
    });
    hit
}

/// Number of instructions in the WHOLE function (live, block-attached) that
/// define vreg id `id`. Fail-closed companion to the def map: an id with MORE
/// than one def cannot be resolved to its reaching definition by the map, so
/// TRACK D's loop-invariant leaf check demands exactly one.
fn count_defs_global(func: &MachFunction, id: u32) -> usize {
    crate::effects::live_def_count(func, id)
}

/// DIAGNOSTIC (default off): accumulated nanoseconds and call count inside
/// `block_of_inst`, so its share of `recognize` can be MEASURED rather than
/// inferred from the fact that it is O(instructions). Enabled by `TCG_TIME_BOI=1`.
pub(crate) static BOI_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static BOI_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

pub(crate) fn boi_timing_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TCG_TIME_BOI").is_some())
}

fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    if boi_timing_enabled() {
        let t = std::time::Instant::now();
        let r = block_of_inst_inner(func, target);
        BOI_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        BOI_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return r;
    }
    block_of_inst_inner(func, target)
}

fn block_of_inst_inner(func: &MachFunction, target: InstId) -> Option<BlockId> {
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

    /// Build the rotated array-reduction loop `for i in 0..n: acc += a[i]` in the
    /// exact shape `loop-latch-layout` emits (guard / header / latch), plus a
    /// second array `b` and a `mul` when `dot` is set (dot product).
    ///
    /// Register map: v0=base_a(ptr), v1=n, v2=base_b(ptr). v3=0, v4=1, v40=4(es).
    /// iv=v5, acc=v6.
    fn build_array_loop(dot: bool, es: i64) -> MachFunction {
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
        // Preheader: base pointers + constants; iv=0, acc=0.
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a (self-copy placeholder)
        push(&mut func, bb0, Copy, vec![v(1), v(1)]); // n
        push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // base_b
        push(&mut func, bb0, Movz, vec![v(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v(4), i(1)]);
        push(&mut func, bb0, Movz, vec![v64(40), i(es)]); // element size
        push(&mut func, bb0, MovR, vec![v(5), v(3)]); // iv = 0
        push(&mut func, bb0, MovR, vec![v(6), v(3)]); // acc = 0
        push(&mut func, bb0, B, vec![b(guard)]);
        // Guard: cmp iv,n; b.lt header; b exit.
        push(&mut func, guard, CmpRR, vec![v(5), v(1)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        // Header: address(es) + load(s) + term + reduction + step.
        push(&mut func, header, Sxtw, vec![v64(10), v(5)]);
        push(
            &mut func,
            header,
            Madd,
            vec![v64(11), v64(10), v64(40), v64(0)],
        ); // a + iv*es
        push(&mut func, header, LdrRI, vec![v(12), v64(11), i(0)]); // load a[i]
        if dot {
            push(&mut func, header, Sxtw, vec![v64(13), v(5)]);
            push(
                &mut func,
                header,
                Madd,
                vec![v64(14), v64(13), v64(40), v64(2)],
            ); // b + iv*es
            push(&mut func, header, LdrRI, vec![v(15), v64(14), i(0)]); // load b[i]
            push(&mut func, header, Madd, vec![v(16), v(12), v(15), v(6)]); // acc + a[i]*b[i]
            push(&mut func, header, AddRR, vec![v(17), v(5), v(4)]); // iv+1
            push(&mut func, header, B, vec![b(latch)]);
            push(&mut func, latch, AddRI, vec![v(5), v(17), i(0)]);
            push(&mut func, latch, AddRI, vec![v(6), v(16), i(0)]);
        } else {
            push(&mut func, header, AddRR, vec![v(16), v(6), v(12)]); // acc + a[i]
            push(&mut func, header, AddRR, vec![v(17), v(5), v(4)]); // iv+1
            push(&mut func, header, B, vec![b(latch)]);
            push(&mut func, latch, AddRI, vec![v(5), v(17), i(0)]);
            push(&mut func, latch, AddRI, vec![v(6), v(16), i(0)]);
        }
        push(&mut func, latch, CmpRR, vec![v(5), v(1)]);
        push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
        // Exit.
        push(&mut func, exit, MovR, vec![v(20), v(6)]);
        push(&mut func, exit, Ret, vec![]);

        func.add_edge(bb0, guard);
        func.add_edge(guard, header);
        func.add_edge(guard, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
        func.next_vreg = 128;
        func
    }

    #[test]
    fn vectorizes_array_sum() {
        let mut func = build_array_loop(false, ELEM_BYTES);
        let mut pass = NeonArrayPass::new();
        assert!(pass.run(&mut func), "should fire on `acc += a[i]`");
        assert_eq!(pass.fired(), 1);
        // 4 accumulators × 1 array = 2 LDP Q-pair loads; 4 accumulate + reduce adds.
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL / 2,
            "2 LDP q,q"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonLd1Post),
            0,
            "LD1 replaced by LDP"
        );
        assert!(
            count(&func, AArch64Opcode::NeonAddV) >= UNROLL,
            "accumulate"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmovGen),
            4,
            "reduce 4 lanes"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonMovi), UNROLL, "zeroed accs");
        assert_eq!(count(&func, AArch64Opcode::NeonMulV), 0, "sum: no mul");
        // No iv term: the iota machinery is NOT emitted (byte-identical legacy).
        assert_eq!(count(&func, AArch64Opcode::NeonDupGen), 0, "no iota");
        assert_eq!(count(&func, AArch64Opcode::NeonInsGen), 0, "no iota");
    }

    /// Build `for i in 0..n: acc += TERM ^ a[i]` where TERM is the affine iv
    /// expression `i*3+7` (`square=false`) or the NON-AFFINE `i*i`
    /// (`square=true`). Register map mirrors `build_array_loop`: v0=base_a, v1=n,
    /// v3=0, v4=1, v40=4(es). iv=v5, acc=v6, load a[i]=v12.
    fn build_iv_term_loop(square: bool) -> MachFunction {
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
        push(&mut func, bb0, Movz, vec![v(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v(4), i(1)]);
        push(&mut func, bb0, Movz, vec![v(7), i(3)]); // constant 3
        push(&mut func, bb0, Movz, vec![v64(40), i(ELEM_BYTES)]);
        push(&mut func, bb0, MovR, vec![v(5), v(3)]); // iv = 0
        push(&mut func, bb0, MovR, vec![v(6), v(3)]); // acc = 0
        push(&mut func, bb0, B, vec![b(guard)]);
        push(&mut func, guard, CmpRR, vec![v(5), v(1)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        push(&mut func, header, Sxtw, vec![v64(10), v(5)]);
        push(
            &mut func,
            header,
            Madd,
            vec![v64(11), v64(10), v64(40), v64(0)],
        );
        push(&mut func, header, LdrRI, vec![v(12), v64(11), i(0)]); // a[i]
        if square {
            push(&mut func, header, MulRR, vec![v(30), v(5), v(5)]); // iv*iv (non-affine)
            push(&mut func, header, EorRR, vec![v(32), v(30), v(12)]);
        } else {
            push(&mut func, header, MulRR, vec![v(30), v(5), v(7)]); // iv*3
            push(&mut func, header, AddRI, vec![v(31), v(30), i(7)]); // iv*3+7
            push(&mut func, header, EorRR, vec![v(32), v(31), v(12)]);
        }
        push(&mut func, header, AddRR, vec![v(16), v(6), v(32)]); // acc += term
        push(&mut func, header, AddRR, vec![v(17), v(5), v(4)]); // iv+1
        push(&mut func, header, B, vec![b(latch)]);
        push(&mut func, latch, AddRI, vec![v(5), v(17), i(0)]);
        push(&mut func, latch, AddRI, vec![v(6), v(16), i(0)]);
        push(&mut func, latch, CmpRR, vec![v(5), v(1)]);
        push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, exit, MovR, vec![v(20), v(6)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, guard);
        func.add_edge(guard, header);
        func.add_edge(guard, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
        func.next_vreg = 128;
        func
    }

    #[test]
    fn vectorizes_add_iv_affine_term() {
        // `acc += (i*3+7) ^ a[i]` — affine iota term ⇒ fires with the iota
        // machinery (DUP iv splat + MOVI/INS iota + per-lane MUL/ADD/EOR).
        let mut func = build_iv_term_loop(false);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "affine iv term add reduction should vectorize"
        );
        assert_eq!(pass.fired(), 1);
        assert!(
            count(&func, AArch64Opcode::NeonDupGen) >= 1,
            "iv splat (DUP)"
        );
        assert!(
            count(&func, AArch64Opcode::NeonInsGen) >= 1,
            "iota lanes via INS"
        );
        assert!(
            count(&func, AArch64Opcode::NeonMulV) >= UNROLL,
            "iv*3 per accumulator"
        );
        assert!(
            count(&func, AArch64Opcode::NeonEorV) >= UNROLL,
            "term ^ a[i] per accumulator"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL / 2,
            "2 LDP q,q"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmovGen),
            4,
            "reduce 4 lanes"
        );
    }

    #[test]
    fn bails_on_add_iv_square_nonaffine() {
        // `acc += (i*i) ^ a[i]` — quadratic (NON-AFFINE) ⇒ must BAIL, no NEON.
        let mut func = build_iv_term_loop(true);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "non-affine iv*iv term must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonDupGen), 0, "no iota");
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            0,
            "no NEON emitted"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonLd1Post),
            0,
            "no NEON emitted"
        );
    }

    /// Build `for i in 0..n: acc += popcount(a[i])` (or, with `nested`,
    /// `acc += popcount(a[i]) + a[i]` — the ctpop NESTED inside a larger term) in
    /// the rotated shape, where the header carries the EXACT width-32 SWAR
    /// expansion isel emits for `ctpop i32` (LSR / AND-with-32-bit-mask / SUB /
    /// ADD). Register map: v0=base_a, v1=n, v3=0, v4=1, v40=4(es). iv=v5, acc=v6.
    /// Load a[i]=v12; SWAR temps v20..v34; popcount root = v34.
    fn build_popcount_loop(nested: bool) -> MachFunction {
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
        push(&mut func, bb0, Movz, vec![v(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v(4), i(1)]);
        push(&mut func, bb0, Movz, vec![v64(40), i(ELEM_BYTES)]);
        push(&mut func, bb0, MovR, vec![v(5), v(3)]); // iv = 0
        push(&mut func, bb0, MovR, vec![v(6), v(3)]); // acc = 0
        push(&mut func, bb0, B, vec![b(guard)]);
        push(&mut func, guard, CmpRR, vec![v(5), v(1)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        // Header: address + load a[i] (=v12).
        push(&mut func, header, Sxtw, vec![v64(10), v(5)]);
        push(
            &mut func,
            header,
            Madd,
            vec![v64(11), v64(10), v64(40), v64(0)],
        );
        push(&mut func, header, LdrRI, vec![v(12), v64(11), i(0)]);
        // SWAR ctpop(i32) of v12 (the exact emit_ctpop_swar width-32 sequence).
        push(&mut func, header, LsrRI, vec![v(20), v(12), i(1)]); // x>>1
        push(&mut func, header, AndRI, vec![v(21), v(20), i(0x5555_5555)]); // paired
        push(&mut func, header, SubRR, vec![v(22), v(12), v(21)]); // t3 = x - paired
        push(&mut func, header, AndRI, vec![v(23), v(22), i(0x3333_3333)]); // low
        push(&mut func, header, LsrRI, vec![v(24), v(22), i(2)]); // t3>>2
        push(&mut func, header, AndRI, vec![v(25), v(24), i(0x3333_3333)]); // high
        push(&mut func, header, AddRR, vec![v(26), v(23), v(25)]); // t7
        push(&mut func, header, LsrRI, vec![v(27), v(26), i(4)]); // t7>>4
        push(&mut func, header, AddRR, vec![v(28), v(26), v(27)]); // t9
        push(&mut func, header, AndRI, vec![v(29), v(28), i(0x0f0f_0f0f)]); // t10
        push(&mut func, header, LsrRI, vec![v(30), v(29), i(8)]); // t10>>8
        push(&mut func, header, AddRR, vec![v(31), v(29), v(30)]); // t12
        push(&mut func, header, LsrRI, vec![v(32), v(31), i(16)]); // t12>>16
        push(&mut func, header, AddRR, vec![v(33), v(31), v(32)]); // t14
        push(&mut func, header, AndRI, vec![v(34), v(33), i(0x3f)]); // popcount root
        // Term root: popcount(a[i]) itself, or (nested) popcount(a[i]) + a[i].
        let term = if nested {
            push(&mut func, header, AddRR, vec![v(35), v(34), v(12)]);
            35
        } else {
            34
        };
        // acc += term; iv += 1.
        push(&mut func, header, AddRR, vec![v(16), v(6), v(term)]);
        push(&mut func, header, AddRR, vec![v(17), v(5), v(4)]);
        push(&mut func, header, B, vec![b(latch)]);
        push(&mut func, latch, AddRI, vec![v(5), v(17), i(0)]);
        push(&mut func, latch, AddRI, vec![v(6), v(16), i(0)]);
        push(&mut func, latch, CmpRR, vec![v(5), v(1)]);
        push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, exit, MovR, vec![v(50), v(6)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, guard);
        func.add_edge(guard, header);
        func.add_edge(guard, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
        func.next_vreg = 256;
        func
    }

    #[test]
    fn vectorizes_popcount_via_cnt_udot() {
        let mut func = build_popcount_loop(false);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "should fire on `acc += popcount(a[i])`"
        );
        assert_eq!(pass.fired(), 1);
        // TERM is EXACTLY `ctpop(a[i])`, so each of the UNROLL accumulators takes
        // the PROVEN UDOT fast path: one CNT.16B then one accumulating
        // `UDOT(acc, cnt, ones)` — 2 compute ops (clang's shape). NO UADDLP and NO
        // separate NeonAddV accumulate remain in the body (the only NeonAddV are
        // the UNROLL-1 combine adds in the vector exit).
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL / 2,
            "2 LDP q,q"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonCntV), UNROLL, "4 CNT.16B");
        assert_eq!(count(&func, AArch64Opcode::NeonUdotV), UNROLL, "4 UDOT.4S");
        assert_eq!(
            count(&func, AArch64Opcode::NeonUaddlpV),
            0,
            "UADDLP chain replaced by the accumulating UDOT"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonAddV),
            UNROLL - 1,
            "no per-accumulator NeonAddV left in the body — UDOT accumulates; only \
             the vector-exit combine adds remain"
        );
        // The all-ones byte vector is materialized ONCE (preheader), on top of the
        // UNROLL zeroed accumulators.
        assert_eq!(
            count(&func, AArch64Opcode::NeonMovi),
            UNROLL + 1,
            "4 accs + ones"
        );
        // The SWAR term is NOT lowered lane-wise: no per-lane shift-immediate ops
        // remain from the popcount bit-twiddle (the fold replaced them).
        assert_eq!(
            count(&func, AArch64Opcode::NeonUshrVImm),
            0,
            "SWAR right-shifts replaced by the CNT+UDOT fold"
        );
    }

    #[test]
    fn nested_popcount_term_keeps_uaddlp_chain() {
        // `acc += popcount(a[i]) + a[i]`: the ctpop is NESTED inside the term, so
        // the accumulating UDOT is NOT sound there (it can only add into the
        // accumulator root). The generic lowering must keep the PROVEN
        // CNT + 2x UADDLP value-producing chain and a NeonAddV accumulate.
        let mut func = build_popcount_loop(true);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "should fire on `acc += popcount(a[i]) + a[i]`"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(count(&func, AArch64Opcode::NeonCntV), UNROLL, "4 CNT.16B");
        assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 0, "nested: NO UDOT");
        assert_eq!(
            count(&func, AArch64Opcode::NeonUaddlpV),
            2 * UNROLL,
            "8 UADDLP (2 per accumulator: .16B->.8H then .8H->.4S)"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonMovi),
            UNROLL,
            "no ones vector materialized when the UDOT path does not fire"
        );
    }

    #[test]
    fn vectorizes_dot_product() {
        let mut func = build_array_loop(true, ELEM_BYTES);
        let mut pass = NeonArrayPass::new();
        assert!(pass.run(&mut func), "should fire on `acc += a[i]*b[i]`");
        assert_eq!(pass.fired(), 1);
        // 4 accumulators × 2 arrays = 4 LDP Q-pair loads; 4 MUL.4S (one per accumulator).
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL,
            "4 LDP q,q"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonMulV), UNROLL, "dot: 4 muls");
    }

    #[test]
    fn vectorizes_i64_array_sum() {
        // 64-bit `for i in 0..n: acc += a[i]` now vectorizes on the `.2D` path.
        let mut func = build_i64_array_loop(false, AArch64Opcode::AddRR);
        let mut pass = NeonArrayPass::new();
        assert!(pass.run(&mut func), "i64 `acc += a[i]` should fire (.2D)");
        assert_eq!(pass.fired(), 1);
        // 4 accumulators × 1 array = 2 LDP Q-pair loads; 4 accumulate + 3 combine
        // adds; 2-lane horizontal reduce (UMOV D[0], UMOV D[1]); no vector multiply.
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL / 2,
            "2 LDP q,q"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonAddV),
            UNROLL + (UNROLL - 1),
            "4 accumulate + 3 combine"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmovGen),
            2,
            "reduce 2 lanes"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonMovi), UNROLL, "zeroed accs");
        assert_eq!(count(&func, AArch64Opcode::NeonMulV), 0, "i64 sum: no mul");
        // The `.2D` arrangement code (6) is used on every vector arithmetic op
        // (the LDP Q-pair load is arrangement-free: it carries the byte offset).
        let has_d2 = func.blocks.iter().flat_map(|b| b.insts.iter()).any(|&id| {
            let inst = func.inst(id);
            matches!(inst.opcode, AArch64Opcode::NeonAddV)
                && inst
                    .operands
                    .iter()
                    .any(|o| matches!(o, MachOperand::Imm(v) if *v == ARR_D2))
        });
        assert!(has_d2, "emits `.2D` arrangement code");
    }

    #[test]
    fn vectorizes_i64_array_xor() {
        // 64-bit `for i in 0..n: acc ^= a[i]` vectorizes on the `.2D` path with
        // NEON EOR accumulators + EOR horizontal fold (identity 0, same zeroed
        // init as the sum). Proves the ReduceOp::Xor path fires (not dead code).
        let mut func = build_i64_array_loop(false, AArch64Opcode::EorRR);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "i64 `acc ^= a[i]` should fire (.2D EOR)"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonEorV),
            UNROLL + (UNROLL - 1),
            "4 EOR accumulate + 3 EOR combine"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonAddV),
            0,
            "xor reduction: no vector ADD in the reduction"
        );
        assert_eq!(
            count(&func, AArch64Opcode::EorRR),
            3,
            "3 scalar EOR: 1 in the retained scalar-tail loop (`acc ^= a[i]`) + \
             horizontal 2-lane fold + seed into scalar acc"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonMovi), UNROLL, "zeroed accs");
    }

    #[test]
    fn bails_on_i64_dot_product() {
        // NON-WIDENING 64-bit `acc += a_i64[i]*b_i64[i]` (i64 loads, NO ext) MUST
        // BAIL: `.2D` has no native integer multiply, and there is no i64->i128
        // widening MAC. Only the i32->i64 WIDENING dot (loads are i32 + Sxtw/Uxtw)
        // is vectorizable via SMLAL/UMLAL — see the widening-dot tests below.
        let mut func = build_i64_array_loop(true, AArch64Opcode::AddRR);
        let mut pass = NeonArrayPass::new();
        assert!(
            !pass.run(&mut func),
            "non-widening i64 dot product must BAIL (no .2D mul)"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonLd1Post),
            0,
            "no NEON emitted"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            0,
            "no NEON emitted"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonSmlalV), 0, "no SMLAL");
        assert_eq!(count(&func, AArch64Opcode::NeonUmlalV), 0, "no UMLAL");
    }

    #[test]
    fn vectorizes_signed_widening_dot() {
        // i64 `acc += (a_i32[i] as i64) * (b_i32[i] as i64)` (Sxtw factors) now
        // vectorizes on the `.2D` path via the widening MAC SMLAL.2D + SMLAL2.2D.
        let mut func = build_widening_dot_loop(AArch64Opcode::Sxtw, AArch64Opcode::Sxtw);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "signed widening dot should fire (SMLAL/SMLAL2)"
        );
        assert_eq!(pass.fired(), 1);
        // 8 accumulators, 2 streams => 4 LDP Q-pair loads per stream = 8 total.
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL_DOT,
            "2 streams × 4 LDP"
        );
        // Per accumulator: SMLAL.2D (low .4S half) + SMLAL2.2D (high half).
        assert_eq!(
            count(&func, AArch64Opcode::NeonSmlalV),
            UNROLL_DOT,
            "8 SMLAL.2D (low)"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonSmlal2V),
            UNROLL_DOT,
            "8 SMLAL2.2D (high)"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmlalV),
            0,
            "signed: no UMLAL"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmlal2V),
            0,
            "signed: no UMLAL2"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonMovi),
            UNROLL_DOT,
            "zeroed .2D accs"
        );
        // 2-lane `.2D` horizontal reduce (UMOV D[0], D[1]).
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmovGen),
            2,
            "reduce 2 lanes"
        );
        // The SMLAL carries the `.4S` input arrangement marker (5).
        let has_s4 = func.blocks.iter().flat_map(|b| b.insts.iter()).any(|&id| {
            let inst = func.inst(id);
            matches!(inst.opcode, AArch64Opcode::NeonSmlalV)
                && inst
                    .operands
                    .iter()
                    .any(|o| matches!(o, MachOperand::Imm(v) if *v == ARR_S4))
        });
        assert!(has_s4, "SMLAL carries the .4S input marker");
    }

    #[test]
    fn vectorizes_unsigned_widening_dot() {
        // Unsigned `acc(u64) += (a_u32[i] as u64) * (b_u32[i] as u64)` (Uxtw
        // factors) vectorizes via UMLAL.2D + UMLAL2.2D.
        let mut func = build_widening_dot_loop(AArch64Opcode::Uxtw, AArch64Opcode::Uxtw);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "unsigned widening dot should fire (UMLAL/UMLAL2)"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmlalV),
            UNROLL_DOT,
            "8 UMLAL.2D (low)"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmlal2V),
            UNROLL_DOT,
            "8 UMLAL2.2D (high)"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonSmlalV),
            0,
            "unsigned: no SMLAL"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonSmlal2V),
            0,
            "unsigned: no SMLAL2"
        );
    }

    #[test]
    fn bails_on_mixed_sign_widening_dot() {
        // One factor sign-extended, the other zero-extended — there is NO single
        // widening MAC for a mixed-sign product; the recognizer MUST BAIL.
        let mut func = build_widening_dot_loop(AArch64Opcode::Sxtw, AArch64Opcode::Uxtw);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "mixed-sign widening dot must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonSmlalV), 0, "no SMLAL");
        assert_eq!(count(&func, AArch64Opcode::NeonUmlalV), 0, "no UMLAL");
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            0,
            "no NEON emitted"
        );
    }

    /// i64 WIDENING DOT `for i in 0..n: acc(i64) += ext(a_i32[i]) * ext(b_i32[i])`.
    /// The loads are i32 (`Gpr32`) at `base + iv*4`; each is widened to i64 via
    /// `ext_a`/`ext_b` (`Sxtw` signed / `Uxtw` unsigned), then multiplied into the
    /// i64 accumulator. iv/acc/n are `Gpr64` (=> `is_i64`), element size 4.
    /// Register map: v64(0)=base_a, v64(1)=n, v64(2)=base_b. v64(3)=0, v64(4)=1,
    /// v64(40)=4(es). iv=v64(5), acc=v64(6); i32 loads v(12)/v(15); widened
    /// v64(18)/v64(19); acc_new v64(16); iv+1 v64(17).
    fn build_widening_dot_loop(ext_a: AArch64Opcode, ext_b: AArch64Opcode) -> MachFunction {
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
        push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // n
        push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // base_b
        push(&mut func, bb0, Movz, vec![v64(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v64(4), i(1)]);
        push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // i32 element size
        push(&mut func, bb0, MovR, vec![v64(5), v64(3)]); // iv = 0
        push(&mut func, bb0, MovR, vec![v64(6), v64(3)]); // acc = 0
        push(&mut func, bb0, B, vec![b(guard)]);
        push(&mut func, guard, CmpRR, vec![v64(5), v64(1)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        // Header: i32 loads at base+iv*4, widen, multiply-accumulate into i64.
        push(
            &mut func,
            header,
            Madd,
            vec![v64(11), v64(5), v64(40), v64(0)],
        ); // a + iv*4
        push(&mut func, header, LdrRI, vec![v(12), v64(11), i(0)]); // load a[i] i32
        push(&mut func, header, ext_a, vec![v64(18), v(12)]); // widen a[i]
        push(
            &mut func,
            header,
            Madd,
            vec![v64(14), v64(5), v64(40), v64(2)],
        ); // b + iv*4
        push(&mut func, header, LdrRI, vec![v(15), v64(14), i(0)]); // load b[i] i32
        push(&mut func, header, ext_b, vec![v64(19), v(15)]); // widen b[i]
        push(
            &mut func,
            header,
            Madd,
            vec![v64(16), v64(18), v64(19), v64(6)],
        ); // acc + xa*xb
        push(&mut func, header, AddRR, vec![v64(17), v64(5), v64(4)]); // iv+1
        push(&mut func, header, B, vec![b(latch)]);
        push(&mut func, latch, AddRI, vec![v64(5), v64(17), i(0)]);
        push(&mut func, latch, AddRI, vec![v64(6), v64(16), i(0)]);
        push(&mut func, latch, CmpRR, vec![v64(5), v64(1)]);
        push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, guard);
        func.add_edge(guard, header);
        func.add_edge(guard, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
        func.next_vreg = 128;
        func
    }

    /// i64 `for i in 0..n: acc += a[i]` (`dot=false`) or `acc += a[i]*b[i]`
    /// (`dot=true`, which must BAIL). Address shape is `base + iv*8` — the index
    /// is `iv` directly (already 64-bit, no `Sxtw`), element size 8.
    /// Register map: v0=base_a, v1=n, v2=base_b (i64). v3=0, v4=1, v40=8(es).
    /// iv=v5, acc=v6.
    fn build_i64_array_loop(dot: bool, red_op: AArch64Opcode) -> MachFunction {
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
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]);
        push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // n (i64)
        push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // base_b
        push(&mut func, bb0, Movz, vec![v64(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v64(4), i(1)]);
        push(&mut func, bb0, Movz, vec![v64(40), i(8)]);
        push(&mut func, bb0, MovR, vec![v64(5), v64(3)]);
        push(&mut func, bb0, MovR, vec![v64(6), v64(3)]);
        push(&mut func, bb0, B, vec![b(guard)]);
        push(&mut func, guard, CmpRR, vec![v64(5), v64(1)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        push(
            &mut func,
            header,
            Madd,
            vec![v64(11), v64(5), v64(40), v64(0)],
        ); // a + iv*8
        push(&mut func, header, LdrRI, vec![v64(12), v64(11), i(0)]); // load a[i]
        if dot {
            push(
                &mut func,
                header,
                Madd,
                vec![v64(14), v64(5), v64(40), v64(2)],
            ); // b + iv*8
            push(&mut func, header, LdrRI, vec![v64(15), v64(14), i(0)]); // load b[i]
            push(
                &mut func,
                header,
                Madd,
                vec![v64(16), v64(12), v64(15), v64(6)],
            ); // acc + a*b
            push(&mut func, header, AddRR, vec![v64(17), v64(5), v64(4)]);
            push(&mut func, header, B, vec![b(latch)]);
        } else {
            push(&mut func, header, red_op, vec![v64(16), v64(6), v64(12)]); // acc OP a[i]
            push(&mut func, header, AddRR, vec![v64(17), v64(5), v64(4)]);
            push(&mut func, header, B, vec![b(latch)]);
        }
        push(&mut func, latch, AddRI, vec![v64(5), v64(17), i(0)]);
        push(&mut func, latch, AddRI, vec![v64(6), v64(16), i(0)]);
        push(&mut func, latch, CmpRR, vec![v64(5), v64(1)]);
        push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, guard);
        func.add_edge(guard, header);
        func.add_edge(guard, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
        func.next_vreg = 128;
        func
    }

    /// The ROTATED (clang -O1) loop shape: the exit test lives at the END of the
    /// HEADER (`CmpRR(iv+1, bound); BCond(EQ) -> exit`) and the LATCH is PURE
    /// writebacks + `B -> header`. Same counted reduction, bottom-tested-in-header.
    fn build_i64_rotated_loop(red_op: AArch64Opcode) -> MachFunction {
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
        push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // n / bound
        push(&mut func, bb0, Movz, vec![v64(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v64(4), i(1)]);
        push(&mut func, bb0, Movz, vec![v64(40), i(8)]);
        push(&mut func, bb0, MovR, vec![v64(5), v64(3)]); // iv = 0
        push(&mut func, bb0, MovR, vec![v64(6), v64(3)]); // acc = 0
        push(&mut func, bb0, B, vec![b(guard)]);
        push(&mut func, guard, B, vec![b(header)]);
        // Header: address, load, reduction, increment, ROTATED exit test.
        push(
            &mut func,
            header,
            Madd,
            vec![v64(11), v64(5), v64(40), v64(0)],
        ); // base + iv*8
        push(&mut func, header, LdrRI, vec![v64(12), v64(11), i(0)]); // load a[i]
        push(&mut func, header, red_op, vec![v64(16), v64(6), v64(12)]); // acc OP a[i]
        push(&mut func, header, AddRR, vec![v64(17), v64(5), v64(4)]); // iv + 1
        push(&mut func, header, CmpRR, vec![v64(17), v64(1)]); // iv+1 vs bound
        push(&mut func, header, BCond, vec![i(CC_EQ), b(exit)]); // leave when iv+1 == bound
        push(&mut func, header, B, vec![b(latch)]); // else continue
        // Latch: PURE writebacks + unconditional B -> header.
        push(&mut func, latch, MovR, vec![v64(5), v64(17)]); // iv <- iv+1
        push(&mut func, latch, MovR, vec![v64(6), v64(16)]); // acc <- acc_next
        push(&mut func, latch, B, vec![b(header)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, guard);
        func.add_edge(guard, header);
        func.add_edge(header, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.next_vreg = 128;
        func
    }

    #[test]
    fn vectorizes_i64_rotated_reduction() {
        // The importer's rotated loop shape (test-in-header, pure-writeback latch)
        // must be recognized and vectorized just like the native shape.
        for op in [AArch64Opcode::AddRR, AArch64Opcode::EorRR] {
            let mut func = build_i64_rotated_loop(op);
            let mut pass = NeonArrayPass::new();
            assert!(
                pass.run(&mut func),
                "rotated i64 reduction ({op:?}) should fire"
            );
            assert_eq!(pass.fired(), 1);
            let vop = if op == AArch64Opcode::AddRR {
                AArch64Opcode::NeonAddV
            } else {
                AArch64Opcode::NeonEorV
            };
            assert_eq!(
                count(&func, vop),
                UNROLL + (UNROLL - 1),
                "4 accumulate + 3 combine on the .2D path"
            );
        }
    }

    #[test]
    fn bails_on_register_reduction_no_loads() {
        // `acc += iv` (no loads) must BAIL — left to neon_reduce.
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
        push(&mut func, bb0, Copy, vec![v(1), v(1)]);
        push(&mut func, bb0, Movz, vec![v(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v(4), i(1)]);
        push(&mut func, bb0, MovR, vec![v(5), v(3)]);
        push(&mut func, bb0, MovR, vec![v(6), v(3)]);
        push(&mut func, bb0, B, vec![b(guard)]);
        push(&mut func, guard, CmpRR, vec![v(5), v(1)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        push(&mut func, header, AddRR, vec![v(16), v(6), v(5)]); // acc += iv
        push(&mut func, header, AddRR, vec![v(17), v(5), v(4)]);
        push(&mut func, header, B, vec![b(latch)]);
        push(&mut func, latch, AddRI, vec![v(5), v(17), i(0)]);
        push(&mut func, latch, AddRI, vec![v(6), v(16), i(0)]);
        push(&mut func, latch, CmpRR, vec![v(5), v(1)]);
        push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, guard);
        func.add_edge(guard, header);
        func.add_edge(guard, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
        func.next_vreg = 128;
        let mut pass = NeonArrayPass::new();
        assert!(
            !pass.run(&mut func),
            "register reduction must BAIL (no loads)"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonLd1Post), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
    }

    // -----------------------------------------------------------------------
    // WIDENING byte/half reductions (TRACK B)
    // -----------------------------------------------------------------------

    /// Build `s(i32) += ext(a[i8/i16][i])` (or `+= ctpop(zext8(a[i]))` when
    /// `pop`) in the exact rotated shape loop-latch-layout emits, with the real
    /// isel address forms: i8 = `LdrbRI(AddRR(base, Sxtw(iv)))`, i16 =
    /// `LdrhRI(Madd(Sxtw(iv), 2, base))`.
    fn build_widen_loop(ext: AArch64Opcode, pop: bool) -> MachFunction {
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
        let is_byte = matches!(ext, Uxtb | Sxtb);
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base
        push(&mut func, bb0, Copy, vec![v(1), v(1)]); // n
        push(&mut func, bb0, Movz, vec![v(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v(4), i(1)]);
        push(&mut func, bb0, Movz, vec![v64(40), i(2)]); // i16 element size
        push(&mut func, bb0, MovR, vec![v(5), v(3)]); // iv = 0
        push(&mut func, bb0, MovR, vec![v(6), v(3)]); // acc = 0
        push(&mut func, bb0, B, vec![b(guard)]);
        push(&mut func, guard, CmpRR, vec![v(5), v(1)]);
        push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, guard, B, vec![b(exit)]);
        // Header: narrow address + load + extend (+ SWAR ctpop when pop).
        push(&mut func, header, Sxtw, vec![v64(10), v(5)]);
        if is_byte {
            push(&mut func, header, AddRR, vec![v64(11), v64(0), v64(10)]);
            push(&mut func, header, LdrbRI, vec![v(12), v64(11), i(0)]);
        } else {
            push(
                &mut func,
                header,
                Madd,
                vec![v64(11), v64(10), v64(40), v64(0)],
            );
            push(&mut func, header, LdrhRI, vec![v(12), v64(11), i(0)]);
        }
        push(&mut func, header, ext, vec![v(13), v(12)]);
        let term = if pop {
            // The exact isel SWAR ctpop tree over v(13) (emit_ctpop_swar).
            push(&mut func, header, LsrRI, vec![v(14), v(13), i(1)]);
            push(&mut func, header, AndRI, vec![v(15), v(14), i(0x5555_5555)]);
            push(&mut func, header, SubRR, vec![v(16), v(13), v(15)]);
            push(&mut func, header, AndRI, vec![v(17), v(16), i(0x3333_3333)]);
            push(&mut func, header, LsrRI, vec![v(18), v(16), i(2)]);
            push(&mut func, header, AndRI, vec![v(19), v(18), i(0x3333_3333)]);
            push(&mut func, header, AddRR, vec![v(20), v(17), v(19)]);
            push(&mut func, header, LsrRI, vec![v(21), v(20), i(4)]);
            push(&mut func, header, AddRR, vec![v(22), v(20), v(21)]);
            push(&mut func, header, AndRI, vec![v(23), v(22), i(0x0f0f_0f0f)]);
            push(&mut func, header, LsrRI, vec![v(24), v(23), i(8)]);
            push(&mut func, header, AddRR, vec![v(25), v(23), v(24)]);
            push(&mut func, header, LsrRI, vec![v(26), v(25), i(16)]);
            push(&mut func, header, AddRR, vec![v(27), v(25), v(26)]);
            push(&mut func, header, AndRI, vec![v(28), v(27), i(0x3f)]);
            28
        } else {
            13
        };
        push(&mut func, header, AddRR, vec![v(30), v(6), v(term)]); // acc += term
        push(&mut func, header, AddRR, vec![v(31), v(5), v(4)]); // iv+1
        push(&mut func, header, B, vec![b(latch)]);
        push(&mut func, latch, AddRI, vec![v(5), v(31), i(0)]);
        push(&mut func, latch, AddRI, vec![v(6), v(30), i(0)]);
        push(&mut func, latch, CmpRR, vec![v(5), v(1)]);
        push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, guard);
        func.add_edge(guard, header);
        func.add_edge(guard, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
        func.next_vreg = 128;
        func
    }

    #[test]
    fn widen_sum_u8_fires_with_uaddlp_chain() {
        let mut func = build_widen_loop(AArch64Opcode::Uxtb, false);
        let mut pass = NeonArrayPass::new();
        assert!(pass.run(&mut func), "zext-i8 sum must vectorize (widening)");
        assert_eq!(pass.fired(), 1);
        // 4 Q registers per iteration = 2 LDP pair loads; per Q: 2 UADDLPs.
        assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 2);
        assert_eq!(count(&func, AArch64Opcode::NeonUaddlpV), 8, "2 per Q x 4");
        assert_eq!(
            count(&func, AArch64Opcode::NeonSaddlpV),
            0,
            "zext must NOT saddlp"
        );
    }

    #[test]
    fn widen_sum_i8_fires_with_saddlp_chain() {
        let mut func = build_widen_loop(AArch64Opcode::Sxtb, false);
        let mut pass = NeonArrayPass::new();
        assert!(pass.run(&mut func), "sext-i8 sum must vectorize (widening)");
        assert_eq!(count(&func, AArch64Opcode::NeonSaddlpV), 8, "2 per Q x 4");
        assert_eq!(
            count(&func, AArch64Opcode::NeonUaddlpV),
            0,
            "sext must NOT uaddlp"
        );
    }

    #[test]
    fn widen_sum_u16_fires_single_uaddlp() {
        let mut func = build_widen_loop(AArch64Opcode::Uxth, false);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "zext-i16 sum must vectorize (widening)"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonUaddlpV), 4, "1 per Q x 4");
    }

    #[test]
    fn widen_sum_i16_fires_single_saddlp() {
        let mut func = build_widen_loop(AArch64Opcode::Sxth, false);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "sext-i16 sum must vectorize (widening)"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonSaddlpV), 4, "1 per Q x 4");
    }

    #[test]
    fn widen_pop_u8_fires_with_cnt_udot() {
        let mut func = build_widen_loop(AArch64Opcode::Uxtb, true);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "byte popcount must vectorize (widening)"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonCntV), 4, "1 CNT.16B per Q");
        assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 4, "1 UDOT per Q");
    }

    #[test]
    fn widen_pop_of_sext_byte_bails_sign_trap() {
        // `ctpop(sext8(a[i]))` is NOT byte-local — the sign extension can add up
        // to 24 set bits — so CNT.16B would MISCOMPILE. Must BAIL (fail-closed).
        let mut func = build_widen_loop(AArch64Opcode::Sxtb, true);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "sext-byte popcount must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonCntV), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
    }

    #[test]
    fn widen_ext_plus_arith_bails() {
        // `s += zext8(a[i]) * 3` — the term is NOT exactly the extended load,
        // and the generic walk cannot lower Uxtb ⇒ the whole loop must BAIL.
        let mut func = build_widen_loop(AArch64Opcode::Uxtb, false);
        // Rewrite the accumulate `acc += v13` into `acc += v13*3`: find the
        // AddRR(v30, v6, v13) instruction and retarget it to a MulRR result.
        let three = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![v(50), i(3)]));
        let mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![v(51), v(13), v(50)],
        ));
        let mut header = None;
        for (bi, blk) in func.blocks.iter().enumerate() {
            for &id in &blk.insts {
                let inst = func.inst(id);
                if inst.opcode == AArch64Opcode::AddRR && inst.operands.first() == Some(&v(30)) {
                    header = Some((BlockId(bi as u32), id));
                }
            }
        }
        let (hblk, add_id) = header.expect("accumulate inst");
        // Insert Movz+Mul before the accumulate and swap its term operand.
        let pos = func
            .block(hblk)
            .insts
            .iter()
            .position(|&id| id == add_id)
            .unwrap();
        func.block_mut(hblk).insts.insert(pos, three);
        func.block_mut(hblk).insts.insert(pos + 1, mul);
        func.inst_mut(add_id).operands[2] = v(51);
        let mut pass = NeonArrayPass::new();
        assert!(
            !pass.run(&mut func),
            "ext-load with extra arithmetic must BAIL"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonUaddlpV), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
    }

    // -----------------------------------------------------------------------
    // INLINED rotated shape: multi-pred guard + in-loop constant bound +
    // multi-def step vreg (the BenchmarkGame/puzzle `findDuplicate` inlined
    // into `main` by clang -O1)
    // -----------------------------------------------------------------------

    /// Build the puzzle-mirror INLINED reduction: an ENCLOSING outer loop whose
    /// header (2 preds: entry + outer back-edge) re-seeds iv/acc and branches
    /// UNCONDITIONALLY into the rotated inner header
    /// `acc(i32) ^= a[i] ^ (int)(i+1)` with iv widened to i64, the bound
    /// `500001` materialized INSIDE the loop (`Movz #41249; Movk #7, lsl 16`),
    /// and the step `+1` held in a REUSED (multi-def) vreg — its OTHER def
    /// lives in `second_step_def_block` (0 = the function's exit block, which
    /// never reaches the loop; 1 = the OUTER LATCH, which DOES reach the header
    /// around the outer back edge and must poison recognition).
    ///
    /// Register map: v0=base(ptr), x3=0, x4=step(+1, MULTI-DEF), w31=0,
    /// iv=x5, acc=w6, iv_next=x17, acc_next=w16, bound=x9, outer j=x30.
    fn build_inlined_puzzle_loop(
        bound_lo: i64,
        bound_hi: i64,
        second_step_def_in_outer_latch: bool,
    ) -> MachFunction {
        let mut func = MachFunction::new("main".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let jheader = func.create_block(); // the multi-pred guard
        let header = func.create_block();
        let latch = func.create_block();
        let jlatch = func.create_block(); // inner exit = outer latch
        let exit = func.create_block();
        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        // Entry: base pointer, constants, outer counter.
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a
        push(&mut func, bb0, Movz, vec![v64(3), i(0)]);
        push(&mut func, bb0, Movz, vec![v64(4), i(1)]); // step (+1) — def #1
        push(&mut func, bb0, Movz, vec![v(31), i(0)]);
        push(&mut func, bb0, Movz, vec![v64(40), i(ELEM_BYTES)]); // es = 4
        push(&mut func, bb0, Movz, vec![v64(30), i(0)]); // j = 0
        push(&mut func, bb0, B, vec![b(jheader)]);
        // Outer header = the GUARD: re-seed iv/acc, fall into the reduction.
        push(&mut func, jheader, MovR, vec![v64(5), v64(3)]); // iv = 0
        push(&mut func, jheader, MovR, vec![v(6), v(31)]); // acc = 0
        push(&mut func, jheader, B, vec![b(header)]);
        // Inner header (rotated): load, xor-iota term, step, IN-LOOP bound,
        // exit test.
        push(
            &mut func,
            header,
            Madd,
            vec![v64(11), v64(5), v64(40), v64(0)],
        ); // base + iv*4
        push(&mut func, header, LdrRI, vec![v(12), v64(11), i(0)]); // a[i]
        push(&mut func, header, EorRR, vec![v(13), v(6), v(12)]); // acc ^ a[i]
        push(&mut func, header, AddRR, vec![v64(17), v64(5), v64(4)]); // iv+1 (multi-def step!)
        push(&mut func, header, MovR, vec![v(14), v64(17)]); // (int)(i+1)
        push(&mut func, header, EorRR, vec![v(16), v(13), v(14)]); // ^ (i+1)
        push(&mut func, header, Movz, vec![v64(9), i(bound_lo)]); // bound lo
        push(&mut func, header, Movk, vec![v64(9), i(bound_hi), i(16)]); // bound hi
        push(&mut func, header, CmpRR, vec![v64(17), v64(9)]); // iv+1 vs bound
        push(&mut func, header, BCond, vec![i(CC_EQ), b(jlatch)]); // leave when ==
        push(&mut func, header, B, vec![b(latch)]);
        // Inner latch: pure writebacks.
        push(&mut func, latch, MovR, vec![v64(5), v64(17)]);
        push(&mut func, latch, MovR, vec![v(6), v(16)]);
        push(&mut func, latch, B, vec![b(header)]);
        // Outer latch: j++, loop 1000x.
        if second_step_def_in_outer_latch {
            // step def #2 with a DIFFERENT value — REACHES the header around
            // the outer back edge, so folding either def would be unsound.
            push(&mut func, jlatch, Movz, vec![v64(4), i(2)]);
        }
        push(&mut func, jlatch, AddRI, vec![v64(30), v64(30), i(1)]);
        push(&mut func, jlatch, CmpRI, vec![v64(30), i(1000)]);
        push(&mut func, jlatch, BCond, vec![i(CC_LT), b(jheader)]);
        push(&mut func, jlatch, B, vec![b(exit)]);
        // Exit: uses acc; holds the step vreg's OTHER def (never reaches the
        // loop) in the default configuration.
        if !second_step_def_in_outer_latch {
            push(&mut func, exit, Movz, vec![v64(4), i(7)]); // step def #2 — dead to the loop
        }
        push(&mut func, exit, MovR, vec![v(20), v(6)]);
        push(&mut func, exit, Ret, vec![]);

        func.add_edge(bb0, jheader);
        func.add_edge(jlatch, jheader); // outer back edge: guard has 2 preds
        func.add_edge(jheader, header);
        func.add_edge(header, latch);
        func.add_edge(header, jlatch);
        func.add_edge(latch, header);
        func.add_edge(jlatch, exit);
        func.next_vreg = 128;
        func
    }

    #[test]
    fn vectorizes_inlined_rotated_const_bound_multidef_step() {
        // The full puzzle-mirror: multi-pred guard + in-loop Movz+Movk bound
        // (500001 = 41249 | 7<<16) + multi-def step vreg. Must fire on the
        // mixed .4S path with the iota machinery.
        let mut func = build_inlined_puzzle_loop(41249, 7, false);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "inlined rotated xor-iota reduction with in-loop constant bound should fire"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            UNROLL / 2,
            "2 LDP q,q"
        );
        assert!(
            count(&func, AArch64Opcode::NeonEorV) >= UNROLL,
            "xor accumulate"
        );
        assert!(
            count(&func, AArch64Opcode::NeonDupGen) >= 1,
            "iota machinery ((i+1) term)"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmovGen),
            4,
            "reduce 4 lanes"
        );
    }

    #[test]
    fn bails_when_second_step_def_reaches_header() {
        // The step vreg's second def sits in the OUTER LATCH: it reaches the
        // inner header around the outer back edge, so the reaching-def fold
        // sees TWO defs and recognition must BAIL (no NEON).
        let mut func = build_inlined_puzzle_loop(41249, 7, true);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "two reaching step defs must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonEorV), 0);
    }

    #[test]
    fn bails_on_zero_const_bound() {
        // Reconstructed bound 0 is outside the accepted [1, i32::MAX] window
        // (the rotated do-while's >=1-trip contract) and must BAIL.
        let mut func = build_inlined_puzzle_loop(0, 0, false);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "constant bound 0 must BAIL");
        assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
    }

    #[test]
    fn bails_native_shape_with_multi_pred_guard() {
        // The gpreds relaxation is ROTATED-only: a NATIVE (latch-tested) loop
        // whose guard has two preds must still BAIL (the native splice
        // requires the single-pred preheader).
        let mut func = build_array_loop(false, ELEM_BYTES);
        // Wire a second pred into the guard: exit -> guard (arbitrary edge
        // that makes gpreds.len() == 2 without touching the loop body).
        let guard = BlockId(1);
        let exit = BlockId(4);
        func.add_edge(exit, guard);
        let mut pass = NeonArrayPass::new();
        assert!(
            !pass.run(&mut func),
            "native shape with multi-pred guard must BAIL"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
    }

    // ---------------------------------------------------------------------
    // FORWARD bounds-guarded `while i<N` CHAIN i32-dot (recognize_forward_chain,
    // the shape the bridge emits for `for i in 0..2048 { s += a[i]*b[i] }` over
    // fixed-size `[i32; 2048]` arrays). d09.
    // ---------------------------------------------------------------------

    /// Build the multi-block chain dot loop, FAITHFUL to d09's post-bounds-
    /// check-elim MIR (blocks {8=header, 9, 13, 14=latch}): header is a
    /// `CmpRI(iv_copy, 2048)` loop-continue DIAMOND (constant bound); block `g_pre`
    /// is a PASS-THROUGH that re-copies the iv (`v76 = MovR(iv)`); block `g_a`
    /// addresses `a[i]` with that iv-COPY used DIRECTLY (`base + iv_copy*4`, no
    /// Sxtw — MIXED i64-index / i32-elem) and loads `a[i]`; the latch addresses
    /// `b[i]` with the iv directly, does the fused-Madd `s += a[i]*b[i]`, steps
    /// `iv+1`, writes back (iv, acc) + back-edge. `ga`: 0 => `g_a` is a
    /// pass-through (d09); 1 => `g_a` is a bounds-guard DIAMOND on the SAME const
    /// 2048 (fires); 2 => DIFFERENT const 1024 (BAILS, single-N); 3 => NON-iv
    /// index (BAILS, same_as_iv). Regs: v0=base_a, v1=base_b, v40=es(4),
    /// v59=iv(Gpr64), v60=acc(Gpr32).
    fn build_chain_dot_loop(ga: u8) -> MachFunction {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let header = func.create_block();
        let g_pre = func.create_block();
        let g_a = func.create_block();
        let latch = func.create_block();
        let abort = func.create_block();
        let exit = func.create_block();
        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        // Preheader.
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a
        push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // base_b
        push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // element size
        push(&mut func, bb0, Movz, vec![v64(59), i(0)]); // iv = 0 (Gpr64, MIXED)
        push(&mut func, bb0, Movz, vec![v(60), i(0)]); // acc = 0 (Gpr32)
        push(&mut func, bb0, B, vec![b(header)]);
        // Header: loop-continue guard `iv <u 2048` (CmpRI constant bound).
        push(&mut func, header, MovR, vec![v64(63), v64(59)]); // iv copy for the guard
        push(&mut func, header, CmpRI, vec![v64(63), i(2048)]);
        push(&mut func, header, BCond, vec![i(CC_LO), b(g_pre)]);
        push(&mut func, header, B, vec![b(exit)]);
        // g_pre: PASS-THROUGH that re-copies the iv for the a[i] address (d09 blk 9).
        push(&mut func, g_pre, MovR, vec![v64(76), v64(59)]); // iv copy for a[i] addr
        push(&mut func, g_pre, B, vec![b(g_a)]);
        func.add_edge(g_pre, g_a);
        // g_a: address a[i] via the iv-COPY used DIRECTLY (no Sxtw), load a[i].
        push(
            &mut func,
            g_a,
            Madd,
            vec![v64(66), v64(76), v64(40), v64(0)],
        ); // a[i] addr
        push(&mut func, g_a, LdrRI, vec![v(67), v64(66), i(0)]); // a[i]
        if ga == 0 {
            push(&mut func, g_a, B, vec![b(latch)]); // PASS-THROUGH
            func.add_edge(g_a, latch);
        } else {
            push(&mut func, g_a, MovR, vec![v64(77), v64(59)]); // iv copy for the guard
            let idx = if ga == 3 { v64(0) } else { v64(77) }; // ga==3: non-iv index
            let lim = if ga == 2 { i(1024) } else { i(2048) }; // ga==2: mismatched N
            push(&mut func, g_a, CmpRI, vec![idx, lim]);
            push(&mut func, g_a, BCond, vec![i(CC_LO), b(latch)]);
            push(&mut func, g_a, B, vec![b(abort)]);
            func.add_edge(g_a, latch);
            func.add_edge(g_a, abort);
        }
        // Latch: address b[i] with the iv directly, load, fused-Madd reduction,
        // step, writebacks (d09 blk 14).
        push(
            &mut func,
            latch,
            Madd,
            vec![v64(69), v64(59), v64(40), v64(1)],
        ); // b[i] addr
        push(&mut func, latch, LdrRI, vec![v(70), v64(69), i(0)]); // b[i]
        push(&mut func, latch, Madd, vec![v(71), v(67), v(70), v(60)]); // acc + a[i]*b[i]
        push(&mut func, latch, AddRI, vec![v64(72), v64(59), i(1)]); // iv + 1
        push(&mut func, latch, MovR, vec![v(60), v(71)]); // acc writeback
        push(&mut func, latch, MovR, vec![v64(59), v64(72)]); // iv writeback
        push(&mut func, latch, B, vec![b(header)]);
        push(&mut func, abort, Ret, vec![]);
        push(&mut func, exit, MovR, vec![v(80), v(60)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, header);
        func.add_edge(header, g_pre);
        func.add_edge(header, exit);
        func.add_edge(latch, header);
        func.next_vreg = 512;
        func
    }

    #[test]
    fn vectorizes_chain_dot() {
        // d09: `for i in 0..2048 { s += a[i]*b[i] }` over fixed-size arrays, with
        // the interior a[i] bounds check ELIDED (g_a is a pass-through). The
        // constant-bound forward chain must be recognized and vectorized as a dot.
        let mut func = build_chain_dot_loop(0);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "constant-bound chain dot should vectorize"
        );
        assert_eq!(pass.fired(), 1);
        // 2 input streams (a,b) x 4 accumulators -> per-lane a*b muls + accumulate
        // adds + 4-lane horizontal drain; const bound 2048 materialized (Movz).
        assert_eq!(
            count(&func, AArch64Opcode::NeonMulV),
            UNROLL,
            "per-lane a[i]*b[i]"
        );
        assert!(
            count(&func, AArch64Opcode::NeonAddV) >= UNROLL,
            "accumulate"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmovGen),
            4,
            "reduce 4 lanes"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonMovi), UNROLL, "zeroed accs");
        // Scalar chain kept intact (the fused Madd reduction is still present).
        assert!(count(&func, AArch64Opcode::Madd) >= 1, "scalar chain kept");
    }

    #[test]
    fn vectorizes_chain_dot_with_interior_diamond() {
        // Same as above but the a[i] bounds check SURVIVED as a diamond checking
        // the SAME const 2048 (single-N holds): still fires.
        let mut func = build_chain_dot_loop(1);
        let mut pass = NeonArrayPass::new();
        assert!(
            pass.run(&mut func),
            "single-N interior diamond should still vectorize"
        );
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonMulV),
            UNROLL,
            "per-lane a[i]*b[i]"
        );
    }

    #[test]
    fn chain_bails_on_mismatched_bound() {
        // SINGLE-N agreement: an interior bounds guard against a DIFFERENT limit
        // (1024) than the loop-continue (2048) proves nothing about the vector
        // range for that array — must BAIL (fail-closed).
        let mut func = build_chain_dot_loop(2);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "mismatched interior bound must BAIL");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonMulV), 0);
    }

    #[test]
    fn chain_bails_on_non_iv_index() {
        // A guard that does not test (a copy of) the induction proves nothing
        // about the vectorized range — must BAIL.
        let mut func = build_chain_dot_loop(3);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "non-iv guard index must BAIL");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonMulV), 0);
    }

    #[test]
    fn chain_bails_on_store_in_body() {
        // A second memory effect anywhere in the chain body (here a StrRI in the
        // latch) is not whitelisted — must BAIL (rules out a hidden aliased write).
        let mut func = build_chain_dot_loop(0);
        // Inject a store into the latch (block 4: bb0,header,g_pre,g_a,latch).
        let latch = BlockId(4);
        let st = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![v(71), v64(69), i(0)],
        ));
        func.block_mut(latch).insts.insert(0, st);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "store in chain body must BAIL");
        assert_eq!(pass.fired(), 0);
    }

    // ---------------------------------------------------------------------
    // TRACK D: forward-chain i64 WIDENING ABS-SUM
    // `s(i64) += zext64(abs_bits(a_i32[i] [+ r]))` (e05_abssum). The abs is a
    // BRANCH DIAMOND mid-chain, exactly the bridge's post-bounds-check-elim MIR.
    // ---------------------------------------------------------------------

    /// Build the e05-faithful chain abs-sum loop. Blocks: bb0(preheader),
    /// header (`iv <u 2048` guard), g_pre (iv-copy pass-through), split
    /// (`Madd; LdrRI; [AddRR inv;] CmpRI #0; BCond LT neg; B pos`), neg
    /// (`SubRR 0-x; MovR phi; B`), pos (`MovR phi, x; B`), latch (`MovR t,phi;
    /// Uxtw; AddRR acc; AddRI iv+1; writebacks; B`), exit. Variants:
    /// 0 = fires (invariant addend `r`); 1 = fires (plain `abs(a[i])`, no add);
    /// 2 = `Sxtw` root (SIGN-extension — the miscompile axis) BAILS;
    /// 3 = neg arm subtracts from constant 1 (not a negation) BAILS;
    /// 4 = extra instruction in the pos arm BAILS;
    /// 5 = third in-loop writer of the phi BAILS;
    /// 6 = split condition `EQ` (not a sign test) BAILS;
    /// 7 = addend defined INSIDE the loop (not invariant) BAILS;
    /// 8 = term routed around the diamond (Uxtw of the raw load) BAILS.
    /// Regs: v0=base, v40=es(4), v50=zero, v51=r, v52=one, v59=iv(Gpr64),
    /// v60=acc(Gpr64), v67=load, v68=x, v70=phi.
    fn build_chain_abs_loop(variant: u8) -> MachFunction {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let header = func.create_block();
        let g_pre = func.create_block();
        let split = func.create_block();
        let neg = func.create_block();
        let pos = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();
        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        // Preheader.
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base
        push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // element size
        push(&mut func, bb0, Movz, vec![v(50), i(0)]); // zero (neg arm)
        if variant != 7 {
            push(&mut func, bb0, Movz, vec![v(51), i(77)]); // invariant addend r
        }
        push(&mut func, bb0, Movz, vec![v(52), i(1)]); // one (variant 3)
        push(&mut func, bb0, Movz, vec![v64(59), i(0)]); // iv = 0 (Gpr64)
        push(&mut func, bb0, Movz, vec![v64(60), i(0)]); // acc = 0 (Gpr64)
        push(&mut func, bb0, B, vec![b(header)]);
        // Header: loop-continue guard `iv <u 2048` (constant bound).
        push(&mut func, header, MovR, vec![v64(63), v64(59)]);
        push(&mut func, header, CmpRI, vec![v64(63), i(2048)]);
        push(&mut func, header, BCond, vec![i(CC_LO), b(g_pre)]);
        push(&mut func, header, B, vec![b(exit)]);
        // g_pre: pass-through iv copy (the elided bounds check's block).
        push(&mut func, g_pre, MovR, vec![v64(76), v64(59)]);
        push(&mut func, g_pre, B, vec![b(split)]);
        // Split: address + load + (add) + sign test.
        push(
            &mut func,
            split,
            Madd,
            vec![v64(66), v64(76), v64(40), v64(0)],
        );
        push(&mut func, split, LdrRI, vec![v(67), v64(66), i(0)]);
        if variant == 7 {
            push(&mut func, split, Movz, vec![v(51), i(77)]); // r defined IN loop
        }
        let x = if variant == 1 {
            67 // plain abs(a[i]): the load IS the compared value
        } else {
            push(&mut func, split, AddRR, vec![v(68), v(67), v(51)]);
            68
        };
        push(&mut func, split, CmpRI, vec![v(x), i(0)]);
        let cc = if variant == 6 { CC_EQ } else { CC_LT };
        push(&mut func, split, BCond, vec![i(cc), b(neg)]);
        push(&mut func, split, B, vec![b(pos)]);
        // Neg arm: phi = 0 - x (variant 3: 1 - x, NOT a negation).
        let zed = if variant == 3 { 52 } else { 50 };
        push(&mut func, neg, SubRR, vec![v(69), v(zed), v(x)]);
        push(&mut func, neg, MovR, vec![v(70), v(69)]);
        push(&mut func, neg, B, vec![b(latch)]);
        // Pos arm: phi = x (variant 4: an extra instruction).
        push(&mut func, pos, MovR, vec![v(70), v(x)]);
        if variant == 4 {
            push(&mut func, pos, AddRI, vec![v(90), v(x), i(1)]);
        }
        push(&mut func, pos, B, vec![b(latch)]);
        // Latch: zext + accumulate + step + writebacks.
        if variant == 5 {
            push(&mut func, latch, MovR, vec![v(70), v(67)]); // third phi writer
        }
        let widen_src = if variant == 8 { 67 } else { 70 };
        push(&mut func, latch, MovR, vec![v(71), v(widen_src)]);
        let ext = if variant == 2 { Sxtw } else { Uxtw };
        push(&mut func, latch, ext, vec![v64(72), v(71)]);
        push(&mut func, latch, AddRR, vec![v64(73), v64(60), v64(72)]);
        push(&mut func, latch, AddRI, vec![v64(74), v64(59), i(1)]);
        push(&mut func, latch, MovR, vec![v64(60), v64(73)]);
        push(&mut func, latch, MovR, vec![v64(59), v64(74)]);
        push(&mut func, latch, B, vec![b(header)]);
        // Exit.
        push(&mut func, exit, MovR, vec![v64(80), v64(60)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, header);
        func.add_edge(header, g_pre);
        func.add_edge(header, exit);
        func.add_edge(g_pre, split);
        func.add_edge(split, neg);
        func.add_edge(split, pos);
        func.add_edge(neg, latch);
        func.add_edge(pos, latch);
        func.add_edge(latch, header);
        func.next_vreg = 512;
        func
    }

    #[test]
    fn vectorizes_chain_abs_widen() {
        // e05: `s(i64) += (a[i].wrapping_add(r)).unsigned_abs() as i64` — must
        // fire TRACK D: DUP(r) + ADD.4S + ABS.4S + ONE pairwise widening
        // UADALP accumulate into `.2D` accumulators + the 2-lane drain
        // (3 SIMD ops per Q, under LLVM's uaddw/uaddw2 pair).
        let mut func = build_chain_abs_loop(0);
        let mut pass = NeonArrayPass::new();
        assert!(pass.run(&mut func), "chain abs-sum with addend should fire");
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonAbsV),
            UNROLL,
            "ABS.4S per Q"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUadalpV),
            UNROLL,
            "ONE UADALP accumulate per Q"
        );
        // NEVER the replaced UADDW/UADDW2 pair, the MAC forms, nor the signed
        // forms (SMLAL would sign-extend the >= 2^31 abs lanes; the signed
        // SADALP is not even encodable).
        assert_eq!(
            count(&func, AArch64Opcode::NeonUaddwV),
            0,
            "UADDW replaced by UADALP"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUaddw2V),
            0,
            "UADDW2 replaced by UADALP"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonUmlalV), 0, "no by-ones MAC");
        assert_eq!(
            count(&func, AArch64Opcode::NeonUmlal2V),
            0,
            "no by-ones MAC"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonSmlalV), 0, "zext not sext");
        assert_eq!(count(&func, AArch64Opcode::NeonSmlal2V), 0, "zext not sext");
        // Invariant broadcast ONLY (no ones splat — UADALP needs none);
        // invariant add (4) + .2D combine (3).
        assert_eq!(count(&func, AArch64Opcode::NeonDupGen), 1, "inv DUP only");
        assert_eq!(
            count(&func, AArch64Opcode::NeonAddV),
            UNROLL + 3,
            "inv adds + combine"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonUmovGen), 2, "2 .2D lanes");
        assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 2, "2 LDP pairs");
        // Every UADALP carries the fixed `.4S` INPUT arrangement and its
        // source (operand 1) is NOT the accumulator (operand 0, tied def-use).
        for blk in &func.blocks {
            for &id in &blk.insts {
                let inst = func.inst(id);
                if inst.opcode == AArch64Opcode::NeonUadalpV {
                    assert!(
                        matches!(inst.operands.last(), Some(MachOperand::Imm(a)) if *a == ARR_S4),
                        "UADALP input arrangement must be .4S"
                    );
                    assert_ne!(
                        inst.operands[0], inst.operands[1],
                        "UADALP source Vn (op 1) must be the abs vector, not the accumulator"
                    );
                }
            }
        }
        // The scalar chain is untouched (purely additive): the diamond survives.
        assert!(count(&func, AArch64Opcode::SubRR) >= 1, "scalar arm kept");
    }

    #[test]
    fn vectorizes_chain_abs_widen_plain() {
        // `s(i64) += (a[i]).unsigned_abs() as i64` (no invariant addend): no
        // DUP at all (no ones splat, no invariant), no per-Q ADD.4S beyond the
        // .2D combine.
        let mut func = build_chain_abs_loop(1);
        let mut pass = NeonArrayPass::new();
        assert!(pass.run(&mut func), "plain chain abs-sum should fire");
        assert_eq!(pass.fired(), 1);
        assert_eq!(count(&func, AArch64Opcode::NeonAbsV), UNROLL);
        assert_eq!(count(&func, AArch64Opcode::NeonUadalpV), UNROLL);
        assert_eq!(
            count(&func, AArch64Opcode::NeonUaddwV),
            0,
            "UADDW replaced by UADALP"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonUaddw2V),
            0,
            "UADDW2 replaced by UADALP"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonDupGen), 0, "no DUPs at all");
        assert_eq!(count(&func, AArch64Opcode::NeonAddV), 3, "combine only");
    }

    #[test]
    fn chain_abs_bails_on_sext_root() {
        // `Sxtw` root = `wrapping_abs() as i64` (SIGN-extension) — a DIFFERENT
        // function from the UADALP zext lowering on abs >= 2^31 (the i32::MIN
        // lane). MUST bail — this is the signed/unsigned miscompile axis.
        let mut func = build_chain_abs_loop(2);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "Sxtw(abs) must BAIL (zext-only)");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonAbsV), 0);
    }

    #[test]
    fn chain_abs_bails_on_non_negation_arm() {
        // Neg arm computing `1 - x` is not `abs` — must BAIL.
        let mut func = build_chain_abs_loop(3);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "non-negation arm must BAIL");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonAbsV), 0);
    }

    #[test]
    fn chain_abs_bails_on_extra_arm_inst() {
        // Any instruction beyond the exact `MovR phi, x; B` in the identity arm
        // deviates from the proven diamond — must BAIL.
        let mut func = build_chain_abs_loop(4);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "extra arm instruction must BAIL");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonAbsV), 0);
    }

    #[test]
    fn chain_abs_bails_on_third_phi_writer() {
        // A third in-loop write of the phi could change the joined value on
        // some path — must BAIL.
        let mut func = build_chain_abs_loop(5);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "third phi writer must BAIL");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonAbsV), 0);
    }

    #[test]
    fn chain_abs_bails_on_wrong_condition() {
        // `EQ` is not a sign test: the diamond is not an abs — must BAIL.
        let mut func = build_chain_abs_loop(6);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "non-sign-test condition must BAIL");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonAbsV), 0);
    }

    #[test]
    fn chain_abs_bails_on_loop_defined_addend() {
        // The addend is (re)defined inside the loop — not invariant, the DUP
        // would freeze one value — must BAIL.
        let mut func = build_chain_abs_loop(7);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "in-loop addend must BAIL");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonAbsV), 0);
    }

    #[test]
    fn chain_abs_bails_on_term_bypassing_diamond() {
        // The loop CONTAINS an abs diamond but the reduction term widens the
        // RAW load instead of the phi: with a diamond present the ONLY
        // admissible term is the diamond's — must BAIL entirely (fail-closed;
        // no other track may fire on this loop either).
        let mut func = build_chain_abs_loop(8);
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "term bypassing the diamond must BAIL");
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonAbsV), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
    }
    /// i64 forward chain `while k <u N { carrier(w,k,lenB); acc += a[k]; k+=1 }`
    /// where N is a MERGED register: bbA writes `N = lenA` (Movz 8), bbB writes
    /// `N = lenB` (Movz 3), joining before the loop. The carrier's length is
    /// `lenB` — NOT the loop bound on the runtime path through bbA (N=8, carrier
    /// traps at k=3). The last-wins def map records bbB's `MovR N, lenB`, so
    /// `strip_copies(N) == lenB` and `chain_bound_agrees` SPURIOUSLY accepts it.
    ///
    /// carrier_len: 0 => carrier bound = lenB (the exploit); 1 => carrier
    /// bound = N itself (genuine agreement); 2 => no carrier at all.
    fn build_merged_bound_carrier_loop(carrier_len: u8) -> MachFunction {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb_a = func.create_block();
        let bb_b = func.create_block();
        let pre = func.create_block();
        let header = func.create_block();
        let gblk = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();
        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a (param placeholder)
        push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // wbase (carrier base)
        push(&mut func, bb0, Movz, vec![v64(3), i(8)]); // lenA = 8
        push(&mut func, bb0, Movz, vec![v64(4), i(3)]); // lenB = 3
        push(&mut func, bb0, Movz, vec![v64(41), i(8)]); // es = 8
        push(&mut func, bb0, CmpRI, vec![v64(3), i(0)]);
        push(&mut func, bb0, BCond, vec![i(CC_EQ), b(bb_b)]);
        push(&mut func, bb0, B, vec![b(bb_a)]);
        // bbA first, bbB second: bbB's `MovR N, lenB` is later in arena order and
        // wins the last-wins def map entry for N.
        push(&mut func, bb_a, MovR, vec![v64(5), v64(3)]);
        push(&mut func, bb_a, B, vec![b(pre)]);
        push(&mut func, bb_b, MovR, vec![v64(5), v64(4)]);
        push(&mut func, bb_b, B, vec![b(pre)]);
        push(&mut func, pre, Movz, vec![v64(59), i(0)]);
        push(&mut func, pre, Movz, vec![v64(60), i(0)]);
        push(&mut func, pre, B, vec![b(header)]);
        push(&mut func, header, CmpRR, vec![v64(59), v64(5)]);
        push(&mut func, header, BCond, vec![i(CC_LO), b(gblk)]);
        push(&mut func, header, B, vec![b(exit)]);
        match carrier_len {
            0 => push(
                &mut func,
                gblk,
                TrapBoundsCheckExact,
                vec![v64(2), v64(59), v64(4)],
            ),
            1 => push(
                &mut func,
                gblk,
                TrapBoundsCheckExact,
                vec![v64(2), v64(59), v64(5)],
            ),
            _ => {}
        }
        push(
            &mut func,
            gblk,
            Madd,
            vec![v64(66), v64(59), v64(41), v64(0)],
        );
        push(&mut func, gblk, LdrRI, vec![v64(67), v64(66), i(0)]);
        push(&mut func, gblk, B, vec![b(latch)]);
        push(&mut func, latch, AddRR, vec![v64(71), v64(60), v64(67)]);
        push(&mut func, latch, AddRI, vec![v64(72), v64(59), i(1)]);
        push(&mut func, latch, MovR, vec![v64(60), v64(71)]);
        push(&mut func, latch, MovR, vec![v64(59), v64(72)]);
        push(&mut func, latch, B, vec![b(header)]);
        push(&mut func, exit, MovR, vec![v64(80), v64(60)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, bb_a);
        func.add_edge(bb0, bb_b);
        func.add_edge(bb_a, pre);
        func.add_edge(bb_b, pre);
        func.add_edge(pre, header);
        func.add_edge(header, gblk);
        func.add_edge(header, exit);
        func.add_edge(gblk, latch);
        func.add_edge(latch, header);
        func.next_vreg = 512;
        func
    }

    #[test]
    fn adv_merged_bound_no_carrier_fires() {
        let mut func = build_merged_bound_carrier_loop(2);
        let mut pass = NeonArrayPass::new();
        assert!(pass.run(&mut func), "merged-bound chain (no carrier) fires");
    }

    #[test]
    fn adv_carrier_same_n_fires() {
        let mut func = build_merged_bound_carrier_loop(1);
        let mut pass = NeonArrayPass::new();
        assert!(pass.run(&mut func), "carrier over N itself fires");
    }

    #[test]
    fn adv_carrier_foreign_len_must_bail() {
        // REVIEW REPRO (2026-08-17): with map-based agreement this FIRED and
        // erased a guaranteed bounds trap. Original program: traps (BRK) at k=3 on the bbA path
        // (N=8, carrier `3 <u 3` fails). Transformed program (observed dump):
        // vector guard N>=8 -> vector loop consumes k=0..8 with NO carrier ->
        // scalar header entered at k=8 -> exits immediately -> returns normally.
        let mut func = build_merged_bound_carrier_loop(0);
        let mut pass = NeonArrayPass::new();
        assert!(
            !pass.run(&mut func),
            "a carrier whose length register is NOT the loop bound must BAIL \
         (review repro: merged multi-def N with a stale last-def map entry \
         aliasing the foreign length; strict_copy_root terminates at the \
         multi-def N and the identity compare rejects lenB)"
        );
    }

    /// The LdrRO slice-sum shape (post-`ext_addr` fusion) must BAIL: the
    /// recognizer runs BEFORE addr-mode fusion, sees only FORM 1
    /// `Madd`+`LdrRI`, and deliberately keeps `LdrRO` OFF the chain
    /// whitelist (a FORM 2 arm added for it was dead code — `node_ok`
    /// routes only `LdrRI` leaves — and was removed by review).
    #[test]
    fn chain_bails_on_ldro_load() {
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let header = func.create_block();
        let gblk = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();
        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        use AArch64Opcode::*;
        push(&mut func, bb0, Copy, vec![v64(0), v64(0)]);
        push(&mut func, bb0, Copy, vec![v64(5), v64(5)]);
        push(&mut func, bb0, Movz, vec![v64(59), i(0)]);
        push(&mut func, bb0, Movz, vec![v64(60), i(0)]);
        push(&mut func, bb0, B, vec![b(header)]);
        push(&mut func, header, CmpRR, vec![v64(59), v64(5)]);
        push(&mut func, header, BCond, vec![i(CC_LO), b(gblk)]);
        push(&mut func, header, B, vec![b(exit)]);
        push(&mut func, gblk, LdrRO, vec![v64(67), v64(0), v64(59), i(7)]);
        push(&mut func, gblk, B, vec![b(latch)]);
        push(&mut func, latch, AddRR, vec![v64(71), v64(60), v64(67)]);
        push(&mut func, latch, AddRI, vec![v64(72), v64(59), i(1)]);
        push(&mut func, latch, MovR, vec![v64(60), v64(71)]);
        push(&mut func, latch, MovR, vec![v64(59), v64(72)]);
        push(&mut func, latch, B, vec![b(header)]);
        push(&mut func, exit, MovR, vec![v64(80), v64(60)]);
        push(&mut func, exit, Ret, vec![]);
        func.add_edge(bb0, header);
        func.add_edge(header, gblk);
        func.add_edge(header, exit);
        func.add_edge(gblk, latch);
        func.add_edge(latch, header);
        func.next_vreg = 512;
        let mut pass = NeonArrayPass::new();
        assert!(!pass.run(&mut func), "LdrRO in the body must fail closed");
    }
}
