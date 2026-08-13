// trust-cg-opt - SOUND NEON 64-bit-accumulator byte-widening reduction vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON byte-widening reduction vectorizer, u64 accumulator (`neon-bytesum`)
//!
//! Vectorizes counted loops that fold a **byte** array into a **64-bit**
//! (`Gpr64`) accumulator, of the shape
//!
//! ```text
//! acc: u64 = seed;  for i in 0..N (i <u N):  acc += TERM(a_u8[i])
//! ```
//!
//! where `TERM` is one of
//!
//! ```text
//!   acc += popcount(a[i])              // byte-popcount sum  (v3_popcount)
//!   acc += a[i] as u64                 // plain byte sum
//!   acc += (a[i] == 0) as u64          // count-if == 0  (p7_sieve)
//!   acc += ((a[i] & M) OP C) as u64    // masked-byte compare  (k4_utf8_maskcount)
//! ```
//!
//! The last form (`OP` is `==` or `!=`, `M`/`C` byte constants) is a STRAIGHT
//! `acc += zext(cset)` reduction whose per-byte predicate the bridge materializes
//! with a `CSet` (`AndRI(load, M); CmpRI(_, C); CSet(c, cc)`) rather than a
//! branch. It lowers with an `AND.16B` (isolate `b & M`) + `CMEQ.16B` (`0xFF`
//! where `(b&M)==C`) [+ `NOT.16B` for `!=`] + `AND.16B`-by-ones prefix feeding
//! the same UDOT-by-ones fold. The UTF-8 code-point-start count
//! `(b & 0xC0) != 0x80` is exactly this shape.
//!
//! The count-if form is not a straight `acc = MovR(AddRR(acc, term))` latch
//! reduction — the bridge lowers `if a[i]==0 { c+=1 }` to a BRANCH-based
//! conditional-increment DIAMOND (`LDRB; Uxtb; Cbz w, then`; the `then` arm does
//! `c+1`; the arms rejoin at a phi-merge `c = MovR(merge)` in the latch). This
//! pass recognizes that diamond directly and lowers it with a `CMEQ.16B` (== 0
//! -> 0xFF per byte lane) + `AND.16B` (0xFF -> 0x01) prefix feeding the same
//! UDOT-by-ones fold. SCOPED to the `== 0` predicate; any other predicate stays
//! scalar.
//!
//! `a` is a `[u8; N]` read-only array (loaded, never stored) and `N` is a
//! **compile-time constant** loop bound that also bounds the array index (the
//! same `N` guards both the loop-continue test and the `a[i]` bounds check, so
//! `N <= a.len()` and every `a[iv]` with `iv <u N` is in bounds).
//!
//! ## Why the mature reduction passes miss it
//!
//! [`crate::neon_array`]'s widening `TRACK B` handles exactly these byte terms
//! (`Uxtb`/popcount), but ONLY into an **`i32`** accumulator and ONLY for a
//! strict 2-block `{header, latch}` loop. `v3_popcount` accumulates into a
//! `u64` (the popcount is `(a[i] as u32).count_ones() as u64`, a **64-bit** SWAR
//! folded into a `Gpr64` acc), and — because its `a[i]` bounds check is not
//! eliminated — its innermost loop is **3 blocks** (`{loop-guard, bounds-guard,
//! body}`). Both facts make `neon_array` (and every other neon reduction pass)
//! BAIL. `neon-bytesum` closes exactly this gap.
//!
//! ## Why this is SOUND
//!
//! The transform is **purely additive**: it inserts a NEON main loop in front
//! of the scalar loop and NEVER edits the scalar loop's instructions (including
//! its bounds checks). The scalar loop is therefore correct by construction;
//! only the inserted vector loop plus the horizontal fold need justifying.
//!
//! * **The vector loads read only in-bounds memory the scalar loop also reads.**
//!   The vector header enters the body only while `iv <u N - (W-1)` (where
//!   `W = width(kind)`, the per-kind bytes-per-iteration: 128 for the plain
//!   byte sum's 8 accumulators, 64 otherwise), so
//!   every element index `iv .. iv+W-1` is `<u N <= a.len()` — an index the
//!   scalar loop, guarded by the same `iv <u N`, also reads. Reads are
//!   read-only, and the reduction target is a REGISTER (`acc`), so aliasing
//!   among reads is irrelevant.
//! * **The per-byte term equals the scalar term.** For a byte `b in [0,255]`,
//!   `CNT.16B` computes `popcount(b)` per lane (`= popcount(b & 0xFFFFFFFF)`, the
//!   scalar `(a[i] as u32).count_ones()` — the high bits are zero, so the mask
//!   is a no-op), and `a[i] as u64` is `zext8(b)`. The byte contributions are
//!   folded straight into the `.4S` accumulators by the FAITHFULLY-PROVEN
//!   `UDOT`-by-ones accumulate (`trust-cg-verify::neon_lowering_proofs`,
//!   `proof_neon_udotv_lanewise_4s`): per i32 lane
//!   `acc[i] += sum_j zext32(src.byte[4i+j]) * 1` — algebraically IDENTICAL,
//!   lane for lane, to the UADDLP(`.16B->.8H`) + UADDLP(`.8H->.4S`) + ADD.4S
//!   chain it replaces (zext associativity: both compute the exact 4-byte group
//!   sum `<= 1020` and add it into lane `i` mod 2^32), in ONE SIMD op per Q
//!   instead of three — the structure LLVM itself emits for this loop
//!   (`udot.4s acc, data, ones` x 4 accumulators).
//! * **No `.4S` overflow (why the const bound is required).** The vector partial
//!   for ONE pass over the array holds `<= 8*N` (popcount) / `<= 255*N` (sum);
//!   we fire only when that provably fits `i32` (`8*N < 2^31`), so the `.4S`
//!   partials are EXACT. The horizontal fold then **zero-extends** each `i32`
//!   lane sum to `u64` before adding into the `Gpr64` acc — exact in `u64`. (A
//!   runtime `N`, or a partial that could exceed `i32`, BAILS: the `.4S` modulus
//!   `2^32` would diverge from the scalar `u64` modulus `2^64`.)
//! * **Reassociation is sound.** The `unroll(kind)` disjoint accumulators
//!   (8 for the plain byte sum, 4 otherwise) + balanced combine
//!   + lane fold reproduce the scalar left-fold because `u64`/`i32` add is
//!     associative and commutative; the pre-loop `acc` seed is folded in (never
//!     overwritten) so the scalar tail continues from it.
//!
//! Every NEON op emitted (`NeonMovi`, `NeonLdpQPost`, `NeonCntV`, `NeonCmeqV`,
//! `NeonAndV`, `NeonUdotV`, `NeonAddV`, `NeonUmovGen`) is already
//! coverage-credited by a discharged proof — this pass introduces **no new
//! emittable opcode** (`NeonUdotV` is the FAITHFUL D-pair accumulate obligation
//! the ctpop-reduction lowering already relies on; the ones vector is the same
//! `MOVI.16B #1` the count-if mask uses). The count-if kernel's `CMEQ.16B` mask
//! is co-credited by the opcode-level `cmeqv.4s` query and additionally backed
//! by the FAITHFUL `.16B` byte-lane obligation `proof_neon_cmeqv_lanewise_16b`
//! (`trust-cg-verify::neon_lowering_proofs`); `AND.16B` by `andv.16b`.
//!
//! ## Fail-closed guards (BAIL preconditions)
//!
//! Innermost loop only; a single `Gpr64` accumulator read ONLY along its
//! reduction path (an `AddRR` reduction, or the count-if diamond's `+1`/`+0`
//! arms); a single `+1` `Gpr64` induction; a compile-time-constant bound `N`
//! with `width(kind) <= N` and `8*N < 2^31` (popcount) / `< 2^31` (count-if) used by
//! EVERY `iv <u ·` guard in the loop (so `N <= a.len()`); a term that is exactly
//! a byte popcount, a widened byte load, or a byte `== 0` count-if diamond,
//! whose index is `iv` and whose base is loop-invariant; and NO
//! store/call/atomic/unmodeled op anywhere in the loop body. A `!= 0`
//! predicate, a non-`+1` increment, a signed / non-byte load, a runtime /
//! multi-valued bound, or `acc` read off the reduction path all BAIL — anything
//! unrecognized leaves the loop entirely scalar.
//!
//! Default-ON; disable with `TRUST_CG_DISABLE_PASSES=neon_bytesum`. Every opcode
//! it emits is credited by the per-compile proof gate — CNT/CMEQ/AND/UDOT/ADD/
//! UMOV via their faithful lowering proofs, the paired-Q load via the shared
//! Ldr*/Str* memory debt, and the `MOVI #0`/`MOVI #1` byte-mask via
//! constant-materialization covered-elsewhere (`function_verifier`) — so a
//! vectorized function promotes with `TCG_NO_PROOF_CERTS` OFF (no fail-closed
//! regression).

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

#[cfg(test)]
mod tests;

/// Bytes per 128-bit Q register.
const LANES_PER_Q: i64 = 16;
/// The SMALLEST per-kind byte width (all kinds use >= 4 Q regs / 64B per
/// iteration). Recognition's EARLY bound gate — which runs before the term
/// kind is known — checks against this; the exact per-kind `width(kind)` gate
/// re-checks (strictly tighter) once the kind is resolved.
const WIDTH_MIN: i64 = 4 * LANES_PER_Q;

/// NEON arrangement operand codes (match neon_array / the encoder mapping).
const ARR_B16: i64 = 1;
const ARR_S4: i64 = 5;
/// NEON element-size code for an `S` (32-bit) `UMOV` lane extract.
const ELEM_S: i64 = 4;

/// AArch64 condition code for unsigned lower (`LO`) — the counted `usize`
/// loop's `iv <u N` guard, as emitted for `while i < N` on a `usize` index.
const CC_LO: i64 = 3;
/// AArch64 condition code for not-equal (`NE`) — the `BCond` of the
/// CSet-materialized guard `CmpRR(iv,N); CSet(c,LO); CmpRI(c,0); BCond(NE,cont)`
/// (branch to the in-loop continue when the `iv <u N` boolean is nonzero).
const CC_NE: i64 = 1;
/// AArch64 condition code for equal (`EQ`) — the `CSet` cc of a masked-byte
/// compare materialized as `(a[i] & MASK) == CONST` (`PredMaskCmp`, ne=false).
const CC_EQ: i64 = 0;
/// AArch64 condition code for unsigned higher-or-same (`HS`/`CS`) — the reverse
/// polarity of the hex-nibble constant-select diamond head `CmpRI(nibble, 10);
/// BCond(HS, arm87)` (branch to the `nibble >= 10` arm).
const CC_HS: i64 = 2;

/// The lowercase-hex nibble map's two ASCII bases: `nib(n) = n + LO_BASE` for
/// `n < 10` (`'0'..'9'` = 48..57) and `n + HI_BASE` for `n >= 10`
/// (`'a'..'f'` = 97..102). `NIB_DELTA = HI_BASE - LO_BASE = 39`, and the nibble
/// boundary is `NIB_THRESHOLD = 10`.
const NIB_LO_BASE: i64 = 48;
const NIB_HI_BASE: i64 = 87;
const NIB_DELTA: i64 = NIB_HI_BASE - NIB_LO_BASE; // 39
const NIB_THRESHOLD: i64 = 10;
/// `48 * 2 = 96`: the constant contribution of both nibbles' `LO_BASE` per byte,
/// folded into the vector loop as a `#96`-per-byte-lane UDOT stream.
const HEX_CONST_PER_BYTE: i64 = NIB_LO_BASE * 2; // 96

/// Largest constant loop bound admitted for the POPCOUNT kernel: one pass'
/// partial is `<= 8*N`, and it must fit `i32` (`< 2^31`) so the `.4S` partials
/// cannot wrap. (Plain byte-sum uses the tighter `255*N < 2^31`.)
const MAX_BOUND_POP: i64 = (1i64 << 31) / 8; // 2^28
const MAX_BOUND_SUM: i64 = (1i64 << 31) / 255;
/// Largest constant loop bound admitted for the COUNT-IF kernel. The per-byte
/// contribution is 0/1, so the TOTAL count over one array pass is `<= N`, and
/// every individual `.4S` lane partial is `<= N` as well (each lane accumulates
/// a disjoint subset of the byte contributions). Firing only when `N < 2^31`
/// therefore guarantees the `.4S` partials never wrap (the `.4S` modulus `2^32`
/// stays faithful to the scalar `u64` modulus). A runtime `N` BAILS.
const MAX_BOUND_COUNT: i64 = 1i64 << 31;
/// Largest constant loop bound admitted for the HEX-NIBBLE-SUM kernel. The
/// per-byte value is `P'_b = (hi+lo) + 96 + 39*[hi>=10] + 39*[lo>=10] <= 204`, so
/// the WHOLE-array sum (and hence every individual `.4S` lane partial, which
/// accumulates a subset of it) is `<= 204*N`. Firing only when `204*N < 2^31`
/// guarantees the `.4S` partials never wrap before the u64 fold. A runtime `N`
/// (non-constant bound) BAILS.
const MAX_BOUND_HEX: i64 = (1i64 << 31) / 204;

/// 64-bit SWAR popcount magic constants (the `(x as u32).count_ones() as u64`
/// lowering the bridge emits — verified against the MIR dump).
const M55: i64 = 0x5555_5555_5555_5555u64 as i64;
const M33: i64 = 0x3333_3333_3333_3333u64 as i64;
const M0F: i64 = 0x0F0F_0F0F_0F0F_0F0Fu64 as i64;
const MASK32: i64 = 0xFFFF_FFFF; // the `as u32` mask preceding the SWAR

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `neon-bytesum` machine pass.
#[derive(Default)]
pub struct NeonBytesumPass {
    fired: usize,
}

impl NeonBytesumPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }
    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonBytesumPass {
    fn name(&self) -> &str {
        "neon-bytesum"
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

impl NeonBytesumPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;
        // Recognize read-only first; applying a plan only ADDS blocks (never
        // renumbers existing ids or edits other loops), so recognized data for
        // other loops stays valid.
        let mut plans = Vec::new();
        let def_map = build_def_map(func);
        for lp in loops.all_loops() {
            // innermost only: no other loop's header lies inside this body.
            let is_innermost = loops
                .all_loops()
                .all(|other| other.header == lp.header || !lp.body.contains(&other.header));
            if !is_innermost {
                continue;
            }
            if let Some(rec) =
                Recognized::recognize(func, dom, &def_map, loops, lp.header, lp.latch, &lp.body)
            {
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
        if changed && std::env::var("TRUST_CG_DUMP_NEONBYTESUM").is_ok() {
            eprintln!("[neon-bytesum] fn={} vectorized={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// Which per-byte reduction term the recognized loop folds into the `u64`
/// accumulator. All three lower to the SAME faithfully-proven `UADDLP` widen
/// chain + `.4S` accumulate + zero-extending `u64` fold; they differ only in the
/// per-Q-register *prefix* that produces the `.16B` byte contributions.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TermKind {
    /// `acc += popcount(a[i])` — `CNT.16B` prefix.
    Popcount,
    /// `acc += a[i] as u64` — no prefix (the raw byte lanes widen directly).
    ByteSum,
    /// `acc += (a[i] == 0) as u64` — the branch-based conditional-increment
    /// diamond (count-if `== 0`). Prefix: `CMEQ.16B` against a zero vector
    /// (0xFF per matching byte) then `AND.16B` with an all-`0x01`-lane mask
    /// (collapse 0xFF -> 0x01), so each byte lane contributes exactly 1/0.
    PredCountEqZero,
    /// `acc += ((a[i] & MASK) OP CONST) as u64` — a masked-byte compare whose
    /// boolean is materialized by a `CSet` (NOT a branch diamond), folded as a
    /// STRAIGHT `acc = MovR(AddRR(acc, zext(cset)))` reduction. `OP` is `==`
    /// (`ne=false`) or `!=` (`ne=true`); `MASK`/`CONST` are byte constants in
    /// `0..=255`. Prefix: `AND.16B` (isolate `b & MASK` per lane), `CMEQ.16B`
    /// against a `CONST`-broadcast vector (`0xFF` where `(b&MASK)==CONST`),
    /// `NOT.16B` when `ne` (invert to `!=`), then `AND.16B` with the all-`0x01`
    /// lane mask (collapse `0xFF -> 0x01`), so each byte lane contributes 1/0.
    /// The UTF-8 code-point-start count `(b & 0xC0) != 0x80` is this shape.
    PredMaskCmp { mask: i64, cnst: i64, ne: bool },
    /// `acc += (a[iv] REL a[iv-1]) as u64` — a byte-STENCIL count-if over a
    /// `[u8; N]`: the BRANCH-based conditional-increment diamond whose head
    /// compares the CURRENT byte `a[iv]` against its SHIFTED NEIGHBOR `a[iv-1]`
    /// (`REL` is `==`, `ne=false`, or `!=`, `ne=true`). The RLE "count runs"
    /// kernel `runs = 1 + count_{j=1..N}(a[j] != a[j-1])` is this shape
    /// (`ne=true`). Lowered per 16-byte block by forming the `a[iv+1]` FORWARD
    /// window via the FAITHFULLY-PROVEN `EXT.16B #1` (slide the loaded block one
    /// byte, pulling the first byte of the adjacent block), then `CMEQ.16B`
    /// against the un-shifted block, then (for `!=`) `NOT.16B`, then the existing
    /// `AND.16B`-by-ones + `UDOT`-by-ones count fold — 1/0 per byte lane. Because
    /// the window is FORWARD (`a[iv+1]`), the vector loop reindexes `a[j] vs
    /// a[j-1]` (j in [iv, iv+width)) to `a[i] vs a[i+1]` over the block loaded at
    /// `base + iv - 1` (so `iv` MUST start at 1 — the first predecessor `a[0]` is
    /// then in bounds — verified fail-closed).
    PredStencilCmp { ne: bool },
    /// `s += nib(b>>4) + nib(b&15)` summed over a `[u8; N]`, where
    /// `nib(n) = n + if n < 10 { 48 } else { 87 }` maps a nibble to its
    /// lowercase-hex ASCII code — the hex-digit-code REDUCTION. Each byte's two
    /// `nib` maps are branchless CONSTANT-SELECT DIAMONDS (`if nibble < 10`
    /// selects `48` else `87`; if-convert leaves them branchy because the
    /// selected value feeds the accumulator, not the loop-carried recurrence).
    ///
    /// EXACT ALGEBRAIC DECOMPOSITION (integer arithmetic, mod `2^64`):
    /// ```text
    ///   nib(n) = n + 48 + 39 * [n >= 10]        (87 - 48 = 39)
    ///   per byte:  nib(hi) + nib(lo)
    ///          = (hi + lo) + 96 + 39*[hi>=10] + 39*[lo>=10]        <= 204 (fits a byte)
    ///   s = Σ_b (nib(hi)+nib(lo)) = Σ_b P'_b   where P'_b = the per-byte value above
    /// ```
    /// Lowered per 16-byte block by forming `hi = USHR.16B #4`,
    /// `lo = AND.16B #15`, the two hex-letter masks
    /// `c_hi/c_lo = AND.16B(CMHS.16B(nibble, #10), #39)` (39 where `nibble>=10`,
    /// else 0), and a constant `#96` block, then dot-summing all FIVE byte streams
    /// (`hi`, `lo`, `c_hi`, `c_lo`, `#96`) into the `.4S` accumulators via the
    /// FAITHFULLY-PROVEN `UDOT`-by-ones fold. The `#96`-per-byte stream contributes
    /// `96` for EACH byte the vector loop processes — exactly matching the scalar
    /// tail's per-byte `96` — so the split between vector prefix and scalar tail is
    /// exact regardless of where it falls. `USHR.16B` and `CMHS.16B` are faithfully
    /// proven `.16B`-lanewise (`proof_neon_ushrv_lanewise_16b(4)` /
    /// `proof_neon_cmhsv_lanewise_16b`); `AND.16B`, `UDOT`, `ADD.4S`, `MOVI` are
    /// already proven/credited. No `ADD.16B` is emitted (the five streams are
    /// summed by the accumulate UDOT, not a byte-lane add).
    HexNibbleSum,
}

/// Independent `.4S` vector accumulators (ILP), PER TERM KIND.
///
/// The UDOT accumulate chain has ~2.33 cy effective latency on Apple M4 while
/// the 3 load pipes feed 4 Q loads in ~1.33 cy, so saturating the plain
/// byte-sum kernel needs `ceil(latency/feed) * 4 ~= 8` accumulators — measured
/// 2.33 -> 1.63-1.78 cy/64B going 4 -> 8 accs (12 accs show the next wall is
/// load bandwidth; 8 is the stop). `ByteSum` therefore uses 8 accumulators /
/// 128B per iteration.
///
/// `Popcount` and `PredCountEqZero` STAY at 4 (codegen bit-identical to the
/// original): count-if is already throughput-bound at 24 SIMD ops/128B
/// (measured ZERO gain at 8 accs, and the doubled scalar tail is
/// mispredict-hostile on its sieve workload), while 8-acc popcount needs ~25
/// live Q regs for a measured ~10% — not worth the spill risk.
fn unroll(kind: TermKind) -> usize {
    match kind {
        TermKind::ByteSum => 8,
        // Popcount / count-if / masked-compare stay at 4 accumulators (see the
        // count-if throughput note above): the masked-compare prefix is even
        // heavier per Q (AND + CMEQ [+ NOT] + AND), so it is firmly SIMD-op-bound
        // and gains nothing from more accumulators.
        TermKind::Popcount | TermKind::PredCountEqZero | TermKind::PredMaskCmp { .. } => 4,
        // The byte-STENCIL count-if uses 3 accumulators so that the per-iteration
        // block set (`unroll` compared blocks + 1 forward look-ahead block =
        // `unroll + 1` = 4 consecutive Q's) is an EVEN number of Q's, loaded by
        // exactly `(unroll + 1) / 2 = 2` post-index `LDP` pairs with ZERO wasted
        // load (the look-ahead block is the 4th load, itself useful). The prefix
        // per accumulator is heavy (EXT + CMEQ [+ NOT] + AND), so it is
        // SIMD-op-bound and does not want more accumulators.
        TermKind::PredStencilCmp { .. } => 3,
        // The hex-nibble sum has a HEAVY per-block prefix (USHR + AND + 2x CMHS +
        // 2x AND = 6 compute ops, then FIVE accumulate UDOTs into the same `.4S`
        // accumulator — a 5-deep tied-accumulate chain per block). So it is firmly
        // SIMD-op-bound; 4 independent accumulators (64B/iter) give enough ILP to
        // overlap the five-deep chains without the register pressure of 8.
        TermKind::HexNibbleSum => 4,
    }
}

/// Byte elements processed per NEON iteration for `kind`
/// (`unroll(kind) * LANES_PER_Q`).
fn width(kind: TermKind) -> i64 {
    unroll(kind) as i64 * LANES_PER_Q
}

struct Recognized {
    header: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    /// The `Gpr64` induction (`iv += 1`).
    iv: VReg,
    /// The `Gpr64` accumulator (`acc += term`).
    acc: VReg,
    /// Compile-time-constant bound `N` (== array length).
    bound: i64,
    /// Loop-invariant array base pointer.
    base: VReg,
    /// The per-byte reduction term kind.
    kind: TermKind,
    /// True when the accumulator is a **`u32`** (`Gpr32`) rather than the `u64`
    /// (`Gpr64`) default. Only the straight `AddRR` reduction (`Popcount`/
    /// `ByteSum`) admits a `Gpr32` acc; the widen chain still computes the exact
    /// byte-sum in `.4S`/`u64`, and the horizontal fold TRUNCATES to `u32` before
    /// the final 32-bit `AddRR` into the acc. SOUND because `u32`-wrapping add is
    /// add mod `2^32`: `(seed + Σ widened bytes) mod 2^32` equals the scalar
    /// `u32` accumulator exactly, and the loop-invariant seed already sits in the
    /// acc (the fold ADDS, never overwrites, so the seed is folded in once).
    acc_is_u32: bool,
}

impl Recognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        _loops: &LoopAnalysis,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        let dump = std::env::var("TRUST_CG_DUMP_NEONBYTESUM").is_ok();
        macro_rules! bail {
            ($($t:tt)*) => {{
                if dump {
                    eprintln!("[neon-bytesum] bail@{}: {}", func.name, format!($($t)*));
                }
                return None;
            }};
        }
        if dump {
            eprintln!(
                "[neon-bytesum] consider@{} header={:?} latch={:?} body={}",
                func.name,
                header,
                latch,
                body.len()
            );
        }
        if header == latch || body.is_empty() {
            bail!("degenerate loop");
        }
        // `def` is supplied by the caller, built ONCE per recognition sweep.
        // Measured at 99.1% of this pass (110.2ms of 111.3ms, many_fns n=200)
        // when it was rebuilt inside every per-loop attempt.

        // Whitelist every opcode in the loop body (rules out stores / calls /
        // atomics / division and any unmodeled effect).
        let mut loop_insts = HashSet::new();
        for &b in body {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    bail!("disallowed body op {:?}", func.inst(id).opcode);
                }
                loop_insts.insert(id);
            }
        }

        // Preheader: the single non-latch predecessor of the header.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            bail!("header preds != {{latch, preheader}}: {:?}", hpreds);
        }
        let preheader = *hpreds.iter().find(|&&b| b != latch)?;
        let Some(&preheader_term) = func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))
        else {
            bail!("no preheader->header branch");
        };

        // Loop-carried writebacks live in the latch as `d = MovR/Copy(s)` where
        // `d` is read across the back-edge. Identify the `iv` (`s = iv + 1`) and
        // the `acc` (`s = AddRR(acc, term)`).
        let mut iv = None;
        let mut acc_term: Option<(VReg, VReg)> = None; // (acc, term)
        for &id in &func.block(latch).insts {
            let Some((d, s)) = copy_like(func.inst(id)) else {
                continue;
            };
            let Some(&sdef) = def.get(&s.id) else {
                continue;
            };
            let si = func.inst(sdef);
            if si.opcode == AArch64Opcode::AddRR && si.operands.len() == 3 {
                let a = vreg_of(&si.operands[1])?;
                let b = vreg_of(&si.operands[2])?;
                // iv: d == a and b == const 1 (or symmetric).
                if a == d && const_value(func, def, b) == Some(1) {
                    iv = Some(d);
                    continue;
                }
                if b == d && const_value(func, def, a) == Some(1) {
                    iv = Some(d);
                    continue;
                }
                // acc: d is one addend; the other is the reduction term.
                if a == d {
                    acc_term = Some((d, b));
                } else if b == d {
                    acc_term = Some((d, a));
                }
            } else if si.opcode == AArch64Opcode::AddRI
                && si.operands.len() == 3
                && vreg_of(&si.operands[1]) == Some(d)
                && imm_of(&si.operands[2]) == Some(1)
            {
                iv = Some(d);
            }
        }
        let Some(iv) = iv else {
            bail!("no +1 iv writeback in latch")
        };
        if iv.class != RegClass::Gpr64 {
            bail!("iv class not Gpr64 (iv={:?})", iv.class);
        }

        // The single constant bound `N`: every `iv`-relative guard in the loop
        // — the `CmpRR(iv-copy, Nreg)` loop-continue / bounds tests AND every
        // `TrapBoundsCheckExact(_, index, Imm(len))` carrier — must agree on ONE
        // constant N. This forces `loop-bound == array-bounds-limit == a.len()`
        // (differing values BAIL), so `iv <u N` proves every `a[iv]` in bounds
        // and the vector prefix reads only memory the scalar loop also reads.
        // Require `width(kind) <= N` (checked in two stages: `WIDTH_MIN` here,
        // the exact per-kind width once the kind is resolved).
        let mut bound: Option<i64> = None;
        let record = |n: i64, bound: &mut Option<i64>| -> Option<()> {
            match *bound {
                Some(prev) if prev != n => None,
                _ => {
                    *bound = Some(n);
                    Some(())
                }
            }
        };
        for &b in body {
            for &id in &func.block(b).insts {
                let inst = func.inst(id);
                match inst.opcode {
                    AArch64Opcode::CmpRR if inst.operands.len() == 2 => {
                        let x = vreg_of(&inst.operands[0])?;
                        let y = vreg_of(&inst.operands[1])?;
                        // The `iv <u N` loop-continue / bounds compare.
                        if same_as_iv(func, &def, x, iv) {
                            let Some(n) = const_value(func, def, y) else {
                                bail!("cmp bound not constant");
                            };
                            if record(n, &mut bound).is_none() {
                                bail!("cmp bound {} disagrees", n);
                            }
                        } else if is_byte_load_val(func, &def, &loop_insts, x)
                            && is_byte_load_val(func, &def, &loop_insts, y)
                        {
                            // The byte-STENCIL count-if's diamond-head compare
                            // `CmpRR(a[iv], a[iv-1])` — two byte VALUES, not a loop
                            // bound. It contributes no N (the diamond recognizer
                            // validates the exact stencil shape). SOUND: a compare
                            // of two loaded bytes never controls loop exit here (the
                            // forward-chain gate proves control leaves only on
                            // `iv >= N`).
                        } else {
                            bail!("cmp lhs not iv (and not a byte-stencil compare)");
                        }
                    }
                    AArch64Opcode::CmpRI if inst.operands.len() == 2 => {
                        // The 12-bit-immediate form `cmp iv, #N` (N <= 4095 folds
                        // to it): the immediate IS the constant N and joins the
                        // single-N agreement. Two other CmpRI shapes are
                        // admissible and contribute NO bound:
                        //   * the CSet-materialized guard's boolean re-test
                        //     `CmpRI(c, 0)` with `c` a CSet result (its guard
                        //     shape is fully validated by the chain walk);
                        //   * the masked-byte-compare's data-materialize
                        //     `CmpRI(v, CONST); CSet(res, cc)` (PredMaskCmp) —
                        //     detected by an IMMEDIATELY-following `CSet`. This is
                        //     a data value fed into a `CSet`, never a loop-exit
                        //     control test (the forward-chain gate proves control
                        //     leaves the loop only on `iv >= N`), so it joins no
                        //     bound agreement.
                        // Anything else BAILS.
                        let x = vreg_of(&inst.operands[0])?;
                        let n = imm_of(&inst.operands[1])?;
                        if same_as_iv(func, &def, x, iv) || is_iv_minus_one(func, &def, x, iv) {
                            // `iv <u N` loop guard OR the byte-STENCIL count-if's
                            // predecessor bounds check `(iv-1) <u N` — the latter's
                            // `iv-1` is induction-derived (never a data value), and
                            // its length joins the single-N agreement (it must equal
                            // the loop bound). SOUND: control leaves the loop only on
                            // an induction-vs-N condition, never on data.
                            if record(n, &mut bound).is_none() {
                                bail!("cmpri bound {} disagrees", n);
                            }
                        } else if !((n == 0 && is_cset_result(func, &def, x))
                            || cmpri_feeds_cset(func, b, id)
                            || is_internal_diamond_head(func, b, body))
                        {
                            // A data compare `CmpRI(x, C)` (x not the iv) is
                            // admissible ONLY when its containing block is an
                            // INTERNAL diamond head — BOTH successors are in the
                            // loop body (a value-select, never a loop exit; the
                            // hex-nibble kernel's `if nibble < 10` select). It
                            // contributes no bound. SOUND: control still leaves the
                            // loop only on an `iv`-vs-`N` guard (proven by the
                            // per-kind chain gate); an internal diamond can only
                            // route WITHIN the body. Anything else BAILS.
                            bail!("cmpri lhs not iv");
                        }
                    }
                    AArch64Opcode::TrapBoundsCheckExact if inst.operands.len() == 3 => {
                        // `[base, index, Imm(len)]`: the index must be the iv, and
                        // its length joins the single-N agreement.
                        let index = vreg_of(&inst.operands[1])?;
                        if !same_as_iv(func, &def, index, iv) {
                            bail!("trap index not iv (index={:?})", index);
                        }
                        if record(imm_of(&inst.operands[2])?, &mut bound).is_none() {
                            bail!("trap len disagrees with loop bound");
                        }
                    }
                    _ => {}
                }
            }
        }
        let Some(bound) = bound else {
            bail!("no constant iv bound found")
        };
        // Early gate against the SMALLEST per-kind width (the kind is not yet
        // known here); the exact `bound < width(kind)` re-check below is
        // strictly tighter and runs once the kind is resolved.
        if bound < WIDTH_MIN {
            bail!("bound {} < WIDTH_MIN {}", bound, WIDTH_MIN);
        }

        // Reduction kind. Two disjoint shapes fold a byte array into the `u64`
        // acc:
        //   * a STRAIGHT `acc = MovR(AddRR(acc, term))` latch reduction whose
        //     term is a byte popcount / widened byte load (Popcount / ByteSum);
        //   * the BRANCH-based conditional-increment DIAMOND where the acc's
        //     latch writeback merges `{acc, acc+1}` under a byte `== 0`
        //     predicate (PredCountEqZero — the `if a[i]==0 { c+=1 }` shape).
        // The latch scan above finds a straight `AddRR` reduction as
        // `acc_term`; if there is none, try the diamond.
        let (kind, acc, base, acc_is_u32) = if let Some((acc, term)) = acc_term {
            // Straight `acc = acc + TERM` reduction. The acc is `u64` (`Gpr64`,
            // v3_popcount) OR `u32` (`Gpr32`, e07's `s: u32` byte-sum). Both are
            // SOUND: the widen chain sums the widened bytes exactly in `.4S`/`u64`
            // and the fold truncates to the acc width, and `u32`-wrapping add is
            // add mod 2^32 (see `acc_is_u32`).
            if iv == acc || !matches!(acc.class, RegClass::Gpr64 | RegClass::Gpr32) {
                bail!("iv/acc alias or acc class (acc={:?})", acc.class);
            }
            let acc_is_u32 = acc.class == RegClass::Gpr32;
            // SOUNDNESS GATE (forward-chain): the loop body must be a SIMPLE
            // header->latch chain of `iv <u N` bounds/continue guard diamonds and
            // pass-throughs — i.e. EVERY branch out of the loop is controlled by
            // an `iv`-vs-`N` test, never a data value. This rejects a
            // data-dependent early exit (a `break`), which — because the vector
            // loop reduces the full `[0,V)` prefix unconditionally while the
            // scalar loop would have stopped early — would otherwise MISCOMPILE
            // the reduction. (The count-if diamond path below is NOT a simple
            // chain and has its own exact-shape recognizer, so this gate scopes to
            // the straight reduction.) Fail-closed on any deviation.
            if recognize_forward_chain(func, &def, header, latch, body, iv, None).is_none() {
                bail!("not a bounds-guarded forward chain (possible data early-exit)");
            }
            // `acc` may be read ONLY by its reduction `AddRR`. (The writeback
            // copy reads the reduction's result, not `acc` itself.)
            let Some(acc_res) = reduction_result(func, &def, latch, acc) else {
                bail!("no acc reduction result");
            };
            let acc_reduction = *def.get(&acc_res.id)?;
            for &id in &loop_insts {
                if id == acc_reduction {
                    continue;
                }
                let inst = func.inst(id);
                for opd in inst.operands.iter().skip(1) {
                    if vreg_of(opd) == Some(acc) {
                        bail!("acc read by non-reduction op {:?}", inst.opcode);
                    }
                }
            }
            // The reduction term: byte popcount, a widened byte load, or a
            // masked-byte compare `(a[i] & MASK) ==/!= CONST` materialized by a
            // `CSet` (PredMaskCmp). Each is fail-closed; anything else BAILS.
            if let Some((pop, base)) = recognize_bytesum_term(func, &def, &loop_insts, iv, term) {
                (
                    if pop {
                        TermKind::Popcount
                    } else {
                        TermKind::ByteSum
                    },
                    acc,
                    base,
                    acc_is_u32,
                )
            } else if let Some((mask, cnst, ne, base)) =
                recognize_maskcmp_term(func, &def, &loop_insts, iv, term)
            {
                // The masked-compare term contributes 0/1 per byte and folds
                // (like the count-if kernel) into a `u64` acc, whose `.4S` lane
                // partials zero-extend to `u64` in the horizontal fold. A `u32`
                // acc is out of scope here (fail-closed): stay scalar.
                if acc_is_u32 {
                    bail!("maskcmp term requires a u64 acc");
                }
                (
                    TermKind::PredMaskCmp { mask, cnst, ne },
                    acc,
                    base,
                    acc_is_u32,
                )
            } else {
                bail!(
                    "term not a byte popcount/widen-load/maskcmp (term={:?})",
                    term
                );
            }
        } else if let Some((acc, base, dh, arms)) =
            recognize_predcount(func, &def, latch, body, &loop_insts, iv, dump)
        {
            // The conditional-increment diamond (count-if `== 0`). Always `u64`.
            // SOUNDNESS GATE: the same simple-chain requirement as the straight
            // path, with the validated count-if diamond skipped as a unit. This
            // proves the diamond is the ONLY data-dependent control flow in the
            // body (a stray data `break` would leave a block off the chain and
            // BAIL) and that every block is covered exactly once.
            if recognize_forward_chain(func, &def, header, latch, body, iv, Some((dh, arms)))
                .is_none()
            {
                bail!("count-if body not a bounds-guarded chain (possible data early-exit)");
            }
            (TermKind::PredCountEqZero, acc, base, false)
        } else if let Some((acc, base, ne, dh, arms)) =
            recognize_stencil(func, &def, preheader, latch, body, &loop_insts, iv, dump)
        {
            // The byte-STENCIL count-if diamond (`a[iv] REL a[iv-1]`). Always
            // `u64`. Same simple-chain soundness gate (the stencil diamond skipped
            // as a unit); `recognize_stencil` has ALREADY verified `iv` starts at
            // 1 (so the FORWARD-window vector loop's first predecessor `a[0]` is in
            // bounds) and that the two loads are `a[iv]` / `a[iv-1]` off ONE
            // invariant base.
            if recognize_forward_chain(func, &def, header, latch, body, iv, Some((dh, arms)))
                .is_none()
            {
                bail!("stencil body not a bounds-guarded chain (possible data early-exit)");
            }
            (TermKind::PredStencilCmp { ne }, acc, base, false)
        } else if let Some((acc, base)) = recognize_hexnibble(
            HexNibbleLoop {
                func,
                def: &def,
                header,
                latch,
                body,
                loop_insts: &loop_insts,
                iv,
                bound,
            },
            dump,
        ) {
            // The hex-digit-code REDUCTION `s += nib(b>>4) + nib(b&15)`. Always a
            // `u64` acc. `recognize_hexnibble` has ALREADY (a) verified the exact
            // double-nibble accumulation `s = (s + nib(hi)) + nib(lo)`, the byte
            // load, the `hi = LSR #4` / `lo = AND #15` split, and both branchless
            // `nib` constant-select diamonds (`< 10 -> 48`, else `87`), and (b) run
            // its OWN no-early-exit chain gate (proving control leaves the loop only
            // on the `iv <u N` header guard — the two select diamonds are internal
            // value merges, never loop exits).
            (TermKind::HexNibbleSum, acc, base, false)
        } else {
            bail!(
                "no acc add-reduction, count-if(==0), byte-stencil, or hex-nibble reduction in latch"
            );
        };

        // Per-kind width gate (STRICTLY TIGHTER than the early `WIDTH_MIN`
        // check): the vector loop must complete at least one full
        // `width(kind)`-byte iteration. Fail-closed: a ByteSum loop with
        // `64 <= N < 128` stays fully scalar. The byte-STENCIL count-if needs a
        // strictly LARGER floor: its vector loop starts at `iv=1`, reads a
        // 1-block FORWARD look-ahead (`width + 16` bytes/iter), and guards on
        // `iv <u N - width - 14` (`stencil_main_bound`); one iteration requires
        // `1 <u N - width - 14`, i.e. `N >= width + 16`.
        let width_floor = match kind {
            TermKind::PredStencilCmp { .. } => width(kind) + LANES_PER_Q + 2,
            _ => width(kind),
        };
        if bound < width_floor {
            bail!("bound {} < width_floor({:?}) {}", bound, kind, width_floor);
        }

        // Soundness bound (no `.4S` overflow for one array pass). Independent
        // of the accumulator count: each `.4S` lane partial is bounded by the
        // WHOLE-array sum, which must fit `i32`.
        let max_bound = match kind {
            TermKind::Popcount => MAX_BOUND_POP,
            TermKind::ByteSum => MAX_BOUND_SUM,
            // All 0/1-per-byte kinds: the whole-array count is `<= N` and each
            // `.4S` lane partial `<= N`, so `N < 2^31` keeps every lane exact.
            TermKind::PredCountEqZero
            | TermKind::PredMaskCmp { .. }
            | TermKind::PredStencilCmp { .. } => MAX_BOUND_COUNT,
            // Each `.4S` lane partial is bounded by the WHOLE-array sum of the
            // per-byte value `P'_b <= 204`, so `204 * N < 2^31` keeps every lane
            // exact (no `.4S` overflow before the u64 fold).
            TermKind::HexNibbleSum => MAX_BOUND_HEX,
        };
        if bound >= max_bound {
            bail!("bound {} >= overflow-safe max {}", bound, max_bound);
        }

        // `base` must be loop-invariant. The address walk may hand back an
        // IN-LOOP COPY of the invariant pointer (the bridge's chain shape copies
        // the base through the latch: `x50 = MovR(x49 = MovR(x0))`); resolve it
        // to the invariant ROOT through SINGLE-DEF copies only (each strip step
        // is value-exact because the vreg has exactly one live def), and require
        // the root's def to sit OUTSIDE the loop and dominate the preheader.
        let Some(base) = resolve_invariant_base(func, &def, &loop_insts, dom, preheader, base)
        else {
            bail!("base not loop-invariant");
        };

        if dump {
            eprintln!(
                "[neon-bytesum] RECOGNIZED@{} iv={:?} acc={:?} bound={} base={:?} kind={:?} u32={}",
                func.name, iv, acc, bound, base, kind, acc_is_u32
            );
        }
        Some(Recognized {
            header,
            preheader,
            preheader_term,
            iv,
            acc,
            bound,
            base,
            kind,
            acc_is_u32,
        })
    }
}

/// SOUNDNESS GATE for the straight-reduction path: prove the loop body is a
/// SIMPLE `header -> ... -> latch` chain in which EVERY non-latch block is either
///
///   * an `iv <u N` bounds/continue guard DIAMOND — two successors, exactly one
///     in the loop body (the guarded continue, taken when `iv <u N`) and one out
///     (the loop exit / bounds panic) — controlled by an `iv`-copy-vs-constant-`N`
///     compare, in the direct (`CmpRR; BCond(LO); B`) OR the CSet-materialized
///     (`CmpRR; CSet(LO); CmpRI(_,0); BCond(NE); B`) form; or
///   * a PASS-THROUGH block (single in-body successor; its `a[iv]` bounds check
///     was elided or is a `TrapBoundsCheckExact` carrier validated by the caller's
///     single-`N` scan).
///
/// All diamonds must agree on ONE constant `N`, each compared against a copy of
/// the induction `iv`, and the walk must cover EVERY body block exactly once,
/// ending at the latch. This proves the ONLY way control leaves the loop is
/// `iv >= N` (never a data value): so the additively-inserted vector loop, which
/// reduces the whole in-bounds `[0,V) ⊆ [0,N)` prefix, cannot diverge from a
/// scalar loop that would have exited early on some data condition. Returns the
/// bound `N`, or `None` (fail-closed) on ANY deviation — e.g. a data-controlled
/// branch (`break`), a `Cbz`/`Cbnz` predicate, or a block off the chain.
///
/// Mirrors the systemic forward-chain recognizers of `neon_map` / `neon_array` /
/// `neon_minmax`; the caller retains its independent single-`N` / iv-index scan
/// over every `CmpRR`/`TrapBoundsCheckExact`, so the two checks are belt-and-
/// suspenders.
///
/// `countif_diamond`: for the `PredCountEqZero` path only, the ALREADY-VALIDATED
/// conditional-increment diamond `(head, [arm0, arm1])` (its exact shape — head
/// succs are exactly the two arms, each arm single-pred/single-succ joining at
/// the latch — was proven by `try_predcount_diamond`). The walk skips it as a
/// unit: head -> {arms} -> latch. `None` for the straight reduction, where any
/// in-body 2-succ block that is not an `iv <u N` guard must BAIL.
fn recognize_forward_chain(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    header: BlockId,
    latch: BlockId,
    body: &HashSet<BlockId>,
    iv: VReg,
    countif_diamond: Option<(BlockId, [BlockId; 2])>,
) -> Option<i64> {
    let mut bound: Option<i64> = None;
    let mut visited: HashSet<BlockId> = HashSet::new();
    let mut cur = header;
    // Bounded by body.len(): a simple path visits each block at most once.
    for _ in 0..=body.len() {
        if !body.contains(&cur) || !visited.insert(cur) {
            return None;
        }
        if cur == latch {
            break;
        }
        let succs = &func.block(cur).succs;
        let next = if let Some((_, arms)) = countif_diamond.filter(|(dh, _)| *dh == cur) {
            // The validated count-if diamond head: mark both arms visited and
            // continue at their join (the latch). The head appears after the
            // loop-continue guard, so `bound` is already established; if the
            // diamond head were the header itself, `bound` stays `None` and the
            // final check fails (fail-closed).
            for a in arms {
                if !body.contains(&a) || !visited.insert(a) {
                    return None;
                }
            }
            latch
        } else if succs.len() == 2 {
            // Bounds/continue guard diamond: validate iv-index + single-N; the
            // taken edge continues INTO the body, the other LEAVES it. The
            // checked value is either the induction `iv` (the `iv <u N` loop
            // guard) or `iv-1` (the byte-STENCIL count-if's predecessor bounds
            // check `a[iv-1]`) — BOTH induction-derived, so the exit condition is
            // still `induction >= N`, never a data value (no data early-exit).
            let (x, n, t_lo) = recognize_chain_guard(func, def, cur, body)?;
            if !(same_as_iv(func, def, x, iv) || is_iv_minus_one(func, def, x, iv)) {
                return None;
            }
            match bound {
                Some(prev) if prev != n => return None,
                None => bound = Some(n),
                _ => {}
            }
            t_lo
        } else if succs.len() == 1 {
            // Pass-through: the header is never a pass-through (it needs the exit
            // diamond), so `bound` is already established before we reach one.
            if bound.is_none() || !body.contains(&succs[0]) {
                return None;
            }
            succs[0]
        } else {
            return None;
        };
        cur = next;
    }
    if !visited.contains(&latch) || visited.len() != body.len() {
        return None;
    }
    bound
}

/// Decode a block's terminating `iv <u N` guard diamond and return
/// `(iv_copy, N_const, in_body_target)`. Accepts BOTH forms the bridge emits:
///
///   * DIRECT (last 3 insts): `CmpRR(x, Nreg); BCond(LO, t_lo); B(t_b)`.
///   * CSet-MATERIALIZED (last 5): `CmpRR(x, Nreg); CSet(c, LO); CmpRI(c, 0);
///     BCond(NE, t_lo); B(t_b)` — the O2 boolean-materialize idiom (`c = iv <u N`,
///     then branch to the continue when `c != 0`).
///
/// The compare must IMMEDIATELY feed the branch (direct: adjacent; materialized:
/// the `CSet` reads the `CmpRR` flags and the `CmpRI(c,0)` re-tests that boolean),
/// the condition polarity must select the in-body edge when `iv <u N`, `N` must be
/// a compile-time constant, and the two edges must split cleanly in/out of the
/// body. Fail-closed (`None`) on any other terminator — a data-value compare, a
/// `Cbz`/`Cbnz`, a wrong condition code, or a mismatched CSet/CmpRI boolean.
fn recognize_chain_guard(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    blk: BlockId,
    body: &HashSet<BlockId>,
) -> Option<(VReg, i64, BlockId)> {
    let insts = &func.block(blk).insts;
    let n = insts.len();
    if n < 3 {
        return None;
    }
    let last = func.inst(insts[n - 1]);
    let bcond = func.inst(insts[n - 2]);
    if last.opcode != AArch64Opcode::B || bcond.opcode != AArch64Opcode::BCond {
        return None;
    }
    let t_lo = *branch_targets(bcond).first()?;
    let t_b = *branch_targets(last).first()?;
    // Exactly one in-body edge (the guarded continue) and one out.
    if !body.contains(&t_lo) || body.contains(&t_b) {
        return None;
    }
    let bcc = imm_of(&bcond.operands[0])?;
    // Decode an `iv <u N` compare with a compile-time-constant N: register form
    // `CmpRR(x, Nreg)` (N materialized by Movz/Movz+Movk) or the 12-bit
    // immediate form `CmpRI(x, #N)` (N <= 4095 folds to it).
    let const_cmp = |cmp: &MachInst| -> Option<(VReg, i64)> {
        match cmp.opcode {
            AArch64Opcode::CmpRR if cmp.operands.len() == 2 => {
                let x = vreg_of(&cmp.operands[0])?;
                let n_reg = vreg_of(&cmp.operands[1])?;
                Some((x, const_value(func, def, n_reg)?))
            }
            AArch64Opcode::CmpRI if cmp.operands.len() == 2 => {
                Some((vreg_of(&cmp.operands[0])?, imm_of(&cmp.operands[1])?))
            }
            _ => None,
        }
    };
    // DIRECT form: `Cmp{RR,RI}(x, N); BCond(LO, t_lo); B`.
    if bcc == CC_LO
        && let Some((x, nc)) = const_cmp(func.inst(insts[n - 3]))
    {
        return Some((x, nc, t_lo));
    }
    // CSet-MATERIALIZED form: `Cmp{RR,RI}(x, N); CSet(c, LO); CmpRI(c, 0);
    // BCond(NE, t_lo); B`.
    if n >= 5 && bcc == CC_NE {
        let cmpi = func.inst(insts[n - 3]);
        let cset = func.inst(insts[n - 4]);
        if cmpi.opcode == AArch64Opcode::CmpRI
            && cmpi.operands.len() == 2
            && imm_of(&cmpi.operands[1]) == Some(0)
            && cset.opcode == AArch64Opcode::CSet
            && cset.operands.len() == 2
            && imm_of(&cset.operands[1]) == Some(CC_LO)
            && let Some((x, nc)) = const_cmp(func.inst(insts[n - 5]))
        {
            let c = vreg_of(&cset.operands[0])?;
            // The `CmpRI(c, 0)` must re-test the very boolean the CSet produced.
            if vreg_of(&cmpi.operands[0])? != c {
                return None;
            }
            return Some((x, nc, t_lo));
        }
    }
    None
}

/// `v` is the boolean a `CSet` produced (the CSet-materialized guard's
/// condition value).
fn is_cset_result(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> bool {
    def.get(&v.id)
        .is_some_and(|&d| func.inst(d).opcode == AArch64Opcode::CSet)
}

/// The reduction's RESULT vreg (`acc_next = AddRR(acc, term)`), found from the
/// latch writeback `acc = MovR(acc_next)`.
fn reduction_result(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    latch: BlockId,
    acc: VReg,
) -> Option<VReg> {
    for &id in &func.block(latch).insts {
        if let Some((d, s)) = copy_like(func.inst(id))
            && d == acc
        {
            let &sd = def.get(&s.id)?;
            if func.inst(sd).opcode == AArch64Opcode::AddRR {
                return Some(s);
            }
        }
    }
    None
}

/// One arm of the count-if diamond.
enum ArmKind {
    /// `merge = MovR(AddRI(acc, 1))` — the `+1` arm. `add_id` is the `AddRI`
    /// (the instruction that READS `acc`).
    PlusOne { add_id: InstId },
    /// `merge = MovR(acc)` — the `+0` arm. `mov_id` is that `MovR` (which reads
    /// `acc`).
    PlusZero { mov_id: InstId },
}

/// Recognize the branch-based conditional-increment DIAMOND that lowers
/// `while i<N { if a[i]==0 { acc += 1 } }` — the count-if `== 0` shape. The
/// straight `AddRR`-in-latch reduction scan BAILS on it (the acc's latch
/// writeback is a phi-merge of `{acc, acc+1}` realised as writes to a common
/// vreg in both arms, NOT an `AddRR`), so this runs only when that scan found
/// no reduction.
///
/// Returns `(acc, base, diamond_head, arms)` for the recognized `u64`
/// accumulator, the byte-array base pointer, and the diamond's blocks (so the
/// caller's chain walk can skip the validated diamond as a unit). Fails closed
/// (`None`) on ANY deviation. SCOPED to the `== 0` predicate (`CMEQ.16B`): a
/// `!= 0` direction (increment on the non-zero arm), a non-`+1` increment, a
/// non-byte / signed load, or `acc` read off the conditional path all BAIL.
fn recognize_predcount(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    latch: BlockId,
    body: &HashSet<BlockId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    dump: bool,
) -> Option<(VReg, VReg, BlockId, [BlockId; 2])> {
    // Candidate acc writebacks in the latch: `acc = MovR(merge)`, `acc` a
    // `Gpr64` loop-carried var distinct from the iv. Try each; take the first
    // that validates as a `{acc, acc+1}` count-if diamond.
    for &wb in &func.block(latch).insts {
        let Some((acc, merge)) = copy_like(func.inst(wb)) else {
            continue;
        };
        if acc == iv || acc.class != RegClass::Gpr64 || merge == acc {
            continue;
        }
        if let Some((base, dh, arms)) =
            try_predcount_diamond(func, def, latch, body, loop_insts, iv, acc, merge)
        {
            if dump {
                eprintln!(
                    "[neon-bytesum] predcount(==0) diamond OK acc={:?} merge={:?} base={:?}",
                    acc, merge, base
                );
            }
            return Some((acc, base, dh, arms));
        }
    }
    if dump {
        eprintln!("[neon-bytesum] predcount-bail: no count-if(==0) diamond in latch");
    }
    None
}

/// Validate the count-if diamond for a specific latch writeback
/// `acc = MovR(merge)`. Returns the loop-invariant base pointer plus the
/// diamond's `(head, arms)` blocks on success.
#[allow(clippy::too_many_arguments)]
fn try_predcount_diamond(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    latch: BlockId,
    body: &HashSet<BlockId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    acc: VReg,
    merge: VReg,
) -> Option<(VReg, BlockId, [BlockId; 2])> {
    // The two arms: body blocks that (a) define `merge` and (b) branch STRAIGHT
    // to the latch (the join). There must be exactly two.
    let mut arms: Vec<BlockId> = Vec::new();
    for &b in body {
        let succs = &func.block(b).succs;
        if !(succs.len() == 1 && succs[0] == latch) {
            continue;
        }
        let defines_merge = func.block(b).insts.iter().any(|&id| {
            let inst = func.inst(id);
            produces_def(inst.opcode) && inst.operands.first().and_then(vreg_of) == Some(merge)
        });
        if defines_merge {
            arms.push(b);
        }
    }
    if arms.len() != 2 {
        return None;
    }

    // Both arms share ONE common predecessor (the diamond head), and each has
    // exactly that single predecessor — so reaching an arm implies its branch
    // edge was the one taken.
    let dh = {
        let p0 = &func.block(arms[0]).preds;
        let p1 = &func.block(arms[1]).preds;
        if p0.len() != 1 || p1.len() != 1 || p0[0] != p1[0] {
            return None;
        }
        p0[0]
    };
    if !body.contains(&dh) {
        return None;
    }
    // The diamond head's successors are EXACTLY the two arms.
    {
        let mut s = func.block(dh).succs.clone();
        s.sort_by_key(|b| b.0);
        s.dedup();
        let mut a = arms.clone();
        a.sort_by_key(|b| b.0);
        if s != a {
            return None;
        }
    }

    // Classify each arm as `+1` (`merge = MovR(AddRI(acc, 1))`) or `+0`
    // (`merge = MovR(acc)`). Require exactly one of each, and collect the two
    // instructions that READ `acc` (the `AddRI` and the `+0` `MovR`).
    let mut inc_arm: Option<BlockId> = None;
    let mut have_zero_arm = false;
    let mut acc_readers: Vec<InstId> = Vec::new();
    for &b in &arms {
        match classify_predcount_arm(func, def, b, merge, acc)? {
            ArmKind::PlusOne { add_id } => {
                if inc_arm.is_some() {
                    return None;
                }
                inc_arm = Some(b);
                acc_readers.push(add_id);
            }
            ArmKind::PlusZero { mov_id } => {
                if have_zero_arm {
                    return None;
                }
                have_zero_arm = true;
                acc_readers.push(mov_id);
            }
        }
    }
    let inc_arm = inc_arm?;
    if !have_zero_arm {
        return None;
    }

    // The diamond head's controlling branch: `Cbz`/`Cbnz w, T` (+ fallthrough
    // `B F`). Extract `w` and which arm is entered when the byte `== 0`.
    let (cond_val, byte_zero_arm) = predcount_branch_zero_arm(func, dh, &arms)?;

    // SCOPE to `== 0` (CMEQ.16B): the `+1` must happen EXACTLY on the byte-zero
    // arm. `!= 0` (increment on the non-zero arm) BAILS.
    if inc_arm != byte_zero_arm {
        return None;
    }

    // `w` must be a byte load `a[iv]` (peels `Uxtb`/`Uxtw`; a signed `Sxtb`
    // load or a wider load fails here); base returned for the invariance check.
    let base = byte_load_base(func, def, loop_insts, iv, cond_val)?;

    // `acc` may be READ only along the conditional-increment path (the `+1`
    // `AddRI` and the `+0` `MovR`). Any other in-loop read means pre-seeding
    // `acc` with the vector partial would perturb a side computation -> BAIL.
    for &id in loop_insts {
        if acc_readers.contains(&id) {
            continue;
        }
        let inst = func.inst(id);
        // Operand 0 is a written def for producers; compares/branches read it.
        let skip = usize::from(produces_def(inst.opcode));
        for opd in inst.operands.iter().skip(skip) {
            if vreg_of(opd) == Some(acc) {
                return None;
            }
        }
    }

    Some((base, dh, [arms[0], arms[1]]))
}

/// Classify one diamond arm: it must contain exactly one def of `merge`, a
/// `MovR`/`Copy`, whose source is either `acc` (the `+0` arm) or an
/// `AddRI(acc, 1)` (the `+1` arm). Returns which, plus the acc-reading inst.
fn classify_predcount_arm(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    arm: BlockId,
    merge: VReg,
    acc: VReg,
) -> Option<ArmKind> {
    // The (unique) def of `merge` in this arm.
    let mut mdef: Option<InstId> = None;
    for &id in &func.block(arm).insts {
        let inst = func.inst(id);
        if produces_def(inst.opcode) && inst.operands.first().and_then(vreg_of) == Some(merge) {
            if mdef.is_some() {
                return None; // merge defined twice in one arm
            }
            mdef = Some(id);
        }
    }
    let (d, s) = copy_like(func.inst(mdef?))?; // merge = MovR(s)
    if d != merge {
        return None;
    }
    // `+0` arm: merge = MovR(acc).
    if s == acc {
        return Some(ArmKind::PlusZero { mov_id: mdef? });
    }
    // `+1` arm: s = AddRI(acc, 1).
    let &sd = def.get(&s.id)?;
    let si = func.inst(sd);
    if si.opcode == AArch64Opcode::AddRI
        && si.operands.len() == 3
        && vreg_of(&si.operands[1]) == Some(acc)
        && imm_of(&si.operands[2]) == Some(1)
    {
        return Some(ArmKind::PlusOne { add_id: sd });
    }
    None
}

/// From the diamond head's terminator `Cbz`/`Cbnz w, T` (+ fallthrough `B F`),
/// return `(w, byte_zero_arm)` where `byte_zero_arm` is whichever arm is entered
/// when `w == 0`. Fails closed on any other terminator (e.g. a `CmpRI+BCond`
/// materialised predicate, which this `== 0` scope does not decode).
fn predcount_branch_zero_arm(
    func: &MachFunction,
    dh: BlockId,
    arms: &[BlockId],
) -> Option<(VReg, BlockId)> {
    // Exactly one `Cbz`/`Cbnz` in the diamond head.
    let mut cbr: Option<(bool /* is_cbz */, VReg, BlockId)> = None;
    for &id in &func.block(dh).insts {
        let inst = func.inst(id);
        let is_cbz = inst.opcode == AArch64Opcode::Cbz;
        let is_cbnz = inst.opcode == AArch64Opcode::Cbnz;
        if is_cbz || is_cbnz {
            if cbr.is_some() {
                return None;
            }
            let w = vreg_of(inst.operands.first()?)?;
            let t = branch_targets(inst).into_iter().next()?;
            cbr = Some((is_cbz, w, t));
        }
    }
    let (is_cbz, w, taken) = cbr?;
    if !arms.contains(&taken) {
        return None;
    }
    let other = *arms.iter().find(|&&b| b != taken)?;
    // `Cbz`: enter `taken` when `w == 0`. `Cbnz`: enter `taken` when `w != 0`,
    // so the byte-zero arm is the fallthrough `other`.
    let byte_zero_arm = if is_cbz { taken } else { other };
    Some((w, byte_zero_arm))
}

// ---------------------------------------------------------------------------
// Byte-STENCIL count-if diamond (`a[iv] REL a[iv-1]`, `PredStencilCmp`).
// ---------------------------------------------------------------------------

/// `v` is (a copy of) `iv - 1`: `SubRI(iv, 1)` or `SubRR(iv, one)` (one a
/// materialized constant `1`), resolved through `MovR`/`Copy`.
fn is_iv_minus_one(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg, iv: VReg) -> bool {
    let v = strip_copies(func, def, v);
    let Some(&d) = def.get(&v.id) else {
        return false;
    };
    let inst = func.inst(d);
    match inst.opcode {
        AArch64Opcode::SubRI if inst.operands.len() == 3 => {
            vreg_of(&inst.operands[1]).is_some_and(|a| same_as_iv(func, def, a, iv))
                && imm_of(&inst.operands[2]) == Some(1)
        }
        AArch64Opcode::SubRR if inst.operands.len() == 3 => {
            vreg_of(&inst.operands[1]).is_some_and(|a| same_as_iv(func, def, a, iv))
                && vreg_of(&inst.operands[2]).is_some_and(|b| const_value(func, def, b) == Some(1))
        }
        _ => false,
    }
}

/// True when `v` is (a widened form of) a byte LOAD `LDRB[...]` inside the loop
/// — the stencil diamond compares two of these (`a[iv]` and `a[iv-1]`). Peels
/// `Uxtb`/`Uxtw` and checks the underlying producer is a `LdrbRI`/`LdrbRO`
/// without pinning the index (that is checked separately by
/// `byte_load_base` / `pred_load_base`).
fn is_byte_load_val(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    v: VReg,
) -> bool {
    let mut cur = strip_copies(func, def, v);
    for _ in 0..4 {
        let Some(&d) = def.get(&cur.id) else {
            return false;
        };
        if !loop_insts.contains(&d) {
            return false;
        }
        let inst = func.inst(d);
        match inst.opcode {
            AArch64Opcode::Uxtb | AArch64Opcode::Uxtw | AArch64Opcode::Uxth => {
                match vreg_of(&inst.operands[1]) {
                    Some(s) => cur = strip_copies(func, def, s),
                    None => return false,
                }
            }
            AArch64Opcode::LdrbRI | AArch64Opcode::LdrbRO => return true,
            _ => return false,
        }
    }
    false
}

/// Recognize a byte load `a[iv-1]` at the PREDECESSOR index: `LdrbRI(addr, 0)`
/// (or `LdrbRO`) whose index is `iv-1`. Mirrors `byte_load_base` but requires
/// the index to be `iv-1` (an `is_iv_minus_one` value) rather than `iv`.
/// Returns the base pointer.
fn pred_load_base(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    v: VReg,
) -> Option<VReg> {
    let mut cur = v;
    for _ in 0..3 {
        let &d = def.get(&cur.id)?;
        if !loop_insts.contains(&d) {
            return None;
        }
        let inst = func.inst(d);
        match inst.opcode {
            AArch64Opcode::Uxtb | AArch64Opcode::Uxtw => {
                cur = vreg_of(&inst.operands[1])?;
            }
            AArch64Opcode::LdrbRO if inst.operands.len() == 4 => {
                let base = vreg_of(&inst.operands[1])?;
                let index = vreg_of(&inst.operands[2])?;
                return is_iv_minus_one(func, def, index, iv).then_some(base);
            }
            AArch64Opcode::LdrbRI if inst.operands.len() == 3 => {
                if imm_of(&inst.operands[2]) != Some(0) {
                    return None;
                }
                let addr = vreg_of(&inst.operands[1])?;
                // addr == base + (iv-1): `AddRR(base, iv-1-like)` or
                // `Madd(iv-1-like, 1, base)`.
                let &ad = def.get(&addr.id)?;
                if !loop_insts.contains(&ad) {
                    return None;
                }
                let ai = func.inst(ad);
                return match ai.opcode {
                    AArch64Opcode::AddRR if ai.operands.len() == 3 => {
                        let a = vreg_of(&ai.operands[1])?;
                        let b = vreg_of(&ai.operands[2])?;
                        if is_iv_minus_one(func, def, a, iv) {
                            Some(b)
                        } else if is_iv_minus_one(func, def, b, iv) {
                            Some(a)
                        } else {
                            None
                        }
                    }
                    AArch64Opcode::Madd if ai.operands.len() == 4 => {
                        let f1 = vreg_of(&ai.operands[1])?;
                        let f2 = vreg_of(&ai.operands[2])?;
                        let base = vreg_of(&ai.operands[3])?;
                        let es = |f: VReg| const_value(func, def, f) == Some(1);
                        if (is_iv_minus_one(func, def, f1, iv) && es(f2))
                            || (is_iv_minus_one(func, def, f2, iv) && es(f1))
                        {
                            Some(base)
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
            }
            _ => return None,
        }
    }
    None
}

/// The loop-carried induction's INITIAL value (as set in the preheader). Finds
/// the LAST preheader instruction that defines `iv` and resolves it to a
/// compile-time constant (`Movz`, or a copy of a constant). `None` (fail-closed)
/// if the initial value is not a resolvable constant.
fn loop_init_value(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    preheader: BlockId,
    iv: VReg,
) -> Option<i64> {
    let d = func
        .block(preheader)
        .insts
        .iter()
        .rev()
        .copied()
        .find(|&id| {
            let inst = func.inst(id);
            produces_def(inst.opcode) && inst.operands.first().and_then(vreg_of) == Some(iv)
        })?;
    let inst = func.inst(d);
    match inst.opcode {
        AArch64Opcode::Movz => move_wide_seed(inst, iv),
        AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => {
            const_value(func, def, vreg_of(&inst.operands[1])?)
        }
        AArch64Opcode::AddRI
            if inst.operands.len() == 3 && imm_of(&inst.operands[2]) == Some(0) =>
        {
            const_value(func, def, vreg_of(&inst.operands[1])?)
        }
        _ => None,
    }
}

/// Recognize the byte-STENCIL count-if diamond `while i<N { if a[i] REL a[i-1] {
/// acc += 1 } }` (`REL` in `{==, !=}`), the RLE "count runs" shape. The straight
/// `AddRR` latch scan and the `PredCountEqZero` (`Cbz`/`Cbnz`, single byte)
/// recognizer both BAIL on it (its diamond head is a two-byte `CmpRR + BCond`),
/// so this runs last.
///
/// Returns `(acc, base, ne, diamond_head, arms)`: the `u64` accumulator, the ONE
/// invariant base both loads share, whether the counted relation is `!=`
/// (`ne=true`) or `==` (`ne=false`), and the diamond blocks (so the caller's
/// chain walk skips the diamond as a unit). Fails closed (`None`) on ANY
/// deviation. CRITICAL SOUNDNESS: `iv` MUST start at 1 (verified here) so the
/// FORWARD-window vector loop's first predecessor `a[0]` is in bounds.
#[allow(clippy::too_many_arguments)]
fn recognize_stencil(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    preheader: BlockId,
    latch: BlockId,
    body: &HashSet<BlockId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    dump: bool,
) -> Option<(VReg, VReg, bool, BlockId, [BlockId; 2])> {
    // The induction MUST start at 1: the vector loop reads the predecessor block
    // starting at `base + iv_init - 1`, so `iv_init >= 1` is REQUIRED for `a[0]`
    // (the first predecessor) to be in bounds. Fail-closed unless it is EXACTLY 1
    // (the RLE `let mut j = 1` seed; a `j = 0` start would panic the scalar loop
    // on its first `a[j-1]` and MUST NOT be silently vectorized).
    if loop_init_value(func, def, preheader, iv) != Some(1) {
        if dump {
            eprintln!("[neon-bytesum] stencil-bail: iv does not start at 1");
        }
        return None;
    }
    for &wb in &func.block(latch).insts {
        let Some((acc, merge)) = copy_like(func.inst(wb)) else {
            continue;
        };
        if acc == iv || acc.class != RegClass::Gpr64 || merge == acc {
            continue;
        }
        if let Some((base, ne, dh, arms)) =
            try_stencil_diamond(func, def, latch, body, loop_insts, iv, acc, merge)
        {
            if dump {
                eprintln!(
                    "[neon-bytesum] stencil diamond OK acc={:?} merge={:?} base={:?} ne={}",
                    acc, merge, base, ne
                );
            }
            return Some((acc, base, ne, dh, arms));
        }
    }
    if dump {
        eprintln!("[neon-bytesum] stencil-bail: no byte-stencil diamond in latch");
    }
    None
}

/// Validate the byte-stencil diamond for a specific latch writeback
/// `acc = MovR(merge)`. Same `{acc, acc+1}` two-arm merge shape as
/// `try_predcount_diamond`, but the diamond head is a two-byte compare
/// `CmpRR(a[iv], a[iv-1]); BCond(cc); B(other)` rather than a `Cbz`/`Cbnz` on a
/// single byte. Returns `(base, ne, head, arms)`.
#[allow(clippy::too_many_arguments)]
fn try_stencil_diamond(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    latch: BlockId,
    body: &HashSet<BlockId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    acc: VReg,
    merge: VReg,
) -> Option<(VReg, bool, BlockId, [BlockId; 2])> {
    // --- Arms: body blocks that define `merge` and branch STRAIGHT to the latch
    // (identical shape to try_predcount_diamond).
    let mut arms: Vec<BlockId> = Vec::new();
    for &b in body {
        let succs = &func.block(b).succs;
        if !(succs.len() == 1 && succs[0] == latch) {
            continue;
        }
        let defines_merge = func.block(b).insts.iter().any(|&id| {
            let inst = func.inst(id);
            produces_def(inst.opcode) && inst.operands.first().and_then(vreg_of) == Some(merge)
        });
        if defines_merge {
            arms.push(b);
        }
    }
    if arms.len() != 2 {
        return None;
    }
    let dh = {
        let p0 = &func.block(arms[0]).preds;
        let p1 = &func.block(arms[1]).preds;
        if p0.len() != 1 || p1.len() != 1 || p0[0] != p1[0] {
            return None;
        }
        p0[0]
    };
    if !body.contains(&dh) {
        return None;
    }
    {
        let mut s = func.block(dh).succs.clone();
        s.sort_by_key(|b| b.0);
        s.dedup();
        let mut a = arms.clone();
        a.sort_by_key(|b| b.0);
        if s != a {
            return None;
        }
    }
    // Classify arms into +1 / +0, collecting the acc-reading insts.
    let mut inc_arm: Option<BlockId> = None;
    let mut have_zero_arm = false;
    let mut acc_readers: Vec<InstId> = Vec::new();
    for &b in &arms {
        match classify_predcount_arm(func, def, b, merge, acc)? {
            ArmKind::PlusOne { add_id } => {
                if inc_arm.is_some() {
                    return None;
                }
                inc_arm = Some(b);
                acc_readers.push(add_id);
            }
            ArmKind::PlusZero { mov_id } => {
                if have_zero_arm {
                    return None;
                }
                have_zero_arm = true;
                acc_readers.push(mov_id);
            }
        }
    }
    let inc_arm = inc_arm?;
    if !have_zero_arm {
        return None;
    }

    // --- Diamond-head branch: `CmpRR(x, y); BCond(cc, t); B(f)` with cc in
    // {EQ, NE}; `x`/`y` the two compared bytes. Decode which arm holds the
    // `+1` and the counted relation direction.
    let (byte_a, byte_b, cc, bcond_target, fall_target) = stencil_branch_decode(func, dh, &arms)?;
    // The `+1` fires when the counted relation is TRUE. If the `+1` arm is the
    // BCond target, the relation is `cc`; if it is the fallthrough, it is `!cc`.
    let inc_on_true_cc = inc_arm == bcond_target;
    if inc_arm != bcond_target && inc_arm != fall_target {
        return None;
    }
    // ne = counting `!=`. cc==NE counts `!=` on its taken edge; cc==EQ counts
    // `==`. Flip when the increment is on the fallthrough (the `!cc` edge).
    let ne = match cc {
        CC_NE => inc_on_true_cc,
        CC_EQ => !inc_on_true_cc,
        _ => return None,
    };

    // --- The two compared values must be `a[iv]` and `a[iv-1]` off ONE base.
    let a_is_cur = is_byte_load_val(func, def, loop_insts, byte_a);
    let (cur_val, pred_val) = if a_is_cur {
        (byte_a, byte_b)
    } else {
        (byte_b, byte_a)
    };
    let base_cur = byte_load_base(func, def, loop_insts, iv, cur_val)?;
    let base_pred = pred_load_base(func, def, loop_insts, iv, pred_val)?;
    if base_cur != base_pred {
        return None;
    }

    // `acc` READ only on the conditional-increment path (same as predcount).
    for &id in loop_insts {
        if acc_readers.contains(&id) {
            continue;
        }
        let inst = func.inst(id);
        let skip = usize::from(produces_def(inst.opcode));
        for opd in inst.operands.iter().skip(skip) {
            if vreg_of(opd) == Some(acc) {
                return None;
            }
        }
    }

    Some((base_cur, ne, dh, [arms[0], arms[1]]))
}

/// From the stencil diamond head's terminator `CmpRR(x, y); BCond(cc, t); B(f)`,
/// return `(x, y, cc, t, f)`. Fails closed on any other terminator (the
/// `Cbz`/`Cbnz` and CSet-materialized shapes are not this scope).
fn stencil_branch_decode(
    func: &MachFunction,
    dh: BlockId,
    arms: &[BlockId],
) -> Option<(VReg, VReg, i64, BlockId, BlockId)> {
    let insts = &func.block(dh).insts;
    let n = insts.len();
    if n < 3 {
        return None;
    }
    let last = func.inst(insts[n - 1]);
    let bcond = func.inst(insts[n - 2]);
    let cmp = func.inst(insts[n - 3]);
    if last.opcode != AArch64Opcode::B
        || bcond.opcode != AArch64Opcode::BCond
        || cmp.opcode != AArch64Opcode::CmpRR
        || cmp.operands.len() != 2
    {
        return None;
    }
    let x = vreg_of(&cmp.operands[0])?;
    let y = vreg_of(&cmp.operands[1])?;
    let cc = imm_of(&bcond.operands[0])?;
    let t = *branch_targets(bcond).first()?;
    let f = *branch_targets(last).first()?;
    // The two edges must be exactly the two arms.
    if !(arms.contains(&t) && arms.contains(&f) && t != f) {
        return None;
    }
    Some((x, y, cc, t, f))
}

// ---------------------------------------------------------------------------
// Hex-digit-code REDUCTION (`s += nib(b>>4) + nib(b&15)`, `HexNibbleSum`).
// ---------------------------------------------------------------------------

/// True when `blk` is an INTERNAL diamond head: exactly two successors, BOTH in
/// the loop body (it routes WITHIN the loop, it cannot exit it). The hex-nibble
/// kernel's `if nibble < 10` constant-select heads are these; a loop-exit guard
/// has exactly one successor out of the body.
fn is_internal_diamond_head(func: &MachFunction, blk: BlockId, body: &HashSet<BlockId>) -> bool {
    let succs = &func.block(blk).succs;
    succs.len() == 2 && succs.iter().all(|s| body.contains(s))
}

/// `a` equals `b` up through `MovR`/`Copy` chains (a general sibling of
/// `same_as_iv`).
fn same_reg(func: &MachFunction, def: &HashMap<u32, InstId>, a: VReg, b: VReg) -> bool {
    strip_copies(func, def, a) == strip_copies(func, def, b)
}

/// A decoded `nib` accumulation term `Uxtw(AddRR(nibble, sel))` where `nibble` is
/// one byte-nibble (`hi = LSR #4` or `lo = AND #15`) of a byte load and `sel` is
/// the branchless constant-select value (`48`/`87`).
struct NibTerm {
    /// True = high nibble (`LSR #4`); false = low nibble (`AND #15`).
    is_hi: bool,
    /// The byte VALUE both nibbles derive from (a `[u8; N]` load).
    byte_src: VReg,
    /// The nibble register (`hi` or `lo`).
    nibble: VReg,
    /// The constant-select output that is added to `nibble` (validated separately
    /// as a `< 10 -> 48`, `>= 10 -> 87` diamond).
    sel: VReg,
}

/// Decode a nibble register: `LsrRI(byte, 4)` (high, `is_hi=true`) or
/// `AndRI(byte, 15)` (low, `is_hi=false`); return `(is_hi, byte_src)`. The shift
/// amount 4 and mask 15 are pinned EXACTLY (any other split BAILS).
fn decode_nibble(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    nibble: VReg,
) -> Option<(bool, VReg)> {
    let nibble = strip_copies(func, def, nibble);
    let &nd = def.get(&nibble.id)?;
    if !loop_insts.contains(&nd) {
        return None;
    }
    let ni = func.inst(nd);
    match ni.opcode {
        AArch64Opcode::LsrRI if ni.operands.len() == 3 && imm_of(&ni.operands[2]) == Some(4) => {
            Some((true, vreg_of(&ni.operands[1])?))
        }
        AArch64Opcode::AndRI if ni.operands.len() == 3 && imm_of(&ni.operands[2]) == Some(15) => {
            Some((false, vreg_of(&ni.operands[1])?))
        }
        _ => None,
    }
}

/// Decode `t = Uxtw(AddRR(nibble, sel))` — the `as u64` widening of a u32 `nib`
/// value `nibble + sel`. `nibble` is `hi`/`lo` (via [`decode_nibble`]); `sel` is
/// the other addend (validated as a constant-select diamond by the caller). Fails
/// closed on any deviation.
fn decode_nib_term(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    t: VReg,
) -> Option<NibTerm> {
    let t = strip_copies(func, def, t);
    let &td = def.get(&t.id)?;
    if !loop_insts.contains(&td) {
        return None;
    }
    let ti = func.inst(td);
    if ti.opcode != AArch64Opcode::Uxtw || ti.operands.len() != 2 {
        return None;
    }
    let g32 = strip_copies(func, def, vreg_of(&ti.operands[1])?);
    let &gd = def.get(&g32.id)?;
    if !loop_insts.contains(&gd) {
        return None;
    }
    let gi = func.inst(gd);
    if gi.opcode != AArch64Opcode::AddRR || gi.operands.len() != 3 {
        return None;
    }
    let a = vreg_of(&gi.operands[1])?;
    let b = vreg_of(&gi.operands[2])?;
    // Either addend order: (nibble, sel) or (sel, nibble).
    for (nibble, sel) in [(a, b), (b, a)] {
        if let Some((is_hi, byte_src)) = decode_nibble(func, def, loop_insts, nibble) {
            return Some(NibTerm {
                is_hi,
                byte_src,
                nibble,
                sel,
            });
        }
    }
    None
}

/// The constant `sel` selects in `arm` (a `MovR`/`Copy` from a materialized
/// constant). Returns `None` if `arm` does not define `sel` exactly once from a
/// constant.
fn arm_select_const(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    arm: BlockId,
    sel: VReg,
) -> Option<i64> {
    let mut cval = None;
    for &id in &func.block(arm).insts {
        let inst = func.inst(id);
        if produces_def(inst.opcode) && inst.operands.first().and_then(vreg_of) == Some(sel) {
            if cval.is_some() {
                return None; // defined twice
            }
            let (d, s) = copy_like(inst)?;
            if d != sel {
                return None;
            }
            cval = Some(const_value(func, def, s)?);
        }
    }
    cval
}

/// Decode the constant-select diamond head `head` (whose two body successors are
/// `a0`/`a1`): the compare `Cmp(x, C)` and which arm is `x < C` (`lt_arm`) vs
/// `x >= C` (`ge_arm`). Handles the DIRECT (`Cmp; BCond(LO/HS); B`) and the
/// CSet-materialized (`Cmp; CSet(cc); CmpRI(_,0); BCond(NE); B`) forms. Returns
/// `(x, C, lt_arm, ge_arm)`; fails closed on anything else.
fn decode_select_head(
    func: &MachFunction,
    head: BlockId,
    a0: BlockId,
    a1: BlockId,
) -> Option<(VReg, i64, BlockId, BlockId)> {
    let insts = &func.block(head).insts;
    let n = insts.len();
    if n < 3 {
        return None;
    }
    let last = func.inst(insts[n - 1]);
    let bcond = func.inst(insts[n - 2]);
    if last.opcode != AArch64Opcode::B || bcond.opcode != AArch64Opcode::BCond {
        return None;
    }
    let taken = *branch_targets(bcond).first()?;
    let fallthru = *branch_targets(last).first()?;
    // The two edges must be EXACTLY the two arms (never an out-of-loop exit).
    if !([a0, a1].contains(&taken) && [a0, a1].contains(&fallthru) && taken != fallthru) {
        return None;
    }
    let bcc = imm_of(&bcond.operands[0])?;
    let const_cmp = |cmp: &MachInst| -> Option<(VReg, i64)> {
        if cmp.opcode == AArch64Opcode::CmpRI && cmp.operands.len() == 2 {
            Some((vreg_of(&cmp.operands[0])?, imm_of(&cmp.operands[1])?))
        } else {
            None
        }
    };
    // `cc` maps the TAKEN edge to a nibble ordering: LO -> `x < C`, HS -> `x >= C`.
    let arms_for = |cc: i64| -> Option<(BlockId, BlockId)> {
        match cc {
            CC_LO => Some((taken, fallthru)),
            CC_HS => Some((fallthru, taken)),
            _ => None,
        }
    };
    // DIRECT form: `Cmp(x, C); BCond(cc, taken); B(fallthru)`.
    if let Some((x, c)) = const_cmp(func.inst(insts[n - 3])) {
        let (lt_arm, ge_arm) = arms_for(bcc)?;
        return Some((x, c, lt_arm, ge_arm));
    }
    // CSet-MATERIALIZED form: `Cmp(x, C); CSet(c, cc0); CmpRI(c, 0); BCond(NE); B`.
    if n >= 5 && bcc == CC_NE {
        let cmpi = func.inst(insts[n - 3]);
        let cset = func.inst(insts[n - 4]);
        if cmpi.opcode == AArch64Opcode::CmpRI
            && cmpi.operands.len() == 2
            && imm_of(&cmpi.operands[1]) == Some(0)
            && cset.opcode == AArch64Opcode::CSet
            && cset.operands.len() == 2
        {
            let c = vreg_of(&cset.operands[0])?;
            if vreg_of(&cmpi.operands[0])? != c {
                return None;
            }
            let cset_cc = imm_of(&cset.operands[1])?;
            if let Some((x, cst)) = const_cmp(func.inst(insts[n - 5])) {
                let (lt_arm, ge_arm) = arms_for(cset_cc)?;
                return Some((x, cst, lt_arm, ge_arm));
            }
        }
    }
    None
}

/// Validate the branchless `nib` constant-select diamond producing `sel`:
/// ```text
///   head:   Cmp(nibble, 10); BCond -> {arm_lt (nibble<10), arm_ge (nibble>=10)}
///   arm_lt: sel = MovR(const 48)
///   arm_ge: sel = MovR(const 87)
/// ```
/// with both arms single-pred (`== head`) / single-succ (a common in-body
/// `merge`), and `head`'s two successors EXACTLY the two arms. Returns
/// `(head, [arm0, arm1], merge)`. Fails closed on ANY deviation (wrong threshold,
/// wrong/opposite constants, reversed polarity, extra defs, arm off the diamond).
fn recognize_select_diamond(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    sel: VReg,
    nibble: VReg,
    body: &HashSet<BlockId>,
) -> Option<(BlockId, [BlockId; 2], BlockId)> {
    // The two arms: body blocks that define `sel` (each exactly once).
    let mut arms: Vec<BlockId> = Vec::new();
    for &b in body {
        let ndefs = func
            .block(b)
            .insts
            .iter()
            .filter(|&&id| {
                let inst = func.inst(id);
                produces_def(inst.opcode) && inst.operands.first().and_then(vreg_of) == Some(sel)
            })
            .count();
        if ndefs > 1 {
            return None;
        }
        if ndefs == 1 {
            arms.push(b);
        }
    }
    if arms.len() != 2 {
        return None;
    }
    // Common single-pred head.
    let head = {
        let p0 = &func.block(arms[0]).preds;
        let p1 = &func.block(arms[1]).preds;
        if p0.len() != 1 || p1.len() != 1 || p0[0] != p1[0] {
            return None;
        }
        p0[0]
    };
    if !body.contains(&head) {
        return None;
    }
    // The head's successors are EXACTLY the two arms.
    {
        let mut s = func.block(head).succs.clone();
        s.sort_by_key(|b| b.0);
        s.dedup();
        let mut a = arms.clone();
        a.sort_by_key(|b| b.0);
        if s != a {
            return None;
        }
    }
    // Both arms single-succ to a common in-body merge.
    let s0 = &func.block(arms[0]).succs;
    let s1 = &func.block(arms[1]).succs;
    if s0.len() != 1 || s1.len() != 1 || s0[0] != s1[0] {
        return None;
    }
    let merge = s0[0];
    if !body.contains(&merge) {
        return None;
    }
    // Decode the head compare + polarity; the compared value must be THIS nibble
    // and the threshold EXACTLY 10.
    let (cmp_x, cmp_c, lt_arm, ge_arm) = decode_select_head(func, head, arms[0], arms[1])?;
    if !same_reg(func, def, cmp_x, nibble) || cmp_c != NIB_THRESHOLD {
        return None;
    }
    // The `< 10` arm selects 48 (`NIB_LO_BASE`); the `>= 10` arm selects 87
    // (`NIB_HI_BASE`). Reversed constants or an inverted map BAIL.
    if arm_select_const(func, def, lt_arm, sel) != Some(NIB_LO_BASE)
        || arm_select_const(func, def, ge_arm, sel) != Some(NIB_HI_BASE)
    {
        return None;
    }
    Some((head, [arms[0], arms[1]], merge))
}

/// NO-EARLY-EXIT soundness gate for the hex-nibble reduction: prove control leaves
/// the loop ONLY via the `iv <u N` header guard, so the additively-inserted vector
/// loop (which reduces the whole in-bounds `[0,V)` prefix) cannot diverge from a
/// scalar loop that might have exited early on a data condition. The walk covers
/// every body block exactly once, treating each validated constant-select diamond
/// as a SKIP-UNIT (`head -> {arm0, arm1} -> merge`) and requiring every other
/// 2-successor block to be an `iv`-vs-`N` guard agreeing on the single bound `N`.
/// Returns `false` (fail-closed) on any deviation (a data `break`, a `Cbz`/`Cbnz`
/// predicate, a block off the chain, a disagreeing bound).
#[derive(Clone, Copy)]
struct HexNibbleLoop<'a> {
    func: &'a MachFunction,
    def: &'a HashMap<u32, InstId>,
    header: BlockId,
    latch: BlockId,
    body: &'a HashSet<BlockId>,
    loop_insts: &'a HashSet<InstId>,
    iv: VReg,
    bound: i64,
}

fn hexnibble_no_early_exit(
    context: HexNibbleLoop<'_>,
    diamonds: &[(BlockId, [BlockId; 2], BlockId)],
) -> bool {
    let HexNibbleLoop {
        func,
        def,
        header,
        latch,
        body,
        iv,
        bound,
        ..
    } = context;
    let mut visited: HashSet<BlockId> = HashSet::new();
    let mut cur = header;
    for _ in 0..=body.len() {
        if !body.contains(&cur) || !visited.insert(cur) {
            return false;
        }
        if cur == latch {
            break;
        }
        if let Some((_, arms, merge)) = diamonds.iter().find(|(h, _, _)| *h == cur) {
            for &a in arms {
                if !body.contains(&a) || !visited.insert(a) {
                    return false;
                }
            }
            cur = *merge;
            continue;
        }
        let succs = func.block(cur).succs.clone();
        if succs.len() == 2 {
            // Must be the `iv <u N` guard (the header). Its bound must equal the
            // single loop bound; the taken edge continues into the body.
            let Some((x, n, t_lo)) = recognize_chain_guard(func, def, cur, body) else {
                return false;
            };
            if !same_as_iv(func, def, x, iv) || n != bound {
                return false;
            }
            cur = t_lo;
        } else if succs.len() == 1 {
            if !body.contains(&succs[0]) {
                return false;
            }
            cur = succs[0];
        } else {
            return false;
        }
    }
    visited.contains(&latch) && visited.len() == body.len()
}

/// Recognize the hex-digit-code REDUCTION `s += nib(b>>4) + nib(b&15)` over a
/// `[u8; N]`, `nib(n) = n + if n < 10 { 48 } else { 87 }`. The latch writeback is
/// `acc = MovR(sum2)` with `sum2 = AddRR(sum1, nibB)`, `sum1 = AddRR(acc, nibA)`
/// (the two chained nibble accumulations). Returns `(acc, base)` on an EXACT
/// match; fails closed (`None`) on ANY deviation. Runs its OWN no-early-exit chain
/// gate internally (the two select diamonds are internal merges, not the single
/// count-if diamond `recognize_forward_chain` handles).
fn recognize_hexnibble(context: HexNibbleLoop<'_>, dump: bool) -> Option<(VReg, VReg)> {
    let HexNibbleLoop {
        func, latch, iv, ..
    } = context;
    for &id in &func.block(latch).insts {
        let Some((acc, s2)) = copy_like(func.inst(id)) else {
            continue;
        };
        // The acc is a `u64` (`s: u64`) latch writeback, distinct from the iv.
        if acc == iv || acc.class != RegClass::Gpr64 {
            continue;
        }
        if let Some(base) = try_hexnibble_acc(context, acc, s2) {
            if dump {
                eprintln!(
                    "[neon-bytesum] HEXNIBBLE@{} acc={:?} base={:?}",
                    func.name, acc, base
                );
            }
            return Some((acc, base));
        }
    }
    None
}

/// Validate the hex-nibble accumulation rooted at `acc = MovR(s2)`. Returns the
/// invariant array `base` on success.
fn try_hexnibble_acc(context: HexNibbleLoop<'_>, acc: VReg, s2: VReg) -> Option<VReg> {
    let HexNibbleLoop {
        func,
        def,
        body,
        loop_insts,
        iv,
        ..
    } = context;
    // s2 = AddRR(p, q): one operand is `sum1 = AddRR(acc, nibA)`, the other `nibB`.
    let s2 = strip_copies(func, def, s2);
    let &s2d = def.get(&s2.id)?;
    if !loop_insts.contains(&s2d) {
        return None;
    }
    let s2i = func.inst(s2d);
    if s2i.opcode != AArch64Opcode::AddRR || s2i.operands.len() != 3 {
        return None;
    }
    let p = vreg_of(&s2i.operands[1])?;
    let q = vreg_of(&s2i.operands[2])?;

    // `sum1 = AddRR(acc, nibA)` — the inner add whose one operand IS the acc.
    // Returns `(nibA, sum1_inst_id)`.
    let decode_sum1 = |v: VReg| -> Option<(VReg, InstId)> {
        let v = strip_copies(func, def, v);
        let &vd = def.get(&v.id)?;
        if !loop_insts.contains(&vd) {
            return None;
        }
        let vi = func.inst(vd);
        if vi.opcode != AArch64Opcode::AddRR || vi.operands.len() != 3 {
            return None;
        }
        let a = vreg_of(&vi.operands[1])?;
        let b = vreg_of(&vi.operands[2])?;
        if same_reg(func, def, a, acc) {
            Some((b, vd))
        } else if same_reg(func, def, b, acc) {
            Some((a, vd))
        } else {
            None
        }
    };
    let (nib_a_reg, nib_b_reg, sum1_id) = if let Some((na, id)) = decode_sum1(p) {
        (na, q, id)
    } else if let Some((na, id)) = decode_sum1(q) {
        (na, p, id)
    } else {
        return None;
    };

    // Decode both nib terms; one must be hi, the other lo, over ONE byte source.
    let na = decode_nib_term(func, def, loop_insts, nib_a_reg)?;
    let nb = decode_nib_term(func, def, loop_insts, nib_b_reg)?;
    if na.is_hi == nb.is_hi {
        return None;
    }
    if !same_reg(func, def, na.byte_src, nb.byte_src) {
        return None;
    }
    // The byte source is a byte load `a[iv]` off ONE (later-invariance-checked) base.
    let base = byte_load_base(func, def, loop_insts, iv, na.byte_src)?;

    // Both branchless `nib` constant-select diamonds, exact shape, DISTINCT.
    let d_a = recognize_select_diamond(func, def, na.sel, na.nibble, body)?;
    let d_b = recognize_select_diamond(func, def, nb.sel, nb.nibble, body)?;
    if d_a.0 == d_b.0 {
        return None;
    }

    // No-early-exit: the ONLY loop exit is the header `iv <u N` guard.
    if !hexnibble_no_early_exit(context, &[d_a, d_b]) {
        return None;
    }

    // `acc` may be READ only by its reduction `sum1 = AddRR(acc, nibA)` (its latch
    // writeback copy reads `sum2`, not `acc`). Any other in-loop read would be
    // perturbed by pre-seeding `acc` with the vector partial -> BAIL.
    for &id in loop_insts {
        if id == sum1_id {
            continue;
        }
        let inst = func.inst(id);
        let skip = usize::from(produces_def(inst.opcode));
        for opd in inst.operands.iter().skip(skip) {
            if vreg_of(opd) == Some(acc) {
                return None;
            }
        }
    }

    Some(base)
}

/// Opcodes permitted anywhere in the loop body. Anything else BAILS.
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR
            | AddRI
            | SubRR
            | SubRI
            | AndRR
            | AndRI
            | OrrRR
            | OrrRI
            | EorRR
            | LsrRI
            | LslRI
            | AsrRI
            | Movz
            | Movk
            | Movn
            | MovR
            | Copy
            | CmpRR
            | CmpRI
            | BCond
            | B
            // The count-if conditional-increment diamond's controlling branch:
            // `Cbz`/`Cbnz` on a byte load, or a materialised `CSet` boolean.
            // All pure (no memory/call effect) — the recognizer is what
            // guarantees the exact `{acc, acc+1}` merge shape.
            | Cbz
            | Cbnz
            | CSet
            | Uxtb
            | Uxth
            | Uxtw
            | Sxtw
            | LdrbRI
            | LdrbRO
            // The array bounds check `a[iv]` lowers to (a) a `CmpRR(iv, len)` +
            // `BCond`->panic pair, or (b) this fused carrier. Both are pure
            // guards: safe inside the loop (the vector loop reads only the
            // in-bounds prefix `iv <u len`, so the guard never traps there).
            | TrapBoundsCheckExact
    )
}

/// Recognize the reduction term as either `popcount(a[i])` (`pop = true`) or a
/// widened byte load `a[i] as u64` (`pop = false`); return `(pop, base)`.
fn recognize_bytesum_term(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    term: VReg,
) -> Option<(bool, VReg)> {
    // Strip the outer `as u64` widening + copies: term = Uxtw(trunc32(inner)).
    let t = strip_copies(func, def, term);
    let inner = match func.inst(*def.get(&t.id)?).opcode {
        // popcount path: Uxtw(trunc32(SWAR64(...))) — trunc32 is a MovR to Gpr32.
        AArch64Opcode::Uxtw => {
            let src = vreg_of(&func.inst(*def.get(&t.id)?).operands[1])?;
            strip_copies(func, def, src)
        }
        _ => t,
    };

    // (a) byte POPCOUNT: `AndRI(SWAR64, 0x7f)` root over a byte load.
    if let Some(masked_in) = detect_ctpop_swar_i64(func, def, inner) {
        // The SWAR input is `byte & 0xFFFFFFFF` (the `as u32`); strip it.
        let byte = strip_u32_mask(func, def, masked_in).unwrap_or(masked_in);
        if let Some(base) = byte_load_base(func, def, loop_insts, iv, byte) {
            return Some((true, base));
        }
    }

    // (b) plain byte SUM: the term IS a (widened) byte load.
    if let Some(base) = byte_load_base(func, def, loop_insts, iv, inner) {
        return Some((false, base));
    }
    None
}

/// True when the `CmpRI` at `id` (in block `blk`) is IMMEDIATELY followed by a
/// `CSet` in the same block — the boolean-materialize idiom `CmpRI(v, CONST);
/// CSet(res, cc)`. Adjacency guarantees no instruction clobbers `NZCV` between
/// the compare and the select, so the `CSet` reads exactly this compare's flags.
fn cmpri_feeds_cset(func: &MachFunction, blk: BlockId, id: InstId) -> bool {
    let insts = &func.block(blk).insts;
    let Some(pos) = insts.iter().position(|&x| x == id) else {
        return false;
    };
    insts
        .get(pos + 1)
        .is_some_and(|&nid| func.inst(nid).opcode == AArch64Opcode::CSet)
}

/// Recognize the reduction term as a masked-byte compare
/// `((a[i] & MASK) OP CONST) as u64` whose boolean is materialized by a `CSet`
/// (`OP` is `==`, `ne=false`, or `!=`, `ne=true`), folded as the STRAIGHT
/// `acc = MovR(AddRR(acc, zext(cset)))` reduction. Returns `(mask, cnst, ne,
/// base)`. Fails closed (`None`) on ANY deviation.
///
/// Chain (each step single-def-resolved through `MovR`/`Copy`):
/// ```text
///   term  = [Uxtw/Uxtb ...] <- CSet(c, cc)         cc in {EQ, NE}
///   CSet's flags  <-  CmpRI(x, CONST)              adjacent, same block
///   x     = [Uxtb ...] <- AndRI(load, MASK)        MASK, CONST in 0..=255
///   load  = a[iv]   (LDRB[base, iv], via byte_load_base)
/// ```
///
/// The UTF-8 code-point-start count `(b & 0xC0) != 0x80` lowers to exactly this
/// (`MASK=0xC0`, `CONST=0x80`, `ne=true`). SOUND: the vector prefix reproduces
/// `(b & MASK) OP CONST` per byte lane with `AND.16B` + `CMEQ.16B` [+ `NOT.16B`]
/// + `AND.16B`-by-ones, all faithfully proven `.16B`-lanewise; the 0/1 per-lane
///   contributions dot-sum into the `.4S` partials, each `<= N < 2^31` (no wrap).
fn recognize_maskcmp_term(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    term: VReg,
) -> Option<(i64, i64, bool, VReg)> {
    // Strip the outer zero-extension chain (`as u64`/`as u32`: Uxtw/Uxtb) and
    // copies down to the CSet.
    let mut t = strip_copies(func, def, term);
    let mut cset_id = None;
    for _ in 0..4 {
        let &d = def.get(&t.id)?;
        if !loop_insts.contains(&d) {
            return None;
        }
        let inst = func.inst(d);
        match inst.opcode {
            AArch64Opcode::Uxtw | AArch64Opcode::Uxtb | AArch64Opcode::Uxth => {
                t = strip_copies(func, def, vreg_of(&inst.operands[1])?);
            }
            AArch64Opcode::CSet if inst.operands.len() == 2 => {
                cset_id = Some(d);
                break;
            }
            _ => return None,
        }
    }
    let cset_id = cset_id?;
    let cset = func.inst(cset_id);
    // `!=` (ne=true) or `==` (ne=false); any other condition BAILS.
    let ne = match imm_of(&cset.operands[1])? {
        CC_NE => true,
        CC_EQ => false,
        _ => return None,
    };

    // The `CSet` reads the flags of a `CmpRI(x, CONST)` that IMMEDIATELY precedes
    // it (flags are not a vreg; adjacency ensures no NZCV clobber between).
    let blk = block_of_inst(func, cset_id)?;
    let insts = &func.block(blk).insts;
    let pos = insts.iter().position(|&x| x == cset_id)?;
    if pos == 0 {
        return None;
    }
    let cmp = func.inst(insts[pos - 1]);
    if cmp.opcode != AArch64Opcode::CmpRI || cmp.operands.len() != 2 {
        return None;
    }
    let cnst = imm_of(&cmp.operands[1])?;
    if !(0..=255).contains(&cnst) {
        return None;
    }

    // `x = [Uxtb/Uxtw ...] <- AndRI(load, MASK)`; peel an optional widening.
    let mut a = strip_copies(func, def, vreg_of(&cmp.operands[0])?);
    let mut and_id = None;
    for _ in 0..3 {
        let &d = def.get(&a.id)?;
        if !loop_insts.contains(&d) {
            return None;
        }
        let inst = func.inst(d);
        match inst.opcode {
            AArch64Opcode::Uxtb | AArch64Opcode::Uxtw | AArch64Opcode::Uxth => {
                a = strip_copies(func, def, vreg_of(&inst.operands[1])?);
            }
            AArch64Opcode::AndRI if inst.operands.len() == 3 => {
                and_id = Some(d);
                break;
            }
            _ => return None,
        }
    }
    let and = func.inst(and_id?);
    let mask = imm_of(&and.operands[2])?;
    if !(0..=255).contains(&mask) {
        return None;
    }

    // The masked value is a byte load `a[iv]` at the induction index.
    let base = byte_load_base(func, def, loop_insts, iv, vreg_of(&and.operands[1])?)?;
    Some((mask, cnst, ne, base))
}

/// `v == byte & 0xFFFFFFFF` (`AndRR` with a materialized `0xFFFFFFFF`, or
/// `AndRI(_, 0xFFFFFFFF)`) -> the pre-mask value. The mask is a no-op on a byte.
fn strip_u32_mask(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<VReg> {
    let inst = func.inst(*def.get(&v.id)?);
    match inst.opcode {
        AArch64Opcode::AndRI if imm_of(&inst.operands[2]) == Some(MASK32) => {
            vreg_of(&inst.operands[1])
        }
        AArch64Opcode::AndRR => {
            let a = vreg_of(&inst.operands[1])?;
            let b = vreg_of(&inst.operands[2])?;
            if const_value(func, def, b) == Some(MASK32) {
                Some(a)
            } else if const_value(func, def, a) == Some(MASK32) {
                Some(b)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Recognize a byte load `a[iv]`: `LdrbRO(base, index, _)` (register offset,
/// the neon-time form) or `LdrbRI(Madd/Add(base, iv), 0)`. The value may be a
/// `Gpr64` (LdrbRO zero-extends) or a `Gpr32` (LdrbRI) possibly re-extended via
/// `Uxtb`/`Uxtw`. Requires `index == iv` and returns the base.
fn byte_load_base(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    v: VReg,
) -> Option<VReg> {
    // Peel `Uxtb`/`Uxtw` extensions over the raw byte load.
    let mut cur = v;
    for _ in 0..3 {
        let &d = def.get(&cur.id)?;
        if !loop_insts.contains(&d) {
            return None;
        }
        let inst = func.inst(d);
        match inst.opcode {
            AArch64Opcode::Uxtb | AArch64Opcode::Uxtw => {
                cur = vreg_of(&inst.operands[1])?;
            }
            AArch64Opcode::LdrbRO if inst.operands.len() == 4 => {
                let base = vreg_of(&inst.operands[1])?;
                let index = vreg_of(&inst.operands[2])?;
                return same_as_iv(func, def, index, iv).then_some(base);
            }
            AArch64Opcode::LdrbRI if inst.operands.len() == 3 => {
                if imm_of(&inst.operands[2]) != Some(0) {
                    return None;
                }
                let addr = vreg_of(&inst.operands[1])?;
                return ldrb_addr_base(func, def, loop_insts, iv, addr);
            }
            _ => return None,
        }
    }
    None
}

/// Resolve `LdrbRI` address `base + iv` (byte stride): `AddRR(base, iv-like)` or
/// `Madd(iv-like, 1, base)`.
fn ldrb_addr_base(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    addr: VReg,
) -> Option<VReg> {
    let &ad = def.get(&addr.id)?;
    if !loop_insts.contains(&ad) {
        return None;
    }
    let inst = func.inst(ad);
    match inst.opcode {
        AArch64Opcode::AddRR if inst.operands.len() == 3 => {
            let a = vreg_of(&inst.operands[1])?;
            let b = vreg_of(&inst.operands[2])?;
            if same_as_iv(func, def, a, iv) {
                Some(b)
            } else if same_as_iv(func, def, b, iv) {
                Some(a)
            } else {
                None
            }
        }
        AArch64Opcode::Madd if inst.operands.len() == 4 => {
            let f1 = vreg_of(&inst.operands[1])?;
            let f2 = vreg_of(&inst.operands[2])?;
            let base = vreg_of(&inst.operands[3])?;
            let es = |f: VReg| const_value(func, def, f) == Some(1);
            if (same_as_iv(func, def, f1, iv) && es(f2))
                || (same_as_iv(func, def, f2, iv) && es(f1))
            {
                Some(base)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `v` equals `iv` up through `MovR`/`Copy` chains.
fn same_as_iv(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg, iv: VReg) -> bool {
    strip_copies(func, def, v) == strip_copies(func, def, iv)
}

/// Follow `MovR`/`Copy` chains to the underlying value.
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

/// Number of LIVE (attached-to-a-block) defs of `v` in the whole function.
fn count_live_defs(func: &MachFunction, v: VReg) -> usize {
    func.blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .filter(|&id| {
            let inst = func.inst(id);
            produces_def(inst.opcode)
                && matches!(inst.operands.first(), Some(MachOperand::VReg(d)) if d.id == v.id)
        })
        .count()
}

/// Resolve the array-base operand `v` to its LOOP-INVARIANT root, stripping
/// value-preserving copies. SOUND stripping discipline: a copy step is followed
/// ONLY when the copied vreg has exactly ONE live def (so the def map's entry is
/// the def that reaches every use — a multi-def vreg, e.g. a loop-carried phi,
/// stops the walk and fails the invariance requirement instead of resolving
/// through the wrong def). The terminal root must itself be single-def, defined
/// OUTSIDE the loop, in a block dominating the preheader — then its value at the
/// vector preheader equals its value at every scalar `a[iv]` access, and `apply`
/// may materialize `p = root + iv` there. `None` (fail-closed) otherwise.
fn resolve_invariant_base(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    dom: &DomTree,
    preheader: BlockId,
    v: VReg,
) -> Option<VReg> {
    let mut cur = v;
    for _ in 0..16 {
        let &d = def.get(&cur.id)?;
        if count_live_defs(func, cur) != 1 {
            return None;
        }
        if let Some((dst, src)) = copy_like(func.inst(d))
            && dst == cur
            && src != cur
            && loop_insts.contains(&d)
        {
            // An in-loop single-def copy: value-exact forward of `src`.
            cur = src;
            continue;
        }
        // Root candidate: its (single) def must be outside the loop and
        // dominate the preheader.
        if loop_insts.contains(&d) {
            return None;
        }
        let blk = block_of_inst(func, d)?;
        if !dom.dominates(blk, preheader) {
            return None;
        }
        return Some(cur);
    }
    None
}

// ---------------------------------------------------------------------------
// 64-bit SWAR popcount detector (`(x as u32).count_ones() as u64`)
// ---------------------------------------------------------------------------

/// Match the 64-bit SWAR population count and return its INPUT (`t0`, the
/// `x & 0xFFFFFFFF` value). Sibling of `neon_array::detect_ctpop_swar_i32` with
/// 64-bit masks, an extra `>>32` fold level, and a `& 0x7f` final mask.
fn detect_ctpop_swar_i64(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    root: VReg,
) -> Option<VReg> {
    // root = t16 & 0x7f
    let (t16, m) = swar_and_imm(func, def, root)?;
    if m != 0x7f {
        return None;
    }
    // t16 = t14 + (t14 >> 32)
    let t14 = swar_add_self_lsr(func, def, t16, 32)?;
    // t14 = t12 + (t12 >> 16)
    let t12 = swar_add_self_lsr(func, def, t14, 16)?;
    // t12 = t10 + (t10 >> 8)
    let t10 = swar_add_self_lsr(func, def, t12, 8)?;
    // t10 = t9 & 0x0f0f...0f
    let (t9, m) = swar_and_imm(func, def, t10)?;
    if m != M0F {
        return None;
    }
    // t9 = t7 + (t7 >> 4)
    let t7 = swar_add_self_lsr(func, def, t9, 4)?;
    // t7 = (t3 & 0x33..33) + ((t3 >> 2) & 0x33..33)
    let (pa, pb) = swar_add_rr(func, def, t7)?;
    let t3 = swar_pairs(func, def, pa, pb)?;
    // t3 = t0 - ((t0 >> 1) & 0x55..55)
    let (t0, paired) = swar_sub_rr(func, def, t3)?;
    let (t1, m) = swar_and_imm(func, def, paired)?;
    if m != M55 {
        return None;
    }
    let (t0b, sh) = swar_lsr_imm(func, def, t1)?;
    if sh != 1 || t0b != t0 {
        return None;
    }
    Some(t0)
}

fn swar_inst<'a>(
    func: &'a MachFunction,
    def: &HashMap<u32, InstId>,
    v: VReg,
) -> Option<&'a MachInst> {
    Some(func.inst(*def.get(&v.id)?))
}

fn swar_and_imm(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<(VReg, i64)> {
    let inst = swar_inst(func, def, v)?;
    if inst.opcode == AArch64Opcode::AndRI && inst.operands.len() == 3 {
        Some((vreg_of(&inst.operands[1])?, imm_of(&inst.operands[2])?))
    } else {
        None
    }
}

fn swar_add_rr(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<(VReg, VReg)> {
    let inst = swar_inst(func, def, v)?;
    if inst.opcode == AArch64Opcode::AddRR && inst.operands.len() == 3 {
        Some((vreg_of(&inst.operands[1])?, vreg_of(&inst.operands[2])?))
    } else {
        None
    }
}

fn swar_sub_rr(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<(VReg, VReg)> {
    let inst = swar_inst(func, def, v)?;
    if inst.opcode == AArch64Opcode::SubRR && inst.operands.len() == 3 {
        Some((vreg_of(&inst.operands[1])?, vreg_of(&inst.operands[2])?))
    } else {
        None
    }
}

fn swar_lsr_imm(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<(VReg, i64)> {
    let inst = swar_inst(func, def, v)?;
    if inst.opcode == AArch64Opcode::LsrRI && inst.operands.len() == 3 {
        Some((vreg_of(&inst.operands[1])?, imm_of(&inst.operands[2])?))
    } else {
        None
    }
}

/// `v = a + (a >> shift)` -> `a`.
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

/// `(x & 0x33..33) + ((x >> 2) & 0x33..33)` given the two addends -> `x`.
fn swar_pairs(func: &MachFunction, def: &HashMap<u32, InstId>, a: VReg, b: VReg) -> Option<VReg> {
    let try_order = |lo: VReg, hi: VReg| -> Option<VReg> {
        let (x, m_lo) = swar_and_imm(func, def, lo)?;
        if m_lo != M33 {
            return None;
        }
        let (shifted, m_hi) = swar_and_imm(func, def, hi)?;
        if m_hi != M33 {
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

// ---------------------------------------------------------------------------
// Transformation (vector-loop-in-front; mirrors neon_array::apply_widen's
// popcount path, folding into a Gpr64 accumulator).
// ---------------------------------------------------------------------------

/// The four hoisted byte-broadcast constants the hex-nibble kernel needs.
struct HexConsts {
    /// `MOVI #0x0F` — the low-nibble isolate mask (`AND.16B` -> `b & 15`).
    v_lomask: VReg,
    /// `MOVI #10` — the hex-letter threshold comparand (`CMHS.16B` -> `nibble >= 10`).
    v_thresh: VReg,
    /// `MOVI #39` — the hex-letter contribution `87-48` (`AND.16B` with the mask
    /// gives `39` where a nibble `>= 10`, else `0`).
    v_delta: VReg,
    /// `MOVI #96` — the per-byte ASCII base `48*2`, dot-summed as a constant stream.
    v_const: VReg,
}

/// Emit the hex-nibble per-block prefix + FIVE accumulate UDOTs into `vacc`:
/// ```text
///   hi = USHR.16B(q, #4)              lo  = AND.16B(q, #15)
///   ch = AND.16B(CMHS.16B(hi,#10),#39)  cl = AND.16B(CMHS.16B(lo,#10),#39)
///   vacc += UDOT(hi) + UDOT(lo) + UDOT(ch) + UDOT(cl) + UDOT(#96)   (by ones)
/// ```
/// so each `.4S` lane accumulates, per byte group,
/// `hi + lo + 96 + 39*[hi>=10] + 39*[lo>=10]` = exactly `nib(hi)+nib(lo)` (the
/// scalar per-byte contribution). Every emitted op is faithfully proven /
/// credited: `USHR.16B #4` (`proof_neon_ushrv_lanewise_16b(4)`), `CMHS.16B`
/// (`proof_neon_cmhsv_lanewise_16b`), `AND.16B`, `UDOT`, `MOVI`.
fn emit_hexnibble_block(
    func: &mut MachFunction,
    vb: BlockId,
    q: VReg,
    vacc: VReg,
    vone: VReg,
    hc: &HexConsts,
) {
    // hi = q >> 4 (per byte lane).
    let hi = alloc(func, RegClass::Fpr128);
    emit(
        func,
        vb,
        AArch64Opcode::NeonUshrVImm,
        vec![vreg(hi), vreg(q), imm(4), imm(ARR_B16)],
    );
    // lo = q & 0x0F (per byte lane).
    let lo = alloc(func, RegClass::Fpr128);
    emit(
        func,
        vb,
        AArch64Opcode::NeonAndV,
        vec![vreg(lo), vreg(q), vreg(hc.v_lomask)],
    );
    // c_x = 39 where nibble >= 10, else 0  (CMHS gives 0xFF/0x00; AND #39 collapses).
    let letter_contrib = |func: &mut MachFunction, nibble: VReg| -> VReg {
        let mask = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonCmhsV,
            vec![vreg(mask), vreg(nibble), vreg(hc.v_thresh), imm(ARR_B16)],
        );
        let c = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonAndV,
            vec![vreg(c), vreg(mask), vreg(hc.v_delta)],
        );
        c
    };
    let ch = letter_contrib(func, hi);
    let cl = letter_contrib(func, lo);
    // Dot-sum all five byte streams (each byte * 1) into the .4S accumulator. The
    // accumulate order is irrelevant (integer addition is associative); the sum is
    // `Σ (hi + lo + 39*[hi>=10] + 39*[lo>=10] + 96)` per byte = the scalar term.
    for src in [hi, lo, ch, cl, hc.v_const] {
        emit(
            func,
            vb,
            AArch64Opcode::NeonUdotV,
            vec![vreg(vacc), vreg(src), vreg(vone), imm(ARR_B16)],
        );
    }
}

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    // Per-kind unroll: ByteSum = 8 accumulators / 128B per iteration;
    // Popcount / PredCountEqZero = 4 / 64B (see `unroll`).
    let unroll = unroll(rec.kind);
    let width = width(rec.kind);
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    insert_new_blocks_before(func, rec.header, &[vh, vb, vl, vx]);
    // Internal edges among the fresh blocks only; the preheader redirect is
    // deferred to the COMMIT so a lowering failure cannot break the CFG.
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: `unroll` zeroed `.4S` accumulators.
    let vacc: Vec<VReg> = (0..unroll)
        .map(|_| {
            let a = alloc(func, RegClass::Fpr128);
            emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(a), imm(0)]);
            a
        })
        .collect();

    // The byte-STENCIL count-if reads a 1-block FORWARD look-ahead: each
    // iteration loads `unroll + 1` consecutive 16-byte blocks (the last is the
    // look-ahead for the last compared block's `EXT.16B #1`), and its running
    // pointer starts at `base + iv - 1` (so block `k` = `a[iv-1+16k ..]` and the
    // FORWARD `EXT.16B #1` recovers `a[iv+16k ..]`).
    let is_stencil = matches!(rec.kind, TermKind::PredStencilCmp { .. });

    // main_bound: the vector loop runs while every in-iteration read is `< N`.
    //   * straight/count-if: read `a[iv .. iv+width)`, so `iv <= N - width`,
    //     guard `iv <u N - (width-1)`.
    //   * stencil: read `a[iv-1 .. iv-1 + (unroll+1)*16)` (the look-ahead block's
    //     highest byte is `iv + (unroll+1)*16 - 2`), so
    //     `iv <= N - (unroll+1)*16 + 1`, guard `iv <u N - (unroll+1)*16 + 2`.
    let stencil_bytes = (unroll as i64 + 1) * LANES_PER_Q;
    let main_bound_val = if is_stencil {
        rec.bound - stencil_bytes + 2
    } else {
        rec.bound - (width - 1)
    };
    // `main_bound_val` can be large: the recognizer admits a compile-time bound
    // `N` up to `MAX_BOUND_*` (2^28..2^31 depending on kernel), so the vector
    // trip bound `N - (width-1)` (or the stencil variant) routinely exceeds the
    // 16-bit single-`MOVZ` field for big arrays (e.g. a u8 array of 100_000 ->
    // 99_873 = 0x18621). A single `MOVZ` fails closed at the encoder (#366);
    // materialize the full value via the standard `MOVZ`+`MOVK` wide-immediate
    // chain, which leaves EXACTLY `main_bound_val` in the register.
    let main_bound = materialize_wide_const(func, pre, main_bound_val, RegClass::Gpr64);
    let p = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::AddRR,
        vec![vreg(p), vreg(rec.base), vreg(rec.iv)],
    );
    if is_stencil {
        // p = base + iv - 1 (the predecessor-aligned block base; iv starts at 1,
        // so the first block is `a[0 ..]` — recognize_stencil verified iv_init==1).
        emit_before(
            func,
            pre,
            AArch64Opcode::SubRI,
            vec![vreg(p), vreg(p), imm(1)],
        );
    }

    // An all-`0x01`-byte-lane ones vector, hoisted for EVERY kind: it is the
    // multiplier of the UDOT-by-ones fold (`acc[i] += sum_j zext(b_j) * 1`) and,
    // for the count-if kernel, also the `0xFF -> 0x01` collapse mask. The byte-
    // form `MOVI` the encoder emits (`MOVI Vd.16B, #imm8`) puts `0x01` in EVERY
    // one of the 16 byte lanes (a low-lane-only 1 would undercount). The
    // count-if kernel additionally needs a zero comparand for `CMEQ.16B`
    // (`MOVI #0` is all-zero in every arrangement).
    let vone = {
        let vo = alloc(func, RegClass::Fpr128);
        emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(vo), imm(1)]);
        vo
    };
    let vzero = if rec.kind == TermKind::PredCountEqZero {
        let vz = alloc(func, RegClass::Fpr128);
        emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(vz), imm(0)]);
        Some(vz)
    } else {
        None
    };
    // The masked-compare kernel hoists two byte-broadcast comparand vectors:
    // `vmask` (the `& MASK` isolate) and `vcnst` (the `== CONST` comparand). Both
    // are loop-invariant `MOVI Vd.16B, #imm8` (imm8 in `0..=255`), so they live
    // in the preheader — one materialize each, not per accumulator.
    let (vmask, vcnst) = if let TermKind::PredMaskCmp { mask, cnst, .. } = rec.kind {
        let vm = alloc(func, RegClass::Fpr128);
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonMovi,
            vec![vreg(vm), imm(mask)],
        );
        let vc = alloc(func, RegClass::Fpr128);
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonMovi,
            vec![vreg(vc), imm(cnst)],
        );
        (Some(vm), Some(vc))
    } else {
        (None, None)
    };
    // The hex-nibble kernel hoists four byte-broadcast constants: `#15` (the low
    // nibble mask), `#10` (the hex-letter threshold comparand), `#39` (the
    // hex-letter contribution `87-48`, applied where a nibble `>= 10`), and `#96`
    // (`48*2`, the per-byte ASCII-base constant). Each is a loop-invariant
    // `MOVI Vd.16B, #imm8`.
    let hex = if rec.kind == TermKind::HexNibbleSum {
        let mk = |func: &mut MachFunction, byteval: i64| {
            let v = alloc(func, RegClass::Fpr128);
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonMovi,
                vec![vreg(v), imm(byteval)],
            );
            v
        };
        Some(HexConsts {
            v_lomask: mk(func, 0x0F),
            v_thresh: mk(func, NIB_THRESHOLD),
            v_delta: mk(func, NIB_DELTA),
            v_const: mk(func, HEX_CONST_PER_BYTE),
        })
    } else {
        None
    };

    // --- Vector header: unsigned `iv <u main_bound` => the whole width-byte
    // block `iv .. iv+width-1` is `<u N <= a.len()` (in bounds). Both operands
    // are non-negative and `< 2^63`, so unsigned is exact.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Vector body loads.
    //   * non-stencil: `unroll/2` post-index `LDP Qt1, Qt2, [p], #32` = `unroll`
    //     Q regs = width bytes/iter; the pointer advances width bytes/iter while
    //     the latch advances iv by width, so `p == base + iv` at every header
    //     eval.
    //   * stencil: `(unroll+1)/2` LDPs load `unroll` compared blocks PLUS one
    //     FORWARD look-ahead block (`unroll` is odd, so `unroll + 1` is even and
    //     the last load is itself useful — ZERO waste). The LDPs over-advance the
    //     pointer by `((unroll+1)/2)*32`; a single `SUB p, p, #(over - width)`
    //     realigns it to `p == base + (iv+width) - 1` for the next iteration.
    let (qs, look): (Vec<VReg>, Option<VReg>) = if is_stencil {
        let nblocks = unroll + 1; // unroll compared + 1 look-ahead (even)
        let npairs = nblocks / 2;
        let mut loaded: Vec<VReg> = Vec::with_capacity(nblocks);
        for _pair in 0..npairs {
            let q0 = alloc(func, RegClass::Fpr128);
            let q1 = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vb,
                AArch64Opcode::NeonLdpQPost,
                vec![vreg(q0), vreg(q1), vreg(p), imm(32)],
            );
            loaded.push(q0);
            loaded.push(q1);
        }
        // Realign the over-advanced pointer: advanced `npairs*32`, need `width`.
        let over = npairs as i64 * 32 - width;
        if over > 0 {
            emit(
                func,
                vb,
                AArch64Opcode::SubRI,
                vec![vreg(p), vreg(p), imm(over)],
            );
        }
        let look = loaded.pop(); // the last loaded block is the look-ahead
        (loaded, look)
    } else {
        let mut qs: Vec<VReg> = Vec::with_capacity(unroll);
        for _pair in 0..unroll / 2 {
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
        (qs, None)
    };

    // Per accumulator: a per-kind `.16B` prefix that produces the byte
    // contributions, then the FIXED proven UDOT-by-ones fold. popcount =
    // CNT.16B; plain sum = the raw byte lanes; count-if = CMEQ.16B (0xFF where
    // byte==0) then AND.16B with the 0x01-per-lane mask.
    //
    // `UDOT.4S vacc, src, vone` accumulates, per i32 lane,
    // `acc[i] += sum_{j=0..3} zext32(src.byte[4i+j]) * 1` (the FAITHFULLY-PROVEN
    // `NeonUdotV` D-pair accumulate semantics) — lane-for-lane IDENTICAL to the
    // UADDLP(.16B->.8H) + UADDLP(.8H->.4S) + ADD.4S chain it replaces (zext
    // associativity: both add the exact 4-byte group sum `<= 1020` into lane `i`
    // mod 2^32), in ONE SIMD op per Q instead of three. This is the exact
    // structure LLVM emits for e07's byte sum (4x `udot.4s acc, data, ones`).
    // `NeonUdotV` operand 0 is a TIED def-use (the accumulate READS Vd) — see
    // `has_tied_def_use`.
    for k in 0..unroll {
        // The hex-nibble kernel emits its OWN five-stream prefix + accumulate UDOTs
        // (no single `src`), so it is handled ahead of the single-UDOT kinds.
        if rec.kind == TermKind::HexNibbleSum {
            emit_hexnibble_block(func, vb, qs[k], vacc[k], vone, hex.as_ref().unwrap());
            continue;
        }
        let src = match rec.kind {
            TermKind::Popcount => {
                let cnt = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonCntV,
                    vec![vreg(cnt), vreg(qs[k]), imm(ARR_B16)],
                );
                cnt
            }
            TermKind::ByteSum => qs[k],
            TermKind::PredCountEqZero => {
                // 0xFF in each byte lane where `qs[k].byte == 0`.
                let mask = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonCmeqV,
                    vec![vreg(mask), vreg(qs[k]), vreg(vzero.unwrap()), imm(ARR_B16)],
                );
                // Collapse 0xFF -> 0x01 so each matching byte contributes 1.
                let m1 = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAndV,
                    vec![vreg(m1), vreg(mask), vreg(vone)],
                );
                m1
            }
            TermKind::PredMaskCmp { ne, .. } => {
                // t0 = qs[k] & vmask : isolate `b & MASK` per byte lane.
                let t0 = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAndV,
                    vec![vreg(t0), vreg(qs[k]), vreg(vmask.unwrap())],
                );
                // t1 = CMEQ.16B(t0, vcnst) : 0xFF where `(b & MASK) == CONST`.
                let t1 = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonCmeqV,
                    vec![vreg(t1), vreg(t0), vreg(vcnst.unwrap()), imm(ARR_B16)],
                );
                // For `!=` (ne), invert per byte lane: 0xFF <-> 0x00. NOT.16B is
                // faithfully proven lanewise (proof_neon_notv_lanewise_16b).
                let matched = if ne {
                    let tn = alloc(func, RegClass::Fpr128);
                    emit(func, vb, AArch64Opcode::NeonNotV, vec![vreg(tn), vreg(t1)]);
                    tn
                } else {
                    t1
                };
                // Collapse 0xFF -> 0x01 so each matching byte contributes 1.
                let m1 = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAndV,
                    vec![vreg(m1), vreg(matched), vreg(vone)],
                );
                m1
            }
            TermKind::PredStencilCmp { ne } => {
                // Block `k` = `a[iv-1 + 16k ..]`; the FORWARD neighbor block is
                // block `k+1` (the look-ahead block for the LAST accumulator).
                let nb = if k + 1 < qs.len() {
                    qs[k + 1]
                } else {
                    look.expect("stencil look-ahead block must exist")
                };
                // curStream = EXT.16B(qs[k], nb, #1) = `a[iv + 16k ..]` (slide the
                // block one byte FORWARD, pulling `nb.byte[0]` into lane 15).
                // FAITHFULLY PROVEN (proof_neon_extv_16b(1)). Operand order
                // [Vd, Vn(LOW), Vm(HIGH), imm].
                let cur = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonExtV,
                    vec![vreg(cur), vreg(qs[k]), vreg(nb), imm(1)],
                );
                // 0xFF per lane where `a[iv+16k+m] == a[iv+16k+m-1]` (curStream vs
                // the un-shifted predecessor block qs[k]).
                let eqm = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonCmeqV,
                    vec![vreg(eqm), vreg(cur), vreg(qs[k]), imm(ARR_B16)],
                );
                // For `!=` (ne=true, the RLE "count runs" relation), invert per
                // lane. NOT.16B is faithfully proven lanewise.
                let matched = if ne {
                    let tn = alloc(func, RegClass::Fpr128);
                    emit(func, vb, AArch64Opcode::NeonNotV, vec![vreg(tn), vreg(eqm)]);
                    tn
                } else {
                    eqm
                };
                // Collapse 0xFF -> 0x01 so each matching lane contributes 1.
                let m1 = alloc(func, RegClass::Fpr128);
                emit(
                    func,
                    vb,
                    AArch64Opcode::NeonAndV,
                    vec![vreg(m1), vreg(matched), vreg(vone)],
                );
                m1
            }
            // Handled by the early `emit_hexnibble_block` + `continue` above.
            TermKind::HexNibbleSum => unreachable!("hex-nibble handled before the match"),
        };
        emit(
            func,
            vb,
            AArch64Opcode::NeonUdotV,
            vec![vreg(vacc[k]), vreg(src), vreg(vone), imm(ARR_B16)],
        );
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: advance the scalar induction by width bytes (width is
    // 64 or 128 — well inside AddRI's 12-bit immediate).
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector exit: combine the `.4S` accumulators (balanced adds),
    // horizontally reduce (UMOV each lane), ZERO-EXTEND each i32 lane to u64,
    // and ADD into the Gpr64 acc (never overwrite: preserves the seed).
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
    // 4 lanes -> zero-extend each to u64 -> balanced u64 fold -> into acc.
    let lane64: Vec<VReg> = (0..4)
        .map(|lane| {
            let w = alloc(func, RegClass::Gpr32);
            emit(
                func,
                vx,
                AArch64Opcode::NeonUmovGen,
                vec![vreg(w), vreg(vsum), imm(lane), imm(ELEM_S)],
            );
            let x = alloc(func, RegClass::Gpr64);
            emit(func, vx, AArch64Opcode::Uxtw, vec![vreg(x), vreg(w)]);
            x
        })
        .collect();
    let s01 = alloc(func, RegClass::Gpr64);
    let s23 = alloc(func, RegClass::Gpr64);
    let ssum = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(s01), vreg(lane64[0]), vreg(lane64[1])],
    );
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(s23), vreg(lane64[2]), vreg(lane64[3])],
    );
    emit(
        func,
        vx,
        AArch64Opcode::AddRR,
        vec![vreg(ssum), vreg(s01), vreg(s23)],
    );
    if rec.acc_is_u32 {
        // `u32` acc: TRUNCATE the exact `u64` partial to 32 bits (a `MovR` to a
        // `Gpr32` — the proven trunc idiom), then a 32-bit `AddRR` into the acc.
        // `AddRR` on `Gpr32` operands is add mod 2^32, so `acc = (seed + partial)
        // mod 2^32` — exactly the scalar `u32`-wrapping accumulator (the seed is
        // already in `acc`; this ADDS the vector partial, preserving it). The
        // scalar tail then continues the mod-2^32 fold from here.
        let ssum32 = alloc(func, RegClass::Gpr32);
        emit(
            func,
            vx,
            AArch64Opcode::MovR,
            vec![vreg(ssum32), vreg(ssum)],
        );
        emit(
            func,
            vx,
            AArch64Opcode::AddRR,
            vec![vreg(rec.acc), vreg(rec.acc), vreg(ssum32)],
        );
    } else {
        emit(
            func,
            vx,
            AArch64Opcode::AddRR,
            vec![vreg(rec.acc), vreg(rec.acc), vreg(ssum)],
        );
    }
    emit(func, vx, AArch64Opcode::B, vec![block(rec.header)]);

    // --- COMMIT: splice the fresh blocks in front of the scalar loop.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.header, vh) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.header);
    func.add_edge(rec.preheader, vh);
    func.add_edge(vx, rec.header);
    true
}

// ---------------------------------------------------------------------------
// Small local IR helpers (independent copies, as in the sibling neon_* passes)
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

/// `MovR(d, s)` / `Copy(d, s)` / `AddRI(d, s, 0)` copy idioms -> `(d, s)`.
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

/// 16-bit `Movz` constant, or a `Movz(lo16)`+`Movk(hi16, lsl 16)` pair (e.g.
/// `0xFFFFFFFF`), through copies. The `Movk` writes its dst IN PLACE (tied), so
/// its low 16 bits come from a preceding `Movz` on the SAME vreg in the block.
fn const_value(func: &MachFunction, def: &HashMap<u32, InstId>, val: VReg) -> Option<i64> {
    let v = strip_copies(func, def, val);
    let id = *def.get(&v.id)?;
    let inst = func.inst(id);
    match inst.opcode {
        AArch64Opcode::Movz => move_wide_seed(inst, v),
        AArch64Opcode::Movk => {
            // Replay same-destination move-wide writes through the final MOVK.
            // Invalid shapes, missing seeds, or intervening definitions make
            // the value unknown rather than fabricating a zero base.
            let blk = block_of_inst(func, id)?;
            let insts = &func.block(blk).insts;
            let pos = insts.iter().position(|&i| i == id)?;
            let mut acc: Option<i64> = None;
            for &pid in &insts[..=pos] {
                let pi = func.inst(pid);
                if pi.operands.first().and_then(vreg_of) != Some(v) || !produces_def(pi.opcode) {
                    continue;
                }
                match pi.opcode {
                    AArch64Opcode::Movz => acc = move_wide_seed(pi, v),
                    AArch64Opcode::Movk => {
                        let (halfword, shift) = move_wide_patch(pi, v)?;
                        let old = acc?;
                        let mask = 0xFFFF_i64 << shift;
                        acc = Some((old & !mask) | (halfword << shift));
                    }
                    _ => acc = None,
                }
            }
            acc
        }
        _ => None,
    }
}

fn move_wide_seed(inst: &MachInst, dst: VReg) -> Option<i64> {
    if !matches!(dst.class, RegClass::Gpr32 | RegClass::Gpr64) {
        return None;
    }
    if inst.opcode != AArch64Opcode::Movz
        || !(2..=3).contains(&inst.operands.len())
        || inst.operands.first().and_then(vreg_of) != Some(dst)
        || (inst.operands.len() == 3 && imm_of(&inst.operands[2]) != Some(0))
    {
        return None;
    }
    imm_of(&inst.operands[1]).filter(|imm| (0..=0xFFFF).contains(imm))
}

fn move_wide_patch(inst: &MachInst, dst: VReg) -> Option<(i64, u32)> {
    if !matches!(dst.class, RegClass::Gpr32 | RegClass::Gpr64) {
        return None;
    }
    if inst.opcode != AArch64Opcode::Movk
        || !(2..=3).contains(&inst.operands.len())
        || inst.operands.first().and_then(vreg_of) != Some(dst)
    {
        return None;
    }
    let halfword = imm_of(&inst.operands[1]).filter(|imm| (0..=0xFFFF).contains(imm))?;
    let shift = match inst.operands.get(2) {
        None => 0,
        Some(operand) => imm_of(operand)?,
    };
    let max_shift = if dst.class == RegClass::Gpr32 { 16 } else { 48 };
    if !matches!(shift, 0 | 16 | 32 | 48) || shift > max_shift {
        return None;
    }
    Some((halfword, shift as u32))
}

/// Conservative "operand 0 is a written def" predicate. Compares/branches do not
/// define a register; the guard carriers (`TrapBoundsCheckExact` etc.) take their
/// checked value as operand 0 but do NOT define a fresh vreg — treating them as a
/// def would clobber the real producer in the last-write-wins map (e.g. a
/// `MovR(v, iv)` followed by `Trap(v, v, len)` would map `v` to the trap and
/// break copy-chain stripping). `Cbz`/`Cbnz` likewise TEST operand 0 (the
/// count-if predicate value) rather than defining it — mapping them as a def
/// would shadow the real byte-load producer and break `byte_load_base`. `Movk`
/// DOES define (in place), so last-write-wins correctly picks the `Movk` over
/// its base `Movz`.
fn produces_def(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    !matches!(
        op,
        CmpRR
            | CmpRI
            | BCond
            | B
            | Cbz
            | Cbnz
            | TrapBoundsCheckExact
            | TrapBoundsCheck
            | TrapOverflow
            | TrapOverflowExact
            | TrapNull
            | TrapNullIfZero
            | TrapDivZero
            | TrapDivZeroIfZero
            | TrapShiftRange
            | TrapShiftRangeIfOOB
            // Stores READ their operand 0 (the stored value) — they define no
            // vreg. Mapping one as a def would shadow the stored value's REAL
            // producer in the last-write-wins map and corrupt the copy-chain /
            // same-as-iv walks (e.g. the `StrbRI` of an init loop elsewhere in
            // the function shadowing a value the reduction loop also reads).
            | StrRI
            | StrbRI
            | StrhRI
            | StrRO
            | StpRI
            // Pre/post-index stores also list the stored value first (their
            // base-pointer writeback is an in-place tie, not an operand-0 def).
            // Excluding them under-maps at worst — a `def.get` miss makes every
            // caller bail, the fail-closed direction.
            | StrPreIndex
            | StrPostIndex
            | StpPreIndex
    )
}

/// Def map (`vreg id -> defining InstId`) over instructions still ATTACHED to a
/// block. `func.insts` is an append-only ARENA that also retains instructions a
/// prior pass DETACHED (e.g. the `TrapBoundsCheckExact` carriers
/// `aarch64-bounds-check-elim` strips once a dominating guard subsumes them, or
/// if-converted branch bodies). A stale detached instruction whose operand 0 is
/// a live vreg would otherwise shadow that vreg's REAL in-block def and break
/// `same_as_iv` / `strip_copies` / `const_value` resolution (the exact failure
/// mode fixed in the neon_map/neon_array/neon_minmax forward-chain work).
/// Restricting to live in-block instructions keeps the map to reaching defs.
/// DIAGNOSTIC (default off, `TCG_TIME_BOI=1`): accumulated time and call count,
/// so this helper's share of the pass is measured rather than assumed.
pub(crate) static BYTESUM_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static BYTESUM_CALLS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    if crate::neon_array::boi_timing_enabled() {
        let t = std::time::Instant::now();
        let r = build_def_map_inner(func);
        BYTESUM_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        BYTESUM_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return r;
    }
    build_def_map_inner(func)
}

fn build_def_map_inner(func: &MachFunction) -> HashMap<u32, InstId> {
    let live: HashSet<InstId> = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .collect();
    let mut map = HashMap::new();
    for (idx, inst) in func.insts.iter().enumerate() {
        let id = InstId(idx as u32);
        if live.contains(&id)
            && let Some(MachOperand::VReg(v)) = inst.operands.first()
            && produces_def(inst.opcode)
        {
            map.insert(v.id, id);
        }
    }
    map
}

fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    for (idx, blk) in func.blocks.iter().enumerate() {
        if blk.insts.contains(&target) {
            return Some(BlockId(idx as u32));
        }
    }
    None
}

fn branch_targets(inst: &MachInst) -> Vec<BlockId> {
    inst.operands
        .iter()
        .filter_map(|o| match o {
            MachOperand::Block(b) => Some(*b),
            _ => None,
        })
        .collect()
}

fn rewrite_block_target(inst: &mut MachInst, old: BlockId, new: BlockId) -> bool {
    let mut changed = false;
    for op in inst.operands.iter_mut() {
        if let MachOperand::Block(b) = op
            && *b == old
        {
            *b = new;
            changed = true;
        }
    }
    changed
}

fn remove_cfg_edge(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.block_mut(from).succs.retain(|&b| b != to);
    func.block_mut(to).preds.retain(|&b| b != from);
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

/// Materialize a non-negative constant `k` into a fresh `class` vreg via the
/// standard AArch64 wide-immediate chain: `MOVZ` for the low 16 bits, then one
/// `MOVK Rd, #chunk, LSL #s` for each non-zero higher 16-bit chunk (s ∈ {16,32,
/// 48}).
///
/// A bare `MOVZ` only encodes a 16-bit field, so any `k > 0xFFFF` MUST use this
/// chain — feeding a wider value as a single `MOVZ` fails closed at the encoder
/// (`MovImmTooWide`, #366). `MOVZ` zero-extends (clearing every higher bit) and
/// each `MOVK` overwrites only its own 16-bit lane, so the register holds
/// EXACTLY `k` after the chain (including the high 16-bit halves — the #366
/// soundness point). `k` is a loop trip bound here: always non-negative and
/// within the recognizer's admitted `MAX_BOUND_*` range, so the four 16-bit
/// chunks reconstruct it losslessly.
fn materialize_wide_const(func: &mut MachFunction, pre: InstId, k: i64, class: RegClass) -> VReg {
    debug_assert!(
        k >= 0,
        "wide-const materialization expects a non-negative bound, got {k}"
    );
    let b = alloc(func, class);
    let bits = k as u64;
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(b), imm((bits & 0xFFFF) as i64)],
    );
    for shift in [16u32, 32, 48] {
        let chunk = ((bits >> shift) & 0xFFFF) as i64;
        if chunk != 0 {
            emit_before(
                func,
                pre,
                AArch64Opcode::Movk,
                vec![vreg(b), imm(chunk), imm(i64::from(shift))],
            );
        }
    }
    b
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
