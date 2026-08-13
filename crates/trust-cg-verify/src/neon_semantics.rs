// trust-cg-verify/neon_semantics.rs - AArch64 NEON SIMD instruction semantics
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Encodes AArch64 NEON (Advanced SIMD) instruction semantics as bitvector
// SMT expressions using lane decomposition. Each NEON instruction operates
// on a 64-bit or 128-bit vector register, treating it as multiple lanes of
// smaller elements. The semantic encoding extracts lanes, applies the scalar
// operation per-lane, and reassembles the result.
//
// Reference: ARM Architecture Reference Manual (DDI 0487), Sections C7.2
//   (SIMD and Floating-point Instructions, alphabetical listing)
// Reference: designs/2026-04-13-verification-architecture.md

//! AArch64 NEON SIMD instruction semantics encoded as [`SmtExpr`] formulas.
//!
//! Key principle: NEON integer operations decompose into per-lane scalar
//! operations. A 128-bit `ADD.4S` is semantically equivalent to four
//! independent 32-bit additions. This decomposition is the foundation for
//! verifying NEON lowering rules: we prove each lane independently.
//!
//! The lane decomposition pattern:
//! 1. Extract each lane from operand vectors using `lane_extract`
//! 2. Apply the scalar operation to corresponding lanes
//! 3. Reassemble using `concat_lanes`
//!
//! Bitwise operations (AND, ORR, EOR) operate on the full 128-bit vector
//! without lane decomposition since they are bit-parallel.

use crate::smt::{
    SmtExpr, VectorArrangement, concat_lanes, lane_concat, lane_extract, lane_insert,
    map_lanes_binary, map_lanes_binary_imm, map_lanes_unary,
};

// ---------------------------------------------------------------------------
// NEON integer arithmetic
// ---------------------------------------------------------------------------

/// Encode `ADD.<T> Vd, Vn, Vm` -- NEON vector integer add.
///
/// Semantics: for each lane `i`: `Vd[i] = Vn[i] + Vm[i]` (wrapping).
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S, 2D.
/// Reference: ARM DDI 0487, C7.2.1 ADD (vector).
pub fn encode_neon_add(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    map_lanes_binary(vn, vm, arrangement, |a, b| a.bvadd(b))
}

/// Encode `SUB.<T> Vd, Vn, Vm` -- NEON vector integer subtract.
///
/// Semantics: for each lane `i`: `Vd[i] = Vn[i] - Vm[i]` (wrapping).
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S, 2D.
/// Reference: ARM DDI 0487, C7.2.323 SUB (vector).
pub fn encode_neon_sub(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    map_lanes_binary(vn, vm, arrangement, |a, b| a.bvsub(b))
}

/// Encode `MUL.<T> Vd, Vn, Vm` -- NEON vector integer multiply.
///
/// Semantics: for each lane `i`: `Vd[i] = Vn[i] * Vm[i]` (wrapping, lower bits).
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S.
/// Note: no 2D (64-bit lane) integer multiply in AArch64 NEON.
/// Reference: ARM DDI 0487, C7.2.208 MUL (vector).
pub fn encode_neon_mul(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    debug_assert!(
        arrangement != VectorArrangement::D2,
        "NEON MUL does not support 2D arrangement"
    );
    map_lanes_binary(vn, vm, arrangement, |a, b| a.bvmul(b))
}

/// Encode `NEG.<T> Vd, Vn` -- NEON vector integer negate.
///
/// Semantics: for each lane `i`: `Vd[i] = -Vn[i]` (two's complement).
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S, 2D.
/// Reference: ARM DDI 0487, C7.2.209 NEG (vector).
pub fn encode_neon_neg(arrangement: VectorArrangement, vn: &SmtExpr) -> SmtExpr {
    map_lanes_unary(vn, arrangement, |a| a.bvneg())
}

// ---------------------------------------------------------------------------
// NEON bitwise operations
// ---------------------------------------------------------------------------

/// Encode `AND.16B Vd, Vn, Vm` -- NEON bitwise AND.
///
/// Semantics: `Vd = Vn AND Vm` (full 128-bit bitwise).
/// No lane decomposition needed -- bitwise AND is bit-parallel.
///
/// Only valid for 16B arrangement (operates on full 128-bit register).
/// 8B variant operates on 64-bit (lower half).
/// Reference: ARM DDI 0487, C7.2.9 AND (vector).
pub fn encode_neon_and(vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    vn.clone().bvand(vm.clone())
}

/// Encode `ORR.16B Vd, Vn, Vm` -- NEON bitwise OR.
///
/// Semantics: `Vd = Vn OR Vm` (full 128-bit bitwise).
/// Reference: ARM DDI 0487, C7.2.215 ORR (vector, register).
pub fn encode_neon_orr(vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    vn.clone().bvor(vm.clone())
}

/// Encode `EOR.16B Vd, Vn, Vm` -- NEON bitwise exclusive OR.
///
/// Semantics: `Vd = Vn XOR Vm` (full 128-bit bitwise).
/// Reference: ARM DDI 0487, C7.2.71 EOR (vector).
pub fn encode_neon_eor(vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    vn.clone().bvxor(vm.clone())
}

/// Encode `BIC.16B Vd, Vn, Vm` -- NEON bitwise bit clear (AND NOT).
///
/// Semantics: `Vd = Vn AND NOT(Vm)`.
/// Reference: ARM DDI 0487, C7.2.15 BIC (vector, register).
pub fn encode_neon_bic(vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    // BIC = AND with complement of second operand.
    // Since we don't have a BvNot, we XOR with all-ones then AND.
    let width = vm.bv_width();
    let all_ones = if width <= 64 {
        SmtExpr::bv_const(
            if width >= 64 {
                u64::MAX
            } else {
                (1u64 << width) - 1
            },
            width,
        )
    } else {
        // For > 64-bit widths (e.g., 128-bit NEON), build all-ones via concat.
        let lo = SmtExpr::bv_const(u64::MAX, 64);
        let hi_width = width - 64;
        let hi = SmtExpr::bv_const(
            if hi_width >= 64 {
                u64::MAX
            } else {
                (1u64 << hi_width) - 1
            },
            hi_width,
        );
        hi.concat(lo)
    };
    let not_vm = vm.clone().bvxor(all_ones);
    vn.clone().bvand(not_vm)
}

/// Encode `NOT.16B Vd, Vn` (alias for `MVN`) -- NEON bitwise NOT.
///
/// Semantics: `Vd = NOT(Vn)` (full-width bitwise inversion).
/// Implemented as `bvxor(vn, all_ones)`.
///
/// Only valid for 16B/8B arrangements (bitwise on full register).
/// Reference: ARM DDI 0487, C7.2.210 NOT (vector).
pub fn encode_neon_not(vn: &SmtExpr) -> SmtExpr {
    let width = vn.bv_width();
    let all_ones = if width <= 64 {
        SmtExpr::bv_const(
            if width >= 64 {
                u64::MAX
            } else {
                (1u64 << width) - 1
            },
            width,
        )
    } else {
        let lo = SmtExpr::bv_const(u64::MAX, 64);
        let hi_width = width - 64;
        let hi = SmtExpr::bv_const(
            if hi_width >= 64 {
                u64::MAX
            } else {
                (1u64 << hi_width) - 1
            },
            hi_width,
        );
        hi.concat(lo)
    };
    vn.clone().bvxor(all_ones)
}

/// Encode `DUP Vd.4S, Wn` -- NEON broadcast scalar to all lanes.
///
/// Semantics: for each lane `i`: `Vd[i] = Wn` (zero-extended to lane width).
/// The scalar value is replicated across all lanes.
///
/// Reference: ARM DDI 0487, C7.2.59 DUP (general).
pub fn encode_neon_dup(arrangement: VectorArrangement, scalar: &SmtExpr) -> SmtExpr {
    let n = arrangement.lane_count();
    let lane_bits = arrangement.lane_bits();
    let lane_val = if scalar.bv_width() > lane_bits {
        scalar.clone().extract(lane_bits - 1, 0)
    } else if scalar.bv_width() < lane_bits {
        // Zero-extend
        let pad = SmtExpr::bv_const(0, lane_bits - scalar.bv_width());
        pad.concat(scalar.clone())
    } else {
        scalar.clone()
    };
    let lanes: Vec<SmtExpr> = (0..n).map(|_| lane_val.clone()).collect();
    concat_lanes(&lanes, arrangement)
}

/// Encode `INS Vd.T[idx], Vn.T[0]` -- NEON lane insert.
///
/// Semantics: only lane `idx` of `Vd` is modified; other lanes unchanged.
/// The inserted value comes from `new_lane_val`.
///
/// This is a thin wrapper around `lane_insert()` for documentation.
///
/// Reference: ARM DDI 0487, C7.2.106 INS (element).
pub fn encode_neon_ins(
    vec: &SmtExpr,
    arrangement: VectorArrangement,
    idx: u32,
    new_lane_val: SmtExpr,
) -> SmtExpr {
    lane_insert(vec, arrangement, idx, new_lane_val)
}

/// Encode `INS Vd.<T>[lane], Rn` -- INS (general): a GPR written into ONE
/// selected vector lane, with a TIED destination. Only lane `lane` is written;
/// every other lane is PRESERVED bit-for-bit. The GPR is TRUNCATED to the
/// element width (`.B`/`.H`/`.S` take the low 8/16/32 bits of `Wn`/`Xn`; `.D` is
/// a full 64-bit copy of `Xn`). INS (general) is always Q=1, so `arr` is a
/// 128-bit arrangement.
///
/// This is the exact DUAL of [`encode_neon_umov_general`], which reads a lane out
/// and ZERO-EXTENDS; this writes one in and TRUNCATES. The plain
/// [`encode_neon_ins`] above does NOT model that truncation -- it takes an
/// already-lane-width value -- which is why it cannot serve as the machine side
/// of a faithful GPR-insertion obligation.
///
/// Reference: ARM DDI 0487, C7.2.152 INS (general).
pub fn encode_neon_ins_general(
    vd: &SmtExpr,
    arr: VectorArrangement,
    lane: u32,
    rn: &SmtExpr,
) -> SmtExpr {
    debug_assert_eq!(
        arr.total_bits(),
        128,
        "the emitted INS (general) form is always Q=1"
    );
    let lane_bits = arr.lane_bits();
    let gpr_bits = rn.bv_width();
    debug_assert!(
        gpr_bits >= lane_bits,
        "INS (general): GPR narrower than the target lane"
    );
    let lane_val = if gpr_bits > lane_bits {
        rn.clone().extract(lane_bits - 1, 0)
    } else {
        rn.clone()
    };
    lane_insert(vd, arr, lane, lane_val)
}

/// Encode `CMEQ.<T> Vd, Vn, Vm` -- NEON per-lane equality comparison.
///
/// Semantics: for each lane `i`:
///   `Vd[i] = if Vn[i] == Vm[i] then all_ones else 0`
///
/// The result mask is all-ones (0xFF...F) for matching lanes and all-zeros
/// for non-matching lanes. This is the standard NEON compare behavior.
///
/// Reference: ARM DDI 0487, C7.2.29 CMEQ (register).
pub fn encode_neon_cmeq(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    let all_ones_lane = SmtExpr::bv_const(
        if lane_bits >= 64 {
            u64::MAX
        } else {
            (1u64 << lane_bits) - 1
        },
        lane_bits,
    );
    let zero_lane = SmtExpr::bv_const(0, lane_bits);
    map_lanes_binary(vn, vm, arrangement, |a, b| {
        SmtExpr::ite(a.eq_expr(b), all_ones_lane.clone(), zero_lane.clone())
    })
}

/// Encode `UMAXV Sd, Vn.4S` -- NEON horizontal unsigned maximum.
///
/// Semantics: `Sd = max_u(Vn[0], Vn[1], Vn[2], Vn[3])`.
///
/// The result is the lane-width scalar, not a reassembled vector. For a
/// `CMEQ.4S` mask this is exactly the ay horizontal-any primitive: each lane
/// is either `0xFFFF_FFFF` or `0`, so the unsigned max is all-ones iff any
/// lane matched.
///
/// Reference: ARM DDI 0487, UMAXV (vector).
pub fn encode_neon_umaxv_4s(vn: &SmtExpr) -> SmtExpr {
    encode_neon_umaxv(vn, VectorArrangement::S4)
}

/// Encode `UMAXV <V>d, Vn.<T>` -- NEON horizontal UNSIGNED maximum ACROSS lanes,
/// at an arbitrary arrangement. The result width is `arr.lane_bits()` (the
/// scalar destination's significant bits): `.4S -> Sd` (32), `.8H -> Hd` (16),
/// `.16B -> Bd` (8).
///
/// A LINEAR LEFT FOLD with strict `bvugt` selection, kept bit-identical to the
/// long-standing `.4S` form so the silicon-differential cross-check in
/// `bdefs_differential_bridge_neon.rs` (which pins this against real M-series
/// hardware, with a non-vacuity witness whose max is NOT in lane 0) continues to
/// describe exactly this expression.
///
/// The arrangement parameter exists so the WRONG-ELEMENT-SIZE negative controls
/// can be built by instantiating the same fold at `.16B` / `.8H`.
///
/// Reference: ARM DDI 0487, C7.2.335 UMAXV (vector).
pub fn encode_neon_umaxv(vn: &SmtExpr, arr: VectorArrangement) -> SmtExpr {
    let mut max_lane = lane_extract(vn, arr, 0);
    for idx in 1..arr.lane_count() {
        let lane = lane_extract(vn, arr, idx);
        max_lane = SmtExpr::ite(lane.clone().bvugt(max_lane.clone()), lane, max_lane);
    }
    max_lane
}

/// Encode `CMGT.<T> Vd, Vn, Vm` -- NEON per-lane signed greater-than comparison.
///
/// Semantics: for each lane `i`:
///   `Vd[i] = if Vn[i] >s Vm[i] then all_ones else 0`
///
/// The result mask is all-ones (0xFF...F) for matching lanes and all-zeros
/// for non-matching lanes. This is the standard NEON compare behavior.
///
/// Reference: ARM DDI 0487, C7.2.31 CMGT (register).
pub fn encode_neon_cmgt(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    let all_ones_lane = SmtExpr::bv_const(
        if lane_bits >= 64 {
            u64::MAX
        } else {
            (1u64 << lane_bits) - 1
        },
        lane_bits,
    );
    let zero_lane = SmtExpr::bv_const(0, lane_bits);
    map_lanes_binary(vn, vm, arrangement, |a, b| {
        SmtExpr::ite(a.bvsgt(b), all_ones_lane.clone(), zero_lane.clone())
    })
}

/// Encode `CMGE.<T> Vd, Vn, Vm` -- NEON per-lane signed greater-or-equal comparison.
///
/// Semantics: for each lane `i`:
///   `Vd[i] = if Vn[i] >=s Vm[i] then all_ones else 0`
///
/// The result mask is all-ones (0xFF...F) for matching lanes and all-zeros
/// for non-matching lanes. This is the standard NEON compare behavior.
///
/// Reference: ARM DDI 0487, C7.2.30 CMGE (register).
pub fn encode_neon_cmge(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    let all_ones_lane = SmtExpr::bv_const(
        if lane_bits >= 64 {
            u64::MAX
        } else {
            (1u64 << lane_bits) - 1
        },
        lane_bits,
    );
    let zero_lane = SmtExpr::bv_const(0, lane_bits);
    map_lanes_binary(vn, vm, arrangement, |a, b| {
        SmtExpr::ite(a.bvsge(b), all_ones_lane.clone(), zero_lane.clone())
    })
}

/// Encode `CMHI.<T> Vd, Vn, Vm` -- NEON per-lane UNSIGNED greater-than comparison.
///
/// Semantics: for each lane `i`:
///   `Vd[i] = if Vn[i] >u Vm[i] then all_ones else 0`
///
/// The UNSIGNED sibling of [`encode_neon_cmgt`] (`bvugt` vs `bvsgt`). The result
/// mask is all-ones (0xFF...F) for lanes where the unsigned comparison holds and
/// all-zeros otherwise — the standard NEON compare-mask convention.
///
/// Reference: ARM DDI 0487, C7.2.32 CMHI (register).
pub fn encode_neon_cmhi(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    let all_ones_lane = SmtExpr::bv_const(
        if lane_bits >= 64 {
            u64::MAX
        } else {
            (1u64 << lane_bits) - 1
        },
        lane_bits,
    );
    let zero_lane = SmtExpr::bv_const(0, lane_bits);
    map_lanes_binary(vn, vm, arrangement, |a, b| {
        SmtExpr::ite(a.bvugt(b), all_ones_lane.clone(), zero_lane.clone())
    })
}

/// Encode `CMHS.<T> Vd, Vn, Vm` -- NEON per-lane UNSIGNED greater-or-equal compare.
///
/// Semantics: for each lane `i`:
///   `Vd[i] = if Vn[i] >=u Vm[i] then all_ones else 0`
///
/// The UNSIGNED sibling of [`encode_neon_cmge`] (`bvuge` vs `bvsge`). Standard
/// NEON compare-mask convention (all-ones / all-zeros per lane).
///
/// Reference: ARM DDI 0487, C7.2.33 CMHS (register).
pub fn encode_neon_cmhs(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    let all_ones_lane = SmtExpr::bv_const(
        if lane_bits >= 64 {
            u64::MAX
        } else {
            (1u64 << lane_bits) - 1
        },
        lane_bits,
    );
    let zero_lane = SmtExpr::bv_const(0, lane_bits);
    map_lanes_binary(vn, vm, arrangement, |a, b| {
        SmtExpr::ite(a.bvuge(b), all_ones_lane.clone(), zero_lane.clone())
    })
}

// ---------------------------------------------------------------------------
// NEON population count / pairwise widening add (popcount fold)
// ---------------------------------------------------------------------------

/// Per-lane population count as an SMT expression: the number of set bits in a
/// `bits`-wide value, returned at the SAME `bits` width. Built as the sum of the
/// individual extracted bits (`sum_{k<bits} zext((a >> k) & 1))`), each widened
/// to `bits` before adding — the count `0..=bits` never overflows a `bits`-wide
/// lane (for `bits >= 4`; used here with `bits = 8`).
fn popcount_lane(a: &SmtExpr, bits: u32) -> SmtExpr {
    debug_assert!(bits >= 1);
    // bit k, zero-extended to `bits` width.
    let bit = |k: u32| a.clone().extract(k, k).zero_ext(bits - 1);
    let mut acc = bit(0);
    for k in 1..bits {
        acc = acc.bvadd(bit(k));
    }
    acc
}

/// Encode `CNT.<T> Vd, Vn` -- NEON per-byte population count.
///
/// Semantics: for each byte lane `i`: `Vd[i] = popcount(Vn[i])` (an 8-bit count
/// in `0..=8`). Valid arrangements: 8B, 16B (byte lanes only).
///
/// Reference: ARM DDI 0487, C7.2.34 CNT.
pub fn encode_neon_cnt(arrangement: VectorArrangement, vn: &SmtExpr) -> SmtExpr {
    debug_assert!(
        arrangement.lane_bits() == 8,
        "NEON CNT operates on byte lanes only (8B/16B)"
    );
    map_lanes_unary(vn, arrangement, |a| popcount_lane(&a, 8))
}

/// Encode `UADDLP Vd.Ta, Vn.Tb` -- NEON unsigned add long pairwise.
///
/// `in_arr` is the INPUT arrangement `Tb`; each output lane is the sum of two
/// adjacent input lanes, ZERO-EXTENDED to twice the input lane width (so the
/// output is `Ta`, the widened half-lane-count sibling). For `.16B->.8H`:
/// `Vd[k] = zext(Vn[2k], 16) + zext(Vn[2k+1], 16)`; for `.8H->.4S`:
/// `Vd[k] = zext(Vn[2k], 32) + zext(Vn[2k+1], 32)`.
///
/// Reference: ARM DDI 0487, C7.2.351 UADDLP.
pub fn encode_neon_uaddlp(in_arr: VectorArrangement, vn: &SmtExpr) -> SmtExpr {
    let in_bits = in_arr.lane_bits();
    let out_count = in_arr.lane_count() / 2;
    let lanes: Vec<SmtExpr> = (0..out_count)
        .map(|k| {
            let lo = lane_extract(vn, in_arr, 2 * k).zero_ext(in_bits);
            let hi = lane_extract(vn, in_arr, 2 * k + 1).zero_ext(in_bits);
            lo.bvadd(hi)
        })
        .collect();
    lane_concat(&lanes)
}

/// Encode `BIT Vd, Vn, Vm` -- NEON bitwise insert if true (whole register).
///
/// Semantics: `Vd = Vd ^ ((Vd ^ Vn) & Vm)` -- for each BIT position, take
/// `Vn`'s bit where the mask `Vm` is 1 and keep the old `Vd` bit where it is
/// 0. `Vd` is both source and destination (tied def-use).
///
/// Reference: ARM DDI 0487, C7.2.16 BIT.
pub fn encode_neon_bit(vd: &SmtExpr, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    vd.clone()
        .bvxor(vd.clone().bvxor(vn.clone()).bvand(vm.clone()))
}

/// Encode `SADDLP Vd.Ta, Vn.Tb` -- NEON signed add long pairwise.
///
/// The SIGNED sibling of [`encode_neon_uaddlp`]: each output lane is the sum of
/// two adjacent input lanes, SIGN-EXTENDED to twice the input lane width. For
/// `.16B->.8H`: `Vd[k] = sext(Vn[2k], 16) + sext(Vn[2k+1], 16)`; for
/// `.8H->.4S`: `Vd[k] = sext(Vn[2k], 32) + sext(Vn[2k+1], 32)`.
///
/// Reference: ARM DDI 0487, C7.2.252 SADDLP.
pub fn encode_neon_saddlp(in_arr: VectorArrangement, vn: &SmtExpr) -> SmtExpr {
    let in_bits = in_arr.lane_bits();
    let out_count = in_arr.lane_count() / 2;
    let lanes: Vec<SmtExpr> = (0..out_count)
        .map(|k| {
            let lo = lane_extract(vn, in_arr, 2 * k).sign_ext(in_bits);
            let hi = lane_extract(vn, in_arr, 2 * k + 1).sign_ext(in_bits);
            lo.bvadd(hi)
        })
        .collect();
    lane_concat(&lanes)
}

/// Per-lane signed absolute value as an SMT expression: `if a <s 0 then 0 - a
/// else a`, where `0 - a` is the two's-complement negate (so `abs(INT_MIN) ==
/// INT_MIN` by wraparound, matching clang and the SUB+SMAX path this replaces).
/// Returned at the SAME `bits` width.
fn abs_lane(a: &SmtExpr, bits: u32) -> SmtExpr {
    let zero = SmtExpr::bv_const(0, bits);
    SmtExpr::ite(a.clone().bvslt(zero), a.clone().bvneg(), a.clone())
}

/// Encode `ABS.<T> Vd, Vn` -- NEON per-lane signed absolute value.
///
/// Semantics: for each lane `i`: `Vd[i] = if Vn[i] <s 0 then 0 - Vn[i] else Vn[i]`
/// (two's-complement, so `abs(INT_MIN) == INT_MIN`).
///
/// Reference: ARM DDI 0487, C7.2.1 ABS (vector).
pub fn encode_neon_abs(arrangement: VectorArrangement, vn: &SmtExpr) -> SmtExpr {
    let bits = arrangement.lane_bits();
    map_lanes_unary(vn, arrangement, |a| abs_lane(&a, bits))
}

/// Encode `UDOT Vd.4S, Vn.16B, Vm.16B` -- NEON unsigned dot-product ACCUMULATE
/// (FEAT_DotProd).
///
/// Semantics: for each 32-bit lane `i` in 0..3:
/// `Vd'[i] = Vd[i] + sum_{j=0..3}(zext32(Vn.byte[4i+j]) * zext32(Vm.byte[4i+j]))`
/// — `vd` (the PRIOR accumulator value) is an explicit input; the addition is
/// modular (wraps at 2^32, though the 4-product sum itself is at most
/// `4 * 255 * 255 < 2^18` and never carries into the wrap on its own). Each
/// output lane reads ONLY the 4 corresponding byte lanes of `Vn`/`Vm` and the
/// same-numbered word lane of `Vd` — all wholly within one 64-bit D-half.
///
/// `in_arr` is the INPUT arrangement; only the `.16B -> .4S` form the
/// ctpop-reduction lowering emits is modeled.
///
/// Reference: ARM DDI 0487, C7.2.361 UDOT (vector).
pub fn encode_neon_udot(
    in_arr: VectorArrangement,
    vd: &SmtExpr,
    vn: &SmtExpr,
    vm: &SmtExpr,
) -> SmtExpr {
    debug_assert!(
        in_arr == VectorArrangement::B16,
        "NEON UDOT is modeled only for the .16B -> .4S form"
    );
    let out_arr = VectorArrangement::S4;
    let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
        .map(|i| {
            let mut acc = lane_extract(vd, out_arr, i);
            for j in 0..4 {
                let n = lane_extract(vn, in_arr, 4 * i + j).zero_ext(24);
                let m = lane_extract(vm, in_arr, 4 * i + j).zero_ext(24);
                acc = acc.bvadd(n.bvmul(m));
            }
            acc
        })
        .collect();
    lane_concat(&lanes)
}

/// Encode `SMLAL/SMLAL2/UMLAL/UMLAL2 Vd.2D, Vn.<2S|4S>, Vm.<2S|4S>` -- NEON
/// widening multiply-ACCUMULATE-LONG.
///
/// Semantics: for each 64-bit output lane `j` in 0..1, with source `.4S` lane
/// index `base + j` (`base = 0` for the LOW form `high=false`, `base = 2` for the
/// HIGH form `high=true`):
/// `Vd'[j] = Vd[j] + EXT64(Vn.4S[base+j]) * EXT64(Vm.4S[base+j])`
/// where `EXT64 = sign_ext(32)` for the SIGNED (SMLAL) form and `zero_ext(32)`
/// for the UNSIGNED (UMLAL) form. The i32xi32->i64 product is EXACT (no
/// truncation); the accumulate is modular (wraps at 2^64). `vd` (the PRIOR
/// accumulator value) is an explicit input. Each output lane reads ONLY the
/// same-numbered pair of source `.4S` lanes and the same-numbered `.2D` lane of
/// `Vd` — all wholly within one 64-bit D-half of the source (`{0,1}` in `lo`,
/// `{2,3}` in `hi`).
///
/// `in_arr` is the INPUT arrangement; only the `.4S -> .2D` form the neon_array
/// widening dot emits is modeled.
///
/// Reference: ARM DDI 0487, C7.2.267 SMLAL/SMLAL2, C7.2.352 UMLAL/UMLAL2.
pub fn encode_neon_smlal(
    in_arr: VectorArrangement,
    high: bool,
    signed: bool,
    vd: &SmtExpr,
    vn: &SmtExpr,
    vm: &SmtExpr,
) -> SmtExpr {
    debug_assert!(
        in_arr == VectorArrangement::S4,
        "NEON SMLAL is modeled only for the .4S -> .2D form"
    );
    let out_arr = VectorArrangement::D2;
    let base = if high { 2 } else { 0 };
    let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
        .map(|j| {
            let acc = lane_extract(vd, out_arr, j);
            let n = lane_extract(vn, in_arr, base + j);
            let m = lane_extract(vm, in_arr, base + j);
            let (ne, me) = if signed {
                (n.sign_ext(32), m.sign_ext(32))
            } else {
                (n.zero_ext(32), m.zero_ext(32))
            };
            acc.bvadd(ne.bvmul(me))
        })
        .collect();
    lane_concat(&lanes)
}

/// Encode `UADDW/UADDW2 Vd.2D, Vn.2D, Vm.<2S|4S>` -- NEON UNSIGNED widening
/// add-wide.
///
/// Semantics: for each 64-bit output lane `j` in 0..1, with source `.4S` lane
/// index `base + j` (`base = 0` for the LOW form `high=false`, `base = 2` for
/// the HIGH form `high=true`):
/// `Vd[j] = Vn[j] + zext64(Vm.4S[base+j])`
/// -- the i64 addend is the SEPARATE wide source register `Vn` (the ISA's plain
/// three-operand form; `Vd`'s prior value is never read, contrast
/// [`encode_neon_smlal`]). The u32->u64 extension is UNSIGNED (zero-extend);
/// the add is modular (wraps at 2^64). Each output lane reads ONLY the
/// same-numbered `.2D` lane of `Vn` and one source `.4S` lane of `Vm` -- all
/// wholly within one 64-bit D-half of the source (`{0,1}` in `lo`, `{2,3}` in
/// `hi`).
///
/// `in_arr` is the INPUT arrangement; only the `.4S -> .2D` form the neon_array
/// widening abs-sum (TRACK D) emits is modeled.
///
/// Reference: ARM DDI 0487, C7.2.350 UADDW/UADDW2.
pub fn encode_neon_uaddw(
    in_arr: VectorArrangement,
    high: bool,
    vn: &SmtExpr,
    vm: &SmtExpr,
) -> SmtExpr {
    debug_assert!(
        in_arr == VectorArrangement::S4,
        "NEON UADDW is modeled only for the .4S -> .2D form"
    );
    let out_arr = VectorArrangement::D2;
    let base = if high { 2 } else { 0 };
    let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
        .map(|j| {
            let addend = lane_extract(vn, out_arr, j);
            let m = lane_extract(vm, in_arr, base + j);
            addend.bvadd(m.zero_ext(32))
        })
        .collect();
    lane_concat(&lanes)
}

/// Encode `SADDW/SADDW2 Vd.2D, Vn.2D, Vm.<2S|4S>` -- NEON SIGNED widening
/// add-wide, the signed sibling of [`encode_neon_uaddw`].
///
/// Semantics: for each 64-bit output lane `j` in 0..1, with source `.4S` lane
/// index `base + j` (`base = 0` for the LOW form `high=false`, `base = 2` for
/// the HIGH form `high=true`):
/// `Vd[j] = Vn[j] + sext64(Vm.4S[base+j])`
/// -- the i64 addend is the SEPARATE wide source register `Vn` (the ISA's plain
/// three-operand form; `Vd`'s prior value is never read, contrast
/// [`encode_neon_smlal`]). The i32->i64 extension is SIGNED (sign-extend --
/// the ONLY difference from [`encode_neon_uaddw`], and a different function on
/// every source lane with bit 31 set); the add is modular (wraps at 2^64).
/// Each output lane reads ONLY the same-numbered `.2D` lane of `Vn` and one
/// source `.4S` lane of `Vm` -- all wholly within one 64-bit D-half of the
/// source (`{0,1}` in `lo`, `{2,3}` in `hi`).
///
/// `in_arr` is the INPUT arrangement; only the `.4S -> .2D` form the
/// neon_predsum widening i64-acc condsum emits is modeled.
///
/// Reference: ARM DDI 0487, C7.2.207 SADDW/SADDW2.
pub fn encode_neon_saddw(
    in_arr: VectorArrangement,
    high: bool,
    vn: &SmtExpr,
    vm: &SmtExpr,
) -> SmtExpr {
    debug_assert!(
        in_arr == VectorArrangement::S4,
        "NEON SADDW is modeled only for the .4S -> .2D form"
    );
    let out_arr = VectorArrangement::D2;
    let base = if high { 2 } else { 0 };
    let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
        .map(|j| {
            let addend = lane_extract(vn, out_arr, j);
            let m = lane_extract(vm, in_arr, base + j);
            addend.bvadd(m.sign_ext(32))
        })
        .collect();
    lane_concat(&lanes)
}

/// Encode `UADALP Vd.2D, Vn.4S` -- NEON UNSIGNED pairwise widening ACCUMULATE
/// (Add and Accumulate Long Pairwise).
///
/// Semantics: for each 64-bit output lane `j` in 0..1:
/// `Vd[j] = Vd[j] + zext64(Vn.4S[2j]) + zext64(Vn.4S[2j+1])`
/// -- the ACCUMULATING sibling of the non-accumulating UADDLP: the prior value
/// of `Vd` is an explicit addend (a tied def-use, like [`encode_neon_udot`] --
/// contrast [`encode_neon_uaddw`], whose addend is the separate register
/// `Vn`). The u32->u64 extension is UNSIGNED (zero-extend); the adds are
/// modular (wrap at 2^64). Each output lane reads ONLY the same-numbered `.2D`
/// lane of `Vd` and the ADJACENT source `.4S` lane pair `{2j, 2j+1}` of `Vn`
/// -- all wholly within one 64-bit D-half (`{0,1}` in `lo`, `{2,3}` in `hi`).
///
/// `in_arr` is the INPUT arrangement; only the `.4S -> .2D` form the
/// neon_array widening abs-sum (TRACK D) emits is modeled.
///
/// Reference: ARM DDI 0487, C7.2.346 UADALP.
pub fn encode_neon_uadalp(in_arr: VectorArrangement, vd: &SmtExpr, vn: &SmtExpr) -> SmtExpr {
    debug_assert!(
        in_arr == VectorArrangement::S4,
        "NEON UADALP is modeled only for the .4S -> .2D form"
    );
    let out_arr = VectorArrangement::D2;
    let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
        .map(|j| {
            let acc = lane_extract(vd, out_arr, j);
            let p0 = lane_extract(vn, in_arr, 2 * j).zero_ext(32);
            let p1 = lane_extract(vn, in_arr, 2 * j + 1).zero_ext(32);
            acc.bvadd(p0).bvadd(p1)
        })
        .collect();
    lane_concat(&lanes)
}

/// Encode `EXT Vd.16B, Vn.16B, Vm.16B, #imm` -- NEON byte-wise
/// extract/concatenate.
///
/// Semantics: the result is bytes `imm .. imm+15` of the 32-byte concatenation
/// `Vm:Vn` (`Vn` supplies the LOW 16 bytes, `Vm` the HIGH 16 bytes):
/// `Vd.byte[j] = if j+imm < 16 then Vn.byte[j+imm] else Vm.byte[j+imm-16]`.
/// Operand ORDER is load-bearing (EXT is not commutative — swapping `Vn`/`Vm`
/// selects the complementary window). The ARM ARM pseudocode forms the 256-bit
/// `Vpart` concatenation `Vm:Vn` and extracts bits `imm*8 + 127 .. imm*8`;
/// that is expressed here in the equivalent 128-bit form
/// `(Vn >> imm*8) | (Vm << (128 - imm*8))` (for `0 < imm < 16` both shifted
/// operands are disjoint bit ranges, so OR is exact concatenation-extract) —
/// the evaluation backend carries at most 128-bit intermediates, so the
/// literal 256-bit `Concat` is out of reach.
///
/// The emitted byte shifts are the whole-i32-lane shifts `4 / 8 / 12` (the
/// stencil vectorizer's middle-window slides) plus the SINGLE-byte shifts
/// `1` and `15` (the neon-bytesum stencil count-if's shifted-neighbor stream:
/// `#1` slides the window one byte FORWARD to form `a[iv+1]`, `#15` one byte
/// BACKWARD to form `a[iv-1]`). The `(vn >> imm*8) | (vm << (128 - imm*8))`
/// disjoint-OR concatenation-extract is exact for EVERY `0 < imm < 16`.
///
/// Reference: ARM DDI 0487, C7.2.116 EXT.
pub fn encode_neon_ext(imm: u32, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    debug_assert!(
        matches!(imm, 1 | 4 | 8 | 12 | 15),
        "NEON EXT is modeled only for the emitted byte shifts 1/4/8/12/15"
    );
    let sh = imm * 8;
    let lo_part = vn.clone().bvlshr(SmtExpr::bv_const(sh as u64, 128));
    let hi_part = vm.clone().bvshl(SmtExpr::bv_const((128 - sh) as u64, 128));
    lo_part.bvor(hi_part)
}

/// Encode `REV64 Vd.4S, Vn.4S` -- NEON element reverse within each 64-bit
/// doubleword, at the 32-bit-element arrangement.
///
/// Semantics: within EACH 64-bit container, the two 32-bit elements swap
/// places: lanes `[l0, l1, l2, l3]` (l0 = bits 31:0) become
/// `[l1, l0, l3, l2]` -- the complex `{rp, ip}` pair swap the AoS butterfly
/// vectorizer (`neon_butterfly`) emits. The ARM ARM pseudocode moves
/// `Elem[operand, base + (esize_per_container-1) - e]` into
/// `Elem[result, base + e]` per container; for the `.4S` form that is
/// expressed here in the equivalent whole-register shift/mask form
/// `((Vn << 32) & ODD_LANES) | ((Vn >> 32) & EVEN_LANES)` (each output lane
/// receives exactly one input lane; the masked shifted operands cover disjoint
/// bit ranges, so OR is exact) -- structurally INDEPENDENT of the per-lane
/// D-half extraction the faithful proof's SOURCE side uses.
///
/// Reference: ARM DDI 0487, C7.2.219 REV64 (vector).
pub fn encode_neon_rev64_4s(vn: &SmtExpr) -> SmtExpr {
    // 128-bit lane masks, assembled from 64-bit halves (bv_const is u64-wide).
    let even = SmtExpr::bv_const(0x0000_0000_FFFF_FFFF, 64);
    let odd = SmtExpr::bv_const(0xFFFF_FFFF_0000_0000, 64);
    let even_lanes = even.clone().concat(even); // lanes 0 and 2
    let odd_lanes = odd.clone().concat(odd); // lanes 1 and 3
    let sh32 = SmtExpr::bv_const(32, 128);
    let up = vn.clone().bvshl(sh32.clone()).bvand(odd_lanes);
    let down = vn.clone().bvlshr(sh32).bvand(even_lanes);
    up.bvor(down)
}

/// Encode `REV32 Vd.16B, Vn.16B` -- NEON per-WORD BYTE reversal: within EACH of
/// the four 32-bit containers the 4 bytes are reversed in place (output byte
/// `4k+j` == input byte `4k+3-j`); a byte NEVER crosses the 32-bit container
/// boundary, which is REV32's defining property. Emitted (paired with a `RBIT`
/// of the same arrangement) as the `<4 x i32>` `reverse_bits()` lowering: REV32
/// reverses byte ORDER within each i32 lane, RBIT reverses bits within each byte.
///
/// This is EXACTLY [`encode_neon_rev64_16b`] MINUS its third step: REV32 is REV64
/// truncated at the 32-bit container, so the #8 (adjacent bytes) and #16
/// (adjacent halfwords) SWAR butterfly steps are kept and the #32 half-swap that
/// would cross into the 64-bit container is dropped. Each step's word-periodic
/// mask confines every routed byte to its own 32-bit container, by the same
/// argument spelled out on the REV64 model.
///
/// Reference: ARM DDI 0487, C7.2.220 REV32 (vector).
pub fn encode_neon_rev32_16b(vn: &SmtExpr) -> SmtExpr {
    let m8 = SmtExpr::bv_const(0x00FF_00FF_00FF_00FF, 64);
    let m16 = SmtExpr::bv_const(0x0000_FFFF_0000_FFFF, 64);
    let m8 = m8.clone().concat(m8);
    let m16 = m16.clone().concat(m16);
    let sh8 = SmtExpr::bv_const(8, 128);
    let sh16 = SmtExpr::bv_const(16, 128);
    // Step 1: swap adjacent bytes within each 16-bit group.
    let x = vn
        .clone()
        .bvlshr(sh8.clone())
        .bvand(m8.clone())
        .bvor(vn.clone().bvand(m8).bvshl(sh8));
    // Step 2: swap adjacent 16-bit groups within each 32-bit WORD container.
    x.clone()
        .bvlshr(sh16.clone())
        .bvand(m16.clone())
        .bvor(x.bvand(m16).bvshl(sh16))
}

/// Encode `REV32 Vd.8B, Vn.8B` -- the Q=0 (64-bit) form: the two LOW 32-bit
/// containers have their bytes reversed exactly as at `.16B`, and bits [127:64]
/// of the destination are ZEROED, as every AArch64 Q=0 SIMD write does. Emitted
/// by the vectorizer's MIXED-WIDTH bit-reverse path (an `I64` plan whose
/// bit-reverse instruction has `I32` element type takes `lanes = vf`; `vf == 2`
/// selects `NeonArrangement::B8`), and admitted by the encoder
/// (`encode_vec_byte_2reg` maps `B8` to `q=0`). Modeling the upper-half zeroing
/// is the whole point of a SEPARATE `.8B` obligation.
///
/// Reference: ARM DDI 0487, C7.2.220 REV32 (vector).
pub fn encode_neon_rev32_8b(vn: &SmtExpr) -> SmtExpr {
    let low_mask = SmtExpr::bv_const(0, 64).concat(SmtExpr::bv_const(u64::MAX, 64));
    encode_neon_rev32_16b(vn).bvand(low_mask)
}

/// Encode `RBIT Vd.8B, Vn.8B` -- the Q=0 (64-bit) form of the per-byte bit
/// reversal: the 8 bits of each of the LOW 8 bytes are reversed in place, and
/// the upper 64 bits of the destination are ZEROED, as every AArch64 `.8B`
/// (Q=0) SIMD write does. Emitted by the vectorizer's mixed-width bit-reverse
/// path (`vectorize.rs`: `VecElementType::I32` with a 2-lane vectorization
/// factor selects the `B8` byte arrangement), and admitted by the encoder
/// (`encode_vec_byte_2reg` maps `B8` to `q=0`).
///
/// Same within-byte SWAR butterfly as [`encode_neon_rbit_16b`] (bits 1/2/4),
/// then the explicit Q=0 upper-half zeroing. Modeling that zeroing is the whole
/// point of a SEPARATE `.8B` obligation: the `.16B` proof says nothing about
/// what happens to bits 127..64, and a lowering that emitted `.8B` where `.16B`
/// was meant would silently drop the top half.
///
/// Reference: ARM DDI 0487, C7.2.218 RBIT (vector).
pub fn encode_neon_rbit_8b(vn: &SmtExpr) -> SmtExpr {
    let low_mask = SmtExpr::bv_const(0, 64).concat(SmtExpr::bv_const(u64::MAX, 64));
    encode_neon_rbit_16b(vn).bvand(low_mask)
}

/// Encode `REV64 Vd.16B, Vn.16B` -- NEON per-doubleword BYTE reversal: within
/// EACH of the two 64-bit containers, the 8 bytes are reversed in place (output
/// byte `8k+j` == input byte `8k+7-j`); a byte NEVER crosses the 64-bit
/// container boundary, which is REV64's defining property. This is the form the
/// vectorizer emits for a `<2 x i64>` bit-reversal (`RBIT.16B` reverses bits
/// within each byte, this REV64 then reverses the byte ORDER within each i64
/// lane -- together a full per-lane 64-bit `reverse_bits`).
///
/// Modeled as the classic three-step SWAR byte-reversal butterfly applied to
/// both doublewords in parallel via doubleword-periodic masks: swap adjacent
/// bytes (#8), then 16-bit groups (#16), then 32-bit halves (#32). Each step's
/// mask confines every routed byte to its own 64-bit container -- the whole-
/// register RIGHT shift drags the next container's low bytes into the previous
/// container's high bytes, but at every step those destination positions are
/// exactly the bits the step's mask clears (mask top group is zero), and
/// symmetrically the LEFT shift only ever moves bits the mask already cleared
/// across the boundary. So this is an EXACT whole-register model of the ARM ARM
/// per-container element-reverse for the 8-bit container at `.16B` -- and
/// STRUCTURALLY INDEPENDENT of the per-BYTE `Extract`/`Concat` permutation the
/// faithful proof's SOURCE side uses.
///
/// Reference: ARM DDI 0487, C7.2.219 REV64 (vector).
pub fn encode_neon_rev64_16b(vn: &SmtExpr) -> SmtExpr {
    // Doubleword-periodic masks, assembled from 64-bit halves (bv_const is
    // u64-wide) and broadcast to both containers.
    let m8 = SmtExpr::bv_const(0x00FF_00FF_00FF_00FF, 64);
    let m16 = SmtExpr::bv_const(0x0000_FFFF_0000_FFFF, 64);
    let m32 = SmtExpr::bv_const(0x0000_0000_FFFF_FFFF, 64);
    let m8 = m8.clone().concat(m8);
    let m16 = m16.clone().concat(m16);
    let m32 = m32.clone().concat(m32);
    let sh8 = SmtExpr::bv_const(8, 128);
    let sh16 = SmtExpr::bv_const(16, 128);
    let sh32 = SmtExpr::bv_const(32, 128);

    // Step 1: swap adjacent bytes within each 16-bit group.
    let x = vn
        .clone()
        .bvlshr(sh8.clone())
        .bvand(m8.clone())
        .bvor(vn.clone().bvand(m8).bvshl(sh8));
    // Step 2: swap adjacent 16-bit groups within each 32-bit group.
    let x = x
        .clone()
        .bvlshr(sh16.clone())
        .bvand(m16.clone())
        .bvor(x.bvand(m16).bvshl(sh16));
    // Step 3: swap the two 32-bit halves within each 64-bit container.
    x.clone()
        .bvlshr(sh32.clone())
        .bvand(m32.clone())
        .bvor(x.bvand(m32).bvshl(sh32))
}

/// Encode `RBIT Vd.16B, Vn.16B` -- NEON per-byte bit reversal: within EACH of
/// the 16 bytes, the 8 bits are reversed in place (output bit `8k+p` == input
/// bit `8k+7-p`); a bit NEVER crosses a byte boundary. This is the per-byte
/// 8-bit reverse (`b.reverse_bits()` mapped over a `[u8; N]`) LLVM emits with
/// `rbit.16b`.
///
/// Modeled as the classic within-byte SWAR bit-reversal butterfly applied to
/// all 16 bytes in parallel via byte-periodic masks. Each step swaps
/// progressively wider bit groups (adjacent bits, 2-bit groups, nibbles); the
/// whole-register shift amounts are 1/2/4 and the byte-periodic masks
/// (`0x55`/`0x33`/`0x0F` broadcast to every byte) confine every routed bit to
/// its own byte: the highest selected bit shifted LEFT by `k` stays within the
/// byte (bit 6 -> 7 for k=1, bits {0,1} -> {6,7} for k=2, low nibble -> high
/// nibble for k=4), and the cross-byte bit the RIGHT shift drags in from the
/// next byte's bit 0 always lands on a position the same mask clears. So this
/// is an EXACT whole-register model of the ARM ARM per-container element-reverse
/// for the 8-bit container -- and STRUCTURALLY INDEPENDENT of the per-BIT
/// `Extract`/`Concat` permutation the faithful proof's SOURCE side uses.
///
/// Reference: ARM DDI 0487, C7.2.218 RBIT (vector).
pub fn encode_neon_rbit_16b(vn: &SmtExpr) -> SmtExpr {
    // Byte-periodic masks broadcast across all 16 bytes (128 bits), assembled
    // from 64-bit halves (bv_const is u64-wide).
    let bcast = |byte_pat: u64| {
        let half = SmtExpr::bv_const(byte_pat, 64);
        half.clone().concat(half)
    };
    let m1 = bcast(0x5555_5555_5555_5555); // bits {0,2,4,6} of each byte
    let m2 = bcast(0x3333_3333_3333_3333); // bits {0,1,4,5} of each byte
    let m4 = bcast(0x0f0f_0f0f_0f0f_0f0f); // bits {0,1,2,3} of each byte
    let sh1 = SmtExpr::bv_const(1, 128);
    let sh2 = SmtExpr::bv_const(2, 128);
    let sh4 = SmtExpr::bv_const(4, 128);
    // swap adjacent bits within each byte
    let x = vn.clone();
    let x = x
        .clone()
        .bvlshr(sh1.clone())
        .bvand(m1.clone())
        .bvor(x.bvand(m1).bvshl(sh1));
    // swap 2-bit groups within each byte
    let x = x
        .clone()
        .bvlshr(sh2.clone())
        .bvand(m2.clone())
        .bvor(x.bvand(m2).bvshl(sh2));
    // swap nibbles within each byte
    x.clone()
        .bvlshr(sh4.clone())
        .bvand(m4.clone())
        .bvor(x.bvand(m4).bvshl(sh4))
}

// ---------------------------------------------------------------------------
// NEON integer min/max operations
// ---------------------------------------------------------------------------

/// Encode `SMIN.<T> Vd, Vn, Vm` -- NEON vector signed minimum.
///
/// Semantics: for each lane `i`: `Vd[i] = if Vn[i] <s Vm[i] then Vn[i] else Vm[i]`.
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S.
/// Note: no 2D (64-bit lane) signed integer minimum in AArch64 NEON.
/// Reference: ARM DDI 0487, C7.2.277 SMIN (vector).
pub fn encode_neon_smin(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    debug_assert!(
        arrangement != VectorArrangement::D2,
        "NEON SMIN does not support 2D arrangement"
    );
    map_lanes_binary(vn, vm, arrangement, |a, b| {
        SmtExpr::ite(a.clone().bvslt(b.clone()), a, b)
    })
}

/// Encode `UMIN.<T> Vd, Vn, Vm` -- NEON vector unsigned minimum.
///
/// Semantics: for each lane `i`: `Vd[i] = if Vn[i] <u Vm[i] then Vn[i] else Vm[i]`.
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S.
/// Note: no 2D (64-bit lane) unsigned integer minimum in AArch64 NEON.
/// Reference: ARM DDI 0487, C7.2.378 UMIN (vector).
pub fn encode_neon_umin(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    debug_assert!(
        arrangement != VectorArrangement::D2,
        "NEON UMIN does not support 2D arrangement"
    );
    map_lanes_binary(vn, vm, arrangement, |a, b| {
        SmtExpr::ite(a.clone().bvult(b.clone()), a, b)
    })
}

/// Encode `SMAX.<T> Vd, Vn, Vm` -- NEON vector signed maximum.
///
/// Semantics: for each lane `i`: `Vd[i] = if Vn[i] >s Vm[i] then Vn[i] else Vm[i]`.
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S.
/// Note: no 2D (64-bit lane) signed integer maximum in AArch64 NEON.
/// Reference: ARM DDI 0487, C7.2.274 SMAX (vector).
pub fn encode_neon_smax(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    debug_assert!(
        arrangement != VectorArrangement::D2,
        "NEON SMAX does not support 2D arrangement"
    );
    map_lanes_binary(vn, vm, arrangement, |a, b| {
        SmtExpr::ite(a.clone().bvsgt(b.clone()), a, b)
    })
}

/// Encode `UMAX.<T> Vd, Vn, Vm` -- NEON vector unsigned maximum.
///
/// Semantics: for each lane `i`: `Vd[i] = if Vn[i] >u Vm[i] then Vn[i] else Vm[i]`.
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S.
/// Note: no 2D (64-bit lane) unsigned integer maximum in AArch64 NEON.
/// Reference: ARM DDI 0487, C7.2.375 UMAX (vector).
pub fn encode_neon_umax(arrangement: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr) -> SmtExpr {
    debug_assert!(
        arrangement != VectorArrangement::D2,
        "NEON UMAX does not support 2D arrangement"
    );
    map_lanes_binary(vn, vm, arrangement, |a, b| {
        SmtExpr::ite(a.clone().bvugt(b.clone()), a, b)
    })
}

// ---------------------------------------------------------------------------
// NEON multiply-accumulate
// ---------------------------------------------------------------------------

/// Encode `MLA.<T> Vd, Vn, Vm` -- NEON vector multiply-accumulate.
///
/// Semantics: for each lane `i`: `Vd[i] = Va[i] + Vn[i] * Vm[i]` (wrapping).
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S.
/// Note: no 2D (64-bit lane) integer multiply-accumulate in AArch64 NEON.
/// Reference: ARM DDI 0487, C7.2.200 MLA (vector).
pub fn encode_neon_mla(
    arrangement: VectorArrangement,
    va: &SmtExpr,
    vn: &SmtExpr,
    vm: &SmtExpr,
) -> SmtExpr {
    debug_assert!(
        arrangement != VectorArrangement::D2,
        "NEON MLA does not support 2D arrangement"
    );
    let lane_count = arrangement.lane_count();
    let lanes: Vec<SmtExpr> = (0..lane_count)
        .map(|i| {
            let a = lane_extract(va, arrangement, i);
            let n = lane_extract(vn, arrangement, i);
            let m = lane_extract(vm, arrangement, i);
            a.bvadd(n.bvmul(m))
        })
        .collect();
    concat_lanes(&lanes, arrangement)
}

/// Encode `MOVI Vd.16B, #imm` -- NEON move immediate (byte broadcast).
///
/// Semantics: every byte of `Vd` is set to `imm` (8-bit immediate).
/// For a 128-bit register, this means all 16 bytes are identical.
/// For a 64-bit register, all 8 bytes are identical.
///
/// Reference: ARM DDI 0487, C7.2.206 MOVI.
pub fn encode_neon_movi(width: u32, imm: u8) -> SmtExpr {
    let byte_count = width / 8;
    let byte_val = SmtExpr::bv_const(imm as u64, 8);
    let mut result = byte_val.clone();
    for _ in 1..byte_count {
        result = byte_val.clone().concat(result);
    }
    result
}

// ---------------------------------------------------------------------------
// POST-INDEX BASE-REGISTER WRITEBACK
// ---------------------------------------------------------------------------
//
// These model ONE facet of the post-index NEON memory instructions: the update
// of the base register. They say NOTHING about the memory transfer itself --
// see the deferral reasons in `coverage_gate::aarch64_deferred_value_op_reason`,
// which those opcodes deliberately KEEP.
//
// `trust-cg-verify` cannot depend on `trust-cg-codegen`, so the real byte
// encoders are unreachable from here and the word layouts below are MIRRORS of
// `encoding_neon.rs`. A mirror is only worth something if it is pinned against
// the original, so `neon_post_index_word_layout_matches_codegen` asserts these
// against the byte-exact encoder values.
//
// The machine side deliberately DECODES the immediate field back out of the
// assembled word rather than restating `base + imm`. Restating it is exactly the
// shape of the already-RETRACTED `proof_post_index_writeback` degenerate
// obligation: both sides would be the same `bvadd`. Decoding `imm7` and applying
// the architectural scale makes the two sides structurally distinct and gives
// the solver something real to prove -- that the ENCODED field, interpreted the
// way hardware interprets it, advances the base by exactly the number of bytes
// the instruction transfers.

/// Bit-layout mirror of codegen `encode_ldp_q_post_imm`: LDP (SIMD&FP Q pair,
/// post-index). `0xACC0_0000 | imm7<<15 | Rt2<<10 | Rn<<5 | Rt`, where `imm7` is
/// the byte offset scaled by the 16-byte Q granule.
pub fn neon_ldp_q_post_word(offset_bytes: i64, rt2: u8, rn: u8, rt: u8) -> u32 {
    let imm7 = ((offset_bytes / 16) as i32 as u32) & 0x7F;
    0xACC0_0000 | (imm7 << 15) | ((rt2 as u32) << 10) | ((rn as u32) << 5) | (rt as u32)
}

/// Bit-layout mirror of codegen `encode_stp_q_post_imm`: identical to LDP with
/// the L bit (22) CLEAR.
pub fn neon_stp_q_post_word(offset_bytes: i64, rt2: u8, rn: u8, rt: u8) -> u32 {
    let imm7 = ((offset_bytes / 16) as i32 as u32) & 0x7F;
    0xAC80_0000 | (imm7 << 15) | ((rt2 as u32) << 10) | ((rn as u32) << 5) | (rt as u32)
}

/// MACHINE side of the Q-PAIR post-index writeback: DECODE `imm7` out of the
/// real instruction word, sign-extend it, and apply the architectural 16-byte
/// scale. `Xn' = Xn + (sext(imm7) << 4)`.
pub fn encode_neon_pair_post_writeback(base: &SmtExpr, word: u32) -> SmtExpr {
    let w = SmtExpr::bv_const(word as u64, 32);
    let imm7 = w.extract(21, 15);
    let scaled = imm7.sign_ext(57).bvshl(SmtExpr::bv_const(4, 64));
    base.clone().bvadd(scaled)
}

/// MACHINE side of the LD1/ST1 single-register post-index writeback. Here the
/// transfer size is carried by the Q bit (bit 30), not an immediate field:
/// `Xn' = Xn + (Q ? 16 : 8)`.
pub fn encode_neon_single_post_writeback(base: &SmtExpr, word: u32) -> SmtExpr {
    let w = SmtExpr::bv_const(word as u64, 32);
    let q = w.extract(30, 30);
    base.clone().bvadd(SmtExpr::ite(
        q.eq_expr(SmtExpr::bv_const(1, 1)),
        SmtExpr::bv_const(16, 64),
        SmtExpr::bv_const(8, 64),
    ))
}

/// Encode the architectural REGISTER WRITE of byte-form `MOVI Vd.<T>, #imm8`,
/// SYMBOLIC in the immediate: the byte `imm` replicated across every byte of the
/// destination, with the upper 64 bits ZEROED when `q == 0` (the Q=0 write
/// semantics every AArch64 64-bit SIMD form has).
///
/// This generalizes [`encode_neon_movi`], which takes a CONCRETE `u8` and can
/// therefore only ever state a fact about one particular constant. A faithful
/// obligation needs the immediate to be a symbolic `Var`, so the claim is "for
/// EVERY byte value" rather than "for this one".
///
/// Reference: ARM DDI 0487, C7.2.206 MOVI (vector), `cmode = 0b1110`, `op = 0`.
pub fn encode_neon_movi_byte_reg(q: u32, imm: &SmtExpr) -> SmtExpr {
    debug_assert_eq!(imm.bv_width(), 8, "byte-form MOVI takes an 8-bit immediate");
    let mut lo64 = imm.clone();
    for _ in 1..8 {
        lo64 = imm.clone().concat(lo64);
    }
    if q == 1 {
        lo64.clone().concat(lo64)
    } else {
        SmtExpr::bv_const(0, 64).concat(lo64)
    }
}

// ---------------------------------------------------------------------------
// NEON shift operations
// ---------------------------------------------------------------------------

/// Encode `SHL.<T> Vd, Vn, #imm` -- NEON vector shift left (immediate).
///
/// Semantics: for each lane `i`: `Vd[i] = Vn[i] << imm`.
/// The shift amount is a compile-time constant, not a register.
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S, 2D.
/// Constraint: `0 <= imm < lane_bits`.
/// Reference: ARM DDI 0487, C7.2.268 SHL (vector).
pub fn encode_neon_shl(arrangement: VectorArrangement, vn: &SmtExpr, imm: u32) -> SmtExpr {
    debug_assert!(
        imm < arrangement.lane_bits(),
        "SHL immediate must be < lane_bits"
    );
    map_lanes_binary_imm(vn, imm as u64, arrangement, |a, b| a.bvshl(b))
}

/// Encode `USHR.<T> Vd, Vn, #imm` -- NEON vector unsigned shift right (immediate).
///
/// Semantics: for each lane `i`: `Vd[i] = Vn[i] >> imm` (logical/unsigned).
/// The shift amount is a compile-time constant.
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S, 2D.
/// Constraint: `1 <= imm <= lane_bits`.
/// Reference: ARM DDI 0487, C7.2.387 USHR (vector).
pub fn encode_neon_ushr(arrangement: VectorArrangement, vn: &SmtExpr, imm: u32) -> SmtExpr {
    debug_assert!(
        imm >= 1 && imm <= arrangement.lane_bits(),
        "USHR immediate must be in [1, lane_bits]"
    );
    map_lanes_binary_imm(vn, imm as u64, arrangement, |a, b| a.bvlshr(b))
}

/// Encode `SSHR.<T> Vd, Vn, #imm` -- NEON vector signed shift right (immediate).
///
/// Semantics: for each lane `i`: `Vd[i] = Vn[i] >>s imm` (arithmetic/signed).
/// The shift amount is a compile-time constant.
///
/// Valid arrangements: 8B, 16B, 4H, 8H, 2S, 4S, 2D.
/// Constraint: `1 <= imm <= lane_bits`.
/// Reference: ARM DDI 0487, C7.2.304 SSHR (vector).
pub fn encode_neon_sshr(arrangement: VectorArrangement, vn: &SmtExpr, imm: u32) -> SmtExpr {
    debug_assert!(
        imm >= 1 && imm <= arrangement.lane_bits(),
        "SSHR immediate must be in [1, lane_bits]"
    );
    map_lanes_binary_imm(vn, imm as u64, arrangement, |a, b| a.bvashr(b))
}

// ===========================================================================
// NEON LANE-WISE FLOATING-POINT (AArch64 SIMD FP) — the B-aarch64-neon-fp side.
// ===========================================================================
//
// AArch64 NEON FP arithmetic decomposes into per-lane scalar FP operations, EXACTLY
// like the NEON integer encoders above decompose into per-lane integer ops. A
// 128-bit `FADD.4S` is four independent binary32 additions; `FADD.2D` is two
// independent binary64 additions; the 64-bit `FADD.2S` (D-register) is two binary32
// additions with the upper 64 bits of the q-register zeroed by hardware.
//
// These encoders build NO new FP MATH: every per-lane op reuses the SmtExpr FP
// nodes (`SmtExpr::fp_add/fp_sub/fp_mul/fp_div/fp_neg/fp_abs/fp_sqrt` and the
// `fp_lt/fp_gt/fp_eq/fp_le/fp_is_nan` predicates), which `try_eval` evaluates
// through the SILICON-VALIDATED INTEGER-ONLY `fp_bitmodel` (host FPU EVICTED for
// f32/f64, #89/#91/#94). The bit-model carries the AArch64 FP semantics directly
// (it was validated on the M4), so this is the lane-wise re-use of the SAME model
// the scalar AArch64 FP bridge (fp_bitmodel_bridge.rs) already grounds.
//
// LANE ↔ FP CARRIER. There is no symbolic bitvector→FP reinterpret node in SmtExpr,
// so a Bv128 vector is split into per-lane RAW-BIT slices and each slice is wrapped
// in an `FPConst { bits, eb, sb }` leaf via [`neon_fp_lanes`] (the named Bv128
// lane-split for FP, by VectorArrangement). The per-op encoders below take those
// per-lane FP leaves and return a `Vec<SmtExpr>` of per-lane RESULT expressions
// (one FP-producing node per lane for arithmetic; one all-ones/all-zero Bv mask per
// lane for the compares). The caller (the differential bridge / a lowering proof)
// recovers each lane's result bits — f64 lane: `to_bits()`; f32 lane: the
// integer-only `fcvt_narrow` of the f64 carrier — and lane-concats them back into
// the Bv128, the inverse of the split. The split-by-arrangement + per-lane FP op +
// (caller-side) concat is the lane-wise NEON-FP pipeline, with NO new FP math.
//
// AArch64-SPECIFIC NaN SEMANTICS (modeled AS ARM, NOT RISC-V minimumNumber, NOT x86
// MINSS-second-operand):
//   * FMIN/FMAX are IEEE legacy / NaN-PROPAGATING (per ARM FPProcessNaN): if EITHER
//     input is NaN the result is a NaN (the selected/quieted input NaN).
//   * FMINNM/FMAXNM are IEEE-2008 minNum/maxNum: a LONE quiet-NaN yields the NUMBER;
//     a signaling-NaN input (or both NaN) forces a NaN result.
//   * The signed-zero ordering -0 < +0 applies to all four (FMIN(-0,+0) = -0, etc.).
// These are dispatched here as explicit ite-trees over the per-lane FP predicates so
// the NaN-vs-number distinction (the load-bearing FMIN-vs-FMINNM difference) is
// modeled symbolically; the evaluator routes the underlying FP classification +
// comparison + the NaN-producing arithmetic through the AArch64 bit-model. NaN
// RESULT lanes are emitted as the format's canonical qNaN, and the bridge compares
// NaN-result lanes by NaN-CLASS (payloads may legitimately differ between the
// FPProcessNaN-selected payload and the canonical NaN) — but NEVER loosens for a
// non-NaN lane value, which is always a strict bit match.

/// The (eb, sb) IEEE parameters for a NEON FP lane: .2S/.4S lanes are binary32
/// (eb=8, sb=24); .2D lanes are binary64 (eb=11, sb=53).
fn fp_lane_params(arrangement: VectorArrangement) -> (u32, u32) {
    match arrangement.lane_bits() {
        32 => (8, 24),
        64 => (11, 53),
        other => panic!("NEON FP: lane width {other} is not a valid FP lane (need 32 or 64)"),
    }
}

/// Canonical quiet-NaN bit pattern for an (eb, sb) FP format: sign 0, exponent all
/// ones, mantissa MSB set, rest zero (0x7fc0_0000 for f32, 0x7ff8.. for f64).
fn canonical_nan_bits(eb: u32, sb: u32) -> u64 {
    let mant = sb - 1;
    let exp_all_ones = ((1u64 << eb) - 1) << mant;
    let qbit = 1u64 << (mant - 1);
    exp_all_ones | qbit
}

/// True iff `x` (known to be +/-0 under a `fp_is_zero` gate) is NEGATIVE ZERO.
///
/// Plain `fp.lt(x, +0)` is FALSE for -0 (IEEE ordered relations treat -0 == +0), so
/// the robust evaluator-supported signal is the DIVISION sign trick: `+Inf / x` is
/// `+Inf` for `x = +0` and `-Inf` for `x = -0` (the integer-only bit-model `fdiv`
/// implements Inf/0 = signed Inf exactly). So `(+Inf / x) < +0` is true EXACTLY for
/// -0. (Mirrors the RISC-V FMIN/FMAX signed-zero tiebreak.)
fn lane_is_neg_zero(x: &SmtExpr, eb: u32, sb: u32) -> SmtExpr {
    let pos_inf = SmtExpr::fp_const(((1u64 << eb) - 1) << (sb - 1), eb, sb);
    let zero = SmtExpr::fp_const(0, eb, sb);
    SmtExpr::fp_div(crate::smt::RoundingMode::RNE, pos_inf, x.clone()).fp_lt(zero)
}

/// Split a 128-bit (or 64-bit) NEON vector value `bits` into its per-lane FP leaves
/// by `arrangement`, least-significant lane first. Each lane is an `FPConst` whose
/// raw bits are the lane's slice of the vector (.2S/.4S -> binary32 leaves; .2D ->
/// binary64 leaves). This is the named Bv128 lane-SPLIT for FP — the FP analog of
/// `lane_split`, the entry point the lane-wise NEON-FP encoders build on.
pub fn neon_fp_lanes(bits: u128, arrangement: VectorArrangement) -> Vec<SmtExpr> {
    let (eb, sb) = fp_lane_params(arrangement);
    let lane_bits = arrangement.lane_bits();
    let n = arrangement.lane_count();
    let mask: u128 = if lane_bits >= 128 {
        u128::MAX
    } else {
        (1u128 << lane_bits) - 1
    };
    (0..n)
        .map(|i| {
            let slice = ((bits >> (i * lane_bits)) & mask) as u64;
            SmtExpr::fp_const(slice, eb, sb)
        })
        .collect()
}

/// Encode `FADD.<T> Vd, Vn, Vm` lane-wise: per lane `Vd[i] = Vn[i] + Vm[i]`.
/// Returns one FP-producing SmtExpr per lane (RNE rounding, the NEON default).
/// Valid arrangements: .2S, .4S (binary32), .2D (binary64).
/// Reference: ARM DDI 0487, C7.2.93 FADD (vector).
pub fn encode_neon_fadd(vn_lanes: &[SmtExpr], vm_lanes: &[SmtExpr]) -> Vec<SmtExpr> {
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        SmtExpr::fp_add(crate::smt::RoundingMode::RNE, a, b)
    })
}

/// Encode `FSUB.<T> Vd, Vn, Vm` lane-wise: per lane `Vd[i] = Vn[i] - Vm[i]`.
/// Reference: ARM DDI 0487, C7.2.118 FSUB (vector).
pub fn encode_neon_fsub(vn_lanes: &[SmtExpr], vm_lanes: &[SmtExpr]) -> Vec<SmtExpr> {
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        SmtExpr::fp_sub(crate::smt::RoundingMode::RNE, a, b)
    })
}

/// Encode `FMUL.<T> Vd, Vn, Vm` lane-wise: per lane `Vd[i] = Vn[i] * Vm[i]`.
/// Reference: ARM DDI 0487, C7.2.114 FMUL (vector).
pub fn encode_neon_fmul(vn_lanes: &[SmtExpr], vm_lanes: &[SmtExpr]) -> Vec<SmtExpr> {
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        SmtExpr::fp_mul(crate::smt::RoundingMode::RNE, a, b)
    })
}

/// Encode `FDIV.<T> Vd, Vn, Vm` lane-wise: per lane `Vd[i] = Vn[i] / Vm[i]`.
/// Reference: ARM DDI 0487, C7.2.97 FDIV (vector).
pub fn encode_neon_fdiv(vn_lanes: &[SmtExpr], vm_lanes: &[SmtExpr]) -> Vec<SmtExpr> {
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        SmtExpr::fp_div(crate::smt::RoundingMode::RNE, a, b)
    })
}

/// Encode `FNEG.<T> Vd, Vn` lane-wise: per lane `Vd[i] = -Vn[i]` (sign-bit flip).
/// Reference: ARM DDI 0487, C7.2.104 FNEG (vector).
pub fn encode_neon_fneg(vn_lanes: &[SmtExpr]) -> Vec<SmtExpr> {
    vn_lanes.iter().map(|a| a.clone().fp_neg()).collect()
}

/// Encode `FABS.<T> Vd, Vn` lane-wise: per lane `Vd[i] = |Vn[i]|` (sign-bit clear).
/// Reference: ARM DDI 0487, C7.2.91 FABS (vector).
pub fn encode_neon_fabs(vn_lanes: &[SmtExpr]) -> Vec<SmtExpr> {
    vn_lanes.iter().map(|a| a.clone().fp_abs()).collect()
}

/// Encode `FSQRT.<T> Vd, Vn` lane-wise: per lane `Vd[i] = sqrt(Vn[i])` (RNE).
/// Reference: ARM DDI 0487, C7.2.117 FSQRT (vector).
pub fn encode_neon_fsqrt(vn_lanes: &[SmtExpr]) -> Vec<SmtExpr> {
    vn_lanes
        .iter()
        .map(|a| SmtExpr::fp_sqrt(crate::smt::RoundingMode::RNE, a.clone()))
        .collect()
}

/// Per-lane all-ones / all-zero mask leaves for the FP compares, at the lane width.
fn cmp_masks(arrangement: VectorArrangement) -> (SmtExpr, SmtExpr) {
    let lane_bits = arrangement.lane_bits();
    let ones = if lane_bits >= 64 {
        u64::MAX
    } else {
        (1u64 << lane_bits) - 1
    };
    (
        SmtExpr::bv_const(ones, lane_bits),
        SmtExpr::bv_const(0, lane_bits),
    )
}

/// Encode `FCMEQ.<T> Vd, Vn, Vm` lane-wise: per lane all-ones iff `Vn[i] == Vm[i]`
/// (ordered; a NaN operand -> 0). Returns per-lane Bv masks.
/// Reference: ARM DDI 0487, C7.2.94 FCMEQ (register).
pub fn encode_neon_fcmeq(
    arrangement: VectorArrangement,
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
) -> Vec<SmtExpr> {
    let (ones, zero) = cmp_masks(arrangement);
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        SmtExpr::ite(a.fp_eq(b), ones.clone(), zero.clone())
    })
}

/// Encode `FCMGT.<T> Vd, Vn, Vm` lane-wise: per lane all-ones iff `Vn[i] > Vm[i]`
/// (ordered; NaN -> 0). Reference: ARM DDI 0487, C7.2.96 FCMGT (register).
pub fn encode_neon_fcmgt(
    arrangement: VectorArrangement,
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
) -> Vec<SmtExpr> {
    let (ones, zero) = cmp_masks(arrangement);
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        SmtExpr::ite(a.fp_gt(b), ones.clone(), zero.clone())
    })
}

/// Encode `FCMGE.<T> Vd, Vn, Vm` lane-wise: per lane all-ones iff `Vn[i] >= Vm[i]`
/// (ordered; NaN -> 0). Reference: ARM DDI 0487, C7.2.95 FCMGE (register).
pub fn encode_neon_fcmge(
    arrangement: VectorArrangement,
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
) -> Vec<SmtExpr> {
    let (ones, zero) = cmp_masks(arrangement);
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        SmtExpr::ite(a.fp_ge(b), ones.clone(), zero.clone())
    })
}

// ---------------------------------------------------------------------------
// NEON FP fused multiply-accumulate / int->FP convert / lane-scalar copy
// (the ops the IV-synthesized FP-reduction vectorizer `neon_fpred` emits)
// ---------------------------------------------------------------------------

/// Encode `FMLA.<T> Vd, Vn, Vm` lane-wise: per lane
/// `Vd[i]' = fma(Vn[i], Vm[i], Vd[i])` — the FUSED multiply-accumulate with a
/// SINGLE rounding (`fp.fma`, `round_RNE(Vn*Vm + Vd)`), NOT the round-TWICE
/// `fp_add(fp_mul(Vn,Vm), Vd)`. `vd_lanes` is the TIED accumulator (read AND
/// written). RNE rounding, the NEON default.
/// Reference: ARM DDI 0487, C7.2.104 FMLA (vector).
pub fn encode_neon_fmla(
    vd_lanes: &[SmtExpr],
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
) -> Vec<SmtExpr> {
    (0..vn_lanes.len())
        .map(|i| {
            SmtExpr::fp_fma(
                crate::smt::RoundingMode::RNE,
                vn_lanes[i].clone(),
                vm_lanes[i].clone(),
                vd_lanes[i].clone(),
            )
        })
        .collect()
}

/// Encode `FMLS.<T> Vd, Vn, Vm` lane-wise: per lane
/// `Vd[i]' = fma(-Vn[i], Vm[i], Vd[i])` — the FUSED multiply-SUBTRACT with a
/// SINGLE rounding. Per ARM the PRODUCT is negated (the `E` bit, exactly like
/// FADD vs FSUB), i.e. `round_RNE(Vd + (-Vn)*Vm)` with ONE rounding.
/// Reference: ARM DDI 0487, C7.2.106 FMLS (vector).
pub fn encode_neon_fmls(
    vd_lanes: &[SmtExpr],
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
) -> Vec<SmtExpr> {
    (0..vn_lanes.len())
        .map(|i| {
            SmtExpr::fp_fma(
                crate::smt::RoundingMode::RNE,
                vn_lanes[i].clone().fp_neg(),
                vm_lanes[i].clone(),
                vd_lanes[i].clone(),
            )
        })
        .collect()
}

/// Encode `FMLA (by element)` `Vd, Vn, Vm.Ts[selector]` lane-wise: per lane
/// `Vd[i]' = fma(Vn[i], Vm[selector], Vd[i])` — the FUSED multiply-accumulate
/// with a SINGLE rounding, EXCEPT the multiplier is ONE broadcast lane
/// `Vm[selector]` rather than the matching lane `Vm[i]`. `vd_lanes` is the TIED
/// accumulator. RNE rounding.
/// Reference: ARM DDI 0487, C7.2.105 FMLA (by element).
pub fn encode_neon_fmla_lane(
    vd_lanes: &[SmtExpr],
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
    selector: usize,
) -> Vec<SmtExpr> {
    let m = vm_lanes[selector].clone();
    (0..vn_lanes.len())
        .map(|i| {
            SmtExpr::fp_fma(
                crate::smt::RoundingMode::RNE,
                vn_lanes[i].clone(),
                m.clone(),
                vd_lanes[i].clone(),
            )
        })
        .collect()
}

/// Encode `FMLS (by element)` `Vd, Vn, Vm.Ts[selector]` lane-wise: per lane
/// `Vd[i]' = fma(-Vn[i], Vm[selector], Vd[i])` — the FUSED multiply-SUBTRACT
/// (product negated, the `E` bit) reading one broadcast lane. This is NOT
/// emitted by the backend; it exists only as the POLARITY refute control for
/// the by-element FMLA obligations (encoding an FMLA-by-element as FMLS must
/// refute). RNE rounding.
/// Reference: ARM DDI 0487, C7.2.107 FMLS (by element).
pub fn encode_neon_fmls_lane(
    vd_lanes: &[SmtExpr],
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
    selector: usize,
) -> Vec<SmtExpr> {
    let m = vm_lanes[selector].clone();
    (0..vn_lanes.len())
        .map(|i| {
            SmtExpr::fp_fma(
                crate::smt::RoundingMode::RNE,
                vn_lanes[i].clone().fp_neg(),
                m.clone(),
                vd_lanes[i].clone(),
            )
        })
        .collect()
}

/// Encode `SCVTF.<T> Vd, Vn` (vector, integer form) lane-wise: per lane
/// `Vd[i] = (fp) (signed) Vn[i]` (RNE). `int_lanes` are the SIGNED integer lanes
/// at their natural width; `(eb, sb)` is the target IEEE format. The shared
/// `BvToFP` node interprets its operand as a SIGNED bitvector, matching SCVTF.
/// Reference: ARM DDI 0487, C7.2.271 SCVTF (vector, integer).
pub fn encode_neon_scvtf_vec(int_lanes: &[SmtExpr], eb: u32, sb: u32) -> Vec<SmtExpr> {
    int_lanes
        .iter()
        .map(|lane| SmtExpr::bv_to_fp(crate::smt::RoundingMode::RNE, lane.clone(), eb, sb))
        .collect()
}

/// Encode `UCVTF.<T> Vd, Vn` (vector, integer form) lane-wise: per lane
/// `Vd[i] = (fp) (unsigned) Vn[i]` (RNE). Because the shared `BvToFP` node
/// interprets its operand as SIGNED, each integer lane is FIRST zero-extended by
/// `lane_width` bits (doubling its width) so the sign-bit-clear wider value
/// yields the correct UNSIGNED magnitude — exactly the scalar-UCVTF trick.
/// Reference: ARM DDI 0487, C7.2.297 UCVTF (vector, integer).
pub fn encode_neon_ucvtf_vec(
    int_lanes: &[SmtExpr],
    lane_width: u32,
    eb: u32,
    sb: u32,
) -> Vec<SmtExpr> {
    int_lanes
        .iter()
        .map(|lane| {
            let zext = lane.clone().zero_ext(lane_width);
            SmtExpr::bv_to_fp(crate::smt::RoundingMode::RNE, zext, eb, sb)
        })
        .collect()
}

/// Encode `FCVTL Vd.2D, Vn.2S` / `FCVTL2 Vd.2D, Vn.4S` (vector `f32 -> f64`
/// widening convert) lane-wise: each of the two output `.2D` (f64) lanes is the
/// `fpext` of a source `f32` lane. `high=false` (FCVTL) reads the LOW two `f32`
/// lanes of `Vn` (lanes 0,1 of `Vn.4S` — the low 64 bits); `high=true` (FCVTL2)
/// reads the HIGH two (lanes 2,3 — the high 64 bits). Widening `f32 -> f64` is
/// EXACT (every `f32` value is representable as `f64`), so each lane is a pure
/// `fp_to_fp` to the f64 format `(11, 53)` — the rounding mode is immaterial
/// (RNE, matching the sibling converts). `vn` is the reassembled 128-bit source
/// register; the `f32` lanes are reinterpreted from raw bits via `bv_bits_to_fp`.
/// Returns the two output f64 lanes (lane 0 first).
/// Reference: ARM DDI 0487, C7.2.98 FCVTL, FCVTL2 (vector).
pub fn encode_neon_fcvtl_vec(vn: &SmtExpr, high: bool) -> Vec<SmtExpr> {
    use crate::smt::RoundingMode;
    let base = if high { 2 } else { 0 };
    (0..2)
        .map(|i| {
            // Source f32 lane: lane (base + i) of the `.4S` view of the register.
            let f32_bits = lane_extract(vn, VectorArrangement::S4, base + i);
            let f32_val = SmtExpr::bv_bits_to_fp(f32_bits, 8, 24);
            // Exact widen to f64.
            SmtExpr::fp_to_fp(RoundingMode::RNE, f32_val, 11, 53)
        })
        .collect()
}

/// Encode `DUP Dd, Vn.D[lane]` (assembler `MOV Dd, Vn.D[lane]`): the 64-bit
/// scalar copy of the selected `.2D` lane, bit-for-bit. Writing `Dd` zeroes the
/// upper 64 bits of `Qd` (the scalar-D-register write semantics), so the
/// meaningful result the drain consumes is exactly the selected 64-bit lane.
/// Reference: ARM DDI 0487, C7.2.85 DUP (element), scalar variant.
pub fn encode_neon_dup_scalar_d(vn: &SmtExpr, lane: u32) -> SmtExpr {
    lane_extract(vn, VectorArrangement::D2, lane)
}

/// Encode `DUP Vd.<T>, Vn.<Ts>[lane]` -- DUP (ELEMENT), vector form: the SELECTED
/// source lane, REPLICATED across every lane of the destination.
///
/// The single `imm5` field encodes BOTH the element size and the source lane, so
/// the destination element size ALWAYS equals the source element size; only Q
/// chooses the lane COUNT. The backend emits Q=1 only -- `encode.rs` derives Q
/// from the destination register class and every emission site allocates an
/// `Fpr128` -- so `arr` is one of the four 128-bit arrangements.
///
/// The selected lane is taken via `lane_extract` over the caller-supplied
/// REASSEMBLED register, so the machine leaf is
/// `Extract(Concat(vn_hi, vn_lo), ..)`; a variant reading the raw halves directly
/// would re-create the very degeneracy the faithful obligation exists to avoid.
///
/// Reference: ARM DDI 0487, C7.2.85 DUP (element).
pub fn encode_neon_dup_element(vn: &SmtExpr, arr: VectorArrangement, lane: u32) -> SmtExpr {
    debug_assert_eq!(
        arr.total_bits(),
        128,
        "the emitted DUP (element) form is always Q=1"
    );
    let selected = lane_extract(vn, arr, lane);
    let lanes: Vec<SmtExpr> = (0..arr.lane_count()).map(|_| selected.clone()).collect();
    concat_lanes(&lanes, arr)
}

/// Encode `UMOV Wd/Xd, Vn.<T>[lane]` (vector element -> GPR extract): the
/// selected lane's bits, ZERO-EXTENDED to the destination GPR width. UMOV always
/// zero-extends (in contrast to SMOV, which sign-extends): the `.B`/`.H`/`.S`
/// forms target a 32-bit `Wd` (`gpr_bits = 32`; writing `Wd` also clears the
/// upper 32 bits of `Xd`), and the `.D` form targets a 64-bit `Xd` as a direct
/// 64-bit copy (`gpr_bits = 64`, no extension). `arr` selects the element size /
/// lane count (`B16`/`H8`/`S4`/`D2`), `lane` the source lane. STRUCTURALLY
/// distinct from the source side's raw-D-half slice — the reduction drains and
/// the `V{16I8,8I16,4I32,2I64}ExtractLane` isel all lower through this one op.
/// Reference: ARM DDI 0487, C7.2.334 UMOV.
pub fn encode_neon_umov_general(
    vn: &SmtExpr,
    arr: VectorArrangement,
    lane: u32,
    gpr_bits: u32,
) -> SmtExpr {
    let lane_val = lane_extract(vn, arr, lane);
    let lane_bits = arr.lane_bits();
    if gpr_bits > lane_bits {
        lane_val.zero_ext(gpr_bits - lane_bits)
    } else {
        lane_val
    }
}

/// Shared FMIN/FMAX/FMINNM/FMAXNM lane builder. `is_min` selects min vs max;
/// `is_nm` selects the IEEE minNum/maxNum (FMINNM/FMAXNM, lone qNaN -> number)
/// vs the NaN-propagating legacy FMIN/FMAX (any NaN -> NaN). Returns the per-lane
/// FP-producing / operand-selecting SmtExpr.
///
/// NaN dispatch (modeled AS ARM):
///   * legacy (is_nm=false): a NaN OR b NaN -> NaN (canonical qNaN here); else numeric.
///   * minNum (is_nm=true):  a sNaN OR b sNaN OR (a NaN AND b NaN) -> NaN ; else a
///     lone NaN -> the OTHER operand ; else numeric.
///     Numeric branch: a<b->a / a>b->b for min (swap for max), with the -0<+0 tiebreak
///     on the equal-zeros case.
fn fminmax_lane(eb: u32, sb: u32, a: SmtExpr, b: SmtExpr, is_min: bool, is_nm: bool) -> SmtExpr {
    let a_nan = a.clone().fp_is_nan();
    let b_nan = b.clone().fp_is_nan();
    let canon = SmtExpr::fp_const(canonical_nan_bits(eb, sb), eb, sb);

    // -0/+0 tiebreak: under fp.lt/fp.gt both report false for equal magnitudes
    // (incl. +-0), so detect the negative-zero operand explicitly.
    let a_neg0 = a
        .clone()
        .fp_is_zero()
        .and_expr(lane_is_neg_zero(&a, eb, sb));
    let b_neg0 = b
        .clone()
        .fp_is_zero()
        .and_expr(lane_is_neg_zero(&b, eb, sb));

    let numeric = if is_min {
        let a_lt_b = a.clone().fp_lt(b.clone());
        let a_gt_b = a.clone().fp_gt(b.clone());
        // equal (incl zeros): the -0 operand wins for min.
        let tie = SmtExpr::ite(a_neg0.clone(), a.clone(), b.clone());
        SmtExpr::ite(a_lt_b, a.clone(), SmtExpr::ite(a_gt_b, b.clone(), tie))
    } else {
        let a_gt_b = a.clone().fp_gt(b.clone());
        let a_lt_b = a.clone().fp_lt(b.clone());
        // equal (incl zeros): the +0 operand wins for max (so the -0 operand loses).
        let tie = SmtExpr::ite(a_neg0.clone(), b.clone(), a.clone());
        SmtExpr::ite(a_gt_b, a.clone(), SmtExpr::ite(a_lt_b, b.clone(), tie))
    };
    let _ = b_neg0; // the single -0 detection above covers both min and max ties.

    if is_nm {
        // IEEE minNum/maxNum: sNaN(any) or both-NaN -> NaN; lone NaN -> the other.
        let a_snan = is_snan_lane(&a, eb, sb);
        let b_snan = is_snan_lane(&b, eb, sb);
        let both_nan = a_nan.clone().and_expr(b_nan.clone());
        let force_nan = a_snan.or_expr(b_snan).or_expr(both_nan);
        SmtExpr::ite(
            force_nan,
            canon.clone(),
            SmtExpr::ite(
                a_nan.clone(),
                b.clone(),
                SmtExpr::ite(b_nan.clone(), a.clone(), numeric),
            ),
        )
    } else {
        // Legacy NaN-propagating: either NaN -> NaN.
        let any_nan = a_nan.or_expr(b_nan);
        SmtExpr::ite(any_nan, canon, numeric)
    }
}

/// True iff `x` is a SIGNALING NaN: NaN AND the mantissa MSB (quiet bit) is CLEAR.
/// Built symbolically: `fp.isNaN(x) AND NOT(qbit-set)`, where the quiet bit is
/// probed by extracting the raw mantissa-MSB from the FP value's bits. Since SmtExpr
/// has no fp->bits node, we detect sNaN via the algebraic identity that quieting a
/// NaN (here, adding it to itself does NOT quiet under the bit-model — instead we
/// use the fp_is_nan of x together with the canonical comparison): a NaN x is
/// SIGNALING iff `fp.isNaN(x)` AND `x` differs (as bits) from its quieted form.
/// We approximate this for the SYMBOLIC encoder by classifying via the bit-model's
/// own quiet-bit test applied to the FPConst leaf bits when concrete; for a general
/// symbolic leaf we conservatively treat any NaN as potentially signaling only when
/// the leaf is a concrete FPConst (the bridge always passes concrete leaves).
fn is_snan_lane(x: &SmtExpr, eb: u32, sb: u32) -> SmtExpr {
    if let SmtExpr::FPConst { bits, .. } = x {
        let f = if eb == 8 && sb == 24 {
            crate::fp_bitmodel::F32
        } else {
            crate::fp_bitmodel::F64
        };
        let is_s = crate::fp_bitmodel::is_snan(f, *bits);
        // Constant predicate: a 1-bit Bv that the ite reads as a Bool.
        SmtExpr::bv_const(is_s as u64, 1)
    } else {
        // Symbolic leaf: detect sNaN as NaN with the quiet bit clear via the raw
        // bits is not expressible without an fp->bits node, so fall back to "is NaN"
        // (over-approximates force-NaN; only reached for non-constant leaves, which
        // the bridge never passes — the integer-only carrier keeps leaves concrete).
        x.clone().fp_is_nan()
    }
}

/// Encode `FMIN.<T> Vd, Vn, Vm` lane-wise — NaN-PROPAGATING (ARM legacy/IEEE):
/// any NaN operand -> a NaN result. -0 < +0. Returns per-lane FP exprs.
/// Reference: ARM DDI 0487, C7.2.100 FMIN (vector).
pub fn encode_neon_fmin(
    arrangement: VectorArrangement,
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
) -> Vec<SmtExpr> {
    let (eb, sb) = fp_lane_params(arrangement);
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        fminmax_lane(eb, sb, a, b, true, false)
    })
}

/// Encode `FMAX.<T> Vd, Vn, Vm` lane-wise — NaN-PROPAGATING.
/// Reference: ARM DDI 0487, C7.2.98 FMAX (vector).
pub fn encode_neon_fmax(
    arrangement: VectorArrangement,
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
) -> Vec<SmtExpr> {
    let (eb, sb) = fp_lane_params(arrangement);
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        fminmax_lane(eb, sb, a, b, false, false)
    })
}

/// Encode `FMINNM.<T> Vd, Vn, Vm` lane-wise — IEEE-2008 minNum: a LONE quiet-NaN
/// yields the NUMBER; a signaling-NaN (or both NaN) forces a NaN. -0 < +0.
/// Reference: ARM DDI 0487, C7.2.102 FMINNM (vector).
pub fn encode_neon_fminnm(
    arrangement: VectorArrangement,
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
) -> Vec<SmtExpr> {
    let (eb, sb) = fp_lane_params(arrangement);
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        fminmax_lane(eb, sb, a, b, true, true)
    })
}

/// Encode `FMAXNM.<T> Vd, Vn, Vm` lane-wise — IEEE-2008 maxNum.
/// Reference: ARM DDI 0487, C7.2.99 FMAXNM (vector).
pub fn encode_neon_fmaxnm(
    arrangement: VectorArrangement,
    vn_lanes: &[SmtExpr],
    vm_lanes: &[SmtExpr],
) -> Vec<SmtExpr> {
    let (eb, sb) = fp_lane_params(arrangement);
    zip_lanes(vn_lanes, vm_lanes, |a, b| {
        fminmax_lane(eb, sb, a, b, false, true)
    })
}

/// Zip two equal-length per-lane operand slices through a binary per-lane builder.
fn zip_lanes(
    a: &[SmtExpr],
    b: &[SmtExpr],
    f: impl Fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> Vec<SmtExpr> {
    assert_eq!(
        a.len(),
        b.len(),
        "NEON FP: lane count mismatch between operands"
    );
    a.iter()
        .zip(b.iter())
        .map(|(x, y)| f(x.clone(), y.clone()))
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::EvalResult;
    use std::collections::HashMap;

    fn env(pairs: &[(&str, u64)]) -> HashMap<String, u64> {
        pairs.iter().map(|(k, v)| (k.to_string(), *v)).collect()
    }

    // -----------------------------------------------------------------------
    // Helper: pack lanes into a vector value for testing.
    //
    // 64-bit vectors (S2, H4, B8) pack into a single u64 and can be tested
    // directly via `EvalResult::Bv(u64)`.
    //
    // 128-bit vectors (S4, H8, B16, D2) exceed the u64 evaluator range.
    // We test them by extracting individual lanes from the result expression
    // before evaluation -- each lane fits in u64. The helper `assert_lane`
    // encapsulates this pattern.
    // -----------------------------------------------------------------------

    /// Pack two 32-bit values into a 64-bit vector (S2 arrangement).
    /// Lane 0 is least-significant.
    fn pack_2s(lane0: u32, lane1: u32) -> u64 {
        (lane1 as u64) << 32 | (lane0 as u64)
    }

    /// Pack four 16-bit values into a 64-bit vector (H4 arrangement).
    fn pack_4h(l0: u16, l1: u16, l2: u16, l3: u16) -> u64 {
        (l3 as u64) << 48 | (l2 as u64) << 32 | (l1 as u64) << 16 | (l0 as u64)
    }

    /// Pack eight 8-bit values into a 64-bit vector (B8 arrangement).
    #[allow(clippy::too_many_arguments)]
    fn pack_8b(l0: u8, l1: u8, l2: u8, l3: u8, l4: u8, l5: u8, l6: u8, l7: u8) -> u64 {
        (l7 as u64) << 56
            | (l6 as u64) << 48
            | (l5 as u64) << 40
            | (l4 as u64) << 32
            | (l3 as u64) << 24
            | (l2 as u64) << 16
            | (l1 as u64) << 8
            | (l0 as u64)
    }

    // -----------------------------------------------------------------------
    // 128-bit test helpers
    //
    // Since EvalResult::Bv stores u64, we cannot evaluate full 128-bit vectors
    // directly. Instead, we extract each lane from the result *symbolically*
    // (producing a sub-64-bit expression), then evaluate that lane.
    //
    // This is architecturally faithful: NEON ops are defined per-lane, so
    // verifying each lane independently is a valid correctness strategy.
    // -----------------------------------------------------------------------

    use crate::smt::lane_extract;

    /// Assert that a specific lane of a 128-bit result expression evaluates
    /// to the expected value.
    fn assert_lane(
        result_expr: &SmtExpr,
        arrangement: VectorArrangement,
        lane_idx: u32,
        expected: u64,
        env: &HashMap<String, u64>,
    ) {
        let lane_expr = lane_extract(result_expr, arrangement, lane_idx);
        let actual = lane_expr.eval(env);
        assert_eq!(
            actual,
            EvalResult::Bv(expected),
            "lane {} mismatch: expected 0x{:X}, got {:?}",
            lane_idx,
            expected,
            actual
        );
    }

    /// Assert all lanes of a 128-bit result match expected values.
    fn assert_all_lanes(
        result_expr: &SmtExpr,
        arrangement: VectorArrangement,
        expected_lanes: &[u64],
        env: &HashMap<String, u64>,
    ) {
        assert_eq!(
            expected_lanes.len() as u32,
            arrangement.lane_count(),
            "wrong number of expected lanes"
        );
        for (i, &expected) in expected_lanes.iter().enumerate() {
            assert_lane(result_expr, arrangement, i as u32, expected, env);
        }
    }

    /// Build a 128-bit vector from two 64-bit halves (lo, hi).
    ///
    /// The input variables are named `{prefix}_lo` (bits [63:0]) and
    /// `{prefix}_hi` (bits [127:64]). Returns the concatenated expression
    /// and the environment entries to set.
    fn var_128(prefix: &str) -> SmtExpr {
        let lo = SmtExpr::var(format!("{}_lo", prefix), 64);
        let hi = SmtExpr::var(format!("{}_hi", prefix), 64);
        hi.concat(lo)
    }

    /// Insert both halves of a 128-bit variable into the environment.
    fn set_128(env: &mut HashMap<String, u64>, prefix: &str, lo: u64, hi: u64) {
        env.insert(format!("{}_lo", prefix), lo);
        env.insert(format!("{}_hi", prefix), hi);
    }

    // =======================================================================
    // ADD tests
    // =======================================================================

    #[test]
    fn test_neon_add_2s() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_add(VectorArrangement::S2, &vn, &vm);

        // vn = [10, 20], vm = [3, 7]
        let e = env(&[("vn", pack_2s(10, 20)), ("vm", pack_2s(3, 7))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_2s(13, 27)));
    }

    #[test]
    fn test_neon_add_2s_wrapping() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_add(VectorArrangement::S2, &vn, &vm);

        // Wrapping: 0xFFFFFFFF + 1 = 0 per lane
        let e = env(&[
            ("vn", pack_2s(0xFFFFFFFF, 0x80000000)),
            ("vm", pack_2s(1, 0x80000000)),
        ]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_2s(0, 0)));
    }

    #[test]
    fn test_neon_add_4h() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_add(VectorArrangement::H4, &vn, &vm);

        let e = env(&[("vn", pack_4h(1, 2, 3, 4)), ("vm", pack_4h(10, 20, 30, 40))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_4h(11, 22, 33, 44)));
    }

    #[test]
    fn test_neon_add_8b() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_add(VectorArrangement::B8, &vn, &vm);

        let e = env(&[
            ("vn", pack_8b(1, 2, 3, 4, 5, 6, 7, 8)),
            ("vm", pack_8b(10, 20, 30, 40, 50, 60, 70, 80)),
        ]);
        assert_eq!(
            result.eval(&e),
            EvalResult::Bv(pack_8b(11, 22, 33, 44, 55, 66, 77, 88))
        );
    }

    #[test]
    fn test_neon_add_8b_wrapping() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_add(VectorArrangement::B8, &vn, &vm);

        // 0xFF + 1 = 0 per byte lane (wrapping)
        let e = env(&[
            ("vn", pack_8b(0xFF, 200, 0, 0, 0, 0, 0, 0)),
            ("vm", pack_8b(1, 100, 0, 0, 0, 0, 0, 0)),
        ]);
        let r = result.eval(&e);
        // Lane 0: 0xFF + 1 = 0x00 (wrapping), Lane 1: 200 + 100 = 300 & 0xFF = 44
        assert_eq!(r, EvalResult::Bv(pack_8b(0, 44, 0, 0, 0, 0, 0, 0)));
    }

    // =======================================================================
    // SUB tests
    // =======================================================================

    #[test]
    fn test_neon_sub_2s() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_sub(VectorArrangement::S2, &vn, &vm);

        let e = env(&[("vn", pack_2s(100, 200)), ("vm", pack_2s(30, 50))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_2s(70, 150)));
    }

    #[test]
    fn test_neon_sub_4h() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_sub(VectorArrangement::H4, &vn, &vm);

        let e = env(&[
            ("vn", pack_4h(100, 200, 300, 400)),
            ("vm", pack_4h(10, 20, 30, 40)),
        ]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_4h(90, 180, 270, 360)));
    }

    #[test]
    fn test_neon_sub_8b() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_sub(VectorArrangement::B8, &vn, &vm);

        let e = env(&[
            ("vn", pack_8b(50, 100, 150, 200, 10, 20, 30, 40)),
            ("vm", pack_8b(10, 20, 30, 40, 5, 10, 15, 20)),
        ]);
        assert_eq!(
            result.eval(&e),
            EvalResult::Bv(pack_8b(40, 80, 120, 160, 5, 10, 15, 20))
        );
    }

    // =======================================================================
    // MUL tests
    // =======================================================================

    #[test]
    fn test_neon_mul_2s() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_mul(VectorArrangement::S2, &vn, &vm);

        let e = env(&[("vn", pack_2s(6, 7)), ("vm", pack_2s(7, 6))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_2s(42, 42)));
    }

    #[test]
    fn test_neon_mul_4h() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_mul(VectorArrangement::H4, &vn, &vm);

        let e = env(&[("vn", pack_4h(2, 3, 4, 5)), ("vm", pack_4h(10, 10, 10, 10))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_4h(20, 30, 40, 50)));
    }

    #[test]
    fn test_neon_mul_8b() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_mul(VectorArrangement::B8, &vn, &vm);

        // 7 * 6 = 42, 15 * 17 = 255 (fits in u8)
        let e = env(&[
            ("vn", pack_8b(7, 15, 3, 0, 0, 0, 0, 0)),
            ("vm", pack_8b(6, 17, 5, 0, 0, 0, 0, 0)),
        ]);
        assert_eq!(
            result.eval(&e),
            EvalResult::Bv(pack_8b(42, 255, 15, 0, 0, 0, 0, 0))
        );
    }

    #[test]
    fn test_neon_mul_8b_wrapping() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_mul(VectorArrangement::B8, &vn, &vm);

        // 200 * 2 = 400, wrapping to 400 & 0xFF = 144
        let e = env(&[
            ("vn", pack_8b(200, 0, 0, 0, 0, 0, 0, 0)),
            ("vm", pack_8b(2, 0, 0, 0, 0, 0, 0, 0)),
        ]);
        assert_eq!(
            result.eval(&e),
            EvalResult::Bv(pack_8b(144, 0, 0, 0, 0, 0, 0, 0))
        );
    }

    // =======================================================================
    // NEG tests
    // =======================================================================

    #[test]
    fn test_neon_neg_2s() {
        let vn = SmtExpr::var("vn", 64);
        let result = encode_neon_neg(VectorArrangement::S2, &vn);

        // neg(1) = 0xFFFFFFFF in 32-bit, neg(0) = 0
        let e = env(&[("vn", pack_2s(1, 0))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_2s(0xFFFFFFFF, 0)));
    }

    #[test]
    fn test_neon_neg_4h() {
        let vn = SmtExpr::var("vn", 64);
        let result = encode_neon_neg(VectorArrangement::H4, &vn);

        // neg(1) = 0xFFFF, neg(2) = 0xFFFE, neg(0) = 0, neg(100) = 0xFF9C
        let e = env(&[("vn", pack_4h(1, 2, 0, 100))]);
        assert_eq!(
            result.eval(&e),
            EvalResult::Bv(pack_4h(0xFFFF, 0xFFFE, 0, 0xFF9C))
        );
    }

    // =======================================================================
    // Bitwise operation tests
    // =======================================================================

    #[test]
    fn test_neon_and_64bit() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_and(&vn, &vm);

        let e = env(&[("vn", 0xFF00_FF00_FF00_FF00), ("vm", 0x0F0F_0F0F_0F0F_0F0F)]);
        assert_eq!(result.eval(&e), EvalResult::Bv(0x0F00_0F00_0F00_0F00));
    }

    #[test]
    fn test_neon_orr_64bit() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_orr(&vn, &vm);

        let e = env(&[("vn", 0xFF00_0000_0000_0000), ("vm", 0x00FF_0000_0000_0000)]);
        assert_eq!(result.eval(&e), EvalResult::Bv(0xFFFF_0000_0000_0000));
    }

    #[test]
    fn test_neon_eor_64bit() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_eor(&vn, &vm);

        let e = env(&[("vn", 0xAAAA_AAAA_AAAA_AAAA), ("vm", 0xFFFF_FFFF_FFFF_FFFF)]);
        assert_eq!(result.eval(&e), EvalResult::Bv(0x5555_5555_5555_5555));
    }

    #[test]
    fn test_neon_bic_64bit() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);
        let result = encode_neon_bic(&vn, &vm);

        // BIC = vn AND NOT(vm)
        // vn = 0xFF, vm = 0x0F => result = 0xFF AND NOT(0x0F) = 0xFF AND 0xF0 = 0xF0
        let e = env(&[("vn", 0xFFFF_FFFF_FFFF_FFFF), ("vm", 0x0F0F_0F0F_0F0F_0F0F)]);
        assert_eq!(result.eval(&e), EvalResult::Bv(0xF0F0_F0F0_F0F0_F0F0));
    }

    // =======================================================================
    // Shift tests
    // =======================================================================

    #[test]
    fn test_neon_shl_2s() {
        let vn = SmtExpr::var("vn", 64);
        let result = encode_neon_shl(VectorArrangement::S2, &vn, 4);

        // Each 32-bit lane shifted left by 4: 1 << 4 = 16, 0xFF << 4 = 0xFF0
        let e = env(&[("vn", pack_2s(1, 0xFF))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_2s(16, 0xFF0)));
    }

    #[test]
    fn test_neon_shl_4h() {
        let vn = SmtExpr::var("vn", 64);
        let result = encode_neon_shl(VectorArrangement::H4, &vn, 1);

        // Each 16-bit lane shifted left by 1
        let e = env(&[("vn", pack_4h(1, 2, 3, 0x7FFF))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_4h(2, 4, 6, 0xFFFE)));
    }

    #[test]
    fn test_neon_shl_8b() {
        let vn = SmtExpr::var("vn", 64);
        let result = encode_neon_shl(VectorArrangement::B8, &vn, 2);

        // Each 8-bit lane shifted left by 2: 1 << 2 = 4, 63 << 2 = 252
        let e = env(&[("vn", pack_8b(1, 63, 0, 0, 0, 0, 0, 0))]);
        assert_eq!(
            result.eval(&e),
            EvalResult::Bv(pack_8b(4, 252, 0, 0, 0, 0, 0, 0))
        );
    }

    #[test]
    fn test_neon_ushr_2s() {
        let vn = SmtExpr::var("vn", 64);
        let result = encode_neon_ushr(VectorArrangement::S2, &vn, 4);

        // Each 32-bit lane logical shift right by 4
        let e = env(&[("vn", pack_2s(0x100, 0xF0000000))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_2s(0x10, 0x0F000000)));
    }

    #[test]
    fn test_neon_ushr_4h() {
        let vn = SmtExpr::var("vn", 64);
        let result = encode_neon_ushr(VectorArrangement::H4, &vn, 8);

        // Each 16-bit lane logical shift right by 8
        let e = env(&[("vn", pack_4h(0xFF00, 0x1234, 0, 0))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_4h(0xFF, 0x12, 0, 0)));
    }

    #[test]
    fn test_neon_sshr_2s() {
        let vn = SmtExpr::var("vn", 64);
        let result = encode_neon_sshr(VectorArrangement::S2, &vn, 4);

        // Arithmetic shift right: sign bit fills.
        // 0x80000000 >> 4 = 0xF8000000 (signed), 0x10 >> 4 = 0x01
        let e = env(&[("vn", pack_2s(0x80000000, 0x10))]);
        assert_eq!(result.eval(&e), EvalResult::Bv(pack_2s(0xF8000000, 0x01)));
    }

    #[test]
    fn test_neon_sshr_4h() {
        let vn = SmtExpr::var("vn", 64);
        let result = encode_neon_sshr(VectorArrangement::H4, &vn, 1);

        // 0x8000 >>s 1 = 0xC000, 0x0002 >>s 1 = 0x0001
        let e = env(&[("vn", pack_4h(0x8000, 0x0002, 0, 0))]);
        assert_eq!(
            result.eval(&e),
            EvalResult::Bv(pack_4h(0xC000, 0x0001, 0, 0))
        );
    }

    #[test]
    fn test_neon_sshr_8b() {
        let vn = SmtExpr::var("vn", 64);
        let result = encode_neon_sshr(VectorArrangement::B8, &vn, 1);

        // 0x80 >>s 1 = 0xC0 (sign extend), 0x02 >>s 1 = 0x01
        let e = env(&[("vn", pack_8b(0x80, 0x02, 0, 0, 0, 0, 0, 0))]);
        assert_eq!(
            result.eval(&e),
            EvalResult::Bv(pack_8b(0xC0, 0x01, 0, 0, 0, 0, 0, 0))
        );
    }

    // =======================================================================
    // Cross-check: ADD then SUB = identity
    // =======================================================================

    #[test]
    fn test_add_sub_identity_2s() {
        let vn = SmtExpr::var("vn", 64);
        let vm = SmtExpr::var("vm", 64);

        // (vn + vm) - vm = vn for all lane values
        let added = encode_neon_add(VectorArrangement::S2, &vn, &vm);
        let result = encode_neon_sub(VectorArrangement::S2, &added, &vm);

        // Test with arbitrary values
        let e = env(&[
            ("vn", pack_2s(0xDEADBEEF, 0x12345678)),
            ("vm", pack_2s(0xCAFEBABE, 0x87654321)),
        ]);
        assert_eq!(
            result.eval(&e),
            EvalResult::Bv(pack_2s(0xDEADBEEF, 0x12345678))
        );
    }

    // =======================================================================
    // Cross-check: SHL then USHR roundtrip (for shift < lane_bits)
    // =======================================================================

    #[test]
    fn test_shl_ushr_clears_high_and_low_bits() {
        let vn = SmtExpr::var("vn", 64);

        // SHL by 4 then USHR by 4: clears both high 4 bits and low 4 bits of each lane.
        // SHL shifts out the top 4 bits, USHR zeros the new top 4 bits.
        let shifted_left = encode_neon_shl(VectorArrangement::S2, &vn, 4);
        let shifted_back = encode_neon_ushr(VectorArrangement::S2, &shifted_left, 4);

        // 0x1234ABCD: SHL 4 -> 0x234ABCD0, USHR 4 -> 0x0234ABCD
        // 0xFFFFFFFF: SHL 4 -> 0xFFFFFFF0, USHR 4 -> 0x0FFFFFFF
        let e = env(&[("vn", pack_2s(0x1234ABCD, 0xFFFFFFFF))]);
        assert_eq!(
            shifted_back.eval(&e),
            EvalResult::Bv(pack_2s(0x0234ABCD, 0x0FFFFFFF))
        );
    }

    // =======================================================================
    // 128-bit ADD tests (16B, 8H, 4S, 2D)
    // =======================================================================

    #[test]
    fn test_neon_add_4s() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_add(VectorArrangement::S4, &vn, &vm);

        let mut e = HashMap::new();
        // vn = [10, 20, 30, 40] as 4x32-bit
        // lo 64 bits: lane0=10, lane1=20 => pack_2s(10, 20)
        // hi 64 bits: lane2=30, lane3=40 => pack_2s(30, 40)
        set_128(&mut e, "vn", pack_2s(10, 20), pack_2s(30, 40));
        // vm = [3, 7, 11, 13]
        set_128(&mut e, "vm", pack_2s(3, 7), pack_2s(11, 13));

        assert_all_lanes(&result, VectorArrangement::S4, &[13, 27, 41, 53], &e);
    }

    #[test]
    fn test_neon_add_4s_wrapping() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_add(VectorArrangement::S4, &vn, &vm);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_2s(0xFFFFFFFF, 0x80000000),
            pack_2s(1, 100),
        );
        set_128(
            &mut e,
            "vm",
            pack_2s(1, 0x80000000),
            pack_2s(0xFFFFFFFF, 200),
        );

        // Lane 0: 0xFFFFFFFF + 1 = 0 (wrapping)
        // Lane 1: 0x80000000 + 0x80000000 = 0 (wrapping)
        // Lane 2: 1 + 0xFFFFFFFF = 0 (wrapping)
        // Lane 3: 100 + 200 = 300
        assert_all_lanes(&result, VectorArrangement::S4, &[0, 0, 0, 300], &e);
    }

    #[test]
    fn test_neon_add_8h() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_add(VectorArrangement::H8, &vn, &vm);

        let mut e = HashMap::new();
        // vn: lanes [1,2,3,4, 5,6,7,8] as 8x16-bit
        set_128(&mut e, "vn", pack_4h(1, 2, 3, 4), pack_4h(5, 6, 7, 8));
        // vm: lanes [10,20,30,40, 50,60,70,80]
        set_128(
            &mut e,
            "vm",
            pack_4h(10, 20, 30, 40),
            pack_4h(50, 60, 70, 80),
        );

        assert_all_lanes(
            &result,
            VectorArrangement::H8,
            &[11, 22, 33, 44, 55, 66, 77, 88],
            &e,
        );
    }

    #[test]
    fn test_neon_add_16b() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_add(VectorArrangement::B16, &vn, &vm);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_8b(1, 2, 3, 4, 5, 6, 7, 8),
            pack_8b(9, 10, 11, 12, 13, 14, 15, 16),
        );
        set_128(
            &mut e,
            "vm",
            pack_8b(10, 20, 30, 40, 50, 60, 70, 80),
            pack_8b(90, 100, 110, 120, 130, 140, 150, 160),
        );

        assert_all_lanes(
            &result,
            VectorArrangement::B16,
            &[
                11, 22, 33, 44, 55, 66, 77, 88, 99, 110, 121, 132, 143, 154, 165, 176,
            ],
            &e,
        );
    }

    #[test]
    fn test_neon_add_16b_wrapping() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_add(VectorArrangement::B16, &vn, &vm);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_8b(0xFF, 200, 0, 0, 0, 0, 0, 0),
            pack_8b(0xFF, 0, 0, 0, 0, 0, 0, 0),
        );
        set_128(
            &mut e,
            "vm",
            pack_8b(1, 100, 0, 0, 0, 0, 0, 0),
            pack_8b(2, 0, 0, 0, 0, 0, 0, 0),
        );

        // Lane 0: 0xFF + 1 = 0x00 (wrapping)
        // Lane 1: 200 + 100 = 300 & 0xFF = 44
        // Lane 8: 0xFF + 2 = 0x01 (wrapping)
        assert_lane(&result, VectorArrangement::B16, 0, 0x00, &e);
        assert_lane(&result, VectorArrangement::B16, 1, 44, &e);
        assert_lane(&result, VectorArrangement::B16, 8, 0x01, &e);
    }

    #[test]
    fn test_neon_add_2d() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_add(VectorArrangement::D2, &vn, &vm);

        let mut e = HashMap::new();
        // 2D: lane0 = bits[63:0] = lo, lane1 = bits[127:64] = hi
        set_128(&mut e, "vn", 100, 200);
        set_128(&mut e, "vm", 30, 50);

        assert_all_lanes(&result, VectorArrangement::D2, &[130, 250], &e);
    }

    // =======================================================================
    // 128-bit SUB tests
    // =======================================================================

    #[test]
    fn test_neon_sub_4s() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_sub(VectorArrangement::S4, &vn, &vm);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", pack_2s(100, 200), pack_2s(300, 400));
        set_128(&mut e, "vm", pack_2s(10, 20), pack_2s(30, 40));

        assert_all_lanes(&result, VectorArrangement::S4, &[90, 180, 270, 360], &e);
    }

    #[test]
    fn test_neon_sub_8h() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_sub(VectorArrangement::H8, &vn, &vm);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_4h(100, 200, 300, 400),
            pack_4h(500, 600, 700, 800),
        );
        set_128(
            &mut e,
            "vm",
            pack_4h(10, 20, 30, 40),
            pack_4h(50, 60, 70, 80),
        );

        assert_all_lanes(
            &result,
            VectorArrangement::H8,
            &[90, 180, 270, 360, 450, 540, 630, 720],
            &e,
        );
    }

    #[test]
    fn test_neon_sub_16b() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_sub(VectorArrangement::B16, &vn, &vm);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_8b(50, 100, 150, 200, 10, 20, 30, 40),
            pack_8b(50, 100, 150, 200, 10, 20, 30, 40),
        );
        set_128(
            &mut e,
            "vm",
            pack_8b(10, 20, 30, 40, 5, 10, 15, 20),
            pack_8b(10, 20, 30, 40, 5, 10, 15, 20),
        );

        assert_all_lanes(
            &result,
            VectorArrangement::B16,
            &[
                40, 80, 120, 160, 5, 10, 15, 20, 40, 80, 120, 160, 5, 10, 15, 20,
            ],
            &e,
        );
    }

    #[test]
    fn test_neon_sub_2d() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_sub(VectorArrangement::D2, &vn, &vm);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", 1000, 2000);
        set_128(&mut e, "vm", 300, 500);

        assert_all_lanes(&result, VectorArrangement::D2, &[700, 1500], &e);
    }

    // =======================================================================
    // 128-bit MUL tests (no D2 -- MUL does not support 2D)
    // =======================================================================

    #[test]
    fn test_neon_mul_4s() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_mul(VectorArrangement::S4, &vn, &vm);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", pack_2s(6, 7), pack_2s(8, 9));
        set_128(&mut e, "vm", pack_2s(7, 6), pack_2s(5, 4));

        assert_all_lanes(&result, VectorArrangement::S4, &[42, 42, 40, 36], &e);
    }

    #[test]
    fn test_neon_mul_8h() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_mul(VectorArrangement::H8, &vn, &vm);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", pack_4h(2, 3, 4, 5), pack_4h(6, 7, 8, 9));
        set_128(
            &mut e,
            "vm",
            pack_4h(10, 10, 10, 10),
            pack_4h(10, 10, 10, 10),
        );

        assert_all_lanes(
            &result,
            VectorArrangement::H8,
            &[20, 30, 40, 50, 60, 70, 80, 90],
            &e,
        );
    }

    #[test]
    fn test_neon_mul_16b() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_mul(VectorArrangement::B16, &vn, &vm);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_8b(7, 15, 3, 2, 0, 0, 0, 0),
            pack_8b(5, 10, 4, 0, 0, 0, 0, 0),
        );
        set_128(
            &mut e,
            "vm",
            pack_8b(6, 17, 5, 3, 0, 0, 0, 0),
            pack_8b(8, 10, 3, 0, 0, 0, 0, 0),
        );

        // lane 0: 7*6=42, lane 1: 15*17=255, lane 2: 3*5=15, lane 3: 2*3=6
        // lane 8: 5*8=40, lane 9: 10*10=100, lane 10: 4*3=12, lane 11: 0*0=0
        assert_lane(&result, VectorArrangement::B16, 0, 42, &e);
        assert_lane(&result, VectorArrangement::B16, 1, 255, &e);
        assert_lane(&result, VectorArrangement::B16, 2, 15, &e);
        assert_lane(&result, VectorArrangement::B16, 3, 6, &e);
        assert_lane(&result, VectorArrangement::B16, 8, 40, &e);
        assert_lane(&result, VectorArrangement::B16, 9, 100, &e);
        assert_lane(&result, VectorArrangement::B16, 10, 12, &e);
    }

    #[test]
    fn test_neon_mul_4s_wrapping() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_mul(VectorArrangement::S4, &vn, &vm);

        let mut e = HashMap::new();
        // 0x80000000 * 2 = 0x100000000 => wraps to 0x00000000
        set_128(&mut e, "vn", pack_2s(0x80000000, 1), pack_2s(100, 0));
        set_128(&mut e, "vm", pack_2s(2, 1), pack_2s(200, 0));

        assert_lane(&result, VectorArrangement::S4, 0, 0, &e);
        assert_lane(&result, VectorArrangement::S4, 1, 1, &e);
        assert_lane(&result, VectorArrangement::S4, 2, 20000, &e);
        assert_lane(&result, VectorArrangement::S4, 3, 0, &e);
    }

    // =======================================================================
    // 128-bit NEG tests
    // =======================================================================

    #[test]
    fn test_neon_neg_4s() {
        let vn = var_128("vn");
        let result = encode_neon_neg(VectorArrangement::S4, &vn);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", pack_2s(1, 0), pack_2s(100, 0xFFFFFFFF));

        // neg(1) = 0xFFFFFFFF, neg(0) = 0, neg(100) = 0xFFFFFF9C, neg(0xFFFFFFFF) = 1
        assert_all_lanes(
            &result,
            VectorArrangement::S4,
            &[0xFFFFFFFF, 0, 0xFFFFFF9C, 1],
            &e,
        );
    }

    #[test]
    fn test_neon_neg_8h() {
        let vn = var_128("vn");
        let result = encode_neon_neg(VectorArrangement::H8, &vn);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_4h(1, 2, 0, 100),
            pack_4h(0xFFFF, 0x8000, 3, 50),
        );

        assert_all_lanes(
            &result,
            VectorArrangement::H8,
            &[0xFFFF, 0xFFFE, 0, 0xFF9C, 1, 0x8000, 0xFFFD, 0xFFCE],
            &e,
        );
    }

    #[test]
    fn test_neon_neg_16b() {
        let vn = var_128("vn");
        let result = encode_neon_neg(VectorArrangement::B16, &vn);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_8b(1, 0, 0xFF, 0x80, 0, 0, 0, 0),
            pack_8b(2, 0, 0xFE, 0x7F, 0, 0, 0, 0),
        );

        // lane 0: neg(1) = 0xFF
        // lane 1: neg(0) = 0
        // lane 2: neg(0xFF) = 1
        // lane 3: neg(0x80) = 0x80
        // lane 8: neg(2) = 0xFE
        // lane 10: neg(0xFE) = 2
        // lane 11: neg(0x7F) = 0x81
        assert_lane(&result, VectorArrangement::B16, 0, 0xFF, &e);
        assert_lane(&result, VectorArrangement::B16, 1, 0, &e);
        assert_lane(&result, VectorArrangement::B16, 2, 1, &e);
        assert_lane(&result, VectorArrangement::B16, 3, 0x80, &e);
        assert_lane(&result, VectorArrangement::B16, 8, 0xFE, &e);
        assert_lane(&result, VectorArrangement::B16, 10, 2, &e);
        assert_lane(&result, VectorArrangement::B16, 11, 0x81, &e);
    }

    #[test]
    fn test_neon_neg_2d() {
        let vn = var_128("vn");
        let result = encode_neon_neg(VectorArrangement::D2, &vn);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", 1, 0);

        // neg(1) in 64-bit = 0xFFFFFFFF_FFFFFFFF
        // neg(0) = 0
        assert_lane(&result, VectorArrangement::D2, 0, 0xFFFFFFFF_FFFFFFFF, &e);
        assert_lane(&result, VectorArrangement::D2, 1, 0, &e);
    }

    // =======================================================================
    // 128-bit bitwise operation tests (AND, ORR, EOR, BIC)
    //
    // Bitwise ops are width-agnostic: they operate on whatever width the
    // input SmtExpr has. For 128-bit, we construct 128-bit inputs and
    // verify the result lane-by-lane.
    // =======================================================================

    #[test]
    fn test_neon_and_128bit() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_and(&vn, &vm);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", 0xFF00_FF00_FF00_FF00, 0xAAAA_AAAA_AAAA_AAAA);
        set_128(&mut e, "vm", 0x0F0F_0F0F_0F0F_0F0F, 0xFFFF_0000_FFFF_0000);

        // Verify via D2 lane extraction (64-bit halves)
        // lo half: 0xFF00_FF00_FF00_FF00 AND 0x0F0F_0F0F_0F0F_0F0F = 0x0F00_0F00_0F00_0F00
        // hi half: 0xAAAA_AAAA_AAAA_AAAA AND 0xFFFF_0000_FFFF_0000 = 0xAAAA_0000_AAAA_0000
        assert_lane(&result, VectorArrangement::D2, 0, 0x0F00_0F00_0F00_0F00, &e);
        assert_lane(&result, VectorArrangement::D2, 1, 0xAAAA_0000_AAAA_0000, &e);
    }

    #[test]
    fn test_neon_orr_128bit() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_orr(&vn, &vm);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", 0xFF00_0000_0000_0000, 0x0000_0000_0000_00FF);
        set_128(&mut e, "vm", 0x00FF_0000_0000_0000, 0x0000_0000_0000_FF00);

        assert_lane(&result, VectorArrangement::D2, 0, 0xFFFF_0000_0000_0000, &e);
        assert_lane(&result, VectorArrangement::D2, 1, 0x0000_0000_0000_FFFF, &e);
    }

    #[test]
    fn test_neon_eor_128bit() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_eor(&vn, &vm);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", 0xAAAA_AAAA_AAAA_AAAA, 0x5555_5555_5555_5555);
        set_128(&mut e, "vm", 0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF);

        assert_lane(&result, VectorArrangement::D2, 0, 0x5555_5555_5555_5555, &e);
        assert_lane(&result, VectorArrangement::D2, 1, 0xAAAA_AAAA_AAAA_AAAA, &e);
    }

    #[test]
    fn test_neon_bic_128bit() {
        let vn = var_128("vn");
        let vm = var_128("vm");
        let result = encode_neon_bic(&vn, &vm);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", 0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF);
        set_128(&mut e, "vm", 0x0F0F_0F0F_0F0F_0F0F, 0xF0F0_F0F0_F0F0_F0F0);

        // BIC = vn AND NOT(vm)
        assert_lane(&result, VectorArrangement::D2, 0, 0xF0F0_F0F0_F0F0_F0F0, &e);
        assert_lane(&result, VectorArrangement::D2, 1, 0x0F0F_0F0F_0F0F_0F0F, &e);
    }

    // =======================================================================
    // 128-bit shift tests (SHL, USHR, SSHR)
    // =======================================================================

    #[test]
    fn test_neon_shl_4s() {
        let vn = var_128("vn");
        let result = encode_neon_shl(VectorArrangement::S4, &vn, 4);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", pack_2s(1, 0xFF), pack_2s(0x1000, 0x80000000));

        // 1 << 4 = 16, 0xFF << 4 = 0xFF0
        // 0x1000 << 4 = 0x10000, 0x80000000 << 4 = 0 (wrapping 32-bit)
        assert_all_lanes(&result, VectorArrangement::S4, &[16, 0xFF0, 0x10000, 0], &e);
    }

    #[test]
    fn test_neon_shl_8h() {
        let vn = var_128("vn");
        let result = encode_neon_shl(VectorArrangement::H8, &vn, 1);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_4h(1, 2, 3, 0x7FFF),
            pack_4h(4, 5, 0x8000, 0xFFFF),
        );

        // Each 16-bit lane << 1
        assert_all_lanes(
            &result,
            VectorArrangement::H8,
            &[2, 4, 6, 0xFFFE, 8, 10, 0, 0xFFFE],
            &e,
        );
    }

    #[test]
    fn test_neon_shl_16b() {
        let vn = var_128("vn");
        let result = encode_neon_shl(VectorArrangement::B16, &vn, 2);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_8b(1, 63, 0, 0, 0, 0, 0, 0),
            pack_8b(10, 0x40, 0, 0, 0, 0, 0, 0),
        );

        // 1 << 2 = 4, 63 << 2 = 252, 10 << 2 = 40, 0x40 << 2 = 0x00 (wrapping 8-bit)
        assert_lane(&result, VectorArrangement::B16, 0, 4, &e);
        assert_lane(&result, VectorArrangement::B16, 1, 252, &e);
        assert_lane(&result, VectorArrangement::B16, 8, 40, &e);
        assert_lane(&result, VectorArrangement::B16, 9, 0, &e);
    }

    #[test]
    fn test_neon_shl_2d() {
        let vn = var_128("vn");
        let result = encode_neon_shl(VectorArrangement::D2, &vn, 8);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", 0xFF, 0x0100_0000_0000_0000);

        // 0xFF << 8 = 0xFF00
        // 0x0100_0000_0000_0000 << 8 = 0 (bit 56 shifted to bit 64, lost in 64-bit)
        assert_lane(&result, VectorArrangement::D2, 0, 0xFF00, &e);
        assert_lane(&result, VectorArrangement::D2, 1, 0, &e);
    }

    #[test]
    fn test_neon_ushr_4s() {
        let vn = var_128("vn");
        let result = encode_neon_ushr(VectorArrangement::S4, &vn, 4);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_2s(0x100, 0xF0000000),
            pack_2s(0xFFFFFFFF, 16),
        );

        assert_all_lanes(
            &result,
            VectorArrangement::S4,
            &[0x10, 0x0F000000, 0x0FFFFFFF, 1],
            &e,
        );
    }

    #[test]
    fn test_neon_ushr_8h() {
        let vn = var_128("vn");
        let result = encode_neon_ushr(VectorArrangement::H8, &vn, 8);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_4h(0xFF00, 0x1234, 0, 0),
            pack_4h(0xABCD, 0x00FF, 0, 0),
        );

        assert_lane(&result, VectorArrangement::H8, 0, 0xFF, &e);
        assert_lane(&result, VectorArrangement::H8, 1, 0x12, &e);
        assert_lane(&result, VectorArrangement::H8, 4, 0xAB, &e);
        assert_lane(&result, VectorArrangement::H8, 5, 0x00, &e);
    }

    #[test]
    fn test_neon_ushr_2d() {
        let vn = var_128("vn");
        let result = encode_neon_ushr(VectorArrangement::D2, &vn, 32);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", 0xDEADBEEF_12345678, 0x00000001_00000000);

        // 0xDEADBEEF_12345678 >> 32 = 0xDEADBEEF
        // 0x00000001_00000000 >> 32 = 1
        assert_lane(&result, VectorArrangement::D2, 0, 0xDEADBEEF, &e);
        assert_lane(&result, VectorArrangement::D2, 1, 1, &e);
    }

    #[test]
    fn test_neon_sshr_4s() {
        let vn = var_128("vn");
        let result = encode_neon_sshr(VectorArrangement::S4, &vn, 4);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_2s(0x80000000, 0x10),
            pack_2s(0xF0000000, 0x7FFFFFFF),
        );

        // 0x80000000 >>s 4 = 0xF8000000 (sign fills)
        // 0x10 >>s 4 = 0x01
        // 0xF0000000 >>s 4 = 0xFF000000 (sign fills)
        // 0x7FFFFFFF >>s 4 = 0x07FFFFFF (positive, zero fills)
        assert_all_lanes(
            &result,
            VectorArrangement::S4,
            &[0xF8000000, 0x01, 0xFF000000, 0x07FFFFFF],
            &e,
        );
    }

    #[test]
    fn test_neon_sshr_8h() {
        let vn = var_128("vn");
        let result = encode_neon_sshr(VectorArrangement::H8, &vn, 1);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_4h(0x8000, 0x0002, 0, 0),
            pack_4h(0xFFFF, 0x7FFF, 0, 0),
        );

        // 0x8000 >>s 1 = 0xC000
        // 0x0002 >>s 1 = 0x0001
        // 0xFFFF >>s 1 = 0xFFFF (-1 >>s 1 = -1)
        // 0x7FFF >>s 1 = 0x3FFF
        assert_lane(&result, VectorArrangement::H8, 0, 0xC000, &e);
        assert_lane(&result, VectorArrangement::H8, 1, 0x0001, &e);
        assert_lane(&result, VectorArrangement::H8, 4, 0xFFFF, &e);
        assert_lane(&result, VectorArrangement::H8, 5, 0x3FFF, &e);
    }

    #[test]
    fn test_neon_sshr_16b() {
        let vn = var_128("vn");
        let result = encode_neon_sshr(VectorArrangement::B16, &vn, 1);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_8b(0x80, 0x02, 0, 0, 0, 0, 0, 0),
            pack_8b(0xFF, 0x7F, 0, 0, 0, 0, 0, 0),
        );

        // 0x80 >>s 1 = 0xC0, 0x02 >>s 1 = 0x01
        // 0xFF >>s 1 = 0xFF (-1 >>s 1 = -1 in 8-bit)
        // 0x7F >>s 1 = 0x3F
        assert_lane(&result, VectorArrangement::B16, 0, 0xC0, &e);
        assert_lane(&result, VectorArrangement::B16, 1, 0x01, &e);
        assert_lane(&result, VectorArrangement::B16, 8, 0xFF, &e);
        assert_lane(&result, VectorArrangement::B16, 9, 0x3F, &e);
    }

    #[test]
    fn test_neon_sshr_2d() {
        let vn = var_128("vn");
        let result = encode_neon_sshr(VectorArrangement::D2, &vn, 4);

        let mut e = HashMap::new();
        // 0x8000_0000_0000_0000 is negative in signed 64-bit
        set_128(&mut e, "vn", 0x8000_0000_0000_0000, 0x10);

        // 0x8000_0000_0000_0000 >>s 4 = 0xF800_0000_0000_0000
        // 0x10 >>s 4 = 0x01
        assert_lane(&result, VectorArrangement::D2, 0, 0xF800_0000_0000_0000, &e);
        assert_lane(&result, VectorArrangement::D2, 1, 0x01, &e);
    }

    // =======================================================================
    // 128-bit cross-checks
    // =======================================================================

    #[test]
    fn test_add_sub_identity_4s() {
        // (vn + vm) - vm = vn for all lane values
        let vn = var_128("vn");
        let vm = var_128("vm");

        let added = encode_neon_add(VectorArrangement::S4, &vn, &vm);
        let result = encode_neon_sub(VectorArrangement::S4, &added, &vm);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_2s(0xDEADBEEF, 0x12345678),
            pack_2s(0xCAFEBABE, 0x87654321),
        );
        set_128(
            &mut e,
            "vm",
            pack_2s(0xCAFEBABE, 0x87654321),
            pack_2s(0xDEADBEEF, 0x12345678),
        );

        assert_all_lanes(
            &result,
            VectorArrangement::S4,
            &[0xDEADBEEF, 0x12345678, 0xCAFEBABE, 0x87654321],
            &e,
        );
    }

    #[test]
    fn test_shl_ushr_roundtrip_4s() {
        let vn = var_128("vn");

        let shifted_left = encode_neon_shl(VectorArrangement::S4, &vn, 4);
        let shifted_back = encode_neon_ushr(VectorArrangement::S4, &shifted_left, 4);

        let mut e = HashMap::new();
        set_128(
            &mut e,
            "vn",
            pack_2s(0x1234ABCD, 0xFFFFFFFF),
            pack_2s(0x0000000F, 0x12345678),
        );

        // SHL 4 then USHR 4 clears top 4 bits of each 32-bit lane
        assert_all_lanes(
            &shifted_back,
            VectorArrangement::S4,
            &[0x0234ABCD, 0x0FFFFFFF, 0x0000000F, 0x02345678],
            &e,
        );
    }

    #[test]
    fn test_add_sub_identity_2d() {
        let vn = var_128("vn");
        let vm = var_128("vm");

        let added = encode_neon_add(VectorArrangement::D2, &vn, &vm);
        let result = encode_neon_sub(VectorArrangement::D2, &added, &vm);

        let mut e = HashMap::new();
        set_128(&mut e, "vn", 0xDEADBEEFCAFEBABE, 0x123456789ABCDEF0);
        set_128(&mut e, "vm", 0xCAFEBABEDEADBEEF, 0x9ABCDEF012345678);

        assert_all_lanes(
            &result,
            VectorArrangement::D2,
            &[0xDEADBEEFCAFEBABE, 0x123456789ABCDEF0],
            &e,
        );
    }

    // =======================================================================
    // Lane-wise FP encoder tests (the B-aarch64-neon-fp side).
    // =======================================================================

    use crate::fp_bitmodel;

    /// Eval one lane to its result bits (f64: to_bits; f32: fcvt_narrow of carrier).
    fn fp_lane_bits(expr: &SmtExpr, lane_bits: u32, is_fp: bool) -> u64 {
        let env: HashMap<String, u64> = HashMap::new();
        match expr.try_eval(&env).expect("fp lane eval") {
            EvalResult::Float(f) => {
                if is_fp && lane_bits == 32 {
                    fp_bitmodel::fcvt_narrow(f.to_bits())
                } else {
                    f.to_bits()
                }
            }
            EvalResult::Bv(v) => v,
            EvalResult::Bv128(v) => v as u64,
            other => panic!("fp lane eval -> {other:?}"),
        }
    }

    fn pack_2d(lo: u64, hi: u64) -> u128 {
        ((hi as u128) << 64) | (lo as u128)
    }

    #[test]
    fn test_neon_fadd_2d() {
        // 1.0 + 2.0 = 3.0 (lane0); 2.0 + 2.0 = 4.0 (lane1), all binary64.
        let one = 1.0f64.to_bits();
        let two = 2.0f64.to_bits();
        let a = neon_fp_lanes(pack_2d(one, two), VectorArrangement::D2);
        let b = neon_fp_lanes(pack_2d(two, two), VectorArrangement::D2);
        let lanes = encode_neon_fadd(&a, &b);
        assert_eq!(fp_lane_bits(&lanes[0], 64, true), 3.0f64.to_bits());
        assert_eq!(fp_lane_bits(&lanes[1], 64, true), 4.0f64.to_bits());
    }

    #[test]
    fn test_neon_fmul_4s() {
        // 4 x f32: 1.5*2.0=3.0, 3.0*3.0=9.0, -1.0*4.0=-4.0, 0.5*0.5=0.25.
        let l = |x: f32| x.to_bits() as u128;
        let a_bits = l(1.5) | (l(3.0) << 32) | (l(-1.0) << 64) | (l(0.5) << 96);
        let b_bits = l(2.0) | (l(3.0) << 32) | (l(4.0) << 64) | (l(0.5) << 96);
        let a = neon_fp_lanes(a_bits, VectorArrangement::S4);
        let b = neon_fp_lanes(b_bits, VectorArrangement::S4);
        let lanes = encode_neon_fmul(&a, &b);
        assert_eq!(fp_lane_bits(&lanes[0], 32, true), 3.0f32.to_bits() as u64);
        assert_eq!(fp_lane_bits(&lanes[1], 32, true), 9.0f32.to_bits() as u64);
        assert_eq!(
            fp_lane_bits(&lanes[2], 32, true),
            (-4.0f32).to_bits() as u64
        );
        assert_eq!(fp_lane_bits(&lanes[3], 32, true), 0.25f32.to_bits() as u64);
    }

    #[test]
    fn test_neon_fcmgt_2d_masks() {
        // 2.0 > 1.0 -> all-ones; 1.0 > 2.0 -> 0.
        let one = 1.0f64.to_bits();
        let two = 2.0f64.to_bits();
        let a = neon_fp_lanes(pack_2d(two, one), VectorArrangement::D2);
        let b = neon_fp_lanes(pack_2d(one, two), VectorArrangement::D2);
        let lanes = encode_neon_fcmgt(VectorArrangement::D2, &a, &b);
        assert_eq!(fp_lane_bits(&lanes[0], 64, false), u64::MAX);
        assert_eq!(fp_lane_bits(&lanes[1], 64, false), 0);
    }

    #[test]
    fn test_neon_fmin_propagates_nan_fminnm_returns_number() {
        // FMIN(qNaN, 1.0) -> NaN (propagating); FMINNM(qNaN, 1.0) -> 1.0 (number).
        let qnan = 0x7ff8_0000_0000_0000u64;
        let one = 1.0f64.to_bits();
        let a = neon_fp_lanes(pack_2d(qnan, one), VectorArrangement::D2);
        let b = neon_fp_lanes(pack_2d(one, one), VectorArrangement::D2);
        let fmin = encode_neon_fmin(VectorArrangement::D2, &a, &b);
        let fminnm = encode_neon_fminnm(VectorArrangement::D2, &a, &b);
        // lane0: qNaN vs 1.0
        assert!(
            fp_bitmodel::is_nan(fp_bitmodel::F64, fp_lane_bits(&fmin[0], 64, true)),
            "FMIN lane with a qNaN operand must be NaN (NaN-propagating, AS ARM)"
        );
        assert_eq!(
            fp_lane_bits(&fminnm[0], 64, true),
            one,
            "FMINNM lane with a lone qNaN must return the NUMBER (IEEE minNum, AS ARM)"
        );
    }

    #[test]
    fn test_neon_fneg_fabs_sign_bit() {
        // FNEG flips sign; FABS clears it (binary64).
        let neg_three = (-3.0f64).to_bits();
        let a = neon_fp_lanes(pack_2d(neg_three, neg_three), VectorArrangement::D2);
        let neg = encode_neon_fneg(&a);
        let abs = encode_neon_fabs(&a);
        assert_eq!(fp_lane_bits(&neg[0], 64, true), 3.0f64.to_bits());
        assert_eq!(fp_lane_bits(&abs[0], 64, true), 3.0f64.to_bits());
    }
}
